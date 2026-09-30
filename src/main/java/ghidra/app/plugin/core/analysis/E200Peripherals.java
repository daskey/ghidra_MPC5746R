/* ###
 * IP: GHIDRA
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package ghidra.app.plugin.core.analysis;

import java.io.*;
import java.util.*;
import java.util.function.Supplier;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.GZIPInputStream;

import generic.jar.ResourceFile;
import ghidra.app.plugin.core.analysis.SvdDevice.*;
import ghidra.app.util.importer.MessageLog;
import ghidra.framework.Application;
import ghidra.framework.options.Options;
import ghidra.framework.store.LockException;
import ghidra.program.model.address.*;
import ghidra.program.model.data.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.*;
import ghidra.program.model.symbol.*;
import ghidra.program.model.util.CodeUnitInsertionException;
import ghidra.util.Msg;
import ghidra.util.exception.CancelledException;
import ghidra.util.exception.InvalidInputException;
import ghidra.util.task.TaskMonitor;

/**
 * Adds the MPC5746R peripherals (part of {@link E200Analyzer}) from NXP's CMSIS-SVD
 * description, which the extension bundles: a volatile memory block for
 * each peripheral where nothing is mapped, and a structure of its registers at its base
 * address, labeled with the peripheral's name. The decompiler then shows peripheral accesses
 * such as {@code INTC.PSR[0x1b] = 0} instead of {@code _DAT_fc040076 = 0}.
 * <ul>
 * <li>Arrays of registers become arrays ({@code SIUL2_SVD_GEN.MSCR[12]}), and registers
 * repeated for each channel become arrays of structures ({@code DMA_0.TCD[ch].SADDR},
 * {@code MEMU.SYS_RAM_CERR[i].STS}).</li>
 * <li>Alternate views of a register (such as {@code PUSHR_SLAVE}) are named in the comment
 * of the register they overlap, and each register's comment lists the masks of its fields.
 * Undocumented space is typed as 4-byte words, which the decompiler names by their hex
 * offset.</li>
 * <li>Peripherals with the same registers share a type, named after their group
 * ({@code DSPI_Type} for {@code DSPI_0} to {@code DSPI_4}).</li>
 * <li>Registers are integers. An option types them as bit field structures instead: the
 * decompiler then names the field a test extracts ({@code FCCU.CTRL.OPS != 3}), but casts
 * every write of a whole register.</li>
 * </ul>
 * Like the RAM blocks of {@link E200DataTypes}, the peripherals are added at the end
 * of analysis: with them mapped, Ghidra's address table analysis takes flash values for
 * pointers into peripheral space.
 */
final class E200Peripherals {

	private static final String OPTION_NAME = "Add MPC5746R peripherals";
	private static final String OPTION_DESCRIPTION =
		"Add the MPC5746R peripherals from NXP's SVD description, bundled with the extension:\n" +
			"a volatile memory block and a structure of registers at each peripheral's base\n" +
			"address, where nothing is mapped.";
	private static final String OPTION_NAME_BIT_FIELDS = "Register bit fields";
	private static final String OPTION_DESCRIPTION_BIT_FIELDS =
		"Type registers as structures of their bit fields rather than as integers. The\n" +
			"decompiler then names the field a test extracts (FCCU.CTRL.OPS != 3), but casts\n" +
			"every write of a whole register.";
	private static final boolean OPTION_DEFAULT_BIT_FIELDS = false;

	private static final String SVD = "svd/MPC5746R.svd.gz";

	/** The bundled device description, read once. */
	private static SvdDevice device;

	private boolean enabled = true;
	private boolean bitFields = OPTION_DEFAULT_BIT_FIELDS;

	/** The initialized memory for which the peripherals were last added. */
	private AddressSetView appliedFor;

	void registerOptions(Options options) {
		options.registerOption(OPTION_NAME, enabled, null, OPTION_DESCRIPTION);
		options.registerOption(OPTION_NAME_BIT_FIELDS, bitFields, null,
			OPTION_DESCRIPTION_BIT_FIELDS);
	}

	void optionsChanged(Options options) {
		enabled = options.getBoolean(OPTION_NAME, enabled);
		bitFields = options.getBoolean(OPTION_NAME_BIT_FIELDS, bitFields);
	}

	/**
	 * Adds the peripherals, at the end of analysis (see the class comment), and again when
	 * memory is added, which may hold tables of base addresses.
	 */
	boolean apply(Program program, TaskMonitor monitor, MessageLog log)
			throws CancelledException {
		AddressSetView memory = program.getMemory().getLoadedAndInitializedAddressSet();
		if (!enabled || memory.equals(appliedFor)) {
			return true;
		}
		appliedFor = memory;
		SvdDevice svd;
		try {
			svd = device();
		}
		catch (IOException e) {
			String message = "Could not read the peripheral description: " + e.getMessage();
			Msg.warn(this, message);
			log.appendMsg(E200Analyzer.NAME, message);
			return false;
		}
		monitor.setMessage(E200Analyzer.NAME + " - " + svd.name);
		new PeripheralBuilder(program, svd, bitFields).build(monitor);
		return true;
	}

	private static synchronized SvdDevice device() throws IOException {
		if (device == null) {
			ResourceFile file = Application.findDataFileInAnyModule(SVD);
			if (file == null) {
				throw new FileNotFoundException(SVD);
			}
			try (InputStream in = new BufferedInputStream(file.getInputStream())) {
				device = SvdDevice.read(new GZIPInputStream(in));
			}
		}
		return device;
	}

	/** Builds the types, memory blocks and data of the peripherals of a device. */
	private static final class PeripheralBuilder {

		/**
		 * A structure component: a register, an array of them, or an array of register groups.
		 * The type is only created for components that are placed.
		 */
		private record Component(long offset, int length, String name, Supplier<DataType> type,
				String comment, boolean alternate) {}

		/** Names of an array of register groups and of the group's registers. */
		private record GroupNames(String name, List<String> members) {}

		/** A register name with a number at the end, as in {@code CPR0} or {@code LOCK12}. */
		private static final Pattern NUMBERED = Pattern.compile("(.*[A-Za-z_])(0|[1-9]\\d*)");

		private final Program program;
		private final SvdDevice device;
		private final boolean bitFields;
		private final DataTypeManager dtm;
		private final CategoryPath category;

		/** Peripheral types by the layout of their registers. */
		private final Map<String, DataType> typesByLayout = new HashMap<>();
		private final Set<String> typeNames = new HashSet<>();

		PeripheralBuilder(Program program, SvdDevice device, boolean bitFields) {
			this.program = program;
			this.device = device;
			this.bitFields = bitFields;
			this.dtm = program.getDataTypeManager();
			this.category = new CategoryPath("/SVD/" + device.name);
		}

		void build(TaskMonitor monitor) throws CancelledException {
			Memory memory = program.getMemory();
			Listing listing = program.getListing();
			AddressSpace space = program.getAddressFactory().getDefaultAddressSpace();
			Map<Long, Integer> peripheralsAtBase = new HashMap<>();
			for (Peripheral p : device.peripherals) {
				peripheralsAtBase.merge(p.baseAddress(), 1, Integer::sum);
			}
			Map<Long, DataType> typesAt = new HashMap<>();
			int blocks = 0;
			int typed = 0;
			for (Peripheral p : device.peripherals) {
				monitor.checkCancelled();
				// the peripheral's base, unless several peripherals share it (as the eTPU's do)
				long start = peripheralsAtBase.get(p.baseAddress()) > 1 ? startOffset(p) : 0;
				long size = endOffset(p) - start;
				if (size <= 0) {
					continue;
				}
				Address first;
				Address last;
				try {
					first = space.getAddress(p.baseAddress() + start);
					last = first.addNoWrap(size - 1);
				}
				catch (AddressOutOfBoundsException | AddressOverflowException e) {
					continue;
				}
				blocks += addBlocks(memory, p, first, last);
				if (!memory.contains(first, last)) {
					continue;
				}
				Data existing = listing.getDefinedDataAt(first);
				if (existing != null && category.equals(existing.getDataType().getCategoryPath())) {
					typesAt.put(first.getOffset(), existing.getDataType()); // added before
					continue;
				}
				if (!listing.isUndefined(first, last)) {
					continue;
				}
				try {
					Data data = listing.createData(first, peripheralType(p, start, size));
					typesAt.put(first.getOffset(), data.getDataType());
					typed++;
				}
				catch (CodeUnitInsertionException e) {
					continue;
				}
				label(first, p.name());
			}
			int pointers = typeBaseAddressTables(typesAt, monitor);
			if (typed > 0 || pointers > 0) {
				Msg.info(E200Peripherals.class, "Added " + typed + " peripherals of " +
					device.name + " (" + blocks + " memory blocks) and typed " + pointers +
					" pointers to them");
			}
		}

		/**
		 * Types tables of peripheral base addresses in initialized memory, such as the tables
		 * of drivers that serve several instances of a peripheral, as pointers to the
		 * peripherals' structures. Only runs of two or more base addresses count: a single one
		 * is as likely a mask or the bound of a memory region.
		 */
		private int typeBaseAddressTables(Map<Long, DataType> typesAt, TaskMonitor monitor)
				throws CancelledException {
			Memory memory = program.getMemory();
			int count = 0;
			for (MemoryBlock block : memory.getBlocks()) {
				if (!block.isInitialized() || block.isVolatile()) {
					continue;
				}
				List<Address> run = new ArrayList<>();
				List<DataType> types = new ArrayList<>();
				long end = block.getEnd().getOffset();
				for (long offset = (block.getStart().getOffset() + 3) & ~3L; offset + 3 <= end;
						offset += 4) {
					monitor.checkCancelled();
					Address address = block.getStart().getNewAddress(offset);
					DataType type = null;
					try {
						type = typesAt.get(memory.getInt(address) & 0xffffffffL);
					}
					catch (MemoryAccessException e) {
						// no bytes
					}
					if (type != null && canTypeWord(address)) {
						run.add(address);
						types.add(type);
					}
					else {
						count += typePointers(run, types);
					}
				}
				count += typePointers(run, types);
			}
			return count;
		}

		/** Whether the word at an address is undefined or an integer the analysis created. */
		private boolean canTypeWord(Address address) {
			Listing listing = program.getListing();
			if (listing.isUndefined(address, address.add(3))) {
				return true;
			}
			Data data = listing.getDefinedDataAt(address);
			if (data == null || data.getLength() != 4) {
				return false;
			}
			DataType type = data.getDataType();
			return Undefined.isUndefined(type) || type instanceof AbstractIntegerDataType;
		}

		/** Types a run of base addresses as pointers, if there are two or more, and clears it. */
		private int typePointers(List<Address> run, List<DataType> types) {
			int count = 0;
			if (run.size() >= 2) {
				Listing listing = program.getListing();
				for (int i = 0; i < run.size(); i++) {
					Address address = run.get(i);
					try {
						listing.clearCodeUnits(address, address.add(3), false);
						listing.createData(address, new PointerDataType(types.get(i), 4, dtm));
						count++;
					}
					catch (CodeUnitInsertionException e) {
						// something else is there
					}
				}
			}
			run.clear();
			types.clear();
			return count;
		}

		/** Adds volatile blocks for the unmapped parts of a peripheral's address range. */
		private int addBlocks(Memory memory, Peripheral p, Address first, Address last) {
			int count = 0;
			AddressSet unmapped = new AddressSet(first, last).subtract(memory);
			for (AddressRange range : unmapped) {
				String name = p.name();
				for (int n = 1; memory.getBlock(name) != null; n++) {
					name = p.name() + "_" + n;
				}
				try {
					MemoryBlock block = memory.createUninitializedBlock(name,
						range.getMinAddress(), range.getLength(), false);
					block.setPermissions(true, true, false);
					block.setVolatile(true);
					block.setComment((p.description() == null ? p.name() : p.description()) +
						", added by " + E200Analyzer.NAME);
					count++;
				}
				catch (LockException | MemoryConflictException | AddressOverflowException e) {
					Msg.info(E200Peripherals.class,
						"Could not add " + name + ": " + e.getMessage());
				}
			}
			return count;
		}

		private static long startOffset(Peripheral p) {
			long start = Long.MAX_VALUE;
			for (AddressBlock b : p.addressBlocks()) {
				start = Math.min(start, b.offset());
			}
			for (Register r : p.registers()) {
				start = Math.min(start, r.offset());
			}
			return start == Long.MAX_VALUE ? 0 : start;
		}

		private static long endOffset(Peripheral p) {
			long end = 0;
			for (AddressBlock b : p.addressBlocks()) {
				end = Math.max(end, b.offset() + b.size());
			}
			for (Register r : p.registers()) {
				end = Math.max(end, r.offset() + (r.dim() - 1) * r.dimIncrement() + r.size());
			}
			return end;
		}

		// ---- Types ------------------------------------------------------------------------

		/** The structure of a peripheral's registers, shared by peripherals of the same layout. */
		private DataType peripheralType(Peripheral p, long start, long size) {
			StringBuilder layout = new StringBuilder().append(size);
			for (Register r : p.registers()) {
				layout.append('|')
						.append(r.name())
						.append(',')
						.append(r.offset() - start)
						.append(',')
						.append(r.size())
						.append(',')
						.append(r.dim())
						.append(',')
						.append(r.dimIncrement())
						.append(',')
						.append(r.dimIndex())
						.append(',')
						.append(r.alternate());
				for (Field f : r.fields()) {
					layout.append(',')
							.append(f.name())
							.append(':')
							.append(f.bitOffset())
							.append(':')
							.append(f.bitWidth());
				}
			}
			DataType existing = typesByLayout.get(layout.toString());
			if (existing != null) {
				return existing;
			}
			String baseName =
				p.groupName() != null && !typeNames.contains(p.groupName() + "_Type")
						? p.groupName()
						: p.name();
			StructureDataType struct =
				new StructureDataType(category, typeName(baseName), (int) size, dtm);
			struct.setDescription(p.description());
			place(struct, components(p, baseName), start, start);
			DataType type = dtm.resolve(struct, DataTypeConflictHandler.KEEP_HANDLER);
			typesByLayout.put(layout.toString(), type);
			return type;
		}

		/**
		 * The components of a peripheral structure. Arrays of registers numbered from 0 become
		 * arrays, strided arrays that repeat together become arrays of structures (see
		 * {@link #addGroups}), and other arrays become separate registers.
		 */
		private List<Component> components(Peripheral p, String baseName) {
			List<Component> components = new ArrayList<>();
			Map<String, List<Register>> strided = new LinkedHashMap<>();
			for (Register r : numberedArrays(p.registers())) {
				String name = trimUnderscores(r.name().replace("%s", ""));
				String typeName = baseName + "_" + name;
				if (r.dim() <= 1) {
					components.add(new Component(r.offset(), r.size(), name,
						() -> registerType(r, typeName), comment(r), r.alternate()));
				}
				else if (!r.name().contains("%s") || !isZeroBased(r.dimIndex())) {
					expand(r, baseName, components);
				}
				else if (r.dimIncrement() == r.size()) {
					components.add(new Component(r.offset(), r.dim() * r.size(), name,
						() -> new ArrayDataType(registerType(r, typeName), r.dim(), r.size(), dtm),
						comment(r), r.alternate()));
				}
				else {
					strided.computeIfAbsent(r.dim() + "|" + r.dimIncrement(),
						k -> new ArrayList<>()).add(r);
				}
			}
			for (List<Register> group : strided.values()) {
				addGroups(group, baseName, components);
			}
			return components;
		}

		/**
		 * Adds strided arrays of the same length and stride as arrays of structures, one for
		 * each window of the stride's length they start in, when the registers of a window can
		 * be named: {@code TCD%s_SADDR} and {@code TCD%s_SOFF} become {@code TCD[n].SADDR} and
		 * {@code TCD[n].SOFF}; {@code SYS_RAM_CERR_STS%s} and {@code SYS_RAM_CERR_ADDR%s} become
		 * {@code SYS_RAM_CERR[n].STS} and {@code .ADDR}. Other registers are added separately.
		 */
		private void addGroups(List<Register> group, String baseName, List<Component> out) {
			group.sort(Comparator.comparingLong(Register::offset));
			long stride = group.get(0).dimIncrement();
			int dim = group.get(0).dim();

			List<List<Register>> windows = new ArrayList<>();
			for (Register r : group) {
				List<Register> window = windows.isEmpty() ? null : windows.get(windows.size() - 1);
				if (window == null || r.offset() + r.size() > window.get(0).offset() + stride) {
					window = new ArrayList<>();
					windows.add(window);
				}
				window.add(r);
			}
			for (List<Register> window : windows) {
				GroupNames names = window.size() > 1 ? groupNames(window, windows.size() > 1)
						: null;
				if (names == null) {
					for (Register r : window) {
						expand(r, baseName, out);
					}
					continue;
				}
				long base = window.get(0).offset();
				String typePrefix = baseName + "_" + names.name();
				List<Component> members = new ArrayList<>();
				for (int i = 0; i < window.size(); i++) {
					Register r = window.get(i);
					String typeName = typePrefix + "_" + names.members().get(i);
					members.add(new Component(r.offset(), r.size(), names.members().get(i),
						() -> registerType(r, typeName), comment(r), r.alternate()));
				}
				out.add(new Component(base, (int) (dim * stride), names.name(), () -> {
					StructureDataType element =
						new StructureDataType(category, typeName(typePrefix), (int) stride, dtm);
					place(element, members, base, 0);
					DataType elementType =
						dtm.resolve(element, DataTypeConflictHandler.KEEP_HANDLER);
					return new ArrayDataType(elementType, dim, (int) stride, dtm);
				}, null, false));
			}
		}

		/**
		 * Names a group of registers repeated together: after the part their names share
		 * before {@code %s} (with several groups of that name, plus the suffix they share), or
		 * for names ending in {@code %s}, after the prefix they share up to an underscore. Null
		 * if the registers cannot be told apart that way.
		 */
		private static GroupNames groupNames(List<Register> window, boolean severalWindows) {
			List<String> before = new ArrayList<>();
			List<String> after = new ArrayList<>();
			for (Register r : window) {
				int percent = r.name().indexOf("%s");
				before.add(r.name().substring(0, percent));
				after.add(r.name().substring(percent + 2));
			}
			String name;
			List<String> members = new ArrayList<>();
			if (!after.contains("") && new HashSet<>(before).size() == 1) {
				String suffix = severalWindows ? commonSuffix(after) : "";
				if (after.contains(suffix)) {
					suffix = "";
				}
				name = trimUnderscores(before.get(0) + suffix);
				for (String a : after) {
					members.add(trimUnderscores(a.substring(0, a.length() - suffix.length())));
				}
			}
			else if (new HashSet<>(after).equals(Set.of(""))) {
				String prefix = commonPrefix(before);
				name = trimUnderscores(prefix);
				for (String b : before) {
					members.add(trimUnderscores(b.substring(prefix.length())));
				}
			}
			else {
				return null;
			}
			if (name.isEmpty() || members.contains("") ||
				new HashSet<>(members).size() != members.size()) {
				return null;
			}
			return new GroupNames(name, members);
		}

		/**
		 * Registers the SVD lists one by one as {@code NAME0}, {@code NAME1}, ... at consecutive
		 * addresses, such as INTC's {@code CPR0} and {@code CPR1} (one for each core), as one
		 * array {@code NAME%s}. Code indexes them, for example with the core number, and the
		 * decompiler then shows {@code INTC.CPR[core]} instead of an offset from another
		 * register. Elements whose fields differ, such as the channel masks of the ADC, get no
		 * fields.
		 */
		private static List<Register> numberedArrays(List<Register> registers) {
			Map<String, List<Register>> runs = new LinkedHashMap<>();
			for (Register r : registers) {
				Matcher m = NUMBERED.matcher(r.name());
				if (r.dim() <= 1 && !r.alternate() && m.matches()) {
					runs.computeIfAbsent(m.group(1), k -> new ArrayList<>()).add(r);
				}
			}
			Set<Register> merged = new HashSet<>();
			List<Register> arrays = new ArrayList<>();
			for (Map.Entry<String, List<Register>> run : runs.entrySet()) {
				List<Register> list = run.getValue();
				list.sort(Comparator.comparingLong(Register::offset));
				Register first = list.get(0);
				boolean array = list.size() >= 2;
				for (int i = 0; array && i < list.size(); i++) {
					Register r = list.get(i);
					array = r.name().equals(run.getKey() + i) && r.size() == first.size() &&
						r.offset() == first.offset() + (long) i * first.size();
				}
				if (!array) {
					continue;
				}
				List<String> index = new ArrayList<>();
				Set<List<Field>> fields = new HashSet<>();
				Set<String> descriptions = new LinkedHashSet<>();
				for (int i = 0; i < list.size(); i++) {
					index.add(Integer.toString(i));
					fields.add(list.get(i).fields());
					if (list.get(i).description() != null) {
						descriptions.add(list.get(i).description());
					}
				}
				arrays.add(new Register(run.getKey() + "%s",
					descriptions.isEmpty() ? null : String.join(" / ", descriptions),
					first.offset(), first.size(), list.size(), first.size(), index, false,
					fields.size() == 1 ? first.fields() : List.of()));
				merged.addAll(list);
			}
			if (merged.isEmpty()) {
				return registers;
			}
			List<Register> out = new ArrayList<>();
			for (Register r : registers) {
				if (!merged.contains(r)) {
					out.add(r);
				}
			}
			out.addAll(arrays);
			return out;
		}

		/** Adds each register of an array separately, named with its index. */
		private void expand(Register r, String baseName, List<Component> out) {
			String typeName = baseName + "_" + trimUnderscores(r.name().replace("%s", ""));
			DataType[] type = new DataType[1];
			Supplier<DataType> shared = () -> {
				if (type[0] == null) {
					type[0] = registerType(r, typeName);
				}
				return type[0];
			};
			String name = r.name().contains("%s") ? r.name() : r.name() + "%s";
			for (int i = 0; i < r.dim(); i++) {
				out.add(new Component(r.offset() + i * r.dimIncrement(), r.size(),
					name.replace("%s", r.dimIndex().get(i)), shared, comment(r),
					r.alternate()));
			}
		}

		/**
		 * Places the components that do not overlap in a structure starting at {@code start},
		 * and types the space between them as 4-byte words named by their offset
		 * ({@code field_0x11bc}), counted from {@code nameOffset} before the structure.
		 */
		private static void place(StructureDataType struct, List<Component> components,
				long start, long nameOffset) {
			for (Component c : placeComponents(components, start)) {
				try {
					struct.replaceAtOffset((int) (c.offset() - start), c.type().get(),
						c.length(), c.name(), c.comment());
				}
				catch (IllegalArgumentException e) {
					// does not fit
				}
			}
			for (int offset = 0; offset + 4 <= struct.getLength(); offset += 4) {
				if (isUndefined(struct, offset, 4)) {
					struct.replaceAtOffset(offset, Undefined4DataType.dataType, 4,
						"field_0x" + Long.toHexString(nameOffset + offset), null);
				}
			}
		}

		private static boolean isUndefined(Structure struct, int offset, int length) {
			for (int i = offset; i < offset + length; i++) {
				DataTypeComponent c = struct.getComponentContaining(i);
				if (c == null || c.getDataType() != DataType.DEFAULT) {
					return false;
				}
			}
			return true;
		}

		/**
		 * The components that do not overlap, registers before their alternates; the names of
		 * the others go in the comment of the component they overlap. Duplicate names get a
		 * number.
		 */
		private static List<Component> placeComponents(List<Component> components, long start) {
			List<Component> sorted = new ArrayList<>(components);
			sorted.sort(Comparator.comparing(Component::alternate)
					.thenComparingLong(Component::offset));
			TreeMap<Long, Component> placed = new TreeMap<>();
			Set<String> names = new HashSet<>();
			for (Component c : sorted) {
				if (c.offset() < start || c.length() <= 0) {
					continue;
				}
				Map.Entry<Long, Component> before = placed.floorEntry(c.offset());
				Map.Entry<Long, Component> after = placed.ceilingEntry(c.offset());
				Component overlapped = null;
				if (before != null && before.getKey() + before.getValue().length() > c.offset()) {
					overlapped = before.getValue();
				}
				else if (after != null && after.getKey() < c.offset() + c.length()) {
					overlapped = after.getValue();
				}
				if (overlapped != null) {
					String note = "Also " + c.name() + ".";
					String comment = overlapped.comment() == null ? note
							: overlapped.comment() + " " + note;
					placed.put(overlapped.offset(), new Component(overlapped.offset(),
						overlapped.length(), overlapped.name(), overlapped.type(), comment,
						overlapped.alternate()));
					continue;
				}
				String name = c.name();
				for (int n = 1; !names.add(name); n++) {
					name = c.name() + "_" + n;
				}
				placed.put(c.offset(), new Component(c.offset(), c.length(), name, c.type(),
					c.comment(), c.alternate()));
			}
			return new ArrayList<>(placed.values());
		}

		/** A register's description and the masks of its fields. */
		private static String comment(Register r) {
			StringBuilder sb = new StringBuilder();
			if (r.description() != null) {
				sb.append(r.description());
			}
			if (!r.fields().isEmpty()) {
				sb.append(sb.length() == 0 ? "" : " ").append("Fields:");
				List<Field> fields = new ArrayList<>(r.fields());
				fields.sort(Comparator.comparingInt(Field::bitOffset).reversed());
				for (Field f : fields) {
					long mask = f.bitWidth() >= 64 ? -1L
							: ((1L << f.bitWidth()) - 1) << f.bitOffset();
					sb.append(' ').append(f.name()).append("=0x").append(Long.toHexString(mask));
				}
			}
			return sb.length() == 0 ? null : sb.toString();
		}

		/**
		 * The type of a register: an integer of its size or, with the option, a structure of
		 * its bit fields.
		 *
		 * @param name the name for a bit field type, without {@code _Type}
		 */
		private DataType registerType(Register r, String name) {
			DataType integer = integerType(r.size());
			List<Field> fields = r.fields();
			if (!bitFields || fields.isEmpty() || r.size() > 8 ||
				(fields.size() == 1 && fields.get(0).bitWidth() >= r.size() * 8)) {
				return integer;
			}
			StructureDataType bits =
				new StructureDataType(category, typeName(name), r.size(), dtm);
			for (Field f : fields) {
				if (f.bitOffset() < 0 || f.bitOffset() + f.bitWidth() > r.size() * 8) {
					continue;
				}
				try {
					bits.insertBitFieldAt(0, r.size(), f.bitOffset(), integer, f.bitWidth(),
						f.name(), f.description());
				}
				catch (InvalidDataTypeException | IllegalArgumentException e) {
					// overlapping fields
				}
			}
			if (bits.getLength() != r.size()) {
				return integer;
			}
			return dtm.resolve(bits, DataTypeConflictHandler.KEEP_HANDLER);
		}

		private static DataType integerType(int size) {
			return switch (size) {
				case 1 -> ByteDataType.dataType;
				case 2 -> UnsignedShortDataType.dataType;
				case 4 -> UnsignedIntegerDataType.dataType;
				case 8 -> UnsignedLongLongDataType.dataType;
				default -> Undefined.getUndefinedDataType(size);
			};
		}

		/** A type name not used yet for this device: {@code name_Type}, or with a number. */
		private String typeName(String name) {
			String typeName = name + "_Type";
			for (int n = 1; !typeNames.add(typeName); n++) {
				typeName = name + "_" + n + "_Type";
			}
			return typeName;
		}

		private static boolean isZeroBased(List<String> index) {
			for (int i = 0; i < index.size(); i++) {
				if (!index.get(i).equals(Integer.toString(i))) {
					return false;
				}
			}
			return true;
		}

		/** The longest suffix, from an underscore, that all names share. */
		private static String commonSuffix(List<String> names) {
			String suffix = names.get(0);
			for (String n : names) {
				while (!n.endsWith(suffix)) {
					suffix = suffix.substring(1);
				}
			}
			int underscore = suffix.indexOf('_');
			return underscore < 0 ? "" : suffix.substring(underscore);
		}

		/** The longest prefix, up to an underscore, that all names share. */
		private static String commonPrefix(List<String> names) {
			String prefix = names.get(0);
			for (String n : names) {
				while (!n.startsWith(prefix)) {
					prefix = prefix.substring(0, prefix.length() - 1);
				}
			}
			return prefix.substring(0, prefix.lastIndexOf('_') + 1);
		}

		private static String trimUnderscores(String name) {
			return name.replaceAll("^_+|_+$", "");
		}

		private void label(Address address, String name) {
			SymbolTable symbols = program.getSymbolTable();
			Symbol primary = symbols.getPrimarySymbol(address);
			if (primary != null && primary.getSource() != SourceType.DEFAULT) {
				return;
			}
			try {
				symbols.createLabel(address, name, SourceType.IMPORTED);
			}
			catch (InvalidInputException e) {
				// not a valid name
			}
		}
	}
}
