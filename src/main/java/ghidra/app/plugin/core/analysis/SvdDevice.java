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

import java.io.IOException;
import java.io.InputStream;
import java.util.*;

import javax.xml.XMLConstants;
import javax.xml.parsers.*;

import org.w3c.dom.*;
import org.xml.sax.SAXException;

/**
 * The peripherals of a device, read from a CMSIS-SVD file. Derived peripherals are resolved;
 * clusters are flattened into registers whose names join the cluster and register names, with
 * the cluster's array dimension.
 */
final class SvdDevice {

	/** A bit field of a register; {@code bitOffset} counts from the least significant bit. */
	record Field(String name, String description, int bitOffset, int bitWidth) {}

	/**
	 * A register, or with {@code dim > 1} an array of registers {@code dimIncrement} bytes
	 * apart, whose name then contains {@code %s} where the index goes.
	 *
	 * @param offset offset from the peripheral base address
	 * @param size size in bytes
	 * @param alternate whether this is an alternate view of another register
	 */
	record Register(String name, String description, long offset, int size, int dim,
			long dimIncrement, List<String> dimIndex, boolean alternate, List<Field> fields) {}

	/** An address block of a peripheral: offset from the base address and size in bytes. */
	record AddressBlock(long offset, long size) {}

	record Peripheral(String name, String description, String groupName, long baseAddress,
			List<AddressBlock> addressBlocks, List<Register> registers) {}

	final String name;
	final List<Peripheral> peripherals;

	private SvdDevice(String name, List<Peripheral> peripherals) {
		this.name = name;
		this.peripherals = peripherals;
	}

	static SvdDevice read(InputStream in) throws IOException {
		Document document;
		try {
			DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
			factory.setFeature(XMLConstants.FEATURE_SECURE_PROCESSING, true);
			factory.setFeature("http://apache.org/xml/features/disallow-doctype-decl", true);
			factory.setExpandEntityReferences(false);
			document = factory.newDocumentBuilder().parse(in);
		}
		catch (ParserConfigurationException | SAXException e) {
			throw new IOException("Not a valid SVD file: " + e.getMessage(), e);
		}
		Element device = document.getDocumentElement();
		if (!"device".equals(device.getTagName())) {
			throw new IOException("Not an SVD file: the root element is not <device>");
		}
		int defaultSize = (int) number(text(device, "size"), 32);

		Map<String, Element> byName = new HashMap<>();
		List<Element> elements = children(child(device, "peripherals"), "peripheral");
		for (Element p : elements) {
			byName.put(text(p, "name"), p);
		}
		List<Peripheral> peripherals = new ArrayList<>();
		for (Element p : elements) {
			Element base = byName.get(p.getAttribute("derivedFrom"));
			int size = (int) number(inherited(p, base, "size"), defaultSize);

			List<AddressBlock> blocks = new ArrayList<>();
			List<Element> blockElements = children(p, "addressBlock");
			if (blockElements.isEmpty() && base != null) {
				blockElements = children(base, "addressBlock");
			}
			for (Element b : blockElements) {
				blocks.add(new AddressBlock(number(text(b, "offset"), 0),
					number(text(b, "size"), 0)));
			}

			List<Register> registers = new ArrayList<>();
			Element registersElement = child(p, "registers");
			if (registersElement == null && base != null) {
				registersElement = child(base, "registers");
			}
			if (registersElement != null) {
				readRegisters(registersElement, "", 0, size, null, registers);
			}
			peripherals.add(new Peripheral(text(p, "name"), inherited(p, base, "description"),
				inherited(p, base, "groupName"), number(text(p, "baseAddress"), 0), blocks,
				registers));
		}
		return new SvdDevice(text(device, "name"), peripherals);
	}

	/** Array dimension of an enclosing cluster. */
	private record Dim(int dim, long increment, List<String> index) {}

	/**
	 * Reads the registers and clusters of a {@code <registers>} or {@code <cluster>} element.
	 *
	 * @param prefix name prefix from enclosing clusters
	 * @param baseOffset offset of the enclosing cluster
	 * @param clusterDim array dimension of the enclosing cluster, or null
	 */
	private static void readRegisters(Element parent, String prefix, long baseOffset,
			int defaultSize, Dim clusterDim, List<Register> out) {
		Map<String, Element> siblings = new HashMap<>();
		for (Element r : children(parent, "register")) {
			siblings.put(text(r, "name"), r);
		}
		for (Element e : children(parent, null)) {
			switch (e.getTagName()) {
				case "register" -> readRegister(e, siblings, prefix, baseOffset, defaultSize,
					clusterDim, out);
				case "cluster" -> readCluster(e, prefix, baseOffset, defaultSize, clusterDim,
					out);
				default -> {
					// description and other elements
				}
			}
		}
	}

	private static void readRegister(Element r, Map<String, Element> siblings, String prefix,
			long baseOffset, int defaultSize, Dim clusterDim, List<Register> out) {
		Element base = siblings.get(r.getAttribute("derivedFrom"));
		String name = arrayName(text(r, "name"));
		String description = inherited(r, base, "description");
		long offset = baseOffset + number(text(r, "addressOffset"), 0);
		int size = (int) number(inherited(r, base, "size"), defaultSize) / 8;
		boolean alternate = inherited(r, base, "alternateGroup") != null ||
			inherited(r, base, "alternateRegister") != null;
		Element fieldsElement = child(r, "fields");
		if (fieldsElement == null && base != null) {
			fieldsElement = child(base, "fields");
		}
		List<Field> fields = readFields(fieldsElement);
		Dim dim = dim(r);
		if (dim != null && dim.increment() == 0) {
			dim = new Dim(dim.dim(), size, dim.index());
		}

		if (clusterDim == null) {
			if (dim == null) {
				out.add(new Register(prefix + name, description, offset, size, 1, size, List.of(),
					alternate, fields));
			}
			else {
				out.add(new Register(prefix + name, description, offset, size, dim.dim(),
					dim.increment(), dim.index(), alternate, fields));
			}
			return;
		}
		// in an array of clusters: an array of registers inside it becomes separate registers
		List<String> names = new ArrayList<>();
		List<Long> offsets = new ArrayList<>();
		if (dim == null) {
			names.add(name);
			offsets.add(offset);
		}
		else {
			for (int i = 0; i < dim.dim(); i++) {
				names.add(name.replace("%s", dim.index().get(i)));
				offsets.add(offset + i * dim.increment());
			}
		}
		for (int i = 0; i < names.size(); i++) {
			out.add(new Register(prefix + names.get(i), description, offsets.get(i), size,
				clusterDim.dim(), clusterDim.increment(), clusterDim.index(), alternate, fields));
		}
	}

	private static void readCluster(Element c, String prefix, long baseOffset, int defaultSize,
			Dim clusterDim, List<Register> out) {
		String name = arrayName(text(c, "name"));
		long offset = baseOffset + number(text(c, "addressOffset"), 0);
		int size = (int) number(text(c, "size"), defaultSize);
		Dim dim = dim(c);
		if (dim == null) {
			readRegisters(c, prefix + name + "_", offset, size, clusterDim, out);
		}
		else if (clusterDim == null) {
			readRegisters(c, prefix + name + "_", offset, size, dim, out);
		}
		else {
			// an array of clusters inside an array of clusters: expand the inner one
			for (int i = 0; i < dim.dim(); i++) {
				readRegisters(c, prefix + name.replace("%s", dim.index().get(i)) + "_",
					offset + i * dim.increment(), size, clusterDim, out);
			}
		}
	}

	private static List<Field> readFields(Element fieldsElement) {
		List<Field> fields = new ArrayList<>();
		if (fieldsElement == null) {
			return fields;
		}
		for (Element f : children(fieldsElement, "field")) {
			int lsb;
			int width;
			String bitRange = text(f, "bitRange");
			if (text(f, "bitOffset") != null) {
				lsb = (int) number(text(f, "bitOffset"), 0);
				width = (int) number(text(f, "bitWidth"), 1);
			}
			else if (text(f, "lsb") != null) {
				lsb = (int) number(text(f, "lsb"), 0);
				width = (int) number(text(f, "msb"), lsb) - lsb + 1;
			}
			else if (bitRange != null && bitRange.matches("\\[\\s*\\w+\\s*:\\s*\\w+\\s*]")) {
				String[] parts = bitRange.replaceAll("[\\[\\]\\s]", "").split(":");
				lsb = (int) number(parts[1], 0);
				width = (int) number(parts[0], lsb) - lsb + 1;
			}
			else {
				continue;
			}
			if (width > 0) {
				fields.add(new Field(text(f, "name"), text(f, "description"), lsb, width));
			}
		}
		return fields;
	}

	private static Dim dim(Element e) {
		String dimText = text(e, "dim");
		if (dimText == null) {
			return null;
		}
		int dim = (int) number(dimText, 1);
		if (dim < 1) {
			return null;
		}
		long increment = number(text(e, "dimIncrement"), 0);
		List<String> index = dimIndex(text(e, "dimIndex"), dim);
		return new Dim(dim, increment, index);
	}

	/** The indexes of an array: {@code 0-3}, {@code A-D} or {@code a,b,c}; 0.. by default. */
	private static List<String> dimIndex(String text, int dim) {
		List<String> index = new ArrayList<>();
		if (text != null) {
			String t = text.replaceAll("\\s", "");
			if (t.matches("\\d+-\\d+")) {
				String[] parts = t.split("-");
				for (int i = Integer.parseInt(parts[0]); i <= Integer.parseInt(parts[1]); i++) {
					index.add(Integer.toString(i));
				}
			}
			else if (t.matches("[A-Za-z]-[A-Za-z]")) {
				for (char ch = t.charAt(0); ch <= t.charAt(2); ch++) {
					index.add(Character.toString(ch));
				}
			}
			else {
				index.addAll(Arrays.asList(t.split(",")));
			}
		}
		if (index.size() != dim) {
			index.clear();
			for (int i = 0; i < dim; i++) {
				index.add(Integer.toString(i));
			}
		}
		return index;
	}

	/** Writes array names such as {@code MSCR[%s]} as {@code MSCR%s}. */
	private static String arrayName(String name) {
		return name == null ? "" : name.replace("[%s]", "%s");
	}

	/**
	 * A scaled non-negative integer as SVD writes them: decimal, {@code 0x} hexadecimal or
	 * {@code #} binary, optionally followed by k, M, G or T.
	 */
	static long number(String text, long defaultValue) {
		if (text == null || text.isBlank()) {
			return defaultValue;
		}
		String t = text.trim();
		long scale = 1;
		char last = Character.toUpperCase(t.charAt(t.length() - 1));
		if (!t.startsWith("0x") && !t.startsWith("0X") && "KMGT".indexOf(last) >= 0) {
			scale = 1L << (10 * ("KMGT".indexOf(last) + 1));
			t = t.substring(0, t.length() - 1);
		}
		try {
			long value;
			if (t.startsWith("0x") || t.startsWith("0X")) {
				value = Long.parseUnsignedLong(t.substring(2), 16);
			}
			else if (t.startsWith("#")) {
				value = Long.parseUnsignedLong(t.substring(1), 2);
			}
			else {
				value = Long.parseLong(t);
			}
			return value * scale;
		}
		catch (NumberFormatException e) {
			return defaultValue;
		}
	}

	private static String inherited(Element e, Element base, String tag) {
		String value = text(e, tag);
		return value == null && base != null ? text(base, tag) : value;
	}

	/** The trimmed text of the child element with the given tag, or null. */
	private static String text(Element e, String tag) {
		Element c = child(e, tag);
		if (c == null) {
			return null;
		}
		String t = c.getTextContent().trim().replaceAll("\\s+", " ");
		return t.isEmpty() ? null : t;
	}

	private static Element child(Element e, String tag) {
		if (e == null) {
			return null;
		}
		for (Node n = e.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n instanceof Element c && c.getTagName().equals(tag)) {
				return c;
			}
		}
		return null;
	}

	/** The child elements with the given tag, or all child elements if the tag is null. */
	private static List<Element> children(Element e, String tag) {
		List<Element> list = new ArrayList<>();
		if (e == null) {
			return list;
		}
		for (Node n = e.getFirstChild(); n != null; n = n.getNextSibling()) {
			if (n instanceof Element c && (tag == null || c.getTagName().equals(tag))) {
				list.add(c);
			}
		}
		return list;
	}
}
