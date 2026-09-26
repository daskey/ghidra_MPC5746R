#!/usr/bin/env python3
"""Copy the PowerPC files this module shares with Ghidra.

The e200z4 language includes Ghidra's own PowerPC sources unmodified and adds
everything e200-specific in separate e200_*.sinc files, so syncing is a plain copy.
The extension version is set to the version of that Ghidra.

usage: sync_upstream.py <ghidra-source-or-install-dir> [--check]

  <dir> is a Ghidra source checkout or installation; both contain the PowerPC module
  at Ghidra/Processors/PowerPC. --check only reports differences (exit status 1).
"""
import filecmp
import re
import shutil
import subprocess
import sys
from pathlib import Path

# Paths relative to the module's data directory.
UPSTREAM_FILES = [
    "languages/ppc_common.sinc",
    "languages/ppc_instructions.sinc",
    "languages/ppc_embedded.sinc",
    "languages/ppc_vle.sinc",
    "languages/quicciii.sinc",
    "languages/lmwInstructions.sinc",
    "languages/lswInstructions.sinc",
    "languages/stmwInstructions.sinc",
    "languages/stswiInstructions.sinc",
    "languages/mulhwInstructions.sinc",
    "languages/SPEF_SCR.sinc",  # register definitions only; keeps the 1.7 register set
    "languages/ppc.dwarf",
    "manuals/PowerISA.idx",
]

MODULE = Path("Ghidra/Processors/PowerPC")
DATA = Path(__file__).resolve().parent.parent / "data"
EXTENSION_PROPERTIES = DATA.parent / "extension.properties"


def upstream_revision(root: Path) -> str:
    try:
        out = subprocess.run(["git", "-C", str(root), "log", "-1", "--format=%H %cs",
                              "--", str(MODULE / "data")],
                             capture_output=True, text=True, check=True)
        if out.stdout.strip():
            return out.stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        pass
    props = root / "Ghidra" / "application.properties"
    if props.exists():
        for line in props.read_text().splitlines():
            if line.startswith("application.revision.ghidra="):
                return line.split("=", 1)[1]
    return "unknown"


def ghidra_version(root: Path):
    props = root / "Ghidra" / "application.properties"
    if props.exists():
        for line in props.read_text().splitlines():
            if line.startswith("application.version="):
                return line.split("=", 1)[1].strip()
    return None


def main() -> int:
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    check = "--check" in sys.argv
    if len(args) != 1:
        print(__doc__)
        return 2
    root = Path(args[0])
    src = root / MODULE / "data"
    if not (src / "languages" / "ppc_common.sinc").is_file():
        print(f"not a Ghidra source or installation directory: {root}")
        return 2
    changed = []
    for name in UPSTREAM_FILES:
        dest = DATA / name
        if dest.exists() and filecmp.cmp(src / name, dest, shallow=False):
            continue
        changed.append(name)
        if not check:
            shutil.copyfile(src / name, dest)
    version = ghidra_version(root)
    props = EXTENSION_PROPERTIES.read_text()
    new_props = re.sub(r"(?m)^version=.*$", f"version={version}", props)
    if version and new_props != props:
        changed.append(f"extension.properties (version {version})")
        if not check:
            EXTENSION_PROPERTIES.write_text(new_props, newline="\n")
    rev = upstream_revision(root)
    if not check:
        (DATA / "languages" / "UPSTREAM").write_text(
            "Unmodified copies of Ghidra PowerPC processor files, synced with\n"
            "tools/sync_upstream.py.\n"
            f"Source revision: {rev}\n"
            "Files: " + ", ".join(UPSTREAM_FILES) + "\n", newline="\n")
    print(("out of date: " if check else "updated: ") + (", ".join(changed) or "nothing"))
    print("upstream revision:", rev)
    return 1 if check and changed else 0


if __name__ == "__main__":
    sys.exit(main())
