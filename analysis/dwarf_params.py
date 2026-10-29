#!/usr/bin/env python3
"""dwarf_params.py ELF OUT.json: the parameters of each function with their DWARF locations at the
function's entry: a register number (DW_OP_regN, or the first entry of a location list), 'stack'
(fbreg/bregN), or 'none'."""
import json, sys
from elftools.elf.elffile import ELFFile
from elftools.dwarf.locationlists import LocationEntry
from elftools.dwarf.descriptions import describe_DWARF_expr
from elftools.dwarf.dwarf_expr import DWARFExprParser


def location(die, dwarf, cu, parser, loclists):
    a = die.attributes.get('DW_AT_location')
    if a is None:
        return 'none'
    if a.form in ('DW_FORM_exprloc', 'DW_FORM_block1', 'DW_FORM_block', 'DW_FORM_block2', 'DW_FORM_block4'):
        return decode(a.value, parser)
    # a location list: the first entry (at the function's entry)
    try:
        entries = loclists.get_location_list_at_offset(a.value, die)
    except Exception:
        return 'none'
    for e in entries:
        if isinstance(e, LocationEntry):
            return decode(e.loc_expr, parser)
    return 'none'


def decode(expr, parser):
    try:
        ops = parser.parse_expr(expr)
    except Exception:
        return 'none'
    if not ops:
        return 'none'
    op = ops[0].op_name
    if op.startswith('DW_OP_reg') and op != 'DW_OP_regx':
        return int(op[len('DW_OP_reg'):])
    if op == 'DW_OP_regx':
        return int(ops[0].args[0])
    if op.startswith('DW_OP_breg') or op == 'DW_OP_fbreg':
        return 'stack'
    return op


def main():
    elf = ELFFile(open(sys.argv[1], 'rb'))
    dwarf = elf.get_dwarf_info()
    loclists = dwarf.location_lists()
    out = []
    for cu in dwarf.iter_CUs():
        parser = DWARFExprParser(cu.structs)
        for die in cu.iter_DIEs():
            if die.tag != 'DW_TAG_subprogram' or 'DW_AT_low_pc' not in die.attributes:
                continue
            params = []
            for child in die.iter_children():
                if child.tag == 'DW_TAG_formal_parameter':
                    name = child.attributes['DW_AT_name'].value.decode('latin-1') if 'DW_AT_name' in child.attributes else None
                    params.append({'name': name, 'loc': location(child, dwarf, cu, parser, loclists)})
            name = die.attributes['DW_AT_name'].value.decode('latin-1') if 'DW_AT_name' in die.attributes else None
            out.append({'low': die.attributes['DW_AT_low_pc'].value, 'name': name, 'params': params})
    json.dump(out, open(sys.argv[2], 'w'))
    locs = [p['loc'] for f in out for p in f['params']]
    from collections import Counter
    print(len(out), 'functions,', len(locs), 'params; locations:', Counter(str(l) if not isinstance(l, int) else 'reg' for l in locs).most_common(8))


if __name__ == '__main__':
    main()
