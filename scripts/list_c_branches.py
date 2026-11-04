#!/usr/bin/env python3
"""List the branch conditions in the C code Lean generates for the
constant-time modules, for manual review.

Usage (after `lake build`):
    python3 scripts/list_c_branches.py

Every `if` in these functions should test public data only: reference counts
(`isSharedCheck`, used for in-place memory reuse), loop counters, table
bounds, public window indices or bits of public exponents. A branch on a limb
value would be a side-channel bug.

This inspects Lean's C output only; the C compiler could still introduce
branches in machine code, so this is not a substitute for checking the binary.
"""

import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent.parent
FILES = ["U256", "Field", "Point"]

for f in FILES:
    path = ROOT / ".lake" / "build" / "ir" / "Secp256k1" / "CT" / f"{f}.c"
    src = path.read_text()
    starts = list(re.finditer(r"^(?:LEAN_EXPORT |static )?[a-z0-9_]+\*? (lp_secp256k1_\w+)\([^)]*\)\{\n_start:", src, re.M))
    for i, m in enumerate(starts):
        name = m.group(1)
        if name.endswith("_boxed"):
            continue
        end = starts[i + 1].start() if i + 1 < len(starts) else len(src)
        lines = src[m.end():end].splitlines()
        branches = []
        for j, line in enumerate(lines):
            if re.match(r"\s*if \(", line):
                # Show the assignment that computed the tested variable.
                var = re.search(r"if \((v_\w+)", line)
                origin = next((l.strip() for l in reversed(lines[:j]) if var and l.strip().startswith(var.group(1) + " =")), "")
                branches.append(re.sub(r"_\d+_", "", origin or line.strip()))
        short = name.replace("lp_secp256k1_Secp256k1_CT_", "")
        print(f"{f}.{short}: " + ("branch-free" if not branches else ""))
        for b in sorted(set(branches)):
            print(f"    if ← {b}")
