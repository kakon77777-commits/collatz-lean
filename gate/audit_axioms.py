"""Is anything in this development cheating?

數學戰士「墜衡」 / AMRAL Research Lab.

A Lean file that compiles proves its theorems *relative to what it assumes and
how it is stated*. There are a handful of well-known ways to make a green build
mean nothing, and a reader who has not audited for them is taking the author's
word. This gate audits for them mechanically so nobody has to.

What it refuses:

1. `sorry` anywhere in the sources — a hole the compiler will happily accept
   with only a warning.
2. an `axiom` declaration of our own — assuming the thing instead of proving it.
3. `native_decide`, which discharges goals through the compiler and so trusts
   far more than the kernel.
4. `unsafe`, `@[implemented_by]`, `partial`, `@[extern]` — escapes from the
   logic into runtime behaviour.
5. any theorem whose axiom set is not contained in Lean's own three
   (`propext`, `Classical.choice`, `Quot.sound`). `sorryAx` shows up here, which
   is the backstop for (1).
6. a theorem in the sources that the audit file does not check. Without this the
   audit passes by simply not looking at the new one.

What it cannot do is tell you the theorems say something interesting. That is
what `crosscheck_against_finite_arm.py` and the non-vacuity evaluations in
`Collatz/Audit.lean` are for.

Usage:  python gate/audit_axioms.py
"""

from __future__ import annotations

import json
import pathlib
import re
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent.parent
SRC = HERE / "Collatz"
AUDIT_FILE = SRC / "Audit.lean"

STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

FORBIDDEN = [
    (r"\bsorry\b", "sorry"),
    (r"^\s*axiom\s", "axiom declaration"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bunsafe\b", "unsafe"),
    (r"@\[implemented_by", "@[implemented_by]"),
    (r"@\[extern", "@[extern]"),
    (r"^\s*partial\s+def\b", "partial def"),
]


def main() -> int:
    rep = {
        "tool": "audit_axioms.py",
        "subject": "every theorem in Collatz/*.lean",
        "standard_axioms": sorted(STANDARD_AXIOMS),
        "forbidden_constructs": {}, "theorems": {}, "problems": [],
    }

    sources = sorted(p for p in SRC.glob("*.lean") if p.name != "Audit.lean")
    rep["sources"] = [p.name for p in sources]

    # ---- 1-4: forbidden constructs, by text
    for pat, label in FORBIDDEN:
        hits = []
        for p in sources + [AUDIT_FILE]:
            for i, line in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
                if re.search(pat, line, re.MULTILINE):
                    hits.append(f"{p.name}:{i}")
        rep["forbidden_constructs"][label] = hits
        if hits:
            rep["problems"].append(f"{label} present at {hits[:5]}")

    # ---- 6: every theorem in the sources must be audited
    declared = []
    for p in sources:
        for m in re.finditer(r"^\s*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'₂]*)",
                             p.read_text(encoding="utf-8"), re.MULTILINE):
            declared.append(m.group(1))
    audit_src = AUDIT_FILE.read_text(encoding="utf-8")
    audited = set(re.findall(r"#print axioms\s+(?:Collatz\.)?([A-Za-z_][A-Za-z0-9_'₂]*)",
                             audit_src))
    unaudited = sorted(set(declared) - audited)
    rep["theorems_declared"] = sorted(set(declared))
    rep["theorems_audited"] = sorted(audited)
    if unaudited:
        rep["problems"].append(f"theorem(s) with no `#print axioms`: {unaudited}")

    # ---- 5: the axiom sets themselves
    p = subprocess.run(["lake", "env", "lean", str(AUDIT_FILE)], cwd=str(HERE),
                       capture_output=True, text=True, encoding="utf-8",
                       errors="replace", timeout=3600)
    out = p.stdout + p.stderr
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out)
    if not found:
        rep["problems"].append("no axiom lines parsed from the audit file")
    for name, axs in found:
        used = {a.strip() for a in axs.split(",") if a.strip()}
        extra = sorted(used - STANDARD_AXIOMS)
        rep["theorems"][name] = {"axioms": sorted(used), "beyond_standard": extra}
        if extra:
            rep["problems"].append(f"{name} depends on {extra}")
    # a theorem that does not appear in the output at all was never checked
    missing = sorted(a for a in audited
                     if not any(n.endswith("." + a) or n == a for n, _ in found))
    if missing:
        rep["problems"].append(f"audited but produced no axiom line: {missing}")

    rep["counts"] = {
        "sources": len(sources),
        "theorems_declared": len(set(declared)),
        "theorems_with_axiom_line": len(found),
        "theorems_beyond_standard_axioms":
            sum(1 for v in rep["theorems"].values() if v["beyond_standard"]),
        "forbidden_construct_hits": sum(len(v) for v in rep["forbidden_constructs"].values()),
        "problems": len(rep["problems"]),
    }
    rep["ok"] = not rep["problems"]
    json.dump(rep, sys.stdout, indent=2, ensure_ascii=False)
    print()
    return 0 if rep["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
