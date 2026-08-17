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
    #
    # The scan is textual, so prose inside a docstring can masquerade as a
    # declaration: a line beginning "theorem had `c + 1` and was not true"
    # matched, and the audit then demanded an axiom line for a theorem named
    # `had`. It erred safe — a phantom name makes the audit refuse rather than
    # pass — but it would block honest work, so comments are stripped first.
    def strip_comments(src: str) -> str:
        out, i, depth = [], 0, 0
        while i < len(src):
            if src.startswith("/-", i):
                depth += 1
                i += 2
            elif src.startswith("-/", i) and depth:
                depth -= 1
                i += 2
            elif depth:
                i += 1
            elif src.startswith("--", i):
                j = src.find("\n", i)
                i = len(src) if j < 0 else j
            else:
                out.append(src[i])
                i += 1
        return "".join(out)

    # The first version of this regex required `theorem`/`lemma` to be the first
    # word on the line, so every declaration carrying an attribute —
    # `@[simp] theorem M_D` and seven others — was INVISIBLE to the coverage
    # scan. All eight happened to be audited anyway, so the gate passed; but a
    # future `@[simp] theorem` with no axiom line would also have passed, which
    # is a check that cannot fail for a whole class of declarations. Attributes
    # and modifiers are consumed now, and the reverse direction is checked below
    # so that a hole like this shows up as an arithmetic mismatch rather than as
    # silence.
    MODIFIERS = r"(?:@\[[^\]]*\]\s*|private\s+|protected\s+|nonrec\s+|noncomputable\s+)*"
    NAME = r"([A-Za-z_][A-Za-z0-9_.'₂]*)"
    DECL = r"(?:theorem|lemma)"
    ANY_DECL = r"(?:theorem|lemma|def|abbrev|instance|structure|inductive)"

    # Comparing on the LAST component made two theorems in different namespaces
    # into one member: `Collatz.Atlas.affine_closure` and
    # `Collatz.Domains.affine_closure` are different theorems, and either could
    # have gone unaudited while the other covered for it. Namespaces exist so that
    # a short name may repeat, so the fix is to qualify rather than to rename.
    #
    # The namespace stack has to distinguish `namespace X` from `section X`,
    # because `end X` must pop the right one — a section name popping a namespace
    # would silently shorten every name after it.
    def qualified_decls(code: str, pattern: str) -> list[str]:
        names, stack = [], []
        for line in code.splitlines():
            m = re.match(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)", line)
            if m:
                stack.append(("ns", m.group(1)))
                continue
            m = re.match(r"^section(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?\s*$", line)
            if m:
                stack.append(("sec", m.group(1)))
                continue
            m = re.match(r"^end(?:\s+([A-Za-z_][A-Za-z0-9_.']*))?\s*$", line)
            if m:
                want = m.group(1)
                for i in range(len(stack) - 1, -1, -1):
                    if stack[i][1] == want:
                        del stack[i]
                        break
                else:
                    if stack:
                        stack.pop()
                continue
            m = re.match(r"^\s*" + MODIFIERS + pattern + r"\s+" + NAME, line)
            if m:
                prefix = ".".join(n for k, n in stack if k == "ns")
                names.append(f"{prefix}.{m.group(1)}" if prefix else m.group(1))
        return names

    declared, declared_any = [], []
    for p in sources:
        code = strip_comments(p.read_text(encoding="utf-8"))
        declared += qualified_decls(code, DECL)
        declared_any += qualified_decls(code, ANY_DECL)

    audit_src = AUDIT_FILE.read_text(encoding="utf-8")
    audit_lines = re.findall(
        r"#print axioms\s+([A-Za-z_][A-Za-z0-9_.'₂]*)", strip_comments(audit_src))
    audited = set(audit_lines)
    # Every audit line must be written FULLY QUALIFIED. Lean would resolve a short
    # name against the enclosing namespace, but emulating its resolver is a second
    # implementation of something subtle, and requiring the qualified form makes
    # the comparison exact and checkable by eye.
    unaudited = sorted(set(declared) - audited)
    rep["theorems_declared"] = sorted(set(declared))
    rep["theorems_audited"] = sorted(audited)
    if unaudited:
        rep["problems"].append(f"theorem(s) with no `#print axioms`: {unaudited}")

    # A repeated audit line is harmless but it is a symptom: it used to be the
    # only visible trace of the last-component collision, showing up as an
    # audited count one higher than the declared count.
    dupes = sorted({n for n in audit_lines if audit_lines.count(n) > 1})
    rep["duplicated_audit_lines"] = dupes

    # Reverse direction: every audited name must name a real declaration in the
    # sources. This is what makes the forward check non-vacuous — if the
    # declaration scan goes blind again, the audited set stops being a subset and
    # the gate refuses instead of quietly demanding nothing.
    phantom = sorted(audited - set(declared_any))
    rep["audited_names_with_no_declaration"] = phantom
    if phantom:
        rep["problems"].append(
            f"`#print axioms` names with no declaration in the sources: {phantom}")

    # ---- 5: the axiom sets themselves
    p = subprocess.run(["lake", "env", "lean", str(AUDIT_FILE)], cwd=str(HERE),
                       capture_output=True, text=True, encoding="utf-8",
                       errors="replace", timeout=3600)
    out = p.stdout + p.stderr

    # The audit file must COMPILE. This gate read its output and never checked
    # that, and the file had been carrying two errors: `open X in section Y` is
    # malformed, and a non-vacuity `#eval` used `Nat.rec` with no motive. The
    # second is the one that matters — a non-vacuity check that fails to elaborate
    # is a check that is not running, and every `#print axioms` around it still
    # printed, so the gate reported success. Errors elsewhere in the file are
    # equally invisible to a parser that only looks for the lines it wants.
    audit_errors = [ln for ln in out.splitlines()
                    if re.search(r":\d+:\d+: error", ln)]
    rep["audit_file_errors"] = audit_errors[:10]
    if audit_errors:
        rep["problems"].append(
            f"the audit file does not compile cleanly: {len(audit_errors)} "
            f"error line(s), first: {audit_errors[0][:200]}")

    # `#print axioms` has TWO output forms, and reading only the first means a
    # theorem that depends on NO axioms is reported as never checked.
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out)
    found += [(n, "") for n in
              re.findall(r"'([^']+)' does not depend on any axioms", out)]
    if not found:
        rep["problems"].append("no axiom lines parsed from the audit file")
    for full_name, axs in found:
        name = full_name
        used = {a.strip() for a in axs.split(",") if a.strip()}
        extra = sorted(used - STANDARD_AXIOMS)
        rep["theorems"][name] = {"axioms": sorted(used), "beyond_standard": extra}
        if extra:
            rep["problems"].append(f"{name} depends on {extra}")
    # a theorem that does not appear in the output at all was never checked.
    # Lean prints the fully qualified name, and the audited set is qualified too,
    # so this must NOT strip to the last component — doing so was the same
    # collision that let two `affine_closure`s count as one.
    reported = {n for n, _ in found}
    missing = sorted(audited - reported)
    if missing:
        rep["problems"].append(f"audited but produced no axiom line: {missing}")

    rep["counts"] = {
        "sources": len(sources),
        "theorems_declared": len(set(declared)),
        # unique NAMES, not output lines: a repeated `#print axioms` used to push
        # this above the declared count, which is a figure nobody could re-derive
        "theorems_with_axiom_line": len({n for n, _ in found}),
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
