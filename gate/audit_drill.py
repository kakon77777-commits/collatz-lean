"""Can the anti-cheating audit actually catch cheating?

數學戰士「墜衡」 / AMRAL Research Lab.

`audit_axioms.py` exists so a reader does not have to take the author's word
that nothing is faked. That only helps if the audit itself can fail. So each way
of cheating it claims to detect is planted in the sources in turn, and the audit
must go red **for the reason named** — not merely go red.

An audit nobody has ever seen fail is a green light with no bulb behind it.

The mutations happen in place, because the audit needs the project's `.lake`
build tree and copying that would mean rebuilding mathlib. Every write is
byte-level and restored under `try/finally`, and each restore is checked for
byte equality before the result is recorded: a drill that corrupts the tree it
audits is a bad drill, and the first version of this file did exactly that by
round-tripping through `write_text`, which rewrites newlines on Windows.

Usage:  python gate/audit_drill.py
"""

from __future__ import annotations

import json
import os
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent.parent

# (name, file, old, new, substring that must appear in the reported problem)
DEFECTS = [
    ("D1_a_theorem_is_closed_with_sorry", "Collatz/AllOnes.lean",
     "  rw [hK]\n  exact Nat.pow_lt_pow_left (by norm_num) (by omega)",
     "  rw [hK]\n  sorry", "sorry"),
    ("D2_a_result_is_assumed_as_an_axiom", "Collatz/AllOnes.lean",
     "/-! ## The no-go -/",
     "axiom cheat : ∀ n : ℕ, n = n\n\n/-! ## The no-go -/", "axiom"),
    ("D3_a_goal_is_discharged_by_native_decide", "Collatz/AllOnes.lean",
     "  have hm : m + 1 - m = 1 := by omega",
     "  have hm : m + 1 - m = 1 := by first | native_decide | omega", "native_decide"),
    ("D4_a_new_theorem_escapes_the_axiom_audit", "Collatz/AllOnes.lean",
     "/-! ## The no-go -/",
     "theorem unaudited_addition (n : ℕ) : n + 0 = n := by simp\n\n/-! ## The no-go -/",
     "no `#print axioms`"),
    ("D5_the_audit_file_stops_checking_a_theorem", "Collatz/Audit.lean",
     "#print axioms finite_local_no_go\n", "", "no `#print axioms`"),
    ("D6_a_definition_is_made_partial", "Collatz/AllOnes.lean",
     "def kappa (n : ℕ) : ℕ := v₂ (3 * n + 1)",
     "partial def kappa (n : ℕ) : ℕ := v₂ (3 * n + 1)", "partial def"),
    # D7 exists because D4 did not catch what it was aimed at. D4 plants a BARE
    # `theorem`, and the coverage scan's regex required `theorem` to be the first
    # word on the line -- so the attribute-prefixed path was never drilled, and
    # 22 real `@[simp]` lemmas sat unaudited while the gate reported `ok`. The
    # defect is planted in the newest file as well, since every other source
    # defect lives in AllOnes.lean and the file axis was unexercised.
    ("D7_an_attributed_theorem_escapes_the_axiom_audit", "Collatz/AnchoredBranch.lean",
     "/-! ## §42, §44: canonical residues of a chain -/",
     "@[simp] theorem unaudited_with_attribute (n : ℕ) : n * 1 = n := by simp\n\n"
     "/-! ## §42, §44: canonical residues of a chain -/",
     "no `#print axioms`"),
    # D8 attacks the reconciliation itself. Once the gate compares declared
    # against audited, the cheapest way to defeat it is to pad the audited side
    # with theorems you did not prove: `#print axioms` on a mathlib lemma
    # compiles, raises the count, and lets the two totals meet while your own
    # theorem stays unchecked. The reverse check is what refuses that, so it gets
    # a defect naming it.
    ("D8_the_audit_pads_its_count_with_a_mathlib_theorem", "Collatz/Audit.lean",
     "namespace Collatz\n",
     "namespace Collatz\n\n#print axioms Nat.succ_le_succ\n",
     "with no declaration in the sources"),
]

TOUCHED = sorted({d[1] for d in DEFECTS})


def run_audit() -> dict:
    p = subprocess.run([sys.executable, str(HERE / "gate" / "audit_axioms.py")],
                       cwd=str(HERE), capture_output=True, text=True,
                       encoding="utf-8", errors="replace", timeout=3600,
                       env={**os.environ, "PYTHONUTF8": "1"})
    try:
        return json.loads(p.stdout)
    except json.JSONDecodeError:
        return {"ok": False, "problems": ["audit crashed"],
                "_crash": (p.stdout + p.stderr)[-400:]}


def main() -> int:
    rep = {"tool": "audit_drill.py", "subject": "gate/audit_axioms.py",
           "defects": {}, "controls": {}}

    baseline = run_audit()
    if not baseline.get("ok"):
        print(json.dumps({"error": "baseline audit is not green",
                          "problems": baseline.get("problems")},
                         indent=2, ensure_ascii=False))
        return 2
    rep["baseline"] = {"theorems": baseline["counts"]["theorems_declared"]}

    # The mutations happen in place, so an interrupted run can leave one behind —
    # and the byte-exact-restore control below baselines on the tree as it is when
    # the drill STARTS, so a leftover would be restored faithfully and the control
    # would report success with the defect still in the sources.
    #
    # An explicit "is any planted form already present?" guard was written here for
    # that, and then removed: it is UNREACHABLE. Every defect in DEFECTS is by
    # construction something `audit_axioms.py` refuses, so a leftover makes the
    # baseline above red and the drill has already returned. A check that cannot
    # fail is worse than no check, and this file exists to say so.
    #
    # What the baseline does NOT cover is a leftover the audit considers harmless —
    # the N1 control appends a comment, and an interruption there leaves a stray
    # comment with the baseline still green. That is recorded rather than guarded,
    # because a guard would have to distinguish it from ordinary uncommitted work.
    snapshot = {r: (HERE / r).read_bytes() for r in TOUCHED}

    for name, rel, old, new, expect in DEFECTS:
        f = HERE / rel
        raw = f.read_bytes()
        text = raw.decode("utf-8")
        if text.count(old) != 1:
            rep["defects"][name] = {
                "caught": False,
                "note": f"anchor matched {text.count(old)} times in {rel}"}
            continue
        try:
            f.write_bytes(text.replace(old, new, 1).encode("utf-8"))
            res = run_audit()
        finally:
            f.write_bytes(raw)
        if f.read_bytes() != raw:
            rep["defects"][name] = {
                "caught": False, "note": f"{rel} was not restored byte-exactly"}
            continue
        problems = " | ".join(res.get("problems", []))
        rep["defects"][name] = {
            "caught": (not res.get("ok")) and expect in problems,
            "expected_substring": expect,
            "reported": res.get("problems", [])[:3]}

    # N1 — a comment must not be a problem, or the audit is simply always-red
    f = HERE / "Collatz/AllOnes.lean"
    raw = f.read_bytes()
    try:
        f.write_bytes(raw + b"\n-- a comment nothing reads\n")
        res = run_audit()
    finally:
        f.write_bytes(raw)
    rep["controls"]["N1_a_comment_is_not_a_problem"] = {
        "undisturbed": bool(res.get("ok"))}

    # N2 — every touched source is byte-identical to how the drill found it
    restored = {r: (HERE / r).read_bytes() == b for r, b in snapshot.items()}
    rep["controls"]["N2_every_source_restored_byte_exactly"] = {
        "undisturbed": all(restored.values()) and run_audit().get("ok") is True,
        "per_file": restored}

    caught = sum(1 for v in rep["defects"].values() if v["caught"])
    quiet = sum(1 for v in rep["controls"].values() if v["undisturbed"])
    rep["counts"] = {"defects_planted": len(rep["defects"]), "caught": caught,
                     "controls": len(rep["controls"]),
                     "controls_undisturbed": quiet}
    rep["ok"] = caught == len(rep["defects"]) and quiet == len(rep["controls"])
    json.dump(rep, sys.stdout, indent=2, ensure_ascii=False)
    print()
    return 0 if rep["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
