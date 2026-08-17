"""Emit the gate counts into the README, so no count is ever typed by hand.

數學戰士「墜衡」 / AMRAL Research Lab.

Every number this repository reports about its own gates used to be prose: "six
ways of cheating", "95 theorems", "six fronts". A number typed into a paragraph
is checked by nothing, and all three of those went stale the moment a gate grew —
the drill reached eight defects and the cross-check a seventh front while the
README still said six of each. That is not a wording slip; it is a figure whose
only artefact is prose, which cannot fail.

So the counts are removed from the prose and generated here instead. This script
runs all three gates, refuses if any of them is red, and rewrites the block
between the two markers in `README.md`. The README's argument stays in prose; its
arithmetic comes from the run.

Usage:  python gate/emit_gate_summary.py          # rewrite the block
        python gate/emit_gate_summary.py --check  # fail if it is out of date
"""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys

HERE = pathlib.Path(__file__).resolve().parent.parent
README = HERE / "README.md"
BEGIN = "<!-- BEGIN GENERATED gate counts: python gate/emit_gate_summary.py -->"
END = "<!-- END GENERATED gate counts -->"

GATES = [
    ("audit_axioms.py", "gate/audit_axioms.py"),
    ("audit_drill.py", "gate/audit_drill.py"),
    ("crosscheck_against_finite_arm.py", "gate/crosscheck_against_finite_arm.py"),
]


def run(rel: str) -> dict:
    p = subprocess.run([sys.executable, str(HERE / rel)], cwd=str(HERE),
                       capture_output=True, text=True, encoding="utf-8",
                       errors="replace", timeout=7200)
    try:
        return json.loads(p.stdout)
    except json.JSONDecodeError:
        raise SystemExit(json.dumps(
            {"error": f"{rel} did not produce JSON", "returncode": p.returncode,
             "tail": (p.stdout + p.stderr)[-1500:]}, indent=2))


def build_block(reports: dict[str, dict]) -> str:
    ax = reports["audit_axioms.py"]
    dr = reports["audit_drill.py"]
    xc = reports["crosscheck_against_finite_arm.py"]

    rows: list[tuple[str, str, object]] = [
        ("1. nothing assumed away", "theorems in the sources",
         ax["counts"]["theorems_declared"]),
        ("", "of those, with a `#print axioms` line",
         ax["counts"]["theorems_with_axiom_line"]),
        ("", "theorems needing an axiom beyond Lean's three",
         ax["counts"]["theorems_beyond_standard_axioms"]),
        ("", "`sorry` / private `axiom` / `native_decide` / `partial def` hits",
         ax["counts"]["forbidden_construct_hits"]),
        ("", "`#print axioms` lines naming no real declaration",
         len(ax.get("audited_names_with_no_declaration", []))),
        ("2. the audit can fail", "ways of cheating planted",
         dr["counts"]["defects_planted"]),
        ("", "caught, each for the reason named", dr["counts"]["caught"]),
        ("", "null controls that must stay undisturbed",
         dr["counts"]["controls_undisturbed"]),
        ("3. the definitions are the right objects",
         "accelerated exponent values compared",
         xc["counts"]["kappa_values_compared"]),
        ("", "accelerated orbit values compared",
         xc["counts"]["orbit_values_compared"]),
        ("", f"atlas words, exhaustive to length {xc['atlas']['max_word_length']}",
         xc["counts"]["atlas_words_compared"]),
        ("", "generalised `mx + r` word comparisons",
         xc["counts"]["generalized_words_compared"]),
        ("", f"integers whose parity word is compared, to depth "
             f"{xc['cylinder']['max_depth']}",
         xc["counts"]["cylinder_integers_compared"]),
        ("", "odd starts whose valuation word is compared",
         xc["counts"]["valuation_starts_compared"]),
        # half-open: the gate compares [lo, hi), and rendering the JSON pair
        # verbatim would advertise a closed interval it never touched
        ("", f"σ(n) values compared on [{xc['sigma']['range'][0]}, "
             f"{xc['sigma']['range'][1]})",
         xc["counts"]["sigma_values_compared"]),
        ("", "residue-tower / hard-witness values compared",
         xc["counts"]["anchored_values_compared"]),
        ("", "total disagreements across all seven fronts",
         xc["counts"]["disagreements"]),
        ("", "controls requiring the comparison to be able to reject",
         len(xc["controls"])),
    ]

    lines = [
        BEGIN,
        "",
        "| gate | measured | value |",
        "| --- | --- | --- |",
    ]
    for gate, what, val in rows:
        lines.append(f"| {gate} | {what} | `{val}` |")
    lines += [
        "",
        "Every figure above is emitted by `gate/emit_gate_summary.py` from the "
        "three gates' own JSON. None of them is typed into this file, because a "
        "number that lives only in prose is checked by nothing — and the three "
        "that used to live here had all gone stale.",
        "",
        "Sharpness of the controls, also measured rather than asserted: the atlas "
        f"offsets take `{xc['atlas']['distinct_bCorr_at_max_len']}` distinct values "
        f"at the maximum length, the parity words "
        f"`{xc['cylinder']['distinct_words_at_max_depth']}` distinct values at the "
        f"maximum depth, σ reaches `{xc['sigma']['max_sigma']}` across "
        f"`{xc['sigma']['distinct']}` distinct values, and of the "
        f"`{xc['anchored']['integers_tested_for_hardness']}` integers in "
        f"`[2, {xc['anchored']['hardness_test_limit']})` exactly "
        f"`{xc['anchored']['non_hard_at_depth_6_below_200']}` fail to be hard at "
        "depth 6 — so hardness is a restriction and not a description of every "
        "integer.",
        "",
        END,
    ]
    return "\n".join(lines)


def main() -> int:
    check_only = "--check" in sys.argv
    reports = {}
    for label, rel in GATES:
        rep = run(rel)
        if not rep.get("ok"):
            print(json.dumps({"error": f"{label} is not green; refusing to "
                                       "publish counts from a red gate",
                              "problems": rep.get("problems"),
                              "disagreements": rep.get("disagreements")},
                             indent=2, ensure_ascii=False))
            return 2
        reports[label] = rep

    block = build_block(reports)
    text = README.read_bytes().decode("utf-8")
    if BEGIN not in text or END not in text:
        print(json.dumps({"error": "README has no generated block markers",
                          "expected": [BEGIN, END]}, indent=2))
        return 2
    head, rest = text.split(BEGIN, 1)
    _, tail = rest.split(END, 1)
    new = head + block + tail

    if check_only:
        stale = new != text
        print(json.dumps({"tool": "emit_gate_summary.py", "mode": "check",
                          "readme_up_to_date": not stale, "ok": not stale},
                         indent=2))
        return 1 if stale else 0

    # A staleness check nobody has seen fail is the same green-light-with-no-bulb
    # as an audit nobody has seen fail, and this one guards the class of defect I
    # commit most often. So the comparison is drilled here, against the block that
    # was just computed — no extra gate run, and no way to ship a `--check` that
    # cannot reject. Every digit is perturbed in turn, one at a time.
    digits = [i for i, ch in enumerate(block) if ch.isdigit()]
    missed = []
    for i in digits:
        bumped = block[:i] + str((int(block[i]) + 1) % 10) + block[i + 1:]
        if bumped == block or (head + bumped + tail) == text:
            missed.append(i)
    control_ok = bool(digits) and not missed

    if not control_ok:
        print(json.dumps(
            {"error": "the staleness comparison failed its own control",
             "digits_in_block": len(digits), "perturbations_not_detected": missed},
            indent=2))
        return 2

    if new != text:
        README.write_bytes(new.encode("utf-8"))
    print(json.dumps({"tool": "emit_gate_summary.py", "mode": "emit",
                      "readme_rewritten": new != text,
                      "rows": block.count("\n| ") - 1,
                      "control_every_digit_perturbation_detected": control_ok,
                      "digits_guarded": len(digits), "ok": True}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
