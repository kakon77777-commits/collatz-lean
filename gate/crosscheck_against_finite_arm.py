"""Does the Lean development define the same objects the finite arm measures?

數學戰士「墜衡」 / AMRAL Research Lab.

A Lean proof that compiles is a proof *about the definitions in the Lean file*.
If `Collatz.orbit` and `Collatz.kappa` are not the accelerated map this project
has been measuring since RUN-008, then the theorems are decoration: correct, and
about something else.

So this gate makes the two arms confront each other. Lean emits its own orbit
values and exponents; `hz_accel_code.py` — written from Round 03-A.1's prose,
never from the Lean — emits its own; they must agree elementwise.

The gate must also be able to FAIL, so it carries a disagreement control: a
deliberately shifted sequence is compared the same way and must be reported as a
mismatch. Without it, a comparison that silently compares nothing to nothing
would pass.

Usage:  python gate/crosscheck_against_finite_arm.py
Env:    COLLATZ_ARM  path to collatz-verification-zhuiheng (default: the sibling
                     checkout under work together/amral-research-trees)
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent.parent
ARM = pathlib.Path(os.environ.get(
    "COLLATZ_ARM",
    r"D:\Ai\work together\amral-research-trees\collatz-verification-zhuiheng"))

# (start, steps) pairs. 27 is the arm's canonical hard start; 4095 and 2047 are
# the all-one witnesses for m = 11 and m = 10; 703 and 35655 are the long spines
# the arm reports. A witness-only sample would not test the generic case.
CASES = [(27, 10), (703, 20), (35655, 24), (4095, 12), (2047, 11), (1, 6)]

EMIT = """import Collatz.AllOnes
set_option linter.style.header false
namespace Collatz
{body}
end Collatz
"""


def lean_values(cases) -> dict:
    body = "\n".join(
        f"#eval ((List.range {m}).map (fun i => kappa (orbit {n} i)), "
        f"(List.range {m}).map (fun i => orbit {n} i))"
        for n, m in cases)
    with tempfile.TemporaryDirectory() as td:
        f = HERE / "Collatz" / "_CrosscheckEmit.lean"
        try:
            f.write_text(EMIT.format(body=body), encoding="utf-8")
            p = subprocess.run(["lake", "env", "lean", str(f)], cwd=str(HERE),
                               capture_output=True, text=True, encoding="utf-8",
                               errors="replace", timeout=1800)
        finally:
            f.unlink(missing_ok=True)
    out = p.stdout + p.stderr
    # each #eval prints a pair of lists: ([...], [...])
    pairs = re.findall(r"\(\[([0-9,\s]*)\],\s*\[([0-9,\s]*)\]\)", out)
    if len(pairs) != len(cases):
        raise SystemExit(json.dumps(
            {"error": "could not parse Lean output",
             "expected_blocks": len(cases), "found": len(pairs),
             "tail": out[-1500:]}, indent=2))

    def nums(s):
        return [int(x) for x in s.replace(" ", "").split(",") if x]

    return {n: {"kappa": nums(a), "orbit": nums(b)}
            for (n, _m), (a, b) in zip(cases, pairs)}


def python_values(cases) -> dict:
    sys.path.insert(0, str(ARM / "code"))
    import hz_accel_code as A                      # noqa: E402
    out = {}
    for n, m in cases:
        out[n] = {"kappa": list(A.accel_code(n, m)),
                  "orbit": list(A.orbit_endpoints(n, m - 1))}
    return out


def main() -> int:
    rep = {
        "tool": "crosscheck_against_finite_arm.py",
        "subject": "Collatz.orbit / Collatz.kappa (Lean) against "
                   "hz_accel_code.accel_code / orbit_endpoints (Python)",
        "why": "the Lean theorems are about the Lean definitions; this is the "
               "only thing that ties them to the object the finite arm measured",
        "cases": {}, "disagreements": [], "controls": {},
    }
    if not (ARM / "code" / "hz_accel_code.py").exists():
        print(json.dumps({"error": f"finite arm not found at {ARM}"}, indent=2))
        return 2

    lean = lean_values(CASES)
    py = python_values(CASES)
    for n, m in CASES:
        L, P = lean[n], py[n]
        agree_k = L["kappa"] == P["kappa"]
        agree_o = L["orbit"] == P["orbit"]
        rep["cases"][str(n)] = {
            "steps": m, "kappa_agrees": agree_k, "orbit_agrees": agree_o,
            "kappa": L["kappa"], "orbit_head": L["orbit"][:4],
        }
        if not agree_k:
            rep["disagreements"].append(
                {"n": n, "field": "kappa", "lean": L["kappa"], "python": P["kappa"]})
        if not agree_o:
            rep["disagreements"].append(
                {"n": n, "field": "orbit", "lean": L["orbit"], "python": P["orbit"]})

    # A comparison that cannot report a mismatch proves nothing. Shift one
    # sequence by one and require the same comparison to reject it.
    n0 = CASES[0][0]
    shifted = py[n0]["kappa"][1:] + [py[n0]["kappa"][0]]
    rep["controls"]["C01_a_shifted_sequence_is_rejected"] = {
        "detected": shifted != lean[n0]["kappa"]}
    # And a sequence that IS equal must be accepted, so the comparison is not
    # simply always-false.
    rep["controls"]["C02_an_identical_sequence_is_accepted"] = {
        "detected": list(py[n0]["kappa"]) == lean[n0]["kappa"]}

    rep["counts"] = {
        "cases": len(CASES),
        "kappa_values_compared": sum(len(v["kappa"]) for v in lean.values()),
        "orbit_values_compared": sum(len(v["orbit"]) for v in lean.values()),
        "disagreements": len(rep["disagreements"]),
    }
    rep["ok"] = (not rep["disagreements"]
                 and all(c["detected"] for c in rep["controls"].values()))
    json.dump(rep, sys.stdout, indent=2, ensure_ascii=False)
    print()
    return 0 if rep["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
