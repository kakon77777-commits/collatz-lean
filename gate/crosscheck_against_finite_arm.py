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
import Collatz.AffineAtlas
import Collatz.Generalized
import Collatz.ResidueCylinder
import Collatz.Valuation
import Collatz.StoppingTime
import Collatz.HardSet
import Collatz.AnchoredBranch
set_option linter.style.header false
namespace Collatz
{body}
end Collatz
"""

# Paper 02: every word up to this length is compared, both counts and offsets.
ATLAS_MAX_LEN = 10

# Paper 07: the same, for a spread of (m, r). `m = 1` is included because §19
# says that case has to be understood separately, and `r = 7` because a
# parameter that only ever appears as 1 is not being tested.
GEN_PARAMS = [(3, 1), (5, 1), (5, 3), (7, 1), (1, 1), (3, 7)]
GEN_MAX_LEN = 8

# Paper 03: the parity word of every n below 2^k, at each depth k. Comparing the
# whole range (not only the residues) also exercises periodicity.
CYL_MAX_K = 9

# Paper 06: valuation words of the odd numbers below this, with their run-length
# expansion and accelerated correction.
VAL_ODD_LIMIT = 400
VAL_STEPS = 6

# Paper 09: the coefficient stopping time sigma(n) for every n in [2, SIGMA_LIMIT).
# This is the quantity the companion arm's exhaustive [3, 2^40] run computes, so
# it is the most direct anchor in the whole gate.
SIGMA_LIMIT = 500

# Paper 09 Theorem F: the residue tower r_k = n mod 2^k, and the depth-k hard
# witness. The theorems here are equivalences about infinite branches, which no
# finite run can settle; what a finite run CAN settle is that the two towers and
# the witness family are the objects the proofs think they are. `27` is the
# tower's fixed start because its residues genuinely move before stabilising.
ANC_MAX_K = 12
ANC_TOWER_START = 27


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


def lean_atlas(max_len: int) -> dict[int, list[tuple[int, int, int]]]:
    """Lean's (encoded word, u, b) for every word of each length up to max_len."""
    # `#eval` pretty-prints and ELIDES long lists with `⋯`, which would silently
    # compare a prefix and pass. `IO.println` of a compact string does not.
    body = "\n".join(
        f'#eval IO.println ("ATLAS {k} " ++ String.intercalate "," '
        f"((Collatz.Atlas.allWords {k}).map (fun w => "
        f's!"{{Collatz.Atlas.encode w}}:{{Collatz.Atlas.uCount w}}:'
        f'{{Collatz.Atlas.bCorr w}}")))'
        for k in range(max_len + 1))
    f = HERE / "Collatz" / "_AtlasEmit.lean"
    try:
        f.write_bytes(EMIT.format(body=body).encode("utf-8"))
        p = subprocess.run(["lake", "env", "lean", str(f)], cwd=str(HERE),
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace", timeout=3600)
    finally:
        f.unlink(missing_ok=True)
    out = p.stdout + p.stderr
    if "⋯" in out:
        raise SystemExit(json.dumps(
            {"error": "the emission was elided; a prefix would have been "
                      "compared and would have passed"}, indent=2))
    res = {}
    for m in re.finditer(r"^ATLAS (\d+) (.*)$", out, re.MULTILINE):
        k = int(m.group(1))
        res[k] = [tuple(int(x) for x in tok.split(":"))
                  for tok in m.group(2).strip().split(",") if tok]
    if sorted(res) != list(range(max_len + 1)):
        raise SystemExit(json.dumps(
            {"error": "could not parse the atlas emission",
             "expected_lengths": list(range(max_len + 1)), "found": sorted(res),
             "tail": out[-1200:]}, indent=2))
    return res


def lean_generalized(params, max_len: int) -> dict:
    """Lean's (encoded word, b^{(m,r)}_w) for each parameter pair."""
    body = "\n".join(
        f'#eval IO.println ("GEN {m} {r} {k} " ++ String.intercalate "," '
        f"((Collatz.Atlas.allWords {k}).map (fun w => "
        f's!"{{Collatz.Atlas.encode w}}:{{Collatz.Generalized.bG {m} {r} w}}")))'
        for (m, r) in params for k in range(max_len + 1))
    f = HERE / "Collatz" / "_GenEmit.lean"
    try:
        f.write_bytes(EMIT.format(body=body).encode("utf-8"))
        p = subprocess.run(["lake", "env", "lean", str(f)], cwd=str(HERE),
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace", timeout=3600)
    finally:
        f.unlink(missing_ok=True)
    out = p.stdout + p.stderr
    if "⋯" in out:
        raise SystemExit(json.dumps(
            {"error": "the generalized emission was elided"}, indent=2))
    res = {}
    for mt in re.finditer(r"^GEN (\d+) (\d+) (\d+) (.*)$", out, re.MULTILINE):
        m, r, k = int(mt.group(1)), int(mt.group(2)), int(mt.group(3))
        res[(m, r, k)] = [tuple(int(x) for x in tok.split(":"))
                          for tok in mt.group(4).strip().split(",") if tok]
    want = {(m, r, k) for (m, r) in params for k in range(max_len + 1)}
    if set(res) != want:
        raise SystemExit(json.dumps(
            {"error": "could not parse the generalized emission",
             "missing": sorted(str(x) for x in want - set(res)),
             "tail": out[-1200:]}, indent=2))
    return res


def lean_cylinder(max_k: int) -> dict:
    """Lean's parity word for every n < 2^k, at each depth up to max_k."""
    body = "\n".join(
        f'#eval IO.println ("CYL {k} " ++ String.intercalate "," '
        f"((List.range (2 ^ {k})).map (fun n => String.join "
        f"((Collatz.Cylinder.parityWord n {k}).map (fun c => "
        f'match c with | Collatz.Atlas.Letter.D => "D" | Collatz.Atlas.Letter.U => "U")))))'
        for k in range(max_k + 1))
    f = HERE / "Collatz" / "_CylEmit.lean"
    try:
        f.write_bytes(EMIT.format(body=body).encode("utf-8"))
        p = subprocess.run(["lake", "env", "lean", str(f)], cwd=str(HERE),
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace", timeout=3600)
    finally:
        f.unlink(missing_ok=True)
    out = p.stdout + p.stderr
    if "⋯" in out:
        raise SystemExit(json.dumps({"error": "the cylinder emission was elided"},
                                    indent=2))
    res = {}
    for mt in re.finditer(r"^CYL (\d+) (.*)$", out, re.MULTILINE):
        k = int(mt.group(1))
        res[k] = mt.group(2).strip().split(",") if mt.group(2).strip() else [""]
    if sorted(res) != list(range(max_k + 1)):
        raise SystemExit(json.dumps(
            {"error": "could not parse the cylinder emission",
             "found": sorted(res), "tail": out[-1200:]}, indent=2))
    return res


def lean_valuation(limit: int, steps: int) -> dict:
    """Lean's (valuation word, K, expanded parity word, B) for odd starts."""
    odds = [n for n in range(1, limit, 2)]
    body = "\n".join(
        f'#eval IO.println ("VAL {n} " '
        f'++ String.intercalate "." ((Collatz.Valuation.valWord {n} {steps}).map toString) '
        f'++ " " ++ toString (Collatz.Valuation.Kcum (Collatz.Valuation.valWord {n} {steps})) '
        f'++ " " ++ String.join ((Collatz.Valuation.expand '
        f'(Collatz.Valuation.valWord {n} {steps})).map (fun c => match c with '
        f'| Collatz.Atlas.Letter.D => "D" | Collatz.Atlas.Letter.U => "U")) '
        f'++ " " ++ toString (Collatz.Valuation.Bcorr '
        f'(Collatz.Valuation.valWord {n} {steps})))'
        for n in odds)
    f = HERE / "Collatz" / "_ValEmit.lean"
    try:
        f.write_bytes(EMIT.format(body=body).encode("utf-8"))
        p = subprocess.run(["lake", "env", "lean", str(f)], cwd=str(HERE),
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace", timeout=3600)
    finally:
        f.unlink(missing_ok=True)
    out = p.stdout + p.stderr
    if "⋯" in out:
        raise SystemExit(json.dumps({"error": "the valuation emission was elided"},
                                    indent=2))
    res = {}
    for mt in re.finditer(r"^VAL (\d+) ([\d.]*) (\d+) ([DU]*) (\d+)$", out,
                          re.MULTILINE):
        n = int(mt.group(1))
        kappa = [int(x) for x in mt.group(2).split(".") if x]
        res[n] = {"kappa": kappa, "K": int(mt.group(3)),
                  "expand": mt.group(4), "B": int(mt.group(5))}
    if sorted(res) != odds:
        raise SystemExit(json.dumps(
            {"error": "could not parse the valuation emission",
             "missing": [n for n in odds if n not in res][:8],
             "tail": out[-1200:]}, indent=2))
    return res


def lean_sigma(limit: int) -> dict:
    """Lean's least descending step count for each n in [2, limit)."""
    body = "\n".join(
        f'#eval IO.println ("SIG {n} " ++ toString '
        f"((List.range 600).find? (fun j => 1 <= j && "
        f"Collatz.Cylinder.T^[j] {n} < {n})))"
        for n in range(2, limit))
    f = HERE / "Collatz" / "_SigEmit.lean"
    try:
        f.write_bytes(EMIT.format(body=body).encode("utf-8"))
        p = subprocess.run(["lake", "env", "lean", str(f)], cwd=str(HERE),
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace", timeout=3600)
    finally:
        f.unlink(missing_ok=True)
    out = p.stdout + p.stderr
    res = {}
    for mt in re.finditer(r"^SIG (\d+) \(some (\d+)\)$", out, re.MULTILINE):
        res[int(mt.group(1))] = int(mt.group(2))
    missing = [n for n in range(2, limit) if n not in res]
    if missing:
        raise SystemExit(json.dumps(
            {"error": "could not parse the sigma emission (or a search failed)",
             "missing": missing[:8], "tail": out[-1200:]}, indent=2))
    return res


def python_expand(kappa: list[int]) -> str:
    """§5's run-length expansion, written from the prose: E(κ) = U D^{κ−1}."""
    return "".join("U" + "D" * (j - 1) for j in kappa)


def python_atlas(encoded: int, k: int) -> tuple[int, int]:
    """Rebuild the word from Lean's encoding, then compose it independently.

    `compose_affine` in the finite arm applies the operators one at a time
    straight off the definitions of D and U; it knows nothing about b_w.
    """
    word = "".join("U" if (encoded >> i) & 1 else "D" for i in range(k))
    sys.path.insert(0, str(ARM / "code"))
    import ot_paper02_recheck as P                  # noqa: E402
    _A, B, _Dn = P.compose_affine(word)
    return word.count("U"), B


def lean_anchored(max_k: int, start: int) -> dict:
    """Lean's residue tower, all-ones tower, depth-k witness and its hardness."""
    body = "\n".join(
        f'#eval IO.println ("ANC {k} "'
        f' ++ toString (Collatz.Anchored.residue {start} {k})'
        f' ++ ":" ++ toString (Collatz.Anchored.allOnesResidue {k})'
        f' ++ ":" ++ toString (Collatz.allOnesStart ({k} + 1))'
        f' ++ ":" ++ toString'
        f' (decide (Collatz.HardSet.Hard {k} (Collatz.allOnesStart ({k} + 1)))))'
        for k in range(max_k + 1))
    f = HERE / "Collatz" / "_AncEmit.lean"
    try:
        f.write_bytes(EMIT.format(body=body).encode("utf-8"))
        p = subprocess.run(["lake", "env", "lean", str(f)], cwd=str(HERE),
                           capture_output=True, text=True, encoding="utf-8",
                           errors="replace", timeout=3600)
    finally:
        f.unlink(missing_ok=True)
    out = p.stdout + p.stderr
    if "\u22ef" in out:
        raise SystemExit(json.dumps(
            {"error": "Lean elided its output", "tail": out[-800:]}, indent=2))
    rows = {}
    for m in re.finditer(r"ANC (\d+) (\d+):(\d+):(\d+):(true|false)", out):
        rows[int(m.group(1))] = {
            "residue": int(m.group(2)), "allOnes": int(m.group(3)),
            "witness": int(m.group(4)), "hard": m.group(5) == "true"}
    if len(rows) != max_k + 1:
        raise SystemExit(json.dumps(
            {"error": "could not parse anchored output", "expected": max_k + 1,
             "found": len(rows), "tail": out[-1500:]}, indent=2))
    return rows


def python_T(n: int) -> int:
    """The modified map, reimplemented here on purpose: a cross-check that calls
    the same code on both sides is one method compared with itself."""
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def python_hard(k: int, n: int) -> bool:
    if n < 2:
        return False
    x = n
    for _ in range(k):
        x = python_T(x)
        if x < n:
            return False
    return True


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

    # ---- Paper 02: every word up to ATLAS_MAX_LEN, counts and offsets
    atlas = lean_atlas(ATLAS_MAX_LEN)
    words = ubad = bbad = 0
    for k, rows in atlas.items():
        if len(rows) != 2 ** k:
            rep["disagreements"].append(
                {"length": k, "field": "word count",
                 "lean": len(rows), "expected": 2 ** k})
        for enc, u_lean, b_lean in rows:
            words += 1
            u_py, b_py = python_atlas(enc, k)
            if u_lean != u_py:
                ubad += 1
                if ubad <= 3:
                    rep["disagreements"].append(
                        {"length": k, "encoded": enc, "field": "uCount",
                         "lean": u_lean, "python": u_py})
            if b_lean != b_py:
                bbad += 1
                if bbad <= 3:
                    rep["disagreements"].append(
                        {"length": k, "encoded": enc, "field": "bCorr",
                         "lean": b_lean, "python": b_py})
    rep["atlas"] = {"max_word_length": ATLAS_MAX_LEN, "words_compared": words,
                    "uCount_disagreements": ubad, "bCorr_disagreements": bbad,
                    "distinct_bCorr_at_max_len":
                        len({b for _e, _u, b in atlas[ATLAS_MAX_LEN]})}
    # A comparison over a set where every b is equal would pass while proving
    # nothing about the offset, so require the offsets to actually vary.
    rep["controls"]["C03_the_offsets_are_not_all_equal"] = {
        "detected": rep["atlas"]["distinct_bCorr_at_max_len"] > 1}
    # and the encoding must be injective, or words are being conflated
    rep["controls"]["C04_the_encoding_separates_the_words"] = {
        "detected": len({e for e, _u, _b in atlas[ATLAS_MAX_LEN]}) == 2 ** ATLAS_MAX_LEN}

    # ---- Paper 07: the same, across parameter pairs
    sys.path.insert(0, str(ARM / "code"))
    import ot_paper07_recheck as P7                 # noqa: E402
    gen = lean_generalized(GEN_PARAMS, GEN_MAX_LEN)
    gwords = gbad = 0
    per_param_distinct = {}
    for (m, r, k), rows in sorted(gen.items()):
        vals = set()
        for enc, b_lean in rows:
            gwords += 1
            word = "".join("U" if (enc >> i) & 1 else "D" for i in range(k))
            b_py = P7.compose(word, m, r)[1]
            vals.add(b_lean)
            if b_lean != b_py:
                gbad += 1
                if gbad <= 3:
                    rep["disagreements"].append(
                        {"m": m, "r": r, "length": k, "encoded": enc,
                         "field": "bG", "lean": b_lean, "python": b_py})
        per_param_distinct.setdefault((m, r), 0)
        per_param_distinct[(m, r)] = max(per_param_distinct[(m, r)], len(vals))
    rep["generalized"] = {
        "params": [list(p) for p in GEN_PARAMS], "max_word_length": GEN_MAX_LEN,
        "words_compared": gwords, "disagreements": gbad,
        "distinct_b_per_param": {f"{m},{r}": n
                                 for (m, r), n in sorted(per_param_distinct.items())}}
    # The parameters must actually change the answer, or comparing across them
    # would be comparing one function to itself six times.
    top = {(m, r): {b for _e, b in gen[(m, r, GEN_MAX_LEN)]} for (m, r) in GEN_PARAMS}
    rep["controls"]["C05_the_parameters_change_the_correction"] = {
        "detected": len({frozenset(v) for v in top.values()}) == len(GEN_PARAMS)}

    # ---- Paper 03: parity words, against the finite arm's own iteration
    cyl = lean_cylinder(CYL_MAX_K)
    cwords = cbad = 0
    for k, rows in sorted(cyl.items()):
        if len(rows) != 2 ** k:
            rep["disagreements"].append(
                {"depth": k, "field": "row count",
                 "lean": len(rows), "expected": 2 ** k})
        for n, w_lean in enumerate(rows):
            cwords += 1
            w_py = P7.actual_word(n, k, 3, 1)[0]
            if w_lean != w_py:
                cbad += 1
                if cbad <= 3:
                    rep["disagreements"].append(
                        {"depth": k, "n": n, "field": "parityWord",
                         "lean": w_lean, "python": w_py})
    rep["cylinder"] = {
        "max_depth": CYL_MAX_K, "integers_compared": cwords,
        "disagreements": cbad,
        "distinct_words_at_max_depth": len(set(cyl[CYL_MAX_K]))}
    # Theorem B says the 2^k residues give 2^k DIFFERENT words. If they did not,
    # the bijection would be false and this comparison would still pass.
    rep["controls"]["C06_the_residues_give_distinct_words"] = {
        "detected": len(set(cyl[CYL_MAX_K])) == 2 ** CYL_MAX_K}
    # and periodicity: n and n + 2^k must agree, checked outside the range above
    rep["controls"]["C07_periodicity_holds_beyond_the_sampled_range"] = {
        "detected": all(
            P7.actual_word(n, CYL_MAX_K, 3, 1)[0]
            == P7.actual_word(n + 2 ** CYL_MAX_K, CYL_MAX_K, 3, 1)[0]
            for n in range(64))}

    # ---- Paper 06: valuation words, run-length expansion, and B_kappa
    import hz_accel_code as A6                     # noqa: E402
    # `P` is a loop variable further up; import under a name that cannot clash.
    import ot_paper02_recheck as P02                # noqa: E402
    val = lean_valuation(VAL_ODD_LIMIT, VAL_STEPS)
    vstarts = vbad = 0
    for n, row in sorted(val.items()):
        vstarts += 1
        kappa_py = list(A6.accel_code(n, VAL_STEPS))
        exp_py = python_expand(row["kappa"])
        b_py = A6.cumulative(row["kappa"])[-1]
        checks = [
            ("kappa", row["kappa"], kappa_py),
            ("K", row["K"], sum(kappa_py)),
            ("expand", row["expand"], exp_py),
            # B_kappa from Paper 02's own composer applied to the expansion:
            # a route that never mentions B at all
            ("B", row["B"], P02.compose_affine(exp_py)[1]),
        ]
        for field, lean_v, py_v in checks:
            if lean_v != py_v:
                vbad += 1
                if vbad <= 3:
                    rep["disagreements"].append(
                        {"n": n, "field": field, "lean": lean_v, "python": py_v})
        _ = b_py
    rep["valuation"] = {
        "odd_starts": vstarts, "steps": VAL_STEPS, "disagreements": vbad,
        "distinct_valuation_words": len({tuple(r["kappa"]) for r in val.values()})}
    # If every start had the same valuation word, the comparison would be one row
    # repeated 200 times.
    rep["controls"]["C08_the_valuation_words_differ_across_starts"] = {
        "detected": rep["valuation"]["distinct_valuation_words"] > 20}

    # ---- Paper 09: the coefficient stopping time, against the arm's engine
    import collatz_ref as CR                       # noqa: E402
    sig = lean_sigma(SIGMA_LIMIT)
    sbad = 0
    for n, s_lean in sorted(sig.items()):
        s_py, _peak = CR.sigma_and_peak(n)
        if s_lean != s_py:
            sbad += 1
            if sbad <= 3:
                rep["disagreements"].append(
                    {"n": n, "field": "sigma", "lean": s_lean, "python": s_py})
    rep["sigma"] = {"range": [2, SIGMA_LIMIT], "compared": len(sig),
                    "disagreements": sbad,
                    "max_sigma": max(sig.values()), "distinct": len(set(sig.values()))}
    # If sigma were constant, comparing it would be comparing one number.
    rep["controls"]["C09_sigma_varies_and_is_sometimes_large"] = {
        "detected": rep["sigma"]["distinct"] > 5 and rep["sigma"]["max_sigma"] > 10}

    # ---- Paper 09 Theorem F: the residue tower and the depth-k hard witness
    anc = lean_anchored(ANC_MAX_K, ANC_TOWER_START)
    abad = 0
    for k, row in sorted(anc.items()):
        want = {"residue": ANC_TOWER_START % 2 ** k,
                "allOnes": 2 ** k - 1,
                "witness": 2 ** (k + 2) - 1,
                "hard": python_hard(k, 2 ** (k + 2) - 1)}
        for field, w in want.items():
            if row[field] != w:
                abad += 1
                if abad <= 4:
                    rep["disagreements"].append(
                        {"k": k, "field": f"anchored.{field}",
                         "lean": row[field], "python": w})
    tower = [anc[k]["residue"] for k in sorted(anc)]
    rep["anchored"] = {
        "max_k": ANC_MAX_K, "tower_start": ANC_TOWER_START,
        "rows_compared": len(anc), "values_compared": 4 * len(anc),
        "disagreements": abad,
        "tower_distinct": len(set(tower)),
        "tower_stabilises_at": tower[-1],
        "witnesses_all_hard": all(r["hard"] for r in anc.values()),
        "distinct_witnesses": len({r["witness"] for r in anc.values()})}
    # The tower must MOVE before it settles, or `residue_stabilises` would be a
    # statement about a constant function and §43's separation would be empty.
    rep["controls"]["C10_the_residue_tower_moves_then_settles"] = {
        "detected": rep["anchored"]["tower_distinct"] > 3
                    and tower[-1] == ANC_TOWER_START}
    # Hardness must be a real restriction: if every integer were hard at depth k,
    # `hard_at_each_depth_is_nonempty` would be saying nothing. Count the failures.
    HARD_LIMIT = 200
    tested = list(range(2, HARD_LIMIT))
    not_hard = [n for n in tested if not python_hard(6, n)]
    rep["anchored"]["hardness_test_limit"] = HARD_LIMIT
    rep["anchored"]["integers_tested_for_hardness"] = len(tested)
    rep["anchored"]["non_hard_at_depth_6_below_200"] = len(not_hard)
    rep["controls"]["C11_hardness_excludes_most_integers"] = {
        "detected": len(not_hard) > 100
                    and rep["anchored"]["witnesses_all_hard"]
                    and rep["anchored"]["distinct_witnesses"] == ANC_MAX_K + 1}

    rep["counts"] = {
        "cases": len(CASES),
        "kappa_values_compared": sum(len(v["kappa"]) for v in lean.values()),
        "orbit_values_compared": sum(len(v["orbit"]) for v in lean.values()),
        "disagreements": len(rep["disagreements"]),
        "atlas_words_compared": rep["atlas"]["words_compared"],
        "generalized_words_compared": rep["generalized"]["words_compared"],
        "cylinder_integers_compared": rep["cylinder"]["integers_compared"],
        "valuation_starts_compared": rep["valuation"]["odd_starts"],
        "sigma_values_compared": rep["sigma"]["compared"],
        "anchored_values_compared": rep["anchored"]["values_compared"],
    }
    rep["ok"] = (not rep["disagreements"]
                 and all(c["detected"] for c in rep["controls"].values()))
    json.dump(rep, sys.stdout, indent=2, ensure_ascii=False)
    print()
    return 0 if rep["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
