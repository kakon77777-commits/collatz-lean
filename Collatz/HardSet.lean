/-
# Hard-Zeta — the `n ≥ 2` stopping domain, and why `1` cannot be let back in

數學戰士「墜衡」 / AMRAL Research Lab.

Queue item 6, first half. The series' `AUDIT_AND_CORRECTIONS.md` records:

> **Hard-Zeta — stopping-domain integration.** The v0.1.1 corrigendum correctly
> said the stopping-time domain is `n ≥ 2`, but the main body still wrote
> `E_k^C = ⊔ H_w`. The correction is now integrated into the main argument:
> `H̃_w = H_w ∩ [2,∞)`, `E_k^C = ⊔_{|w|=k} H̃_w`, and the chart Dirichlet mass is
> parameterized directly by the exact quotient bounds for `H̃_w`, so the `n = 1`
> boundary cannot silently re-enter through the Hurwitz-zeta representation.

The reason `1` has to be excluded is not a convention — it is a fact about the
map, and it is proved below. Under the modified map `1 → 2 → 1`, so **`1` never
descends below itself**: `T^j(1) ∈ {1, 2}` for every `j`, and neither is `< 1`.
Without the `2 ≤ n` clause, `1` would be a permanent member of *every* hard set
`E_k`, and a Dirichlet sum over `E_k` would silently carry a `1^{-s} = 1` term at
every depth. `one_is_permanently_undescended` and `one_not_hard` are the two
halves of that.

The other thing the correction points at is the **exact quotient bound**. Within
a cylinder, whether `n` has descended by step `k` is not a fact about `n` at all:
in chart coordinates it is a linear inequality in `a`, with the slope
`2^k − 3^u`. `descent_iff_quotient` is that statement, and it is what makes the
per-chart mass computable rather than merely bounded.
-/

import Mathlib.Tactic
import Collatz.AffineAtlas
import Collatz.ResidueCylinder
import Collatz.StoppingTime

namespace Collatz.HardSet

open Collatz.Cylinder (T parityWord)
open Collatz.Atlas (Letter uCount bCorr)

/-! ## The hard set at depth `k` -/

/-- `n` is **hard at depth `k`** if it is in the stopping-time domain `n ≥ 2` and
has not dropped below itself within `k` steps — that is, `σ(n) > k`. -/
def Hard (k n : ℕ) : Prop := 2 ≤ n ∧ ∀ j, 1 ≤ j → j ≤ k → n ≤ T^[j] n

/-- Hardness at depth `k` is decidable, so the hard set is a computable filter of
any interval — which is what an exhaustive run enumerates. -/
instance (k n : ℕ) : Decidable (Hard k n) := by
  unfold Hard
  exact inferInstance

/-- The hard sets shrink as the depth grows. -/
theorem hard_mono {k l n : ℕ} (h : k ≤ l) (hl : Hard l n) : Hard k n :=
  ⟨hl.1, fun j hj1 hjk => hl.2 j hj1 (hjk.trans h)⟩

/-- Hardness at depth `k` is exactly "the stopping time is not `≤ k`". -/
theorem hard_iff (k n : ℕ) (hn : 2 ≤ n) :
    Hard k n ↔ ¬ ∃ j, 1 ≤ j ∧ j ≤ k ∧ T^[j] n < n := by
  constructor
  · rintro ⟨-, h⟩ ⟨j, hj1, hjk, hlt⟩
    exact absurd (h j hj1 hjk) (by omega)
  · intro h
    refine ⟨hn, fun j hj1 hjk => ?_⟩
    by_contra hc
    exact h ⟨j, hj1, hjk, by omega⟩

/-! ## Why `1` has to be excluded

This is the content of the corrigendum. `1` is not awkward by convention; it is
a fixed point of the two-cycle, so it never descends, and any hard set that did
not exclude it would contain it at every depth. -/

/-- Under the modified map, `1 → 2 → 1`: every iterate of `1` is `1` or `2`. -/
theorem iterate_one_mem (j : ℕ) : T^[j] 1 = 1 ∨ T^[j] 1 = 2 := by
  induction j with
  | zero => left; rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · right; rw [h]; decide
      · left; rw [h]; decide

/-- **The boundary.** `1` never descends below itself, at any depth. So without
the `2 ≤ n` clause it would sit in every `E_k`, and a Dirichlet sum over the hard
set would carry a `1^{-s}` term forever. -/
theorem one_is_permanently_undescended : ∀ j, ¬ (T^[j] 1 < 1) := by
  intro j
  rcases iterate_one_mem j with h | h <;> rw [h] <;> omega

/-- …and with the clause, it is excluded at every depth. -/
theorem one_not_hard (k : ℕ) : ¬ Hard k 1 := by
  rintro ⟨h2, -⟩
  omega

/-- `0` is excluded too, and for a different reason: `T 0 = 0`, so it is a fixed
point that never reaches `1` either. The domain condition `2 ≤ n` rules out both
degenerate points at once. -/
theorem zero_not_hard (k : ℕ) : ¬ Hard k 0 := by
  rintro ⟨h2, -⟩
  omega

/-! ## `E_k^C = ⊔_{|w|=k} H̃_w`

The decomposition is by parity word, and it is a genuine partition because
`parityWord · k` is a function: every hard `n` lies in exactly one chart. The
corrected form intersects each piece with `[2, ∞)`, which is already what `Hard`
carries. -/

/-- `H̃_w`: the hard integers of depth `k` whose parity word is `w`. The `2 ≤ n`
of `Hard` is the `∩ [2,∞)` of the corrected statement. -/
def HardIn (k : ℕ) (w : List Letter) : Set ℕ := {n | Hard k n ∧ parityWord n k = w}

/-- Every hard integer lies in the chart of its own parity word. -/
theorem mem_hardIn {k n : ℕ} (h : Hard k n) : n ∈ HardIn k (parityWord n k) :=
  ⟨h, rfl⟩

/-- **The pieces are pairwise disjoint.** -/
theorem hardIn_disjoint {k : ℕ} {w v : List Letter} (hwv : w ≠ v) :
    Disjoint (HardIn k w) (HardIn k v) := by
  rw [Set.disjoint_left]
  rintro n ⟨-, hw⟩ ⟨-, hv⟩
  exact hwv (hw ▸ hv ▸ rfl)

/-- **The pieces cover the hard set.** Together with disjointness this is
`E_k^C = ⊔_{|w|=k} H̃_w`, with the union taken over words of length `k` — and
`length_parityWord` is what guarantees no other word contributes. -/
theorem hard_eq_iUnion (k : ℕ) :
    {n | Hard k n} = ⋃ w ∈ {w : List Letter | w.length = k}, HardIn k w := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · intro h
    exact ⟨parityWord n k, Collatz.Cylinder.length_parityWord n k, mem_hardIn h⟩
  · rintro ⟨w, -, h, -⟩
    exact h

/-- And `1` is in none of the pieces, at any depth — the `n = 1` boundary cannot
re-enter through the decomposition either. -/
theorem one_not_mem_hardIn (k : ℕ) (w : List Letter) : (1 : ℕ) ∉ HardIn k w := by
  rintro ⟨h, -⟩
  exact one_not_hard k h

/-! ## The exact quotient bound

Within a chart, "has `n` descended by step `k`" is not a question about `n`. In
chart coordinates it is a linear inequality in `a` whose slope is `2^k − 3^u`, so
each chart contributes a half-line of quotient coordinates — or all of them, or
none. That is what makes the per-chart Dirichlet mass exactly computable. -/

/-- **The exact quotient bound.** For `n` in the cylinder of its own parity word,
with `m` the chart's base point (`2^k·m = 3^u·r + b_w`), descent at step `k` is
the inequality `m + 3^u·a < r + 2^k·a` on the chart coordinate `a`.

No division and no `ℕ`-subtraction: both sides are the numerators. -/
theorem descent_iff_quotient (n k : ℕ) {r m a : ℤ}
    (hn : (n : ℤ) = r + 2 ^ k * a)
    (hm : 2 ^ k * m = 3 ^ uCount (parityWord n k) * r + bCorr (parityWord n k)) :
    ((T^[k] n : ℕ) : ℤ) < (n : ℤ)
      ↔ m + 3 ^ uCount (parityWord n k) * a < r + 2 ^ k * a := by
  have hnum : (2 : ℤ) ^ k * (T^[k] n : ℤ)
      = 3 ^ uCount (parityWord n k) * (n : ℤ) + bCorr (parityWord n k) :=
    Collatz.Cylinder.iterate_numerator n k
  have h2 : (0 : ℤ) < 2 ^ k := by positivity
  have hTk : ((T^[k] n : ℕ) : ℤ) = m + 3 ^ uCount (parityWord n k) * a := by
    refine mul_left_cancel₀ (ne_of_gt h2) ?_
    calc (2 : ℤ) ^ k * (T^[k] n : ℤ)
        = 3 ^ uCount (parityWord n k) * (n : ℤ) + bCorr (parityWord n k) := hnum
      _ = 3 ^ uCount (parityWord n k) * (r + 2 ^ k * a)
            + bCorr (parityWord n k) := by rw [hn]
      _ = (3 ^ uCount (parityWord n k) * r + bCorr (parityWord n k))
            + 3 ^ uCount (parityWord n k) * (2 ^ k * a) := by ring
      _ = 2 ^ k * m + 3 ^ uCount (parityWord n k) * (2 ^ k * a) := by rw [← hm]
      _ = 2 ^ k * (m + 3 ^ uCount (parityWord n k) * a) := by ring
  rw [hTk, hn]

/-- The slope of that inequality is `2^k − 3^u`, so the chart's descending
coordinates are a half-line when `3^u < 2^k`, and **empty for all large `a`**
when `2^k < 3^u`. The sign of the slope is the whole classification, and it
depends only on `(k, u)` — the counts, not the order.

The threshold is `|c| + 1` and not `c + 1`. That is not tidiness: with `c`
negative and the slope at least `2`, `a ≥ c + 1` permits `a < 0`, where `s·a`
runs the *wrong* way and the statement is false. The first version of this
theorem had `c + 1` and was simply not true. -/
theorem quotient_slope_sign (k u : ℕ) :
    (3 ^ u < 2 ^ k → ∀ c : ℤ, ∀ a : ℤ, |c| + 1 ≤ a → c < (2 ^ k - 3 ^ u) * a)
    ∧ (2 ^ k < 3 ^ u → ∀ c : ℤ, ∀ a : ℤ, |c| + 1 ≤ a → (2 ^ k - 3 ^ u) * a < c) := by
  constructor
  · intro hlt c a ha
    have habs : (0 : ℤ) ≤ |c| := abs_nonneg c
    have hcle : c ≤ |c| := le_abs_self c
    have ha1 : (1 : ℤ) ≤ a := by omega
    have hs1 : (1 : ℤ) ≤ 2 ^ k - 3 ^ u := by
      have : (3 : ℤ) ^ u < 2 ^ k := by exact_mod_cast hlt
      omega
    -- `a ≤ s·a` needs `a ≥ 0`; that is exactly why the bound is `|c| + 1`, not `c + 1`
    have hgrow : a ≤ (2 ^ k - 3 ^ u) * a := le_mul_of_one_le_left (by omega) hs1
    omega
  · intro hlt c a ha
    have habs : (0 : ℤ) ≤ |c| := abs_nonneg c
    have hcge : -|c| ≤ c := neg_abs_le c
    have ha1 : (1 : ℤ) ≤ a := by omega
    have hs1 : 2 ^ k - 3 ^ u ≤ -1 := by
      have : (2 : ℤ) ^ k < 3 ^ u := by exact_mod_cast hlt
      omega
    have hshrink : (2 ^ k - 3 ^ u) * a ≤ -1 * a :=
      mul_le_mul_of_nonneg_right hs1 (by omega)
    omega

end Collatz.HardSet
