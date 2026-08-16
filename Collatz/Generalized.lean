/-
# Paper 07 — the generalised `mx + r` atlas, and the irrationality of `α_m`

數學戰士「墜衡」 / AMRAL Research Lab.

Queue item 2. Neo.K's *Generalized `mx+r` Systems* strips `3` and `1` out of the
Collatz branches and asks which of Paper 02's structure survives. Its answer is
"all of the finite-word algebra", and §6 says the specialisation
`(m, r) = (3, 1)` "immediately recovers Paper 02".

That last sentence is the reason this item follows Paper 02 in the queue: it is a
claim about the *previous* development, so formalising it tests whether the
generalisation really is one. Here it is `bG_three_one`, proved rather than
remarked — the two definitions are given independently and shown equal.

§25 is the first place in the whole queue where real numbers are unavoidable,
and it is instructive how little of it is analysis. The mathematical content is
an integer statement — an odd power is never a power of two — and the
irrationality of `α_m = log_m 2` follows from it in a few lines. So the integer
core is proved first and stands on its own, and the real statement is derived.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import Collatz.AffineAtlas

namespace Collatz.Generalized

open Collatz.Atlas (Letter)
open Collatz.Atlas.Letter

/-! ## §1–§3: the generalised branches -/

variable (m r : ℕ)

/-- §1: `D x = x/2`, `U_{m,r} x = (m x + r)/2`. -/
def stepG : Letter → ℚ → ℚ
  | D, x => x / 2
  | U, x => (m * x + r) / 2

/-- §3: the formal operator of a word, executed left to right. -/
def FG : List Letter → ℚ → ℚ
  | [], x => x
  | (σ :: v), x => FG v (stepG m r σ x)

/-- §5: the generalised order correction, by the recursion `List` recurses on. -/
def bG : List Letter → ℕ
  | [] => 0
  | (D :: v) => 2 * bG v
  | (U :: v) => r * m ^ Collatz.Atlas.uCount v + 2 * bG v

@[simp] lemma bG_nil : bG m r [] = 0 := rfl
@[simp] lemma bG_cons_D (v : List Letter) : bG m r (D :: v) = 2 * bG m r v := rfl
@[simp] lemma bG_cons_U (v : List Letter) :
    bG m r (U :: v) = r * m ^ Collatz.Atlas.uCount v + 2 * bG m r v := rfl

/-! ## §2: why `m` and `r` must be odd -/

/-- §2: with `m` and `r` odd, the odd branch lands in `ℤ` automatically — no
admissibility hypothesis is needed to keep `U_{m,r}` integral on odd inputs. -/
theorem odd_branch_integral {m r n : ℕ} (hm : Odd m) (hr : Odd r) (hn : Odd n) :
    2 ∣ (m * n + r) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hr
  obtain ⟨c, hc⟩ := hn
  subst ha; subst hb; subst hc
  refine ⟨(2 * a + 1) * c + a + b + 1, ?_⟩
  ring

/-- The hypothesis is not decoration: with `m` even the branch leaves `ℤ`. -/
theorem odd_branch_needs_odd_m : ¬ (2 ∣ (2 * 1 + 1)) := by decide

/-! ## §4: generalised affine closure (Theorem A) -/

/-- **Theorem A (§4).** `F^{(m,r)}_w(x) = (m^{u(w)} x + b^{(m,r)}_w) / 2^{|w|}`. -/
theorem affine_closure_G (w : List Letter) (x : ℚ) :
    FG m r w x = (m ^ Collatz.Atlas.uCount w * x + bG m r w) / 2 ^ w.length := by
  induction w generalizing x with
  | nil => simp [FG]
  | cons σ v ih =>
      have h2 : (2 : ℚ) ^ v.length ≠ 0 := by positivity
      cases σ with
      | D =>
          rw [FG, stepG, ih, List.length_cons, Collatz.Atlas.uCount_cons_D,
            bG_cons_D]
          push_cast
          field_simp
          ring
      | U =>
          rw [FG, stepG, ih, List.length_cons, Collatz.Atlas.uCount_cons_U,
            bG_cons_U]
          push_cast
          field_simp
          ring

/-! ## §5, §9: the recurrence and the concatenation law -/

/-- **§9's concatenation law.** `b_{wv} = m^{u(v)} b_w + 2^{|w|} b_v`. -/
theorem bG_append (w v : List Letter) :
    bG m r (w ++ v)
      = m ^ Collatz.Atlas.uCount v * bG m r w + 2 ^ w.length * bG m r v := by
  induction w with
  | nil => simp
  | cons σ t ih =>
      cases σ with
      | D => simp [ih, List.length_cons, pow_succ]; ring
      | U =>
          simp [ih, List.length_cons, pow_succ, Collatz.Atlas.uCount_append,
            pow_add]
          ring

/-- **Theorem B (§5), first half.** -/
theorem bG_append_D (w : List Letter) : bG m r (w ++ [D]) = bG m r w := by
  simp [bG_append]

/-- **Theorem B (§5), second half.** `b_{wU} = m b_w + r 2^{|w|}`. -/
theorem bG_append_U (w : List Letter) :
    bG m r (w ++ [U]) = m * bG m r w + r * 2 ^ w.length := by
  simp [bG_append]
  ring

/-! ## §6: the closed form, and the specialisation back to Paper 02 -/

/-- **§33, made precise.** The parameter `r` factors out of the correction
entirely: it scales the finite geometry and touches nothing else. -/
theorem bG_factor_r (w : List Letter) : bG m r w = r * bG m 1 w := by
  induction w with
  | nil => simp
  | cons σ v ih => cases σ <;> simp [ih] <;> ring

/-- The `r = 1` correction, in closed form — Paper 02's Theorem C with `3 ↦ m`. -/
theorem bG_one_closed_form (w : List Letter) :
    bG m 1 w = ∑ i ∈ Finset.range w.length,
      (if (w.drop i).head? = some U
        then 2 ^ i * m ^ Collatz.Atlas.uCount (w.drop (i + 1)) else 0) := by
  induction w with
  | nil => simp
  | cons σ v ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.drop_zero, List.head?_cons, List.drop_succ_cons]
      have hshift : ∀ i, (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := fun i => by ring
      cases σ with
      | D =>
          simp only [reduceCtorEq, if_false, add_zero, bG_cons_D, ih]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : (v.drop i).head? = some U <;> simp [h, hshift i] <;> ring
      | U =>
          simp only [if_true, bG_cons_U, ih, one_mul]
          rw [Finset.mul_sum, add_comm]
          congr 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            by_cases h : (v.drop i).head? = some U <;> simp [h, hshift i] <;> ring
          · simp

/-- **Theorem B (§6), closed form.** `b_w = r Σ_t 2^{j_t−1} m^{u−t}`. -/
theorem bG_closed_form (w : List Letter) :
    bG m r w = r * ∑ i ∈ Finset.range w.length,
      (if (w.drop i).head? = some U
        then 2 ^ i * m ^ Collatz.Atlas.uCount (w.drop (i + 1)) else 0) := by
  rw [bG_factor_r, bG_one_closed_form]

/-- **§6's specialisation.** At `(m, r) = (3, 1)` the generalised correction *is*
Paper 02's, so Paper 07 really does contain Paper 02 rather than resemble it.

The two are defined independently — neither definition mentions the other — so
this is a theorem about the generalisation, not a restatement of it. -/
theorem bG_three_one (w : List Letter) : bG 3 1 w = Collatz.Atlas.bCorr w := by
  induction w with
  | nil => simp
  | cons σ v ih => cases σ <;> simp [ih]

/-- The same specialisation at the level of the operator. -/
theorem FG_three_one (w : List Letter) (x : ℚ) :
    FG 3 1 w x = Collatz.Atlas.F w x := by
  rw [affine_closure_G, Collatz.Atlas.affine_closure, bG_three_one]
  norm_num

/-! ## §25: `α_m` is irrational -/

/-- The integer core of §25, which is where all the content is: for odd `m > 1`
no positive power of `m` is a power of two. Left side odd, right side even. -/
theorem odd_pow_ne_two_pow {m : ℕ} (hm : Odd m) (h1 : 1 < m) {p q : ℕ}
    (hp : 0 < p) : m ^ p ≠ 2 ^ q := by
  intro h
  rcases Nat.eq_zero_or_pos q with hq | hq
  · -- `2^0 = 1`, but `m^p > 1`
    subst hq
    have : 1 < m ^ p := Nat.one_lt_pow (by omega) h1
    omega
  · -- otherwise the right side is even and the left side is odd
    have hodd : Odd (m ^ p) := hm.pow
    have heven : 2 ∣ 2 ^ q := dvd_pow_self 2 (by omega)
    rw [h] at hodd
    rw [Nat.odd_iff] at hodd
    omega

/-- **§25.** `α_m = log_m 2` is irrational for every odd `m > 1`, so there is no
nonempty word of neutral slope. -/
theorem alpha_irrational {m : ℕ} (hm : Odd m) (h1 : 1 < m) :
    Irrational (Real.logb m 2) := by
  rintro ⟨c, hc⟩
  have hm1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast h1
  have hlogm : 0 < Real.log m := Real.log_pos hm1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `c = log 2 / log m`, hence `c > 0` and `c · log m = log 2`
  have hcval : (c : ℝ) = Real.log 2 / Real.log m := by rw [hc, Real.logb]
  have hcpos : 0 < (c : ℝ) := by rw [hcval]; positivity
  have hceq : (c : ℝ) * Real.log m = Real.log 2 := by
    rw [hcval, div_mul_cancel₀ _ (ne_of_gt hlogm)]
  -- clear the denominator: `num · log m = den · log 2`
  have hden : ((c.den : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr c.den_nz
  have hnum : 0 < c.num := Rat.num_pos.mpr (by exact_mod_cast hcpos)
  have hsplit : (c.num : ℝ) * Real.log m = (c.den : ℝ) * Real.log 2 := by
    have hcast : (c : ℝ) = (c.num : ℝ) / (c.den : ℝ) := Rat.cast_def c
    rw [hcast, div_mul_eq_mul_div, div_eq_iff hden] at hceq
    linarith
  -- turn it into an equality of two positive reals, then of two naturals
  set p : ℕ := c.num.toNat with hp
  have hpz : ((p : ℤ)) = c.num := Int.toNat_of_nonneg (le_of_lt hnum)
  have hpc : (p : ℝ) = (c.num : ℝ) := by exact_mod_cast hpz
  have hlogeq : Real.log ((m : ℝ) ^ p) = Real.log ((2 : ℝ) ^ c.den) := by
    rw [Real.log_pow, Real.log_pow, hpc, hsplit]
  have hreal : (m : ℝ) ^ p = (2 : ℝ) ^ c.den := by
    have hmp : (0 : ℝ) < (m : ℝ) ^ p := by positivity
    have h2q : (0 : ℝ) < (2 : ℝ) ^ c.den := by positivity
    rw [← Real.exp_log hmp, ← Real.exp_log h2q, hlogeq]
  have hnat : m ^ p = 2 ^ c.den := by exact_mod_cast hreal
  have hppos : 0 < p := by
    have : (0 : ℤ) < (p : ℤ) := by rw [hpz]; exact hnum
    exact_mod_cast this
  exact odd_pow_ne_two_pow hm h1 hppos hnat

end Collatz.Generalized
