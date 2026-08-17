/-
# Paper 03 — parity words, residue cylinders, and the `r_w = 0` boundary

數學戰士「墜衡」 / AMRAL Research Lab.

Queue item 3. Paper 02 closed the *algebra* of a finite parity word but left its
**domain** open: `F_w` is a formal operator on `ℚ`, and which integers actually
follow `w` was a separate question. Paper 03 answers it — the integers following
`w` are exactly one residue class mod `2^{|w|}`, and `w ↦ r_w` is a bijection
`{D,U}^k ≃ ℤ/2^kℤ`.

## Why this item was flagged in the queue

The series' own `AUDIT_AND_CORRECTIONS.md` records a repair here:

> **Paper 03 — induction proof at `r_w = 0`.** The original proof used
> `r_w ∈ Ω_w`. This fails for the all-`D` residue cylinder where canonical
> `r_w = 0`. The theorem itself is not false. The proof is repaired by using the
> always-positive representative `r_w + 2^k`.

That is exactly the kind of gap a proof assistant does not let you walk past, so
the boundary is made explicit below rather than left to a reader's goodwill:
`allD_residue_zero` states the awkward case and
`cylinder_has_positive_member` is the repair, stated for every cylinder rather
than patched onto the one that breaks.

## The one place the obvious statement is wrong

Periodicity is **not** `parityWord (n + 2^k) k = parityWord n k` proved by naive
induction: the `U` branch sends `n + c·2^k ↦ T n + 3c·2^{k-1}`, so the multiplier
`c` is not preserved — it is multiplied by 3. The induction only closes if `c` is
quantified over *all* odd numbers. Stating it with `c = 1` gives an induction
hypothesis too weak to use on its own successor.
-/

import Mathlib.Tactic
import Collatz.AffineAtlas

namespace Collatz.Cylinder

open Collatz.Atlas (Letter uCount bCorr)
open Collatz.Atlas.Letter

/-! ## The modified map and the parity word of an integer -/

/-- §1's modified Collatz map `T`, on `ℕ`. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

@[simp] lemma T_even {n : ℕ} (h : n % 2 = 0) : T n = n / 2 := by simp [T, h]

@[simp] lemma T_odd {n : ℕ} (h : n % 2 = 1) : T n = (3 * n + 1) / 2 := by
  simp [T, h]

/-- The letter `n` takes on its first step. -/
def letterOf (n : ℕ) : Letter := if n % 2 = 0 then D else U

/-- §3–§7: the first `k` parity branches of `n`. -/
def parityWord (n : ℕ) : ℕ → List Letter
  | 0 => []
  | (k + 1) => letterOf n :: parityWord (T n) k

@[simp] lemma parityWord_zero (n : ℕ) : parityWord n 0 = [] := rfl

@[simp] lemma parityWord_succ (n k : ℕ) :
    parityWord n (k + 1) = letterOf n :: parityWord (T n) k := rfl

@[simp] lemma length_parityWord (n k : ℕ) : (parityWord n k).length = k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih => simp [ih]

/-! ## Theorem A, first half: the word depends only on `n` mod `2^k` -/

/-- Adding `c · 2^k` for **odd** `c` does not change the first `k` branches.

The odd multiplier is not a convenience: the `U` branch turns `c` into `3c`, so
an induction hypothesis fixed at `c = 1` cannot be applied to its own successor.
-/
theorem parityWord_add_odd_mul (k : ℕ) :
    ∀ (n c : ℕ), Odd c → parityWord (n + c * 2 ^ k) k = parityWord n k := by
  induction k with
  | zero => intro n c _; simp
  | succ k ih =>
      intro n c hc
      -- `X` is the whole bump; everything below is linear in it, which is what
      -- `omega` needs — `c * 2^k` is a product of two variables and is not.
      set X : ℕ := c * 2 ^ k with hX
      have hbump : c * 2 ^ (k + 1) = 2 * X := by rw [hX]; ring
      have hpar : (n + c * 2 ^ (k + 1)) % 2 = n % 2 := by rw [hbump]; omega
      have hletter : letterOf (n + c * 2 ^ (k + 1)) = letterOf n := by
        unfold letterOf; rw [hpar]
      rw [parityWord_succ, parityWord_succ, hletter]
      congr 1
      rcases Nat.even_or_odd n with hn | hn
      · -- `D`: the multiplier survives unchanged
        have hn0 : n % 2 = 0 := Nat.even_iff.mp hn
        have h1 : (n + c * 2 ^ (k + 1)) % 2 = 0 := by rw [hpar]; exact hn0
        rw [T_even h1, T_even hn0]
        have hdiv : (n + c * 2 ^ (k + 1)) / 2 = n / 2 + X := by rw [hbump]; omega
        rw [hdiv, hX]
        exact ih (n / 2) c hc
      · -- `U`: the multiplier becomes `3c`, still odd
        have hn1 : n % 2 = 1 := Nat.odd_iff.mp hn
        have h1 : (n + c * 2 ^ (k + 1)) % 2 = 1 := by rw [hpar]; exact hn1
        rw [T_odd h1, T_odd hn1]
        have hdiv : (3 * (n + c * 2 ^ (k + 1)) + 1) / 2 = (3 * n + 1) / 2 + 3 * X := by
          rw [hbump]; omega
        rw [hdiv]
        have : 3 * X = 3 * c * 2 ^ k := by rw [hX]; ring
        rw [this]
        exact ih ((3 * n + 1) / 2) (3 * c) (by
          obtain ⟨d, hd⟩ := hc; exact ⟨3 * d + 1, by omega⟩)

/-- The `c = 1` corollary, which is the form the paper states. -/
theorem parityWord_add_pow (n k : ℕ) :
    parityWord (n + 2 ^ k) k = parityWord n k := by
  simpa using parityWord_add_odd_mul k n 1 odd_one

/-- Any number of whole periods may be added. -/
theorem parityWord_add_mul (n k j : ℕ) :
    parityWord (n + 2 ^ k * j) k = parityWord n k := by
  induction j with
  | zero => simp
  | succ j ihj =>
      have : n + 2 ^ k * (j + 1) = (n + 2 ^ k * j) + 2 ^ k := by ring
      rw [this, parityWord_add_pow, ihj]

/-- Congruent integers have the same first `k` branches — Theorem A's
"the cylinder is a union of residue classes" half. -/
theorem parityWord_of_modEq {n m k : ℕ} (h : n ≡ m [MOD 2 ^ k]) :
    parityWord n k = parityWord m k := by
  have key : ∀ x : ℕ, parityWord x k = parityWord (x % 2 ^ k) k := by
    intro x
    conv_lhs => rw [← Nat.mod_add_div x (2 ^ k)]
    exact parityWord_add_mul _ k _
  rw [key n, key m, h]

/-! ## Theorem A, second half: distinct residues give distinct words -/

/-- If two integers agree on their first `k` branches then they are congruent
mod `2^k`. With the previous theorem this pins the cylinder to exactly one
residue class. -/
theorem modEq_of_parityWord {k : ℕ} :
    ∀ {n m : ℕ}, parityWord n k = parityWord m k → n ≡ m [MOD 2 ^ k] := by
  induction k with
  | zero => intro n m _; simp [Nat.ModEq, Nat.mod_one]
  | succ k ih =>
      intro n m h
      rw [parityWord_succ, parityWord_succ] at h
      have hl : letterOf n = letterOf m := (List.cons.inj h).1
      have hstep : T n ≡ T m [MOD 2 ^ k] := ih (List.cons.inj h).2
      have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      -- `omega` cannot help here: the modulus `2^k` is a variable, so the
      -- congruences are handled through `Nat.ModEq` rather than through `%`.
      rcases Nat.even_or_odd n with hn | hn
      · have hn0 : n % 2 = 0 := Nat.even_iff.mp hn
        have hm0 : m % 2 = 0 := by
          by_contra hc
          have h1 : m % 2 = 1 := by omega
          unfold letterOf at hl; rw [hn0, h1] at hl; simp at hl
        rw [T_even hn0, T_even hm0] at hstep
        have := hstep.mul_left' (c := 2)
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hn0),
          Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm0)] at this
        rwa [hpow]
      · have hn1 : n % 2 = 1 := Nat.odd_iff.mp hn
        have hm1 : m % 2 = 1 := by
          by_contra hc
          have h0 : m % 2 = 0 := by omega
          unfold letterOf at hl; rw [hn1, h0] at hl; simp at hl
        rw [T_odd hn1, T_odd hm1] at hstep
        have hdn : 2 ∣ (3 * n + 1) := by omega
        have hdm : 2 ∣ (3 * m + 1) := by omega
        have h3 := hstep.mul_left' (c := 2)
        rw [Nat.mul_div_cancel' hdn, Nat.mul_div_cancel' hdm] at h3
        rw [← hpow] at h3
        -- `3n + 1 ≡ 3m + 1` ⟹ `3n ≡ 3m` ⟹ `n ≡ m`, since 3 is coprime to 2^{k+1}
        have h4 : 3 * n ≡ 3 * m [MOD 2 ^ (k + 1)] :=
          Nat.ModEq.add_right_cancel' 1 h3
        have hcop : Nat.gcd (2 ^ (k + 1)) 3 = 1 :=
          Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left _ (by norm_num))
        exact Nat.ModEq.cancel_left_of_coprime hcop h4

/-- **Theorems A and B together.** Two integers follow the same length-`k`
parity word **iff** they are congruent mod `2^k`. -/
theorem parityWord_eq_iff_modEq (n m k : ℕ) :
    parityWord n k = parityWord m k ↔ n ≡ m [MOD 2 ^ k] :=
  ⟨modEq_of_parityWord, parityWord_of_modEq⟩

/-- **Theorem B.** `w ↦ r_w` is injective on residues, so the `2^k` words of
length `k` and the `2^k` residues mod `2^k` correspond. -/
theorem residues_injective {k : ℕ} {n m : ℕ} (hn : n < 2 ^ k) (hm : m < 2 ^ k)
    (h : parityWord n k = parityWord m k) : n = m := by
  have := modEq_of_parityWord h
  rw [Nat.ModEq, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this
  exact this

/-- Every length-`k` word is realised, so the correspondence is onto: the map
from canonical residues to words is injective between two sets of size `2^k`. -/
theorem residues_surjective (k : ℕ) :
    ((Finset.range (2 ^ k)).image (fun n => parityWord n k)).card = 2 ^ k := by
  rw [Finset.card_image_of_injOn]
  · simp
  · intro a ha b hb h
    exact residues_injective (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h

/-! ## The `r_w = 0` boundary the corrections file repairs -/

/-- The all-`D` cylinder has canonical residue `0`. -/
theorem allD_residue_zero (k : ℕ) : parityWord 0 k = List.replicate k D := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, letterOf, T, ih]

/-- **The repair, stated generally.** Every non-empty cylinder contains a
*positive* integer — so an induction may always be run on a positive member,
whatever the canonical residue is.

This is what the corrections file replaces `r_w ∈ Ω_w` with. The all-`D`
cylinder is the case that forces it: its canonical residue is `0`, and `0` is
not a positive integer, so the original phrasing had no witness there. -/
theorem cylinder_has_positive_member (k : ℕ) {w : List Letter}
    (h : ∃ n, parityWord n k = w) : ∃ n, 0 < n ∧ parityWord n k = w := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 2 ^ k, by positivity, ?_⟩
  rw [parityWord_add_pow, hn]

/-- The repair: `r_w + 2^k` is always a positive member of the same cylinder,
whatever `r_w` is. Stated for every residue, not only the awkward one. -/
theorem positive_representative (r k : ℕ) :
    0 < r + 2 ^ k ∧ parityWord (r + 2 ^ k) k = parityWord r k := by
  refine ⟨by positivity, parityWord_add_pow r k⟩

/-- The boundary made concrete: `2^k` is the positive witness for the all-`D`
word, and it does follow that word. -/
theorem allD_positive_witness (k : ℕ) :
    0 < 2 ^ k ∧ parityWord (2 ^ k) k = List.replicate k D := by
  refine ⟨by positivity, ?_⟩
  have := parityWord_add_pow 0 k
  simpa [allD_residue_zero] using this

/-! ## Theorem C — the closed congruence formula -/

/-- One step, transported to `ℚ`: the formal branch map applied to `n` is the
cast of the integer step. -/
lemma step_cast (n : ℕ) :
    Collatz.Atlas.step (letterOf n) (n : ℚ) = ((T n : ℕ) : ℚ) := by
  rcases Nat.even_or_odd n with hn | hn
  · have h0 : n % 2 = 0 := Nat.even_iff.mp hn
    have hdvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero h0
    rw [show letterOf n = D from by unfold letterOf; rw [h0]; rfl]
    rw [Collatz.Atlas.step, T_even h0,
      Nat.cast_div hdvd (by norm_num : (2 : ℚ) ≠ 0)]
    norm_num
  · have h1 : n % 2 = 1 := Nat.odd_iff.mp hn
    have hdvd : 2 ∣ (3 * n + 1) := by omega
    have hne : ¬ (n % 2 = 0) := by omega
    rw [show letterOf n = U from by unfold letterOf; rw [if_neg hne]]
    rw [Collatz.Atlas.step, T_odd h1,
      Nat.cast_div hdvd (by norm_num : (2 : ℚ) ≠ 0)]
    push_cast
    ring

/-- The dynamics agrees with Paper 02's formal operator on the cylinder: after
`k` steps from `n`, the value is `F_w(n)` where `w` is `n`'s own parity word.

This is the bridge between the `ℕ` dynamics and the `ℚ` algebra, and it holds
with no admissibility hypothesis because `w` is read off `n` itself. -/
theorem iterate_eq_F (n k : ℕ) :
    ((T^[k] n : ℕ) : ℚ) = Collatz.Atlas.F (parityWord n k) n := by
  induction k generalizing n with
  | zero => simp [Collatz.Atlas.F]
  | succ k ih =>
      rw [Function.iterate_succ_apply, parityWord_succ, Collatz.Atlas.F,
        ih (T n), step_cast]

/-- **Theorem C (§10).** For `n` following `w`, `2^k` divides `3^{u(w)} n + b_w`
— which is exactly what makes `r_w ≡ −b_w · 3^{−u} (mod 2^k)` well posed, since
`3^u` is a unit mod `2^k`. -/
theorem cylinder_congruence (n k : ℕ) :
    2 ^ k ∣ 3 ^ uCount (parityWord n k) * n + bCorr (parityWord n k) := by
  have hF := iterate_eq_F n k
  rw [Collatz.Atlas.affine_closure, length_parityWord] at hF
  have h2 : (2 : ℚ) ^ k ≠ 0 := by positivity
  have hq : ((3 ^ uCount (parityWord n k) * n + bCorr (parityWord n k) : ℕ) : ℚ)
      = ((T^[k] n : ℕ) : ℚ) * 2 ^ k := by
    push_cast
    field_simp at hF
    linarith [hF]
  have hnat : 3 ^ uCount (parityWord n k) * n + bCorr (parityWord n k)
      = T^[k] n * 2 ^ k := by exact_mod_cast hq
  exact ⟨T^[k] n, by rw [hnat]; ring⟩

/-- `3^u` really is invertible mod `2^k`, so Theorem C determines `r_w`. -/
theorem three_pow_coprime (u k : ℕ) : Nat.Coprime (3 ^ u) (2 ^ k) :=
  Nat.Coprime.pow u k (by norm_num)

/-! ## §13–§19: the charts, local identity trivialization, and exact recovery

The charts are `φ_w(n) = (n − r_w)/2^k` and `ψ_w(y) = (y − m_w)/3^u`, so they
live on `ℤ`, not `ℕ` — subtraction is essential. And §16's first display is about
the **formal** operator `F_w` on the whole cylinder `C_w = r_w + 2^k ℤ`; only its
restriction is about `T^k` on `Ω_w`. Both are done below, in that order.

`m_w` is not defined by a division here. It is taken as any integer with
`2^k · m = 3^u · r + b_w`, which is exactly what §4 establishes and what the
`r_w = 0` repair was needed for. Stating it that way keeps every proof below a
ring identity. -/

/-- `φ_w⁻¹`: the source cylinder in chart coordinates is the ordinary integer
line. -/
def cyl (r : ℤ) (k : ℕ) (a : ℤ) : ℤ := r + 2 ^ k * a

/-- `ψ_w⁻¹`: the target progression, likewise. -/
def prog (m : ℤ) (u : ℕ) (a : ℤ) : ℤ := m + 3 ^ u * a

/-- §14: `φ_w` recovers the chart coordinate. The division is exact by
construction, so this is an identity and not an approximation. -/
@[simp] theorem phi_cyl (r : ℤ) (k : ℕ) (a : ℤ) : (cyl r k a - r) / 2 ^ k = a := by
  unfold cyl
  rw [add_sub_cancel_left]
  exact Int.mul_ediv_cancel_left a (by positivity)

/-- §15: `ψ_w` recovers the chart coordinate. -/
@[simp] theorem psi_prog (m : ℤ) (u : ℕ) (a : ℤ) : (prog m u a - m) / 3 ^ u = a := by
  unfold prog
  rw [add_sub_cancel_left]
  exact Int.mul_ediv_cancel_left a (by positivity)

/-- **Theorem D (§12), Exact Cylinder Transport**, as an identity between
numerators so that no division appears: if `2^k m = 3^u r + b` then the affine
operator carries `r + 2^k a` to `m + 3^u a`. -/
theorem transport {r m b : ℤ} {k u : ℕ} (hm : 2 ^ k * m = 3 ^ u * r + b) (a : ℤ) :
    2 ^ k * prog m u a = 3 ^ u * cyl r k a + b := by
  unfold prog cyl
  linear_combination hm

/-- **Theorem E (§16), Local Identity Trivialization.** In the two charts, the
formal operator is the identity on `ℤ`: `ψ_w ∘ F_w ∘ φ_w⁻¹ = id`. -/
theorem local_identity {r m b : ℤ} {k u : ℕ} (hm : 2 ^ k * m = 3 ^ u * r + b)
    (a : ℤ) : ((3 ^ u * cyl r k a + b) / 2 ^ k - m) / 3 ^ u = a := by
  rw [← transport hm a, Int.mul_ediv_cancel_left _ (by positivity), psi_prog]

/-- **Theorem F (§18), Exact Recovery.** The source is recovered from the target
with no loss, given the word's data. -/
theorem exact_recovery {r m : ℤ} {k u : ℕ} (a : ℤ) :
    cyl r k ((prog m u a - m) / 3 ^ u) = cyl r k a := by
  rw [psi_prog]

/-- §19, Faithfulness: distinct chart coordinates give distinct integers, so the
trivialization loses nothing. -/
theorem cyl_injective (r : ℤ) (k : ℕ) : Function.Injective (cyl r k) := by
  intro a b h
  unfold cyl at h
  have h2 : (2 : ℤ) ^ k ≠ 0 := by positivity
  exact mul_left_cancel₀ h2 (add_left_cancel h)

/-- …and the same for the target progression. -/
theorem prog_injective (m : ℤ) (u : ℕ) : Function.Injective (prog m u) := by
  intro a b h
  unfold prog at h
  have h3 : (3 : ℤ) ^ u ≠ 0 := by positivity
  exact mul_left_cancel₀ h3 (add_left_cancel h)

/-! ### The restriction to the positive dynamical domain

Everything above is about the formal operator. This is the part that is about
`T^k`, and it needs the bridge `iterate_eq_F` rather than a ring identity. -/

/-- The numerator identity for the real dynamics: `2^k · T^k(n) = 3^u n + b_w`,
with `w` read off `n`. This is `cylinder_congruence` with the quotient named. -/
theorem iterate_numerator (n k : ℕ) :
    (2 : ℤ) ^ k * (T^[k] n : ℤ)
      = 3 ^ uCount (parityWord n k) * (n : ℤ) + bCorr (parityWord n k) := by
  have hF := iterate_eq_F n k
  rw [Collatz.Atlas.affine_closure, length_parityWord] at hF
  have h2 : (2 : ℚ) ^ k ≠ 0 := by positivity
  field_simp at hF
  have : ((2 ^ k * (T^[k] n) : ℕ) : ℚ)
      = ((3 ^ uCount (parityWord n k) * n + bCorr (parityWord n k) : ℕ) : ℚ) := by
    push_cast
    linarith [hF]
  have hnat : 2 ^ k * T^[k] n
      = 3 ^ uCount (parityWord n k) * n + bCorr (parityWord n k) := by
    exact_mod_cast this
  exact_mod_cast congrArg (fun x : ℕ => (x : ℤ)) hnat

/-- **§16's restriction.** On the positive domain, `T^k` is the identity in the
two charts: for any `a` with `r + 2^k a` a natural number following `w`, the
chart coordinate of `T^k` of it is `a` again. -/
theorem local_identity_dynamical (n k : ℕ) {r m : ℤ}
    (hr : (n : ℤ) = cyl r k ((((n : ℤ)) - r) / 2 ^ k))
    (hm : 2 ^ k * m = 3 ^ uCount (parityWord n k) * r
            + bCorr (parityWord n k)) :
    ((T^[k] n : ℤ) - m) / 3 ^ uCount (parityWord n k) = ((n : ℤ) - r) / 2 ^ k := by
  set a : ℤ := ((n : ℤ) - r) / 2 ^ k with ha
  have hnum : (2 : ℤ) ^ k * (T^[k] n : ℤ)
      = 3 ^ uCount (parityWord n k) * cyl r k a + bCorr (parityWord n k) := by
    rw [← hr]; exact iterate_numerator n k
  have h2 : (2 : ℤ) ^ k ≠ 0 := by positivity
  have hTk : (T^[k] n : ℤ) = prog m (uCount (parityWord n k)) a := by
    have := transport hm a
    have heq : (2 : ℤ) ^ k * (T^[k] n : ℤ)
        = 2 ^ k * prog m (uCount (parityWord n k)) a := by rw [hnum, this]
    exact mul_left_cancel₀ h2 heq
  rw [hTk, psi_prog]

end Collatz.Cylinder
