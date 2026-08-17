/-
# Paper 08 — where each RCOT theorem stops, stated for every ring at once

數學戰士「墜衡」 / AMRAL Research Lab.

Queue item 7, the last one. The queue rated it **least leverage**, on the ground
that this arm's finite witnesses already tell a reader where each theorem stops
applying — `RUN-002-OT-SERIES.md` §8 carries a concrete witness for every rung of
the ladder. That is right about Theorems B, C and G, whose universally quantified
forms add the quantifier and nothing else.

It is wrong about two of them, and reading the paper rather than the queue entry is
what showed it — the same correction that item 5 needed.

* **Theorem A** is the abstract form of the whole series' slogan: *counts determine
  the multiplicative skeleton, order determines the affine correction*. Over a
  commutative ring `A_w` and `D_w` are permutation-invariant and `B_w` is not, and
  a finite witness can exhibit the second half but cannot state the first.
* **Theorem D** turns "contraction is not a property of the operator" into three
  inequalities about **one** operator. Paper 02's own word `UUDD` gives
  `λ = 9/16`, which is an archimedean contraction, a `2`-adic expansion and a
  `3`-adic contraction simultaneously. No finite table of Collatz orbits states
  that, because the object it is about is the choice of absolute value.

## What is proved

Theorems A–G of §51, each as the paper states it, plus the witnesses that keep the
hypotheses from being vacuous. In particular §14's distinction is proved in both
directions: **non-unit does not imply non-injective** (`2` in `ℤ`), and a zero
divisor does (`2` in `ℤ/6`). Those two control different structures — residue
uniqueness and exact recovery — and the paper is explicit that conflating them
would be an error.

## What is not proved

Nothing here bears on Collatz. Every theorem is a statement about which algebraic
property a *method* needs, and the Collatz case appears only as the instance where
each hypothesis happens to hold.
-/

import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree
import Collatz.AffineAtlas

namespace Collatz.Domains

open Collatz.Atlas (Letter uCount bCorr)
open Collatz.Atlas.Letter

/-! ## §5: a branch, over any commutative ring

A branch is the affine datum `x ↦ (a x + b) / d`, carried as a triple so that the
statements about `A_w`, `B_w`, `D_w` can be made before any division exists. Paper
02 worked over `ℚ` throughout; the point of Paper 08 is that the *algebra* of the
triples needs only a commutative ring. -/

/-- A branch: the numerator coefficients `a`, `b` and the denominator `d` of
`x ↦ (a x + b) / d`. -/
structure Branch (R : Type*) [CommRing R] where
  a : R
  b : R
  d : R
  deriving DecidableEq

variable {R : Type*} [CommRing R]

/-- The multiplicative skeleton: the product of the branch multipliers. -/
def Aw : List (Branch R) → R
  | [] => 1
  | (σ :: v) => σ.a * Aw v

/-- The denominator skeleton. -/
def Dw : List (Branch R) → R
  | [] => 1
  | (σ :: v) => σ.d * Dw v

/-- The affine correction. A word runs **left to right** — `F_w = σ_k ∘ ⋯ ∘ σ₁` —
so composing `σ` onto the front of `v` gives
`(A_v (a x + b) + d B_v) / (d D_v)`, hence this recursion. Paper 08's §5 closed
form `B_w = Σ_j b_j (∏_{ℓ>j} a_ℓ)(∏_{ℓ<j} d_ℓ)` is what it unrolls to: the head
term is `b · A_v` with an empty `d`-product, and `d · B_v` supplies the `d`-prefix
for every later position. -/
def Bw : List (Branch R) → R
  | [] => 0
  | (σ :: v) => Aw v * σ.b + σ.d * Bw v

@[simp] lemma Aw_nil : Aw ([] : List (Branch R)) = 1 := rfl
@[simp] lemma Dw_nil : Dw ([] : List (Branch R)) = 1 := rfl
@[simp] lemma Bw_nil : Bw ([] : List (Branch R)) = 0 := rfl

@[simp] lemma Aw_cons (σ : Branch R) (v : List (Branch R)) :
    Aw (σ :: v) = σ.a * Aw v := rfl

@[simp] lemma Dw_cons (σ : Branch R) (v : List (Branch R)) :
    Dw (σ :: v) = σ.d * Dw v := rfl

@[simp] lemma Bw_cons (σ : Branch R) (v : List (Branch R)) :
    Bw (σ :: v) = Aw v * σ.b + σ.d * Bw v := rfl

/-! ## Theorem A: the skeleton is a product, the correction is not

`A_w` and `D_w` are products over the word, so in a **commutative** ring they see
only which branches occur and how often. That is the precise form of "counts
determine the multiplicative skeleton", and it is a statement about all words at
once — a finite table cannot make it. -/

theorem Aw_eq_prod (w : List (Branch R)) : Aw w = (w.map Branch.a).prod := by
  induction w with
  | nil => simp
  | cons σ v ih => simp [ih]

theorem Dw_eq_prod (w : List (Branch R)) : Dw w = (w.map Branch.d).prod := by
  induction w with
  | nil => simp
  | cons σ v ih => simp [ih]

/-- **Counts determine the multiplicative skeleton.** Reordering a word leaves
`A_w` alone. -/
theorem Aw_perm {w v : List (Branch R)} (h : w.Perm v) : Aw w = Aw v := by
  rw [Aw_eq_prod, Aw_eq_prod]
  exact (h.map Branch.a).prod_eq

theorem Dw_perm {w v : List (Branch R)} (h : w.Perm v) : Dw w = Dw v := by
  rw [Dw_eq_prod, Dw_eq_prod]
  exact (h.map Branch.d).prod_eq

/-! ### and the other half is a separation, not an absence of proof

"Order determines the affine correction" is only content if some reordering
actually moves `B_w`. The witness is Collatz's own two branches. -/

/-- Collatz's `D` branch, `x ↦ x/2`. -/
def bD : Branch ℤ := ⟨1, 0, 2⟩

/-- Collatz's `U` branch, `x ↦ (3x+1)/2`. -/
def bU : Branch ℤ := ⟨3, 1, 2⟩

/-- **Order determines the affine correction**, and the witness is the Collatz
pair itself: `UD` and `DU` are permutations of each other with the same `A_w` and
the same `D_w`, and different `B_w`. So `Aw_perm` cannot be strengthened. -/
theorem Bw_not_perm_invariant :
    ∃ w v : List (Branch ℤ), w.Perm v ∧ Aw w = Aw v ∧ Dw w = Dw v ∧ Bw w ≠ Bw v := by
  refine ⟨[bU, bD], [bD, bU], List.Perm.swap _ _ _, ?_, ?_, ?_⟩
  · simp [Aw, bU, bD]
  · simp [Dw, bU, bD]
  · simp [Bw, Aw, bU, bD]

/-! ## Theorem A, the closure itself

Over a field, with every denominator nonzero, the word operator **is** the single
affine map the skeleton and correction describe. This is Paper 02's Theorem A with
`(3,1,2)` and `(1,0,2)` replaced by arbitrary branch data. -/

variable {K : Type*} [Field K]

/-- The action of one branch. -/
def step (σ : Branch K) (x : K) : K := (σ.a * x + σ.b) / σ.d

/-- The word operator, left to right, matching Paper 02's `F`. -/
def F : List (Branch K) → K → K
  | [], x => x
  | (σ :: v), x => F v (step σ x)

/-- The denominator skeleton of a word with nonzero denominators is nonzero. Stated
separately because `affine_closure` needs it at every step of its induction. -/
theorem Dw_ne_zero {w : List (Branch K)} (hd : ∀ σ ∈ w, σ.d ≠ 0) : Dw w ≠ 0 := by
  induction w with
  | nil => simp
  | cons σ v ih =>
      have hσ : σ.d ≠ 0 := hd σ (by simp)
      have hv : ∀ τ ∈ v, τ.d ≠ 0 := fun τ hτ => hd τ (by simp [hτ])
      simpa [Dw_cons] using mul_ne_zero hσ (ih hv)

/-- **Theorem A.** `F_w(x) = (A_w x + B_w) / D_w`, for every word whose
denominators are all nonzero.

The induction has to generalise `x`: the word runs left to right, so the tail is
applied to `step σ x` rather than to `x`, and an induction hypothesis fixed at the
original `x` cannot be used. Same shape as the `parityWord` periodicity trap in
Paper 03, where the hypothesis had to be quantified over all odd multipliers. -/
theorem affine_closure (w : List (Branch K)) (hd : ∀ σ ∈ w, σ.d ≠ 0) (x : K) :
    F w x = (Aw w * x + Bw w) / Dw w := by
  induction w generalizing x with
  | nil => simp [F]
  | cons σ v ih =>
      have hσ : σ.d ≠ 0 := hd σ (by simp)
      have hv : ∀ τ ∈ v, τ.d ≠ 0 := fun τ hτ => hd τ (by simp [hτ])
      have hDv : Dw v ≠ 0 := Dw_ne_zero hv
      rw [F, ih hv, step, Aw_cons, Bw_cons, Dw_cons]
      field_simp
      ring

/-! ## and it recovers Paper 02

Paper 08 says the general theorem specialises to the earlier papers. That is a
claim about a *previous* development, which is the one kind of claim a finite check
cannot make, so it is proved. The two developments are defined independently:
`bCorr` recurses on Paper 02's own `Letter`, and `Bw` on a triple of ring elements
that knows nothing about `3`, `1` or `2`. -/

/-- Paper 02's two branches as Paper 08 branch data over `ℚ`. -/
def toBranch : Letter → Branch ℚ
  | D => ⟨1, 0, 2⟩
  | U => ⟨3, 1, 2⟩

@[simp] lemma toBranch_D : toBranch D = ⟨1, 0, 2⟩ := rfl
@[simp] lemma toBranch_U : toBranch U = ⟨3, 1, 2⟩ := rfl

theorem Aw_toBranch (w : List Letter) : Aw (w.map toBranch) = 3 ^ uCount w := by
  induction w with
  | nil => simp
  | cons σ v ih => cases σ <;> simp [ih, pow_succ, mul_comm]

theorem Dw_toBranch (w : List Letter) : Dw (w.map toBranch) = 2 ^ w.length := by
  induction w with
  | nil => simp
  | cons σ v ih => cases σ <;> simp [ih, pow_succ, mul_comm]

/-- **Paper 08's Theorem A specialises to Paper 02's `b_w`.** The general affine
correction over an arbitrary commutative ring, evaluated at the Collatz branch
data, *is* the correction Paper 02 defines by its own recursion. -/
theorem Bw_toBranch (w : List Letter) : Bw (w.map toBranch) = (bCorr w : ℚ) := by
  induction w with
  | nil => simp
  | cons σ v ih =>
      cases σ
      · simp [Collatz.Atlas.bCorr, ih]
      · simp [Collatz.Atlas.bCorr, ih, Aw_toBranch]

/-- and the operators agree, not merely their coefficients. -/
theorem F_toBranch (w : List Letter) (x : ℚ) :
    F (w.map toBranch) x = Collatz.Atlas.F w x := by
  induction w generalizing x with
  | nil => simp [F, Collatz.Atlas.F]
  | cons σ v ih =>
      cases σ <;> simp [F, Collatz.Atlas.F, step, Collatz.Atlas.step, ih]

/-! ## Theorem B: the quotient-unit criterion

§8. `A_w x + B_w ≡ 0 (mod I)` has a **unique** solution as soon as `[A_w]` is a
unit in `R / I`. §9 is the other half: when it is not a unit the multiplication map
need not be a bijection, so the word-to-residue chart can have no solution, several
solutions, or a unique one by accident — and "one word ↔ one residue" stops being a
structural theorem. -/

/-- The algebraic core, in any commutative ring. -/
theorem unique_solution_of_isUnit {S : Type*} [CommRing S] {A B : S} (hA : IsUnit A) :
    ∃! x : S, A * x + B = 0 := by
  obtain ⟨u, rfl⟩ := hA
  refine ⟨-(↑u⁻¹ * B), by simp [mul_comm, mul_left_comm], fun y hy => ?_⟩
  have : (u : S) * y = -B := by linear_combination hy
  calc y = ↑u⁻¹ * ((u : S) * y) := by
            rw [← mul_assoc]; simp [← Units.val_mul]
    _ = -(↑u⁻¹ * B) := by rw [this]; ring

/-- **Theorem B**, in the paper's own form: over any commutative ring and any
ideal, `[A_w] ∈ (R/I)^×` gives a unique residue chart. -/
theorem unique_residue_chart {R : Type*} [CommRing R] (I : Ideal R) (A B : R)
    (hA : IsUnit (Ideal.Quotient.mk I A)) :
    ∃! x : R ⧸ I, Ideal.Quotient.mk I A * x + Ideal.Quotient.mk I B = 0 :=
  unique_solution_of_isUnit hA

/-- **The Collatz case satisfies the hypothesis automatically**, which is §8's
closing remark: `A_w = 3^u` and `I = (2^k)`, and `gcd(3^u, 2^k) = 1`. -/
theorem collatz_multiplier_isUnit (u k : ℕ) : IsUnit ((3 : ZMod (2 ^ k)) ^ u) := by
  refine IsUnit.pow u ?_
  have h3 : ((3 : ℕ) : ZMod (2 ^ k)) = (3 : ZMod (2 ^ k)) := by push_cast; ring
  rw [← h3, ZMod.isUnit_iff_coprime]
  exact Nat.Coprime.pow_right k (by norm_num)

/-! ### §10's witness: without the unit hypothesis, both failures occur -/

/-- `2x ≡ 2 (mod 6)` has **two** solutions, named rather than merely asserted to
exist: `1` and `4`. -/
theorem mod_six_two_solutions :
    (2 : ZMod 6) * 1 + (-2) = 0 ∧ (2 : ZMod 6) * 4 + (-2) = 0 ∧ (1 : ZMod 6) ≠ 4 := by
  refine ⟨by decide, by decide, by decide⟩

/-- so uniqueness genuinely fails. -/
theorem mod_six_not_unique :
    ¬ ∃! x : ZMod 6, (2 : ZMod 6) * x + (-2) = 0 := by
  rintro ⟨z, -, hz⟩
  have h1 : (1 : ZMod 6) = z := hz 1 (by decide)
  have h4 : (4 : ZMod 6) = z := hz 4 (by decide)
  exact absurd (h1.trans h4.symm) (by decide)

/-- `2x ≡ 1 (mod 6)` has **no** solution, so existence fails too. The two failures
are different, and §9 lists them separately. -/
theorem mod_six_no_solution : ¬ ∃ x : ZMod 6, (2 : ZMod 6) * x + (-1) = 0 := by decide

/-- and `[2]` really is not a unit mod `6`, so these are instances of §9 rather
than of some other obstruction. -/
theorem two_not_isUnit_mod_six : ¬ IsUnit (2 : ZMod 6) := by
  have h : ((2 : ℕ) : ZMod 6) = (2 : ZMod 6) := by push_cast; ring
  rw [← h, ZMod.isUnit_iff_coprime]
  decide

/-! ## Theorem C: the regular-multiplier recovery criterion, and §14's distinction

§13. `A` regular makes `x ↦ Ax + B` injective, so exact recovery survives. §14 is
the part worth formalising: **non-unit does not imply non-injective.** `2` in `ℤ` is
not a unit and multiplication by it is injective anyway. The two properties control
different structures — unit-ness modulo the ideal controls residue *uniqueness*,
regularity in the state algebra controls exact *recovery* — and the paper says
plainly that conflating them would be an error. -/

/-- **Theorem C.** A regular multiplier makes the affine map injective. -/
theorem injective_of_isRegular {S : Type*} [CommRing S] {A : S} (hA : IsLeftRegular A)
    (B : S) : Function.Injective (fun x : S => A * x + B) := by
  intro x y hxy
  exact hA (by simpa using add_right_cancel hxy)

/-- **§14, first half: non-unit does not imply non-injective.** `2` is not a unit in
`ℤ`, and `x ↦ 2x + B` is injective regardless, because `ℤ` is a domain. -/
theorem nonunit_not_noninjective :
    ¬ IsUnit (2 : ℤ) ∧ ∀ B : ℤ, Function.Injective (fun x : ℤ => 2 * x + B) := by
  refine ⟨by simp [Int.isUnit_iff], fun B => injective_of_isRegular ?_ B⟩
  exact (IsRegular.of_ne_zero (by norm_num : (2 : ℤ) ≠ 0)).left

/-- **§14, second half: a zero divisor does.** `2` is a zero divisor in `ℤ/6`, and
there multiplication by it is not injective — `2·1 = 2·4`. So the hypothesis of
Theorem C is not automatic, and the two sections are about different failures. -/
theorem zero_divisor_breaks_recovery :
    (2 : ZMod 6) * 3 = 0 ∧ ¬ Function.Injective (fun x : ZMod 6 => 2 * x + 0) := by
  refine ⟨by decide, fun h => ?_⟩
  have : (1 : ZMod 6) = 4 := h (by decide)
  exact absurd this (by decide)

/-! ## Theorem D: contraction is the operator **plus** a chosen absolute value

§22. This is the item the queue undersold. The Lipschitz identity itself is one
line in any absolute value; the content is that the *same* `λ` is a contraction in
one and an expansion in another, so "`F` contracts" is not a property of `F`. Paper
02's own word `UUDD` is the witness the paper picks, and its coefficients are
computed here rather than quoted. -/

theorem padicNorm_pow (p : ℕ) [Fact p.Prime] (q : ℚ) (n : ℕ) :
    padicNorm p (q ^ n) = padicNorm p q ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, padicNorm.mul, ih, pow_succ]

/-- **Theorem D, archimedean.** An affine map scales distances by exactly `|λ|`. -/
theorem abs_lipschitz (lam c x y : ℚ) :
    |(lam * x + c) - (lam * y + c)| = |lam| * |x - y| := by
  have h : (lam * x + c) - (lam * y + c) = lam * (x - y) := by ring
  rw [h, abs_mul]

/-- **Theorem D, `p`-adic.** The same identity, in any `p`-adic absolute value. The
proof is the same one line, which is the point: the identity is not what varies. -/
theorem padic_lipschitz (p : ℕ) [Fact p.Prime] (lam c x y : ℚ) :
    padicNorm p ((lam * x + c) - (lam * y + c)) = padicNorm p lam * padicNorm p (x - y) := by
  have h : (lam * x + c) - (lam * y + c) = lam * (x - y) := by ring
  rw [h, padicNorm.mul]

/-- Paper 02's word `UUDD`, the paper's own example. -/
def UUDD : List Letter := [U, U, D, D]

/-- **The paper's coefficients, computed rather than quoted.** §22 asserts
`F_{UUDD}(x) = (9x+5)/16`; here that is read off `Aw`, `Bw`, `Dw` at the Collatz
branch data. `Bw = 5` is the one that could have been mistyped, and is not. -/
theorem UUDD_coefficients :
    Aw (UUDD.map toBranch) = 9 ∧ Bw (UUDD.map toBranch) = 5 ∧
      Dw (UUDD.map toBranch) = 16 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [UUDD, Aw, Bw, Dw, toBranch]

/-- and therefore the operator is what the paper says it is. -/
theorem UUDD_operator (x : ℚ) : F (UUDD.map toBranch) x = (9 * x + 5) / 16 := by
  obtain ⟨hA, hB, hD⟩ := UUDD_coefficients
  rw [affine_closure _ (by intro σ hσ; fin_cases hσ <;> norm_num [toBranch]), hA, hB, hD]

/-- The Lipschitz factor of `UUDD`. -/
def lam : ℚ := 9 / 16

theorem lam_archimedean : |lam| < 1 := by
  rw [lam, abs_of_pos (by norm_num)]; norm_num

theorem lam_two_adic : padicNorm 2 lam = 16 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h9 : padicNorm 2 (9 : ℚ) = 1 := by
    have h : (9 : ℚ) = ((9 : ℕ) : ℚ) := by norm_num
    rw [h, padicNorm.nat_eq_one_iff]; decide
  have h16 : padicNorm 2 (16 : ℚ) = 1 / 16 := by
    have h : (16 : ℚ) = (((2 : ℕ) : ℚ)) ^ 4 := by norm_num
    rw [h, padicNorm_pow, padicNorm.padicNorm_p (by norm_num : 1 < 2)]
    norm_num
  rw [lam, padicNorm.div, h9, h16]; norm_num

theorem lam_three_adic : padicNorm 3 lam = 1 / 9 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h9 : padicNorm 3 (9 : ℚ) = 1 / 9 := by
    have h : (9 : ℚ) = (((3 : ℕ) : ℚ)) ^ 2 := by norm_num
    rw [h, padicNorm_pow, padicNorm.padicNorm_p (by norm_num : 1 < 3)]
    norm_num
  have h16 : padicNorm 3 (16 : ℚ) = 1 := by
    have h : (16 : ℚ) = ((16 : ℕ) : ℚ) := by norm_num
    rw [h, padicNorm.nat_eq_one_iff]; decide
  rw [lam, padicNorm.div, h9, h16]; norm_num

/-- **`contraction = operator + chosen valuation`, as three inequalities about one
number.** `λ = 9/16` is an archimedean contraction, a `2`-adic **expansion** and a
`3`-adic contraction. So no property of the operator alone decides the question. -/
theorem contraction_is_geometry_relative :
    |lam| < 1 ∧ 1 < padicNorm 2 lam ∧ padicNorm 3 lam < 1 := by
  refine ⟨lam_archimedean, ?_, ?_⟩
  · rw [lam_two_adic]; norm_num
  · rw [lam_three_adic]; norm_num

/-- and spelled out on an actual pair of points, so that "expansion" is a statement
about distances rather than about a coefficient. -/
theorem same_operator_contracts_and_expands :
    ∃ x y : ℚ, x ≠ y ∧
      |lam * x - lam * y| < |x - y| ∧
      padicNorm 2 (x - y) < padicNorm 2 (lam * x - lam * y) := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  refine ⟨1, 0, by norm_num, ?_, ?_⟩
  · rw [show lam * 1 - lam * 0 = lam by ring, show (1 : ℚ) - 0 = 1 by ring]
    simpa using lam_archimedean
  · rw [show lam * 1 - lam * 0 = lam by ring, show (1 : ℚ) - 0 = 1 by ring,
      padicNorm.one, lam_two_adic]
    norm_num

/-! ## Theorem E: the first breakage of the multiplicative skeleton

§28. `Aw_perm` above used commutativity and nothing else. Drop it and the theorem
is false, not merely unproven: equal branch counts no longer determine the leading
word operator. The paper's witness is the pair of unipotent matrices. -/

/-- The paper's first matrix. -/
def MA : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]

/-- The paper's second. -/
def MB : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 1, 1]

theorem MA_mul_MB_ne : MA * MB ≠ MB * MA := by
  intro h
  have h00 : (MA * MB) 0 0 = (MB * MA) 0 0 := by rw [h]
  simp [MA, MB, Matrix.mul_apply, Fin.sum_univ_succ] at h00

/-- **Theorem E.** The multiset of branch multipliers does **not** determine their
product once they fail to commute — so `Aw_perm` is exactly as strong as its
commutativity hypothesis, and no stronger. -/
theorem counts_do_not_determine_skeleton :
    ∃ w v : List (Matrix (Fin 2) (Fin 2) ℤ), w.Perm v ∧ w.prod ≠ v.prod := by
  refine ⟨[MA, MB], [MB, MA], List.Perm.swap _ _ _, ?_⟩
  simpa using MA_mul_MB_ne

/-! ## Theorem G: nonlinear degree growth

§50. `deg(f ∘ g) = deg f · deg g` over an integral domain is mathlib's
`Polynomial.natDegree_comp`; the paper's conclusion is what it implies, namely that
a degree `> 1` map leaves **every** fixed-degree class rather than some particular
one. That is the statement worth having, because a finite table of iterates can
only exhibit growth up to where it stops. -/

variable {D : Type*} [CommRing D] [IsDomain D]

/-- The `n`-fold composite of `f` with itself, with `iterComp f 0 = X`. -/
noncomputable def iterComp (f : Polynomial D) : ℕ → Polynomial D
  | 0 => Polynomial.X
  | (n + 1) => (iterComp f n).comp f

/-- **Theorem G.** The degree of the `n`-th iterate is exactly `(deg f)^n`. -/
theorem natDegree_iterComp (f : Polynomial D) (n : ℕ) :
    (iterComp f n).natDegree = f.natDegree ^ n := by
  induction n with
  | zero => simp [iterComp]
  | succ n ih => rw [iterComp, Polynomial.natDegree_comp, ih, pow_succ]

/-- **and therefore degree `> 1` iteration escapes every fixed-degree class.** For
any bound `N`, some iterate exceeds it. This is the sense in which the affine and
projective atlases are left behind: not "eventually", but for a computable `n`. -/
theorem escapes_every_fixed_degree (f : Polynomial D) (hf : 1 < f.natDegree) (N : ℕ) :
    ∃ n, N < (iterComp f n).natDegree := by
  refine ⟨N, ?_⟩
  rw [natDegree_iterComp]
  exact Nat.lt_pow_self hf

/-- Non-vacuity: the hypothesis is satisfiable, and the growth is the stated one.
`X^2` over `ℤ` has iterates of degree `1, 2, 4, 8`. -/
theorem square_iterates_degrees :
    ((List.range 4).map fun n =>
      (iterComp (Polynomial.X ^ 2 : Polynomial ℤ) n).natDegree) = [1, 2, 4, 8] := by
  have hd : (Polynomial.X ^ 2 : Polynomial ℤ).natDegree = 2 := by
    simp [Polynomial.natDegree_pow]
  simp only [natDegree_iterComp, hd]
  decide

/-! ## Theorem F is deliberately absent

§40's projective rung — Möbius finite-word closure survives while
arithmetic-progression transport generally fails — is **not** formalised here.
Stating the failure needs a formal notion of "transport of an arithmetic
progression along a Möbius map", and building one to support a single negative
remark would be machinery in place of content. The finite witness in
`RUN-002-OT-SERIES.md` §8 already exhibits it, and the queue is right that in that
case the quantifier is all that would be added.

Recording the gap is the point. An omission that is written down is a different
object from one that is not. -/

end Collatz.Domains
