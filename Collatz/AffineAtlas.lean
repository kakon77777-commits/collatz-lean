/-
# Paper 02 — the finite-word affine closure, for all words

數學戰士「墜衡」 / AMRAL Research Lab.

Queue item 1. Neo.K's *Collatz Local Affine Atlas* (Series paper 02) proves that
every finite parity word acts on `ℚ` as one affine map, and that the whole of a
`k`-step branch history compresses to the triple `(k, u, b_w)`. Its six theorems
are all inductions on word length and need nothing beyond `ℤ` and `ℚ`.

The finite arm checked them exhaustively to `k ≤ 16` — 131,070 words — against a
referee that assumes none of them. So the statements were never in doubt. What
is added here is the quantifier, and one thing a finite check cannot give: the
`b_w` machinery in a form every later queue item can reuse.

## Conventions, taken from the paper and not from convenience

- `D x = x / 2`, `U x = (3x+1)/2` (§1, the *modified* map `T`, which folds the
  forced division into the odd branch).
- A word is read **left to right**, so `F_w = σ_k ∘ ⋯ ∘ σ₁` (§2). Consequently
  matrices multiply in the *opposite* order to reading, `M_w = M_{σ_k} ⋯ M_{σ₁}`
  (§16), and Theorem E is stated that way here rather than the way that would
  look tidier.
- `F_w` is a formal operator on all of `ℚ`. Whether a given `n` actually follows
  `w` is a separate question — §3's distinction between formal legality and
  dynamical legality — and nothing below assumes admissibility.

`b_w` is defined by the recursion that matches `List`'s own (cons on the left);
the paper's right-append recurrence (Theorem B) is then *proved*, as a corollary
of Theorem D. Defining it the paper's way and recursing the other way would have
buried the content in list-reversal lemmas.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

namespace Collatz.Atlas

/-! ## Words -/

/-- A parity letter: `D` halves, `U` is the odd branch. -/
inductive Letter
  | D : Letter
  | U : Letter
  deriving DecidableEq, Repr

open Letter

/-- §1: the two branch maps of the modified Collatz map `T`. -/
def step : Letter → ℚ → ℚ
  | D, x => x / 2
  | U, x => (3 * x + 1) / 2

/-- §2: the formal operator of a word, executed **left to right**. -/
def F : List Letter → ℚ → ℚ
  | [], x => x
  | (σ :: v), x => F v (step σ x)

/-- §4: `u w`, the number of `U`s in `w`. -/
def uCount : List Letter → ℕ
  | [] => 0
  | (D :: v) => uCount v
  | (U :: v) => uCount v + 1

/-- §6: the order correction `b_w`, by recursion on the head of the word.

The paper's recurrence appends on the right; this one prepends, which is what
`List` recurses on. They agree — that is Theorem B below. -/
def bCorr : List Letter → ℕ
  | [] => 0
  | (D :: v) => 2 * bCorr v
  | (U :: v) => 3 ^ uCount v + 2 * bCorr v

@[simp] lemma uCount_nil : uCount [] = 0 := rfl
@[simp] lemma uCount_cons_D (v : List Letter) : uCount (D :: v) = uCount v := rfl
@[simp] lemma uCount_cons_U (v : List Letter) : uCount (U :: v) = uCount v + 1 := rfl
@[simp] lemma bCorr_nil : bCorr [] = 0 := rfl
@[simp] lemma bCorr_cons_D (v : List Letter) : bCorr (D :: v) = 2 * bCorr v := rfl
@[simp] lemma bCorr_cons_U (v : List Letter) :
    bCorr (U :: v) = 3 ^ uCount v + 2 * bCorr v := rfl

@[simp] lemma uCount_append (w v : List Letter) :
    uCount (w ++ v) = uCount w + uCount v := by
  induction w with
  | nil => simp
  | cons σ t ih => cases σ <;> simp [ih] <;> omega

lemma uCount_le_length (w : List Letter) : uCount w ≤ w.length := by
  induction w with
  | nil => simp
  | cons σ t ih => cases σ <;> simp <;> omega

/-! ## Theorem A — finite-word affine closure -/

/-- **Theorem A (§4).** Every finite word acts on `ℚ` as a single affine map:
`F_w(x) = (3^{u(w)} x + b_w) / 2^{|w|}`, for every rational `x`. -/
theorem affine_closure (w : List Letter) (x : ℚ) :
    F w x = (3 ^ uCount w * x + bCorr w) / 2 ^ w.length := by
  induction w generalizing x with
  | nil => simp [F]
  | cons σ v ih =>
      have h2 : (2 : ℚ) ^ v.length ≠ 0 := by positivity
      cases σ with
      | D =>
          rw [F, step, ih, List.length_cons, uCount_cons_D, bCorr_cons_D]
          push_cast
          field_simp
          ring
      | U =>
          rw [F, step, ih, List.length_cons, uCount_cons_U, bCorr_cons_U]
          push_cast
          field_simp
          ring

/-! ## Theorems D and B — concatenation, and the paper's recurrence -/

/-- **Theorem D (§14).** `b_{wv} = 3^{u(v)} b_w + 2^{|w|} b_v`.

Stated for the *execution* order: `w` runs first, then `v`. -/
theorem bCorr_append (w v : List Letter) :
    bCorr (w ++ v) = 3 ^ uCount v * bCorr w + 2 ^ w.length * bCorr v := by
  induction w with
  | nil => simp
  | cons σ t ih =>
      cases σ with
      | D => simp [ih, List.length_cons, pow_succ]; ring
      | U =>
          simp [ih, List.length_cons, pow_succ, uCount_append, pow_add]
          ring

/-- **Theorem B (§6), first half.** Appending a `D` leaves the correction alone. -/
theorem bCorr_append_D (w : List Letter) : bCorr (w ++ [D]) = bCorr w := by
  simp [bCorr_append]

/-- **Theorem B (§6), second half.** Appending a `U` sends `b ↦ 3b + 2^{|w|}`. -/
theorem bCorr_append_U (w : List Letter) :
    bCorr (w ++ [U]) = 3 * bCorr w + 2 ^ w.length := by
  simp [bCorr_append]

/-- §14's order defect, as an identity rather than a slogan: swapping the two
halves changes only the correction coordinate, by exactly this much. -/
theorem order_defect (w v : List Letter) :
    (bCorr (w ++ v) : ℤ) - bCorr (v ++ w)
      = bCorr w * (3 ^ uCount v - 2 ^ v.length)
        - bCorr v * (3 ^ uCount w - 2 ^ w.length) := by
  rw [bCorr_append, bCorr_append]
  push_cast
  ring

/-! ## Theorem C — the closed form -/

/-- **Theorem C (§7).** `b_w = Σ_t 2^{j_t − 1} 3^{u−t}` over the positions `j_t`
of the `U`s.

In zero-based form: position `i` contributes `2^i · 3^(number of U's strictly
after it)` when the letter there is `U`, and nothing otherwise. -/
theorem bCorr_closed_form (w : List Letter) :
    bCorr w = ∑ i ∈ Finset.range w.length,
      (if (w.drop i).head? = some U then 2 ^ i * 3 ^ uCount (w.drop (i + 1)) else 0) := by
  induction w with
  | nil => simp
  | cons σ v ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.drop_zero, List.head?_cons, List.drop_succ_cons]
      have hshift : ∀ i, (2 : ℕ) ^ (i + 1) = 2 * 2 ^ i := fun i => by ring
      cases σ with
      | D =>
          simp only [reduceCtorEq, if_false, add_zero, bCorr_cons_D, ih]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          by_cases h : (v.drop i).head? = some U <;> simp [h, hshift i] <;> ring
      | U =>
          simp only [if_true, bCorr_cons_U, ih]
          rw [Finset.mul_sum, add_comm]
          congr 1
          · refine Finset.sum_congr rfl fun i _ => ?_
            by_cases h : (v.drop i).head? = some U <;> simp [h, hshift i] <;> ring
          · simp

/-! ## Theorem E — the matrix representation -/

/-- §15: an upper-triangular matrix for `x ↦ (Ax+B)/D`. -/
def M (w : List Letter) : Matrix (Fin 2) (Fin 2) ℕ :=
  !![3 ^ uCount w, bCorr w; 0, 2 ^ w.length]

/-- **Theorem E (§16).** Word concatenation becomes matrix multiplication — in
the **opposite** order, because a word is read left to right while composition
applies the last letter last: `M_w = M_{σ_k} ⋯ M_{σ₁}`. -/
theorem M_append (w v : List Letter) : M (w ++ v) = M v * M w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [M, Matrix.mul_apply, Fin.sum_univ_succ, bCorr_append, pow_add,
      uCount_append, List.length_append] <;> ring

/-- The two generators of §15. -/
@[simp] theorem M_D : M [D] = !![1, 0; 0, 2] := by simp [M]
@[simp] theorem M_U : M [U] = !![3, 1; 0, 2] := by simp [M]

/-! ## Theorem F — the order extremes -/

/-- The minimising word of §21: all `U`s first. -/
def wMin (k u : ℕ) : List Letter := List.replicate u U ++ List.replicate (k - u) D

/-- The maximising word of §21: all `U`s last. -/
def wMax (k u : ℕ) : List Letter := List.replicate (k - u) D ++ List.replicate u U

@[simp] lemma uCount_replicate_U (n : ℕ) : uCount (List.replicate n U) = n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

@[simp] lemma uCount_replicate_D (n : ℕ) : uCount (List.replicate n D) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

@[simp] lemma bCorr_replicate_D (n : ℕ) : bCorr (List.replicate n D) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

/-- §22: `b(U^u) = 3^u − 2^u`, stated without natural subtraction. -/
theorem bCorr_replicate_U (n : ℕ) : bCorr (List.replicate n U) + 2 ^ n = 3 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, bCorr_cons_U, uCount_replicate_U]
      rw [pow_succ, pow_succ]
      omega

/-- **Theorem F (§23), lower bound.** `3^u − 2^u ≤ b_w`, subtraction-free. -/
theorem bCorr_lower (w : List Letter) : 3 ^ uCount w ≤ bCorr w + 2 ^ uCount w := by
  induction w with
  | nil => simp
  | cons σ v ih =>
      cases σ with
      | D =>
          simp only [uCount_cons_D, bCorr_cons_D]
          omega
      | U =>
          simp only [uCount_cons_U, bCorr_cons_U, pow_succ]
          omega

/-- **Theorem F (§23), upper bound.** `b_w ≤ 2^{k−u}(3^u − 2^u)`, subtraction-free:
`b_w + 2^k ≤ 2^{k−u} · 3^u`. -/
theorem bCorr_upper (w : List Letter) :
    bCorr w + 2 ^ w.length ≤ 2 ^ (w.length - uCount w) * 3 ^ uCount w := by
  induction w with
  | nil => simp
  | cons σ v ih =>
      have hu : uCount v ≤ v.length := uCount_le_length v
      cases σ with
      | D =>
          simp only [uCount_cons_D, bCorr_cons_D, List.length_cons]
          have hlen : v.length + 1 - uCount v = (v.length - uCount v) + 1 := by omega
          rw [hlen, pow_succ, pow_succ]
          nlinarith [ih, Nat.zero_le (bCorr v)]
      | U =>
          simp only [uCount_cons_U, bCorr_cons_U, List.length_cons]
          have hlen : v.length + 1 - (uCount v + 1) = v.length - uCount v := by omega
          rw [hlen, pow_succ 2 v.length, pow_succ 3 (uCount v)]
          have hpow : (2 : ℕ) ^ uCount v ≤ 2 ^ v.length :=
            Nat.pow_le_pow_right (by norm_num) hu
          have hlow : 3 ^ uCount v ≤ bCorr v + 2 ^ uCount v := bCorr_lower v
          nlinarith [ih, hpow, hlow]

/-- The two bounds are attained, so Theorem F is sharp and not merely true.
`u = k` forces `w = U^k` and the bounds coincide (§24). -/
theorem extremes_attained (n : ℕ) :
    bCorr (List.replicate n U) + 2 ^ (List.replicate n U).length
      = 2 ^ ((List.replicate n U).length - uCount (List.replicate n U))
        * 3 ^ uCount (List.replicate n U) := by
  simp [bCorr_replicate_U n]

/-! ## Enumeration, for the cross-check against the finite arm -/

/-- Every word of a given length. -/
def allWords : ℕ → List (List Letter)
  | 0 => [[]]
  | (n + 1) => (allWords n).flatMap (fun w => [D :: w, U :: w])

/-- A word as a number: the letter at position `i` is bit `i`, `U = 1`.

The cross-check emits this alongside each `b_w` so the other side can rebuild
the word itself rather than trusting that both sides enumerate in the same
order — an agreement that came from a shared ordering would prove nothing. -/
def encode : List Letter → ℕ
  | [] => 0
  | (D :: v) => 2 * encode v
  | (U :: v) => 1 + 2 * encode v

theorem length_allWords (n : ℕ) : (allWords n).length = 2 ^ n := by
  induction n with
  | zero => simp [allWords]
  | succ n ih => simp [allWords, List.length_flatMap, ih, pow_succ]

end Collatz.Atlas
