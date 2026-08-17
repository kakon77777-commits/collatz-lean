/-
# Paper 09 Theorem F — the counterexample equivalence, without leaving `ℕ`

數學戰士「墜衡」 / AMRAL Research Lab.

Queue item 5's second half, and with it item 5. The queue expected this to need
`PadicInt` and "the eventual-stabilisation characterisation of an ordinary
positive integer inside `ℤ₂`". Reading §42–§47 rather than the queue's summary,
it does not. `ℤ₂` is needed for the *interpretation* — what a non-anchored branch
converges to — but every claim in Theorem 47.1 is about canonical residues
`r_k = n mod 2^k`, and §44's content is simply that `n mod 2^k = n` once
`2^k > n`. So the whole theorem lives in `ℕ`.

## What is proved

* **§44, `residue_stabilises`.** A chain coming from an ordinary positive integer
  has canonical residues that are eventually constant at `n`. That is the whole
  of "integer-anchored".
* **§43, `nested_not_always_anchored`.** The caution that a formal infinite branch
  need not be a positive-integer counterexample, as a *theorem*: the chain
  `r_k = 2^k − 1` is nested and anchored at no positive integer at all. Its
  `2`-adic value is `−1`, which is exactly §43's "negative integer" case — but the
  statement needs no `ℤ₂` to make, because non-stabilisation is visible in `ℕ`.
* **§47, `no_stopping_iff_hard_forever`.** Theorem 47.1's (1) ⟺ (2) ⟺ (3).
* **§48, `collatz_iff_no_anchored_hard_branch`.** The minimal obstruction form:
  Collatz holds iff no `n > 1` stays hard at every depth.

## What is not proved

The `ℤ₂` reading of §42–§43 — that the limit of a non-anchored branch *is* a
specific 2-adic integer, negative or otherwise — is not formalised. It is not
needed for Theorem 47.1 or §48, and stating it would add `PadicInt` machinery to
support a remark rather than a step. The queue entry should be corrected on this
point, and is.
-/

import Mathlib.Tactic
import Collatz.ResidueCylinder
import Collatz.StoppingTime
import Collatz.HardSet

namespace Collatz.Anchored

open Collatz.Cylinder (T parityWord)
open Collatz.Stopping (Reaches1 HasFiniteStoppingTime)
open Collatz.HardSet (Hard)

/-! ## §42, §44: canonical residues of a chain -/

/-- §44: the canonical representative of `n` at depth `k`. -/
def residue (n k : ℕ) : ℕ := n % 2 ^ k

/-- A chain of canonical residues is **nested**: each refines the last, and each
is canonical for its depth. This is §42's compatibility condition, which is what
makes the chain define an inverse-limit point. -/
def Nested (r : ℕ → ℕ) : Prop := ∀ k, r (k + 1) % 2 ^ k = r k ∧ r k < 2 ^ k

/-- §45: the chain is **anchored at `n`** if its residues are eventually `n`. -/
def Anchored (r : ℕ → ℕ) (n : ℕ) : Prop := ∃ K, ∀ k, K ≤ k → r k = n

/-- The residues of an actual integer form a nested chain. -/
theorem nested_residue (n : ℕ) : Nested (residue n) := by
  intro k
  refine ⟨?_, Nat.mod_lt _ (by positivity)⟩
  unfold residue
  rw [Nat.mod_mod_of_dvd n (pow_dvd_pow 2 (Nat.le_succ k))]

/-- **§44.** The chain of an ordinary positive integer stabilises at `n`, from the
first depth with `2^k > n`. This is all "integer-anchored" means. -/
theorem residue_stabilises (n : ℕ) : Anchored (residue n) n := by
  refine ⟨n + 1, fun k hk => ?_⟩
  have h : n < 2 ^ k := lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_of_lt_succ
    (Nat.lt_succ_of_le (le_trans hk (Nat.le_of_lt (Nat.lt_two_pow_self)))))
  exact Nat.mod_eq_of_lt h

/-! ## §43: a nested chain need not be anchored at any integer

This is the caution the section makes, as a theorem. `2^k − 1` is a perfectly
good nested chain of canonical residues — it is what the all-`U`-ish prefixes
give — and it is anchored at nothing, because it is strictly increasing. Its
`2`-adic value is `−1`; that reading needs `ℤ₂`, but the *non-anchoring* does
not. -/

/-- The chain `2^k − 1`, named rather than a lambda so that `omega` and `rw` can
see through it. -/
def allOnesResidue (k : ℕ) : ℕ := 2 ^ k - 1

/-- `r_k = 2^k − 1` is a nested chain of canonical residues. -/
theorem nested_allOnes : Nested allOnesResidue := by
  intro k
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
  refine ⟨?_, by unfold allOnesResidue; omega⟩
  unfold allOnesResidue
  have hsplit : (2 : ℕ) ^ (k + 1) - 1 = 2 ^ k + (2 ^ k - 1) := by omega
  rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- **§43.** That chain is anchored at **no** integer. So the existence of an
infinite formal branch does not by itself produce a positive-integer
counterexample — which is exactly why §47 has to say *integer-anchored*. -/
theorem nested_not_always_anchored : ¬ ∃ n, Anchored allOnesResidue n := by
  rintro ⟨n, K, hK⟩
  have h1 := hK K le_rfl
  have h2 := hK (K + 1) (Nat.le_succ K)
  unfold allOnesResidue at h1 h2
  have hp : (1 : ℕ) ≤ 2 ^ K := Nat.one_le_two_pow
  have hgrow : (2 : ℕ) ^ (K + 1) = 2 * 2 ^ K := by ring
  omega

/-- Together: being nested is strictly weaker than being anchored. -/
theorem anchored_strictly_stronger :
    (∃ r, Nested r ∧ ¬ ∃ n, Anchored r n)
    ∧ (∀ n, Nested (residue n) ∧ Anchored (residue n) n) :=
  ⟨⟨allOnesResidue, nested_allOnes, nested_not_always_anchored⟩,
   fun n => ⟨nested_residue n, residue_stabilises n⟩⟩

/-! ## §47: the counterexample equivalence -/

/-- `σ(n) = ∞`, as the negation of `HasFiniteStoppingTime`. -/
def NoFiniteStoppingTime (n : ℕ) : Prop := ∀ j, 1 ≤ j → n ≤ T^[j] n

/-- The two readings of `σ(n) = ∞` agree. -/
theorem noFinite_iff_not_hasFinite (n : ℕ) :
    NoFiniteStoppingTime n ↔ ¬ HasFiniteStoppingTime n := by
  unfold NoFiniteStoppingTime HasFiniteStoppingTime
  constructor
  · rintro h ⟨j, hj1, hjlt⟩
    exact absurd (h j hj1) (by omega)
  · intro h j hj1
    by_contra hc
    exact h ⟨j, hj1, by omega⟩

/-- **Theorem 47.1, (1) ⟺ (2) ⟺ (3).** For `n > 1`, `σ(n) = ∞` is the same as
staying hard at every finite depth — which, by `residue_stabilises`, is the same
as `n`'s parity-prefix chain being an integer-anchored infinite hard branch.

The third condition adds nothing for an ordinary integer, and that is the point:
anchoring is automatic once the branch comes from one. -/
theorem no_stopping_iff_hard_forever {n : ℕ} (hn : 1 < n) :
    NoFiniteStoppingTime n ↔ ∀ k, Hard k n := by
  constructor
  · intro h k
    exact ⟨by omega, fun j hj1 _ => h j hj1⟩
  · intro h j hj1
    exact (h j).2 j hj1 le_rfl

/-- The anchored-branch form of the same statement, with the anchoring exhibited
rather than assumed. -/
theorem hard_forever_iff_anchored_hard {n : ℕ} (hn : 1 < n) :
    (∀ k, Hard k n) ↔ (Anchored (residue n) n ∧ ∀ k, Hard k n) :=
  ⟨fun h => ⟨residue_stabilises n, h⟩, fun h => h.2⟩

/-! ## §48: the minimal obstruction form -/

/-- **Theorem 48.1.** Collatz holds **iff** there is no `n > 1` that stays hard at
every depth — that is, iff no integer-anchored infinite hard branch exists.

This is the series' own "cleanest global remainder statement", and it is where
this whole development stops: the right-hand side is not decided here, and
nothing in this repository bears on whether it is true. -/
theorem collatz_iff_no_anchored_hard_branch :
    (∀ n, 0 < n → Reaches1 n) ↔ ¬ ∃ n, 1 < n ∧ ∀ k, Hard k n := by
  rw [Collatz.Stopping.collatz_iff_finite_stopping]
  constructor
  · rintro h ⟨n, hn, hhard⟩
    have := (noFinite_iff_not_hasFinite n).mp
      ((no_stopping_iff_hard_forever hn).mpr hhard)
    exact this (h n hn)
  · intro h n hn
    by_contra hc
    exact h ⟨n, hn, (no_stopping_iff_hard_forever hn).mp
      ((noFinite_iff_not_hasFinite n).mpr hc)⟩

/-- …and the obstruction is not vacuously absent: at every *fixed* depth there
really are hard integers, so the statement is about an infinite intersection
being empty, not about each stage being empty. -/
theorem hard_at_each_depth_is_nonempty (k : ℕ) : ∃ n, Hard k n := by
  -- The witness is `allOnesStart (k+1)`, one step longer than the depth.
  -- `allOnesStart k` does NOT work: at `k = 0` it is `1`, and `Hard 0 1` fails on
  -- the `2 ≤ n` clause. The first version of this proof used it, and the
  -- statement was false at `k = 0`.
  refine ⟨Collatz.allOnesStart (k + 1), ?_, fun j hj1 hjk => ?_⟩
  · unfold Collatz.allOnesStart
    have h4 : (4 : ℕ) ≤ 2 ^ (k + 1 + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have hjk' : j ≤ k + 1 := hjk.trans (Nat.le_succ k)
    -- kept in terms of `allOnesStart (k+1)` throughout: unfolding it in one place
    -- and not the other makes two atoms out of one and `omega` loses the link
    have hY : Collatz.orbit (Collatz.allOnesStart (k + 1)) j + 1
        = 3 ^ j * 2 ^ (k + 1 + 1 - j) := Collatz.orbit_allOnes (k + 1) j hjk'
    have hn2 : Collatz.allOnesStart (k + 1) + 1 = 2 ^ (k + 1 + 1) := by
      unfold Collatz.allOnesStart
      have h1 : 1 ≤ 2 ^ (k + 1 + 1) := Nat.one_le_two_pow
      omega
    have hodd : Collatz.allOnesStart (k + 1) % 2 = 1 := by
      have h2 : 2 ∣ 2 ^ (k + 1 + 1) := dvd_pow_self 2 (by omega)
      omega
    have hiter : T^[j] (Collatz.allOnesStart (k + 1))
        = Collatz.orbit (Collatz.allOnesStart (k + 1)) j := by
      have hK : Collatz.Valuation.Kcum
          (Collatz.Valuation.valWord (Collatz.allOnesStart (k + 1)) j) = j := by
        unfold Collatz.Valuation.Kcum Collatz.Valuation.valWord
        have hmap : (List.range j).map
              (fun i => Collatz.kappa
                (Collatz.orbit (Collatz.allOnesStart (k + 1)) i))
            = (List.range j).map (fun _ => 1) := by
          apply List.map_congr_left
          intro i hi
          exact Collatz.kappa_allOnes (k + 1) i
            (lt_of_lt_of_le (List.mem_range.mp hi) hjk')
        rw [hmap]; simp
      rw [Collatz.Valuation.orbit_eq_iterate hodd j, hK]
    rw [hiter]
    have hsplit : (2 : ℕ) ^ (k + 1 + 1) = 2 ^ j * 2 ^ (k + 1 + 1 - j) := by
      rw [← pow_add, Nat.add_sub_cancel' (hjk'.trans (Nat.le_succ (k + 1)))]
    have hmono : (2 : ℕ) ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by norm_num) j
    have hmul : (2 : ℕ) ^ j * 2 ^ (k + 1 + 1 - j) ≤ 3 ^ j * 2 ^ (k + 1 + 1 - j) :=
      Nat.mul_le_mul_right _ hmono
    omega

end Collatz.Anchored
