/-
# Paper 09 — the stopping-time equivalence, and why a bounded run means something

數學戰士「墜衡」 / AMRAL Research Lab.

Queue item 5. Paper 09 §2 defines the coefficient stopping time

    σ(n) = inf { j ≥ 1 : T^j(n) < n },   σ(n) = ∞ if there is none,

and §3–§4 prove `Collatz ⟺ ∀ n > 1, σ(n) < ∞`. The queue's note on this item was
that Theorem A "is what makes every finite verification meaningful, so having it
formal is worth more than its difficulty suggests" — and that is the reason it is
here, because the difficulty really is low.

Three things are proved beyond the equivalence itself:

* **`reaches_one_of_bounded_stopping`.** Verifying `σ(n) < ∞` on `[2, N]` proves
  Collatz on `[1, N]`. This is what a bounded computation actually establishes —
  the companion arm's exhaustive `[3, 2^40]` descent run is exactly an instance —
  and the paper implies it without stating it separately, so it is stated here.
* **`no_uniform_depth`.** §52 warns that `∀n ∃k` must not be swapped for
  `∃k ∀n`. That warning is a *theorem*, and its counterexample is the all-ones
  witness family from `Collatz/AllOnes.lean`: for every depth `k ≥ 1`,
  `2^{k+1} − 1` has not descended after `k` steps.
* **`sigma_spec`.** Where `σ` is finite it is the *least* such `j`, so the
  definition by `Nat.find` matches the paper's `inf`.

`σ` itself is not given a value at `∞`; the finiteness is carried as the
proposition `HasFiniteStoppingTime`. Introducing `ℕ∞` would add a coercion to
every statement and prove nothing extra.
-/

import Mathlib.Tactic
import Collatz.AllOnes
import Collatz.ResidueCylinder
import Collatz.Valuation

namespace Collatz.Stopping

open Collatz.Cylinder (T)

/-! ## Basic facts about the modified map -/

/-- `T` keeps positive integers positive. -/
lemma T_pos {n : ℕ} (hn : 0 < n) : 0 < T n := by
  rcases Nat.even_or_odd n with he | ho
  · have h0 : n % 2 = 0 := Nat.even_iff.mp he
    rw [Collatz.Cylinder.T_even h0]
    omega
  · have h1 : n % 2 = 1 := Nat.odd_iff.mp ho
    rw [Collatz.Cylinder.T_odd h1]
    omega

/-- …hence so does every iterate. -/
lemma iterate_pos {n : ℕ} (hn : 0 < n) : ∀ j, 0 < T^[j] n := by
  intro j
  induction j with
  | zero => simpa using hn
  | succ j ih => rw [Function.iterate_succ_apply']; exact T_pos ih

/-- `n` reaches `1`. With the *modified* map `1 → 2 → 1`, so this is the right
notion of "the orbit terminates". -/
def Reaches1 (n : ℕ) : Prop := ∃ j, T^[j] n = 1

@[simp] lemma reaches1_one : Reaches1 1 := ⟨0, rfl⟩

/-! ## §2: the coefficient stopping time -/

/-- §2: `σ(n) < ∞`, carried as a proposition rather than as a value in `ℕ∞`. -/
def HasFiniteStoppingTime (n : ℕ) : Prop := ∃ j, 1 ≤ j ∧ T^[j] n < n

/-- §2's `σ`, where it is finite. -/
noncomputable def sigma {n : ℕ} (h : HasFiniteStoppingTime n) : ℕ :=
  Nat.find (p := fun j => 1 ≤ j ∧ T^[j] n < n) ⟨h.choose, h.choose_spec⟩

/-- `σ` is the **least** `j ≥ 1` that descends, so `Nat.find` really is §2's
`inf` and not merely some witness. -/
theorem sigma_spec {n : ℕ} (h : HasFiniteStoppingTime n) :
    (1 ≤ sigma h ∧ T^[sigma h] n < n)
      ∧ ∀ j, j < sigma h → ¬ (1 ≤ j ∧ T^[j] n < n) := by
  refine ⟨Nat.find_spec (p := fun j => 1 ≤ j ∧ T^[j] n < n) _, ?_⟩
  intro j hj
  exact Nat.find_min (p := fun j => 1 ≤ j ∧ T^[j] n < n) _ hj

/-! ## §3–§4: the equivalence -/

/-- **Theorem 3.1.** Finite stopping time everywhere implies Collatz.

Strong induction on `n`: a descent to `T^j(n) < n` hands the goal to a strictly
smaller positive integer. -/
theorem reaches_one_of_finite_stopping
    (h : ∀ n, 1 < n → HasFiniteStoppingTime n) :
    ∀ n, 0 < n → Reaches1 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn
      rcases Nat.eq_or_lt_of_le (show 1 ≤ n from hn) with h1 | h1
      · exact h1 ▸ reaches1_one
      · obtain ⟨j, hj1, hjlt⟩ := h n h1
        obtain ⟨i, hi⟩ := ih (T^[j] n) hjlt (iterate_pos hn j)
        exact ⟨i + j, by rw [Function.iterate_add_apply, hi]⟩

/-- **Theorem 4.1, converse direction.** Collatz implies finite stopping time:
the first visit to `1` is already a descent below any `n > 1`. -/
theorem finite_stopping_of_reaches_one
    (h : ∀ n, 0 < n → Reaches1 n) :
    ∀ n, 1 < n → HasFiniteStoppingTime n := by
  intro n hn
  obtain ⟨j, hj⟩ := h n (by omega)
  refine ⟨j, ?_, by rw [hj]; omega⟩
  rcases Nat.eq_zero_or_pos j with hz | hp
  · exfalso; rw [hz] at hj; simp at hj; omega
  · exact hp

/-- **Theorem 4.1.** `Collatz ⟺ ∀ n > 1, σ(n) < ∞`. -/
theorem collatz_iff_finite_stopping :
    (∀ n, 0 < n → Reaches1 n) ↔ (∀ n, 1 < n → HasFiniteStoppingTime n) :=
  ⟨finite_stopping_of_reaches_one, reaches_one_of_finite_stopping⟩

/-! ## What a bounded verification establishes

The equivalence above is a statement about all of `ℕ`. A computation only ever
checks an interval, so the useful form is the bounded one — and it is the same
induction, because a descent from `n ≤ N` lands strictly below `n` and therefore
still inside the interval. -/

/-- **The bounded form.** Verifying `σ(n) < ∞` for every `1 < n ≤ N` proves that
every positive `n ≤ N` reaches `1`.

This is exactly what an exhaustive descent run over an interval establishes, and
it is why such a run is evidence about that interval rather than about nothing.
It is **not** evidence about `N + 1`. -/
theorem reaches_one_of_bounded_stopping (N : ℕ)
    (h : ∀ n, 1 < n → n ≤ N → HasFiniteStoppingTime n) :
    ∀ n, 0 < n → n ≤ N → Reaches1 n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn hN
      rcases Nat.eq_or_lt_of_le (show 1 ≤ n from hn) with h1 | h1
      · exact h1 ▸ reaches1_one
      · obtain ⟨j, hj1, hjlt⟩ := h n h1 hN
        obtain ⟨i, hi⟩ := ih (T^[j] n) hjlt (iterate_pos hn j) (by omega)
        exact ⟨i + j, by rw [Function.iterate_add_apply, hi]⟩

/-! ## §52: the quantifiers may not be swapped

`∀n ∃k, T^k(n) < n` is the hypothesis. `∃k ∀n, T^k(n) < n` — a *uniform* descent
depth — is much stronger, and false. The witness is the all-ones family from
`Collatz/AllOnes.lean`: `2^{k+1} − 1` spends its first `k` accelerated steps at
exponent `1`, so `k` modified steps and `k` accelerated steps coincide, and the
value has *grown* by a factor of `(3/2)^k`. -/

/-- For the all-ones witness, `k` accelerated steps are `k` modified steps,
because every exponent along the way is `1`. -/
lemma allOnes_iterate (k : ℕ) :
    T^[k] (Collatz.allOnesStart k) = Collatz.orbit (Collatz.allOnesStart k) k := by
  have hodd : Collatz.allOnesStart k % 2 = 1 := by
    unfold Collatz.allOnesStart
    have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    have h2 : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (by omega)
    omega
  have hK : Collatz.Valuation.Kcum
      (Collatz.Valuation.valWord (Collatz.allOnesStart k) k) = k := by
    unfold Collatz.Valuation.Kcum Collatz.Valuation.valWord
    have hmap : (List.range k).map
          (fun i => Collatz.kappa (Collatz.orbit (Collatz.allOnesStart k) i))
        = (List.range k).map (fun _ => 1) := by
      apply List.map_congr_left
      intro i hi
      exact Collatz.kappa_allOnes k i (List.mem_range.mp hi)
    rw [hmap]
    simp
  rw [Collatz.Valuation.orbit_eq_iterate hodd k, hK]

/-- **§52.** There is no uniform descent depth: for every `k ≥ 1` some `n > 1`
has not descended after `k` steps. So the Collatz hypothesis cannot be weakened
to a single `k`, and no finite computation can establish it by exhibiting one. -/
theorem no_uniform_depth :
    ¬ ∃ k, 1 ≤ k ∧ ∀ n, 1 < n → T^[k] n < n := by
  rintro ⟨k, hk1, hk⟩
  have hn1 : 1 < Collatz.allOnesStart k := by
    unfold Collatz.allOnesStart
    have h4 : 4 ≤ 2 ^ (k + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  -- the orbit value has GROWN: `Y_k + 1 = 3^k · 2` while `n + 1 = 2^{k+1}`
  have hY : Collatz.orbit (Collatz.allOnesStart k) k + 1
      = 3 ^ k * 2 ^ (k + 1 - k) := Collatz.orbit_allOnes k k le_rfl
  rw [show k + 1 - k = 1 from by omega, pow_one] at hY
  have hnv : Collatz.allOnesStart k + 1 = 2 ^ (k + 1) := by
    unfold Collatz.allOnesStart
    have h1 : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
    omega
  have hlt : (2 : ℕ) ^ (k + 1) < 3 ^ k * 2 := by
    have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 := by ring
    have h3 : (2 : ℕ) ^ k < 3 ^ k := Nat.pow_lt_pow_left (by norm_num) (by omega)
    omega
  have hdesc := hk (Collatz.allOnesStart k) hn1
  rw [allOnes_iterate k] at hdesc
  omega

/-! ## The two arms

The companion arm's exhaustive run is a bounded stopping-time verification, and
`reaches_one_of_bounded_stopping` is what licenses reading it as a statement about
its interval. There is deliberately **no** theorem here bridging the bounded
conclusion to the unbounded one: that gap is the conjecture, and
`no_uniform_depth` is the precise reason no computation of any fixed depth can
close it. -/

end Collatz.Stopping
