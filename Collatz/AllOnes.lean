/-
# The finite-local no-go — the all-one exponent code and its realization

數學戰士「墜衡」 / AMRAL Research Lab.

The first item off `LEAN-QUEUE.md`, and deliberately not the most famous one. It
is the cheapest entry in the queue and the one with the most leverage, because
it is a statement about **proof methods**: it retires a whole strategy class.

Round 03-A.5 §5–§6 of Neo.K's Hard-Zeta line observes that the all-one
accelerated exponent code is subcritical at every prefix and is realized by the
concrete integer `2^(m+1) - 1`. Arbitrarily long zero-occupancy prefixes
therefore exist, so **no finite forbidden-pattern argument can finish the A
line** — whatever finite pattern you forbid, a genuine positive integer avoids it
for as long as you like.

The finite arm of this project verified all of this to `m = 40` by exact integer
arithmetic. Instantiation is not the claim. What is added here is the
quantifier: `∀ m`.

Everything below is elementary — `ℕ`, `padicValNat 2`, and one parity argument.
No real numbers appear, because the subcriticality condition `K_j < j log₂ 3` is
equivalent to the integer statement `2 ^ K_j < 3 ^ j`, and that is how it is
stated here.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace Collatz

/-! ## The accelerated map -/

/-- `v₂ n` is the 2-adic valuation, written for readability. -/
abbrev v₂ (n : ℕ) : ℕ := padicValNat 2 n

/-- The exponent the accelerated (shortcut) map spends at `n`: `κ(n) = v₂(3n+1)`. -/
def kappa (n : ℕ) : ℕ := v₂ (3 * n + 1)

/-- The accelerated map `S n = (3n+1) / 2 ^ v₂(3n+1)`, which sends odd to odd. -/
def S (n : ℕ) : ℕ := (3 * n + 1) / 2 ^ kappa n

/-- The accelerated orbit of `n`. -/
def orbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | (i + 1) => S (orbit n i)

/-- `K n m = Σ_{i<m} κ(Y_i)`, the cumulative exponent after `m` accelerated steps. -/
def K (n : ℕ) (m : ℕ) : ℕ := ∑ i ∈ Finset.range m, kappa (orbit n i)

/-! ## Two valuation lemmas -/

/-- An odd number has 2-adic valuation zero. -/
lemma v₂_eq_zero_of_odd {k : ℕ} (hk : Odd k) : v₂ k = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  rw [Nat.two_dvd_ne_zero]
  simpa [Nat.odd_iff] using hk

/-- Twice an odd number has 2-adic valuation exactly one. -/
lemma v₂_two_mul_odd {k : ℕ} (hk : Odd k) : v₂ (2 * k) = 1 := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  show padicValNat 2 (2 * k) = 1
  rw [padicValNat.mul (by norm_num) hk0, padicValNat.self (by norm_num)]
  rw [show padicValNat 2 k = v₂ k from rfl, v₂_eq_zero_of_odd hk]

/-! ## The witness family -/

/-- §5's witness: the smallest integer realizing the length-`m` all-one code. -/
def allOnesStart (m : ℕ) : ℕ := 2 ^ (m + 1) - 1

/-- The orbit invariant, stated **without natural subtraction**: after `i` steps
the orbit value is one less than `3^i · 2^(m+1-i)`.

This is the whole content of §5. Everything else is bookkeeping. -/
theorem orbit_allOnes (m : ℕ) :
    ∀ i ≤ m, orbit (allOnesStart m) i + 1 = 3 ^ i * 2 ^ (m + 1 - i) := by
  intro i
  induction i with
  | zero =>
      intro _
      have h : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      simp [orbit, allOnesStart, Nat.sub_add_cancel h]
  | succ i ih =>
      intro hi
      have hi' : i ≤ m := Nat.le_of_succ_le hi
      have hY : orbit (allOnesStart m) i + 1 = 3 ^ i * 2 ^ (m + 1 - i) := ih hi'
      -- `m + 1 - i = (m - i) + 1` because `i ≤ m`
      have hsplit : m + 1 - i = (m - i) + 1 := by omega
      -- the successor's value, before we know its valuation
      have hodd : Odd (3 ^ (i + 1) * 2 ^ (m - i) - 1) := by
        have h1 : 1 ≤ 3 ^ (i + 1) * 2 ^ (m - i) :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have heven : 2 ∣ 3 ^ (i + 1) * 2 ^ (m - i) := by
          have : 0 < m - i := by omega
          exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
        rcases heven with ⟨c, hc⟩
        refine ⟨c - 1, ?_⟩
        omega
      -- `3 * Y_i + 1 = 2 * (3^(i+1) * 2^(m-i) - 1)`
      have hstep : 3 * orbit (allOnesStart m) i + 1
          = 2 * (3 ^ (i + 1) * 2 ^ (m - i) - 1) := by
        have h3 : 3 * (orbit (allOnesStart m) i + 1) = 3 ^ (i + 1) * 2 ^ (m + 1 - i) := by
          rw [hY]; ring
        rw [hsplit] at h3
        have h1 : 1 ≤ 3 ^ (i + 1) * 2 ^ (m - i) :=
          Nat.one_le_iff_ne_zero.mpr (by positivity)
        have : 3 ^ (i + 1) * 2 ^ ((m - i) + 1) = 2 * (3 ^ (i + 1) * 2 ^ (m - i)) := by ring
        omega
      have hk : kappa (orbit (allOnesStart m) i) = 1 := by
        unfold kappa
        rw [hstep, v₂_two_mul_odd hodd]
      have h1 : 1 ≤ 3 ^ (i + 1) * 2 ^ (m - i) :=
        Nat.one_le_iff_ne_zero.mpr (by positivity)
      show orbit (allOnesStart m) (i + 1) + 1 = 3 ^ (i + 1) * 2 ^ (m + 1 - (i + 1))
      have hm : m + 1 - (i + 1) = m - i := by omega
      rw [hm, orbit, S, hk, hstep]
      simp only [pow_one]
      omega

/-- **The all-one code is realized.** Every one of the first `m` accelerated
exponents of `2^(m+1) - 1` is exactly `1`. -/
theorem kappa_allOnes (m : ℕ) :
    ∀ i < m, kappa (orbit (allOnesStart m) i) = 1 := by
  intro i hi
  have hY : orbit (allOnesStart m) i + 1 = 3 ^ i * 2 ^ (m + 1 - i) :=
    orbit_allOnes m i (Nat.le_of_lt hi)
  have hsplit : m + 1 - i = (m - i) + 1 := by omega
  have hodd : Odd (3 ^ (i + 1) * 2 ^ (m - i) - 1) := by
    have h1 : 1 ≤ 3 ^ (i + 1) * 2 ^ (m - i) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have heven : 2 ∣ 3 ^ (i + 1) * 2 ^ (m - i) :=
      Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
    rcases heven with ⟨c, hc⟩
    exact ⟨c - 1, by omega⟩
  have hstep : 3 * orbit (allOnesStart m) i + 1 = 2 * (3 ^ (i + 1) * 2 ^ (m - i) - 1) := by
    have h3 : 3 * (orbit (allOnesStart m) i + 1) = 3 ^ (i + 1) * 2 ^ (m + 1 - i) := by
      rw [hY]; ring
    rw [hsplit] at h3
    have h1 : 1 ≤ 3 ^ (i + 1) * 2 ^ (m - i) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have : 3 ^ (i + 1) * 2 ^ ((m - i) + 1) = 2 * (3 ^ (i + 1) * 2 ^ (m - i)) := by ring
    omega
  unfold kappa
  rw [hstep, v₂_two_mul_odd hodd]

/-- The cumulative exponent of the witness is exactly `m`. -/
theorem K_allOnes (m : ℕ) : K (allOnesStart m) m = m := by
  unfold K
  rw [Finset.sum_congr rfl (fun i hi => kappa_allOnes m i (Finset.mem_range.mp hi))]
  simp

/-- **Subcriticality at every prefix.** `K_j < j log₂ 3` is the integer statement
`2 ^ K_j < 3 ^ j`; for the all-one code that is `2^j < 3^j`. -/
theorem subcritical_allOnes (m : ℕ) :
    ∀ j, 0 < j → j ≤ m → 2 ^ K (allOnesStart m) j < 3 ^ j := by
  intro j hj hjm
  have hK : K (allOnesStart m) j = j := by
    unfold K
    rw [Finset.sum_congr rfl (fun i hi =>
      kappa_allOnes m i (lt_of_lt_of_le (Finset.mem_range.mp hi) hjm))]
    simp
  rw [hK]
  exact Nat.pow_lt_pow_left (by norm_num) (by omega)

/-- **Sharpness.** The run of ones ends exactly at `m`: the very next exponent
is at least `2`, because `3 · Y_m + 1 = 2 · (3^(m+1) - 1)` and `3^(m+1) - 1` is
even. So the witness realizes the all-one code of length `m` and no longer. -/
theorem kappa_at_m_ge_two (m : ℕ) : 2 ≤ kappa (orbit (allOnesStart m) m) := by
  have hY : orbit (allOnesStart m) m + 1 = 3 ^ m * 2 ^ (m + 1 - m) :=
    orbit_allOnes m m le_rfl
  have hm : m + 1 - m = 1 := by omega
  rw [hm, pow_one] at hY
  -- `3 * Y_m + 1 = 4 * ((3^(m+1) - 1) / 2)`, i.e. `4 ∣ 3 * Y_m + 1`
  have hodd : Odd (3 ^ (m + 1)) := Odd.pow (by decide)
  obtain ⟨c, hc⟩ := hodd
  have hval : 3 * orbit (allOnesStart m) m + 1 = 4 * c := by omega
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : (3 : ℕ) ^ (m + 1) = 1 := by omega
    have h1 : 3 ^ 1 ≤ 3 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  unfold kappa
  show 2 ≤ padicValNat 2 (3 * orbit (allOnesStart m) m + 1)
  rw [hval, show (4 : ℕ) = 2 ^ 2 from rfl]
  rw [padicValNat.mul (by positivity) hc0, padicValNat.prime_pow]
  omega

/-! ## The no-go -/

/-- The number of the first `m` exponents that exceed 1 — the "occupancy" a
finite forbidden-pattern argument would need to bound below. -/
def occupancy (n m : ℕ) : ℕ :=
  ((Finset.range m).filter (fun i => 2 ≤ kappa (orbit n i))).card

/-- The witness has **zero** occupancy over its whole prefix. -/
theorem occupancy_allOnes (m : ℕ) : occupancy (allOnesStart m) m = 0 := by
  unfold occupancy
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  rw [kappa_allOnes m i (Finset.mem_range.mp hi)]
  omega

/-- **The finite-local no-go (A.5 §5–§6).**

There is no positive lower bound `g` on occupancy that holds for every start: for
each `m` there is a positive integer whose first `m` accelerated exponents are
all `1`, whose every prefix is subcritical, and whose occupancy is therefore `0`.

Any argument that finishes the A line by forbidding a *finite* pattern of
exponents is refuted by this family, because the pattern it forbids is avoided
outright for `m` steps and `m` is arbitrary. -/
theorem finite_local_no_go :
    ¬ ∃ g : ℕ → ℕ, (∀ m, 0 < m → 0 < g m) ∧
      (∀ n m, 0 < n → 0 < m → g m ≤ occupancy n m) := by
  rintro ⟨g, hpos, hbound⟩
  have hm : (0 : ℕ) < 1 := Nat.one_pos
  have hn : 0 < allOnesStart 1 := by norm_num [allOnesStart]
  have hb := hbound (allOnesStart 1) 1 hn hm
  rw [occupancy_allOnes 1] at hb
  have hp := hpos 1 hm
  omega

/-- The same statement in the form the queue records it, with the witness
exhibited rather than the bound refuted: arbitrarily long zero-occupancy
subcritical prefixes exist. -/
theorem arbitrarily_long_zero_occupancy (m : ℕ) :
    ∃ n : ℕ, 0 < n ∧ occupancy n m = 0 ∧
      (∀ j, 0 < j → j ≤ m → 2 ^ K n j < 3 ^ j) := by
  refine ⟨allOnesStart m, ?_, occupancy_allOnes m, subcritical_allOnes m⟩
  unfold allOnesStart
  have : 2 ≤ 2 ^ (m + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end Collatz
