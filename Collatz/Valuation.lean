/-
# Paper 06 — the valuation language, and its exact correspondence with Paper 02

數學戰士「墜衡」 / AMRAL Research Lab.

Queue item 4. Paper 06 changes coordinates: instead of a parity word over
`{D,U}`, an odd-to-odd orbit is described by its **valuation word**
`κ = (κ₁,…,κ_m)` with `κ_i = v₂(3n_{i−1}+1)`, and the accelerated map
`S(n) = (3n+1)/2^{κ(n)}` moves between consecutive odd states.

§14 claims a complete correspondence with Paper 02. As with Paper 07's §6, that
is a claim about a previous development and so it is proved here rather than
remarked: `bCorr_expand` shows the accelerated correction `B_κ` **is** Paper 02's
parity correction of the run-length expansion, and `orbit_eq_iterate` shows the
accelerated orbit **is** the modified orbit re-indexed. Theorem B then follows
from Paper 02's Theorem A rather than needing its own induction.

## Recursion direction, for the third time

`B_j = 3B_{j−1} + 2^{K_{j−1}}` appends on the right. Rewritten for the recursion
`List` actually has,

    B [] = 0,   B (κ :: rest) = 3 ^ rest.length + 2 ^ κ * B rest,

which is exactly the shape `bCorr` has on the expanded parity word — which is why
the correspondence is a one-line induction rather than a fight with
`List.reverse`.
-/

import Mathlib.Tactic
import Collatz.AffineAtlas
import Collatz.AllOnes
import Collatz.ResidueCylinder

namespace Collatz.Valuation

open Collatz.Atlas (Letter uCount bCorr)
open Collatz.Atlas.Letter

/-! ## §5: the run-length expansion -/

/-- §5: `E(κ) = U D^{κ−1}` for one symbol, concatenated over the word. -/
def expand : List ℕ → List Letter
  | [] => []
  | (j :: rest) => (U :: List.replicate (j - 1) D) ++ expand rest

/-- §7's cumulative valuation `K_j`, and `K = K_m` as the word's sum. -/
def Kcum (κ : List ℕ) : ℕ := κ.sum

/-- §10–§11: the accelerated correction, by the recursion `List` recurses on.

The paper's `B_j = 3B_{j−1} + 2^{K_{j−1}}` appends on the right; this prepends.
`Bcorr_append_right` below shows they agree. -/
def Bcorr : List ℕ → ℕ
  | [] => 0
  | (j :: rest) => 3 ^ rest.length + 2 ^ j * Bcorr rest

@[simp] lemma expand_nil : expand [] = [] := rfl
@[simp] lemma Bcorr_nil : Bcorr [] = 0 := rfl
@[simp] lemma Bcorr_cons (j : ℕ) (rest : List ℕ) :
    Bcorr (j :: rest) = 3 ^ rest.length + 2 ^ j * Bcorr rest := rfl

/-! ## Theorem A — the run-length encoding -/

/-- **Theorem A, first half.** `|E(κ)| = K`, provided every symbol is at least 1.
Without that hypothesis `κ_i = 0` would contribute a `U` and no `D`, and the
length would exceed the sum — so the hypothesis is load-bearing, not decorative. -/
theorem length_expand {κ : List ℕ} (h : ∀ j ∈ κ, 1 ≤ j) :
    (expand κ).length = Kcum κ := by
  induction κ with
  | nil => simp [Kcum]
  | cons j rest ih =>
      have hj : 1 ≤ j := h j (List.mem_cons_self ..)
      have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hih : (expand rest).length = rest.sum := by
        simpa [Kcum] using ih hrest
      simp only [expand, List.length_append, List.length_cons,
        List.length_replicate, hih, Kcum, List.sum_cons]
      omega

/-- **Theorem A, second half.** `u(E(κ)) = m`: one `U` per valuation symbol. -/
@[simp] theorem uCount_expand (κ : List ℕ) : uCount (expand κ) = κ.length := by
  induction κ with
  | nil => simp
  | cons j rest ih =>
      have hrep : uCount (List.replicate (j - 1) D) = 0 := by
        induction (j - 1) with
        | zero => simp
        | succ n ihn => simp [List.replicate_succ, ihn]
      simp only [expand, List.cons_append, Collatz.Atlas.uCount_cons_U,
        Collatz.Atlas.uCount_append, hrep, ih, List.length_cons]
      omega

/-! ## Theorem C — and the correspondence with Paper 02 -/

/-- Leading `D`s simply double the correction. -/
lemma bCorr_replicate_D_append (n : ℕ) (v : List Letter) :
    bCorr (List.replicate n D ++ v) = 2 ^ n * bCorr v := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, pow_succ]; ring

/-- **Theorem C, and §14's correspondence.** The accelerated correction `B_κ`
**is** Paper 02's parity correction of the run-length expansion.

The two are defined independently — `Bcorr` from Paper 06's recurrence, `bCorr`
from Paper 02's — so this is a theorem about the change of coordinates, not a
restatement of it. -/
theorem bCorr_expand {κ : List ℕ} (h : ∀ j ∈ κ, 1 ≤ j) :
    bCorr (expand κ) = Bcorr κ := by
  induction κ with
  | nil => simp
  | cons j rest ih =>
      have hj : 1 ≤ j := h j (List.mem_cons_self ..)
      have hrest : ∀ x ∈ rest, 1 ≤ x := fun x hx => h x (List.mem_cons_of_mem _ hx)
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hrep : uCount (List.replicate i D) = 0 := by
        induction i with
        | zero => simp
        | succ n ihn => simp [List.replicate_succ, ihn]
      rw [expand, List.cons_append, Collatz.Atlas.bCorr_cons_U,
        Collatz.Atlas.uCount_append, bCorr_replicate_D_append, ih hrest]
      simp only [Nat.add_sub_cancel, hrep, uCount_expand, Bcorr_cons, pow_succ]
      ring

/-- The paper's right-append recurrence `B_j = 3 B_{j−1} + 2^{K_{j−1}}`, proved
from the cons definition. -/
theorem Bcorr_append_right (κ : List ℕ) (j : ℕ) :
    Bcorr (κ ++ [j]) = 3 * Bcorr κ + 2 ^ Kcum κ := by
  induction κ with
  | nil => simp [Kcum]
  | cons a t ih =>
      simp only [List.cons_append, Bcorr_cons, List.length_append,
        List.length_cons, List.length_nil, ih, Kcum, List.sum_cons, pow_add]
      ring

/-! ## §6: the run-length correspondence between the two orbits -/

open Collatz.Cylinder (T)

/-- Halving `i` times undoes `2^i`. This is the `D^{κ−1}` tail of one
accelerated step, with no valuation reasoning in it at all. -/
lemma iterate_T_pow_mul (c : ℕ) (hc : 0 < c) :
    ∀ i, T^[i] (2 ^ i * c) = c := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      have hstep : 2 ^ (i + 1) * c = 2 * (2 ^ i * c) := by ring
      rw [Function.iterate_succ_apply, hstep]
      have heven : (2 * (2 ^ i * c)) % 2 = 0 := by omega
      rw [Collatz.Cylinder.T_even heven,
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      exact ih

/-- **§6, the run-length correspondence.** One accelerated step is exactly
`κ(x)` modified steps: a `U`, then `κ(x) − 1` `D`s. -/
theorem iterate_kappa (x : ℕ) (hx : x % 2 = 1) :
    T^[Collatz.kappa x] x = Collatz.S x := by
  have hne0 : 3 * x + 1 ≠ 0 := by omega
  have hne1 : 3 * x + 1 ≠ 1 := by omega
  have hdvd2 : 2 ∣ (3 * x + 1) := by omega
  -- `v₂(3x+1) ≥ 1`, because `3x+1` is even and neither 0 nor 1
  have hk1 : 1 ≤ Collatz.kappa x := by
    obtain ⟨q, hq⟩ := hdvd2
    have hq0 : q ≠ 0 := by omega
    show 1 ≤ padicValNat 2 (3 * x + 1)
    rw [hq, padicValNat.mul (by norm_num) hq0, padicValNat.self (by norm_num)]
    omega
  -- `3x + 1 = 2^κ · S x`
  have hdvd : 2 ^ Collatz.kappa x ∣ 3 * x + 1 := pow_padicValNat_dvd
  have hfac : 3 * x + 1 = 2 ^ Collatz.kappa x * Collatz.S x := by
    unfold Collatz.S
    exact (Nat.mul_div_cancel' hdvd).symm
  have hSpos : 0 < Collatz.S x := by
    rcases Nat.eq_zero_or_pos (Collatz.S x) with hz | hp
    · rw [hz, Nat.mul_zero] at hfac; omega
    · exact hp
  -- one `U`, then `κ − 1` halvings
  obtain ⟨k, hk⟩ : ∃ k, Collatz.kappa x = k + 1 := ⟨Collatz.kappa x - 1, by omega⟩
  rw [hk, Function.iterate_succ_apply, Collatz.Cylinder.T_odd hx]
  have hhalf : (3 * x + 1) / 2 = 2 ^ k * Collatz.S x := by
    rw [hfac, hk, pow_succ,
      show 2 ^ k * 2 * Collatz.S x = 2 * (2 ^ k * Collatz.S x) from by ring,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  rw [hhalf, iterate_T_pow_mul _ hSpos]

/-! ## Theorem B — accelerated affine closure, from Paper 02 -/

/-- **Theorem E (§17).** The valuation contraction boundary, in integers:
`2^K > 3^m` is the exact form of `K/m > log₂ 3`. No real numbers needed. -/
theorem contraction_boundary (m K : ℕ) :
    2 ^ K > 3 ^ m ↔ ¬ (2 ^ K ≤ 3 ^ m) := by
  omega

/-- The accelerated map preserves oddness: every factor of 2 has been removed,
so what is left cannot be even. Uses the **maximality** of `v₂`, which is the
only place in this file that needs more than divisibility. -/
lemma S_odd {x : ℕ} (hx : x % 2 = 1) : Collatz.S x % 2 = 1 := by
  have hne : 3 * x + 1 ≠ 0 := by omega
  have hdvd : 2 ^ Collatz.kappa x ∣ 3 * x + 1 := pow_padicValNat_dvd
  have hfac : 3 * x + 1 = 2 ^ Collatz.kappa x * Collatz.S x := by
    unfold Collatz.S
    exact (Nat.mul_div_cancel' hdvd).symm
  by_contra hev
  have h2 : 2 ∣ Collatz.S x := by omega
  obtain ⟨e, he⟩ := h2
  have hbig : 2 ^ (Collatz.kappa x + 1) ∣ 3 * x + 1 := ⟨e, by rw [hfac, he, pow_succ]; ring⟩
  exact pow_succ_padicValNat_not_dvd hne hbig

/-- Hence the whole accelerated orbit of an odd start is odd. -/
lemma orbit_odd {n : ℕ} (hn : n % 2 = 1) : ∀ i, Collatz.orbit n i % 2 = 1 := by
  intro i
  induction i with
  | zero => simpa [Collatz.orbit] using hn
  | succ i ih => rw [Collatz.orbit]; exact S_odd ih

/-- §3: the valuation word of the first `m` accelerated steps. -/
def valWord (n m : ℕ) : List ℕ :=
  (List.range m).map (fun i => Collatz.kappa (Collatz.orbit n i))

@[simp] lemma valWord_zero (n : ℕ) : valWord n 0 = [] := by simp [valWord]

lemma valWord_succ (n m : ℕ) :
    valWord n (m + 1) = valWord n m ++ [Collatz.kappa (Collatz.orbit n m)] := by
  simp [valWord, List.range_succ]

/-- Every valuation symbol is at least 1, which is what `length_expand` and
`bCorr_expand` need — and it is a fact about the map, not an assumption. -/
lemma one_le_valWord {n : ℕ} (hn : n % 2 = 1) : ∀ j ∈ valWord n m, 1 ≤ j := by
  intro j hj
  simp only [valWord, List.mem_map, List.mem_range] at hj
  obtain ⟨i, _, rfl⟩ := hj
  have hodd : Collatz.orbit n i % 2 = 1 := orbit_odd hn i
  obtain ⟨q, hq⟩ : 2 ∣ (3 * Collatz.orbit n i + 1) := by omega
  have hq0 : q ≠ 0 := by omega
  change 1 ≤ padicValNat 2 (3 * Collatz.orbit n i + 1)
  rw [hq, padicValNat.mul (by norm_num) hq0, padicValNat.self (by norm_num)]
  omega

/-- **§6, in full.** `m` accelerated steps are exactly `K = Σκ` modified steps.
This is the re-indexing that makes Paper 06 and Paper 02 the same object seen in
two coordinate systems. -/
theorem orbit_eq_iterate {n : ℕ} (hn : n % 2 = 1) :
    ∀ m, Collatz.orbit n m = T^[Kcum (valWord n m)] n := by
  intro m
  induction m with
  | zero => simp [Collatz.orbit, Kcum]
  | succ m ih =>
      rw [Collatz.orbit, valWord_succ, Kcum, List.sum_append, List.sum_cons,
        List.sum_nil, Nat.add_zero, ← Kcum, Nat.add_comm,
        Function.iterate_add_apply, ← ih, iterate_kappa _ (orbit_odd hn m)]

/-- **Theorem B (§10), accelerated affine closure.** `S^m(n) = (3^m n + B_κ)/2^K`.

Proved by Paper 06's own induction (§11) rather than through Paper 02, so that
`bCorr_expand` above stays an independent statement about the change of
coordinates rather than a step in this proof. -/
theorem accelerated_affine_closure {n : ℕ} (hn : n % 2 = 1) :
    ∀ m, (2 : ℤ) ^ Kcum (valWord n m) * (Collatz.orbit n m : ℤ)
      = 3 ^ m * (n : ℤ) + Bcorr (valWord n m) := by
  intro m
  induction m with
  | zero => simp [Collatz.orbit, Kcum]
  | succ m ih =>
      have hodd : Collatz.orbit n m % 2 = 1 := orbit_odd hn m
      set x := Collatz.orbit n m with hx
      set j := Collatz.kappa x with hj
      -- one accelerated step, as an integer identity
      have hdvd : 2 ^ j ∣ 3 * x + 1 := pow_padicValNat_dvd
      have hstep : (2 : ℤ) ^ j * (Collatz.S x : ℤ) = 3 * (x : ℤ) + 1 := by
        have : (2 : ℕ) ^ j * Collatz.S x = 3 * x + 1 := by
          unfold Collatz.S
          exact Nat.mul_div_cancel' hdvd
        exact_mod_cast congrArg (fun y : ℕ => (y : ℤ)) this
      rw [Collatz.orbit, valWord_succ, Kcum, List.sum_append, List.sum_cons,
        List.sum_nil, Nat.add_zero, ← Kcum, pow_add]
      rw [Bcorr_append_right, ← hx, ← hj]
      have h2 : ((2 : ℤ) ^ Kcum (valWord n m)) * (2 ^ j * (Collatz.S x : ℤ))
          = 2 ^ Kcum (valWord n m) * (3 * (x : ℤ) + 1) := by rw [hstep]
      have hexp : (2 : ℤ) ^ Kcum (valWord n m) * 2 ^ j * (Collatz.S x : ℤ)
          = 2 ^ Kcum (valWord n m) * (3 * (x : ℤ) + 1) := by
        rw [mul_assoc]; exact h2
      rw [hexp]
      push_cast
      linear_combination 3 * ih

/-! ## Theorem F — the one-step valuation density -/

/-- **§21.** `v₂(3n+1) = j` pins `n` to a single residue mod `2^{j+1}`: the
condition is `3n ≡ 2^j − 1`, and `3` is a unit there. -/
theorem one_step_residue_unique (j : ℕ) {n n' : ℕ}
    (hn : (3 * n + 1) % 2 ^ (j + 1) = 2 ^ j % 2 ^ (j + 1))
    (hn' : (3 * n' + 1) % 2 ^ (j + 1) = 2 ^ j % 2 ^ (j + 1)) :
    n ≡ n' [MOD 2 ^ (j + 1)] := by
  have h3 : 3 * n + 1 ≡ 3 * n' + 1 [MOD 2 ^ (j + 1)] := by
    unfold Nat.ModEq
    rw [hn, hn']
  have h4 : 3 * n ≡ 3 * n' [MOD 2 ^ (j + 1)] :=
    Nat.ModEq.add_right_cancel' 1 h3
  have hcop : Nat.gcd (2 ^ (j + 1)) 3 = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left _ (by norm_num))
  exact Nat.ModEq.cancel_left_of_coprime hcop h4

/-- **§22's counting half.** Among the `2^{j+1}` residues mod `2^{j+1}`,
exactly `2^j` are odd — the denominator of the density. -/
theorem odd_residue_count (j : ℕ) :
    ((Finset.range (2 ^ (j + 1))).filter (fun n => n % 2 = 1)).card = 2 ^ j := by
  have hbij : ((Finset.range (2 ^ (j + 1))).filter (fun n => n % 2 = 1))
      = (Finset.range (2 ^ j)).image (fun i => 2 * i + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hlt, hodd⟩
      refine ⟨n / 2, ?_, by omega⟩
      have : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
      omega
    · rintro ⟨i, hi, rfl⟩
      have : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
      exact ⟨by omega, by omega⟩
  rw [hbij, Finset.card_image_of_injective _ (fun a b hab => by omega),
    Finset.card_range]

end Collatz.Valuation