/-
# Hard-Zeta — why the invariant-measure route has to be conditional

數學戰士「墜衡」 / AMRAL Research Lab.

Queue item 6, second half. The series' `AUDIT_AND_CORRECTIONS.md` records:

> **Hard-Zeta — invariant-measure route qualification.** The phrase that a
> subsequential empirical limit *must* produce an invariant/quasi-invariant
> object was too strong without a specified state space and limit-passage
> assumptions. The route is now explicitly conditional on an appropriate
> compactification/state space, tightness, and the regularity needed to pass
> dynamics to a weak limit.

The queue's note on this item was that **formalising the hypotheses is the value
here, not the conclusion** — and the sharpest way to formalise a hypothesis is to
show what breaks without it. That is what this file does, in the same shape as
`no_uniform_depth` did for §52: the caution becomes a theorem.

## What is proved

Without a hypothesis that keeps mass from escaping, the failure is not the mild
one. It is not that the empirical measures might converge to something that
happens not to be invariant. It is that on such a state space **there is no
invariant probability measure at all**, so there is nothing for them to converge
to.

`succ_no_invariant_prob` is that, for the canonical mass-escaping system: the
successor map on `ℕ`. Every singleton is forced to measure zero by invariance
alone, and a countable space whose atoms all vanish has total measure zero, not
one.

## What is not proved

This is not Krylov–Bogolyubov, and it is not a claim about the Collatz dynamics.
mathlib at this pin has no Krylov–Bogolyubov, so the positive direction is not
cited here either; the point is only that the qualification the corrections file
added is load-bearing rather than pedantic.

Nor is weak convergence itself formalised. It does not need to be: if no
invariant probability measure exists, then no limit of any kind can be one, and
that is the whole content of the objection.
-/

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

namespace Collatz.InvariantLimit

open MeasureTheory

/-! ## The canonical mass-escaping system -/

/-- The successor map on `ℕ`: the simplest dynamical system in which every orbit
leaves every finite set and never returns. -/
def succ (n : ℕ) : ℕ := n + 1

lemma measurable_succ : Measurable succ := measurable_from_top

@[simp] lemma preimage_succ_zero : succ ⁻¹' {0} = (∅ : Set ℕ) := by
  ext n; simp [succ]

@[simp] lemma preimage_succ_succ (k : ℕ) : succ ⁻¹' {k + 1} = {k} := by
  ext n; simp [succ]

/-! ## Invariance alone kills every atom -/

/-- If `μ` is invariant under the successor map then every singleton has measure
zero. Note there is no finiteness hypothesis here — this is forced by invariance
by itself, walking down from `0`, where the preimage is empty. -/
theorem singleton_eq_zero {μ : Measure ℕ} (hinv : μ.map succ = μ) :
    ∀ k, μ {k} = 0 := by
  intro k
  induction k with
  | zero =>
      have h : μ {0} = μ (succ ⁻¹' {0}) := by
        conv_lhs => rw [← hinv]
        rw [Measure.map_apply measurable_succ (measurableSet_singleton 0)]
      simpa using h
  | succ k ih =>
      have h : μ {k + 1} = μ (succ ⁻¹' {k + 1}) := by
        conv_lhs => rw [← hinv]
        rw [Measure.map_apply measurable_succ (measurableSet_singleton (k + 1))]
      rw [h, preimage_succ_succ]
      exact ih

/-! ## Hence no invariant probability measure exists -/

/-- **The qualification is load-bearing.** The successor map on `ℕ` has **no**
invariant probability measure.

So on a state space where mass can escape, the claim that a subsequential
empirical limit *must* be invariant cannot hold: there is no invariant
probability measure for it to be. The compactification / tightness hypothesis is
what rules this out, which is exactly why the corrections file added it. -/
theorem succ_no_invariant_prob :
    ¬ ∃ μ : Measure ℕ, IsProbabilityMeasure μ ∧ μ.map succ = μ := by
  rintro ⟨μ, hprob, hinv⟩
  have hatoms : ∀ k, μ {k} = 0 := singleton_eq_zero hinv
  have hcover : (Set.univ : Set ℕ) = ⋃ k : ℕ, ({k} : Set ℕ) := by
    ext n; simp
  have hdisj : Pairwise (Function.onFun Disjoint fun k : ℕ => ({k} : Set ℕ)) := by
    intro i j hij
    simp only [Function.onFun, Set.disjoint_singleton]
    exact hij
  have huniv : μ (Set.univ : Set ℕ) = 0 := by
    rw [hcover, measure_iUnion hdisj (fun k => measurableSet_singleton k)]
    simp [hatoms]
  rw [hprob.measure_univ] at huniv
  exact one_ne_zero huniv

/-- The same statement in the form the correction is about: "an invariant
probability measure exists" is **not** a theorem of measurable dynamics. It is a
hypothesis, and `ℕ` with the successor map is a system where it is false. -/
theorem invariant_prob_existence_is_a_hypothesis :
    ¬ ∀ (f : ℕ → ℕ), Measurable f →
        ∃ μ : Measure ℕ, IsProbabilityMeasure μ ∧ μ.map f = μ := by
  intro h
  exact succ_no_invariant_prob (h succ measurable_succ)

/-! ## The failure is specifically the normalisation

Dropping the probability normalisation, invariant measures do exist for shifts —
counting measure on `ℤ` is the standard example. So the hypothesis the route
needs is not "some invariant object exists" in the loosest sense; it is the one
that keeps a *probability* measure from leaking away, which is what tightness
does. The `ℕ` case above is stronger than that, because there even the unnormalised
walk-down forces every atom to zero. -/

/-- On `ℕ` the failure is not a normalisation artefact: invariance forces every
atom to zero, so **any** invariant measure is zero on every finite set. -/
theorem invariant_vanishes_on_finite {μ : Measure ℕ} (hinv : μ.map succ = μ)
    (s : Finset ℕ) : μ (s : Set ℕ) = 0 := by
  classical
  have : (s : Set ℕ) = ⋃ k ∈ s, ({k} : Set ℕ) := by
    ext n; simp
  rw [this]
  refine measure_biUnion_null_iff s.countable_toSet |>.mpr ?_
  intro k _
  exact singleton_eq_zero hinv k

end Collatz.InvariantLimit
