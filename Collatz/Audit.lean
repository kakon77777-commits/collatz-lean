import Collatz.AllOnes
import Collatz.AffineAtlas
import Collatz.Generalized
import Collatz.ResidueCylinder
import Collatz.Valuation
import Collatz.StoppingTime
import Collatz.HardSet
import Collatz.InvariantLimit
import Collatz.AnchoredBranch

/-! Axiom audit and concrete evaluation. Nothing here is a theorem; it exists so
the claims can be inspected rather than trusted. -/

namespace Collatz

#print axioms v₂_eq_zero_of_odd
#print axioms v₂_two_mul_odd
#print axioms orbit_allOnes
#print axioms kappa_allOnes
#print axioms K_allOnes
#print axioms subcritical_allOnes
#print axioms occupancy_allOnes
#print axioms finite_local_no_go
#print axioms arbitrarily_long_zero_occupancy

-- the witness and its first exponents, for cross-checking against the finite arm
#eval (List.range 6).map allOnesStart
#eval (List.range 12).map (fun i => kappa (orbit (allOnesStart 11) i))
#eval (List.range 12).map (fun i => orbit (allOnesStart 11) i)
#eval (List.range 8).map (fun m => occupancy (allOnesStart m) m)
-- occupancy is NOT identically zero: an unrelated start must make it positive,
-- or the no-go would be about a quantity that cannot be positive
#eval (List.range 10).map (fun i => kappa (orbit 27 i))
#eval occupancy 27 10

end Collatz

#print axioms Collatz.kappa_at_m_ge_two
#eval (List.range 6).map (fun m => Collatz.kappa (Collatz.orbit (Collatz.allOnesStart m) m))

/-! ### Paper 02 — the affine atlas -/

open Collatz.Atlas in
section AtlasAudit

#print axioms Collatz.Atlas.affine_closure
#print axioms Collatz.Atlas.bCorr_append
#print axioms Collatz.Atlas.bCorr_append_D
#print axioms Collatz.Atlas.bCorr_append_U
#print axioms Collatz.Atlas.order_defect
#print axioms Collatz.Atlas.bCorr_closed_form
#print axioms Collatz.Atlas.M_append
#print axioms Collatz.Atlas.M_D
#print axioms Collatz.Atlas.M_U
#print axioms Collatz.Atlas.bCorr_lower
#print axioms Collatz.Atlas.bCorr_upper
#print axioms Collatz.Atlas.bCorr_replicate_U
#print axioms Collatz.Atlas.extremes_attained
#print axioms Collatz.Atlas.uCount_le_length
#print axioms Collatz.Atlas.uCount_append
#print axioms Collatz.Atlas.length_allWords

-- Non-vacuity. "Counts determine slope, order determines offset" is only a
-- statement if b actually VARIES across words with the same (k, u).
#eval Collatz.Atlas.bCorr [Collatz.Atlas.Letter.U, Collatz.Atlas.Letter.D]
#eval Collatz.Atlas.bCorr [Collatz.Atlas.Letter.D, Collatz.Atlas.Letter.U]
-- how many DISTINCT corrections occur among the 2^10 words of length 10
#eval ((Collatz.Atlas.allWords 10).map Collatz.Atlas.bCorr).eraseDups.length
-- and Theorem F's bounds must not coincide, or "extremes" is one point
#eval (Collatz.Atlas.bCorr (Collatz.Atlas.wMin 6 3), Collatz.Atlas.bCorr (Collatz.Atlas.wMax 6 3))

end AtlasAudit

/-! ### Paper 07 — the generalised mx+r atlas -/

section GeneralizedAudit

#print axioms Collatz.Generalized.odd_branch_integral
#print axioms Collatz.Generalized.odd_branch_needs_odd_m
#print axioms Collatz.Generalized.affine_closure_G
#print axioms Collatz.Generalized.bG_append
#print axioms Collatz.Generalized.bG_append_D
#print axioms Collatz.Generalized.bG_append_U
#print axioms Collatz.Generalized.bG_factor_r
#print axioms Collatz.Generalized.bG_one_closed_form
#print axioms Collatz.Generalized.bG_closed_form
#print axioms Collatz.Generalized.bG_three_one
#print axioms Collatz.Generalized.FG_three_one
#print axioms Collatz.Generalized.odd_pow_ne_two_pow
#print axioms Collatz.Generalized.alpha_irrational

-- Non-vacuity. `bG_three_one` says the m=3, r=1 case IS Paper 02; that is only
-- a statement if other parameters give something else.
#eval ((Collatz.Atlas.allWords 4).map (Collatz.Generalized.bG 3 1)).eraseDups.length
#eval ((Collatz.Atlas.allWords 4).map (Collatz.Generalized.bG 5 1)).eraseDups.length
#eval ((Collatz.Atlas.allWords 4).map (fun w =>
  Collatz.Generalized.bG 3 1 w == Collatz.Generalized.bG 5 1 w)).count false
-- and r really does just scale
#eval ((Collatz.Atlas.allWords 4).map (fun w =>
  Collatz.Generalized.bG 3 7 w == 7 * Collatz.Generalized.bG 3 1 w)).count false
-- §25 is not about wildly separated magnitudes: 3^12 and 2^19 are within 1.4%
#eval (3 ^ 12, 2 ^ 19)

end GeneralizedAudit

/-! ### Paper 03 — residue cylinders and the r_w = 0 boundary -/

section CylinderAudit

#print axioms Collatz.Cylinder.T_even
#print axioms Collatz.Cylinder.T_odd
#print axioms Collatz.Cylinder.length_parityWord
#print axioms Collatz.Cylinder.parityWord_add_odd_mul
#print axioms Collatz.Cylinder.parityWord_add_pow
#print axioms Collatz.Cylinder.parityWord_add_mul
#print axioms Collatz.Cylinder.parityWord_of_modEq
#print axioms Collatz.Cylinder.modEq_of_parityWord
#print axioms Collatz.Cylinder.parityWord_eq_iff_modEq
#print axioms Collatz.Cylinder.residues_injective
#print axioms Collatz.Cylinder.residues_surjective
#print axioms Collatz.Cylinder.allD_residue_zero
#print axioms Collatz.Cylinder.cylinder_has_positive_member
#print axioms Collatz.Cylinder.positive_representative
#print axioms Collatz.Cylinder.allD_positive_witness
#print axioms Collatz.Cylinder.step_cast
#print axioms Collatz.Cylinder.iterate_eq_F
#print axioms Collatz.Cylinder.cylinder_congruence
#print axioms Collatz.Cylinder.three_pow_coprime
#print axioms Collatz.Cylinder.phi_cyl
#print axioms Collatz.Cylinder.psi_prog
#print axioms Collatz.Cylinder.transport
#print axioms Collatz.Cylinder.local_identity
#print axioms Collatz.Cylinder.exact_recovery
#print axioms Collatz.Cylinder.cyl_injective
#print axioms Collatz.Cylinder.prog_injective
#print axioms Collatz.Cylinder.iterate_numerator
#print axioms Collatz.Cylinder.local_identity_dynamical

-- Non-vacuity. The bijection is only a statement if the 2^k residues really do
-- give 2^k DIFFERENT words.
#eval ((List.range 32).map (fun n => Collatz.Cylinder.parityWord n 5)).eraseDups.length
-- the r_w = 0 boundary, concretely: the all-D cylinder at k = 5
#eval (Collatz.Cylinder.parityWord 0 5, Collatz.Cylinder.parityWord 32 5)
-- and words genuinely vary with n, so parityWord is not a constant function
#eval ((List.range 8).map (fun n => Collatz.Cylinder.parityWord n 3))

end CylinderAudit

-- Non-vacuity for the charts: the trivialization is only interesting if F_w is
-- NOT already the identity. `cyl` and `prog` must genuinely move points.
#eval ((List.range 6).map (fun a => Collatz.Cylinder.cyl 3 4 (a : Int)))
#eval ((List.range 6).map (fun a => Collatz.Cylinder.prog 5 3 (a : Int)))
-- 27's own transport data at depth 10: word, T^10(27), and the numerator identity
#eval (Collatz.Cylinder.T^[10] 27,
       Collatz.Atlas.uCount (Collatz.Cylinder.parityWord 27 10),
       Collatz.Atlas.bCorr (Collatz.Cylinder.parityWord 27 10))

/-! ### Paper 06 — the valuation language -/

section ValuationAudit

#print axioms Collatz.Valuation.length_expand
#print axioms Collatz.Valuation.bCorr_replicate_D_append
#print axioms Collatz.Valuation.bCorr_expand
#print axioms Collatz.Valuation.Bcorr_append_right
#print axioms Collatz.Valuation.iterate_T_pow_mul
#print axioms Collatz.Valuation.iterate_kappa
#print axioms Collatz.Valuation.contraction_boundary
#print axioms Collatz.Valuation.S_odd
#print axioms Collatz.Valuation.orbit_odd
#print axioms Collatz.Valuation.valWord_succ
#print axioms Collatz.Valuation.one_le_valWord
#print axioms Collatz.Valuation.orbit_eq_iterate
#print axioms Collatz.Valuation.accelerated_affine_closure
#print axioms Collatz.Valuation.one_step_residue_unique
#print axioms Collatz.Valuation.odd_residue_count

-- Non-vacuity. The run-length expansion must actually expand: a valuation word
-- of length 3 with a 4 in it becomes a parity word of length 7.
#eval (Collatz.Valuation.expand [2, 1, 4], Collatz.Valuation.Kcum [2, 1, 4])
#eval (Collatz.Valuation.Bcorr [2, 1, 4],
       Collatz.Atlas.bCorr (Collatz.Valuation.expand [2, 1, 4]))
-- 27's own valuation word, and that m accelerated steps = K modified steps
#eval (Collatz.Valuation.valWord 27 8, Collatz.Valuation.Kcum (Collatz.Valuation.valWord 27 8))
#eval (Collatz.orbit 27 8,
       Collatz.Cylinder.T^[Collatz.Valuation.Kcum (Collatz.Valuation.valWord 27 8)] 27)
-- and the valuation is NOT constant, or the density theorem would be trivial
#eval ((List.range 12).map (fun i => Collatz.kappa (2 * i + 1))).eraseDups

end ValuationAudit

/-! ### Paper 09 — the stopping-time equivalence -/

section StoppingAudit

#print axioms Collatz.Stopping.T_pos
#print axioms Collatz.Stopping.iterate_pos
#print axioms Collatz.Stopping.sigma_spec
#print axioms Collatz.Stopping.reaches_one_of_finite_stopping
#print axioms Collatz.Stopping.finite_stopping_of_reaches_one
#print axioms Collatz.Stopping.collatz_iff_finite_stopping
#print axioms Collatz.Stopping.reaches_one_of_bounded_stopping
#print axioms Collatz.Stopping.allOnes_iterate
#print axioms Collatz.Stopping.no_uniform_depth

-- Non-vacuity. The equivalence is only interesting if descents actually happen,
-- and `no_uniform_depth` only if the witness really fails to descend.
#eval ((List.range 8).map (fun i =>
  let n := 2 * i + 3
  (n, (List.range 12).find? (fun j => 1 <= j && Collatz.Cylinder.T^[j] n < n))))
-- the all-ones witness at k = 6: it has GROWN after 6 steps
#eval (Collatz.allOnesStart 6, Collatz.Cylinder.T^[6] (Collatz.allOnesStart 6))
-- and 1 sits on the modified map's 2-cycle, which is why Reaches1 1 is trivial
#eval ((List.range 4).map (fun j => Collatz.Cylinder.T^[j] 1))

end StoppingAudit

/-! ### Hard-Zeta — the n >= 2 stopping domain -/

section HardAudit

#print axioms Collatz.HardSet.hard_mono
#print axioms Collatz.HardSet.hard_iff
#print axioms Collatz.HardSet.iterate_one_mem
#print axioms Collatz.HardSet.one_is_permanently_undescended
#print axioms Collatz.HardSet.one_not_hard
#print axioms Collatz.HardSet.zero_not_hard
#print axioms Collatz.HardSet.mem_hardIn
#print axioms Collatz.HardSet.hardIn_disjoint
#print axioms Collatz.HardSet.hard_eq_iUnion
#print axioms Collatz.HardSet.one_not_mem_hardIn
#print axioms Collatz.HardSet.descent_iff_quotient
#print axioms Collatz.HardSet.quotient_slope_sign

-- Non-vacuity. The hard set must be neither empty nor everything, or the
-- partition would be a statement about nothing.
#eval ((List.range 40).filter (fun n => decide (Collatz.HardSet.Hard 3 n))).length
#eval ((List.range 40).filter (fun n => decide (Collatz.HardSet.Hard 8 n)))
-- and it must actually shrink with depth
#eval ((List.range 200).map (fun k =>
  ((List.range 200).filter (fun n => decide (Collatz.HardSet.Hard k n))).length)).take 8
-- 1 never descends, which is the whole reason the domain starts at 2
#eval ((List.range 6).map (fun j => Collatz.Cylinder.T^[j] 1))

end HardAudit

/-! ### Hard-Zeta — the invariant-measure qualification -/

section InvariantAudit

#print axioms Collatz.InvariantLimit.measurable_succ
#print axioms Collatz.InvariantLimit.singleton_eq_zero
#print axioms Collatz.InvariantLimit.succ_no_invariant_prob
#print axioms Collatz.InvariantLimit.invariant_prob_existence_is_a_hypothesis
#print axioms Collatz.InvariantLimit.invariant_vanishes_on_finite

-- Non-vacuity: the successor map really does leave every finite set, which is
-- why no probability mass can be invariant under it.
#eval ((List.range 6).map (fun i => Nat.rec 7 (fun _ x => Collatz.InvariantLimit.succ x) i))

end InvariantAudit

/-! ### Paper 09 Theorem F — nested residues and the anchored branch -/

section AnchoredAudit

#print axioms Collatz.Anchored.nested_residue
#print axioms Collatz.Anchored.residue_stabilises
#print axioms Collatz.Anchored.nested_allOnes
#print axioms Collatz.Anchored.nested_not_always_anchored
#print axioms Collatz.Anchored.anchored_strictly_stronger
#print axioms Collatz.Anchored.noFinite_iff_not_hasFinite
#print axioms Collatz.Anchored.no_stopping_iff_hard_forever
#print axioms Collatz.Anchored.hard_forever_iff_anchored_hard
#print axioms Collatz.Anchored.collatz_iff_no_anchored_hard_branch
#print axioms Collatz.Anchored.hard_at_each_depth_is_nonempty

-- Non-vacuity 1: the residue tower of a fixed `n` must genuinely MOVE before it
-- stabilises, or `Anchored` would be trivially true of every tower and §43's
-- separation would be empty.
#eval (List.range 8).map (fun k => Collatz.Anchored.residue 27 k)

-- Non-vacuity 2: the all-ones tower must be genuinely unbounded, or the
-- counterexample to "nested implies anchored" would not be one.
#eval (List.range 10).map Collatz.Anchored.allOnesResidue

-- Non-vacuity 3: the two towers must AGREE on the nesting condition and DISAGREE
-- on anchoring — that is the whole content of `anchored_strictly_stronger`.
-- `residue 27` is eventually constant at 27; `allOnesResidue` never repeats.
#eval ((List.range 12).map (fun k => Collatz.Anchored.residue 27 k)).dedup.length
#eval ((List.range 12).map Collatz.Anchored.allOnesResidue).dedup.length

-- Non-vacuity 4: the depth-k witness must actually be hard at depth k, and it
-- must NOT be the same number for every k (a constant witness would make
-- `hard_at_each_depth_is_nonempty` a statement about one integer).
#eval (List.range 8).map (fun k => Collatz.allOnesStart (k + 1))
#eval (List.range 8).map (fun k => decide (Collatz.HardSet.Hard k (Collatz.allOnesStart (k + 1))))

-- Non-vacuity 5: hardness at depth k is not everything — the witness family is
-- special. Most integers fail at some depth, so `Hard` is a real restriction.
#eval ((List.range 300).filter (fun n => decide (Collatz.HardSet.Hard 6 n))).length

end AnchoredAudit

/-! ### Definitional unfolding lemmas

These 22 were invisible to the coverage scan until the declaration regex learned
to consume attributes: every one of them is `@[simp]`, and `@[simp] lemma foo`
does not begin with the word `lemma`. Eight sibling lemmas happened to be audited
anyway, so the gate reported `ok` while claiming to cover "every theorem". The
class is closed here rather than the eight instances.
-/

section UnfoldingAudit

-- AffineAtlas.lean
#print axioms Collatz.Atlas.bCorr_cons_D
#print axioms Collatz.Atlas.bCorr_cons_U
#print axioms Collatz.Atlas.bCorr_nil
#print axioms Collatz.Atlas.bCorr_replicate_D
#print axioms Collatz.Atlas.uCount_cons_D
#print axioms Collatz.Atlas.uCount_cons_U
#print axioms Collatz.Atlas.uCount_nil
#print axioms Collatz.Atlas.uCount_replicate_D
#print axioms Collatz.Atlas.uCount_replicate_U

-- Generalized.lean
#print axioms Collatz.Generalized.bG_cons_D
#print axioms Collatz.Generalized.bG_cons_U
#print axioms Collatz.Generalized.bG_nil

-- InvariantLimit.lean
#print axioms Collatz.InvariantLimit.preimage_succ_succ
#print axioms Collatz.InvariantLimit.preimage_succ_zero

-- ResidueCylinder.lean
#print axioms Collatz.Cylinder.parityWord_succ
#print axioms Collatz.Cylinder.parityWord_zero

-- StoppingTime.lean
#print axioms Collatz.Stopping.reaches1_one

-- Valuation.lean
#print axioms Collatz.Valuation.Bcorr_cons
#print axioms Collatz.Valuation.Bcorr_nil
#print axioms Collatz.Valuation.expand_nil
#print axioms Collatz.Valuation.uCount_expand
#print axioms Collatz.Valuation.valWord_zero

end UnfoldingAudit
