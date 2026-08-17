import Collatz.AllOnes
import Collatz.AffineAtlas
import Collatz.Generalized
import Collatz.ResidueCylinder

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

-- Non-vacuity. The bijection is only a statement if the 2^k residues really do
-- give 2^k DIFFERENT words.
#eval ((List.range 32).map (fun n => Collatz.Cylinder.parityWord n 5)).eraseDups.length
-- the r_w = 0 boundary, concretely: the all-D cylinder at k = 5
#eval (Collatz.Cylinder.parityWord 0 5, Collatz.Cylinder.parityWord 32 5)
-- and words genuinely vary with n, so parityWord is not a constant function
#eval ((List.range 8).map (fun n => Collatz.Cylinder.parityWord n 3))

end CylinderAudit
