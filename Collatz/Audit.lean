import Collatz.AllOnes
import Collatz.AffineAtlas

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
