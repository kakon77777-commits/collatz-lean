import Collatz.AllOnes

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
