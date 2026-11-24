import Candidate.GRSCC.MomentData

namespace PoissonDAG.GRSCC.MomentPolynomial
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem mask12 : packed 12 base = witness 12 := by decide +kernel
theorem mask13 : packed 13 base = witness 13 := by decide +kernel
theorem mask14 : packed 14 base = witness 14 := by decide +kernel
theorem mask15 : packed 15 base = witness 15 := by decide +kernel
theorem mask16 : packed 16 base = witness 16 := by decide +kernel
theorem mask17 : packed 17 base = witness 17 := by decide +kernel

end PoissonDAG.GRSCC.MomentPolynomial
