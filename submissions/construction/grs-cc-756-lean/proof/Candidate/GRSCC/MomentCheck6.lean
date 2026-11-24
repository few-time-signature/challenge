import Candidate.GRSCC.MomentData

namespace PoissonDAG.GRSCC.MomentPolynomial
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem mask6 : packed 6 base = witness 6 := by decide +kernel
theorem mask7 : packed 7 base = witness 7 := by decide +kernel
theorem mask8 : packed 8 base = witness 8 := by decide +kernel
theorem mask9 : packed 9 base = witness 9 := by decide +kernel
theorem mask10 : packed 10 base = witness 10 := by decide +kernel
theorem mask11 : packed 11 base = witness 11 := by decide +kernel

end PoissonDAG.GRSCC.MomentPolynomial
