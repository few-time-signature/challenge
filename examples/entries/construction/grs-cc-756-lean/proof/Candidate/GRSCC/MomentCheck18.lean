import Candidate.GRSCC.MomentData

namespace PoissonDAG.GRSCC.MomentPolynomial
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem mask18 : packed 18 base = witness 18 := by decide +kernel
theorem mask19 : packed 19 base = witness 19 := by decide +kernel
theorem mask20 : packed 20 base = witness 20 := by decide +kernel
theorem mask21 : packed 21 base = witness 21 := by decide +kernel
theorem mask22 : packed 22 base = witness 22 := by decide +kernel
theorem mask23 : packed 23 base = witness 23 := by decide +kernel

end PoissonDAG.GRSCC.MomentPolynomial
