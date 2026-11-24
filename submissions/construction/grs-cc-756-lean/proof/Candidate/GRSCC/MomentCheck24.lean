import Candidate.GRSCC.MomentData

namespace PoissonDAG.GRSCC.MomentPolynomial
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem mask24 : packed 24 base = witness 24 := by decide +kernel
theorem mask25 : packed 25 base = witness 25 := by decide +kernel
theorem mask26 : packed 26 base = witness 26 := by decide +kernel
theorem mask27 : packed 27 base = witness 27 := by decide +kernel
theorem mask28 : packed 28 base = witness 28 := by decide +kernel
theorem mask29 : packed 29 base = witness 29 := by decide +kernel

end PoissonDAG.GRSCC.MomentPolynomial
