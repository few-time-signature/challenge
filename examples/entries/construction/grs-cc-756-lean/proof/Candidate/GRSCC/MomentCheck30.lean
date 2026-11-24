import Candidate.GRSCC.MomentData

namespace PoissonDAG.GRSCC.MomentPolynomial
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem mask30 : packed 30 base = witness 30 := by decide +kernel
theorem mask31 : packed 31 base = witness 31 := by decide +kernel
theorem mask32 : packed 32 base = witness 32 := by decide +kernel
theorem mask33 : packed 33 base = witness 33 := by decide +kernel
theorem mask34 : packed 34 base = witness 34 := by decide +kernel
theorem mask35 : packed 35 base = witness 35 := by decide +kernel

end PoissonDAG.GRSCC.MomentPolynomial
