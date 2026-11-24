import Candidate.GRSCC.MomentData

namespace PoissonDAG.GRSCC.MomentPolynomial
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem mask42 : packed 42 base = witness 42 := by decide +kernel
theorem mask43 : packed 43 base = witness 43 := by decide +kernel
theorem mask44 : packed 44 base = witness 44 := by decide +kernel
theorem mask45 : packed 45 base = witness 45 := by decide +kernel
theorem mask46 : packed 46 base = witness 46 := by decide +kernel
theorem mask47 : packed 47 base = witness 47 := by decide +kernel

end PoissonDAG.GRSCC.MomentPolynomial
