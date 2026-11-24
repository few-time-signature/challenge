import Candidate.GRSCC.MomentData

namespace PoissonDAG.GRSCC.MomentPolynomial
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem mask60 : packed 60 base = witness 60 := by decide +kernel
theorem mask61 : packed 61 base = witness 61 := by decide +kernel
theorem mask62 : packed 62 base = witness 62 := by decide +kernel

end PoissonDAG.GRSCC.MomentPolynomial
