import Candidate.GRSCC.MomentData

namespace PoissonDAG.GRSCC.MomentPolynomial
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem mask0 : packed 0 base = witness 0 := by decide +kernel
theorem mask1 : packed 1 base = witness 1 := by decide +kernel
theorem mask2 : packed 2 base = witness 2 := by decide +kernel
theorem mask3 : packed 3 base = witness 3 := by decide +kernel
theorem mask4 : packed 4 base = witness 4 := by decide +kernel
theorem mask5 : packed 5 base = witness 5 := by decide +kernel

end PoissonDAG.GRSCC.MomentPolynomial
