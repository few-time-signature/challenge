import Candidate.GRSCC.MomentCheck0
import Candidate.GRSCC.MomentCheck6
import Candidate.GRSCC.MomentCheck12
import Candidate.GRSCC.MomentCheck18
import Candidate.GRSCC.MomentCheck24
import Candidate.GRSCC.MomentCheck30
import Candidate.GRSCC.MomentCheck36
import Candidate.GRSCC.MomentCheck42
import Candidate.GRSCC.MomentCheck48
import Candidate.GRSCC.MomentCheck54
import Candidate.GRSCC.MomentCheck60

namespace PoissonDAG.GRSCC.MomentPolynomial
set_option maxRecDepth 20000
set_option maxHeartbeats 0

theorem checked (mask : Fin 63) : packed mask base = witness mask := by
  fin_cases mask
  · exact mask0
  · exact mask1
  · exact mask2
  · exact mask3
  · exact mask4
  · exact mask5
  · exact mask6
  · exact mask7
  · exact mask8
  · exact mask9
  · exact mask10
  · exact mask11
  · exact mask12
  · exact mask13
  · exact mask14
  · exact mask15
  · exact mask16
  · exact mask17
  · exact mask18
  · exact mask19
  · exact mask20
  · exact mask21
  · exact mask22
  · exact mask23
  · exact mask24
  · exact mask25
  · exact mask26
  · exact mask27
  · exact mask28
  · exact mask29
  · exact mask30
  · exact mask31
  · exact mask32
  · exact mask33
  · exact mask34
  · exact mask35
  · exact mask36
  · exact mask37
  · exact mask38
  · exact mask39
  · exact mask40
  · exact mask41
  · exact mask42
  · exact mask43
  · exact mask44
  · exact mask45
  · exact mask46
  · exact mask47
  · exact mask48
  · exact mask49
  · exact mask50
  · exact mask51
  · exact mask52
  · exact mask53
  · exact mask54
  · exact mask55
  · exact mask56
  · exact mask57
  · exact mask58
  · exact mask59
  · exact mask60
  · exact mask61
  · exact mask62

end PoissonDAG.GRSCC.MomentPolynomial
