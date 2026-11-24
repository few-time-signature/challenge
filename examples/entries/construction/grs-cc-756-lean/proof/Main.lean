import Candidate.GRSCC.MomentChecks
import Candidate.GRSCC.MomentCertificate

open PoissonDAG
open PoissonDAG.GRSCC

theorem Submission.certificate : V2.ConstructionCertificate scheme 756 :=
  MomentPolynomial.certified_of_table MomentPolynomial.checked
