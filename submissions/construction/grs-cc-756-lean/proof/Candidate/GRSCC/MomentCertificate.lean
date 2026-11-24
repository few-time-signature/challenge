import Candidate.GRSCC.MomentData
import PoissonDAG.Constructions.GRSCC.Certification

namespace PoissonDAG.GRSCC.MomentPolynomial
set_option maxRecDepth 20000
set_option maxHeartbeats 0

deriving instance DecidableEq for Term

def multiplier (m v : Nat) := (Nat.choose 6 (m-v)) * ((6-(m-v)).choose v)
def numeratorTerm (m v mask : Nat) : Int :=
  subsetSign mask * (((witness mask / base^(v+7*(m-v)) % base) / multiplier m v : Nat) : Int)
def cap (m v : Nat) := (Small.caps[m]?.getD [])[v-1]?.getD 0

private theorem entries : ∀ m v : Fin 7, v.val ≤ m.val →
    terms[v.val+7*(m.val-v.val)]? = some ⟨multiplier m v,v.val,m.val-v.val⟩ ∧
    0 < multiplier m v := by decide +kernel

private theorem cap_checks : ∀ m v : Fin 7, 2 ≤ m.val → 0 < v.val → v.val ≤ m.val →
    ((List.range 63).map (numeratorTerm m v)).sum*1000000 ≤
      (cap m v : Int)*(15597^(m.val+1)*31^(m.val-v.val) : Nat) := by decide +kernel

private theorem term_eq (checked : ∀ i : Fin 63, packed i base = witness i) (m v : Fin 7) (valid : v.val ≤ m.val) (mask : Fin 63) :
    SupplierFold.contribution m v mask = numeratorTerm m v mask := by
  obtain ⟨entry,positive⟩ := entries m v valid
  have h := extract mask (v.val+7*(m.val-v.val))
  rw [checked,List.getElem?_map,entry] at h
  change _ = measure mask (monomial ⟨multiplier m v,v.val,m.val-v.val⟩) at h
  rw [monomial_mass] at h
  unfold numeratorTerm
  rw [signed,h,Nat.mul_div_cancel_left _ positive]

theorem local_bounds (checked : ∀ i : Fin 63, packed i base = witness i) (m v : Nat) (lo : 2 ≤ m) (hi : m ≤ 6) (pos : 0 < v) (valid : v ≤ m) :
    localCover m v ≤ (cap m v : Rat)/1000000 := by
  apply SupplierFold.bound m v _ pos valid
  have m7 : m < 7 := by omega
  have v7 : v < 7 := by omega
  have eqn : (List.range 63).map (SupplierFold.contribution m v) =
      (List.range 63).map (numeratorTerm m v) :=
    List.map_congr_left (fun i h => term_eq checked ⟨m,m7⟩ ⟨v,v7⟩ valid ⟨i,List.mem_range.mp h⟩)
  rw [eqn]
  exact cap_checks ⟨m,m7⟩ ⟨v,v7⟩ lo pos valid

/-- The fixed graph, encoder and four-byte counter meet the challenge's
correctness, authentication, cost, size and raw-covering requirements. -/
theorem certified_of_table (checked : ∀ i : Fin 63, packed i base = witness i) :
    V2.ConstructionCertificate scheme 756 := construction756_of_local_bounds (local_bounds checked)

#print axioms certified_of_table
end PoissonDAG.GRSCC.MomentPolynomial
