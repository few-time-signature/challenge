import Candidate.Constructions.PORS.CoordinatePruning
import Candidate.Constructions.PORS.SingleAccepted
import Mathlib.Algebra.BigOperators.Fin

namespace PoissonDAG.PORS.ConfigurationRanks
open PrunedCount CoordinatePruning

abbrev Choices (s : Shape) (k : Nat) := ↥((Finset.univ : Finset (Leaf s)).powersetCard k)

def rankedSupport (s : Shape) (k : Nat) (r : Fin (s.leaves.choose k)) : Choices s k :=
  ⟨SingleAccepted.leafSupport s k r, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by
    have h := (Finset.mem_powersetCard.mp (Colex.support_mem r.isLt)).2
    rwa [← SingleAccepted.address_image s k r r.isLt,Finset.card_map] at h⟩⟩

private theorem support_bijective (s : Shape) (k : Nat) : Function.Bijective (rankedSupport s k) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro r t h
    apply Fin.ext
    apply Colex.support_injective r.isLt t.isLt
    rw [← SingleAccepted.address_image s k r r.isLt,← SingleAccepted.address_image s k t t.isLt]
    exact congrArg (Finset.map (SingleAccepted.address s)) (congrArg Subtype.val h)
  · simp [Choices,Finset.card_powersetCard,card_leaf]

/-- Each unpruned coordinate factors into bucket, support, and depth digits.
The depth digit is least significant, as in the rank gate. -/
noncomputable def one (s : Shape) (k B D : Nat) :
    Fin ((B * s.leaves.choose k) * D) ≃ Choices s k × Fin (B*D) :=
  let C := s.leaves.choose k
  let split := (finProdFinEquiv (m := B*C) (n := D)).symm
  let digits := (finProdFinEquiv (m := B) (n := C)).symm.prodCongr (Equiv.refl (Fin D))
  let swap := (Equiv.prodComm (Fin B) (Fin C)).prodCongr (Equiv.refl (Fin D))
  let regroup := Equiv.prodAssoc (Fin C) (Fin B) (Fin D)
  let support := Equiv.ofBijective _ (support_bijective s k)
  split.trans (digits.trans (swap.trans (regroup.trans (support.prodCongr finProdFinEquiv))))

noncomputable def allRanks (s : Shape) (k B D K : Nat) :
    Fin (((B * s.leaves.choose k) * D)^K) ≃
      (Fin K → Choices s k) × (Fin K → Fin (B*D)) :=
  finFunctionFinEquiv.symm.trans ((Equiv.piCongrRight fun _ => one s k B D).trans
    (Equiv.arrowProdEquivProdArrow _ _ _))

theorem one_support (s : Shape) (k B D : Nat) (r : Fin ((B * s.leaves.choose k) * D)) :
    ((one s k B D r).1).val =
      SingleAccepted.leafSupport s k (r.val / D % s.leaves.choose k) := rfl

theorem digit_support (s : Shape) (k B D K : Nat) (r : Fin (((B * s.leaves.choose k) * D)^K))
    (i : Fin K) :
    ((allRanks s k B D K r).1 i).val =
      SingleAccepted.leafSupport s k (((r.val / ((B*s.leaves.choose k)*D)^i.val) %
        ((B*s.leaves.choose k)*D)) / D % s.leaves.choose k) := rfl

/-- The shared cutoff filters only the tuple of supports. All bucket and
depth assignments remain available for every surviving tuple. -/
theorem countRanks (s : Shape) (k B D K M : Nat) :
    (Finset.univ.filter (fun r : Fin (((B*s.leaves.choose k)*D)^K) =>
      (∑ i, siblings s (((allRanks s k B D K r).1 i).val)) ≤ M)).card =
    (survivors s k K M).card * (B*D)^K := by
  classical
  let e := allRanks s k B D K
  let fs (r : Fin (((B*s.leaves.choose k)*D)^K)) (i : Fin K) := ((e r).1 i).val
  let target := (survivors s k K M) ×ˢ (Finset.univ : Finset (Fin K → Fin (B*D)))
  have target_count : target.card=(survivors s k K M).card * (B*D)^K := by
    simp [target,Fintype.card_fun]
  rw [← target_count]
  apply Finset.card_bij (fun r _ => (fs r,(e r).2))
  · intro r hr
    refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨?_,(Finset.mem_filter.mp hr).2⟩,Finset.mem_univ _⟩
    exact Fintype.mem_piFinset.mpr (fun i => ((e r).1 i).property)
  · intro x _ y _ h
    apply e.injective
    apply Prod.ext
    · funext i
      exact Subtype.ext (congrFun (congrArg Prod.fst h) i)
    · have haux := congrArg (fun z : (Fin K → Finset (Leaf s)) × (Fin K → Fin (B*D)) => z.2) h
      exact haux
  · rintro ⟨u,v⟩ huv
    obtain ⟨hu,cut⟩ := Finset.mem_filter.mp (Finset.mem_product.mp huv).1
    let a (i : Fin K) : Choices s k := ⟨u i,(Fintype.mem_piFinset.mp hu i)⟩
    let r := e.symm (a,v)
    have he : e r = (a,v) := e.apply_symm_apply _
    have hfs : fs r=u := by funext i; simp [fs,he,a]
    refine ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · change (∑ i, siblings s (fs r i)) ≤ M
      rwa [hfs]
    · rw [hfs,he]

end PoissonDAG.PORS.ConfigurationRanks
