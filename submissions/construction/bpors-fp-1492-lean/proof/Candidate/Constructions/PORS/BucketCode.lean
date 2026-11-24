import Candidate.Constructions.PORS.ConfigurationRanks
import Candidate.Constructions.PORS.BucketJoint

namespace PoissonDAG.PORS.BucketCode
open ConfigurationRanks PrunedCount

def aux (B : Nat) : Fin (B*1) ≃ Fin B where
  toFun x := (finProdFinEquiv.symm x).1
  invFun x := finProdFinEquiv (x,0)
  left_inv x := by
    apply finProdFinEquiv.symm.injective
    simp only [Equiv.symm_apply_apply]
    exact Prod.ext (by rfl) (Subsingleton.elim _ _)
  right_inv x := by simp

theorem coord_tag (s : Shape) (k B D K : Nat)
    (r : Fin (((B*s.leaves.choose k)*D)^K)) (i : Fin K) :
    ((finProdFinEquiv (m:=B) (n:=D)).symm ((allRanks s k B D K r).2 i)).1.val =
      (r.val / ((B*s.leaves.choose k)*D)^i.val % ((B*s.leaves.choose k)*D)) /
        D / s.leaves.choose k := by
  let C := s.leaves.choose k
  let y : Fin ((B*C)*D) := finFunctionFinEquiv.symm r i
  let pair : Fin (B*C) × Fin D := finProdFinEquiv.symm y
  let step : Fin B × Fin C := finProdFinEquiv.symm pair.1
  change ((finProdFinEquiv (m:=B) (n:=D)).symm (finProdFinEquiv (step.1,pair.2))).1.val = _
  rw [Equiv.symm_apply_apply]
  rfl

private theorem idx_div (x B C : Nat) (hb : 0<B) (hc : 0<C) :
    x % ((B*C)*1) / 1 / C = x / 1 / C % B := by
  simp only [Nat.mul_one,Nat.div_one]
  rw [Nat.mul_comm B C,Nat.mod_mul_right_div_self]

theorem tag (s : Shape) (k B K : Nat) (hb : 0<B) (hc : 0<s.leaves.choose k)
    (r : Fin (((B*s.leaves.choose k)*1)^K)) (i : Fin K) :
    (aux B ((allRanks s k B 1 K r).2 i)).val =
      r.val / ((B*s.leaves.choose k)*1)^i.val / 1 / s.leaves.choose k % B :=
  (coord_tag s k B 1 K r i).trans (idx_div _ B _ hb hc)

def mapChoice {s : Shape} {k t : Nat} (a : Leaf s ≃ Fin t) :
    Choices s k ↪ BucketAverage.Choices t k where
  toFun x := ⟨x.val.map a.toEmbedding, Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _,by rw [Finset.card_map]; exact (Finset.mem_powersetCard.mp x.property).2⟩⟩
  inj' _ _ h := Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h))

def fullSupport {s : Shape} {k K t M : Nat} (addr : Leaf s ≃ Fin t) :
    {u : Fin K → Choices s k // (∑ i, siblings s (u i).val) ≤ M} ↪ (Fin K → BucketAverage.Choices t k) where
  toFun x i := mapChoice addr (x.val i)
  inj' x y h := Subtype.ext (funext (fun i => (mapChoice addr).injective (congrFun h i)))

end PoissonDAG.PORS.BucketCode
