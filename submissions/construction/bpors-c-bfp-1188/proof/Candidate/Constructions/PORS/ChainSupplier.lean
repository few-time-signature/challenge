import Candidate.Constructions.PORS.DepthGapWords
import Candidate.Probability.BoundedCompositions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace PoissonDAG.PORS.ChainSupplier
open ChainDepths BoundedCompositions

/-- A decoded profile uses its four depths in the order of the selected leaves. -/
def profileTuple (E : Nat) : Profile E ≃ NatTuple 4 E where
  toFun x := ⟨![x.a,x.b,x.c,x.d],by simpa [Fin.sum_univ_succ,Nat.add_assoc] using x.total⟩
  invFun x := ⟨x.val 0,x.val 1,x.val 2,x.val 3,by
    simpa [Fin.sum_univ_succ,Nat.add_assoc] using x.property⟩
  left_inv _ := rfl
  right_inv x := by apply Subtype.ext; funext i; fin_cases i <;> rfl

noncomputable def rankTuple : Fin ((35:Nat).choose 3) ≃ NatTuple 4 32 :=
  (Equiv.ofBijective _ chain_depth_ranks.1).trans (profileTuple 32)

theorem decoded (r : Fin ((35:Nat).choose 3)) :
    RankGates.DepthGaps.chainValues r.val = List.ofFn (rankTuple r).val := by
  rw [RankGates.DepthGaps.chainValues_eq_profile]
  rfl

private def subtract {k E : Nat} (d : Fin k → Nat) (h : ∑ i, d i ≤ E) :
    {x : NatTuple k E // ∀ i, d i ≤ x.val i} ≃ NatTuple k (E-∑ i,d i) where
  toFun x := ⟨fun i => x.val.val i - d i,by
    rw [Finset.sum_tsub_distrib _ (fun i _ => x.property i),x.val.property]⟩
  invFun y := ⟨⟨fun i => y.val i + d i,by
    rw [Finset.sum_add_distrib,y.property,Nat.sub_add_cancel h]⟩,fun i => Nat.le_add_left ..⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; funext i; exact Nat.sub_add_cancel (x.property i)
  right_inv _ := by apply Subtype.ext; funext i; exact Nat.add_sub_cancel _ _

/-- A supplier satisfies simultaneous lower bounds by spending their sum.
The remaining depth may be assigned freely to its four coordinates. -/
theorem count_dominating (d : Fin 4 → Nat) (E : Nat) (fits : ∑ i,d i ≤ E) :
    Fintype.card {x : NatTuple 4 E // ∀ i, d i ≤ x.val i} = (E-(∑ i,d i)+3).choose 3 := by
  rw [Fintype.card_congr (subtract d fits),natTuple_card]
  have h : 4+(E-∑ i,d i)-1=(E-∑ i,d i)+3 := by omega
  rw [h]
  exact Nat.choose_symm_add

noncomputable def ranksAbove (d : Fin 4 → Nat) := Finset.univ.filter (fun r : Fin ((35:Nat).choose 3) =>
    ∀ i, d i ≤ (rankTuple r).val i)

theorem rank_count (d : Fin 4 → Nat) (fits : ∑ i,d i ≤ 32) :
    (ranksAbove d).card = (32-(∑ i,d i)+3).choose 3 := by
  classical
  let e : ↥(ranksAbove d) ≃ {x : NatTuple 4 32 // ∀ i,d i≤x.val i} :=
    {toFun := fun x => ⟨rankTuple x.val,(Finset.mem_filter.mp x.property).2⟩
     invFun := fun x => ⟨rankTuple.symm x.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
       change ∀ j, d j ≤ (rankTuple (rankTuple.symm x.val)).val j
       rw [Equiv.apply_symm_apply]; exact x.property⟩⟩
     left_inv := fun x => Subtype.ext (rankTuple.symm_apply_apply x.val)
     right_inv := fun x => Subtype.ext (rankTuple.apply_symm_apply x.val)}
  exact (Fintype.card_coe _).symm.trans ((Fintype.card_congr e).trans (count_dominating d 32 fits))

/-- Use a chosen order to place the i demands on distinct history slots.
The sum, and therefore the number of possible suppliers, is independent of this order. -/
def demand {i : Nat} (place : Fin i ↪ Fin 4) (v : Fin i → Nat) (s : Fin 4) : Nat :=
  ∑ j, if place j = s then v j else 0

theorem demand_at {i : Nat} (place : Fin i ↪ Fin 4) (v : Fin i → Nat) (j : Fin i) :
    demand place v (place j)=v j := by
  simp [demand]

theorem demand_sum {i : Nat} (place : Fin i ↪ Fin 4) (v : Fin i → Nat) :
    (∑ s,demand place v s) = ∑ j,v j := by
  unfold demand; rw [Finset.sum_comm]; simp

theorem local_choices (i d : Nat) (positive : 0<i) (fits : d≤32) (place : Fin i ↪ Fin 4) :
    (∑ v : NatTuple i d, (ranksAbove (demand place v.val)).card) =
      (d+i-1).choose (i-1) * (32-d+3).choose 3 := by
  have hs (v : NatTuple i d) : (∑ s,demand place v.val s)=d := (demand_sum ..).trans v.property
  have term (v : NatTuple i d) : (ranksAbove (demand place v.val)).card=(32-d+3).choose 3 := by
    rw [rank_count _ ((hs v).symm ▸ fits),hs]
  simp_rw [term]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,natTuple_card]
  have n : i+d-1=d+(i-1) := by omega
  have n' : d+i-1=d+(i-1) := by omega
  rw [n,n',Nat.choose_symm_add]
  rfl

end PoissonDAG.PORS.ChainSupplier
