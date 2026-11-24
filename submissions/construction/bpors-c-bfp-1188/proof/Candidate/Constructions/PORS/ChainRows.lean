import Candidate.Constructions.PORS.ChainAtoms
import Candidate.Constructions.PORS.ChainLift

namespace PoissonDAG.PORS.ChainRows
open ChainSupplier ChainAtoms BoundedCompositions

abbrev Rank := Fin ((35:Nat).choose 3)
abbrev RowCode := Sum Rank Letter
abbrev W (m : Nat) := ChainLift.Lift (Fin m × Fin 4) 4 32

def row {m : Nat} (w : W m) (j : Fin m) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => (j,i) ∈ w.selected)

def need {m : Nat} (w : W m) (j : Fin m) (i : ↥(row w j)) : Nat :=
  w.residual ⟨(j,i.val),(Finset.mem_filter.mp i.property).2⟩

def charge {m : Nat} (w : W m) (j : Fin m) := ∑ i : row w j, need w j i

private def pieces {m : Nat} (w : W m) : w.selected ≃ (Σ j : Fin m, ↥(row w j)) where
  toFun s := ⟨s.val.1,⟨s.val.2,Finset.mem_filter.mpr ⟨Finset.mem_univ _,s.property⟩⟩⟩
  invFun s := ⟨(s.1,s.2.val),(Finset.mem_filter.mp s.2.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem row_weight {m : Nat} (w : W m) : (∑ j,(row w j).card)=4 := by
  have e := Fintype.card_congr (pieces w)
  simpa only [Fintype.card_coe,Fintype.card_sigma,w.weight] using e.symm

theorem row_total {m : Nat} (w : W m) : ∑ j,charge w j=32 := by
  have e := Fintype.sum_equiv (pieces w) w.residual (fun x => need w x.1 x.2) (fun _ => rfl)
  rw [Fintype.sum_sigma] at e
  exact e.symm.trans w.total

def Fits {m : Nat} (w : W m) (h : Fin m → Rank) :=
  ∀ s : w.selected, w.residual s ≤ (rankTuple (h s.val.1)).val s.val.2

private def activeKind {m : Nat} (w : W m) (j : Fin m) (pos : (row w j).Nonempty) : Kind :=
  ⟨⟨(row w j).card-1,by
    have cap : (row w j).card≤4 := (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
    have := pos.card_pos
    omega⟩,⟨charge w j,by
    have cap := Finset.single_le_sum (f:=charge w) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [row_total] at cap; omega⟩⟩

private theorem arity_eq {m : Nat} (w : W m) (j : Fin m) (pos : (row w j).Nonempty) :
    (activeKind w j pos).1.val+1=(row w j).card := Nat.sub_add_cancel pos.card_pos

private def mask {m : Nat} (w : W m) (j : Fin m) (pos : (row w j).Nonempty) :
    Mask ((activeKind w j pos).1.val+1) :=
  ⟨row w j,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,(arity_eq w j pos).symm⟩⟩

private noncomputable def demands {m : Nat} (w : W m) (j : Fin m) (pos : (row w j).Nonempty) :
    NatTuple ((activeKind w j pos).1.val+1) (activeKind w j pos).2.val :=
  let e := order (mask w j pos)
  ⟨fun s => need w j (e s),Fintype.sum_equiv e _ (need w j) (fun _ => rfl)⟩

private theorem no_demand {i : Nat} (e : Fin i ↪ Fin 4) (v : Fin i → Nat) (s : Fin 4)
    (skip : ∀ j, e j ≠ s) : demand e v s=0 := by simp [demand,skip]

noncomputable def letter {m : Nat} (w : W m) (h : Fin m → Rank) (ok : Fits w h)
    (j : Fin m) (pos : (row w j).Nonempty) : Letter := by
  let s := mask w j pos
  let v := demands w j pos
  refine ⟨activeKind w j pos,s,v,h j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  intro l
  by_cases mem : l∈row w j
  · let ix := (order s).symm ⟨l,mem⟩
    have id : place s ix=l := congrArg Subtype.val ((order s).apply_symm_apply ⟨l,mem⟩)
    rw [←id,demand_at]
    have z := ok ⟨(j,l),(Finset.mem_filter.mp mem).2⟩
    change need w j (order s ix) ≤ (rankTuple (h j)).val (place s ix)
    rw [id]
    simpa only [ix,Equiv.apply_symm_apply,need] using z
  · rw [no_demand]
    · exact Nat.zero_le _
    · intro i eq
      exact mem (eq ▸ ((order s) i).property)

noncomputable def code {m : Nat} (w : W m) (h : Fin m → Rank) (ok : Fits w h)
    (j : Fin m) : RowCode := if pos : (row w j).Nonempty then .inr (letter w h ok j pos) else .inl (h j)

def history : RowCode → Rank
  | .inl r => r
  | .inr a => a.2.2.2.val

noncomputable def read {j : Kind} (s : Mask (j.1.val+1)) (v : NatTuple (j.1.val+1) j.2.val) (l : Fin 4) : Option Nat :=
  if hl : l ∈ s.val then some (v.val ((order s).symm ⟨l,hl⟩)) else none

noncomputable def offered : RowCode → Fin 4 → Option Nat
  | .inl _, _ => none
  | .inr a, l => read a.2.1 a.2.2.1 l

theorem code_history {m : Nat} (w : W m) (h : Fin m → Rank) (ok : Fits w h) (j : Fin m) :
    history (code w h ok j)=h j := by
  unfold code; split <;> rfl

theorem code_offered {m : Nat} (w : W m) (h : Fin m → Rank) (ok : Fits w h) (j : Fin m) (l : Fin 4) :
    offered (code w h ok j) l = (if mem : (j,l) ∈ w.selected then some (w.residual ⟨(j,l),mem⟩) else none) := by
  by_cases mem : l∈row w j
  · have pos : (row w j).Nonempty := ⟨l,mem⟩
    have hsel := (Finset.mem_filter.mp mem).2
    simp only [code,dif_pos pos,offered,letter,read,mask,mem,dif_pos,demands,
      need,hsel]
    apply congrArg some
    apply congrArg w.residual
    apply Subtype.ext
    exact congrArg (fun x : ↥(row w j) => (j,x.val)) ((order (mask w j pos)).apply_symm_apply ⟨l,mem⟩)
  · have hsel : (j,l) ∉ w.selected := fun h => mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    unfold code; split <;> simp [offered,letter,read,mask,mem,hsel]

end PoissonDAG.PORS.ChainRows
