import Candidate.Constructions.PORS.ChainSupplier
import Mathlib.Data.Finset.Image

namespace PoissonDAG.PORS.ChainLift

/-- One local witness keeps the historical slot that supplies each target
leaf, together with the requested residual at that slot. -/
structure Lift (Slot : Type) [DecidableEq Slot] (k E : Nat) where
  selected : Finset Slot
  weight : selected.card=k
  residual : selected → Nat
  total : ∑ z, residual z=E

section
variable {Leaf Slot : Type} [DecidableEq Slot] [DecidableEq Leaf] {k E : Nat}
variable (leaf : Slot → Leaf) (available : Slot → Nat)
variable (target : Fin k ↪ Leaf) (need : Fin k → Nat)
variable (total : ∑ i,need i=E)
variable (covered : ∀ i, ∃ s,leaf s=target i ∧ need i≤available s)

noncomputable def pick (i : Fin k) : Slot := (covered i).choose

theorem picks (i : Fin k) : leaf (pick leaf available target need covered i)=target i ∧
    need i ≤ available (pick leaf available target need covered i) := (covered i).choose_spec

noncomputable def injection : Fin k ↪ Slot :=
  ⟨pick leaf available target need covered,fun i j h => target.injective
    ((picks leaf available target need covered i).1.symm.trans
      ((congrArg leaf h).trans (picks leaf available target need covered j).1))⟩

private noncomputable def ontoSelection (f : Fin k ↪ Slot) :
    Fin k ≃ ↥(Finset.univ.map f) where
  toFun i := ⟨f i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  invFun s := (Finset.mem_map.mp s.property).choose
  left_inv i := f.injective ((Finset.mem_map.mp (Finset.mem_map.mpr
    ⟨i,Finset.mem_univ _,rfl⟩ : f i ∈ Finset.univ.map f)).choose_spec.2)
  right_inv s := Subtype.ext ((Finset.mem_map.mp s.property).choose_spec.2)

noncomputable def witness : Lift Slot k E :=
  let f := injection leaf available target need covered
  let e := ontoSelection f
  { selected := Finset.univ.map f
    weight := by simp
    residual := fun s => need (e.symm s)
    total := (Fintype.sum_equiv e.symm _ need (fun _ => rfl)).trans total }

omit total in
private theorem underlying (s : ↥(Finset.univ.map (injection leaf available target need covered))) :
    let e := ontoSelection (injection leaf available target need covered)
    leaf s.val=target (e.symm s) ∧ need (e.symm s) ≤ available s.val := by
  let f := injection leaf available target need covered
  let e := ontoSelection f
  have value : f (e.symm s) = s.val := congrArg Subtype.val (e.apply_symm_apply s)
  have hp := picks leaf available target need covered (e.symm s)
  change leaf (f (e.symm s)) = _ ∧ _ ≤ available (f (e.symm s)) at hp
  rwa [value] at hp

theorem witness_ok (s : (witness leaf available target need total covered).selected) :
    (witness leaf available target need total covered).residual s ≤ available s.val :=
  (underlying leaf available target need covered s).2

def requests (t : Fin k → Leaf) (v : Fin k → Nat) : Finset (Leaf×Nat) :=
  Finset.univ.image fun i => (t i,v i)

def recover (l : Slot → Leaf) (w : Lift Slot k E) : Finset (Leaf×Nat) :=
  Finset.univ.image fun i : w.selected => (l i.val,w.residual i)

theorem recover_witness :
    recover leaf (witness leaf available target need total covered) = requests target need := by
  let f := injection leaf available target need covered
  let e := ontoSelection f
  ext x
  constructor
  · intro hx
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨e.symm s,Finset.mem_univ _,?_⟩
    exact (congrArg (fun l => (l,need (e.symm s))) (underlying leaf available target need covered s).1.symm).trans hs
  · intro hx
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨e i,Finset.mem_univ _,?_⟩
    change (leaf (f i),need (e.symm (e i)))=_
    rw [e.symm_apply_apply]
    exact (congrArg (fun l => (l,need i)) (picks leaf available target need covered i).1).trans hi

end

end PoissonDAG.PORS.ChainLift
