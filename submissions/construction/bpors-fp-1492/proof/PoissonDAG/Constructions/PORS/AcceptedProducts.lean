import PoissonDAG.Constructions.PORS.ConfigurationRanks
import Mathlib.Data.List.NodupEquivFin

namespace PoissonDAG.PORS.AcceptedProducts
open ConfigurationRanks CoordinatePruning PrunedCount

/-- Rank validity is part of the gate. The predicate may couple the
supports of every coordinate, but is independent of the auxiliary digits. -/
def Gate (sc : Scheme) {n : Nat} {U V : Type} (e : Fin n ≃ U × V) (keep : U → Prop) :=
  ∀ x < 2^sc.encoder.inputs, sc.accept x = true ↔ ∃ h : x < n, keep (e ⟨x,h⟩).1

private theorem accepted_iff {sc : Scheme} {n : Nat} {U V : Type}
    {e : Fin n ≃ U × V} {keep : U → Prop} (gate : Gate sc e keep)
    (fits : n ≤ 2^sc.encoder.inputs) (x : Nat) :
    x ∈ sc.accepted ↔ ∃ h : x<n, keep (e ⟨x,h⟩).1 := by
  constructor
  · intro hx
    obtain ⟨mem,ok⟩ := List.mem_filter.mp hx
    exact (gate x (List.mem_range.mp mem)).mp ok
  · rintro ⟨h,valid⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (h.trans_le fits),
      (gate x (h.trans_le fits)).mpr ⟨h,valid⟩⟩

private def acceptedRank {sc : Scheme} {n : Nat} {U V : Type} {e : Fin n ≃ U × V}
    {keep : U → Prop} (gate : Gate sc e keep) (fits : n ≤ 2^sc.encoder.inputs) :
    {x // x ∈ sc.accepted} ≃ {r : Fin n // keep (e r).1} where
  toFun x := ⟨⟨x.val,((accepted_iff gate fits x.val).mp x.property).choose⟩,
    ((accepted_iff gate fits x.val).mp x.property).choose_spec⟩
  invFun r := ⟨r.val.val,(accepted_iff gate fits _).mpr ⟨r.val.isLt,r.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def split {n : Nat} {U V : Type} (e : Fin n ≃ U × V) (keep : U → Prop) :
    {r : Fin n // keep (e r).1} ≃ {u : U // keep u} × V where
  toFun r := (⟨(e r.val).1,r.property⟩,(e r.val).2)
  invFun x := ⟨e.symm (x.1.val,x.2),by simpa using x.1.property⟩
  left_inv r := Subtype.ext (e.symm_apply_apply r.val)
  right_inv x := by ext <;> simp

/-- Uniform sampling with replacement from the accepted list gives a
uniform pruned support tuple and independent uniform auxiliary digits. -/
def equiv {sc : Scheme} {n : Nat} {U V : Type} {e : Fin n ≃ U × V} {keep : U → Prop}
    (gate : Gate sc e keep) (fits : n ≤ 2^sc.encoder.inputs) :
    Fin sc.accepted.length ≃ {u : U // keep u} × V :=
  let nd : sc.accepted.Nodup := List.nodup_range.filter _
  (nd.getEquiv sc.accepted).trans ((acceptedRank gate fits).trans (split e keep))

theorem equiv_rank {sc : Scheme} {n : Nat} {U V : Type} {e : Fin n ≃ U × V}
    {keep : U → Prop} (gate : Gate sc e keep) (fits : n ≤ 2^sc.encoder.inputs)
    (i : Fin sc.accepted.length) :
    ∃ h : sc.accepted[i] < n,
      (((equiv gate fits i).1.val),(equiv gate fits i).2) = e ⟨sc.accepted[i],h⟩ := by
  exact ⟨((accepted_iff gate fits _).mp (List.getElem_mem i.isLt)).choose,rfl⟩

def keep (s : Shape) (k K M : Nat) (u : Fin K → Choices s k) : Prop :=
  (∑ i, siblings s (u i).val) ≤ M

def rank {sc : Scheme} {n : Nat} {U V : Type} {e : Fin n ≃ U × V} {keep : U → Prop}
    (gate : Gate sc e keep) (fits : n ≤ 2^sc.encoder.inputs) (i : Fin sc.accepted.length) : Fin n :=
  ⟨sc.accepted[i],((accepted_iff gate fits _).mp (List.getElem_mem i.isLt)).choose⟩

theorem support_eq {sc : Scheme} {n : Nat} {U V : Type} {e : Fin n ≃ U × V} {keep : U → Prop}
    (gate : Gate sc e keep) (fits : n ≤ 2^sc.encoder.inputs) (i : Fin sc.accepted.length) :
    (equiv gate fits i).1.val = (e (rank gate fits i)).1 := rfl

theorem tags_eq {sc : Scheme} {n : Nat} {U V : Type} {e : Fin n ≃ U × V} {keep : U → Prop}
    (gate : Gate sc e keep) (fits : n ≤ 2^sc.encoder.inputs) (i : Fin sc.accepted.length) :
    (equiv gate fits i).2 = (e (rank gate fits i)).2 := rfl

private def retained (s : Shape) (k K M : Nat) :
    {u // keep s k K M u} ≃ ↥(survivors s k K M) where
  toFun u := ⟨fun i => (u.val i).val,Finset.mem_filter.mpr
    ⟨Fintype.mem_piFinset.mpr (fun i => (u.val i).property),u.property⟩⟩
  invFun x := ⟨fun i => ⟨x.val i,(Fintype.mem_piFinset.mp (Finset.mem_filter.mp x.property).1 i)⟩,
    (Finset.mem_filter.mp x.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem length {sc : Scheme} (s : Shape) (k K M B D : Nat)
    (gate : Gate sc (allRanks s k B D K) (keep s k K M))
    (fits : ((B*s.leaves.choose k)*D)^K ≤ 2^sc.encoder.inputs) :
    sc.accepted.length = (survivors s k K M).card * (B*D)^K := by
  classical
  have e := (equiv gate fits).trans ((retained s k K M).prodCongr (Equiv.refl _))
  simpa using Fintype.card_congr e

end PoissonDAG.PORS.AcceptedProducts
