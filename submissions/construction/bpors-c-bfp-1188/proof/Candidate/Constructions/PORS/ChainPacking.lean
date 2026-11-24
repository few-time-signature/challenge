import Candidate.Constructions.PORS.ChainRows

namespace PoissonDAG.PORS.ChainPacking
open ChainRows ChainAtoms ChainRefined

def arity : RowCode → Nat
  | .inl _ => 0
  | .inr a => a.1.1.val+1
def residual : RowCode → Nat
  | .inl _ => 0
  | .inr a => a.1.2.val

def active {m : Nat} (a : Fin m → RowCode) := Finset.univ.filter (fun j => (a j).isRight)

def Valid {m : Nat} (a : Fin m → RowCode) := (∑ j,arity (a j))=4 ∧ (∑ j,residual (a j))=32

private theorem zero_if {m : Nat} (w : W m) (j : Fin m) (empty : ¬ (row w j).Nonempty) :
    (row w j).card=0 ∧ charge w j=0 := by
  have no := Finset.not_nonempty_iff_eq_empty.mp empty
  constructor
  · rw [no]; rfl
  · unfold charge
    apply Finset.sum_eq_zero
    intro i _
    exact (empty ⟨i.val,i.property⟩).elim

theorem code_valid {m : Nat} (w : W m) (h : Fin m → Rank) (ok : Fits w h) :
    Valid (code w h ok) := by
  have one (j) : arity (code w h ok j)=(row w j).card ∧ residual (code w h ok j)=charge w j := by
    unfold code
    split
    next pos =>
      change (row w j).card-1+1 = _ ∧ _ = _
      exact ⟨Nat.sub_add_cancel pos.card_pos,rfl⟩
    next neg => exact ⟨(zero_if w j neg).1.symm,(zero_if w j neg).2.symm⟩
  exact ⟨(Finset.sum_congr rfl (fun j _ => (one j).1)).trans (row_weight w),
    (Finset.sum_congr rfl (fun j _ => (one j).2)).trans (row_total w)⟩

private noncomputable def slotOrder {m k : Nat} (S : Finset (Fin m)) (card : S.card=k) : Fin k ≃ ↥S :=
  (Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans card)).symm

abbrev Masks (m k : Nat) := ↥((Finset.univ : Finset (Fin m)).powersetCard k)
abbrev Packet (m : Nat) := Σ t : Fin 4, Σ S : Masks m (t.val+1),
  ↥(words (t.val+1)) × ((↥(S.valᶜ)) → Rank)

private theorem exists_right {m : Nat} (a : Fin m → RowCode) (s : active a) :
    ∃ x, a s.val = .inr x := by
  have h := (Finset.mem_filter.mp s.property).2
  cases eq : a s.val with
  | inl r => simp [eq] at h
  | inr x => exact ⟨x,rfl⟩

private theorem exists_left {m : Nat} (a : Fin m → RowCode) (s : ↥((active a)ᶜ)) :
    ∃ r, a s.val = .inl r := by
  have h := Finset.mem_compl.mp s.property
  cases eq : a s.val with
  | inl r => exact ⟨r,rfl⟩
  | inr x => exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [eq]⟩)).elim

private noncomputable def activeLetter {m : Nat} (a : Fin m → RowCode) (s : active a) : Letter :=
  (exists_right a s).choose

private noncomputable def inactiveRank {m : Nat} (a : Fin m → RowCode) (s : ↥((active a)ᶜ)) : Rank :=
  (exists_left a s).choose

private theorem active_value {m : Nat} (a : Fin m → RowCode) (s : active a) :
    a s.val = .inr (activeLetter a s) := (exists_right a s).choose_spec

private theorem inactive_value {m : Nat} (a : Fin m → RowCode) (s : ↥((active a)ᶜ)) :
    a s.val = .inl (inactiveRank a s) := (exists_left a s).choose_spec

private theorem active_sum {m : Nat} (a : Fin m → RowCode) (f : RowCode → Nat)
    (zero : ∀ r, f (.inl r)=0) :
    (∑ j : active a,f (a j.val)) = ∑ j,f (a j) := by
  rw [Finset.sum_coe_sort (active a) (fun j => f (a j))]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  rw [inactive_value a ⟨j,Finset.mem_compl.mpr hj⟩]
  exact zero _

private theorem active_card {m : Nat} (a : Fin m → RowCode) (valid : Valid a) :
    0<(active a).card ∧ (active a).card≤4 := by
  have s := (active_sum a arity (fun _ => rfl)).trans valid.1
  have positive : ∀ i : active a, 1≤arity (a i.val) := by
    intro i; rw [active_value a i]; exact Nat.succ_le_succ (Nat.zero_le _)
  constructor
  · by_contra! no
    have empty : active a=∅ := Finset.card_eq_zero.mp (by omega)
    haveI : IsEmpty (↥(active a)) := ⟨fun x => (Finset.not_nonempty_iff_eq_empty.mpr empty) ⟨x.val,x.property⟩⟩
    simp at s
  · have lower := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => positive i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,Nat.cast_id,mul_one,s] using lower

private noncomputable def packedWords {m : Nat} (a : Fin m → RowCode) (valid : Valid a)
    {n : Nat} (e : Fin n ≃ ↥(active a)) : ↥(words n) := by
  let out (i : Fin n) := activeLetter a (e i)
  refine ⟨out,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  have s1 := (active_sum a arity (fun _ => rfl)).trans valid.1
  have s2 := (active_sum a residual (fun _ => rfl)).trans valid.2
  have h (i : Fin n) : deg (out i).1 = arity (a (e i).val)+17*residual (a (e i).val) := by
    rw [active_value a (e i)]; rfl
  rw [Finset.sum_congr rfl (fun i _ => h i),Finset.sum_add_distrib,←Finset.mul_sum,
    Fintype.sum_equiv e _ (fun j => arity (a j.val)) (fun _ => rfl),
    Fintype.sum_equiv e _ (fun j => residual (a j.val)) (fun _ => rfl),s1,s2]
  rfl

noncomputable def pack {m : Nat} (a : Fin m → RowCode) (valid : Valid a) : Packet m := by
  have pos := (active_card a valid).1
  have cap := (active_card a valid).2
  let t : Fin 4 := ⟨(active a).card-1,by omega⟩
  have eqn : (active a).card=t.val+1 := (Nat.sub_add_cancel pos).symm
  let S : Masks m (t.val+1) := ⟨active a,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,eqn⟩⟩
  exact ⟨t,S,packedWords a valid (slotOrder (active a) eqn),inactiveRank a⟩

noncomputable def unpack {m : Nat} (v : Packet m) (i : Fin m) : RowCode :=
  if hi : i∈v.2.1.val then .inr (v.2.2.1.val
    ((slotOrder v.2.1.val (Finset.mem_powersetCard.mp v.2.1.property).2).symm ⟨i,hi⟩))
  else .inl (v.2.2.2 ⟨i,Finset.mem_compl.mpr hi⟩)

theorem unpack_pack {m : Nat} (a : Fin m → RowCode) (valid : Valid a) :
    unpack (pack a valid)=a := by
  funext i
  by_cases hi : i∈active a
  · simp only [unpack,pack,packedWords,dif_pos hi]
    let e := slotOrder (k:=(active a).card-1+1) (active a)
      (Nat.sub_add_cancel (active_card a valid).1).symm
    exact (congrArg (fun s => (Sum.inr (activeLetter a s) : RowCode))
      (e.apply_symm_apply ⟨i,hi⟩)).trans (active_value a ⟨i,hi⟩).symm
  · simpa only [unpack,pack,dif_neg hi] using (inactive_value a ⟨i,Finset.mem_compl.mpr hi⟩).symm

theorem packet_card (m : Nat) :
    Fintype.card (Packet m) = ∑ t : Fin 4,m.choose (t.val+1) *
      coefs[t.val]?.getD 0 * ChainRefined.p.depthCount^(m-(t.val+1)) := by
  classical
  have one (t : Fin 4) (S : Masks m (t.val+1)) :
      Fintype.card (↥(words (t.val+1)) × (↥(S.valᶜ) → Rank)) =
        coefs[t.val]?.getD 0 * p.depthCount^(m-(t.val+1)) := by
    rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_coe,Fintype.card_coe,Fintype.card_fin,
      Finset.card_compl,Fintype.card_fin,(Finset.mem_powersetCard.mp S.property).2,
      counted _ (Nat.succ_pos _) (by have := t.isLt; omega),
      ChainDepths.chain_depth_ranks.2]
    rfl
  simp only [Packet,Fintype.card_sigma,one,Finset.sum_const,Finset.card_univ,Masks,
    Fintype.card_coe,Finset.card_powersetCard,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_assoc]

end PoissonDAG.PORS.ChainPacking
