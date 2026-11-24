import Candidate.Constructions.PORS.ChainRankGate
import Candidate.Constructions.PORS.ChainSupplier

namespace PoissonDAG.PORS.ChainLaw
open ChainProgram ChainRefined Literal PrunedCount ConfigurationRanks RankGates

attribute [local irreducible] Literal.scheme Literal.shape Scheme.accepted

/-- The acceptance predicate constrains the tuple of supports only. -/
abbrev H := {u : Fin p.K → Choices child p.k // AcceptedProducts.keep child p.k p.K p.M u}
abbrev Buckets := Fin p.K → Fin p.buckets
abbrev DepthRanks := Fin p.K → Fin ((35:Nat).choose 3)

private theorem depth_count : p.depthCount=(35:Nat).choose 3 := by decide +kernel
private def splitDigits : Fin (p.buckets*p.depthCount) ≃ Fin p.buckets × Fin ((35:Nat).choose 3) :=
  finProdFinEquiv.symm.trans ((Equiv.refl _).prodCongr (finCongr depth_count))

attribute [local irreducible] ChainRefined.p in
noncomputable def accepted : Fin (scheme p).accepted.length ≃ H × (Buckets × DepthRanks) :=
  (AcceptedProducts.equiv ChainRankGate.gate ChainRankGate.fits_domain).trans
    ((Equiv.refl _).prodCongr ((Equiv.piCongrRight fun _ => splitDigits).trans
      (Equiv.arrowProdEquivProdArrow _ _ _)))

private noncomputable abbrev rawRank :=
  AcceptedProducts.rank ChainRankGate.gate ChainRankGate.fits_domain

attribute [local irreducible] ChainRefined.p in
theorem owner (z : Fin (scheme p).accepted.length) (i : Fin p.K) :
    ((accepted z).2.1 i).val=(coord (scheme p).accepted[z] i.val).bucket := by
  let e := AcceptedProducts.tags_eq ChainRankGate.gate ChainRankGate.fits_domain z
  exact (congrArg (fun f => (splitDigits (f i)).1.val) e).trans (ChainRankGate.tag_owner (rawRank z) i)

attribute [local irreducible] ChainRefined.p in
theorem depthRank_eq (z : Fin (scheme p).accepted.length) (i : Fin p.K) :
    (accepted z).2.2 i=ChainRankGate.profileRank (scheme p).accepted[z] i.val := by
  apply Fin.ext
  let e := AcceptedProducts.tags_eq ChainRankGate.gate ChainRankGate.fits_domain z
  exact (congrArg (fun f => (splitDigits (f i)).2.val) e).trans (ChainRankGate.tag_depth (rawRank z) i)

attribute [local irreducible] ChainRefined.p in
theorem selected (z : Fin (scheme p).accepted.length) (i : Fin p.K) :
    ((accepted z).1.val i).val=ChainRankGate.support (scheme p).accepted[z] i.val := by
  let e := AcceptedProducts.support_eq ChainRankGate.gate ChainRankGate.fits_domain z
  exact (congrArg (fun f => (f i).val) e).trans (ChainRankGate.digit (rawRank z) i)

/-- Assign a support its unique colex rank, giving a canonical local slot
number to each leaf independently of any history or choice of depth. -/
private noncomputable def supportEquiv (s : Shape) (k : Nat) : Fin (s.leaves.choose k) ≃ Choices s k :=
  Equiv.ofBijective (rankedSupport s k) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · intro x y eq
      apply Fin.ext
      apply Colex.support_injective x.isLt y.isLt
      rw [← SingleAccepted.address_image s k x x.isLt,← SingleAccepted.address_image s k y y.isLt]
      exact congrArg (Finset.map (SingleAccepted.address s)) (congrArg Subtype.val eq)
    · simp [Choices,card_leaf])

noncomputable def supportRank (h : H) (i : Fin p.K) : Fin ChainRankGate.C :=
  (supportEquiv child p.k).symm (h.val i)

theorem supportRank_eq (z : Fin (scheme p).accepted.length) (i : Fin p.K) :
    (supportRank (accepted z).1 i).val=ChainRankGate.supportRank (scheme p).accepted[z] i.val := by
  let raw := (scheme p).accepted[z]
  let r : Fin ChainRankGate.C := ⟨ChainRankGate.supportRank raw i,by
    change _ < child.leaves.choose p.k
    rw [ChainRankGate.t_eq]
    exact ChainRankGate.support_fit raw i⟩
  have he : supportRank (accepted z).1 i = r := by
    apply (supportEquiv child p.k).injective
    rw [supportRank,Equiv.apply_symm_apply]
    exact Subtype.ext (selected z i)
  exact congrArg Fin.val he

private def ids (r : Fin ChainRankGate.C) := (Colex.digits p.t p.k r.val).reverse
private theorem ids_len (r : Fin ChainRankGate.C) : (ids r).length=4 := by
  simp only [ids,List.length_reverse,Colex.digits_length]; rfl
private theorem id_order (r : Fin ChainRankGate.C) : (ids r).Pairwise (· < ·) := by
  have valid : r.val<p.t.choose p.k := by rw [←ChainRankGate.t_eq]; exact r.isLt
  exact (Colex.digits_spec (Nat.le_refl p.t) valid).2.2.reverse
private theorem id_bound (r : Fin ChainRankGate.C) (v : Nat) (hv : v∈ids r) : v<p.t := by
  have valid : r.val<p.t.choose p.k := by rw [←ChainRankGate.t_eq]; exact r.isLt
  exact (Colex.digits_spec (Nat.le_refl p.t) valid).2.1 v (List.mem_reverse.mp hv)

private def listSlot {n k : Nat} (xs : List Nat) (hlen : xs.length=k) (bound : ∀ x∈xs, x<n)
    (order : xs.Pairwise (· < ·)) : Fin k ↪ Fin n where
  toFun j := ⟨xs[j.val]'(hlen.symm ▸ j.isLt),bound _ (List.getElem_mem _)⟩
  inj' a b eq := by
    apply Fin.ext
    have ha : a.val<xs.length := hlen.symm ▸ a.isLt
    have hb : b.val<xs.length := hlen.symm ▸ b.isLt
    apply (List.getElem?_inj ha order.nodup).mp
    simpa only [List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb,Option.some.injEq] using
      congrArg Fin.val eq

private theorem listSlot_ids {n k : Nat} (xs : List Nat) (hl : xs.length=k)
    (bound : ∀ x∈xs,x<n) (order : xs.Pairwise (· < ·)) :
    List.ofFn (fun j => (listSlot xs hl bound order j).val)=xs := by
  subst k
  exact List.ofFn_getElem

noncomputable def baseSlot (r : Fin ChainRankGate.C) : Fin 4 ↪ Fin p.t :=
  listSlot (ids r) (ids_len r) (id_bound r) (id_order r)

noncomputable def slot (h : H) (i : Fin p.K) := baseSlot (supportRank h i)

theorem slot_eq (h : H) (i : Fin p.K) : slot h i=baseSlot (supportRank h i) := rfl

theorem baseSlot_strict (r : Fin ChainRankGate.C) : StrictMono (baseSlot r) := by
  intro a b lt
  exact (List.pairwise_iff_getElem.mp (id_order r)) _ _ _ _ lt

theorem slot_ids (h : H) (i : Fin p.K) :
    List.ofFn (fun j => (slot h i j).val)=ids (supportRank h i) :=
  listSlot_ids (ids (supportRank h i)) (ids_len _) (id_bound _) (id_order _)

theorem slot_strict (h : H) (i : Fin p.K) : StrictMono (slot h i) :=
  baseSlot_strict _

theorem leaves_eq (z : Fin (scheme p).accepted.length) (i : Fin p.K) :
    (coord (scheme p).accepted[z] i.val).leaves=List.ofFn (fun j => (slot (accepted z).1 i j).val) := by
  rw [slot_ids]
  unfold ids
  rw [supportRank_eq]
  rfl

private theorem zip_ofFn {n : Nat} (a : Fin n → α) (b : Fin n → β) :
    (List.ofFn a).zip (List.ofFn b)=List.ofFn (fun j => (a j,b j)) := by
  apply List.ext_getElem <;> simp

theorem pairs_eq (z : Fin (scheme p).accepted.length) (i : Fin p.K) :
    pairs (scheme p).accepted[z] i.val=List.ofFn (fun j : Fin 4 =>
      ((slot (accepted z).1 i j).val,(ChainSupplier.rankTuple ((accepted z).2.2 i)).val j)) := by
  unfold pairs
  rw [leaves_eq,depthRank_eq,←zip_ofFn]
  exact congrArg _ (ChainSupplier.decoded (ChainRankGate.profileRank (scheme p).accepted[z] i.val))

theorem baseSlot_injective : Function.Injective baseSlot := by
  intro a b h
  have e : ids a=ids b := by
    have list (r : Fin ChainRankGate.C) : List.ofFn (fun j => (baseSlot r j).val)=ids r :=
      listSlot_ids (ids r) (ids_len r) (id_bound r) (id_order r)
    rw [←list a,←list b,h]
  have digits := congrArg List.reverse e
  simp only [ids,List.reverse_reverse] at digits
  have valid (r : Fin ChainRankGate.C) : r.val<p.t.choose p.k := by
    rw [←ChainRankGate.t_eq]; exact r.isLt
  exact Fin.ext (Colex.digits_injective (valid a) (valid b) digits)

/-- The four ordered embeddings identify the whole pruned support tuple. -/
theorem slots_injective : Function.Injective slot := by
  intro a b he
  apply Subtype.ext
  funext i
  exact (supportEquiv child p.k).symm.injective (baseSlot_injective (congrFun he i))

def requests {n k : Nat} (a : Fin k ↪ Fin n) (v : Fin k → Nat) : Finset (Fin n × Nat) :=
  Finset.univ.image fun j => (a j,v j)

private theorem request_mem {n k : Nat} {a : Fin k ↪ Fin n} {v : Fin k → Nat}
    {leaf : Fin n} {e : Nat} : (leaf,e)∈requests a v ↔ ∃ j,a j=leaf ∧ v j=e := by
  simp [requests,Prod.ext_iff]

private theorem sorted_list {n k : Nat} (a : Fin k ↪ Fin n) (ha : StrictMono a) :
    (List.ofFn (fun j => a j)).Pairwise (· < ·) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj h
  simp only [List.getElem_ofFn]
  exact ha h

/-- Recover the increasing list of leaves from the unordered requests.
Each leaf then identifies one residual and its unique slot. -/
theorem requests_unique {n k : Nat} {a b : Fin k ↪ Fin n} {v w : Fin k → Nat}
    (ha : StrictMono a) (hb : StrictMono b) (eq : requests a v=requests b w) : a=b ∧ v=w := by
  have forward (i : Fin k) : ∃ j,b j=a i ∧ w j=v i :=
    request_mem.mp (eq ▸ (request_mem.mpr ⟨i,rfl,rfl⟩ : (a i,v i)∈requests a v))
  have backward (i : Fin k) : ∃ j,a j=b i ∧ v j=w i :=
    request_mem.mp (eq.symm ▸ (request_mem.mpr ⟨i,rfl,rfl⟩ : (b i,w i)∈requests b w))
  have ls : List.ofFn (fun j => a j)=List.ofFn (fun j => b j) := by
    apply List.Pairwise.eq_of_mem_iff (sorted_list a ha) (sorted_list b hb)
    intro x
    simp only [List.mem_ofFn]
    constructor
    · rintro ⟨i,rfl⟩
      obtain ⟨j,h,_⟩ := forward i
      exact ⟨j,h⟩
    · rintro ⟨i,rfl⟩
      obtain ⟨j,h,_⟩ := backward i
      exact ⟨j,h⟩
  have same : a=b := by
    apply DFunLike.ext
    intro j
    have h := congrArg (fun xs : List (Fin n) => xs[j.val]?) ls
    simpa [j.isLt] using h
  subst b
  refine ⟨rfl,?_⟩
  funext i
  obtain ⟨j,hj,depth⟩ := forward i
  exact (a.injective hj ▸ depth).symm

theorem base_requests_injective : Function.Injective
    (fun t : Fin ChainRankGate.C × Fin ((35:Nat).choose 3) =>
      requests (baseSlot t.1) (ChainSupplier.rankTuple t.2).val) := by
  intro a b e
  obtain ⟨slots,depths⟩ := requests_unique (baseSlot_strict a.1) (baseSlot_strict b.1) e
  exact Prod.ext (baseSlot_injective slots) (ChainSupplier.rankTuple.injective (Subtype.ext depths))

/-- An accepted target is identified by its four buckets and the four
unordered sets of requested (leaf, residual) pairs. -/
theorem target_injective : Function.Injective (fun z : Fin (scheme p).accepted.length =>
    ((accepted z).2.1,fun i => requests (slot (accepted z).1 i)
      (ChainSupplier.rankTuple ((accepted z).2.2 i)).val)) := by
  intro x y eq
  have same (i : Fin p.K) := requests_unique (slot_strict (accepted x).1 i) (slot_strict (accepted y).1 i)
    (congrArg (fun z => z.2 i) eq)
  have buckets : (accepted x).2.1=(accepted y).2.1 :=
    congrArg (fun z : Buckets × (Fin p.K → Finset (Fin p.t × Nat)) => z.1) eq
  apply accepted.injective
  exact Prod.ext (slots_injective (funext fun i => (same i).1))
    (Prod.ext buckets (funext fun i =>
      ChainSupplier.rankTuple.injective (Subtype.ext (same i).2)))

end PoissonDAG.PORS.ChainLaw
