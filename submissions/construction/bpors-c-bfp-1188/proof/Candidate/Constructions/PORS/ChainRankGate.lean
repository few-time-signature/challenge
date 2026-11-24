import Candidate.Constructions.PORS.ChainProgram
import Candidate.Constructions.PORS.AcceptedProducts
import Candidate.Constructions.PORS.BucketCode

namespace PoissonDAG.PORS.ChainRankGate
open Literal LiteralMaskSemantics ChainProgram ChainRefined ConfigurationRanks PrunedCount RankGates

attribute [local irreducible] Literal.shape Literal.scheme Scheme.accepted
set_option maxRecDepth 4096

abbrev C := child.leaves.choose p.k
abbrev base := (p.buckets*C)*p.depthCount
abbrev domain := ((p.buckets * child.leaves.choose p.k) * p.depthCount)^p.K
attribute [local irreducible] ChainRefined.p in
noncomputable def ranks : Fin domain ≃
    (Fin p.K → Choices child p.k) × (Fin p.K → Fin (p.buckets*p.depthCount)) :=
  allRanks child p.k p.buckets p.depthCount p.K

theorem t_eq : child.leaves=p.t := shape_card _ (by decide)
theorem c_eq : C=p.supports := by
  change child.leaves.choose p.k=p.supports
  rw [t_eq,Nat.choose_eq_fast_choose]; rfl
theorem base_eq : base=MixedDecode.radix p := by
  change (p.buckets*C)*p.depthCount=_
  rw [c_eq]; unfold MixedDecode.radix; ac_rfl
attribute [local irreducible] ChainRefined.p in
theorem domain_eq : domain=p.domain :=
  congrArg (fun n : Nat => ((p.buckets*n)*p.depthCount)^p.K) c_eq

def supportRank (raw i : Nat) := (raw/(MixedDecode.radix p)^i/p.depthCount)%p.supports
def depthRank (raw i : Nat) := (raw/(MixedDecode.radix p)^i)%p.depthCount

def profileRank (raw i : Nat) : Fin ((35 : Nat).choose 3) :=
  ⟨depthRank raw i,by
    rw [show (35 : Nat).choose 3=p.depthCount by decide +kernel]
    exact Nat.mod_lt _ (by decide +kernel : 0<p.depthCount)⟩

def profile (raw i : Nat) := ChainDepths.profileOfRank 32 (profileRank raw i)

theorem depths_exact (raw i : Nat) : (coord raw i).depths =
    [(profile raw i).a,(profile raw i).b,(profile raw i).c,(profile raw i).d] :=
  DepthGaps.chainValues_eq_profile (profileRank raw i)

theorem support_fit (raw i : Nat) : supportRank raw i < p.t.choose p.k := by
  rw [Nat.choose_eq_fast_choose]
  exact Nat.mod_lt _ (by decide +kernel : 0<p.supports)

private theorem lengths (raw i : Nat) : (coord raw i).leaves.length=(coord raw i).depths.length := by
  rw [depths_exact]
  change (Colex.digits p.t p.k (supportRank raw i)).reverse.length=4
  rw [List.length_reverse,Colex.digits_length]
  rfl

theorem leaf_ids (raw i : Nat) : (pairs raw i).map Prod.fst=(coord raw i).leaves :=
  List.map_fst_zip (lengths raw i).le

theorem residuals (raw i : Nat) : (pairs raw i).map Prod.snd=(coord raw i).depths :=
  List.map_snd_zip (lengths raw i).symm.le

theorem distinct (raw i : Nat) : ((pairs raw i).map Prod.fst).Nodup := by
  rw [leaf_ids]
  change (Colex.digits p.t p.k (supportRank raw i)).reverse.Nodup
  exact ((Colex.digits_spec (Nat.le_refl p.t) (support_fit raw i)).2.2.nodup).reverse.imp
    (fun h => Ne.symm h)

theorem total_depth (raw i : Nat) : ((pairs raw i).map Prod.snd).sum=p.E := by
  rw [residuals,depths_exact]
  have h := (profile raw i).total
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
  change _=32
  omega

theorem depth_bound (raw i j e : Nat) (h : (j,e)∈pairs raw i) : e ≤ p.cap := by
  have he : e∈(coord raw i).depths := (List.of_mem_zip h).2
  rw [depths_exact] at he
  have total := (profile raw i).total
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  change e≤32
  omega

noncomputable def support (raw i : Nat) : Finset (Leaf child) :=
  SingleAccepted.leafSupport child p.k (supportRank raw i)

private theorem colex_agrees (s : Shape) (t k r : Nat) (ht : s.leaves=t) (x : Leaf s) :
    (leafIndex s x).val ∈ (Colex.digits t k r).reverse ↔ x∈SingleAccepted.leafSupport s k r := by
  simp only [List.mem_reverse,SingleAccepted.leafSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    Colex.support,List.mem_toFinset,ht]
  rfl

theorem live_iff (xs : List (Nat×Nat)) (n : Nat) :
    ChainLeafGates.live xs n=true ↔ n∈xs.map Prod.fst := by
  simp [ChainLeafGates.live,List.mem_map]

theorem agrees (raw i : Nat) (x : Leaf child) :
    ChainLeafGates.live (pairs raw i) (leafIndex child x).val=true ↔ x∈support raw i := by
  rw [live_iff,leaf_ids]
  exact colex_agrees child p.t p.k (supportRank raw i) t_eq x

private theorem weight_of_rank (s : Shape) (k r : Nat) (valid : r<s.leaves.choose k) :
    (SingleAccepted.leafSupport s k r).card=k := by
  have h := (Finset.mem_powersetCard.mp (Colex.support_mem valid)).2
  rwa [← SingleAccepted.address_image s k r valid,Finset.card_map] at h

theorem support_weight (raw i : Nat) : (support raw i).card=p.k := by
  apply weight_of_rank
  rw [t_eq]
  exact support_fit raw i

theorem inner_count (raw i : Nat) : (atCoordView raw i).count=siblings child (support raw i) :=
  (ChainCoord.inner_support p.cap (pairs raw i) child 0 (support raw i)
    (fun x => by simpa only [Nat.zero_add] using agrees raw i x)).2

attribute [local irreducible] ChainRefined.p in
theorem digit (r : Fin domain) (i : Fin p.K) : ((ranks r).1 i).val=support r.val i.val := by
  apply (digit_support child p.k p.buckets p.depthCount p.K r i).trans
  apply congrArg (SingleAccepted.leafSupport child p.k)
  change ((r.val/base^i.val % ((p.buckets*C)*p.depthCount))/p.depthCount)%C=_
  rw [Nat.mod_mul_left_div_self,Nat.mod_mul_left_mod,base_eq,c_eq]
  rfl

private theorem depth_tag (s : Shape) (k B D K : Nat)
    (r : Fin (((B*s.leaves.choose k)*D)^K)) (i : Fin K) :
    ((finProdFinEquiv (m:=B) (n:=D)).symm ((allRanks s k B D K r).2 i)).2.val =
      (r.val / ((B*s.leaves.choose k)*D)^i.val % ((B*s.leaves.choose k)*D)) % D := by
  let S := s.leaves.choose k
  let y : Fin ((B*S)*D) := finFunctionFinEquiv.symm r i
  let z : Fin (B*S) × Fin D := finProdFinEquiv.symm y
  let step : Fin B × Fin S := finProdFinEquiv.symm z.1
  change ((finProdFinEquiv (m:=B) (n:=D)).symm (finProdFinEquiv (step.1,z.2))).2.val = _
  rw [Equiv.symm_apply_apply]
  rfl

attribute [local irreducible] ChainRefined.p in
theorem tag_owner (r : Fin domain) (i : Fin p.K) :
    ((finProdFinEquiv (m:=p.buckets) (n:=p.depthCount)).symm ((ranks r).2 i)).1.val =
      (coord r.val i.val).bucket := by
  apply (BucketCode.coord_tag child p.k p.buckets p.depthCount p.K r i).trans
  change (r.val/base^i.val % ((p.buckets*C)*p.depthCount))/p.depthCount/C = _
  rw [Nat.mod_mul_left_div_self,Nat.mod_mul_left_div_self,base_eq,c_eq]
  rfl

attribute [local irreducible] ChainRefined.p in
theorem tag_depth (r : Fin domain) (i : Fin p.K) :
    ((finProdFinEquiv (m:=p.buckets) (n:=p.depthCount)).symm ((ranks r).2 i)).2.val =
      depthRank r.val i.val := by
  apply (depth_tag child p.k p.buckets p.depthCount p.K r i).trans
  change (r.val/base^i.val % ((p.buckets*C)*p.depthCount))%p.depthCount = _
  rw [Nat.mod_mul_left_mod,base_eq]
  rfl

private theorem forest_four :
    forest = .branch (.branch .leaf .leaf) (.branch .leaf .leaf) := by
  unfold forest Literal.shape
  rfl

private theorem four_sum (f : Nat → Nat) :
    (∑ i : Fin p.K, f i.val) = (f 0+f 1)+(f 2+f 3) := by
  change (∑ i : Fin 4, f i.val)=_
  simp [Fin.sum_univ_succ,Nat.add_assoc]

theorem view_count (raw : Nat) :
    (view raw).count = ∑ i : Fin p.K, siblings child (support raw i.val) := by
  rw [four_sum (fun i => siblings child (support raw i))]
  unfold view
  rw [forest_four]
  change ((atCoordView raw 0).count+(atCoordView raw 1).count+0)+
    ((atCoordView raw 2).count+(atCoordView raw 3).count+0)+0=_
  simp only [inner_count,Nat.add_zero]

attribute [local irreducible] ChainRefined.p in
theorem cost_eq (r : Fin domain) : (view r.val).count = ∑ i, siblings child (((ranks r).1 i).val) := by
  simp_rw [digit]
  exact view_count r.val

attribute [local irreducible] ChainRefined.p in
theorem gate : AcceptedProducts.Gate (scheme p) ranks (AcceptedProducts.keep child p.k p.K p.M) := by
  intro raw hr
  rw [literal_inputs] at hr
  rw [(protected_output raw hr).1]
  change decide (raw<p.domain ∧ (view raw).count≤p.M)=true ↔ _
  rw [decide_eq_true_eq,←domain_eq]
  constructor
  · rintro ⟨h,cut⟩
    refine ⟨h,?_⟩
    unfold AcceptedProducts.keep
    rw [←cost_eq]; exact cut
  · rintro ⟨h,cut⟩
    unfold AcceptedProducts.keep at cut
    rw [←cost_eq] at cut
    exact ⟨h,cut⟩

theorem fits_domain : domain ≤ 2^(scheme p).encoder.inputs := by
  rw [domain_eq,literal_inputs]; decide +kernel

private theorem row_count (sc : Scheme) (s : Shape) (row : Row)
    (h : AcceptedProducts.Gate sc (allRanks s row.k row.buckets row.depthCount row.K)
      (AcceptedProducts.keep s row.k row.K row.M))
    (room : ((row.buckets*s.leaves.choose row.k)*row.depthCount)^row.K ≤ 2^sc.encoder.inputs)
    (exactCount : (CoordinatePruning.configurations s row).card = row.acceptedWords) :
    sc.accepted.length=row.acceptedWords := by
  apply (AcceptedProducts.length s row.k row.K row.M row.buckets row.depthCount h room).trans
  simpa only [CoordinatePruning.configurations,Finset.card_product,Finset.card_univ,
    Fintype.card_fun,Fintype.card_fin] using exactCount

attribute [local irreducible] ChainRefined.p in
theorem accepted_count : (scheme p).accepted.length=p.acceptedWords :=
  row_count (scheme p) child p gate fits_domain CoordinatePruning.chain_configurations

end PoissonDAG.PORS.ChainRankGate
