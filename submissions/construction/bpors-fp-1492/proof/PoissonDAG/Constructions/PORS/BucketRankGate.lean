import PoissonDAG.Constructions.PORS.AcceptedProducts
import PoissonDAG.Constructions.PORS.BucketProgram

namespace PoissonDAG.PORS.BucketRankGate
open Literal LiteralMaskSemantics BucketProgram BucketRefined ConfigurationRanks
open PrunedCount RankGates

attribute [local irreducible] Literal.shape Literal.scheme Scheme.accepted
set_option maxHeartbeats 40000

abbrev C := child.leaves.choose p.k
abbrev base := (p.buckets * C) * p.depthCount
abbrev domain := base^p.K
noncomputable abbrev ranks := allRanks child p.k p.buckets p.depthCount p.K

private theorem t_eq : child.leaves=p.t := shape_card _ (by decide +kernel)
private theorem c_eq : C = p.supports := by
  change child.leaves.choose p.k = p.supports
  rw [t_eq,Nat.choose_eq_fast_choose]; rfl
private theorem base_eq : base = MixedDecode.radix p := by
  change (p.buckets*C)*p.depthCount=_
  rw [c_eq]; unfold MixedDecode.radix; ac_rfl
private theorem domain_eq : domain=p.domain := by
  simp only [domain,base,c_eq,Row.domain]

private theorem colex_agrees (s : Shape) (t k rank : Nat) (ht : s.leaves=t) (x : Leaf s) :
    decide ((leafIndex s x).val ∈ (Colex.digits t k rank).reverse) = true ↔
      x ∈ SingleAccepted.leafSupport s k rank := by
  simp only [decide_eq_true_eq,List.mem_reverse,SingleAccepted.leafSupport,Finset.mem_filter,
    Finset.mem_univ,true_and,Colex.support,List.mem_toFinset,ht]
  rfl

def supportRank (raw i : Nat) :=
  (raw / (MixedDecode.radix p)^i / p.depthCount) % p.supports

theorem agrees (raw i : Nat) (x : Leaf child) :
    decide ((leafIndex child x).val ∈ (coord raw i).leaves) = true ↔
      x ∈ SingleAccepted.leafSupport child p.k (supportRank raw i) :=
  colex_agrees child p.t p.k _ t_eq x

theorem inner_count (raw i : Nat) :
    (inner (coord raw i)).count = siblings child (SingleAccepted.leafSupport child p.k (supportRank raw i)) :=
  (child_support child 0 _ _ (fun x => by simpa only [Nat.zero_add] using agrees raw i x)).2

theorem digit (raw : Fin domain) (i : Fin p.K) :
    ((ranks raw).1 i).val = SingleAccepted.leafSupport child p.k (supportRank raw i) := by
  apply (digit_support child p.k p.buckets p.depthCount p.K raw i).trans
  apply congrArg (SingleAccepted.leafSupport child p.k)
  change ((raw.val / base ^ i.val % base) / p.depthCount) % C = _
  simp only [supportRank,show p.depthCount=1 by rfl,Nat.div_one,base_eq,c_eq]
  apply Nat.mod_mod_of_dvd
  unfold MixedDecode.radix
  exact dvd_mul_of_dvd_left (dvd_mul_left p.supports p.depthCount) _

private theorem two_sum (f : Nat → Nat) :
    (∑ i : Fin p.K, f i.val) = f 0 + f 1 := by
  change (∑ i : Fin 2, f i.val) = _
  simp [Fin.sum_univ_succ]

theorem cost_eq (r : Fin domain) :
    (view r.val).count = ∑ i, siblings child (((ranks r).1 i).val) := by
  simp_rw [digit]
  rw [two_sum (fun i => siblings child (SingleAccepted.leafSupport child p.k (supportRank r.val i)))]
  change (inner (coord r.val 0)).count + (inner (coord r.val 1)).count + 0 = _
  rw [Nat.add_zero,inner_count,inner_count]

theorem gate : AcceptedProducts.Gate (scheme p) ranks (AcceptedProducts.keep child p.k p.K p.M) := by
  intro raw hr
  have bits := literal_inputs p
  rw [bits] at hr
  rw [(protected_output raw hr).1]
  change decide (raw<p.domain ∧ (view raw).count≤p.M) = true ↔ _
  rw [decide_eq_true_eq,←domain_eq]
  constructor
  · rintro ⟨h,cut⟩
    refine ⟨h,?_⟩
    unfold AcceptedProducts.keep
    rw [← cost_eq]
    exact cut
  · rintro ⟨h,cut⟩
    unfold AcceptedProducts.keep at cut
    rw [← cost_eq] at cut
    exact ⟨h,cut⟩

theorem fits : domain ≤ 2^(scheme p).encoder.inputs := by
  rw [domain_eq,literal_inputs]; decide +kernel

private theorem row_count (sc : Scheme) (s : Shape) (row : Row)
    (h : AcceptedProducts.Gate sc (allRanks s row.k row.buckets row.depthCount row.K)
      (AcceptedProducts.keep s row.k row.K row.M))
    (room : ((row.buckets*s.leaves.choose row.k)*row.depthCount)^row.K ≤ 2^sc.encoder.inputs)
    (exactCount : (CoordinatePruning.configurations s row).card = row.acceptedWords) :
    sc.accepted.length = row.acceptedWords := by
  apply (AcceptedProducts.length s row.k row.K row.M row.buckets row.depthCount h room).trans
  simpa only [CoordinatePruning.configurations,Finset.card_product,Finset.card_univ,
    Fintype.card_fun,Fintype.card_fin] using exactCount

theorem accepted_count : (scheme p).accepted.length = p.acceptedWords :=
  row_count (scheme p) child p gate fits CoordinatePruning.bucket_configurations

end PoissonDAG.PORS.BucketRankGate
