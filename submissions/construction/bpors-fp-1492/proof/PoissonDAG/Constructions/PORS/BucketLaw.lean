import PoissonDAG.Constructions.PORS.BucketRankGate
import PoissonDAG.Constructions.PORS.BucketExperiment
import PoissonDAG.Constructions.PORS.BucketCode

namespace PoissonDAG.PORS.BucketLaw
open Literal BucketRefined BucketProgram PrunedCount
open ConfigurationRanks BucketExperiment

attribute [local irreducible] Literal.scheme Literal.shape Scheme.accepted
private theorem leaves_t : child.leaves=p.t := shape_card _ (by decide)
def addr : Leaf child ≃ Fin p.t := (leafIndex child).trans (finCongr leaves_t)

abbrev H := {u : Fin p.K → Choices child p.k // AcceptedProducts.keep child p.k p.K p.M u}

noncomputable def accepted : Fin (scheme p).accepted.length ≃ H × BucketTags :=
  (AcceptedProducts.equiv BucketRankGate.gate BucketRankGate.fits).trans
    ((Equiv.refl H).prodCongr (Equiv.piCongrRight (fun _ => BucketCode.aux p.buckets)))

def supports : H ↪ Full := BucketCode.fullSupport addr

private theorem row_base : BucketRankGate.base = RankGates.MixedDecode.radix p := by
  simp only [BucketRankGate.base,BucketRankGate.C,leaves_t,Nat.choose_eq_fast_choose,
    Row.supports,RankGates.MixedDecode.radix]
  ac_rfl

private theorem tag_val (r : Fin BucketRankGate.domain) (i : Fin p.K) :
    (BucketCode.aux p.buckets ((BucketRankGate.ranks r).2 i)).val =
      (coord r.val i.val).bucket := by
  have note := BucketCode.tag child p.k p.buckets p.K (Nat.two_pow_pos _)
    (by rw [leaves_t]; exact Nat.choose_pos (by decide)) r i
  change _ = r.val / BucketRankGate.base^i.val / 1 / BucketRankGate.C % p.buckets at note
  change _ = r.val / (RankGates.MixedDecode.radix p)^i.val / p.depthCount / p.supports % p.buckets
  have card : BucketRankGate.C = p.supports := by
    change child.leaves.choose p.k = _
    rw [leaves_t,Nat.choose_eq_fast_choose]; rfl
  apply note.trans
  exact congrArg₂ (fun a b : Nat => r.val / a^i.val / 1 / b % p.buckets) row_base card

private noncomputable abbrev rawRank := AcceptedProducts.rank BucketRankGate.gate BucketRankGate.fits

theorem owner (i : Fin (scheme p).accepted.length) (c : Fin p.K) :
    ((accepted i).2 c).val = (coord (scheme p).accepted[i] c.val).bucket := by
  let eqt := AcceptedProducts.tags_eq BucketRankGate.gate BucketRankGate.fits i
  exact (congrArg (fun z => (BucketCode.aux p.buckets (z c)).val) eqt).trans (tag_val (rawRank i) c)

theorem selected (i : Fin (scheme p).accepted.length) (c : Fin p.K) (x : Leaf child) :
    addr x ∈ (supports (accepted i).1 c).val ↔
    decide ((leafIndex child x).val ∈ (coord (scheme p).accepted[i] c.val).leaves) = true := by
  let e := AcceptedProducts.support_eq BucketRankGate.gate BucketRankGate.fits i
  have eqs := (congrArg (fun z => (z c).val) e).trans (BucketRankGate.digit (rawRank i) c)
  change addr.toEmbedding x ∈ ((AcceptedProducts.equiv BucketRankGate.gate BucketRankGate.fits i).1.val c).val.map addr.toEmbedding ↔ _
  rw [Finset.mem_map',eqs]
  exact (BucketRankGate.agrees _ _ x).symm

private theorem total_card (t k B K : Nat) :
    Fintype.card ((Fin K → BucketAverage.Choices t k) × (Fin K → Fin B)) =
      (B * Nat.fast_choose t k)^K := by
  simp only [BucketAverage.Choices,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ,Nat.choose_eq_fast_choose,mul_pow]
  exact Nat.mul_comm _ _

theorem domain_card : Fintype.card (Full × BucketTags) = p.domain := by
  rw [total_card]
  unfold Row.domain
  rw [show p.depthCount=1 by rfl,Nat.mul_one]
  rfl

end PoissonDAG.PORS.BucketLaw
