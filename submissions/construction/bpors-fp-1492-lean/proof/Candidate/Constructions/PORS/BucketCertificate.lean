import Candidate.Constructions.PORS.BucketRoutes
import Candidate.Constructions.PORS.BucketSource
import Candidate.Constructions.PORS.BucketLaw

namespace PoissonDAG.PORS.BucketCertificate
open Literal LiteralMaskSemantics BucketRefined BucketProgram PrunedCount
open BucketExperiment UniformMatching

private theorem graph_of (row : Row) : (scheme row).graph =
    graph (shape row.K) (shape row.buckets) (shape row.t) row.cap := rfl

attribute [local irreducible] Literal.scheme Literal.shape Scheme.accepted Scheme.coverCoefficient

private theorem depth_iff (raw i j : Nat) :
    (BucketRoutes.depth raw i j).isSome = true ↔ BucketRoutes.hit raw i j=true := by
  unfold BucketRoutes.depth asDepth
  cases h : BucketRoutes.hit raw i j <;> decide

private theorem supplies {q : Nat} (h : Hist (scheme p) q) (t : Fin (scheme p).accepted.length)
    (covered : (scheme p).covered (indexHistory (scheme p).accepted h) (scheme p).accepted[t]=true)
    (i : Fin p.K) :
    (BucketLaw.supports (BucketLaw.accepted t).1 i).val ⊆
      BucketAverage.supplyPool (fun j => (BucketLaw.supports (BucketLaw.accepted (h j)).1 i).val)
        ((BucketLaw.accepted t).2 i,fun j => (BucketLaw.accepted (h j)).2 i) := by
  intro leaf selected
  let x := BucketLaw.addr.symm leaf
  have addrEq : BucketLaw.addr x = leaf := BucketLaw.addr.apply_symm_apply _
  have target : BucketRoutes.hit (scheme p).accepted[t] i (leafIndex child x).val=true :=
    (BucketLaw.selected t i x).mp (addrEq.symm ▸ selected)
  have hi : i.val < (shape p.K).leaves := by rw [shape_card _ (by decide)]; exact i.isLt
  have hb : BucketRoutes.owner (scheme p).accepted[t] i < outer.leaves := by
    rw [shape_card _ (by decide)]; exact BucketRoutes.owner_bound _ _
  obtain ⟨j,owner,hit⟩ := BucketSource.supplier (scheme p) (shape p.K) outer child
    BucketRoutes.owner BucketRoutes.depth (graph_of p) (scheme_output_arity p)
    (fun _ hx => by
      obtain ⟨a,ha,hf,_⟩ := BucketRoutes.traversal hx
      exact ⟨a,ha,hf⟩) h t i _ hi (leafIndex child x).isLt hb ((depth_iff ..).mpr target) covered
  apply Finset.mem_biUnion.mpr
  refine ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
  · exact Fin.ext ((BucketLaw.owner _ i).trans (owner.trans (BucketLaw.owner _ i).symm))
  · rw [← addrEq]
    exact (BucketLaw.selected _ i x).mpr ((depth_iff ..).mp hit)

private theorem major (q : Nat) (h : Hist (scheme p) q) (t : Fin (scheme p).accepted.length) :
    (if (scheme p).covered (indexHistory (scheme p).accepted h) (scheme p).accepted[t]
      then (1:ℚ) else 0) ≤ bound q (fun j => BucketLaw.supports (BucketLaw.accepted (h j)).1)
        (fun j => (BucketLaw.accepted (h j)).2)
        (BucketLaw.supports (BucketLaw.accepted t).1,(BucketLaw.accepted t).2) := by
  split
  next hc =>
    have all (i : Fin p.K) := supplies h t hc i
    simp only [bound,BucketAverage.hitColumn,if_pos (all _),Finset.prod_const_one,le_refl]
  next =>
    apply Finset.prod_nonneg
    intro i _
    unfold BucketAverage.hitColumn; split <;> norm_num

theorem historical (q : Nat) : (scheme p).coverCoefficient q ≤ p.rawEnvelope q := by
  classical
  letI : Fintype BucketLaw.H := Fintype.ofFinite _
  have pos : 0 < (scheme p).accepted.length := by rw [BucketRankGate.accepted_count]; decide +kernel
  letI : Nonempty BucketLaw.H := ⟨(BucketLaw.accepted ⟨0,pos⟩).1⟩
  apply le_min
  · have cap := SingleCover.coefficient_of_count (scheme p) q ((scheme p).accepted.length:ℚ) pos
      (fun h => by
        have hh := Finset.card_le_univ (SingleCover.hits (scheme p) (indexHistory (scheme p).accepted h))
        exact_mod_cast (by simpa only [Fintype.card_fin] using hh :
          (SingleCover.hits (scheme p) (indexHistory (scheme p).accepted h)).card ≤ (scheme p).accepted.length))
    rw [BucketRankGate.accepted_count,literal_inputs] at cap
    exact cap
  · have hh := coverage (scheme p) q pos BucketLaw.accepted BucketLaw.supports (major q)
    rw [BucketLaw.domain_card,literal_inputs] at hh
    exact hh

theorem certificate : V2.ConstructionCertificate bucket 1492 := by
  apply bucket_conditional
  exact { count := BucketRankGate.accepted_count
          work := fun _ h => (BucketRoutes.resources h).2
          labels := fun _ h => (BucketRoutes.resources h).1
          traversal := fun raw h => ⟨BucketRoutes.owner raw,BucketRoutes.depth raw,BucketRoutes.traversal h⟩
          historicalCount := historical }

#print axioms certificate

end PoissonDAG.PORS.BucketCertificate
