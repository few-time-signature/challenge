import Candidate.Constructions.PORS.ChainBarrier
import Candidate.Constructions.PORS.ChainRoutes
import Candidate.Constructions.PORS.ChainLaw

section

namespace PoissonDAG.PORS.ChainHistorical

open Literal ChainProgram ChainRefined

private theorem graph_of (row : Row) : (scheme row).graph =
    graph (shape row.K) (shape row.buckets) (shape row.t) row.cap := rfl

attribute [local irreducible] Literal.scheme Literal.shape Scheme.accepted

/-- In the literal production experiment, every selected target pair has a
same-bucket historical pair at the same leaf and at least its residual depth. -/
theorem supplier {q : Nat} (h : Fin q → Fin (scheme p).accepted.length)
    (t : Fin (scheme p).accepted.length)
    (covered : (scheme p).covered (indexHistory (scheme p).accepted h) (scheme p).accepted[t]=true)
    (i : Fin p.K) (j : Fin child.leaves) (e : Nat)
    (target : (j.val,e)∈pairs (scheme p).accepted[t] i.val) :
    ∃ z : Fin q, ChainRoutes.owner (scheme p).accepted[h z] i.val=ChainRoutes.owner (scheme p).accepted[t] i.val ∧
      ∃ k, (j.val,k)∈pairs (scheme p).accepted[h z] i.val ∧ e ≤ k := by
  have hi : i.val<forest.leaves := by rw [shape_card _ (by decide)]; exact i.isLt
  have hb : ChainRoutes.owner (scheme p).accepted[t] i.val<outer.leaves := by
    rw [shape_card _ (by decide)]
    exact ChainRoutes.owner_bound _ _
  have chosen := (ChainCoord.lookup_mem _ (ChainRankGate.distinct _ _) j.val e).mpr target
  obtain ⟨z,b,k,hk,le⟩ := ChainPositions.supplier (scheme p) forest outer child p.cap ChainRoutes.owner
    ChainRoutes.depth (graph_of p) (scheme_output_arity p)
    (fun _ hx => by
      obtain ⟨a,rt,front,_⟩ := ChainRoutes.traversal hx
      exact ⟨a,rt,front⟩) h t i.val j.val e hi j.isLt hb chosen (ChainRankGate.depth_bound _ _ _ _ target) covered
  exact ⟨z,b,k,(ChainCoord.lookup_mem _ (ChainRankGate.distinct _ _) _ _).mp hk,le⟩

end PoissonDAG.PORS.ChainHistorical
end

section

namespace PoissonDAG.PORS.ChainHistorical

open Literal ChainRefined ChainProgram ChainLaw

attribute [local irreducible] Literal.scheme Literal.shape Scheme.accepted

/-- Each selected target slot of a covered word has a historical slot with
the same coordinate bucket and leaf, and at least its requested residual. -/
theorem covered_slot {q : Nat} (history : Fin q → Fin (scheme p).accepted.length)
    (target : Fin (scheme p).accepted.length)
    (hc : (scheme p).covered (indexHistory (scheme p).accepted history) (scheme p).accepted[target]=true)
    (i : Fin p.K) (j : Fin 4) :
    ∃ (z : Fin q) (l : Fin 4),
      (accepted (history z)).2.1 i=(accepted target).2.1 i ∧
      slot (accepted (history z)).1 i l=slot (accepted target).1 i j ∧
      (ChainSupplier.rankTuple ((accepted target).2.2 i)).val j ≤
        (ChainSupplier.rankTuple ((accepted (history z)).2.2 i)).val l := by
  let leaf := slot (accepted target).1 i j
  let e := (ChainSupplier.rankTuple ((accepted target).2.2 i)).val j
  have hm : (leaf.val,e)∈pairs (scheme p).accepted[target] i.val := by
    rw [pairs_eq]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  let loc : Fin child.leaves := ⟨leaf.val,by rw [ChainRankGate.t_eq]; exact leaf.isLt⟩
  obtain ⟨z,bk,k,hk,le⟩ := supplier history target hc i loc e hm
  rw [pairs_eq] at hk
  obtain ⟨l,hpair⟩ := List.mem_ofFn.mp hk
  have pos := congrArg Prod.fst hpair
  have dep := congrArg Prod.snd hpair
  change (slot (accepted (history z)).1 i l).val=leaf.val at pos
  change (ChainSupplier.rankTuple ((accepted (history z)).2.2 i)).val l=k at dep
  refine ⟨z,l,Fin.ext ((ChainLaw.owner _ _).trans (bk.trans (ChainLaw.owner _ _).symm)),Fin.ext pos,?_⟩
  rw [dep]
  exact le

end PoissonDAG.PORS.ChainHistorical
end
