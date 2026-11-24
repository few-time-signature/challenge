import Candidate.Constructions.PORS.SingleProgram

namespace PoissonDAG.PORS.SingleCertificate
open Literal LiteralMaskSemantics SingleProgram SingleRefined PrunedCount

private theorem view_length (s : Shape) (f : Nat → Bool) (off : Nat) :
    (shapeView true (fun i => leafView (f i)) s off).prefixMarks.length + 1 =
      (s.fill (chain 1)).nodes := by
  induction s generalizing off with
  | leaf => rfl
  | branch l r il ir =>
    simp only [shapeView, joinView, List.length_append, List.length_singleton, Shape.fill,
      Tree.nodes, il, ir]

private theorem graph_eq (row : Row) : (scheme row).graph =
    graph (shape row.K) (shape row.buckets) (shape row.t) row.cap := rfl

private theorem graph_nodes (row : Row) (hf : shape row.K=.leaf) (hb : shape row.buckets=.leaf)
    (hc : row.cap=0) : (scheme row).graph.length = ((shape row.t).fill (chain 1)).nodes := by
  rw [graph_eq,hf,hb,hc]
  exact Tree.emit_length _ _

private theorem graph_length_single : single.graph.length = (child.fill (chain 1)).nodes :=
  graph_nodes p rfl rfl rfl

attribute [local irreducible] Literal.scheme Literal.shape

theorem fields (raw : Nat) (hr : raw < 2^p.r) :
    single.accept raw = acceptedBit raw ∧ single.frontier raw = (marks raw).map Prod.fst ∧
      single.plan raw = (marks raw).map Prod.snd := by
  have length : (marks raw).length = single.graph.length := by
    rw [graph_length_single]
    simpa only [marks,view,List.length_append,List.length_singleton] using view_length child (hit raw) 0
  exact masks_of_source p raw hr (acceptedBit raw) (marks raw) length (source_output raw hr)

end PoissonDAG.PORS.SingleCertificate
