import PoissonDAG.Constructions.PORS.SingleOpeningSources
import PoissonDAG.Constructions.PORS.ColexDigits
import PoissonDAG.Constructions.PORS.LiteralCosts
import Mathlib.Data.List.Sort

namespace PoissonDAG.PORS.SingleCover

private theorem row_inputs (row : Row) : (Literal.scheme row).encoder.inputs = row.r := rfl

/-- Specialize the graph and input-width laws symbolically before instantiating
the full fixed row. -/
theorem row_historicalCount (row : Row) (bits : row.r = SingleRefined.p.r)
    (count : (Literal.scheme row).accepted.length = SingleRefined.p.acceptedWords)
    (code : SourceCode (Literal.scheme row) 9) (q : Nat) :
    (Literal.scheme row).coverCoefficient q ≤ SingleRefined.p.rawEnvelope q :=
  historicalCount_of_shape (Literal.scheme row) (Literal.scheme_output_arity row)
    ((row_inputs row).trans bits) count code q

/-- Conditional coverage theorem for the literal 1,780-byte row. -/
def single_historicalCount := row_historicalCount SingleRefined.p rfl

end PoissonDAG.PORS.SingleCover

namespace PoissonDAG.PORS.SingleOpeningSources

open SingleRefined

abbrev singleShape := Literal.shape p.t

private theorem row_graph (row : Row) : (Literal.scheme row).graph =
    graph (Literal.shape row.K) (Literal.shape row.buckets) (Literal.shape row.t) row.cap := rfl

private theorem single_graph : Literal.single.graph = (block singleShape).emit 0 :=
  (row_graph p).trans (by rfl)

attribute [local irreducible] Literal.scheme Scheme.accepted

/-- With the colex decoder, the only circuit-side premises are validity of
the accepted rank and its source-frontier correspondence to the routed opening.
The sorting, cardinality, address translation and injectivity are derived. -/
theorem single_code_of_colex
    (valid : ∀ raw ∈ Literal.single.accepted, raw < p.t.choose 9)
    (routes : ∀ raw ∈ Literal.single.accepted, ∃ a : Opening (block singleShape),
      routedOpening .leaf .leaf singleShape 0 (fun _ => 0)
        (zeroDepth (Colex.digits p.t 9 raw).toFinset) = some a ∧
      Literal.single.frontier raw = a.marks.map Prod.fst) :
    SingleCover.SourceCode Literal.single 9 := by
  let support := fun raw => (Colex.digits p.t 9 raw).toFinset
  let finiteSupport := fun raw => selected singleShape (zeroDepth (support raw) 0)
  have values (raw : Nat) (hraw : raw ∈ Literal.single.accepted) :
      (finiteSupport raw).map Fin.valEmbedding = support raw := by
    apply selected_zeroDepth_values
    intro i hi
    rw [show singleShape.leaves = p.t from Literal.shape_card _ (by decide)]
    exact (Colex.digits_spec (Nat.le_refl _) (valid raw hraw)).2.1 i (List.mem_toFinset.mp hi)
  apply sourceCode_of_supports singleShape Literal.single 9 finiteSupport
  · intro raw hr
    obtain ⟨a, route, front⟩ := routes raw hr
    exact sources_eq_map singleShape Literal.single raw single_graph _ _ route front
  · intro raw hr
    have hsort := (Colex.digits_spec (Nat.le_refl _) (valid raw hr)).2.2
    calc
      _ = ((finiteSupport raw).map Fin.valEmbedding).card := (Finset.card_map _).symm
      _ = (support raw).card := by rw [values raw hr]
      _ = (Colex.digits p.t 9 raw).length := List.toFinset_card_of_nodup hsort.nodup
      _ = 9 := Colex.digits_length _ _ _
  · intro x hx y hy he
    have hu : support x = support y := by rw [← values x hx, ← values y hy, he]
    have sx := (Colex.digits_spec (Nat.le_refl _) (valid x hx)).2.2
    have sy := (Colex.digits_spec (Nat.le_refl _) (valid y hy)).2.2
    apply Colex.digits_injective (valid x hx) (valid y hy)
    apply sx.eq_of_mem_iff sy
    intro i
    simpa only [support, List.mem_toFinset] using (show i ∈ support x ↔ i ∈ support y by rw [hu])

end PoissonDAG.PORS.SingleOpeningSources
