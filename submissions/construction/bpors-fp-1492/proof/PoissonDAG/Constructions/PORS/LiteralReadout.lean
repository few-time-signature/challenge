import PoissonDAG.Constructions.PORS.Literal
import PoissonDAG.Constructions.PORS.WireSemantics

namespace PoissonDAG.PORS.Literal

theorem literal_inputs (p : Row) : (scheme p).encoder.inputs = p.r := rfl

/-- Source wire execution before the renderer inserts the false sentinel. -/
def sourceBits (p : Row) (raw : Nat) : List Bool :=
  let program := (build p (shape p.K) (shape p.buckets) (shape p.t)).run
    #[.constant false, .constant true]
  program.1.map (get (executeGates raw program.2.toList))

theorem eval_of_source (p : Row) (raw : Nat) (hr : raw < 2^p.r)
    (arity : (sourceBits p raw).length = 1+2*(scheme p).graph.length) :
    (scheme p).encoder.eval raw = sourceBits p raw := by
  let program := (build p (shape p.K) (shape p.buckets) (shape p.t)).run
    #[.constant false, .constant true]
  have hw : program.1.length = 1+2*(scheme p).graph.length := by
    simpa [sourceBits,program] using arity
  change (render p.r (1+2*(scheme p).graph.length) program.2 program.1).eval raw = _
  rw [← hw, render_eval_eq_source _ _ _ _ hr]
  rfl

/-- The actual protected fields follow from the source program's bit stream. -/
theorem masks_of_source (p : Row) (raw : Nat) (hr : raw < 2^p.r) (accept : Bool)
    (marks : List (Bool × Bool)) (hlen : marks.length = (scheme p).graph.length)
    (he : sourceBits p raw = accept :: (marks.map Prod.fst ++ marks.map Prod.snd)) :
    (scheme p).accept raw = accept ∧ (scheme p).frontier raw = marks.map Prod.fst ∧
      (scheme p).plan raw = marks.map Prod.snd := by
  have arity : (sourceBits p raw).length = 1+2*(scheme p).graph.length := by
    rw [he]; simp [hlen]; omega
  have hb := (eval_of_source p raw hr arity).trans he
  simp only [Scheme.accept, Scheme.frontier, Scheme.plan, hb]
  rw [← hlen]
  simp [get, Nat.add_comm 1, List.drop_succ_cons]

end PoissonDAG.PORS.Literal
