import Candidate.Constructions.PORS.SingleDecode
import Candidate.Constructions.PORS.LiteralMaskSemantics
import Candidate.Constructions.PORS.LiteralReadout

namespace PoissonDAG.PORS.SingleProgram
open RankGates Literal LiteralMaskSemantics SingleRefined

abbrev child := Literal.shape p.t
def leaves (raw : Nat) := (Colex.digits p.t p.k (raw%p.supports)).reverse
def hit (raw i : Nat) := decide (i ∈ leaves raw)
def view (raw : Nat) := shapeView true (fun i => leafView (hit raw i)) child 0
def marks (raw : Nat) := (view raw).prefixMarks ++ [(view raw).root]
def acceptedBit (raw : Nat) := decide (raw < p.supports ∧ (view raw).count ≤ p.M)

private def finish (row : Row) (valid : Nat) (a : Part) : Build (List Nat) := do
  let (_,past) ← addSub a.siblings (lit (width row) (row.M+1)) true
  let accept ← both valid (← neg past)
  return accept :: (a.marks.toList.map Prod.fst ++ a.marks.toList.map Prod.snd)

private theorem build_single : build p (shape p.K) (shape p.buckets) child = (do
    let (valid, ds) ← decode p
    let a ← atCoord p child .leaf ds.toArray[0]!
    finish p valid a) := by
  have hf : shape p.K = .leaf := rfl
  have hb : shape p.buckets = .leaf := rfl
  unfold build
  rw [hf,hb]
  rfl

private theorem finish_spec {raw valid a gates} (seed : Seeded raw gates)
    (hvalid : HasBit raw gates valid (decide (raw<p.supports)))
    (ha : Represents raw gates (width p) a (view raw)) :
    Builds raw gates (finish p valid a) (fun q out =>
      out.map (wireValue raw q) =
        acceptedBit raw :: ((marks raw).map Prod.fst ++ (marks raw).map Prod.snd)) := by
  have hword : Holds raw gates (width p) a.siblings (view raw).count :=
    ⟨ha.count.size,ha.count.valid,ha.count.value⟩
  have cap : p.M+1 < 2^(width p) := by rw [RankBounds.single_width.1]; decide
  have lim : Holds raw gates (width p) (lit (width p) (p.M+1)) (p.M+1) := by
    simpa only [Nat.mod_eq_of_lt cap] using holds_literal seed (width p) (p.M+1)
  unfold finish
  refine (holds_sub seed hword lim).bind fun q v e cut => ?_
  refine (neg_bit (seed.mono e) cut.2).bind fun q2 ok e2 hok => ?_
  have ef := e.trans e2
  refine (both_bit (seed.mono ef) (hvalid.mono ef) hok).bind fun q3 keep e3 hkeep => ?_
  apply builds_pure
  have value : wireValue raw q3 keep = acceptedBit raw := by
    rw [hkeep.2]
    by_cases a : raw < p.supports <;> by_cases b : (view raw).count ≤ p.M <;>
      simp [acceptedBit, a, b, show (p.M+1 ≤ (view raw).count) ↔ ¬((view raw).count ≤ p.M) by omega]
  have hm := (ha.mono (ef.trans e3)).mark_values
  change _ = marks raw at hm
  rw [List.map_cons, value, List.map_append, ← hm]
  simp [List.map_map, Function.comp_def]

private theorem output_of_build (row : Row) (raw : Nat) (bs : List Bool)
    (h : Builds raw #[.constant false,.constant true]
      (build row (shape row.K) (shape row.buckets) (shape row.t))
      (fun q out => out.map (wireValue raw q) = bs)) : sourceBits row raw = bs := h.2

/-- The output bits of the real gate generator on every raw input. -/
theorem source_output (raw : Nat) (hr : raw < 2^p.r) :
    sourceBits p raw =
      acceptedBit raw :: ((marks raw).map Prod.fst ++ (marks raw).map Prod.snd) := by
  let start : Array Gate := #[.constant false,.constant true]
  have initial : Seeded raw start := initial_seeded raw
  have hb : Builds raw start (build p (shape p.K) (shape p.buckets) child)
      (fun q out => out.map (wireValue raw q) =
        acceptedBit raw :: ((marks raw).map Prod.fst ++ (marks raw).map Prod.snd)) := by
    rw [build_single]
    refine (decode_single initial hr).bind fun q pair e h => ?_
    rcases pair with ⟨valid,coords⟩
    obtain ⟨d,ds,hv,bucket,digits⟩ := h.mask_inputs
    change coords = [d] at ds
    subst coords
    dsimp only
    refine (atCoord_single (initial.mono e) d (leaves raw) digits bucket).bind
      fun q' a e' ha => ?_
    exact finish_spec ((initial.mono e).mono e') (hv.mono e') ha
  exact output_of_build p raw _ hb

end PoissonDAG.PORS.SingleProgram
