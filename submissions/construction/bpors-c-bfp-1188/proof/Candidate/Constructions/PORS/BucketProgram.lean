import Candidate.Constructions.PORS.MixedDecode
import Candidate.Constructions.PORS.SingleDecode
import Candidate.Constructions.PORS.BucketCoordGates
import Candidate.Constructions.PORS.LiteralReadout

namespace PoissonDAG.PORS.BucketProgram
open RankGates Literal LiteralMaskSemantics BucketRefined

abbrev child := shape p.t
abbrev outer := shape p.buckets

def coord (raw i : Nat) :=
  MixedDecode.coordinate p MixedDecode.bucketDepths (raw / (MixedDecode.radix p)^i)

def inner (c : MixedDecode.Coordinate) :=
  shapeView true (fun j => leafView (decide (j ∈ c.leaves))) child 0

def atBucket (c : MixedDecode.Coordinate) := BucketCoord.coordView outer (inner c) c.bucket
def view (raw : Nat) := joinView false (atBucket (coord raw 0)) (atBucket (coord raw 1))
def marks (raw : Nat) := (view raw).prefixMarks ++ [(view raw).root]
def acceptedBit (raw : Nat) := decide (raw < p.domain ∧ (view raw).count ≤ p.M)

def finish (row : Row) (valid : Nat) (a : Part) : Build (List Nat) := do
  let (_, past) ← addSub a.siblings (lit (width row) (row.M+1)) true
  let accept ← both valid (← neg past)
  return accept :: (a.marks.toList.map Prod.fst ++ a.marks.toList.map Prod.snd)

theorem finish_spec {raw gates valid a v} (row : Row) (seed : Seeded raw gates)
    (good : Prop) [Decidable good] (hv : HasBit raw gates valid (decide good))
    (ha : Represents raw gates (width row) a v) (fit : row.M+1 < 2^width row) :
    Builds raw gates (finish row valid a) (fun q out =>
      let ms := v.prefixMarks ++ [v.root]
      out.map (wireValue raw q) =
        decide (good ∧ v.count ≤ row.M) :: (ms.map Prod.fst ++ ms.map Prod.snd)) := by
  have hn : Holds raw gates (width row) a.siblings v.count :=
    ⟨ha.count.size, ha.count.valid, ha.count.value⟩
  have lim : Holds raw gates (width row) (lit (width row) (row.M+1)) (row.M+1) := by
    simpa only [Nat.mod_eq_of_lt fit] using holds_literal seed (width row) (row.M+1)
  unfold finish
  refine (holds_sub seed hn lim).bind fun q pair e cut => ?_
  refine (neg_bit (seed.mono e) cut.2).bind fun r ok f hOk => ?_
  have ef := e.trans f
  refine (both_bit (seed.mono ef) (hv.mono ef) hOk).bind fun t keep g hkeep => ?_
  apply builds_pure
  have he : wireValue raw t keep = decide (good ∧ v.count ≤ row.M) := by
    rw [hkeep.2]
    by_cases hg : good <;> by_cases hc : v.count ≤ row.M <;>
      simp [hg, hc, show (row.M+1 ≤ v.count) ↔ ¬v.count ≤ row.M by omega]
  have hm := (ha.mono (ef.trans g)).mark_values
  rw [List.map_cons, he, List.map_append, ← hm]
  simp [List.map_map, Function.comp_def]

private theorem build_pair (row : Row) (o c : Shape) :
    build row (.branch .leaf .leaf) o c = (do
    let (valid, ds) ← decode row
    let l ← atCoord row c o ds.toArray[0]!
    let r ← atCoord row c o ds.toArray[1]!
    let full ← merge false l r
    finish row valid full) := by
  simp [build, atShape, Shape.leaves, finish, bind_assoc]

private theorem forest_pair : shape p.K = .branch .leaf .leaf := rfl

private theorem related_two {R : α → β → Prop} {ds : List α} {u v : β}
    (h : List.Forall₂ R ds [u,v]) : ∃ x y, ds = [x,y] ∧ R x u ∧ R y v := by
  cases h with
  | cons hx htail =>
    cases htail with
    | cons hy rest =>
      cases rest
      exact ⟨_, _, rfl, hx, hy⟩

private theorem coord_spec {raw gs d} (seed : Seeded raw gs) (i : Nat)
    (h : MixedDecode.Represents raw gs (width p) d (coord raw i)) :
    Builds raw gs (atCoord p child outer d) (fun q a =>
      Represents raw q (width p) a (atBucket (coord raw i))) := by
  have len : (coord raw i).leaves.length = p.k := by
    simp [coord, MixedDecode.coordinate]
  have hd : List.Forall₂ (Holds raw gs (width p)) d.depths
      (List.replicate (coord raw i).leaves.length 0) := by rw [len]; exact h.depths
  exact BucketCoord.production_coord seed d _ _ (decoded_leafDigits h.leaves hd)
    ⟨h.bucket.size, h.bucket.valid, h.bucket.value_eq⟩

private theorem count_fit (raw : Nat) : (view raw).count < 2^width p := by
  have bound (i : Nat) : (atBucket (coord raw i)).count + 1 ≤ child.leaves :=
    child_count_le child (fun j => decide (j ∈ (coord raw i).leaves)) 0
  have hz := shape_card p.t (by decide)
  change child.leaves = p.t at hz
  have fit : p.t+p.t < 2^width p := by decide +kernel
  have h0 := bound 0
  have h1 := bound 1
  change (atBucket (coord raw 0)).count + (atBucket (coord raw 1)).count + 0 < _
  omega

private theorem source_of_build (row : Row) (raw : Nat) (bs : List Bool)
    (h : Builds raw #[.constant false,.constant true]
      (build row (shape row.K) (shape row.buckets) (shape row.t))
      (fun q out => out.map (wireValue raw q) = bs)) : sourceBits row raw = bs := h.2

private theorem graph_span (row : Row) :
    (scheme row).graph.length + 1 =
      (shape row.K).leaves * ((shape row.buckets).leaves * ((shape row.t).leaves*(row.cap+3))) :=
  graph_length (shape row.K) (shape row.buckets) (shape row.t) row.cap

set_option allowUnsafeReducibility true in
attribute [local irreducible] Literal.shape Literal.atCoord Literal.merge Literal.build RankGates.decode

theorem source_output (raw : Nat) (hr : raw < 2^p.r) :
    sourceBits p raw = acceptedBit raw :: ((marks raw).map Prod.fst ++ (marks raw).map Prod.snd) := by
  let start : Array Gate := #[.constant false, .constant true]
  have s : Seeded raw start := initial_seeded raw
  have cert : Builds raw start (build p (shape p.K) outer child) (fun q out =>
      out.map (wireValue raw q) = acceptedBit raw ::
        ((marks raw).map Prod.fst ++ (marks raw).map Prod.snd)) := by
    rw [forest_pair, build_pair]
    refine (MixedDecode.decode_bucket s hr).bind fun q pair e hp => ?_
    rcases pair with ⟨valid, coords⟩
    obtain ⟨hv, hs⟩ := hp
    have two : MixedDecode.coordinates p MixedDecode.bucketDepths p.K raw =
        [coord raw 0, coord raw 1] := by
      rw [show p.K=2 by rfl]
      simp [MixedDecode.coordinates, coord]
    rw [two] at hs
    obtain ⟨l, r, hcoords, hl, hr'⟩ := related_two hs
    change coords = [l,r] at hcoords
    subst coords
    dsimp only
    have se := s.mono e
    refine (coord_spec se 0 hl).bind fun q1 left f hleft => ?_
    refine (coord_spec (se.mono f) 1 (hr'.mono f)).bind fun q2 right g hright => ?_
    have fg := f.trans g
    refine (merge_spec (se.mono fg) (by decide +kernel) (hleft.mono g) hright false
      (count_fit raw)).bind fun q3 full z hfull => ?_
    exact finish_spec p (se.mono (fg.trans z)) (raw<p.domain) (hv.mono (fg.trans z)) hfull
      (by decide +kernel)
  exact source_of_build p raw _ cert

private theorem join_length (flag : Bool) (l r : View) :
    (joinView flag l r).prefixMarks.length+2 =
      (l.prefixMarks.length+2) + (r.prefixMarks.length+2) := by
  simp [joinView]
  omega

theorem shape_length (flag : Bool) (f : Nat → View) (unit : Nat)
    (hf : ∀ i, (f i).prefixMarks.length+2 = unit) (s : Shape) (off : Nat) :
    (shapeView flag f s off).prefixMarks.length + 2 = s.leaves * unit := by
  induction s generalizing off with
  | leaf => simpa [shapeView, Shape.leaves] using hf off
  | branch l r il ir =>
    simp only [shapeView, join_length, il, ir, Shape.leaves, Nat.add_mul]

private theorem atBucket_length (c : MixedDecode.Coordinate) :
    (atBucket c).prefixMarks.length + 2 = outer.leaves*(child.leaves*3) := by
  have hi : (inner c).prefixMarks.length+2 = child.leaves*3 :=
    shape_length true (fun j => leafView (decide (j ∈ c.leaves))) 3 (fun _ => rfl) child 0
  change (BucketCoord.outerView outer (inner c) c.bucket 0).prefixMarks.length + 2 = _
  unfold BucketCoord.outerView
  apply shape_length
  intro i
  simpa only [BucketCoord.gated, List.length_map] using hi

theorem marks_length (raw : Nat) : (marks raw).length = (scheme p).graph.length := by
  have g := graph_span p
  rw [forest_pair, show (Shape.branch .leaf .leaf).leaves = 2 by rfl,
    show p.cap+3 = 3 by rfl] at g
  change (scheme p).graph.length + 1 = 2*(outer.leaves*(child.leaves*3)) at g
  have span : (view raw).prefixMarks.length+2 = 2*(outer.leaves*(child.leaves*3)) := by
    simp only [view, join_length, atBucket_length]
    omega
  have len : (marks raw).length = (view raw).prefixMarks.length+1 := by simp [marks]
  omega

/-- The fields read by the protected judge equal the acceptance bit and the
two mark streams produced by this pair of coordinate views. -/
theorem protected_output (raw : Nat) (hr : raw < 2^p.r) :
    (scheme p).accept raw = acceptedBit raw ∧
    (scheme p).frontier raw = (marks raw).map Prod.fst ∧
    (scheme p).plan raw = (marks raw).map Prod.snd :=
  masks_of_source p raw hr _ _ (marks_length raw) (source_output raw hr)

end PoissonDAG.PORS.BucketProgram
