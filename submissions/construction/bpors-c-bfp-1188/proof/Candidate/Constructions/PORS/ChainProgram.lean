import Candidate.Constructions.PORS.ChainCoordGates
import Candidate.Constructions.PORS.BucketProgram

namespace PoissonDAG.PORS.ChainProgram
open Literal LiteralMaskSemantics RankGates ChainRefined

abbrev child := shape p.t
abbrev outer := shape p.buckets
abbrev forest := shape p.K

def coord (raw i : Nat) :=
  MixedDecode.coordinate p DepthGaps.chainValues (raw / (MixedDecode.radix p)^i)

def pairs (raw i : Nat) := (coord raw i).leaves.zip (coord raw i).depths

def atCoordView (raw i : Nat) :=
  BucketCoord.coordView outer (ChainCoord.inner p.cap (pairs raw i) child 0) (coord raw i).bucket

def view (raw : Nat) := shapeView false (atCoordView raw) forest 0
def marks (raw : Nat) := (view raw).prefixMarks ++ [(view raw).root]
def acceptedBit (raw : Nat) := decide (raw < p.domain ∧ (view raw).count ≤ p.M)

private theorem zip_pairs {raw gs w} {ls ds : List Word} {xs es : List Nat}
    (l : List.Forall₂ (Holds raw gs w) ls xs) (d : List.Forall₂ (Holds raw gs w) ds es) :
    ChainLeafGates.paired raw gs w (ls.zip ds) (xs.zip es) := by
  induction l generalizing ds es with
  | nil => exact .nil
  | cons head tail ih =>
    cases d with
    | nil => exact .nil
    | cons hd more =>
      exact .cons ⟨⟨head.size,head.valid,head.value_eq⟩,⟨hd.size,hd.valid,hd.value_eq⟩⟩ (ih more)

private theorem coord_spec {raw gs d} (s : Seeded raw gs) (i : Nat)
    (h : MixedDecode.Represents raw gs (width p) d (coord raw i)) :
    Builds raw gs (atCoord p child outer d) (fun q a => Represents raw q (width p) a (atCoordView raw i)) :=
  ChainCoord.production_coord s d _ _ (zip_pairs h.leaves h.depths)
    ⟨h.bucket.size,h.bucket.valid,h.bucket.value_eq⟩

private theorem indexed [Inhabited α] {R : α → β → Prop} {xs ys}
    (rel : List.Forall₂ R xs ys) (i : Nat) {target : β} (atIndex : ys[i]? = some target) :
    R xs[i]! target := by
  induction rel generalizing i with
  | nil => simp at atIndex
  | cons h tail ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at atIndex
      rw [List.getElem!_cons_zero,←atIndex]
      exact h
    | succ i => simpa only [List.getElem!_cons_succ] using ih i atIndex

/-- A forest join adds the two child counters. A uniform slot bound thus
controls every counter in the forest, including all intermediate joins. -/
theorem count_le (v : Nat → View) (B : Nat) (each : ∀ i, (v i).count ≤ B) (s : Shape) (off : Nat) :
    (shapeView false v s off).count ≤ s.leaves*B := by
  induction s generalizing off with
  | leaf => simpa only [shapeView,Shape.leaves,Nat.one_mul] using each off
  | branch l r il ir =>
    change (shapeView false v l off).count+(shapeView false v r (off+l.leaves)).count+0 ≤
      (l.leaves+r.leaves)*B
    rw [Nat.add_zero,Nat.add_mul]
    exact Nat.add_le_add (il off) (ir (off+l.leaves))

theorem fits (v : Nat → View) (B w : Nat) (each : ∀ i, (v i).count ≤ B) (s : Shape) (off : Nat)
    (room : s.leaves*B < 2^w) : Fits false v w s off := by
  induction s generalizing off with
  | leaf => trivial
  | branch l r il ir =>
    refine ⟨lt_of_le_of_lt (count_le v B each _ off) room,?_,?_⟩
    · apply il
      simp only [Shape.leaves,Nat.add_mul] at room
      omega
    · apply ir
      simp only [Shape.leaves,Nat.add_mul] at room
      omega

private theorem build_forest (row : Row) (f o c : Shape) :
    build row f o c = (do
      let (valid,ds) ← decode row
      let a ← atShape false (fun i => atCoord row c o ds.toArray[i]!) f 0
      BucketProgram.finish row valid a) := rfl

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

/-- The slot index used by the literal gate program agrees with the
least-significant-first quotient used by the mixed-radix decoder. -/
theorem source_output (raw : Nat) (hr : raw < 2^p.r) :
    sourceBits p raw = acceptedBit raw :: ((marks raw).map Prod.fst ++ (marks raw).map Prod.snd) := by
  let start : Array Gate := #[.constant false,.constant true]
  have seed : Seeded raw start := initial_seeded raw
  apply source_of_build
  rw [build_forest]
  refine (MixedDecode.decode_chain seed hr).bind fun gs result e h => ?_
  rcases result with ⟨valid,ds⟩
  obtain ⟨hv,hd⟩ := h
  have card : forest.leaves=p.K := shape_card _ (by decide)
  have each (i : Nat) : (atCoordView raw i).count ≤ p.t := by
    have hcount := ChainCoord.inner_count_le p.cap (pairs raw i) child 0
    have ht : child.leaves=p.t := shape_card _ (by decide)
    change (ChainCoord.inner p.cap (pairs raw i) child 0).count ≤ p.t
    omega
  have room : forest.leaves*p.t < 2^width p := by rw [card]; decide +kernel
  have se := seed.mono e
  dsimp only
  refine (atShape_spec false _ (atCoordView raw) forest 0 raw gs (width p) se (by decide) ?_
    (fits _ _ _ each forest 0 room)).bind fun q a ex ha => ?_
  · intro i _ hi q ex
    have hi' : i<p.K := by simpa only [Nat.zero_add,card] using hi
    have lookup := MixedDecode.coordinates_get p DepthGaps.chainValues p.K raw i hi'
    have current := (indexed hd i lookup).mono ex
    simpa only [List.getElem!_toArray] using coord_spec (se.mono ex) i current
  · exact BucketProgram.finish_spec p (se.mono ex) (raw<p.domain) (hv.mono ex) ha (by decide +kernel)

private theorem scan_length (f : Nat → Bool) (is : List Nat) (b : Bool) :
    (ChainLeafGates.scan f is b).1.length = is.length := by
  induction is generalizing b with
  | nil => rfl
  | cons i is ih => simp [ChainLeafGates.scan,ih]

private theorem atCoord_length (raw i : Nat) :
    (atCoordView raw i).prefixMarks.length + 2 = outer.leaves*(child.leaves*(p.cap+3)) := by
  have leaf (j : Nat) : (ChainLeafGates.chainView p.cap j (pairs raw i)).prefixMarks.length+2=p.cap+3 := by
    simp [ChainLeafGates.chainView,scan_length]
  have inner : (ChainCoord.inner p.cap (pairs raw i) child 0).prefixMarks.length+2 = child.leaves*(p.cap+3) :=
    BucketProgram.shape_length true _ _ leaf child 0
  change (BucketCoord.outerView outer _ _ 0).prefixMarks.length+2 = _
  unfold BucketCoord.outerView
  apply BucketProgram.shape_length
  intro j
  simpa only [BucketCoord.gated,List.length_map] using inner

theorem marks_length (raw : Nat) : (marks raw).length = (scheme p).graph.length := by
  have h := BucketProgram.shape_length false (atCoordView raw) _ (atCoord_length raw) forest 0
  change (view raw).prefixMarks.length + 2 = _ at h
  have span : (view raw).prefixMarks.length+2=(scheme p).graph.length+1 :=
    h.trans (graph_span p).symm
  have len : (marks raw).length = (view raw).prefixMarks.length+1 := by simp [marks]
  omega

theorem protected_output (raw : Nat) (hr : raw<2^p.r) :
    (scheme p).accept raw = acceptedBit raw ∧
    (scheme p).frontier raw = (marks raw).map Prod.fst ∧ (scheme p).plan raw = (marks raw).map Prod.snd :=
  masks_of_source p raw hr _ _ (marks_length raw) (source_output raw hr)

end PoissonDAG.PORS.ChainProgram
