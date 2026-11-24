import Candidate.Constructions.PORS.PrunedCount
import PoissonDAG.Constructions.PORS.RoutedOpening
import Candidate.Constructions.PORS.LiteralMaskLeaf

namespace PoissonDAG.PORS.LiteralMaskSemantics

open RankGates Literal

open PrunedCount

set_option allowUnsafeReducibility true in
attribute [local reducible] Leaf Shape.fill

/-- Every extra sibling occurs at a different internal vertex. -/
theorem child_count_le (s : Shape) (hit : Nat → Bool) (off : Nat) :
    (shapeView true (fun i => leafView (hit i)) s off).count + 1 ≤ s.leaves := by
  induction s generalizing off with
  | leaf => rfl
  | branch l r il ir =>
    have hL := il off
    have hR := ir (off+l.leaves)
    simp only [shapeView, joinView, Shape.leaves, increment, if_true]
    have hbit (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
    have := hbit (xor (shapeView true (fun i => leafView (hit i)) l off).active
      (shapeView true (fun i => leafView (hit i)) r (off+l.leaves)).active)
    omega

theorem child_fits (s : Shape) (hit : Nat → Bool) (off w : Nat) (width : s.leaves ≤ 2^w) :
    Fits true (fun i => leafView (hit i)) w s off := by
  induction s generalizing off with
  | leaf => trivial
  | branch l r il ir =>
    change l.leaves + r.leaves ≤ 2^w at width
    have h := child_count_le (.branch l r) hit off
    change _ + 1 ≤ l.leaves+r.leaves at h
    exact ⟨by omega, il off (by omega), ir (off+l.leaves) (by omega)⟩

theorem child_builder {raw p} (seed : Seeded raw p) (d : Digits) (xs : List Nat)
    (digits : LeafDigits raw p (width SingleRefined.p) (d.leaves.zip d.depths) xs)
    (s : Shape) (off : Nat) (bound : off+s.leaves ≤ 2^(width SingleRefined.p)) :
    Builds raw p (atShape true (atLeaf SingleRefined.p d) s off) (fun q v =>
      Represents raw q (width SingleRefined.p) v
        (shapeView true (fun i => leafView (decide (i ∈ xs))) s off)) := by
  apply atShape_spec _ _ _ _ _ _ _ _ seed (by decide +kernel)
  · intro i _ hhi q e
    exact atLeaf_single (seed.mono e) d xs (digits.mono e) i (by omega)
  · exact child_fits s _ off _ (by omega)

private theorem active_or (x y : Nat) :
    (decide (0<x) || decide (0<y)) = decide (0<x+y) := by
  cases x <;> cases y <;> simp

private theorem active_xor (x y : Nat) :
    (xor (decide (0<x)) (decide (0<y))).toNat = extraSibling x y := by
  cases x <;> cases y <;> simp [extraSibling]

/-- Both the builder's nonemptiness flag and its integer counter have the
same meaning as the ordinary-subset pruning recurrence. -/
theorem child_support (s : Shape) (off : Nat) (hit : Nat → Bool) (u : Finset (Leaf s))
    (agree : ∀ x, hit (off+(leafIndex s x).val) = true ↔ x ∈ u) :
    let v := shapeView true (fun i => leafView (hit i)) s off
    v.active = decide (0<u.card) ∧ v.count = siblings s u := by
  induction s generalizing off with
  | leaf =>
    change Finset Unit at u
    have ha := agree ()
    change hit (off+0) = true ↔ () ∈ u at ha
    rw [Nat.add_zero] at ha
    change hit off = decide (0<u.card) ∧ 0=0
    refine ⟨Bool.eq_iff_iff.mpr ?_,rfl⟩
    rw [ha, decide_eq_true_eq, Finset.card_pos]
    constructor
    · intro h; exact ⟨(),h⟩
    · rintro ⟨x,hx⟩; cases x; exact hx
  | branch l r il ir =>
    change Finset (Leaf l ⊕ Leaf r) at u
    have hL := il off u.toLeft (fun x => by
      rw [Finset.mem_toLeft]
      exact agree (.inl x))
    have hR := ir (off+l.leaves) u.toRight (fun x => by
      rw [Finset.mem_toRight, Nat.add_assoc]
      exact agree (.inr x))
    obtain ⟨aL,cL⟩ := hL
    obtain ⟨aR,cR⟩ := hR
    have hc : u.toLeft.card+u.toRight.card=u.card := Finset.card_toLeft_add_card_toRight
    simp only [shapeView, joinView, aL, aR, cL, cR, siblings, increment, if_true,
      active_or, active_xor, hc, and_self]

def optionalLeaf (hit : Nat → Bool) (i : Nat) : Option (Opening (chain 1)) :=
  if hit i then some (openChain 1 0) else none

/-- Include a sibling root when its parent is active through its other child. -/
def withSibling (v : View) (other : Bool) : List (Bool×Bool) :=
  v.prefixMarks ++ [(v.root.1 || (!v.active && other), v.root.2)]

private def openMarks {t : Tree} (o : Option (Opening t)) (other : Bool) : List (Bool×Bool) :=
  match o with
  | some a => a.marks
  | none => List.replicate (t.nodes-1) (false,false) ++ [(other,false)]

private theorem nodes_pos (t : Tree) : 0<t.nodes := by cases t <;> simp [Tree.nodes]

private theorem blank_marks (t : Tree) :
    List.replicate (t.nodes-1) (false,false) ++ [(false,false)] =
      List.replicate t.nodes (false,false) := by
  rw [← List.replicate_succ', show t.nodes-1+1=t.nodes by have := nodes_pos t; omega]

/-- Every positioned mark produced by the semantic join is the mark of the
corresponding stopping traversal, including the blank interior of an inactive subtree. -/
private theorem shape_openMarks (s : Shape) (off : Nat) (hit : Nat → Bool) :
    let v := shapeView true (fun i => leafView (hit i)) s off
    let o := openSelected (chain 1) (optionalLeaf hit) s off
    v.active = o.isSome ∧ ∀ other, withSibling v other = openMarks o other := by
  induction s generalizing off with
  | leaf =>
    cases h : hit off <;>
      simp [shapeView, leafView, openSelected, optionalLeaf, h, withSibling, openMarks,
        Shape.fill, openChain, Opening.marks, chain, Tree.nodes]
  | branch l r il ir =>
    obtain ⟨al,ml⟩ := il off
    obtain ⟨ar,mr⟩ := ir (off+l.leaves)
    let L := shapeView true (fun i => leafView (hit i)) l off
    let R := shapeView true (fun i => leafView (hit i)) r (off+l.leaves)
    change L.active = _ at al
    change R.active = _ at ar
    have hL := ml R.active
    have hR := mr L.active
    change withSibling L R.active = _ at hL
    change withSibling R L.active = _ at hR
    change (L.active || R.active) = _ ∧ ∀ other, withSibling (joinView true L R) other = _
    cases el : openSelected (chain 1) (optionalLeaf hit) l off <;>
      cases er : openSelected (chain 1) (optionalLeaf hit) r (off+l.leaves) <;>
      simp only [el,er,Option.isSome_none,Option.isSome_some] at al ar <;>
      simp only [withSibling, el, er, al, ar, openMarks, blank_marks, Bool.not_false,
        Bool.not_true, Bool.false_and, Bool.true_and, Bool.false_or, Bool.true_or, Bool.or_false,
        Bool.and_false] at hL hR <;>
      simp only [withSibling, joinView, openSelected, el, er, al, ar, openMarks,
        Opening.marks, Bool.not_false, Bool.not_true, Bool.false_and, Bool.true_and,
        Bool.false_or, Bool.true_or, Bool.or_false, Bool.and_false, Option.isSome_none,
        Option.isSome_some, true_and, Shape.fill, Tree.nodes, Nat.add_sub_cancel,
        blank_marks, List.replicate_add] <;>
      intro other <;> rw [hL,hR]

/-- Relate the root output marks to the exact routed opening for a decoded child. -/
theorem child_marks {s : Shape} {off : Nat} {hit : Nat → Bool} {a : Opening (s.fill (chain 1))}
    (ho : openSelected (chain 1) (optionalLeaf hit) s off = some a) :
    let v := shapeView true (fun i => leafView (hit i)) s off
    v.prefixMarks ++ [v.root] = a.marks := by
  have hm := (shape_openMarks s off hit).2 false
  rw [ho] at hm
  simpa [withSibling, openMarks] using hm

def gateLoop (hit : Nat) (xs : List (Nat×Nat)) (initial : Array (Nat×Nat)) :
    Build (Array (Nat×Nat)) := do
  let mut marks := initial
  for (s,h) in xs do
    marks := marks.push (← both s hit, ← both h hit)
  return marks

theorem gateLoop_cons (hit : Nat) (x y : Nat) (xs : List (Nat×Nat)) (a : Array (Nat×Nat)) :
    gateLoop hit ((x,y)::xs) a = (do
      let xm ← both x hit
      let ym ← both y hit
      gateLoop hit xs (a.push (xm,ym))) := by
  simp [gateLoop, List.forIn_cons, bind_assoc] <;> rfl

private theorem gated_marks {raw : Nat} (xs : List (Nat×Nat)) (vs : List (Bool×Bool))
    (p : Array Gate) (seed : Seeded raw p) (hit : Nat) (bit : HasBit raw p hit true)
    (input : List.Forall₂ (PairBits raw p) xs vs)
    (initial : Array (Nat×Nat)) (pre : List (Bool×Bool)) (known : Marks raw p initial pre) :
    Builds raw p (gateLoop hit xs initial) (fun q out => Marks raw q out (pre++vs)) := by
  induction xs generalizing p vs initial pre with
  | nil =>
    cases input
    simpa [gateLoop] using
      (builds_pure (raw := raw) (x := initial) (post := fun q a => Marks raw q a pre) known)
  | cons xy xs ih =>
    rcases xy with ⟨x,y⟩
    cases vs with
    | nil => cases input
    | cons b vs =>
      obtain ⟨hxy,hrest⟩ := List.forall₂_cons.mp input
      rw [gateLoop_cons]
      refine (both_bit seed hxy.1 bit).bind fun q xm e hx => ?_
      refine (both_bit (seed.mono e) (hxy.2.mono e) (bit.mono e)).bind fun q' ym e' hy => ?_
      have E := e.trans e'
      have hmore : Marks raw q' (initial.push (xm,ym)) (pre++[b]) := by
        change List.Forall₂ _ _ _
        rw [Array.toList_push]
        apply List.rel_append (known.mono E)
        exact .cons ⟨by simpa using hx.mono e', by simpa using hy⟩ .nil
      simpa only [List.append_assoc, List.singleton_append] using
        ih vs q' (seed.mono E) (bit.mono E)
          (List.Forall₂.imp (fun _ _ h => ⟨h.1.mono E,h.2.mono E⟩) hrest)
          _ _ hmore

theorem last_pair {raw p} (pre : List (Bool×Bool)) (b : Bool×Bool)
    (ws : List (Nat×Nat)) (h : List.Forall₂ (PairBits raw p) ws (pre++[b])) :
    ∃ xs x, ws=xs++[x] ∧ List.Forall₂ (PairBits raw p) xs pre ∧ PairBits raw p x b := by
  induction pre generalizing ws with
  | nil =>
    cases ws with
    | nil => cases h
    | cons x xs =>
      obtain ⟨hx,rest⟩ := List.forall₂_cons.mp h
      cases rest
      exact ⟨[],x,rfl,.nil,hx⟩
  | cons v vs ih =>
    cases ws with
    | nil => cases h
    | cons w ws =>
      obtain ⟨hw,hr⟩ := List.forall₂_cons.mp h
      obtain ⟨xs,x,rfl,hxs,hx⟩ := ih _ hr
      exact ⟨w::xs,x,rfl,.cons hw hxs,hx⟩

private def coordGate (w : Nat) (d : Digits) (inner : Part) : Build Part := do
  let hit ← eqw d.bucket (lit w 0)
  let marks ← gateLoop hit inner.marks.toList #[]
  let live ← both inner.active hit
  return ⟨live,marks,inner.siblings⟩

private theorem atCoord_one (row : Row) (child : Shape) (d : Digits) :
    atCoord row child .leaf d = (do
      let inner ← atShape true (atLeaf row d) child 0
      coordGate (width row) d inner) := by
  simp [atCoord, atShape, coordGate, gateLoop, bind_assoc] <;> rfl

private theorem coordGate_spec {raw p w a v} {d : Digits} (seed : Seeded raw p)
    (bucket : Number raw p w d.bucket 0) (h : Represents raw p w a v) :
    Builds raw p (coordGate w d a) (fun q out => Represents raw q w out v) := by
  unfold coordGate
  refine (eqw_number seed bucket (literal_number seed w 0 (by positivity))).bind
    fun q hit e hh => ?_
  have ht : HasBit raw q hit true := by simpa using hh
  obtain ⟨pre,last,he,hpre,hlast⟩ := (h.mono e).marks
  have hm : List.Forall₂ (PairBits raw q) a.marks.toList (v.prefixMarks++[v.root]) := by
    rw [he,Array.toList_push]
    exact List.rel_append hpre (.cons hlast .nil)
  refine (gated_marks _ _ q (seed.mono e) hit ht hm #[] [] .nil).bind fun q' marks e' hm' => ?_
  have E := e.trans e'
  refine (both_bit (seed.mono E) (h.active.mono E) (ht.mono e')).bind fun q'' active e'' ha => ?_
  apply builds_pure
  have all : Marks raw q'' marks (v.prefixMarks++[v.root]) := hm'.mono e''
  obtain ⟨xs,x,he,hxs,hx⟩ := last_pair _ _ _ all
  refine ⟨by simpa using ha, ⟨xs.toArray,x,?_,?_,hx⟩,h.count.mono (E.trans e'')⟩
  · apply Array.toList_inj.mp
    simpa using he
  · simpa [Marks] using hxs

/-- Gating every child mark by the one valid bucket preserves the entire
coordinate mask and the selected child count. -/
theorem atCoord_single {raw p} (seed : Seeded raw p) (d : Digits) (xs : List Nat)
    (digits : LeafDigits raw p (width SingleRefined.p) (d.leaves.zip d.depths) xs)
    (bucket : Number raw p (width SingleRefined.p) d.bucket 0) :
    Builds raw p (atCoord SingleRefined.p (shape SingleRefined.p.t) .leaf d)
      (fun q a => Represents raw q (width SingleRefined.p) a
        (shapeView true (fun i => leafView (decide (i ∈ xs))) (shape SingleRefined.p.t) 0)) := by
  rw [atCoord_one]
  have hb : 0+(shape SingleRefined.p.t).leaves ≤ 2^(width SingleRefined.p) := by
    rw [Nat.zero_add, Literal.shape_card _ (by decide +kernel)]
    decide +kernel
  refine (child_builder seed d xs digits _ 0 hb).bind fun q a e h => ?_
  exact coordGate_spec (seed.mono e) (bucket.mono e) h

/-- The same zero-capacity depth function is used in the protected traversal. -/
def asDepth (hit : Nat → Bool) (_coord i : Nat) : Option Nat :=
  if hit i then some 0 else none

theorem routed_eq_selected (s : Shape) (hit : Nat → Bool) :
    routedOpening .leaf .leaf s 0 (fun _ => 0) (asDepth hit) =
      openSelected (chain 1) (optionalLeaf hit) s 0 := by
  change openSelected (chain 1) _ s 0 = openSelected (chain 1) _ s 0
  congr 1
  funext i
  cases h : hit i <;> simp [optionalLeaf, asDepth, h]

/-- A nonempty support yields a routed opening with exactly the coordinate's masks. -/
theorem route_of_nonempty (s : Shape) (hit : Nat → Bool) (u : Finset (Leaf s))
    (agree : ∀ x, hit (leafIndex s x).val = true ↔ x ∈ u) (nonempty : 0<u.card) :
    ∃ a, routedOpening .leaf .leaf s 0 (fun _ => 0) (asDepth hit) = some a ∧
      (shapeView true (fun i => leafView (hit i)) s 0).prefixMarks ++
        [(shapeView true (fun i => leafView (hit i)) s 0).root] = a.marks := by
  rw [routed_eq_selected]
  obtain ⟨ha,_⟩ := child_support s 0 hit u (by simpa using agree)
  have hact := (shape_openMarks s 0 hit).1
  rw [ha] at hact
  cases h : openSelected (chain 1) (optionalLeaf hit) s 0 with
  | none => simp [h,nonempty] at hact
  | some a => exact ⟨a,rfl,child_marks h⟩

private theorem evalPairs {raw p ws vs} (h : List.Forall₂ (PairBits raw p) ws vs) :
    ws.map (fun z => (wireValue raw p z.1,wireValue raw p z.2)) = vs := by
  induction h with
  | nil => rfl
  | cons pair tail ih =>
    simp only [List.map_cons, pair.1.2, pair.2.2, ih]

theorem Represents.mark_values {raw p w a v} (h : Represents raw p w a v) :
    a.marks.toList.map (fun z => (wireValue raw p z.1,wireValue raw p z.2)) =
      v.prefixMarks ++ [v.root] := by
  obtain ⟨pre,last,he,hp,hl⟩ := h.marks
  rw [he, Array.toList_push]
  exact evalPairs (List.rel_append hp (.cons hl .nil))

end PoissonDAG.PORS.LiteralMaskSemantics
