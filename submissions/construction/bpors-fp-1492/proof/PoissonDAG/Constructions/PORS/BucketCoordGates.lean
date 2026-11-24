import PoissonDAG.Constructions.PORS.LiteralMaskSemantics

namespace PoissonDAG.PORS.BucketCoord

open RankGates Literal LiteralMaskSemantics

def mask (hit : Bool) (b : Bool×Bool) := (b.1 && hit, b.2 && hit)

def gated (hit : Bool) (v : View) : View :=
  ⟨v.active && hit, v.prefixMarks.map (mask hit), mask hit v.root, 0⟩

def outerView (outer : Shape) (v : View) (bucket off : Nat) :=
  shapeView false (fun j => gated (decide (j=bucket)) v) outer off

def coordView (outer : Shape) (v : View) (bucket : Nat) :=
  {outerView outer v bucket 0 with count := v.count}

private theorem gates_mask (raw : Nat) (xs : List (Nat×Nat)) (vs : List (Bool×Bool))
    (p : Array Gate) (seed : Seeded raw p) (hit : Nat) (b : Bool) (hb : HasBit raw p hit b)
    (input : List.Forall₂ (PairBits raw p) xs vs)
    (initial : Array (Nat×Nat)) (pre : List (Bool×Bool)) (known : Marks raw p initial pre) :
    Builds raw p (gateLoop hit xs initial) (fun q out => Marks raw q out (pre++vs.map (mask b))) := by
  induction xs generalizing p vs initial pre with
  | nil =>
    cases input
    simpa [gateLoop] using
      (builds_pure (raw := raw) (x := initial) (post := fun q a => Marks raw q a pre) known)
  | cons xy xs ih =>
    rcases xy with ⟨x,y⟩
    cases vs with
    | nil => cases input
    | cons v vs =>
      obtain ⟨hxy,hrest⟩ := List.forall₂_cons.mp input
      rw [gateLoop_cons]
      refine (both_bit seed hxy.1 hb).bind fun q xm e hx => ?_
      refine (both_bit (seed.mono e) (hxy.2.mono e) (hb.mono e)).bind fun q' ym e' hy => ?_
      have E := e.trans e'
      have pair : PairBits raw q' (xm,ym) (mask b v) := ⟨hx.mono e',hy⟩
      have hmore : Marks raw q' (initial.push (xm,ym)) (pre++[mask b v]) := by
        change List.Forall₂ _ _ _
        rw [Array.toList_push]
        exact List.rel_append (known.mono E) (.cons pair .nil)
      simpa only [List.map_cons, List.append_assoc, List.singleton_append] using
        ih vs q' (seed.mono E) (hb.mono E)
          (List.Forall₂.imp (fun _ _ h => ⟨h.1.mono E,h.2.mono E⟩) hrest) _ _ hmore

/-- The outer leaf gates the entire inner mask and resets its local counter. -/
def atBucket (w : Nat) (d : Digits) (inner : Part) (j : Nat) : Build Part := do
  let hit ← eqw d.bucket (lit w j)
  let marks ← gateLoop hit inner.marks.toList #[]
  let active ← both inner.active hit
  return ⟨active,marks,lit w 0⟩

theorem atBucket_spec {raw p w a v} {d : Digits} (seed : Seeded raw p)
    {idx j : Nat} (bucket : Number raw p w d.bucket idx) (hj : j<2^w)
    (part : Represents raw p w a v) :
    Builds raw p (atBucket w d a j) (fun q out => Represents raw q w out (gated (decide (j=idx)) v)) := by
  unfold atBucket
  refine (eqw_number seed bucket (literal_number seed w j hj)).bind fun q hit e hh => ?_
  have ht : HasBit raw q hit (decide (j=idx)) := by simpa [eq_comm] using hh
  obtain ⟨pre,last,he,hpre,hlast⟩ := (part.mono e).marks
  have hm : List.Forall₂ (PairBits raw q) a.marks.toList (v.prefixMarks++[v.root]) := by
    rw [he,Array.toList_push]
    exact List.rel_append hpre (.cons hlast .nil)
  refine (gates_mask raw _ _ q (seed.mono e) hit _ ht hm #[] [] .nil).bind fun q' marks e' hm' => ?_
  have E := e.trans e'
  refine (both_bit (seed.mono E) (part.active.mono E) (ht.mono e')).bind fun q'' active e'' ha => ?_
  apply builds_pure
  have all : Marks raw q'' marks
      (v.prefixMarks.map (mask (decide (j=idx))) ++ [mask (decide (j=idx)) v.root]) := by
    simpa using hm'.mono e''
  obtain ⟨xs,x,he,hxs,hx⟩ := last_pair _ _ _ all
  refine ⟨ha, ⟨xs.toArray,x,?_,?_,hx⟩, literal_number (seed.mono (E.trans e'')) w 0 (by positivity)⟩
  · apply Array.toList_inj.mp
    simpa using he
  · simpa [Marks,gated] using hxs

@[simp] theorem outer_count (outer : Shape) (v : View) (idx off : Nat) :
    (outerView outer v idx off).count = 0 := by
  induction outer generalizing off with
  | leaf => rfl
  | branch l r il ir =>
    change (outerView l v idx off).count + (outerView r v idx (off+l.leaves)).count + 0 = 0
    rw [il,ir]

private theorem outer_fits (outer : Shape) (v : View) (idx off w : Nat) :
    Fits false (fun j => gated (decide (j=idx)) v) w outer off := by
  induction outer generalizing off with
  | leaf => trivial
  | branch l r il ir =>
    exact ⟨by change (outerView (.branch l r) v idx off).count < 2^w; rw [outer_count]; positivity,
      il off, ir (off+l.leaves)⟩

/-- A subtree of the outer Merkle tree is live precisely when it contains
the selected bucket and the inner support is nonempty. -/
theorem outer_active (outer : Shape) (v : View) (idx off : Nat) :
    (outerView outer v idx off).active = (v.active && decide (off ≤ idx ∧ idx < off+outer.leaves)) := by
  induction outer generalizing off with
  | leaf =>
    change (v.active && decide (off=idx)) = (v.active && decide (off ≤ idx ∧ idx<off+1))
    apply congrArg (fun b : Bool => v.active && b)
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  | branch l r il ir =>
    change ((outerView l v idx off).active || (outerView r v idx (off+l.leaves)).active) = _
    rw [il,ir]
    cases v.active <;> simp only [Bool.false_and, Bool.true_and, Bool.false_or, Shape.leaves]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    omega

private theorem child_gates (row : Row) (hc : row.cap=0) {raw p} (seed : Seeded raw p)
    (d : Digits) (xs : List Nat) (digits : LeafDigits raw p (width row) (d.leaves.zip d.depths) xs)
    (child : Shape) (room : child.leaves ≤ 2^(width row)) (hw : 0<width row) :
    Builds raw p (atShape true (atLeaf row d) child 0) (fun q a => Represents raw q (width row) a
        (shapeView true (fun i => leafView (decide (i ∈ xs))) child 0)) := by
  apply atShape_spec _ _ _ _ _ _ _ _ seed hw
  · intro i _ hi q e
    exact atLeaf_chainless row hc (seed.mono e) d xs (digits.mono e) i (by omega)
  · exact child_fits child _ 0 _ room

private theorem atCoord_gates (row : Row) (child outer : Shape) (d : Digits) :
    atCoord row child outer d = (do
      let inner ← atShape true (atLeaf row d) child 0
      let result ← atShape false (atBucket (width row) d inner) outer 0
      return {result with siblings := inner.siblings}) := by
  delta atBucket
  simp [atCoord,gateLoop,bind_assoc]

/-- Lift a proved literal child builder through the selected outer bucket. -/
theorem atCoord_of_inner (row : Row) (child outer : Shape) {raw p} (seed : Seeded raw p)
    (d : Digits) (idx : Nat) (cv : View)
    (bucket : Number raw p (width row) d.bucket idx) (houter : outer.leaves ≤ 2^(width row))
    (hw : 0<width row) (inner_spec : Builds raw p (atShape true (atLeaf row d) child 0)
      (fun q a => Represents raw q (width row) a cv)) :
    Builds raw p (atCoord row child outer d) (fun q out => Represents raw q (width row) out
      (coordView outer cv idx)) := by
  rw [atCoord_gates]
  refine inner_spec.bind fun q inner e hinner => ?_
  have hleaf : ∀ j, 0 ≤ j → j < 0+outer.leaves → ∀ q', Extends raw q q' →
      Builds raw q' (atBucket (width row) d inner j) (fun q'' out =>
        Represents raw q'' (width row) out (gated (decide (j=idx)) cv)) := by
    intro j _ hj q' ext
    exact atBucket_spec (seed.mono (e.trans ext)) (bucket.mono (e.trans ext)) (by omega)
      (hinner.mono ext)
  refine (atShape_spec false _ _ outer 0 raw q (width row) (seed.mono e) hw hleaf
    (outer_fits outer cv idx 0 _)).bind fun q' out e' houter' => ?_
  exact builds_pure ⟨houter'.active,houter'.marks,hinner.count.mono e'⟩

/-- Gate semantics for every bucket of an arbitrary zero-capacity row.
Only the native inner sibling count survives the outer traversal. -/
theorem atCoord_chainless (row : Row) (hc : row.cap=0) (child outer : Shape)
    {raw p} (seed : Seeded raw p) (d : Digits) (xs : List Nat) (idx : Nat)
    (digits : LeafDigits raw p (width row) (d.leaves.zip d.depths) xs)
    (bucket : Number raw p (width row) d.bucket idx)
    (hchild : child.leaves ≤ 2^(width row)) (houter : outer.leaves ≤ 2^(width row)) (hw : 0<width row) :
    Builds raw p (atCoord row child outer d) (fun q out =>
      Represents raw q (width row) out
        (coordView outer (shapeView true (fun i => leafView (decide (i ∈ xs))) child 0) idx)) := by
  exact atCoord_of_inner row child outer seed d idx _ bucket houter hw
    (child_gates row hc seed d xs digits child hchild hw)

open BucketRefined in
theorem production_coord {raw g} (seed : Seeded raw g) (d : Digits) (xs : List Nat) (idx : Nat)
    (digits : LeafDigits raw g (width p) (d.leaves.zip d.depths) xs)
    (bucket : Number raw g (width p) d.bucket idx) :
    Builds raw g (atCoord p (shape p.t) (shape p.buckets) d) (fun q out =>
      Represents raw q (width p) out (coordView (shape p.buckets)
        (shapeView true (fun i => leafView (decide (i ∈ xs))) (shape p.t) 0) idx)) := by
  apply atCoord_chainless p rfl _ _ seed d xs idx digits bucket
  · rw [shape_card _ (by decide +kernel)]; decide +kernel
  · rw [shape_card _ (by decide +kernel)]; decide +kernel
  · decide +kernel

end PoissonDAG.PORS.BucketCoord
