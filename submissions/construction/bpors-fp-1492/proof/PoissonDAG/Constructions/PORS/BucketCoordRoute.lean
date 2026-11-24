import PoissonDAG.Constructions.PORS.BucketCoordGates

namespace PoissonDAG.PORS.BucketCoord

open LiteralMaskSemantics PrunedCount

private def expected {t : Tree} (o : Option (Opening t)) (other : Bool) :=
  match o with
  | some a => a.marks
  | none => List.replicate (t.nodes-1) (false,false) ++ [(other,false)]

private structure Models {t : Tree} (v : View) (o : Option (Opening t)) : Prop where
  active : v.active=o.isSome
  marks : ∀ other, withSibling v other = expected o other

private theorem blank (t : Tree) :
    List.replicate (t.nodes-1) (false,false) ++ [(false,false)] =
      List.replicate t.nodes (false,false) := by
  have hp : 0<t.nodes := by cases t <;> simp [Tree.nodes]
  rw [← List.replicate_succ', show t.nodes-1+1=t.nodes by omega]

private def joined {l r : Tree} : Option (Opening l) → Option (Opening r) →
    Option (Opening (.join l r))
  | none, none => none
  | some a, none => some (.join a (.stop _))
  | none, some b => some (.join (.stop _) b)
  | some a, some b => some (.join a b)

private theorem model_join {l r : Tree} {a : Option (Opening l)} {b : Option (Opening r)}
    {L R : View} (left : Models L a) (right : Models R b) (countHere : Bool) :
    Models (joinView countHere L R) (joined a b) := by
  have al := left.active
  have ar := right.active
  have hL := left.marks R.active
  have hR := right.marks L.active
  cases a <;> cases b <;>
    simp only [Option.isSome_none,Option.isSome_some] at al ar <;>
    simp only [withSibling,al,ar,expected,blank,Bool.not_false,Bool.not_true,Bool.false_and,
      Bool.true_and,Bool.false_or,Bool.true_or,Bool.or_false,Bool.and_false] at hL hR <;>
    constructor <;>
    simp only [joined,joinView,withSibling,expected,al,ar,Option.isSome_none,Option.isSome_some,
      Bool.not_false,Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_or,Bool.true_or,
      Bool.or_false,Bool.and_false,Opening.marks,Tree.nodes,Nat.add_sub_cancel,List.replicate_add] <;>
    intro other <;> rw [hL,hR]

/-- Lift leaf-opening semantics through an arbitrary postorder shape. -/
private theorem model_shape (unit : Tree) (out : Nat → Option (Opening unit)) (v : Nat → View)
    (correct : ∀ i, Models (v i) (out i)) (s : Shape) (off : Nat) (countHere : Bool) :
    Models (shapeView countHere v s off) (openSelected unit out s off) := by
  induction s generalizing off with
  | leaf => exact correct off
  | branch l r il ir =>
    have h := model_join (il off) (ir (off+l.leaves)) countHere
    change Models _ (joined (openSelected unit out l off) (openSelected unit out r (off+l.leaves))) at h
    cases hl : openSelected unit out l off <;> cases hr : openSelected unit out r (off+l.leaves) <;>
      simp only [shapeView,openSelected,hl,hr,joined] at h ⊢ <;> exact h

/-- Any nonempty tree of locally matching optional openings has the literal
postorder marks of the resulting stopping traversal. -/
theorem route_from_leaves (unit : Tree) (out : Nat → Option (Opening unit)) (v : Nat → View)
    (active : ∀ i, (v i).active=(out i).isSome)
    (marks : ∀ i other, withSibling (v i) other =
      match out i with
      | some a => a.marks
      | none => List.replicate (unit.nodes-1) (false,false) ++ [(other,false)])
    (s : Shape) (off : Nat) (countHere : Bool) (live : (shapeView countHere v s off).active=true) :
    ∃ a, openSelected unit out s off=some a ∧ (shapeView countHere v s off).prefixMarks ++
      [(shapeView countHere v s off).root]=a.marks := by
  have hm := model_shape unit out v (fun i => ⟨active i,marks i⟩) s off countHere
  have ha := hm.active
  rw [live] at ha
  cases h : openSelected unit out s off with
  | none => simp [h] at ha
  | some a =>
    refine ⟨a,rfl,?_⟩
    have hh := hm.marks false
    rw [h] at hh
    simpa [withSibling,expected] using hh

private theorem mask_true : mask true = id := by
  funext b
  cases b
  simp [mask]

private theorem mask_false (b : Bool×Bool) : mask false b = (false,false) := by
  simp [mask]

private theorem false_prefix (vs : List (Bool×Bool)) :
    vs.map (mask false) = List.replicate vs.length (false,false) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [mask_false, ih, List.replicate_succ]

private theorem gate_model {t : Tree} {v : View} {a : Opening t}
    (live : v.active=true) (marks : v.prefixMarks ++ [v.root] = a.marks) (hit : Bool) :
    Models (gated hit v) (if hit then some a else none) := by
  have hl := congrArg List.length marks
  simp only [List.length_append, List.length_singleton, Opening.mark_length] at hl
  have len : v.prefixMarks.length = t.nodes-1 := by omega
  cases hit with
  | false =>
    constructor
    · simp [gated]
    · intro other
      simp [gated, withSibling, expected, false_prefix, len, mask_false]
  | true =>
    constructor
    · simpa [gated] using live
    · intro other
      simpa [gated, withSibling, expected, live, mask_true] using marks

/-- The uniquely active bucket carries the entire inner opening. Every
inactive sibling on its outer path contributes exactly its stopped root. -/
theorem outer_route (outer : Shape) (off idx : Nat) {inner : Tree} (a : Opening inner) (v : View)
    (live : v.active=true) (marks : v.prefixMarks++[v.root]=a.marks)
    (hidx : off ≤ idx ∧ idx<off+outer.leaves) :
    ∃ opened, openSelected inner (fun j => if j=idx then some a else none) outer off = some opened ∧
      (outerView outer v idx off).prefixMarks ++ [(outerView outer v idx off).root] = opened.marks := by
  let pick := fun j : Nat => if j=idx then some a else none
  have hm : Models (outerView outer v idx off) (openSelected inner pick outer off) := by
    apply model_shape
    intro i
    simpa [pick] using gate_model live marks (decide (i=idx))
  have ha := hm.active
  rw [outer_active,live] at ha
  cases h : openSelected inner pick outer off with
  | none => simp [h,hidx] at ha
  | some result =>
    refine ⟨result,by first | exact h | rfl,?_⟩
    have hh := hm.marks false
    rw [h] at hh
    simpa [withSibling,expected] using hh

/-- A nonempty support and an in-range bucket give the actual decoded
coordinate a routed opening, even before imposing the sibling cutoff. -/
theorem routed_coord (child outer : Shape) (idx : Nat) (hit : Nat → Bool)
    (u : Finset (Leaf child)) (agree : ∀ x, hit (leafIndex child x).val = true ↔ x ∈ u)
    (nonempty : 0<u.card) (idx_lt : idx < outer.leaves) :
    let v := shapeView true (fun i => leafView (hit i)) child 0
    ∃ a, routedOpening .leaf outer child 0 (fun _ => idx) (asDepth hit) = some a ∧
      (coordView outer v idx).prefixMarks ++ [(coordView outer v idx).root] = a.marks := by
  let v := shapeView true (fun i => leafView (hit i)) child 0
  obtain ⟨inner, issued, hm⟩ := route_of_nonempty child hit u agree nonempty
  rw [routed_eq_selected] at issued
  have hl : v.active=true := by
    have h := (child_support child 0 hit u (by simpa using agree)).1
    simpa [nonempty,v] using h
  obtain ⟨a,hr,ha⟩ := outer_route outer 0 idx inner v hl hm ⟨by omega,by simpa using idx_lt⟩
  refine ⟨a,?_,ha⟩
  have hf : (fun i => ((asDepth hit) 0 i).map (fun e => openChain (0+1) (0-e))) =
      optionalLeaf hit := by
    funext i
    cases h : hit i <;> simp [asDepth,optionalLeaf,h]
  change openSelected _ (fun j => if j=idx then openSelected (chain 1) _ child 0 else none) outer 0 =
    some a
  rw [hf,issued]
  exact hr

/-- When both coordinates are live, the forest-level gate merge preserves
each complete coordinate opening and appends the plan bit for the joining hash. -/
theorem live_join {l r : Tree} (a : Opening l) (b : Opening r) (L R : View)
    (hL : L.active=true) (hR : R.active=true)
    (mL : L.prefixMarks ++ [L.root] = a.marks) (mR : R.prefixMarks ++ [R.root] = b.marks) :
    (joinView false L R).active=true ∧ (joinView false L R).count = L.count+R.count ∧
    (joinView false L R).prefixMarks ++ [(joinView false L R).root] = (Opening.join a b).marks := by
  have left : (L.root.1 || (!L.active && R.active), L.root.2) = L.root := by simp [hL]
  have right : (R.root.1 || (!R.active && L.active), R.root.2) = R.root := by simp [hR]
  constructor
  · simp [joinView,hL]
  constructor
  · rfl
  · change (L.prefixMarks ++ [(L.root.1 || (!L.active && R.active), L.root.2)]) ++
        (R.prefixMarks ++ [(R.root.1 || (!R.active && L.active), R.root.2)]) ++
        [(false,L.active || R.active)] = a.marks ++ b.marks ++ [(false,true)]
    rw [left,right,mL,mR,hL,hR, Bool.true_or]

end PoissonDAG.PORS.BucketCoord
