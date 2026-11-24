import Candidate.Constructions.PORS.BucketCoordRoute
import Candidate.Constructions.PORS.SingleOpeningCosts

namespace PoissonDAG.PORS.BucketCoord

open LiteralMaskSemantics PrunedCount

set_option allowUnsafeReducibility true in
attribute [local reducible] Shape.fill

def pathDepth : Shape → Nat → Nat
  | .leaf, _ => 0
  | .branch l r, i => (if i<l.leaves then pathDepth l i else pathDepth r (i-l.leaves)) + 1

theorem complete_depth (h i : Nat) : pathDepth (Literal.leftShape h 0) i = h := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => simp [Literal.leftShape, pathDepth, ih]

private def supply {t : Tree} (a : Opening t) := weight (a.marks.map Prod.fst)
private def work {t : Tree} (a : Opening t) := weight (a.marks.map Prod.snd)

private theorem stop_weights (t : Tree) : supply (.stop t) = 1 ∧ work (.stop t) = 0 := by
  simp [supply,work,Opening.marks,weight,List.count_replicate]

private theorem join_weights {l r : Tree} (a : Opening l) (b : Opening r) :
    supply (.join a b) = supply a + supply b ∧ work (.join a b) = work a + work b + 1 := by
  simp [supply,work,Opening.marks,weight,Nat.add_assoc]

def selectBucket {inner : Tree} (a : Opening inner) (idx j : Nat) :=
  if j=idx then some a else none

private theorem outer_absent (s : Shape) (idx off : Nat) {inner : Tree} (a : Opening inner)
    (outside : idx<off ∨ off+s.leaves ≤ idx) :
    openSelected inner (selectBucket a idx) s off = none := by
  induction s generalizing off with
  | leaf =>
    change idx<off ∨ off+1 ≤ idx at outside
    change selectBucket a idx off=none
    exact if_neg (by omega)
  | branch l r il ir =>
    change idx<off ∨ off+(l.leaves+r.leaves) ≤ idx at outside
    rw [openSelected,il off (by omega),ir (off+l.leaves) (by omega)]

/-- The outer path has one stopped sibling and one binary hash at
every level between the active bucket and the outer root. -/
theorem path_weights (s : Shape) (idx off : Nat) {inner : Tree} (a : Opening inner)
    (inside : off ≤ idx ∧ idx<off+s.leaves) {out : Opening (s.fill inner)}
    (route : openSelected inner (selectBucket a idx) s off = some out) :
    weight (out.marks.map Prod.fst) = weight (a.marks.map Prod.fst)+pathDepth s (idx-off) ∧
    weight (out.marks.map Prod.snd) = weight (a.marks.map Prod.snd)+pathDepth s (idx-off) := by
  change supply out = supply a + pathDepth s (idx-off) ∧ work out = work a + pathDepth s (idx-off)
  induction s generalizing off with
  | leaf =>
    change off ≤ idx ∧ idx<off+1 at inside
    have h : off=idx := by omega
    change selectBucket a idx off=some out at route
    have he : a=out := Option.some.inj ((if_pos h : selectBucket a idx off=some a).symm.trans route)
    subst out
    exact ⟨rfl,rfl⟩
  | branch l r il ir =>
    change off ≤ idx ∧ idx<off+(l.leaves+r.leaves) at inside
    change Opening ((l.fill inner).join (r.fill inner)) at out
    by_cases hleft : idx<off+l.leaves
    · have er := outer_absent r idx (off+l.leaves) a (by omega)
      cases el : openSelected inner (selectBucket a idx) l off with
      | none => simp [openSelected,el,er] at route
      | some v =>
        have eq : Opening.join v (.stop (r.fill inner)) = out := by
          simpa only [openSelected,el,er,Option.some.injEq] using route
        subst out
        obtain ⟨hs,hw⟩ := il off ⟨inside.1,hleft⟩ el
        have j := join_weights v (.stop (r.fill inner))
        have stop := stop_weights (r.fill inner)
        simp only [pathDepth,if_pos (show idx-off<l.leaves by omega),j.1,j.2,stop.1,stop.2,hs,hw]
        omega
    · have el := outer_absent l idx off a (by omega)
      cases er : openSelected inner (selectBucket a idx) r (off+l.leaves) with
      | none => simp [openSelected,el,er] at route
      | some v =>
        have eq : Opening.join (.stop (l.fill inner)) v = out := by
          simpa only [openSelected,el,er,Option.some.injEq] using route
        subst out
        obtain ⟨hs,hw⟩ := ir (off+l.leaves) ⟨by omega,by omega⟩ er
        have j := join_weights (.stop (l.fill inner)) v
        have stop := stop_weights (l.fill inner)
        simp only [pathDepth,if_neg (show ¬idx-off<l.leaves by omega),
          show idx-off-l.leaves=idx-(off+l.leaves) by omega,j.1,j.2,stop.1,stop.2,hs,hw]
        omega

/-- The proof retains the inner authentication budget and charges the
chosen bucket's public outer path separately. -/
theorem coord_weights (child outer : Shape) (idx : Nat) (hit : Nat → Bool)
    (u : Finset (Leaf child)) (agree : ∀ x, hit (leafIndex child x).val=true ↔ x∈u)
    (nonempty : 0<u.card) (idx_lt : idx<outer.leaves) {out : Opening (outer.fill (child.fill (chain 1)))}
    (route : routedOpening .leaf outer child 0 (fun _=>idx) (asDepth hit) = some out) :
    weight (out.marks.map Prod.fst) = u.card+siblings child u+pathDepth outer idx ∧
    weight (out.marks.map Prod.snd)+1 = 2*u.card+siblings child u+pathDepth outer idx := by
  obtain ⟨a,ha,_⟩ := route_of_nonempty child hit u agree nonempty
  have hm : SingleOpeningCosts.Agrees child 0 (asDepth hit 0) u := by
    intro x
    have h := agree x
    cases hh : hit (leafIndex child x).val <;> simpa [asDepth,hh] using h
  obtain ⟨hs,hw⟩ := SingleOpeningCosts.routed_weights child (fun _=>0) (asDepth hit) u hm ha
  rw [routed_eq_selected] at ha
  have hf : (fun i => ((asDepth hit) 0 i).map (fun e => openChain (0+1) (0-e))) =
      optionalLeaf hit := by
    funext i; cases h : hit i <;> simp [asDepth,optionalLeaf,h]
  change openSelected _ (fun j => if j=idx then openSelected (chain 1) _ child 0 else none) outer 0 =
    some out at route
  rw [hf,ha] at route
  have pw := path_weights outer idx 0 a ⟨by omega,by simpa using idx_lt⟩ route
  simp only [Nat.sub_zero] at pw
  constructor
  · exact pw.1.trans (congrArg (fun n => n+pathDepth outer idx) hs)
  · calc
      _ = weight (a.marks.map Prod.snd) + 1 + pathDepth outer idx := by
        rw [pw.2]; omega
      _ = _ := congrArg (fun n => n+pathDepth outer idx) hw

private theorem production_depth (idx : Nat) : pathDepth (Literal.shape BucketRefined.p.buckets) idx = 10 := by
  have he : Literal.shape BucketRefined.p.buckets = Literal.leftShape 10 0 := rfl
  rw [he,complete_depth]

/-- A single coordinate contributes six private labels, its forced inner
siblings and ten outer labels. Its verification plan contains the six
unary hashes and all joins of the inner and outer openings. -/
theorem production_coord_weights (idx : Nat) (hit : Nat → Bool)
    (u : Finset (Leaf (Literal.shape BucketRefined.p.t)))
    (agree : ∀ x, hit (leafIndex (Literal.shape BucketRefined.p.t) x).val=true ↔ x∈u)
    (hk : u.card=6) (idx_lt : idx<BucketRefined.p.buckets)
    {out : Opening ((Literal.shape BucketRefined.p.buckets).fill ((Literal.shape BucketRefined.p.t).fill (chain 1)))}
    (route : routedOpening .leaf (Literal.shape BucketRefined.p.buckets) (Literal.shape BucketRefined.p.t)
      0 (fun _=>idx) (asDepth hit) = some out) :
    weight (out.marks.map Prod.fst) = 16+siblings (Literal.shape BucketRefined.p.t) u ∧
    weight (out.marks.map Prod.snd) = 21+siblings (Literal.shape BucketRefined.p.t) u := by
  have hroom : idx < (Literal.shape BucketRefined.p.buckets).leaves := by
    rw [Literal.shape_card _ (by decide +kernel)]
    exact idx_lt
  have w := coord_weights _ _ idx hit u agree (by omega) hroom route
  rw [production_depth] at w
  omega

/-- Joining two completed coordinate openings adds one planned binary hash. -/
theorem two_weights {l r : Tree} (a : Opening l) (b : Opening r) (s0 s1 : Nat)
    (ha : weight (a.marks.map Prod.fst)=16+s0 ∧ weight (a.marks.map Prod.snd)=21+s0)
    (hb : weight (b.marks.map Prod.fst)=16+s1 ∧ weight (b.marks.map Prod.snd)=21+s1) :
    weight ((Opening.join a b).marks.map Prod.fst)=32+s0+s1 ∧
    weight ((Opening.join a b).marks.map Prod.snd)=43+s0+s1 := by
  have h := join_weights a b
  unfold supply work at h
  omega

/-- At the production cutoff the protected output uses at most 93 labels
and its verifier uses at most 106 hashes, including two digest calls. -/
theorem two_resources (scheme : Scheme) (raw : Nat) {l r : Tree} (a : Opening l) (b : Opening r)
    (graph : scheme.graph=(Tree.join l r).emit 0)
    (frontier : scheme.frontier raw=(Opening.join a b).marks.map Prod.fst)
    (plan : scheme.plan raw=(Opening.join a b).marks.map Prod.snd)
    (digest : scheme.digestCalls=2) (s0 s1 : Nat)
    (ha : weight (a.marks.map Prod.fst)=16+s0 ∧ weight (a.marks.map Prod.snd)=21+s0)
    (hb : weight (b.marks.map Prod.fst)=16+s1 ∧ weight (b.marks.map Prod.snd)=21+s1)
    (cutoff : s0+s1 ≤ 61) :
    weight (scheme.frontier raw) ≤ 93 ∧ scheme.verifyCalls raw ≤ 106 := by
  obtain ⟨hf,hp⟩ := two_weights a b s0 s1 ha hb
  have hlen : (scheme.plan raw).length=scheme.graph.length := by
    rw [plan,graph,List.length_map,Opening.mark_length,Tree.emit_length]
  have scan := close_calls_le_weight scheme.graph (scheme.frontier raw) (scheme.plan raw) hlen
  rw [← frontier] at hf
  rw [← plan] at hp
  unfold Scheme.verifyCalls
  omega

/-- The real two-coordinate traversal is the join of its two routed
coordinate openings at offsets zero and one. -/
theorem routed_two (outer child : Shape) (cap : Nat) (bucket : Nat → Nat) (d : Nat → Nat → Option Nat)
    {a b : Opening (outer.fill (child.fill (chain (cap+1))))}
    (left : routedOpening .leaf outer child cap (fun _ => bucket 0) (fun _ => d 0) = some a)
    (right : routedOpening .leaf outer child cap (fun _ => bucket 1) (fun _ => d 1) = some b) :
    routedOpening (.branch .leaf .leaf) outer child cap bucket d = some (.join a b) := by
  let co := fun i => openSelected (child.fill (chain (cap+1))) (fun j =>
    if j = bucket i then openSelected (chain (cap+1))
      (fun x => (d i x).map (fun e => openChain (cap+1) (cap-e))) child 0 else none) outer 0
  change co 0 = some a at left
  change co 1 = some b at right
  change openSelected _ co (.branch .leaf .leaf) 0 = some (Opening.join a b)
  simp only [openSelected,Shape.leaves,Nat.zero_add,left,right]

end PoissonDAG.PORS.BucketCoord
