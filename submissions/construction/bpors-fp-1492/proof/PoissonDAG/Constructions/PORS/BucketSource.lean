import PoissonDAG.Constructions.PORS.SingleOpeningSources

namespace PoissonDAG.PORS.BucketSource

/-- Position of an interior vertex of the i-th block under a binary shape. -/
def atBlock (t : Tree) : Shape → Nat → Nat → Nat
  | .leaf, _, v => v
  | .branch l r, i, v => if i < l.leaves then atBlock t l i v
      else (l.fill t).nodes + atBlock t r (i-l.leaves) v

theorem interior (t : Tree) (s : Shape) {i v : Nat} (hi : i<s.leaves) (hv : v+1<t.nodes) :
    atBlock t s i v + 1 < (s.fill t).nodes := by
  induction s generalizing i with
  | leaf => exact hv
  | branch l r il ir =>
    change i<l.leaves+r.leaves at hi
    by_cases h : i<l.leaves
    · have := il h
      simp only [atBlock, if_pos h,Shape.fill,Tree.nodes]
      omega
    · have := ir (i:=i-l.leaves) (by omega)
      simp only [atBlock, if_neg h,Shape.fill,Tree.nodes]
      omega

theorem node_at (t : Tree) (s : Shape) (base i v : Nat)
    (hi : i < s.leaves) (hv : v+1 < t.nodes)
    (isSource : ∀ b, (t.emit b)[v]? = some .source) :
    ((s.fill t).emit base)[atBlock t s i v]? = some .source := by
  induction s generalizing i base with
  | leaf => exact isSource base
  | branch l r il ir =>
    change i < l.leaves+r.leaves at hi
    let L := (l.fill t).emit base
    let R := (r.fill t).emit (base+(l.fill t).nodes)
    let root := Node.binary (base+(l.fill t).nodes-1) (base+(l.fill t).nodes+(r.fill t).nodes-1)
    change ((L++R)++[root])[atBlock t (.branch l r) i v]? = _
    by_cases h : i<l.leaves
    · have lt : atBlock t l i v < L.length := by
        have hh := interior t l h hv
        change _ < ((l.fill t).emit base).length
        rw [Tree.emit_length]; omega
      simp only [atBlock,if_pos h,List.getElem?_append_left (show atBlock t l i v < (L++R).length by simp only [List.length_append]; omega),
        List.getElem?_append_left lt]
      exact il _ _ h
    · have sub : i-l.leaves < r.leaves := by omega
      have lt : atBlock t r (i-l.leaves) v < R.length := by
        have hh := interior t r sub hv
        change _ < ((r.fill t).emit _).length
        rw [Tree.emit_length]; omega
      have len : L.length = (l.fill t).nodes := Tree.emit_length _ _
      simp only [atBlock,if_neg h,←len]
      rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
        List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
      exact ir _ _ sub

def bit {t : Tree} (o : Option (Opening t)) (v : Nat) : Bool :=
  match o with
  | none => false
  | some a => get (a.marks.map Prod.fst) v

private theorem stopped (t : Tree) {v : Nat} (h : v+1<t.nodes) :
    bit (some (Opening.stop t)) v = false := by
  have hv : v < t.nodes-1 := by omega
  simp [bit,Opening.marks,get,List.getElem?_map,List.getElem?_append,hv,List.getElem?_replicate]

private theorem left_bit {l r : Tree} (a : Opening l) (b : Opening r) {v : Nat}
    (h : v<l.nodes) : bit (some (Opening.join a b)) v = bit (some a) v := by
  have len : v<a.marks.length := by rwa [a.mark_length]
  simp only [bit,Opening.marks,get,List.getElem?_map,List.getElem?_append_left len,
    List.getElem?_append_left (show v<(a.marks++b.marks).length by simp only [List.length_append]; omega)]

private theorem right_bit {l r : Tree} (a : Opening l) (b : Opening r) {v : Nat}
    (h : v<r.nodes) : bit (some (Opening.join a b)) (l.nodes+v) = bit (some b) v := by
  have inside : l.nodes+v < (a.marks++b.marks).length := by
    simp only [List.length_append,Opening.mark_length]; omega
  have right : a.marks.length ≤ l.nodes+v := by rw [a.mark_length]; omega
  simp only [bit,Opening.marks,get,List.getElem?_map,List.getElem?_append_left inside,
    List.getElem?_append_right right,Opening.mark_length,Nat.add_sub_cancel_left]

/-- Stopping an unopened sibling reveals its root alone. Consequently an
interior vertex is marked exactly when the selected block marks it. -/
theorem through (t : Tree) (pick : Nat → Option (Opening t)) (s : Shape) (off i v : Nat)
    (hi : i<s.leaves) (hv : v+1<t.nodes) :
    bit (openSelected t pick s off) (atBlock t s i v) = bit (pick (off+i)) v := by
  induction s generalizing off i with
  | leaf =>
    have h0 : i=0 := by change i<1 at hi; omega
    subst i
    exact congrArg (fun n => bit (pick n) v) (Nat.add_zero off).symm
  | branch l r il ir =>
    change i<l.leaves+r.leaves at hi
    by_cases h : i<l.leaves
    · rw [← il off i h]
      have a := interior t l h hv
      cases hl : openSelected t pick l off <;> cases hr : openSelected t pick r (off+l.leaves) <;>
        simp only [openSelected,hl,hr,atBlock,if_pos h] <;>
        first | rfl | exact left_bit _ _ (by omega) | exact (left_bit _ _ (by omega)).trans (stopped _ a)
    · have sub : i-l.leaves<r.leaves := by omega
      rw [show off+i = off+l.leaves+(i-l.leaves) by omega,← ir (off+l.leaves) (i-l.leaves) sub]
      have a := interior t r sub hv
      cases hl : openSelected t pick l off <;> cases hr : openSelected t pick r (off+l.leaves) <;>
        simp only [openSelected,hl,hr,atBlock,if_neg h] <;>
        first | rfl | exact right_bit _ _ (by omega) | exact (right_bit _ _ (by omega)).trans (stopped _ a)

def vertex (f o c : Shape) (i b j : Nat) : Nat :=
  let block := c.fill (chain 1)
  atBlock (o.fill block) f i (atBlock block o b (SingleOpeningSources.address c j))

theorem source (f o c : Shape) {i b j : Nat} (hi : i<f.leaves) (hb : b<o.leaves) (hj : j<c.leaves) :
    (graph f o c 0)[vertex f o c i b j]? = some .source := by
  apply node_at _ f _ _ _ hi (interior _ o hb (SingleOpeningSources.address_below_root c hj))
  intro base
  exact node_at _ o base b _ hb (SingleOpeningSources.address_below_root c hj)
    (fun off => SingleOpeningSources.address_source c off hj)

theorem routed (f o c : Shape) (owner : Nat → Nat) (d : Nat → Nat → Option Nat)
    {i b j : Nat} (hi : i<f.leaves) (hb : b<o.leaves) (hj : j<c.leaves) :
    bit (routedOpening f o c 0 owner d) (vertex f o c i b j) =
      (decide (b = owner i) && (d i j).isSome) := by
  unfold vertex routedOpening
  have interiorChild := SingleOpeningSources.address_below_root c hj
  rw [through _ _ f 0 i _ hi (interior _ o hb interiorChild),Nat.zero_add i,
    through _ _ o 0 b _ hb interiorChild,Nat.zero_add b]
  by_cases h : b=owner i
  · simp only [if_pos h,decide_eq_true h,Bool.true_and]
    have marks := SingleOpeningSources.selected_mark c (d i) 0 j hj
    change bit (openSelected (chain 1) (SingleOpeningSources.leafOpening (d i)) c 0)
      (SingleOpeningSources.address c j) = _
    rw [Nat.zero_add j] at marks
    cases hs : openSelected (chain 1) (SingleOpeningSources.leafOpening (d i)) c 0 <;>
      rw [hs] at marks <;> exact marks
  · simp [h,bit]

/-- A covered target needs an actual historical supplier in the same
coordinate and bucket for each selected private leaf. -/
theorem supplier (s : Scheme) (f o c : Shape)
    (owner : Nat → Nat → Nat) (d : Nat → Nat → Nat → Option Nat)
    (graphEq : s.graph = graph f o c 0)
    (arity : s.encoder.outputs.length = 1+2*s.graph.length)
    (routes : ∀ x ∈ s.accepted, ∃ a,
      routedOpening f o c 0 (owner x) (d x) = some a ∧ s.frontier x = a.marks.map Prod.fst)
    {q : Nat} (h : Fin q → Fin s.accepted.length) (t : Fin s.accepted.length)
    (i j : Nat) (hi : i<f.leaves) (hj : j<c.leaves)
    (inBucket : owner s.accepted[t] i < o.leaves)
    (chosen : (d s.accepted[t] i j).isSome=true)
    (hc : s.covered (indexHistory s.accepted h) s.accepted[t]=true) :
    ∃ z : Fin q, owner s.accepted[(h z)] i = owner s.accepted[t] i ∧
      (d s.accepted[h z] i j).isSome=true := by
  let b := owner s.accepted[t] i
  let v := vertex f o c i b j
  have node : s.graph[v]? = some .source := graphEq ▸ source f o c hi inBucket hj
  have interiorV : v+1 < s.graph.length := by
    rw [graphEq]
    unfold graph
    rw [Tree.emit_length]
    exact interior _ f hi (interior _ o inBucket (SingleOpeningSources.address_below_root c hj))
  have marked (x : Nat) (hx : x∈s.accepted) : get (s.frontier x) v =
      (decide (b = owner x i) && (d x i j).isSome) := by
    obtain ⟨a,route,front⟩ := routes x hx
    have e := routed f o c (owner x) (d x) hi inBucket hj
    rw [route] at e
    rw [front]; exact e
  have target : v∈SingleCover.sources s s.accepted[t] := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),node,by omega,?_⟩
    rw [marked s.accepted[t] (List.getElem_mem t.isLt)]
    simpa only [b,decide_true,Bool.true_and,decide_eq_true rfl] using chosen
  obtain ⟨x,hx,hv⟩ := SingleCover.covered_source_has_supplier s _ _ v arity target hc
  obtain ⟨z,rfl⟩ := List.mem_ofFn.mp hx
  have hit := (Finset.mem_filter.mp hv).2.2.2
  rw [marked s.accepted[h z] (List.getElem_mem (h z).isLt),Bool.and_eq_true,decide_eq_true_eq] at hit
  exact ⟨z,hit.1.symm,hit.2⟩

end PoissonDAG.PORS.BucketSource
