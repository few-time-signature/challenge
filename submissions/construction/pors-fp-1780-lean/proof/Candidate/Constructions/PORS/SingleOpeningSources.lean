import Candidate.Constructions.PORS.SingleCover
import PoissonDAG.Constructions.PORS.RoutedOpening
import Mathlib.Data.Finset.Fin

namespace PoissonDAG.PORS.SingleOpeningSources

abbrev block (s : Shape) := s.fill (chain 1)

/-- Postorder vertex address of the private source at left-to-right leaf i. -/
def address : Shape → Nat → Nat
  | .leaf, _ => 0
  | .branch l r, i =>
    if i < l.leaves then address l i else (block l).nodes + address r (i-l.leaves)

theorem address_below_root (s : Shape) {i : Nat} (hi : i < s.leaves) :
    address s i + 1 < (block s).nodes := by
  induction s generalizing i with
  | leaf => change 1 < 2; decide
  | branch l r il ir =>
    change i < l.leaves + r.leaves at hi
    change address (.branch l r) i + 1 < (block l).nodes + (block r).nodes + 1
    by_cases h : i < l.leaves
    · have := il h
      simp only [address, if_pos h]
      omega
    · have := ir (i := i-l.leaves) (by omega)
      simp only [address, if_neg h]
      omega

private theorem address_injective (s : Shape) {i j : Nat} (hi : i < s.leaves)
    (hj : j < s.leaves) (he : address s i = address s j) : i = j := by
  induction s generalizing i j with
  | leaf => change i < 1 at hi; change j < 1 at hj; omega
  | branch l r il ir =>
    change i < l.leaves + r.leaves at hi
    change j < l.leaves + r.leaves at hj
    by_cases hx : i < l.leaves <;> by_cases hy : j < l.leaves <;>
      simp only [address, hx, hy, if_true, if_false] at he
    · exact il hx hy he
    · have := address_below_root l hx
      omega
    · have := address_below_root l hy
      omega
    · have hdiff := ir (i := i-l.leaves) (j := j-l.leaves) (by omega) (by omega) (by omega)
      omega

def sourceEmbedding (s : Shape) : Fin s.leaves ↪ Nat :=
  ⟨fun i => address s i, fun i j he => Fin.ext (address_injective s i.isLt j.isLt he)⟩

private theorem left_lookup {α : Type} (a b : List α) (v : α) {i : Nat} (hi : i < a.length) :
    ((a ++ b) ++ [v])[i]? = a[i]? := by
  rw [List.getElem?_append_left (show i < (a++b).length by simp only [List.length_append]; omega),
    List.getElem?_append_left hi]

private theorem right_lookup {α : Type} (a b : List α) (v : α) {i : Nat} (hi : i < b.length) :
    ((a ++ b) ++ [v])[a.length+i]? = b[i]? := by
  rw [List.getElem?_append_left (show a.length+i < (a++b).length by
    simp only [List.length_append]; omega)]
  exact after_prefix _ _ _

/-- Every leaf address actually points to a secret vertex of the emitted graph. -/
theorem address_source (s : Shape) (base : Nat) {i : Nat} (hi : i < s.leaves) :
    ((block s).emit base)[address s i]? = some .source := by
  induction s generalizing base i with
  | leaf => rfl
  | branch l r il ir =>
    change i < l.leaves + r.leaves at hi
    simp only [block, Shape.fill, Tree.emit]
    by_cases h : i < l.leaves
    · simp only [address, if_pos h]
      rw [left_lookup _ _ _
        (by rw [Tree.emit_length]; exact (Nat.lt_succ_self _).trans (address_below_root l h))]
      exact il base h
    · have hj : i-l.leaves < r.leaves := by omega
      simp only [address, if_neg h]
      rw [← Tree.emit_length (block l) base, right_lookup _ _ _
        (by rw [Tree.emit_length]; exact (Nat.lt_succ_self _).trans (address_below_root r hj))]
      exact ir _ hj

/-- Conversely, the leaves enumerate every source in this graph. -/
theorem source_has_address (s : Shape) (base v : Nat)
    (hs : ((block s).emit base)[v]? = some .source) :
    ∃ i : Fin s.leaves, address s i = v := by
  induction s generalizing base v with
  | leaf =>
    cases v with
    | zero => exact ⟨⟨0, by decide⟩, rfl⟩
    | succ v => cases v <;> simp [block, Shape.fill, chain, Tree.emit] at hs
  | branch l r il ir =>
    let L := (block l).emit base
    let R := (block r).emit (base+(block l).nodes)
    let root := Node.binary (base+(block l).nodes-1) (base+(block l).nodes+(block r).nodes-1)
    change ((L++R)++[root])[v]? = some .source at hs
    by_cases hL : v < L.length
    · rw [left_lookup L R root hL] at hs
      obtain ⟨i, he⟩ := il _ _ hs
      refine ⟨⟨i.val, (show i.val < l.leaves+r.leaves by have := i.isLt; omega)⟩, ?_⟩
      simpa only [address, if_pos i.isLt] using he
    by_cases hR : v < L.length + R.length
    · have hj : v-L.length < R.length := by omega
      have hlookup := right_lookup L R root hj
      rw [show L.length+(v-L.length) = v by omega] at hlookup
      rw [hlookup] at hs
      obtain ⟨i, he⟩ := ir _ _ hs
      refine ⟨⟨l.leaves+i.val, (show l.leaves+i.val < l.leaves+r.leaves by have := i.isLt; omega)⟩, ?_⟩
      have hlen : L.length = (block l).nodes := Tree.emit_length _ _
      simp only [address, Nat.not_lt_of_ge (Nat.le_add_right _ _), if_false, Nat.add_sub_cancel_left]
      omega
    · rw [List.getElem?_append_right (by simp only [List.length_append]; omega)] at hs
      generalize v-(L++R).length = j at hs
      cases j <;> simp [root] at hs

private theorem stop_mark (s : Shape) {i : Nat} (hi : i < s.leaves) :
    get ((Opening.stop (block s)).marks.map Prod.fst) (address s i) = false := by
  have hb : address s i < (block s).nodes-1 := by have := address_below_root s hi; omega
  simp [Opening.marks, get, List.getElem?_map, List.getElem?_append, hb,
    List.getElem?_replicate]

private theorem left_mark {l r : Tree} (a : Opening l) (b : Opening r)
    {i : Nat} (hi : i < l.nodes) :
    get ((Opening.join a b).marks.map Prod.fst) i = get (a.marks.map Prod.fst) i := by
  have h := left_lookup a.marks b.marks (false,true) (by simpa only [a.mark_length] using hi)
  simp only [Opening.marks, get, List.getElem?_map, h]

private theorem right_mark {l r : Tree} (a : Opening l) (b : Opening r)
    {i : Nat} (hi : i < r.nodes) :
    get ((Opening.join a b).marks.map Prod.fst) (l.nodes+i) = get (b.marks.map Prod.fst) i := by
  have h := right_lookup a.marks b.marks (false,true) (by simpa only [b.mark_length] using hi)
  rw [a.mark_length] at h
  simp only [Opening.marks, get, List.getElem?_map, h]

def leafOpening (d : Nat → Option Nat) (j : Nat) : Option (Opening (chain 1)) :=
  (d j).map (fun e => openChain 1 (0-e))

private def mark {s : Shape} (o : Option (Opening (block s))) (i : Nat) : Bool :=
  match o with
  | none => false
  | some a => get (a.marks.map Prod.fst) (address s i)

/-- A sibling subtree stopped by forced pruning marks its root. Its private
sources stay hidden. Thus the source mark is exactly the decoder selection bit. -/
theorem selected_mark (s : Shape) (d : Nat → Option Nat) (off i : Nat) (hi : i < s.leaves) :
    mark (s := s) (openSelected (chain 1) (leafOpening d) s off) i = (d (off+i)).isSome := by
  induction s generalizing off i with
  | leaf =>
    have hz : i = 0 := by change i < 1 at hi; omega
    subst i
    cases hd : d off <;> simp [openSelected, leafOpening, hd, mark, address, openChain,
      Opening.marks, Tree.nodes, chain, get]
  | branch l r il ir =>
    change i < l.leaves + r.leaves at hi
    by_cases h : i < l.leaves
    · rw [← il off i h]
      have hi' : address l i < (block l).nodes := by have := address_below_root l h; omega
      cases hl : openSelected (chain 1) (leafOpening d) l off <;>
        cases hr : openSelected (chain 1) (leafOpening d) r (off+l.leaves) <;>
        simp only [openSelected, hl, hr, mark, address, if_pos h] <;>
        first | exact left_mark _ _ hi' | exact (left_mark _ _ hi').trans (stop_mark l h)
    · have hj : i-l.leaves < r.leaves := by omega
      have he : off+i = (off+l.leaves)+(i-l.leaves) := by omega
      rw [he, ← ir (off+l.leaves) (i-l.leaves) hj]
      have hi' : address r (i-l.leaves) < (block r).nodes := by
        have := address_below_root r hj; omega
      cases hl : openSelected (chain 1) (leafOpening d) l off <;>
        cases hr : openSelected (chain 1) (leafOpening d) r (off+l.leaves) <;>
        simp only [openSelected, hl, hr, mark, address, if_neg h] <;>
        first | exact right_mark _ _ hi' | exact (right_mark _ _ hi').trans (stop_mark r hj)

/-- The full one-coordinate, one-bucket route directly specializes the tree result. -/
theorem routed_source_mark (s : Shape) (d : Nat → Nat → Option Nat) (bucket : Nat → Nat)
    {a : Opening (block s)} (route : routedOpening .leaf .leaf s 0 bucket d = some a)
    (i : Fin s.leaves) :
    get (a.marks.map Prod.fst) (address s i) = (d 0 i).isSome := by
  change (if 0 = bucket 0 then openSelected (chain 1) (leafOpening (d 0)) s 0 else none) =
    some a at route
  split at route
  · have h := selected_mark s (d 0) 0 i i.isLt
    rw [route] at h
    simpa only [mark, Nat.zero_add] using h
  · contradiction

def selected (s : Shape) (d : Nat → Option Nat) : Finset (Fin s.leaves) :=
  Finset.univ.filter (fun i => (d i.val).isSome = true)

/-- Identify the protected source set with exactly the selected natural leaves,
transported by the postorder address embedding. -/
theorem sources_eq_map (s : Shape) (scheme : Scheme) (raw : Nat)
    (graph : scheme.graph = (block s).emit 0) (d : Nat → Nat → Option Nat)
    (bucket : Nat → Nat) {a : Opening (block s)}
    (route : routedOpening .leaf .leaf s 0 bucket d = some a)
    (frontier : scheme.frontier raw = a.marks.map Prod.fst) :
    SingleCover.sources scheme raw = (selected s (d 0)).map (sourceEmbedding s) := by
  ext v
  constructor
  · intro hv
    obtain ⟨_, hsource, _, hbit⟩ := Finset.mem_filter.mp hv
    rw [graph] at hsource
    obtain ⟨i, he⟩ := source_has_address s 0 v hsource
    refine Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
    rw [← routed_source_mark s d bucket route i, ← frontier, he]
    exact hbit
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
    have hb := address_below_root s i.isLt
    have hlen : scheme.graph.length = (block s).nodes := by rw [graph, Tree.emit_length]
    change address s i ∈ SingleCover.sources scheme raw
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, by omega, ?_⟩
    · rw [graph]
      exact address_source s 0 i.isLt
    · rw [frontier, routed_source_mark s d bucket route i]
      exact (Finset.mem_filter.mp hi).2

/-- A proof that the accepted colex supports are fixed-weight and uniquely
identify the raw rank transfers to the protected source interface. -/
theorem sourceCode_of_supports (s : Shape) (scheme : Scheme) (k : Nat)
    (support : Nat → Finset (Fin s.leaves))
    (masks : ∀ raw ∈ scheme.accepted,
      SingleCover.sources scheme raw = (support raw).map (sourceEmbedding s))
    (weight : ∀ raw ∈ scheme.accepted, (support raw).card = k)
    (unique : ∀ x ∈ scheme.accepted, ∀ y ∈ scheme.accepted, support x = support y → x = y) :
    SingleCover.SourceCode scheme k := by
  constructor
  · intro raw hr
    rw [masks raw hr, Finset.card_map, weight raw hr]
  · intro x hx y hy he
    rw [masks x hx, masks y hy] at he
    exact unique x hx y hy (Finset.map_injective _ he)

/-- The chainless decoder supplies the private point, of residual depth zero,
at precisely those natural leaf numbers in the colex support. -/
def zeroDepth (u : Finset Nat) (_coord leaf : Nat) : Option Nat :=
  if leaf ∈ u then some 0 else none

theorem selected_zeroDepth (s : Shape) (u : Finset Nat) (coord : Nat)
    (bounded : ∀ i ∈ u, i < s.leaves) :
    selected s (zeroDepth u coord) = u.attachFin bounded := by
  ext i
  by_cases hi : i.val ∈ u <;> simp [selected, zeroDepth, hi]

theorem selected_zeroDepth_values (s : Shape) (u : Finset Nat) (coord : Nat)
    (bounded : ∀ i ∈ u, i < s.leaves) :
    (selected s (zeroDepth u coord)).map Fin.valEmbedding = u := by
  rw [selected_zeroDepth s u coord bounded, Finset.map_valEmbedding_attachFin]

end PoissonDAG.PORS.SingleOpeningSources
