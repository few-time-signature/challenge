import PoissonDAG.Model
import PoissonDAG.Constructions.GRSCC.Graph
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# Pooled closure and backward barriers

These lemmas use the protected `close` function itself. A backward barrier is
a set of unavailable vertices such that each of its non-source vertices has a
parent in the barrier. A pool avoiding the barrier cannot acquire any barrier
vertex by forward closure, even with joins between different histories.

This is infrastructure for private-prefix necessity. This file does not assert
the GRS-CC covering bound or identify an abstract recurrence with a Scheme.
-/
namespace PoissonDAG.GRSCC

def Avoids (blocked : Nat → Prop) (known : List Bool) : Prop :=
  ∀ i, blocked i → get known i = false

theorem not_avoids_witness {blocked : Nat → Prop} {known : List Bool}
    (hav : ¬Avoids blocked known) : ∃ i, blocked i ∧ get known i = true := by
  classical
  simp only [Avoids, not_forall] at hav
  obtain ⟨i, hb, hg⟩ := hav
  refine ⟨i, hb, ?_⟩
  cases h : get known i with
  | false => exact False.elim (hg h)
  | true => rfl

def HasBlockedParent (blocked : Nat → Prop) : Node → Prop
  | .source => True
  | .unary p => blocked p
  | .binary l r => blocked l ∨ blocked r

def BackwardBarrier (graph : List Node) (blocked : Nat → Prop) : Prop :=
  ∀ node i, (node, i) ∈ graph.zipIdx → blocked i → HasBlockedParent blocked node

theorem HasBlockedParent.mono {a b : Nat → Prop} {node : Node}
    (hn : HasBlockedParent a node) (hab : ∀ i, a i → b i) :
    HasBlockedParent b node := by
  cases node with
  | source => trivial
  | unary p => exact hab p hn
  | binary l r =>
      rcases hn with hl | hr
      · exact Or.inl (hab l hl)
      · exact Or.inr (hab r hr)

theorem BackwardBarrier.union {graph : List Node} {a b : Nat → Prop}
    (ha : BackwardBarrier graph a) (hb : BackwardBarrier graph b) :
    BackwardBarrier graph (fun i => a i ∨ b i) := by
  intro node i hmem hi
  rcases hi with hia | hib
  · exact (ha node i hmem hia).mono (fun _ h => Or.inl h)
  · exact (hb node i hmem hib).mono (fun _ h => Or.inr h)

/-- Add an actual graph vertex whose selected parent is already in the
barrier. This builds owner subtrees and unary edge prefixes structurally. -/
theorem BackwardBarrier.insert {graph : List Node} {blocked : Nat → Prop}
    (hb : BackwardBarrier graph blocked) {vertex : Nat} {node : Node}
    (hv : graph[vertex]? = some node) (hn : HasBlockedParent blocked node) :
    BackwardBarrier graph (fun i => i = vertex ∨ blocked i) := by
  intro actual i hmem hi
  rcases hi with hieq | hib
  · subst i
    have hlookup := List.mk_mem_zipIdx_iff_getElem?.mp hmem
    have hnode : actual = node := Option.some.inj (hlookup.symm.trans hv)
    subst actual
    exact hn.mono (fun _ h => Or.inr h)
  · exact (hb actual i hmem hib).mono (fun _ h => Or.inr h)

theorem ready_false_of_avoids {blocked : Nat → Prop} {known : List Bool}
    {node : Node} (hk : Avoids blocked known)
    (hn : HasBlockedParent blocked node) : ready known node = false := by
  cases node with
  | source => rfl
  | unary p => exact hk p hn
  | binary l r =>
      rcases hn with hl | hr
      · simp [ready, hk l hl]
      · simp [ready, hk r hr]

theorem avoids_set_of_not_blocked {blocked : Nat → Prop} {known : List Bool}
    {i : Nat} (hk : Avoids blocked known) (hi : ¬blocked i) :
    Avoids blocked (known.set i true) := by
  intro j hj
  have hij : i ≠ j := by
    intro heq
    subst j
    exact hi hj
  simpa only [get, List.getElem?_set_ne hij] using hk j hj

/-- Full protected forward closure preserves every backward barrier. In
particular, this theorem does not replace pooled closure by a union of
individual closures. -/
theorem close_avoids {graph : List Node} {blocked : Nat → Prop}
    {disclosed allowed : List Bool} (hb : BackwardBarrier graph blocked)
    (hd : Avoids blocked disclosed) :
    Avoids blocked (close graph disclosed allowed).1 := by
  unfold close
  apply List.foldlRecOn (motive := fun state : List Bool × Nat => Avoids blocked state.1)
      (graph.zipIdx) _ hd
  intro state hs item hitem
  rcases item with ⟨node, i⟩
  dsimp only
  split
  · exact hs
  · split
    · apply avoids_set_of_not_blocked hs
      intro hi
      have hr := ready_false_of_avoids hs (hb node i hitem hi)
      simp_all
    · exact hs

theorem avoids_union {blocked : Nat → Prop} {a b : List Bool}
    (ha : Avoids blocked a) (hb : Avoids blocked b) : Avoids blocked (union a b) := by
  have pointwise : ∀ (a b : List Bool) (i : Nat),
      get a i = false → get b i = false → get (union a b) i = false := by
    intro a
    induction a with
    | nil => intro b i _ _; simp [union, get]
    | cons x xs ih =>
        intro b i ha hb
        cases b with
        | nil => simp [union, get]
        | cons y ys =>
            cases i with
            | zero => simpa [union, get] using congrArg₂ (· || ·) ha hb
            | succ i =>
                exact ih ys i (by simpa [get] using ha) (by simpa [get] using hb)
  intro i hi
  exact pointwise a b i (ha i hi) (hb i hi)

theorem avoids_replicate_false (blocked : Nat → Prop) (n : Nat) :
    Avoids blocked (List.replicate n false) := by
  intro i _
  by_cases hi : i < n
  · simp [get, List.getElem?_replicate, hi]
  · simp [get, List.getElem?_replicate, hi]

/-- A pooled list of history disclosures avoids a barrier whenever every
history disclosure avoids it. This includes arbitrary cross-history pooling. -/
theorem pool_avoids {blocked : Nat → Prop} {hs : List Nat}
    {frontier : Nat → List Bool} {n : Nat}
    (hh : ∀ raw ∈ hs, Avoids blocked (frontier raw)) :
    Avoids blocked
      (hs.foldl (fun known raw => union known (frontier raw))
        (List.replicate n false)) := by
  apply List.foldlRecOn (motive := Avoids blocked) hs _ (avoids_replicate_false blocked n)
  intro known hk raw hraw
  exact avoids_union hk (hh raw hraw)

/-- The actual protected pool, including its public root identity, cannot
cross a backward barrier absent from every disclosure and from the root. -/
theorem protected_pool_close_avoids (s : Scheme) (hs : List Nat)
    {blocked : Nat → Prop} (hb : BackwardBarrier s.graph blocked)
    (hr : ¬blocked (s.graph.length - 1))
    (hh : ∀ raw ∈ hs, Avoids blocked (s.frontier raw)) :
    Avoids blocked
      (close s.graph
        ((hs.foldl (fun known raw => union known (s.frontier raw))
          (List.replicate s.graph.length false)).set (s.graph.length - 1) true)
        (List.replicate s.graph.length true)).1 := by
  exact close_avoids hb (avoids_set_of_not_blocked (pool_avoids hh) hr)

theorem close_length (graph : List Node) (disclosed allowed : List Bool) :
    (close graph disclosed allowed).1.length = disclosed.length := by
  unfold close
  apply List.foldlRecOn (motive := fun state : List Bool × Nat =>
    state.1.length = disclosed.length) (graph.zipIdx) _ rfl
  intro state hs item _
  rcases item with ⟨node, i⟩
  dsimp only
  split
  · exact hs
  · split
    · simpa only [List.length_set] using hs
    · exact hs

theorem subset_get {a b : List Bool} {i : Nat}
    (hsub : subset a b = true) (ha : i < a.length) (hb : i < b.length)
    (hget : get a i = true) : get b i = true := by
  induction a generalizing b i with
  | nil => simp_all
  | cons x xs ih =>
      cases b with
      | nil => simp_all
      | cons y ys =>
          have hsplit : ((!x || y) && subset xs ys) = true := hsub
          cases i with
          | zero =>
              cases x <;> cases y <;> simp_all [get]
          | succ i =>
              change get ys i = true
              exact ih (b := ys) (i := i) (Bool.and_eq_true_iff.mp hsplit).2
                (by simpa using ha) (by simpa using hb) (by simpa [get] using hget)

theorem scheme_frontier_length (s : Scheme)
    (houtputs : s.encoder.outputs.length = 1 + 2 * s.graph.length) (raw : Nat) :
    (s.frontier raw).length = s.graph.length := by
  simp only [Scheme.frontier, Circuit.eval, List.length_take, List.length_drop,
    List.length_map, houtputs]
  omega

theorem pool_length (s : Scheme) (hs : List Nat)
    (houtputs : s.encoder.outputs.length = 1 + 2 * s.graph.length) :
    (hs.foldl (fun known raw => union known (s.frontier raw))
      (List.replicate s.graph.length false)).length = s.graph.length := by
  apply List.foldlRecOn (motive := fun known : List Bool => known.length = s.graph.length)
    hs _ (by simp)
  intro known hk raw _
  simp [union, hk, scheme_frontier_length s houtputs raw]

/-- Every covered target requirement in a backward barrier needs some actual
history disclosure in that barrier. The assertion is about the protected
`Scheme.covered` event, including full pooled closure and the public root. -/
theorem covered_requires_barrier_hit (s : Scheme) (hs : List Nat) (target i : Nat)
    {blocked : Nat → Prop}
    (houtputs : s.encoder.outputs.length = 1 + 2 * s.graph.length)
    (hb : BackwardBarrier s.graph blocked) (hr : ¬blocked (s.graph.length - 1))
    (hi : i < s.graph.length) (hib : blocked i) (hit : get (s.frontier target) i = true)
    (hc : s.covered hs target = true) :
    ∃ raw ∈ hs, ¬Avoids blocked (s.frontier raw) := by
  by_contra hnone
  push_neg at hnone
  have hav := protected_pool_close_avoids s hs hb hr hnone
  let pooled := (hs.foldl (fun known raw => union known (s.frontier raw))
    (List.replicate s.graph.length false)).set (s.graph.length - 1) true
  let known := (close s.graph pooled (List.replicate s.graph.length true)).1
  have hknownlen : known.length = s.graph.length := by
    dsimp [known, pooled]
    rw [close_length, List.length_set, pool_length s hs houtputs]
  have hsub : subset (s.frontier target) known = true := by
    change (s.accept target && subset (s.frontier target) known) = true at hc
    exact (Bool.and_eq_true_iff.mp hc).2
  have hcovered := subset_get hsub
    (by rw [scheme_frontier_length s houtputs]; exact hi)
    (by rw [hknownlen]; exact hi) hit
  have hmissing : get known i = false := hav i hib
  rw [hmissing] at hcovered
  contradiction

theorem covered_implies_accepted (s : Scheme) (hs : List Nat) (target : Nat)
    (hc : s.covered hs target = true) : s.accept target = true := by
  unfold Scheme.covered at hc
  exact (Bool.and_eq_true_iff.mp hc).1

theorem count_true_filter_preserving (xs : List Nat) (accept event : Nat → Bool)
    (h : ∀ x, event x = true → accept x = true) :
    (xs.map event).count true = ((xs.filter accept).map event).count true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases ha : accept x <;> cases he : event x <;>
        simp_all [List.filter_cons]

/-- The conditional accepted-target coefficient, with the same literal
histories and full pooled event as the protected raw-target coefficient. -/
def acceptedTargetCoefficient (s : Scheme) (q : Nat) : Rat :=
  let hs := histories s.accepted q
  let numerator := ((hs.flatMap (fun h =>
    s.accepted.map (fun x => s.covered h x))).count true)
  (numerator : Rat) / ((s.accepted.length ^ (q + 1) : Nat) : Rat)

/-- Exact raw/accepted target bridge: acceptance is counted once. This proof
uses actual protected finite counts, not an assumed sampler distribution. -/
theorem coverCoefficient_acceptance_once (s : Scheme) (q : Nat)
    (haccepted : 0 < s.accepted.length) :
    s.coverCoefficient q = s.tau * acceptedTargetCoefficient s q := by
  have hn : ((histories s.accepted q).flatMap (fun h =>
      s.raws.map (fun x => s.covered h x))).count true =
      ((histories s.accepted q).flatMap (fun h =>
        s.accepted.map (fun x => s.covered h x))).count true := by
    simp only [List.count_flatMap, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro hs _
    exact count_true_filter_preserving s.raws s.accept (s.covered hs)
      (covered_implies_accepted s hs)
  unfold Scheme.coverCoefficient acceptedTargetCoefficient
  dsimp only
  rw [hn]
  unfold Scheme.tau
  have ha : (s.accepted.length : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt haccepted
  have hr : ((2 ^ s.encoder.inputs : Nat) : Rat) ≠ 0 := by
    exact_mod_cast pow_ne_zero s.encoder.inputs (by decide : (2 : Nat) ≠ 0)
  push_cast at hr
  push_cast
  rw [pow_succ]
  field_simp [ha, hr] <;> ring

def guardStart (a : OwnerAddress) (slot : Slot) : Nat :=
  ownerBase a.bucket a.layer a.owner + slot.val * 10

/-- The private guard's ancestors through the required opening, inclusive. -/
def guardPrefix (a : OwnerAddress) (slot : Slot) (point : Fin 9) (i : Nat) : Prop :=
  guardStart a slot ≤ i ∧ i ≤ guardStart a slot + point.val

def InOwner (a : OwnerAddress) (i : Nat) : Prop :=
  ownerBase a.bucket.val a.layer.val a.owner.val ≤ i ∧
    i < ownerBase a.bucket.val a.layer.val a.owner.val + 847

theorem InOwner.lt_graph {a : OwnerAddress} {i : Nat} (hi : InOwner a i) :
    i < graph.length := by
  have hb := a.bucket.isLt
  have hn := a.ownerNumber_lt
  rw [graph_length]
  dsimp [InOwner, ownerBase] at hi
  omega

theorem root_not_in_owner (a : OwnerAddress) : ¬InOwner a (graph.length - 1) := by
  have hb := a.bucket.isLt
  have hn := a.ownerNumber_lt
  rw [root_index]
  dsimp [InOwner, ownerBase]
  omega

theorem guardPrefix_in_owner (a : OwnerAddress) (slot : Slot) (point : Fin 9)
    (i : Nat) (hi : guardPrefix a slot point i) : InOwner a i := by
  have hs := slot.isLt
  have hp := point.isLt
  dsimp [guardPrefix, guardStart] at hi
  dsimp [InOwner]
  omega

theorem guard_child_local_lt (a : OwnerAddress) (slot : Slot) (point : Fin 9) :
    (a.layer.val * 32 + a.owner.val) * 847 + slot.val * 10 + point.val < 164318 := by
  have hl := a.layer.isLt
  have ho := a.owner.isLt
  have hs := slot.isLt
  have hp := point.isLt
  unfold ownerCount at ho
  split at ho <;> omega

theorem guardPrefix_barrier (a : OwnerAddress) (slot : Slot) (point : Fin 9) :
    BackwardBarrier graph (guardPrefix a slot point) := by
  intro node i hmem hi
  have hlookup := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  have hibound := List.snd_lt_of_mem_zipIdx hmem
  simp only [Nat.add_zero, graph_length] at hibound
  have hp := point.isLt
  let offset : Fin 9 := ⟨i - guardStart a slot, by dsimp [guardPrefix] at hi; omega⟩
  have hieq : i = guardVertex a slot offset := by
    change i = guardStart a slot + (i - guardStart a slot)
    have hlo := hi.1
    omega
  have hgraph : graphNode i = node := by
    have hget := graph_get ⟨i, by rw [fixed_geometry.2.2.2.1]; exact hibound⟩
    rw [hlookup] at hget
    exact Option.some.inj hget.symm
  rw [← hgraph, hieq, graphNode_guard]
  split
  · trivial
  · rename_i hnonzero
    change guardPrefix a slot point (guardVertex a slot offset - 1)
    rw [← hieq]
    dsimp [guardPrefix] at hi ⊢
    dsimp [offset] at hnonzero
    omega

theorem guardPrefix_excludes_root (a : OwnerAddress) (slot : Slot) (point : Fin 9) :
    ¬guardPrefix a slot point (graph.length - 1) := by
  have hc := guard_child_local_lt a slot point
  have hb := a.bucket.isLt
  rw [root_index]
  dsimp [guardPrefix, guardStart, ownerBase]
  omega

/-- A whole guarded leaf remains unavailable if its private guard chain is
unavailable, even when the shared successor root is public knowledge. -/
def leafBarrier (a : OwnerAddress) (slot : Slot) (i : Nat) : Prop :=
  i = leafVertex a.bucket.val a.layer.val a.owner.val slot.val ∨
    guardPrefix a slot ⟨8, by decide⟩ i

theorem leafBarrier_in_owner (a : OwnerAddress) (slot : Slot) (i : Nat)
    (hi : leafBarrier a slot i) : InOwner a i := by
  rcases hi with rfl | hguard
  · have hs := slot.isLt
    dsimp [InOwner, leafVertex]
    omega
  · exact guardPrefix_in_owner a slot _ i hguard

theorem leafBarrier_barrier (a : OwnerAddress) (slot : Slot) :
    BackwardBarrier graph (leafBarrier a slot) := by
  apply BackwardBarrier.insert (guardPrefix_barrier a slot ⟨8, by decide⟩)
    (node := graphNode (leafVertex a.bucket.val a.layer.val a.owner.val slot.val))
  · have hb := a.bucket.isLt
    have hn := a.ownerNumber_lt
    have hs := slot.isLt
    have hbound : leafVertex a.bucket.val a.layer.val a.owner.val slot.val < graphNodes := by
      rw [fixed_geometry.2.2.2.1]
      dsimp [leafVertex, ownerBase]
      omega
    exact graph_get ⟨_, hbound⟩
  · have hguard : guardPrefix a slot ⟨8, by decide⟩
        (leafVertex a.bucket.val a.layer.val a.owner.val slot.val - 1) := by
      dsimp [guardPrefix, guardStart, leafVertex]
      omega
    rw [graphNode_leaf]
    split
    · exact hguard
    · exact Or.inl hguard

def edgePrefixBarrier (a : OwnerAddress) (level : Depth) (childPosition : Nat)
    (point : Fin 9) (base : Nat → Prop) (i : Nat) : Prop :=
  base i ∨ ∃ k : Fin 9, 1 ≤ k.val ∧ k.val ≤ point.val ∧
    i = edgePointVertex a.bucket.val a.layer.val a.owner.val
      level.val childPosition k.val

instance edgePrefixBarrier_decidable (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9) (base : Nat → Prop)
    [DecidablePred base] (i : Nat) :
    Decidable (edgePrefixBarrier a level childPosition point base i) := by
  unfold edgePrefixBarrier
  infer_instance

/-- Extending an unavailable private subtree along its real unary edge
preserves a backward barrier. This is valid even when all external nodes are
already available. -/
theorem edgePrefixBarrier_barrier (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9) {base : Nat → Prop}
    (hchild : childPosition < 2 ^ (5 - level.val))
    (hbase : BackwardBarrier graph base)
    (hroot : base (treeChild a.bucket.val a.layer.val a.owner.val
      level.val childPosition)) :
    BackwardBarrier graph (edgePrefixBarrier a level childPosition point base) := by
  intro actual i hmem hi
  rcases hi with hib | ⟨k, hkpos, hkup, hieq⟩
  · exact (hbase actual i hmem hib).mono (fun _ h => Or.inl h)
  · have hlookup := List.mk_mem_zipIdx_iff_getElem?.mp hmem
    have hibound := List.snd_lt_of_mem_zipIdx hmem
    simp only [Nat.add_zero, graph_length] at hibound
    have hget := graph_get ⟨i, by rw [fixed_geometry.2.2.2.1]; exact hibound⟩
    rw [hlookup] at hget
    have hactual : graphNode i = actual := Option.some.inj hget.symm
    have hp := point.isLt
    have hkstep : k.val - 1 < 8 := by omega
    have hk : k.val - 1 + 1 = k.val := by omega
    have hnode := graphNode_edge a level childPosition hchild ⟨k.val - 1, hkstep⟩
    dsimp only at hnode
    simp only [Fin.val_mk, hk] at hnode
    rw [← hactual, hieq, hnode]
    by_cases hone : k.val = 1
    · simp only [hone, Nat.sub_self, ↓reduceIte]
      exact Or.inl hroot
    · have hnz : k.val - 1 ≠ 0 := by omega
      simp only [if_neg hnz]
      apply Or.inr
      let previous : Fin 9 := ⟨k.val - 1, by omega⟩
      refine ⟨previous, ?_, ?_, ?_⟩
      · change 1 ≤ k.val - 1
        omega
      · change k.val - 1 ≤ point.val
        omega
      · change edgePointVertex a.bucket.val a.layer.val a.owner.val level.val childPosition k.val - 1 =
          edgePointVertex a.bucket.val a.layer.val a.owner.val level.val childPosition (k.val - 1)
        have hkzero : k.val ≠ 0 := by omega
        simp only [edgePointVertex, if_neg hkzero, if_neg hnz]
        omega

theorem edgePrefixBarrier_in_owner (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9) {base : Nat → Prop}
    (hchild : childPosition < 2 ^ (5 - level.val))
    (hbase : ∀ i, base i → InOwner a i) (i : Nat)
    (hi : edgePrefixBarrier a level childPosition point base i) : InOwner a i := by
  rcases hi with hib | ⟨k, _, _, rfl⟩
  · exact hbase i hib
  · exact edgePointVertex_in_owner a level childPosition hchild k

/-- Assemble two private child-edge barriers and their actual binary join.
Repeated with `leafBarrier_barrier` and `edgePrefixBarrier_barrier`, this
constructs unavailable owner subtrees without assuming union/closure commute. -/
theorem treeJoinBarrier_barrier (a : OwnerAddress) (level : Depth) (position : Nat)
    {left right : Nat → Prop} (hposition : position < 2 ^ (4 - level.val))
    (hleft : BackwardBarrier graph left) (hright : BackwardBarrier graph right)
    (hleftEnd : left (treeJoin a.bucket.val a.layer.val a.owner.val
      level.val position - 9)) :
    BackwardBarrier graph (fun i =>
      i = treeJoin a.bucket.val a.layer.val a.owner.val level.val position ∨
        (left i ∨ right i)) := by
  apply BackwardBarrier.insert (hleft.union hright)
    (node := graphNode (treeJoin a.bucket.val a.layer.val a.owner.val level.val position))
  · have hb := a.bucket.isLt
    have ho := a.ownerNumber_lt
    have hi : treeJoin a.bucket.val a.layer.val a.owner.val level.val position < graphNodes := by
      rw [fixed_geometry.2.2.2.1]
      fin_cases level <;> norm_num [treeJoin, treeLevelBase, ownerBase] at * <;> omega
    exact graph_get ⟨_, hi⟩
  · rw [graphNode_treeJoin a level position hposition]
    exact Or.inl (Or.inl hleftEnd)

def privateSubtreeRoot (a : OwnerAddress) : Nat → Nat → Nat
  | 0, position => leafVertex a.bucket.val a.layer.val a.owner.val position
  | height + 1, position => treeJoin a.bucket.val a.layer.val a.owner.val height position

/-- A private owner subtree, retaining guard predecessors at every leaf and
excluding the shared successor roots at nonfinal-layer links. -/
def privateSubtreeBarrier (a : OwnerAddress) : Nat → Nat → Nat → Prop
  | 0, position =>
      if h : position < 32 then leafBarrier a ⟨position, h⟩ else fun _ => False
  | height + 1, position =>
      if h : height < 5 then
        let level : Depth := ⟨height, h⟩
        let left := edgePrefixBarrier a level (2 * position) ⟨8, by decide⟩
          (privateSubtreeBarrier a height (2 * position))
        let right := edgePrefixBarrier a level (2 * position + 1) ⟨8, by decide⟩
          (privateSubtreeBarrier a height (2 * position + 1))
        fun i => i = treeJoin a.bucket.val a.layer.val a.owner.val height position ∨
          (left i ∨ right i)
      else fun _ => False

instance privateSubtreeBarrier_decidable (a : OwnerAddress) (height position i : Nat) :
    Decidable (privateSubtreeBarrier a height position i) := by
  induction height generalizing position i with
  | zero =>
      unfold privateSubtreeBarrier
      split
      · unfold leafBarrier guardPrefix
        infer_instance
      · infer_instance
  | succ height ih =>
      unfold privateSubtreeBarrier
      split
      · dsimp only
        letI : DecidablePred (privateSubtreeBarrier a height (2 * position)) :=
          fun j => ih (2 * position) j
        letI : DecidablePred (privateSubtreeBarrier a height (2 * position + 1)) :=
          fun j => ih (2 * position + 1) j
        infer_instance
      · infer_instance

theorem privateSubtreeRoot_mem (a : OwnerAddress) (height position : Nat)
    (hh : height ≤ 5) (hp : position < 2 ^ (5 - height)) :
    privateSubtreeBarrier a height position (privateSubtreeRoot a height position) := by
  cases height with
  | zero =>
      have hpos : position < 32 := by simpa using hp
      simp only [privateSubtreeBarrier, dif_pos hpos, privateSubtreeRoot, leafBarrier]
      exact Or.inl trivial
  | succ height =>
      have hheight : height < 5 := by omega
      simp only [privateSubtreeBarrier, dif_pos hheight, privateSubtreeRoot]
      exact Or.inl trivial

theorem privateSubtreeRoot_treeChild (a : OwnerAddress) (height position : Nat) :
    privateSubtreeRoot a height position =
      treeChild a.bucket.val a.layer.val a.owner.val height position := by
  cases height <;> simp [privateSubtreeRoot, treeChild]

set_option maxHeartbeats 3000000 in
theorem privateSubtreeBarrier_barrier (a : OwnerAddress) (height position : Nat)
    (hh : height ≤ 5) (hp : position < 2 ^ (5 - height)) :
    BackwardBarrier graph (privateSubtreeBarrier a height position) := by
  induction height generalizing position with
  | zero =>
      have hpos : position < 32 := by simpa using hp
      simp only [privateSubtreeBarrier, dif_pos hpos]
      exact leafBarrier_barrier a ⟨position, hpos⟩
  | succ height ih =>
      have hheight : height < 5 := by omega
      let level : Depth := ⟨height, hheight⟩
      have hpos : position < 2 ^ (4 - height) := by
        have hexp : 5 - (height + 1) = 4 - height := by omega
        simpa only [hexp] using hp
      have hleft : 2 * position < 2 ^ (5 - height) := by
        interval_cases height <;> norm_num at * <;> omega
      have hright : 2 * position + 1 < 2 ^ (5 - height) := by
        interval_cases height <;> norm_num at * <;> omega
      have hleftBase := ih (2 * position) (by omega) hleft
      have hrightBase := ih (2 * position + 1) (by omega) hright
      have hleftRoot : privateSubtreeBarrier a height (2 * position)
          (treeChild a.bucket.val a.layer.val a.owner.val height (2 * position)) := by
        rw [← privateSubtreeRoot_treeChild]
        exact privateSubtreeRoot_mem a height (2 * position) (by omega) hleft
      have hrightRoot : privateSubtreeBarrier a height (2 * position + 1)
          (treeChild a.bucket.val a.layer.val a.owner.val height (2 * position + 1)) := by
        rw [← privateSubtreeRoot_treeChild]
        exact privateSubtreeRoot_mem a height (2 * position + 1) (by omega) hright
      have hleftEdge := edgePrefixBarrier_barrier a level (2 * position) ⟨8, by decide⟩
        (by simpa only [level, Fin.val_mk] using hleft) hleftBase hleftRoot
      have hrightEdge := edgePrefixBarrier_barrier a level (2 * position + 1) ⟨8, by decide⟩
        (by simpa only [level, Fin.val_mk] using hright) hrightBase hrightRoot
      have hleftEnd : edgePrefixBarrier a level (2 * position) ⟨8, by decide⟩
          (privateSubtreeBarrier a height (2 * position))
          (treeJoin a.bucket.val a.layer.val a.owner.val height position - 9) := by
        apply Or.inr
        refine ⟨8, by decide, by decide, ?_⟩
        simp only [treeJoin, edgePointVertex, level, Fin.val_mk]
        norm_num
        omega
      have hjoin := treeJoinBarrier_barrier a level position
        (by simpa only [level, Fin.val_mk] using hpos) hleftEdge hrightEdge hleftEnd
      simpa only [privateSubtreeBarrier, dif_pos hheight, level, Fin.val_mk] using hjoin

def privateEdgeBarrier (a : OwnerAddress) (level : Depth) (childPosition : Nat)
    (point : Fin 9) : Nat → Prop :=
  edgePrefixBarrier a level childPosition point
    (privateSubtreeBarrier a level.val childPosition)

instance privateEdgeBarrier_decidable (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9) (i : Nat) :
    Decidable (privateEdgeBarrier a level childPosition point i) := by
  unfold privateEdgeBarrier
  infer_instance

theorem privateEdgeBarrier_barrier (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9)
    (hchild : childPosition < 2 ^ (5 - level.val)) :
    BackwardBarrier graph (privateEdgeBarrier a level childPosition point) := by
  have hl := level.isLt
  apply edgePrefixBarrier_barrier a level childPosition point hchild
    (privateSubtreeBarrier_barrier a level.val childPosition (by omega) hchild)
  rw [← privateSubtreeRoot_treeChild]
  exact privateSubtreeRoot_mem a level.val childPosition (by omega) hchild

theorem privateEdgeBarrier_mem (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9)
    (hchild : childPosition < 2 ^ (5 - level.val)) :
    privateEdgeBarrier a level childPosition point
      (edgePointVertex a.bucket.val a.layer.val a.owner.val level.val childPosition point.val) := by
  by_cases hp : point.val = 0
  · apply Or.inl
    simp only [edgePointVertex, hp, ↓reduceIte]
    rw [← privateSubtreeRoot_treeChild]
    exact privateSubtreeRoot_mem a level.val childPosition (by have h := level.isLt; omega) hchild
  · exact Or.inr ⟨point, by omega, le_rfl, rfl⟩

set_option maxHeartbeats 3000000 in
theorem privateSubtreeBarrier_in_owner (a : OwnerAddress) (height position : Nat)
    (hh : height ≤ 5) (hp : position < 2 ^ (5 - height)) (i : Nat)
    (hi : privateSubtreeBarrier a height position i) : InOwner a i := by
  induction height generalizing position i with
  | zero =>
      have hpos : position < 32 := by simpa using hp
      simp only [privateSubtreeBarrier, dif_pos hpos] at hi
      exact leafBarrier_in_owner a ⟨position, hpos⟩ i hi
  | succ height ih =>
      have hheight : height < 5 := by omega
      let level : Depth := ⟨height, hheight⟩
      have hpos : position < 2 ^ (4 - height) := by
        have hexp : 5 - (height + 1) = 4 - height := by omega
        simpa only [hexp] using hp
      have hleft : 2 * position < 2 ^ (5 - height) := by
        interval_cases height <;> norm_num at * <;> omega
      have hright : 2 * position + 1 < 2 ^ (5 - height) := by
        interval_cases height <;> norm_num at * <;> omega
      simp only [privateSubtreeBarrier, dif_pos hheight] at hi
      rcases hi with rfl | hleftHit | hrightHit
      · exact treeJoin_in_owner a level position hpos
      · exact edgePrefixBarrier_in_owner a level (2 * position) ⟨8, by decide⟩ hleft
          (fun j hj => ih (2 * position) (by omega) hleft j hj) i hleftHit
      · exact edgePrefixBarrier_in_owner a level (2 * position + 1) ⟨8, by decide⟩ hright
          (fun j hj => ih (2 * position + 1) (by omega) hright j hj) i hrightHit

theorem privateEdgeBarrier_in_owner (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9)
    (hchild : childPosition < 2 ^ (5 - level.val)) (i : Nat)
    (hi : privateEdgeBarrier a level childPosition point i) : InOwner a i := by
  exact edgePrefixBarrier_in_owner a level childPosition point hchild
    (fun j hj => privateSubtreeBarrier_in_owner a level.val childPosition
      (by have hl := level.isLt; omega) hchild j hj) i hi

theorem privateEdgeBarrier_excludes_root (a : OwnerAddress) (level : Depth)
    (childPosition : Nat) (point : Fin 9)
    (hchild : childPosition < 2 ^ (5 - level.val)) :
    ¬privateEdgeBarrier a level childPosition point (graph.length - 1) := by
  intro hroot
  exact root_not_in_owner a
    (privateEdgeBarrier_in_owner a level childPosition point hchild _ hroot)

theorem covered_edge_requires_private_disclosure (s : Scheme) (hs : List Nat)
    (target : Nat) (a : OwnerAddress) (level : Depth) (childPosition : Nat)
    (point : Fin 9) (hchild : childPosition < 2 ^ (5 - level.val))
    (hgraph : s.graph = graph)
    (houtputs : s.encoder.outputs.length = 1 + 2 * s.graph.length)
    (htarget : get (s.frontier target)
      (edgePointVertex a.bucket.val a.layer.val a.owner.val
        level.val childPosition point.val) = true)
    (hcovered : s.covered hs target = true) :
    ∃ raw ∈ hs, ∃ i, privateEdgeBarrier a level childPosition point i ∧
      get (s.frontier raw) i = true := by
  let vertex := edgePointVertex a.bucket.val a.layer.val a.owner.val
    level.val childPosition point.val
  have hb : BackwardBarrier s.graph (privateEdgeBarrier a level childPosition point) := by
    rw [hgraph]
    exact privateEdgeBarrier_barrier a level childPosition point hchild
  have hr : ¬privateEdgeBarrier a level childPosition point (s.graph.length - 1) := by
    rw [hgraph]
    exact privateEdgeBarrier_excludes_root a level childPosition point hchild
  have hvb : privateEdgeBarrier a level childPosition point vertex :=
    privateEdgeBarrier_mem a level childPosition point hchild
  have hv : vertex < s.graph.length := by
    rw [hgraph]
    exact (privateEdgeBarrier_in_owner a level childPosition point hchild vertex hvb).lt_graph
  obtain ⟨raw, hraw, hav⟩ := covered_requires_barrier_hit s hs target vertex
    houtputs hb hr hv hvb htarget hcovered
  obtain ⟨i, hblocked, hget⟩ := not_avoids_witness hav
  exact ⟨raw, hraw, i, hblocked, hget⟩

/-- Concrete private-guard necessity for the protected covering event. A
public root, authenticated successor root, or a join of separate histories
cannot replace an actual disclosure somewhere in this private prefix. -/
theorem covered_guard_requires_private_disclosure (s : Scheme) (hs : List Nat)
    (target : Nat) (a : OwnerAddress) (slot : Slot) (point : Fin 9)
    (hgraph : s.graph = graph)
    (houtputs : s.encoder.outputs.length = 1 + 2 * s.graph.length)
    (htarget : get (s.frontier target) (guardVertex a slot point) = true)
    (hcovered : s.covered hs target = true) :
    ∃ raw ∈ hs, ∃ i, guardPrefix a slot point i ∧ get (s.frontier raw) i = true := by
  have hb : BackwardBarrier s.graph (guardPrefix a slot point) := by
    rw [hgraph]
    exact guardPrefix_barrier a slot point
  have hr : ¬guardPrefix a slot point (s.graph.length - 1) := by
    rw [hgraph]
    exact guardPrefix_excludes_root a slot point
  have hi : guardVertex a slot point < s.graph.length := by
    rw [hgraph]
    simpa only [graph_length, fixed_geometry.2.2.2.1] using guardVertex_lt a slot point
  have hib : guardPrefix a slot point (guardVertex a slot point) := by
    dsimp [guardPrefix, guardStart, guardVertex]
    omega
  obtain ⟨raw, hraw, hav⟩ := covered_requires_barrier_hit s hs target
    (guardVertex a slot point) houtputs hb hr hi hib htarget hcovered
  obtain ⟨i, hblocked, hget⟩ := not_avoids_witness hav
  exact ⟨raw, hraw, i, hblocked, hget⟩

end PoissonDAG.GRSCC
