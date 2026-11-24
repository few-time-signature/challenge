import Candidate.Constructions.PORS.PrunedCount
import PoissonDAG.Constructions.PORS.RoutedOpening

namespace PoissonDAG.PORS.SingleOpeningCosts

open PrunedCount

set_option allowUnsafeReducibility true in
attribute [local reducible] Leaf Shape.fill

private def supplied {t : Tree} (a : Opening t) := weight (a.marks.map Prod.fst)
private def planned {t : Tree} (a : Opening t) := weight (a.marks.map Prod.snd)

private theorem supplied_stop (t : Tree) : supplied (.stop t) = 1 := by
  simp [supplied, Opening.marks, weight, List.count_replicate]

private theorem planned_stop (t : Tree) : planned (.stop t) = 0 := by
  simp [planned, Opening.marks, weight, List.count_replicate]

private theorem supplied_join {l r : Tree} (a : Opening l) (b : Opening r) :
    supplied (.join a b) = supplied a + supplied b := by
  simp [supplied, Opening.marks, weight]

private theorem planned_join {l r : Tree} (a : Opening l) (b : Opening r) :
    planned (.join a b) = planned a + planned b + 1 := by
  simp [planned, Opening.marks, weight, Nat.add_assoc]

private def start (d : Nat → Option Nat) (j : Nat) : Option (Opening (chain 1)) :=
  (d j).map fun e => openChain 1 (0-e)

/-- Identify an ordinary leaf subset with the active decoded leaf addresses. -/
def Agrees (s : Shape) (off : Nat) (d : Nat → Option Nat) (u : Finset (Leaf s)) : Prop :=
  ∀ x, (d (off + (leafIndex s x).val)).isSome = true ↔ x ∈ u

private def Stats (s : Shape) (u : Finset (Leaf s)) :
    Option (Opening (s.fill (chain 1))) → Prop
  | none => u.card = 0 ∧ siblings s u = 0
  | some a => 0 < u.card ∧ supplied a = u.card + siblings s u ∧
      planned a + 1 = 2*u.card + siblings s u

/-- The number of labels is the number of selected secrets plus the number
of stopped siblings. Each selected secret adds one unary hash, and the
binary part of the traversal has one fewer join than frontier nodes. -/
private theorem selected_stats (s : Shape) (off : Nat) (d : Nat → Option Nat)
    (u : Finset (Leaf s)) (agree : Agrees s off d u) :
    Stats s u (openSelected (chain 1) (start d) s off) := by
  induction s generalizing off with
  | leaf =>
    change Finset Unit at u
    have ha := agree ()
    change (d (off+0)).isSome = true ↔ () ∈ u at ha
    rw [Nat.add_zero] at ha
    cases hd : d off with
    | none =>
      have he : u = ∅ := by
        ext x
        change x ∈ u ↔ _
        cases x
        simp [hd] at ha
        simp [ha]
      subst u
      simp [openSelected, start, hd, Stats, siblings]
    | some e =>
      have he : u = {()} := by
        ext x
        change x ∈ u ↔ _
        cases x
        simp [hd] at ha
        simp [ha]
      subst u
      simp [openSelected, start, hd, Stats, siblings, supplied, planned, openChain,
        chain, Opening.marks, weight, Tree.nodes]
  | branch l r il ir =>
    change Finset (Leaf l ⊕ Leaf r) at u
    have al : Agrees l off d u.toLeft := by
      intro x
      rw [Finset.mem_toLeft]
      exact agree (.inl x)
    have ar : Agrees r (off+l.leaves) d u.toRight := by
      intro x
      rw [Finset.mem_toRight,Nat.add_assoc]
      exact agree (.inr x)
    have hl := il off u.toLeft al
    have hr := ir (off+l.leaves) u.toRight ar
    have hcard : u.toLeft.card + u.toRight.card = u.card := Finset.card_toLeft_add_card_toRight
    cases el : openSelected (chain 1) (start d) l off <;>
      cases er : openSelected (chain 1) (start d) r (off+l.leaves) <;>
      simp only [openSelected, el, er, Stats, Shape.fill] at hl hr ⊢ <;>
      simp only [siblings, extraSibling, supplied_join, planned_join, supplied_stop, planned_stop] <;>
      split_ifs <;> (repeat' constructor) <;> omega

/-- Connect the exact weight calculation to the existing routed traversal. -/
theorem routed_weights (s : Shape) (bucket : Nat → Nat) (d : Nat → Nat → Option Nat)
    (u : Finset (Leaf s)) (agree : Agrees s 0 (d 0) u)
    {a : Opening (s.fill (chain 1))} (route : routedOpening .leaf .leaf s 0 bucket d = some a) :
    weight (a.marks.map Prod.fst) = u.card + siblings s u ∧
    weight (a.marks.map Prod.snd) + 1 = 2*u.card + siblings s u := by
  change (if 0 = bucket 0 then openSelected (chain 1) (start (d 0)) s 0 else none) =
    some a at route
  split at route
  · have h := selected_stats s 0 (d 0) u agree
    rw [route] at h
    exact h.2
  · contradiction

/-- The protected close interpreter charges at most one call for every true
plan bit. This adds the actual message-digest cost to the tree bound. -/
theorem routed_resources (scheme : Scheme) (raw : Nat) (s : Shape)
    (graph : scheme.graph = (s.fill (chain 1)).emit 0)
    (bucket : Nat → Nat) (d : Nat → Nat → Option Nat) (u : Finset (Leaf s))
    (agree : Agrees s 0 (d 0) u) {a : Opening (s.fill (chain 1))}
    (route : routedOpening .leaf .leaf s 0 bucket d = some a)
    (frontier : scheme.frontier raw = a.marks.map Prod.fst)
    (plan : scheme.plan raw = a.marks.map Prod.snd) :
    weight (scheme.frontier raw) = u.card + siblings s u ∧
    scheme.verifyCalls raw ≤ scheme.digestCalls + (2*u.card + siblings s u - 1) := by
  obtain ⟨hfront, hplan⟩ := routed_weights s bucket d u agree route
  refine ⟨by rw [frontier, hfront], ?_⟩
  have hlen : (scheme.plan raw).length = scheme.graph.length := by
    rw [plan, graph, List.length_map, Opening.mark_length, Tree.emit_length]
  have hscan := close_calls_le_weight scheme.graph (scheme.frontier raw) (scheme.plan raw) hlen
  rw [← plan] at hplan
  unfold Scheme.verifyCalls
  omega


private theorem scheme_graph (p : Row) : (Literal.scheme p).graph =
    graph (Literal.shape p.K) (Literal.shape p.buckets) (Literal.shape p.t) p.cap := rfl

private theorem one_graph (p : Row) (hf : Literal.shape p.K = .leaf)
    (hb : Literal.shape p.buckets = .leaf) (hc : p.cap=0) :
    (Literal.scheme p).graph = ((Literal.shape p.t).fill (chain 1)).emit 0 := by
  rw [scheme_graph, hf, hb, hc]
  rfl

private theorem bounds_of_row (row : Row) (child : Shape) (hc : Literal.shape row.t = child)
    (hf : Literal.shape row.K = .leaf) (hb : Literal.shape row.buckets = .leaf)
    (hz : row.cap = 0) (hd : (Literal.scheme row).digestCalls = 2)
    (raw : Nat) (bucket : Nat → Nat) (d : Nat → Nat → Option Nat) (u : Finset (Leaf child))
    (agree : Agrees child 0 (d 0) u) {a : Opening (child.fill (chain 1))}
    (route : routedOpening .leaf .leaf child 0 bucket d = some a)
    (frontier : (Literal.scheme row).frontier raw = a.marks.map Prod.fst)
    (plan : (Literal.scheme row).plan raw = a.marks.map Prod.snd)
    (hk : u.card = 9) (cutoff : siblings child u ≤ 102) :
    weight ((Literal.scheme row).frontier raw) ≤ 111 ∧ (Literal.scheme row).verifyCalls raw ≤ 121 := by
  have graph := one_graph row hf hb hz
  rw [hc] at graph
  obtain ⟨hfront,hwork⟩ := routed_resources (Literal.scheme row) raw child graph bucket d u
    agree route frontier plan
  omega

/-- At most 111 labels and 121 hashes including the digest on an accepted support. -/
private theorem digest_eq (row : Row) : (Literal.scheme row).digestCalls = row.digestCalls := rfl

def single_bounds := bounds_of_row SingleRefined.p (Literal.shape SingleRefined.p.t)
  rfl rfl rfl rfl ((digest_eq _).trans (by decide))

end PoissonDAG.PORS.SingleOpeningCosts
