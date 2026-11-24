import PoissonDAG.Constructions.PORS.BucketRankGate
import PoissonDAG.Constructions.PORS.BucketOpeningCosts
import PoissonDAG.Constructions.PORS.LiteralAssembly

namespace PoissonDAG.PORS.BucketRoutes
open Literal LiteralMaskSemantics BucketProgram BucketRefined PrunedCount

def owner (raw i : Nat) := (coord raw i).bucket
def hit (raw i j : Nat) := decide (j ∈ (coord raw i).leaves)
def depth (raw i j : Nat) := asDepth (hit raw i) i j
noncomputable def support (raw i : Nat) := SingleAccepted.leafSupport child p.k (BucketRankGate.supportRank raw i)
noncomputable def siblingCount (raw i : Nat) := siblings child (support raw i)

abbrev coordTree := outer.fill (child.fill (chain 1))
private theorem forest_pair : shape p.K = .branch .leaf .leaf := rfl
private theorem cap_zero : p.cap = 0 := rfl
private theorem graph_eq (row : Row) : (scheme row).graph =
    ((shape row.K).fill ((shape row.buckets).fill ((shape row.t).fill (chain (row.cap+1))))).emit 0 := rfl

attribute [local irreducible] Literal.shape Literal.scheme Scheme.accepted

theorem owner_bound (raw i : Nat) : owner raw i < p.buckets :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

theorem hit_agrees (raw i : Nat) (x : Leaf child) :
    hit raw i (leafIndex child x).val = true ↔ x ∈ support raw i :=
  BucketRankGate.agrees raw i x

private theorem weight_of_rank (c : Shape) (k r : Nat) (hr : r < c.leaves.choose k) :
    (SingleAccepted.leafSupport c k r).card = k := by
  have h := (Finset.mem_powersetCard.mp (Colex.support_mem hr)).2
  rwa [← SingleAccepted.address_image c k r hr, Finset.card_map] at h

theorem support_weight (raw i : Nat) : (support raw i).card = 6 := by
  have fit : BucketRankGate.supportRank raw i < child.leaves.choose p.k := by
    rw [shape_card p.t (by decide), Nat.choose_eq_fast_choose]
    exact Nat.mod_lt _ (by decide +kernel : 0<p.supports)
  exact weight_of_rank child p.k _ fit

private theorem coordinate_opening (raw i : Nat) :
    ∃ a : Opening coordTree,
      routedOpening .leaf outer child 0 (fun _ => owner raw i) (asDepth (hit raw i)) = some a ∧
      (atBucket (coord raw i)).active = true ∧
      (atBucket (coord raw i)).prefixMarks ++ [(atBucket (coord raw i)).root] = a.marks ∧
      weight (a.marks.map Prod.fst) = 16+siblingCount raw i ∧
      weight (a.marks.map Prod.snd) = 21+siblingCount raw i := by
  have size := support_weight raw i
  have nonempty : 0 < (support raw i).card := by omega
  have bound : owner raw i < outer.leaves := by
    rw [shape_card p.buckets (by decide)]
    exact owner_bound raw i
  obtain ⟨a, route, marks⟩ := BucketCoord.routed_coord child outer (owner raw i) (hit raw i)
    (support raw i) (hit_agrees raw i) nonempty bound
  have active : (inner (coord raw i)).active = true := by
    have h := (child_support child 0 (hit raw i) (support raw i)
      (fun x => by simpa only [Nat.zero_add] using hit_agrees raw i x)).1
    simpa only [inner, hit, nonempty, decide_true] using h
  have live : (atBucket (coord raw i)).active = true := by
    change (BucketCoord.outerView outer (inner (coord raw i)) (owner raw i) 0).active = true
    rw [BucketCoord.outer_active, active]
    simp [bound]
  exact ⟨a, route, live, marks,
    BucketCoord.production_coord_weights (owner raw i) (hit raw i) (support raw i)
      (hit_agrees raw i) size (owner_bound raw i) route⟩

private theorem pair_opening (raw : Nat) (hr : raw < 2^p.r) :
    ∃ a b : Opening coordTree,
      routedOpening (.branch .leaf .leaf) outer child 0 (owner raw) (depth raw) = some (.join a b) ∧
      (scheme p).frontier raw = (Opening.join a b).marks.map Prod.fst ∧
      (scheme p).plan raw = (Opening.join a b).marks.map Prod.snd ∧
      (weight (a.marks.map Prod.fst) = 16+siblingCount raw 0 ∧
        weight (a.marks.map Prod.snd) = 21+siblingCount raw 0) ∧
      (weight (b.marks.map Prod.fst) = 16+siblingCount raw 1 ∧
        weight (b.marks.map Prod.snd) = 21+siblingCount raw 1) := by
  obtain ⟨a, ha, la, ma, wa⟩ := coordinate_opening raw 0
  obtain ⟨b, hb, lb, mb, wb⟩ := coordinate_opening raw 1
  have route := BucketCoord.routed_two outer child 0 (owner raw) (depth raw) ha hb
  have same : marks raw = (Opening.join a b).marks :=
    (BucketCoord.live_join a b (atBucket (coord raw 0)) (atBucket (coord raw 1))
      la lb ma mb).2.2
  have fields := (protected_output raw hr).2
  exact ⟨a, b, route, fields.1.trans (congrArg (List.map Prod.fst) same),
    fields.2.trans (congrArg (List.map Prod.snd) same), wa, wb⟩

private theorem joined_graph : (scheme p).graph = (Tree.join coordTree coordTree).emit 0 := by
  rw [graph_eq, forest_pair, cap_zero]
  rfl

private theorem accepted_info {raw : Nat} (hm : raw ∈ (scheme p).accepted) :
    raw < 2^p.r ∧ siblingCount raw 0 + siblingCount raw 1 ≤ 61 := by
  unfold Scheme.accepted Scheme.raws at hm
  obtain ⟨h, keep⟩ := List.mem_filter.mp hm
  have hr := List.mem_range.mp h
  rw [literal_inputs] at hr
  rw [(protected_output raw hr).1] at keep
  change decide (raw < p.domain ∧ (view raw).count ≤ p.M) = true at keep
  have cut := (of_decide_eq_true keep).2
  change (inner (coord raw 0)).count + (inner (coord raw 1)).count + 0 ≤ 61 at cut
  rw [Nat.add_zero, BucketRankGate.inner_count, BucketRankGate.inner_count] at cut
  exact ⟨hr,cut⟩

/-- Every accepted raw word uses up to 93 frontier labels and 106 verifier
hashes, including the digest and the forest root. -/
theorem resources {raw : Nat} (hm : raw ∈ (scheme p).accepted) :
    weight ((scheme p).frontier raw) ≤ 93 ∧ (scheme p).verifyCalls raw ≤ 106 := by
  obtain ⟨hr, cut⟩ := accepted_info hm
  obtain ⟨a,b,_,frontier,plan,wa,wb⟩ := pair_opening raw hr
  have digest : (scheme p).digestCalls = 2 := by
    rw [Scheme.digestCalls, literal_inputs]
    decide
  exact BucketCoord.two_resources (scheme p) raw a b joined_graph frontier plan digest
    (siblingCount raw 0) (siblingCount raw 1) wa wb cut

/-- The two actual coordinate paths join to the production forest with the
decoded bucket and support functions exposed for source-label coverage. -/
theorem traversal {raw : Nat} (hm : raw ∈ (scheme p).accepted) :
    ∃ a : Opening (rowTree p),
      routedOpening (shape p.K) outer child p.cap (owner raw) (depth raw) = some a ∧
      (scheme p).frontier raw = a.marks.map Prod.fst ∧ (scheme p).plan raw = a.marks.map Prod.snd := by
  obtain ⟨a,b,route,frontier,plan,_,_⟩ := pair_opening raw (accepted_info hm).1
  unfold rowTree
  rw [forest_pair, cap_zero]
  exact ⟨.join a b, route, frontier, plan⟩

end PoissonDAG.PORS.BucketRoutes
