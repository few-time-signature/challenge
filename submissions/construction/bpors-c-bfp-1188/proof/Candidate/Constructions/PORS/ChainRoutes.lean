import Candidate.Constructions.PORS.ChainOpeningCosts
import Candidate.Constructions.PORS.ChainRankGate
import PoissonDAG.Constructions.PORS.LiteralAssembly

section

namespace PoissonDAG.PORS.ChainCoord

def fourShape : Shape := .branch (.branch .leaf .leaf) (.branch .leaf .leaf)

def fourOpen {t : Tree} (a b c d : Opening t) : Opening (fourShape.fill t) :=
  .join (.join a b) (.join c d)

theorem routed_four (outer child : Shape) (cap : Nat) (bucket : Nat → Nat) (depth : Nat → Nat → Option Nat)
    {a b c d : Opening (outer.fill (child.fill (chain (cap+1))))}
    (r0 : routedOpening .leaf outer child cap (fun _ => bucket 0) (fun _ => depth 0)=some a)
    (r1 : routedOpening .leaf outer child cap (fun _ => bucket 1) (fun _ => depth 1)=some b)
    (r2 : routedOpening .leaf outer child cap (fun _ => bucket 2) (fun _ => depth 2)=some c)
    (r3 : routedOpening .leaf outer child cap (fun _ => bucket 3) (fun _ => depth 3)=some d) :
    routedOpening fourShape outer child cap bucket depth=some (fourOpen a b c d) := by
  let co := fun i => openSelected (child.fill (chain (cap+1))) (fun j =>
    if j=bucket i then openSelected (chain (cap+1))
      (fun x => (depth i x).map (fun e => openChain (cap+1) (cap-e))) child 0 else none) outer 0
  change co 0=some a at r0
  change co 1=some b at r1
  change co 2=some c at r2
  change co 3=some d at r3
  change openSelected _ co fourShape 0=some (fourOpen a b c d)
  simp only [fourShape,fourOpen,openSelected,Shape.leaves,Nat.zero_add,
    show (1:Nat)+1=2 by decide,show (2:Nat)+1=3 by decide,r0,r1,r2,r3]

open LiteralMaskSemantics in
theorem four_masks {t : Tree} (a b c d : Opening t) (A B C D : View)
    (a0 : A.active=true) (a1 : B.active=true) (a2 : C.active=true) (a3 : D.active=true)
    (m0 : A.prefixMarks++[A.root]=a.marks) (m1 : B.prefixMarks++[B.root]=b.marks)
    (m2 : C.prefixMarks++[C.root]=c.marks) (m3 : D.prefixMarks++[D.root]=d.marks) :
    let v := joinView false (joinView false A B) (joinView false C D)
    v.active=true ∧ v.count=A.count+B.count+C.count+D.count ∧
      v.prefixMarks++[v.root]=(fourOpen a b c d).marks := by
  obtain ⟨al,cl,ml⟩ := BucketCoord.live_join a b A B a0 a1 m0 m1
  obtain ⟨ar,cr,mr⟩ := BucketCoord.live_join c d C D a2 a3 m2 m3
  obtain ⟨af,cf,mf⟩ := BucketCoord.live_join (.join a b) (.join c d) _ _ al ar ml mr
  exact ⟨af,by rw [cf,cl,cr]; omega,mf⟩

/-- Four coordinate plans together require exactly three binary hashes above
the coordinate roots. -/
theorem four_weights {t : Tree} (a b c d : Opening t) (s0 s1 s2 s3 : Nat)
    (h0 : weight (a.marks.map Prod.fst)=14+s0 ∧ weight (a.marks.map Prod.snd)=49+s0)
    (h1 : weight (b.marks.map Prod.fst)=14+s1 ∧ weight (b.marks.map Prod.snd)=49+s1)
    (h2 : weight (c.marks.map Prod.fst)=14+s2 ∧ weight (c.marks.map Prod.snd)=49+s2)
    (h3 : weight (d.marks.map Prod.fst)=14+s3 ∧ weight (d.marks.map Prod.snd)=49+s3) :
    weight ((fourOpen a b c d).marks.map Prod.fst)=56+s0+s1+s2+s3 ∧
    weight ((fourOpen a b c d).marks.map Prod.snd)=199+s0+s1+s2+s3 := by
  have sj {l r : Tree} (x : Opening l) (y : Opening r) :
      weight ((Opening.join x y).marks.map Prod.fst) =
      weight (x.marks.map Prod.fst)+weight (y.marks.map Prod.fst) := by simp [Opening.marks,weight]
  have wj {l r : Tree} (x : Opening l) (y : Opening r) :
      weight ((Opening.join x y).marks.map Prod.snd) =
      weight (x.marks.map Prod.snd)+weight (y.marks.map Prod.snd)+1 := by
    simp [Opening.marks,weight,Nat.add_assoc]
  have hs : weight ((fourOpen a b c d).marks.map Prod.fst)=_ := sj (.join a b) (.join c d)
  have hw : weight ((fourOpen a b c d).marks.map Prod.snd)=_ := wj (.join a b) (.join c d)
  rw [hs,hw,sj a b,sj c d,wj a b,wj c d]
  omega

/-- At most 74 labels and 219 actual verification hashes, including the
two message-digest calls, at the total inner sibling cutoff of 18. -/
theorem four_resources (scheme : Scheme) (raw : Nat) {t : Tree} (a b c d : Opening t)
    (graph : scheme.graph=(fourShape.fill t).emit 0)
    (frontier : scheme.frontier raw=(fourOpen a b c d).marks.map Prod.fst)
    (plan : scheme.plan raw=(fourOpen a b c d).marks.map Prod.snd) (digest : scheme.digestCalls=2)
    (s0 s1 s2 s3 : Nat)
    (h0 : weight (a.marks.map Prod.fst)=14+s0 ∧ weight (a.marks.map Prod.snd)=49+s0)
    (h1 : weight (b.marks.map Prod.fst)=14+s1 ∧ weight (b.marks.map Prod.snd)=49+s1)
    (h2 : weight (c.marks.map Prod.fst)=14+s2 ∧ weight (c.marks.map Prod.snd)=49+s2)
    (h3 : weight (d.marks.map Prod.fst)=14+s3 ∧ weight (d.marks.map Prod.snd)=49+s3)
    (cutoff : s0+s1+s2+s3 ≤ 18) :
    weight (scheme.frontier raw) ≤ 74 ∧ scheme.verifyCalls raw ≤ 219 := by
  obtain ⟨hf,hp⟩ := four_weights a b c d s0 s1 s2 s3 h0 h1 h2 h3
  have len : (scheme.plan raw).length=scheme.graph.length := by
    rw [plan,graph,List.length_map,Opening.mark_length,Tree.emit_length]
  have scan := close_calls_le_weight scheme.graph (scheme.frontier raw) (scheme.plan raw) len
  rw [← frontier] at hf
  rw [← plan] at hp
  unfold Scheme.verifyCalls
  omega

end PoissonDAG.PORS.ChainCoord
end

section

namespace PoissonDAG.PORS.ChainRoutes

open Literal LiteralMaskSemantics ChainProgram ChainRefined PrunedCount

def owner (raw i : Nat) := (coord raw i).bucket
def depth (raw i j : Nat) := (pairs raw i).lookup j
noncomputable def siblingCount (raw i : Nat) := siblings child (ChainRankGate.support raw i)

abbrev coordTree := outer.fill (child.fill (chain (p.cap+1)))
private theorem forest_four : shape p.K=ChainCoord.fourShape := rfl
private theorem graph_eq (row : Row) : (scheme row).graph =
    ((shape row.K).fill ((shape row.buckets).fill ((shape row.t).fill (chain (row.cap+1))))).emit 0 := rfl

attribute [local irreducible] Literal.shape Literal.scheme Scheme.accepted

theorem owner_bound (raw i : Nat) : owner raw i < p.buckets := Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem id_bound (raw i : Nat) (z : Nat×Nat) (hz : z∈pairs raw i) : z.1<24 := by
  have hl : z.1 ∈ (coord raw i).leaves := (List.of_mem_zip hz).1
  change z.1∈(Colex.digits p.t p.k (ChainRankGate.supportRank raw i)).reverse at hl
  exact (Colex.digits_spec (Nat.le_refl p.t) (ChainRankGate.support_fit raw i)).2.1 z.1
    (List.mem_reverse.mp hl)

theorem depth_agrees (raw i : Nat) :
    SingleOpeningCosts.Agrees child 0 (depth raw i) (ChainRankGate.support raw i) := by
  intro x
  rw [Nat.zero_add,← ChainRankGate.agrees raw i x]
  simp only [depth,List.lookup_isSome_iff,beq_iff_eq,ChainLeafGates.live,List.any_eq_true,decide_eq_true_eq]
  constructor <;> rintro ⟨z,hz,eq⟩ <;> exact ⟨z,hz,eq.symm⟩

/-- A decoded coordinate carries its exact leaf positions and four residuals
from the literal gate program through its selected outer bucket. -/
theorem coordinate_opening (raw i : Nat) :
    ∃ a : Opening coordTree,
      routedOpening .leaf outer child p.cap (fun _ => owner raw i) (fun _ => depth raw i)=some a ∧
      (atCoordView raw i).active=true ∧ (atCoordView raw i).prefixMarks++[(atCoordView raw i).root]=a.marks ∧
      weight (a.marks.map Prod.fst)=14+siblingCount raw i ∧ weight (a.marks.map Prod.snd)=49+siblingCount raw i := by
  have size : (ChainRankGate.support raw i).card=4 := ChainRankGate.support_weight raw i
  have idx : owner raw i<outer.leaves := by
    rw [shape_card p.buckets (by decide)]
    exact owner_bound raw i
  obtain ⟨_,active,a,route,marks⟩ := ChainCoord.routed_coord p.cap (pairs raw i) child outer (owner raw i)
    (ChainRankGate.distinct raw i) (ChainRankGate.depth_bound raw i) (ChainRankGate.support raw i)
    (ChainRankGate.agrees raw i) (by omega) idx
  have w := ChainCoord.production_weights (pairs raw i) (owner raw i) (ChainRankGate.distinct raw i)
    (ChainRankGate.depth_bound raw i) (id_bound raw i) _ (depth_agrees raw i) size
    (ChainRankGate.total_depth raw i) (owner_bound raw i) route
  exact ⟨a,route,active,marks,w⟩

private theorem accepted_info {raw : Nat} (hm : raw∈(scheme p).accepted) :
    raw<2^p.r ∧ siblingCount raw 0+siblingCount raw 1+siblingCount raw 2+siblingCount raw 3 ≤ 18 := by
  unfold Scheme.accepted Scheme.raws at hm
  obtain ⟨h,keep⟩ := List.mem_filter.mp hm
  have hr := List.mem_range.mp h
  rw [literal_inputs] at hr
  rw [(protected_output raw hr).1] at keep
  change decide (raw<p.domain ∧ (view raw).count ≤ p.M)=true at keep
  have cut := (of_decide_eq_true keep).2
  rw [ChainRankGate.view_count] at cut
  change (∑ i : Fin 4, siblingCount raw i.val) ≤ 18 at cut
  simp [Fin.sum_univ_succ,Nat.add_assoc] at cut
  exact ⟨hr,by simpa [Nat.add_assoc] using cut⟩

private theorem joined_graph : (scheme p).graph=(ChainCoord.fourShape.fill coordTree).emit 0 := by
  rw [graph_eq,forest_four]

/-- The protected frontier and hash plan are the complete postorder marks of
one four-coordinate opening, including every decoded chain and outer path. -/
theorem accepted_opening {raw : Nat} (hm : raw∈(scheme p).accepted) :
    ∃ a : Opening (rowTree p), routedOpening forest outer child p.cap (owner raw) (depth raw)=some a ∧
      (scheme p).frontier raw=a.marks.map Prod.fst ∧ (scheme p).plan raw=a.marks.map Prod.snd ∧
      weight ((scheme p).frontier raw) ≤ 74 ∧ (scheme p).verifyCalls raw ≤ 219 := by
  obtain ⟨hr,cut⟩ := accepted_info hm
  obtain ⟨a,h0,l0,m0,w0⟩ := coordinate_opening raw 0
  obtain ⟨b,h1,l1,m1,w1⟩ := coordinate_opening raw 1
  obtain ⟨c,h2,l2,m2,w2⟩ := coordinate_opening raw 2
  obtain ⟨d,h3,l3,m3,w3⟩ := coordinate_opening raw 3
  have route := ChainCoord.routed_four outer child p.cap (owner raw) (depth raw) h0 h1 h2 h3
  have mv := (ChainCoord.four_masks a b c d _ _ _ _ l0 l1 l2 l3 m0 m1 m2 m3).2.2
  have same : marks raw = (ChainCoord.fourOpen a b c d).marks := by
    unfold marks view forest
    rw [forest_four]
    exact mv
  have fields := (protected_output raw hr).2
  have front := fields.1.trans (congrArg (List.map Prod.fst) same)
  have plan := fields.2.trans (congrArg (List.map Prod.snd) same)
  have digest : (scheme p).digestCalls=2 := by rw [Scheme.digestCalls,literal_inputs]; decide
  have bounds := ChainCoord.four_resources (scheme p) raw a b c d joined_graph front plan digest
    (siblingCount raw 0) (siblingCount raw 1) (siblingCount raw 2) (siblingCount raw 3) w0 w1 w2 w3 cut
  unfold rowTree forest
  rw [forest_four]
  exact ⟨ChainCoord.fourOpen a b c d,route,front,plan,bounds⟩

theorem resources {raw : Nat} (hm : raw∈(scheme p).accepted) :
    weight ((scheme p).frontier raw) ≤ 74 ∧ (scheme p).verifyCalls raw ≤ 219 := by
  obtain ⟨_,_,_,_,h⟩ := accepted_opening hm
  exact h

theorem traversal {raw : Nat} (hm : raw∈(scheme p).accepted) :
    ∃ a : Opening (rowTree p), routedOpening forest outer child p.cap (owner raw) (depth raw)=some a ∧
      (scheme p).frontier raw=a.marks.map Prod.fst ∧ (scheme p).plan raw=a.marks.map Prod.snd := by
  obtain ⟨a,h,f,pl,_⟩ := accepted_opening hm
  exact ⟨a,h,f,pl⟩

end PoissonDAG.PORS.ChainRoutes
end
