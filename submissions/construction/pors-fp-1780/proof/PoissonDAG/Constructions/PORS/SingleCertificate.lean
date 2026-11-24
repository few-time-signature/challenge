import PoissonDAG.Constructions.PORS.SingleRoutes
import PoissonDAG.Constructions.PORS.SingleOpeningCosts
import PoissonDAG.Constructions.PORS.SingleCoverageLiteral
import PoissonDAG.Constructions.PORS.LiteralAssembly

namespace PoissonDAG.PORS.SingleCertificate
open Literal LiteralMaskSemantics SingleProgram SingleRefined PrunedCount

private theorem forest_leaf : shape p.K = .leaf := rfl
private theorem outer_leaf : shape p.buckets = .leaf := rfl
private theorem zero_cap : p.cap = 0 := rfl

attribute [local irreducible] Literal.scheme Literal.shape Scheme.accepted Scheme.coverCoefficient

private theorem agrees_depth (s : Shape) (hit : Nat → Bool) (u : Finset (Leaf s))
    (ag : ∀ x, hit (leafIndex s x).val = true ↔ x ∈ u) :
    SingleOpeningCosts.Agrees s 0 (asDepth hit 0) u := by
  intro x
  simp only [Nat.zero_add]
  have h := ag x
  cases he : hit (leafIndex s x).val <;> simpa [asDepth,he] using h

private theorem bounds {raw : Nat} (h : raw ∈ single.accepted) :
    weight (single.frontier raw) ≤ 111 ∧ single.verifyCalls raw ≤ 121 := by
  obtain ⟨_,cut⟩ := facts.info raw h
  obtain ⟨a,ha,hf,hp⟩ := facts.route raw h
  exact SingleOpeningCosts.single_bounds raw _ _ _
    (agrees_depth _ _ _ (facts.agrees raw h)) ha hf hp (facts.weight raw h) cut

private theorem depths_colex (t k dom raw : Nat) (hd : raw < dom) :
    asDepth (readHit t k dom raw) = SingleOpeningSources.zeroDepth (Colex.digits t k raw).toFinset := by
  funext coord i
  simp [asDepth,readHit,Nat.mod_eq_of_lt hd,SingleOpeningSources.zeroDepth]

private theorem replace_depth {s : Shape} {d e : Nat → Nat → Option Nat}
    {a : Opening (s.fill (chain 1))} (he : d=e)
    (route : routedOpening .leaf .leaf s 0 (fun _ => 0) d = some a) :
    routedOpening .leaf .leaf s 0 (fun _ => 0) e = some a := he ▸ route

private theorem source_code : SingleCover.SourceCode single 9 := by
  apply SingleOpeningSources.single_code_of_colex
  · intro raw h
    rw [Nat.choose_eq_fast_choose]; exact (facts.info raw h).1
  · intro raw h
    obtain ⟨a,ha,hf,_⟩ := facts.route raw h
    exact ⟨a,replace_depth (depths_colex _ _ _ raw (facts.info raw h).1) ha,hf⟩

/-- Every resource and covering predicate is checked on the protected
Boolean circuit and addressed graph of the single-tree construction. -/
theorem certificate : V2.ConstructionCertificate single 1780 := by
  apply single_conditional
  exact { count := count
          work := fun _ h => (bounds h).2
          labels := fun _ h => (bounds h).1
          traversal := fun _ h => by
            obtain ⟨a,ha,hf,hp⟩ := facts.route _ h
            unfold rowTree
            rw [forest_leaf,outer_leaf,zero_cap]
            exact ⟨fun _ => 0,_,a,ha,hf,hp⟩
          historicalCount := SingleCover.single_historicalCount count source_code }

#print axioms certificate

end PoissonDAG.PORS.SingleCertificate
