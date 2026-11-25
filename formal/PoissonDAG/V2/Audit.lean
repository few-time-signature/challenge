import PoissonDAG.V2.OpeningLowerBound
import Mathlib.Tactic.FinCases

namespace PoissonDAG.V2

/-- The scan treats a supplied vertex as a leaf of its computation. -/
theorem Uses.atInput {g f k label node} (h : Uses g f k label node)
    (hn : get f node = true) : label = node := by
  cases h with
  | input => rfl
  | hash _ hf _ _ => simp_all

private theorem Uses.atUnary {g f k label node c} (h : Uses g f k label node)
    (hn : get f node = false) (hr : g[node]? = some (.unary c))
    (hc : get f c = true) : label = c := by
  cases h with
  | input he => simp_all
  | hash hp _ _ edge =>
    have eq := (show _ = c from by simpa [IsParent, hr] using edge)
    exact (hp.atInput (by simpa only [eq] using hc)).trans eq

/-- When the sole root input is supplied, it must be the only disclosure. -/
theorem onlyInputOfUnaryRoot {g f plan c} (h : Authenticated g f plan)
    (hr : g[g.length - 1]? = some (.unary c)) (hc : get f c = true)
    (i : Fin g.length) (hi : get f i = true) : i.val = c := by
  exact (h.2.2 i hi).atUnary h.1 hr hc

private def tree : List Node := [.source, .source, .binary 0 1, .unary 2]

/-- Both leaves feed the binary hash, then the unary public root. -/
theorem twoLeaves : Authenticated tree [true, true, false, false] [false, false, true, true] := by
  refine ⟨by decide, by decide, ?_⟩
  intro leaf h
  change Fin 4 at leaf
  fin_cases leaf
  · exact .hash (parent := 2) (.hash (.input h) (by decide) (by decide) (Or.inl rfl))
      (by decide) (by decide) rfl
  · exact .hash (parent := 2) (.hash (.input h) (by decide) (by decide) (Or.inr rfl))
      (by decide) (by decide) rfl
  all_goals contradiction

/-- Supplying the intermediate cuts off the path from leaf zero. -/
theorem unusedLeaf : ¬ Authenticated tree [true, false, true, false] [false, false, false, true] := by
  intro h
  have impossible := onlyInputOfUnaryRoot (c := 2) h (by decide) (by decide) ⟨0, by decide⟩ (by decide)
  exact (by decide : (0 : Nat) ≠ 2) impossible

example : ¬ Authenticated [.source] [true] [false] := by
  intro h
  exact Bool.noConfusion h.1

/-- Supplying an intermediate is legitimate if a second root input actually reads its parent. -/
example : Authenticated [.source, .unary 0, .binary 0 1] [true, true, false] [false, true, true] := by
  refine ⟨by decide, by decide, ?_⟩
  intro leaf h
  fin_cases leaf
  · exact .hash (.input h) (by decide) (by decide) (Or.inl rfl)
  · exact .hash (.input h) (by decide) (by decide) (Or.inr rfl)
  all_goals contradiction

example : ¬ Authenticated tree [true, true, false, false] [false, false, false, true] := by
  intro h
  exact Bool.noConfusion h.2.1

example : PoissonDAG.V2.UniversalLowerBound 99 := PoissonDAG.V2.openingLowerBound
#check PoissonDAG.V2.ConstructionCertificate
/-- info: 'PoissonDAG.V2.openingLowerBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PoissonDAG.V2.openingLowerBound
#print axioms PoissonDAG.V2.ofBaseConstruction
#print axioms onlyInputOfUnaryRoot
#print axioms twoLeaves
#print axioms unusedLeaf

end PoissonDAG.V2
