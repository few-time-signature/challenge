import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Combinatorics.Enumerative.InclusionExclusion

/-! Finite bounded compositions, with an explicit guard before natural subtraction. -/
namespace PoissonDAG.BoundedCompositions

open scoped BigOperators

abbrev NatTuple (n t : Nat) := {x : Fin n → Nat // ∑ j, x j = t}

noncomputable instance (n t : Nat) : Fintype (NatTuple n t) :=
  Fintype.ofEquiv (Sym (Fin n) t) (Sym.equivNatSumOfFintype (Fin n) t)

theorem natTuple_card (n t : Nat) :
    Fintype.card (NatTuple n t) = (n + t - 1).choose t := by
  rw [← Fintype.card_congr (Sym.equivNatSumOfFintype (Fin n) t)]
  simpa using (Sym.card_sym_eq_choose (α := Fin n) t)

noncomputable def boundedTupleCount (n t : Nat) (b : Fin n → Nat) : Nat := by
  classical
  exact Fintype.card {x : NatTuple n t // ∀ j, x.val j < b j}

def boundSum {n : Nat} (b : Fin n → Nat) (T : Finset (Fin n)) : Nat := ∑ j ∈ T, b j

def residualCount (n t B : Nat) : Nat :=
  if B ≤ t then (n + (t - B) - 1).choose (t - B) else 0

private def shiftEquiv {n t : Nat} (c : Fin n → Nat) (hc : (∑ j, c j) ≤ t) :
    {x : NatTuple n t // ∀ j, c j ≤ x.val j} ≃ NatTuple n (t - ∑ j, c j) where
  toFun x := ⟨fun j => x.val.val j - c j, by
    rw [Finset.sum_tsub_distrib _ (fun j _ => x.property j), x.val.property]⟩
  invFun y := ⟨⟨fun j => y.val j + c j, by
    rw [Finset.sum_add_distrib, y.property, Nat.sub_add_cancel hc]⟩,
    fun j => Nat.le_add_left _ _⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    exact Nat.sub_add_cancel (x.property j)
  right_inv y := by
    apply Subtype.ext
    funext j
    exact Nat.add_sub_cancel _ _

private theorem lowerTuple_card {n t : Nat} (c : Fin n → Nat) :
    Fintype.card {x : NatTuple n t // ∀ j, c j ≤ x.val j} =
      residualCount n t (∑ j, c j) := by
  classical
  unfold residualCount
  split_ifs with hc
  · rw [Fintype.card_congr (shiftEquiv c hc), natTuple_card]
  · haveI : IsEmpty {x : NatTuple n t // ∀ j, c j ≤ x.val j} := ⟨by
      intro x
      exact hc ((Finset.sum_le_sum (fun j _ => x.property j)).trans_eq x.val.property)⟩
    simp

private theorem mem_inf {I X : Type} [DecidableEq I] [Fintype X] [DecidableEq X]
    (T : Finset I) (sets : I → Finset X) (x : X) :
    x ∈ T.inf sets ↔ ∀ j ∈ T, x ∈ sets j := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert j T hj ih => simp [Finset.inf_insert, Finset.inf_eq_inter, ih]

private noncomputable def badSet {n t : Nat} (b : Fin n → Nat) (j : Fin n) :
    Finset (NatTuple n t) := by
  classical
  exact Finset.univ.filter (fun x => b j ≤ x.val j)

private theorem intersection_card {n t : Nat} (b : Fin n → Nat)
    (T : Finset (Fin n)) :
    (T.inf (badSet (t := t) b)).card = residualCount n t (boundSum b T) := by
  classical
  let c : Fin n → Nat := fun j => if j ∈ T then b j else 0
  have hmem (x : NatTuple n t) :
      x ∈ T.inf (badSet b) ↔ ∀ j, c j ≤ x.val j := by
    simp only [mem_inf, badSet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j
      by_cases hj : j ∈ T <;> simp [c, hj, h]
    · intro h j hj
      simpa [c, hj] using h j
  rw [← Fintype.card_of_subtype _ hmem, lowerTuple_card]
  congr 1
  simp [c, boundSum]

theorem boundedTupleCount_eq (n t : Nat) (b : Fin n → Nat) :
    (boundedTupleCount n t b : Int) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        (-1 : Int) ^ T.card * (residualCount n t (boundSum b T) : Int) := by
  classical
  have hmem (x : NatTuple n t) :
      x ∈ (Finset.univ : Finset (Fin n)).inf (fun j => (badSet b j)ᶜ) ↔
        ∀ j, x.val j < b j := by
    simp [mem_inf, badSet]
  unfold boundedTupleCount
  rw [Fintype.card_of_subtype _ hmem,
    Finset.inclusion_exclusion_card_inf_compl]
  apply Finset.sum_congr rfl
  intro T hT
  rw [intersection_card]

noncomputable def boundedTupleCount6 (b : Fin 6 → Nat) : Nat := boundedTupleCount 6 16 b

theorem boundedTupleCount6_eq (b : Fin 6 → Nat) :
    (boundedTupleCount6 b : Int) =
      ∑ T ∈ (Finset.univ : Finset (Fin 6)).powerset,
        (-1 : Int) ^ T.card *
          (if boundSum b T ≤ 16 then (16 - boundSum b T + 5).choose 5 else 0) := by
  rw [boundedTupleCount6, boundedTupleCount_eq]
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  unfold residualCount
  split_ifs with h
  · have heq : 6 + (16 - boundSum b T) - 1 = (16 - boundSum b T) + 5 := by omega
    rw [heq]
    exact congrArg (fun k : Nat => (k : Int))
      (Nat.choose_symm_add (a := 16 - boundSum b T) (b := 5))
  · rfl

end PoissonDAG.BoundedCompositions
