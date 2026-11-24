import PoissonDAG.Probability.SamplePaths
import Mathlib.Logic.Equiv.Prod

/-! # Exact finite averages and forgotten independent coordinates

All distributions are literal uniform finite sample spaces. These lemmas
justify reindexing and restricting histories, without assuming a sampling law.
-/
namespace PoissonDAG.FiniteKernels

open scoped BigOperators

def average {A : Type} [Fintype A] (f : A → ℚ) : ℚ :=
  (∑ a, f a) / (Fintype.card A : ℚ)

theorem average_mono {A : Type} [Fintype A] {f g : A → ℚ}
    (h : ∀ a, f a ≤ g a) : average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

theorem average_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : A → ℚ) (g : B → ℚ) (h : ∀ a, f a = g (e a)) :
    average f = average g := by
  unfold average
  rw [Fintype.sum_equiv e f g h, Fintype.card_congr e]

theorem average_const {A : Type} [Fintype A] [Nonempty A] (c : ℚ) :
    average (fun _ : A => c) = c := by
  have hn : (Fintype.card A : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [average, hn]

theorem average_prod {A B : Type} [Fintype A] [Fintype B] (f : A × B → ℚ) :
    average f = average (fun a => average (fun b => f (a, b))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    Finset.sum_div, div_div]
  rw [mul_comm (Fintype.card B : ℚ) (Fintype.card A : ℚ)]

theorem average_restrict {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (p : I → Prop) [DecidablePred p] (f : ({i // p i} → A) → ℚ) :
    average (fun all : I → A => f (fun i => all i.val)) = average f := by
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => A)
  calc
    _ = average (fun pair : ({i // p i} → A) × ({i // ¬p i} → A) => f pair.1) := by
      apply average_equiv e
      intro all
      rfl
    _ = _ := by
      rw [average_prod]
      simp_rw [average_const]

/-- Restrict only the history coordinates, retain an independent target, and
reindex the retained histories by any finite equivalence. -/
theorem average_pair_restrict_equiv {I J A : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype A] [Nonempty A] (p : I → Prop) [DecidablePred p]
    (e : {i // p i} ≃ J) (f : A × (J → A) → ℚ) :
    average (fun sample : A × (I → A) =>
      f (sample.1, fun j => sample.2 (e.symm j).val)) = average f := by
  rw [average_prod, average_prod]
  apply congrArg average
  funext target
  calc
    _ = average (fun restricted : {i // p i} → A =>
        f (target, fun j => restricted (e.symm j))) := average_restrict p _
    _ = _ := by
      apply average_equiv (Equiv.arrowCongr e (Equiv.refl A))
      intro restricted
      rfl

end PoissonDAG.FiniteKernels
