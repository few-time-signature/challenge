import Candidate.Probability.FiniteKernels
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Independent finite sample paths and their joint-event kernel

Independence is represented by the full function space `Fin n → A`, with its
uniform counting measure. The event checks the evolving state at every step.
-/

namespace PoissonDAG.FiniteKernels

open scoped BigOperators

variable {S A : Type} [Fintype S] [Fintype A] [DecidableEq S]

def tupleSucc (n : Nat) : (Fin (n + 1) → A) ≃ A × (Fin n → A) where
  toFun f := (f 0, fun i => f i.succ)
  invFun pair := Fin.cases pair.1 pair.2
  left_inv f := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv pair := by
    rcases pair with ⟨head, tail⟩
    rfl

def pathEvent (event : S → A → Bool) (next : A → S) : S → List A → Bool
  | _, [] => true
  | state, sample :: samples => event state sample && pathEvent event next (next sample) samples

def pathProbability (event : S → A → Bool) (next : A → S) (n : Nat) (state : S) : ℚ :=
  (∑ samples : Fin n → A,
    if pathEvent event next state (List.ofFn samples) then (1 : ℚ) else 0) /
      (Fintype.card A : ℚ) ^ n

theorem pathProbability_zero (event : S → A → Bool) (next : A → S) (state : S) :
    pathProbability event next 0 state = 1 := by
  simp [pathProbability, pathEvent, Fintype.card_fun]

theorem pathProbability_succ (event : S → A → Bool) (next : A → S) (n : Nat) (state : S) :
    pathProbability event next (n + 1) state =
      (∑ sample, if event state sample then pathProbability event next n (next sample) else 0) /
        (Fintype.card A : ℚ) := by
  have hsum : (∑ samples : Fin (n + 1) → A,
      if pathEvent event next state (List.ofFn samples) then (1 : ℚ) else 0) =
      ∑ head : A, if event state head then
        (∑ tail : Fin n → A,
          if pathEvent event next (next head) (List.ofFn tail) then (1 : ℚ) else 0) else 0 := by
    calc
      _ = ∑ pair : A × (Fin n → A),
          if pathEvent event next state (List.ofFn ((tupleSucc n).symm pair))
            then (1 : ℚ) else 0 := by
        apply Fintype.sum_equiv (tupleSucc n)
        intro samples
        simp
      _ = _ := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro head hhead
        by_cases he : event state head = true
        · simp [tupleSucc, List.ofFn_succ, pathEvent, he]
        · have hef : event state head = false := Bool.eq_false_iff.mpr he
          simp [tupleSucc, List.ofFn_succ, pathEvent, hef]
  unfold pathProbability
  rw [hsum, Finset.sum_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro sample hsample
  by_cases he : event state sample = true
  · simp [he, pow_succ, div_div]
  · have hef : event state sample = false := Bool.eq_false_iff.mpr he
    simp [hef]

theorem backward_sampleKernel (event : S → A → Bool) (next : A → S)
    (value : S → ℚ) (source : S) :
    backward (sampleKernel event next) value source =
      (∑ sample, if event source sample then value (next sample) else 0) /
        (Fintype.card A : ℚ) := by
  unfold backward sampleKernel
  calc
    _ = (∑ target, ∑ sample,
        (if event source sample = true ∧ next sample = target then (1 : ℚ) else 0) * value target) /
          (Fintype.card A : ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro target htarget
      rw [← Finset.sum_mul]
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro sample hsample
      by_cases he : event source sample = true
      · simp [he, eq_comm]
      · have hef : event source sample = false := Bool.eq_false_iff.mpr he
        simp [hef]

theorem pathProbability_eq_backward (event : S → A → Bool) (next : A → S) (n : Nat) :
    pathProbability event next n = (backward (sampleKernel event next))^[n] (fun _ => 1) := by
  induction n with
  | zero => funext state; exact pathProbability_zero event next state
  | succ n ih =>
      funext state
      rw [pathProbability_succ, Function.iterate_succ_apply', backward_sampleKernel]
      rw [← ih]

theorem pathProbability_nonneg (event : S → A → Bool) (next : A → S) (n : Nat) (state : S) :
    0 ≤ pathProbability event next n state := by
  unfold pathProbability
  apply div_nonneg
  · exact Finset.sum_nonneg (fun _ _ => by split <;> norm_num)
  · positivity

theorem pathProbability_le_one [Nonempty A] (event : S → A → Bool) (next : A → S)
    (n : Nat) (state : S) : pathProbability event next n state ≤ 1 := by
  have hd : (0 : ℚ) < (Fintype.card A : ℚ) ^ n := by
    exact pow_pos (by exact_mod_cast Fintype.card_pos) _
  unfold pathProbability
  apply (div_le_one hd).2
  calc
    _ ≤ ∑ _samples : Fin n → A, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro samples hsamples
      split <;> norm_num
    _ = _ := by simp [Fintype.card_fun, Nat.cast_pow]

def initialMass {O : Type} [Fintype O] (start : O → S) : S → ℚ :=
  project start (fun _ => 1 / (Fintype.card O : ℚ))

theorem initialMass_pairing {O : Type} [Fintype O] (start : O → S) (value : S → ℚ) :
    (∑ state, initialMass start state * value state) =
      (∑ initial, value (start initial)) / (Fintype.card O : ℚ) := by
  rw [initialMass, sum_project_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro initial hinitial
  ring

theorem total_sample_iterate {O : Type} [Fintype O] (start : O → S)
    (event : S → A → Bool) (next : A → S) (n : Nat) :
    (∑ state, ((step (sampleKernel event next))^[n] (initialMass start)) state) =
      (∑ initial, pathProbability event next n (start initial)) / (Fintype.card O : ℚ) := by
  rw [total_iterate_eq_survival, ← pathProbability_eq_backward, initialMass_pairing]

end PoissonDAG.FiniteKernels
