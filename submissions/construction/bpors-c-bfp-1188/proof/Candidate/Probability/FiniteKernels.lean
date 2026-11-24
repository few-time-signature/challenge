import PoissonDAG.Probability.Counting
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod

/-! # Projecting finite joint-event kernels

Masses may be substochastic. No independence or transition law is assumed by
a definition: applications must prove the displayed row-projection equality.
-/

namespace PoissonDAG.FiniteKernels

open scoped BigOperators

variable {S J : Type} [Fintype S] [Fintype J] [DecidableEq J]

def step (kernel : S → S → ℚ) (mass : S → ℚ) (target : S) : ℚ :=
  ∑ source, mass source * kernel source target

def project (index : S → J) (mass : S → ℚ) (target : J) : ℚ :=
  ∑ state, if index state = target then mass state else 0

def backward (kernel : S → S → ℚ) (value : S → ℚ) (source : S) : ℚ :=
  ∑ target, kernel source target * value target

theorem step_adjoint (kernel : S → S → ℚ) (mass value : S → ℚ) :
    (∑ target, step kernel mass target * value target) =
      ∑ source, mass source * backward kernel value source := by
  unfold step backward
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source hsource
  apply Finset.sum_congr rfl
  intro target htarget
  ring

theorem iterate_adjoint (kernel : S → S → ℚ) (mass value : S → ℚ) (n : Nat) :
    (∑ target, ((step kernel)^[n] mass) target * value target) =
      ∑ source, mass source * ((backward kernel)^[n] value) source := by
  induction n generalizing mass with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, ih, step_adjoint]
      simp only [Function.iterate_succ_apply']

theorem total_iterate_eq_survival (kernel : S → S → ℚ) (mass : S → ℚ) (n : Nat) :
    (∑ target, ((step kernel)^[n] mass) target) =
      ∑ source, mass source * ((backward kernel)^[n] (fun _ => 1)) source := by
  simpa using iterate_adjoint kernel mass (fun _ => (1 : ℚ)) n

theorem sum_project_mul (index : S → J) (mass : S → ℚ) (value : J → ℚ) :
    (∑ target, project index mass target * value target) =
      ∑ state, mass state * value (index state) := by
  unfold project
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro state hstate
  simp only [ite_mul, zero_mul]
  simp [eq_comm]

theorem project_step (index : S → J) (kernel : S → S → ℚ)
    (quotient : J → J → ℚ)
    (hrow : ∀ source target, (∑ state,
      if index state = target then kernel source state else 0) = quotient (index source) target)
    (mass : S → ℚ) :
    project index (step kernel mass) = step quotient (project index mass) := by
  funext target
  unfold project step
  calc
    _ = ∑ state, ∑ source,
        mass source * (if index state = target then kernel source state else 0) := by
      apply Finset.sum_congr rfl
      intro state hstate
      split <;> simp_all
    _ = ∑ source, mass source *
        ∑ state, if index state = target then kernel source state else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source hsource
      rw [Finset.mul_sum]
    _ = ∑ source, mass source * quotient (index source) target := by simp_rw [hrow]
    _ = _ := (sum_project_mul index mass (fun source => quotient source target)).symm

theorem project_iterate (index : S → J) (kernel : S → S → ℚ)
    (quotient : J → J → ℚ)
    (hrow : ∀ source target, (∑ state,
      if index state = target then kernel source state else 0) = quotient (index source) target)
    (mass : S → ℚ) (n : Nat) :
    project index ((step kernel)^[n] mass) = (step quotient)^[n] (project index mass) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        project_step index kernel quotient hrow, ih]

theorem sum_project (index : S → J) (mass : S → ℚ) :
    (∑ target, project index mass target) = ∑ state, mass state := by
  simpa using sum_project_mul index mass (fun _ => (1 : ℚ))

theorem projected_total_iterate (index : S → J) (kernel : S → S → ℚ)
    (quotient : J → J → ℚ)
    (hrow : ∀ source target, (∑ state,
      if index state = target then kernel source state else 0) = quotient (index source) target)
    (mass : S → ℚ) (n : Nat) :
    (∑ state, ((step kernel)^[n] mass) state) =
      ∑ target, ((step quotient)^[n] (project index mass)) target := by
  rw [← sum_project index, project_iterate index kernel quotient hrow]

section Samples

variable {A : Type} [Fintype A] [DecidableEq S]

def sampleKernel (event : S → A → Bool) (next : A → S) (source target : S) : ℚ :=
  (∑ sample, if event source sample = true ∧ next sample = target then (1 : ℚ) else 0) /
    (Fintype.card A : ℚ)

theorem sample_project_row (index : S → J) (event : S → A → Bool) (next : A → S)
    (source : S) (target : J) :
    (∑ state, if index state = target then sampleKernel event next source state else 0) =
      (∑ sample, if event source sample = true ∧ index (next sample) = target then (1 : ℚ) else 0) /
        (Fintype.card A : ℚ) := by
  have hsum : (∑ state, if index state = target then
      ∑ sample, if event source sample = true ∧ next sample = state then (1 : ℚ) else 0
      else 0) =
      ∑ sample, if event source sample = true ∧ index (next sample) = target then (1 : ℚ) else 0 := by
    calc
      _ = ∑ state, ∑ sample, if index state = target then
          (if event source sample = true ∧ next sample = state then (1 : ℚ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro state hstate
        split <;> simp_all
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro sample hsample
        by_cases he : event source sample = true
        · rw [Finset.sum_eq_single (next sample)]
          · simp [he]
          · intro state hstate hne
            simp [he, Ne.symm hne]
          · intro hnot
            simp at hnot
        · simp [he]
  unfold sampleKernel
  calc
    _ = (∑ state, if index state = target then
        ∑ sample, if event source sample = true ∧ next sample = state then (1 : ℚ) else 0
        else 0) / (Fintype.card A : ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro state hstate
      split <;> simp_all
    _ = _ := by rw [hsum]

theorem sample_project_row_count (index : S → J) (event : S → A → Bool) (next : A → S)
    (source : S) (target : J) :
    (∑ state, if index state = target then sampleKernel event next source state else 0) =
      (((Finset.univ : Finset A).filter (fun sample =>
        event source sample = true ∧ index (next sample) = target)).card : ℚ) /
        (Fintype.card A : ℚ) := by
  rw [sample_project_row, Finset.sum_boole]

end Samples

end PoissonDAG.FiniteKernels
