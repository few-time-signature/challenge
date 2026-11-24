import Candidate.Probability.SamplePaths
import Candidate.Probability.UniformAverage
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FieldSimp

/-! # The protected coefficient as a finite sampling experiment

A history is a full function on `Fin q`. The independent target has its own
coordinate. Restricting the target to accepted inputs extracts exactly one
factor `tau`; it does not change the accepted-history distribution.
-/
namespace PoissonDAG

open scoped BigOperators

def indexHistory (accepted : List Nat) {q : Nat}
    (sample : Fin q → Fin accepted.length) : List Nat :=
  List.ofFn (fun i => accepted[sample i])

private theorem sum_map_eq_index {α : Type} (xs : List α) (f : α → ℚ) :
    (xs.map f).sum = ∑ i : Fin xs.length, f xs[i] := by
  rw [← List.ofFn_getElem_eq_map xs f, Fin.sum_ofFn]
  simp only [Fin.getElem_fin]

private theorem sum_flatMap_rat {α : Type} (xs : List α) (f : α → List ℚ) :
    (xs.flatMap f).sum = (xs.map (fun x => (f x).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, List.sum_append]

/-- With-replacement list histories are exactly independent uniform indices. -/
theorem histories_sum_eq_index (accepted : List Nat) (q : Nat) (f : List Nat → ℚ) :
    ((histories accepted q).map f).sum =
      ∑ sample : Fin q → Fin accepted.length, f (indexHistory accepted sample) := by
  induction q generalizing f with
  | zero => simp [histories, indexHistory]
  | succ q ih =>
      simp only [histories, List.map_flatMap, sum_flatMap_rat, List.map_map]
      rw [ih]
      calc
        _ = ∑ tail : Fin q → Fin accepted.length,
            ∑ head : Fin accepted.length,
              f (accepted[head] :: indexHistory accepted tail) := by
          apply Finset.sum_congr rfl
          intro tail htail
          exact sum_map_eq_index accepted _
        _ = ∑ head : Fin accepted.length,
            ∑ tail : Fin q → Fin accepted.length,
              f (accepted[head] :: indexHistory accepted tail) := Finset.sum_comm
        _ = ∑ pair : Fin accepted.length × (Fin q → Fin accepted.length),
            f (accepted[pair.1] :: indexHistory accepted pair.2) := by
          rw [Fintype.sum_prod_type]
        _ = _ := by
          symm
          apply Fintype.sum_equiv (FiniteKernels.tupleSucc q)
          intro sample
          simp [indexHistory, List.ofFn_succ, FiniteKernels.tupleSucc]

private theorem count_true_eq_sum (xs : List Bool) :
    (xs.count true : ℚ) = (xs.map (fun b => if b then (1 : ℚ) else 0)).sum := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp [ih, add_comm]

private theorem sum_filter_eq_of_zero {α : Type} (xs : List α) (p : α → Bool)
    (f : α → ℚ) (hzero : ∀ x ∈ xs, p x = false → f x = 0) :
    (xs.map f).sum = ((xs.filter p).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have htail := ih (fun y hy => hzero y (by simp [hy]))
      by_cases hp : p x = true
      · simp [hp, htail]
      · have hf : p x = false := Bool.eq_false_iff.mpr hp
        simp [hf, hzero x (by simp) hf, htail]

def Scheme.acceptedCoverProbability (s : Scheme) (q : Nat) : ℚ :=
  (∑ history : Fin q → Fin s.accepted.length,
    ∑ target : Fin s.accepted.length,
      if s.covered (indexHistory s.accepted history) s.accepted[target]
        then (1 : ℚ) else 0) / (s.accepted.length : ℚ) ^ (q + 1)

/-- Coordinate zero is the target; the remaining coordinates are histories. -/
theorem Scheme.acceptedCoverProbability_eq_tuple (s : Scheme) (q : Nat) :
    s.acceptedCoverProbability q =
      FiniteKernels.average (fun sample : Fin (q + 1) → Fin s.accepted.length =>
        if s.covered (indexHistory s.accepted (fun i => sample i.succ)) s.accepted[sample 0]
          then (1 : ℚ) else 0) := by
  have hsum :
      (∑ history : Fin q → Fin s.accepted.length,
        ∑ target : Fin s.accepted.length,
          if s.covered (indexHistory s.accepted history) s.accepted[target]
            then (1 : ℚ) else 0) =
      ∑ sample : Fin (q + 1) → Fin s.accepted.length,
        if s.covered (indexHistory s.accepted (fun i => sample i.succ)) s.accepted[sample 0]
          then (1 : ℚ) else 0 := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ pair : Fin s.accepted.length × (Fin q → Fin s.accepted.length),
          if s.covered (indexHistory s.accepted pair.2) s.accepted[pair.1]
            then (1 : ℚ) else 0 := by rw [Fintype.sum_prod_type]
      _ = _ := by
        symm
        apply Fintype.sum_equiv (FiniteKernels.tupleSucc q)
        intro sample
        rfl
  unfold Scheme.acceptedCoverProbability FiniteKernels.average
  rw [hsum]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

/-- Literal identity for the original executable experiment. -/
theorem Scheme.coverCoefficient_eq_acceptedProbability (s : Scheme)
    (hpositive : 0 < s.accepted.length) (q : Nat) :
    s.coverCoefficient q = s.tau * s.acceptedCoverProbability q := by
  have htarget (history : List Nat) :
      ((s.raws.map (fun raw => if s.covered history raw then (1 : ℚ) else 0)).sum) =
        ∑ target : Fin s.accepted.length,
          if s.covered history s.accepted[target] then (1 : ℚ) else 0 := by
    calc
      _ = ((s.accepted.map (fun raw => if s.covered history raw then (1 : ℚ) else 0)).sum) := by
        apply sum_filter_eq_of_zero
        intro raw hraw hreject
        simp [Scheme.covered, hreject]
      _ = _ := sum_map_eq_index s.accepted _
  have hnum :
      (((histories s.accepted q).flatMap (fun history =>
        s.raws.map (fun raw => s.covered history raw))).count true : ℚ) =
      ∑ history : Fin q → Fin s.accepted.length,
        ∑ target : Fin s.accepted.length,
          if s.covered (indexHistory s.accepted history) s.accepted[target]
            then (1 : ℚ) else 0 := by
    rw [count_true_eq_sum, List.map_flatMap, sum_flatMap_rat]
    simp only [List.map_map, Function.comp_def]
    simp_rw [htarget]
    exact histories_sum_eq_index s.accepted q _
  have ha : (s.accepted.length : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hpositive
  have hr : ((2 ^ s.encoder.inputs : Nat) : ℚ) ≠ 0 := by positivity
  unfold Scheme.coverCoefficient Scheme.tau Scheme.acceptedCoverProbability
  dsimp only
  rw [hnum]
  simp only [Nat.cast_mul, Nat.cast_pow, pow_succ]
  field_simp

end PoissonDAG
