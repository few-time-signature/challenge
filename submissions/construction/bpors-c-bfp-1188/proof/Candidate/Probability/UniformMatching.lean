import Candidate.Probability.SamplePaths
import Candidate.Probability.UniformAverage
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FieldSimp

/-! # Exact matching sets for independently uniform owners or buckets

These finite conditional experiments are used inside the shared Poisson law;
they introduce no cap or replacement distribution for the history count.
-/

set_option maxHeartbeats 20000

namespace PoissonDAG.UniformMatching

open scoped BigOperators

abbrev Sample (m q : Nat) := Fin m × (Fin q → Fin m)

def matchingSet {m q : Nat} (sample : Sample m q) : Finset (Fin q) :=
  Finset.univ.filter (fun i => sample.2 i = sample.1)

abbrev Different {m : Nat} (target : Fin m) := {x : Fin m // x ≠ target}

abbrev FiberData (m : Nat) {q : Nat} (subset : Finset (Fin q)) :=
  Σ target : Fin m, ((subsetᶜ : Finset (Fin q)) → Different target)

def fiberEquiv (m : Nat) {q : Nat} (subset : Finset (Fin q)) :
    {sample : Sample m q // matchingSet sample = subset} ≃ FiberData m subset where
  toFun sample := ⟨sample.val.1, fun i => ⟨sample.val.2 i.val, by
    intro heq
    have hi : i.val ∈ matchingSet sample.val := by simp [matchingSet, heq]
    rw [sample.property] at hi
    exact (Finset.mem_compl.mp i.property) hi⟩⟩
  invFun data := ⟨(data.1, fun i => if hi : i ∈ subset then data.1
      else (data.2 ⟨i, Finset.mem_compl.mpr hi⟩).val), by
    ext i
    by_cases hi : i ∈ subset
    · simp [matchingSet, hi]
    · simp [matchingSet, hi, (data.2 ⟨i, Finset.mem_compl.mpr hi⟩).property]⟩
  left_inv sample := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      have hmem : sample.val.2 i = sample.val.1 ↔ i ∈ subset := by
        calc
          _ ↔ i ∈ matchingSet sample.val := by simp [matchingSet]
          _ ↔ i ∈ subset := Iff.of_eq (congrArg (fun set => i ∈ set) sample.property)
      by_cases hi : i ∈ subset
      · simp [hi, hmem.mpr hi]
      · simp [hi]
  right_inv data := by
    rcases data with ⟨target, history⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext i
      apply Subtype.ext
      simp [Finset.mem_compl.mp i.property]

theorem different_card {m : Nat} (target : Fin m) : Fintype.card (Different target) = m - 1 := by
  simpa [Different] using Fintype.card_subtype_compl (fun x : Fin m => x = target)

theorem matching_fiber_card (m : Nat) {q : Nat} (subset : Finset (Fin q)) :
    Fintype.card {sample : Sample m q // matchingSet sample = subset} =
      m * (m - 1) ^ (q - subset.card) := by
  rw [Fintype.card_congr (fiberEquiv m subset), Fintype.card_sigma]
  simp [FiberData, Fintype.card_fun, different_card, Finset.card_compl]

def mass (m q : Nat) : Finset (Fin q) → ℚ :=
  FiniteKernels.initialMass (@matchingSet m q)

theorem mass_eq_count (m q : Nat) (subset : Finset (Fin q)) :
    mass m q subset =
      ((m * (m - 1) ^ (q - subset.card) : Nat) : ℚ) / ((m * m ^ q : Nat) : ℚ) := by
  have hcount : ((Finset.univ : Finset (Sample m q)).filter
      (fun sample => matchingSet sample = subset)).card = m * (m - 1) ^ (q - subset.card) := by
    simpa only [Fintype.card_subtype] using matching_fiber_card m subset
  unfold mass FiniteKernels.initialMass FiniteKernels.project
  calc
    _ = (∑ sample : Sample m q, if matchingSet sample = subset then (1 : ℚ) else 0) /
        (Fintype.card (Sample m q) : ℚ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro sample hsample
      split <;> simp_all
    _ = _ := by
      rw [Finset.sum_boole, hcount]
      simp [Sample, Fintype.card_prod, Fintype.card_fun]

theorem subsets_of_card (q k : Nat) :
    ((Finset.univ : Finset (Finset (Fin q))).filter (fun subset => subset.card = k)).card =
      q.choose k := by
  have huniv : (Finset.univ : Finset (Finset (Fin q))) =
      (Finset.univ : Finset (Fin q)).powerset := by
    ext subset
    simp
  rw [huniv, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard]
  simp

def byCount (m q k : Nat) : ℚ :=
  ∑ subset : Finset (Fin q), if subset.card = k then mass m q subset else 0

theorem byCount_eq_count (m q k : Nat) :
    byCount m q k = (q.choose k : ℚ) *
      (((m * (m - 1) ^ (q - k) : Nat) : ℚ) / ((m * m ^ q : Nat) : ℚ)) := by
  unfold byCount
  calc
    _ = ∑ subset : Finset (Fin q), if subset.card = k then
        (((m * (m - 1) ^ (q - k) : Nat) : ℚ) / ((m * m ^ q : Nat) : ℚ)) else 0 := by
      apply Finset.sum_congr rfl
      intro subset hsubset
      by_cases hcard : subset.card = k
      · simp [hcard, mass_eq_count]
      · simp [hcard]
    _ = _ := by
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      rw [subsets_of_card]

theorem byCount_eq_probability {m : Nat} (hm : 0 < m) (q k : Nat) (hk : k ≤ q) :
    byCount m q k = (q.choose k : ℚ) * ((1 : ℚ) / m) ^ k *
      (1 - (1 : ℚ) / m) ^ (q - k) := by
  rw [byCount_eq_count]
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hbase : (1 : ℚ) - 1 / m = ((m - 1 : Nat) : ℚ) / m := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    simp only [Nat.cast_one]
    field_simp [hmQ]
  have hpow : (m : ℚ) ^ q = (m : ℚ) ^ k * (m : ℚ) ^ (q - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  rw [hbase]
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [hpow]
  simp only [div_pow, one_pow]
  field_simp [hmQ]

def cardinalityIndex {q : Nat} (subset : Finset (Fin q)) : Fin (q + 1) :=
  ⟨subset.card, by
    have h := Finset.card_le_univ subset
    simpa using Nat.lt_succ_of_le h⟩

theorem mass_project_cardinality (m q : Nat) (k : Fin (q + 1)) :
    FiniteKernels.project cardinalityIndex (mass m q) k = byCount m q k.val := by
  unfold FiniteKernels.project byCount
  apply Finset.sum_congr rfl
  intro subset hsubset
  simp only [cardinalityIndex, Fin.ext_iff]

/-- The exact binomial law for a matching set inside the common-q experiment.
This finite conditional identity does not replace the shared Poisson law. -/
theorem average_cardinality {m : Nat} (hm : 0 < m) (q : Nat)
    (value : Fin (q + 1) → ℚ) :
    FiniteKernels.average (fun sample : Sample m q =>
      value (cardinalityIndex (matchingSet sample))) =
      ∑ k : Fin (q + 1),
        ((q.choose k.val : ℚ) * ((1 : ℚ) / m) ^ k.val *
          (1 - (1 : ℚ) / m) ^ (q - k.val)) * value k := by
  calc
    _ = ∑ subset : Finset (Fin q), mass m q subset * value (cardinalityIndex subset) := by
      symm
      exact FiniteKernels.initialMass_pairing (@matchingSet m q) _
    _ = ∑ k : Fin (q + 1), byCount m q k.val * value k := by
      rw [← FiniteKernels.sum_project_mul cardinalityIndex]
      simp_rw [mass_project_cardinality]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [byCount_eq_probability hm q k.val (by have := k.isLt; omega)]

end PoissonDAG.UniformMatching
