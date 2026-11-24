import PoissonDAG.Constructions.PORS.BucketRefinedRow
import PoissonDAG.Probability.UniformMatching
import Mathlib.Algebra.BigOperators.Fin

namespace PoissonDAG.PORS.BucketAverage
open FiniteKernels UniformMatching

/-- Fix every historical support, including any dependence due to pruning.
Only the histories whose bucket agrees with the target can supply a secret. -/
def supplyPool {t q B : Nat} (sets : Fin q → Finset (Fin t)) (buckets : Sample B q) :=
  (matchingSet buckets).biUnion sets

theorem pool_size {t q B k : Nat} (sets : Fin q → Finset (Fin t))
    (weights : ∀ i, (sets i).card = k) (buckets : Sample B q) :
    (supplyPool sets buckets).card ≤ k*(matchingSet buckets).card := by
  simpa only [supplyPool,Nat.mul_comm k] using Finset.card_biUnion_le_card_mul (matchingSet buckets)
    sets k (fun i _ => (weights i).le)

private theorem child_bound (p : Row) (q : Nat) (hk : 0 < p.k) (depths : p.depthCount=1)
    (ht : p.k≤p.t) (sets : Fin q → Finset (Fin p.t)) (weights : ∀ i, (sets i).card = p.k)
    (b : Sample p.buckets q) :
    (((supplyPool sets b).powersetCard p.k).card : ℚ) / p.supports ≤
      p.child (matchingSet b).card := by
  let m := (matchingSet b).card
  let u := supplyPool sets b
  have bound := pool_size sets weights b
  have ht' : u.card ≤ p.t := by simpa only [Fintype.card_fin] using Finset.card_le_univ u
  have pos : 0 < p.supports := by
    rw [Row.supports,← Nat.choose_eq_fast_choose]
    exact Nat.choose_pos ht
  have hs : (0 : ℚ) < p.supports := by exact_mod_cast pos
  have one : (u.card.choose p.k : ℚ) / p.supports ≤ 1 := by
    apply (div_le_one hs).mpr
    rw [Row.supports, ← Nat.choose_eq_fast_choose]
    exact_mod_cast Nat.choose_le_choose p.k ht'
  have num : u.card.choose p.k ≤ (p.k*m).choose p.k := Nat.choose_le_choose _ bound
  rw [Finset.card_powersetCard]
  change (u.card.choose p.k : ℚ) / p.supports ≤ p.child m
  by_cases h0 : m=0
  · rw [h0,Nat.mul_zero,Nat.choose_eq_zero_of_lt hk] at num
    simp [Row.child,h0,show u.card.choose p.k=0 by omega]
  by_cases h1 : m=1
  · rw [h1,Nat.mul_one,Nat.choose_self] at num
    simp only [Row.child,h0,h1,ite_false,ite_true,depths,Nat.mul_one]
    exact div_le_div_of_nonneg_right (by exact_mod_cast num) hs.le
  · simp only [Row.child,h0,h1,ite_false,← Nat.choose_eq_fast_choose]
    exact le_min one (div_le_div_of_nonneg_right (by exact_mod_cast num) hs.le)

private theorem fin_sum (n : Nat) (f : Nat → ℚ) :
    (∑ i : Fin n, f i.val) = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.sum_univ_castSucc, List.range_succ, ih]

/-- The exact finite bucket average for one coordinate, conditional on q.
This calculation does not average over or resample q. -/
theorem matching_average (p : Row) (hb : p.b ≠ 0) (q : Nat) :
    average (fun b : Sample p.buckets q => p.child (matchingSet b).card) = p.bucketEnvelope q := by
  have hB : 0 < p.buckets := by simp [Row.buckets]
  have hBr : (p.buckets : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have h := average_cardinality hB q (fun n => p.child n.val)
  change average (fun b : Sample p.buckets q => p.child (matchingSet b).card) = _ at h
  rw [h, Row.bucketEnvelope, if_neg hb]
  let f := fun m : Nat => ((Nat.fast_choose q m * (p.buckets-1)^(q-m) : Nat) : ℚ) * p.child m
  change _ = ((List.range (q+1)).map f).sum / _
  rw [← fin_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  rw [← byCount_eq_probability hB q m.val (by have := m.isLt; omega),byCount_eq_count]
  dsimp only [f]
  rw [← Nat.choose_eq_fast_choose]
  push_cast
  field_simp [hBr]

theorem bucket_coordinate (q : Nat) (sets : Fin q → Finset (Fin BucketRefined.p.t))
    (weights : ∀ i, (sets i).card = BucketRefined.p.k) :
    average (fun b : Sample BucketRefined.p.buckets q =>
      (((supplyPool sets b).powersetCard BucketRefined.p.k).card : ℚ) / BucketRefined.p.supports) ≤
      BucketRefined.p.bucketEnvelope q := by
  rw [← matching_average _ (by decide)]
  exact average_mono (child_bound _ q (by decide) rfl (by decide) sets weights)

end PoissonDAG.PORS.BucketAverage
