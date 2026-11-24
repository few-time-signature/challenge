import Candidate.Constructions.PORS.BucketAverage
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace PoissonDAG.PORS.BucketAverage
open FiniteKernels UniformMatching

/-- Uniform support before testing the target's pruning cutoff. -/
abbrev Choices (t k : Nat) := ↥((Finset.univ : Finset (Fin t)).powersetCard k)

private theorem conditional {p : Row} {u : Finset (Fin p.t)} :
    average (fun x : Choices p.t p.k => if x.val ⊆ u then (1:ℚ) else 0) =
      ((u.powersetCard p.k).card : ℚ) / p.supports := by
  classical
  let covered := (Finset.univ : Finset (Choices p.t p.k)).filter (fun x => x.val ⊆ u)
  have bij : covered.card = (u.powersetCard p.k).card := by
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp hx).2,(Finset.mem_powersetCard.mp x.property).2⟩
    · intro _ _ _ _ h; exact Subtype.ext h
    · intro x hx
      obtain ⟨sub,card⟩ := Finset.mem_powersetCard.mp hx
      exact ⟨⟨x,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,card⟩⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub⟩,rfl⟩
  unfold average
  rw [Finset.sum_boole]
  change (covered.card : ℚ) / (Fintype.card (Choices p.t p.k) : ℚ) = _
  rw [bij]
  simp only [Choices,Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin,
    Row.supports,Nat.choose_eq_fast_choose]

abbrev Column (p : Row) (q : Nat) := Sample p.buckets q × Choices p.t p.k

def hitColumn {p : Row} {q : Nat} (sets : Fin q → Finset (Fin p.t)) (x : Column p q) : ℚ :=
  if x.2.val ⊆ supplyPool sets x.1 then 1 else 0

private theorem column_average (q : Nat) (sets : Fin q → Finset (Fin BucketRefined.p.t))
    (weight : ∀ i, (sets i).card=BucketRefined.p.k) :
    average (hitColumn (p := BucketRefined.p) sets) ≤ BucketRefined.p.bucketEnvelope q := by
  rw [average_prod]
  unfold hitColumn
  simp_rw [conditional]
  exact bucket_coordinate q sets weight

private theorem independent {A : Type} [Fintype A] (n : Nat) (f : Fin n → A → ℚ) :
    average (fun x : Fin n → A => ∏ i, f i (x i)) = ∏ i, average (f i) := by
  unfold average
  rw [← Fintype.prod_sum, Finset.prod_div_distrib, Fintype.card_fun]
  simp

/-- For arbitrary historical supports in both coordinates, the shared-q
bucket experiment has the squared single-coordinate envelope. Conditioning on
an accepted historical support tuple is therefore permissible. -/
theorem joint_bucket_bound (q : Nat)
    (sets : Fin BucketRefined.p.K → Fin q → Finset (Fin BucketRefined.p.t))
    (weight : ∀ i j, (sets i j).card=BucketRefined.p.k) :
    average (fun x : Fin BucketRefined.p.K → Column BucketRefined.p q =>
      ∏ i, hitColumn (p := BucketRefined.p) (sets i) (x i)) ≤ BucketRefined.p.bucketEnvelope q ^ BucketRefined.p.K := by
  rw [independent]
  calc
    _ ≤ ∏ _ : Fin BucketRefined.p.K, BucketRefined.p.bucketEnvelope q := by
      apply Finset.prod_le_prod
      · intro i _
        unfold average hitColumn
        exact div_nonneg (Finset.sum_nonneg (fun x _ => by split <;> norm_num)) (Nat.cast_nonneg _)
      · intro i _; exact column_average q (sets i) (weight i)
    _ = _ := by simp

end PoissonDAG.PORS.BucketAverage
