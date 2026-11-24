import Candidate.Constructions.PORS.BucketJoint
import Candidate.Constructions.PORS.SingleCover

namespace PoissonDAG.PORS.BucketExperiment
open FiniteKernels UniformMatching BucketRefined BucketAverage

abbrev BucketTags := Fin p.K → Fin p.buckets
abbrev Full := Fin p.K → Choices p.t p.k
abbrev Hist (s : Scheme) (q : Nat) := Fin q → Fin s.accepted.length

/-- A conditional history of pruned supports still has all its bucket tags.
Transposing the table of tags produces the per-coordinate matching samples. -/
private def columns (q : Nat) :
    (Fin q → BucketTags) × (Full × BucketTags) ≃ (Fin p.K → Column p q) where
  toFun x i := ((x.2.2 i,fun j => x.1 j i),x.2.1 i)
  invFun y := (fun j i => (y i).1.2 j,fun i => (y i).2,fun i => (y i).1.1)
  left_inv _ := rfl
  right_inv _ := rfl

def bound (q : Nat) (hs : Fin q → Full) (hb : Fin q → BucketTags)
    (target : Full × BucketTags) : ℚ :=
  ∏ i, hitColumn (p:=p) (fun j => (hs j i).val) ((target.2 i,fun j => hb j i),target.1 i)

private theorem bound_nonneg (q : Nat) (hs : Fin q → Full) (hb : Fin q → BucketTags)
    (x : Full × BucketTags) : 0 ≤ bound q hs hb x := by
  unfold bound
  apply Finset.prod_nonneg
  intro i _
  unfold hitColumn
  split <;> norm_num

theorem over_buckets (q : Nat) (hs : Fin q → Full) :
    average (fun hb : Fin q → BucketTags => average (bound q hs hb)) ≤ p.bucketEnvelope q ^ p.K := by
  rw [← average_prod (fun x : (Fin q → BucketTags) × (Full × BucketTags) => bound q hs x.1 x.2)]
  let sets (i : Fin p.K) (j : Fin q) := (hs j i).val
  apply (average_equiv (columns q) (fun x => bound q hs x.1 x.2)
    (fun x => ∏ i, hitColumn (p:=p) (sets i) (x i)) (fun _ => rfl)).le.trans
  exact joint_bucket_bound q sets (fun i j => (Finset.mem_powersetCard.mp (hs j i).property).2)

private theorem extend_sum {A X : Type} [Fintype A] [Fintype X]
    (e : A ↪ X) (f : A → ℚ) (g : X → ℚ) (nonneg : ∀ x, 0 ≤ g x)
    (major : ∀ a, f a ≤ g (e a)) : (∑ a, f a) ≤ ∑ x, g x := by
  classical
  calc
    _ ≤ ∑ a, g (e a) := Finset.sum_le_sum (fun a _ => major a)
    _ = ∑ x ∈ Finset.univ.map e, g x := (Finset.sum_map _ _ _).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => nonneg x)

private theorem mass (s : Scheme) (q : Nat) (pos : 0<s.accepted.length) :
    s.coverCoefficient q =
      average (fun h : Hist s q => ∑ x : Fin s.accepted.length,
        if s.covered (indexHistory s.accepted h) s.accepted[x] then (1:ℚ) else 0) /
        2^s.encoder.inputs := by
  rw [s.coverCoefficient_eq_acceptedProbability pos]
  unfold Scheme.acceptedCoverProbability Scheme.tau average
  simp only [Hist,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,pow_succ]
  have nz : (s.accepted.length : ℚ) ≠ 0 := by exact_mod_cast pos.ne'
  field_simp [nz] <;> ring

theorem coverage (s : Scheme) (q : Nat) (pos : 0<s.accepted.length)
    {H : Type} [Fintype H] [Nonempty H]
    (accepted : Fin s.accepted.length ≃ H × BucketTags) (support : H ↪ Full)
    (major : ∀ (h : Hist s q) (t : Fin s.accepted.length),
      (if s.covered (indexHistory s.accepted h) s.accepted[t] then (1:ℚ) else 0) ≤
        bound q (fun j => support (accepted (h j)).1) (fun j => (accepted (h j)).2)
          (support (accepted t).1,(accepted t).2)) :
    s.coverCoefficient q ≤ ((Fintype.card (Full × BucketTags) : ℚ)/2^s.encoder.inputs) *
      p.bucketEnvelope q ^ p.K := by
  classical
  let pop : ℚ := Fintype.card (Full × BucketTags)
  let emb : Fin s.accepted.length ↪ Full × BucketTags :=
    accepted.toEmbedding.trans (support.prodMap (Function.Embedding.refl _))
  let hist := (Equiv.piCongrRight (fun _ : Fin q => accepted)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)
  let T (hs : Fin q → H) (hb : Fin q → BucketTags) :=
    average (bound q (fun j => support (hs j)) hb)
  have nz : pop ≠ 0 := by
    change (Fintype.card (Full × BucketTags) : ℚ) ≠ 0
    haveI : Nonempty (Full × BucketTags) := ⟨emb ⟨0,pos⟩⟩
    exact_mod_cast Fintype.card_ne_zero
  have comparison (h : Hist s q) :
      (∑ x : Fin s.accepted.length, if s.covered (indexHistory s.accepted h) s.accepted[x]
        then (1:ℚ) else 0) ≤ pop*T (hist h).1 (hist h).2 := by
    have hh := extend_sum emb _ (bound q (fun j => support (accepted (h j)).1)
        (fun j => (accepted (h j)).2)) (bound_nonneg q _ _) (major h)
    apply hh.trans_eq
    change _ = pop * (_ / pop)
    field_simp <;> rfl
  have avg : average (fun h : Hist s q => pop*T (hist h).1 (hist h).2) =
      pop*average (fun hs : Fin q → H => average (T hs)) := by
    rw [average_equiv hist _ (fun x => pop*T x.1 x.2) (fun _ => rfl)]
    rw [← average_prod (fun x : (Fin q → H) × (Fin q → BucketTags) => T x.1 x.2)]
    unfold average
    rw [← Finset.mul_sum]; ring
  have hT : average (fun hs : Fin q → H => average (T hs)) ≤ p.bucketEnvelope q ^ p.K := by
    rw [← average_const (A:=Fin q → H) (p.bucketEnvelope q ^ p.K)]
    exact average_mono (fun hs => over_buckets q (fun j => support (hs j)))
  rw [mass s q pos]
  calc
    _ ≤ _ := div_le_div_of_nonneg_right (average_mono comparison) (by positivity)
    _ = _ := congrArg (fun z : ℚ => z/2^s.encoder.inputs) avg
    _ ≤ (pop*(p.bucketEnvelope q ^ p.K))/2^s.encoder.inputs :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg _)) (by positivity)
    _ = _ := by dsimp only [pop]; ring

end PoissonDAG.PORS.BucketExperiment
