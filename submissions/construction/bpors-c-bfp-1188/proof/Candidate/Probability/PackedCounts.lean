import Candidate.Probability.BoundedCompositions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! One base-B digit counts a degree fiber whenever the entire finite sample
space has fewer than B elements. Multiplying geometric sums then computes
bounded-composition counts, including repeated degrees and empty ranges. -/
namespace PoissonDAG.PackedCounts

private theorem zero_count {ι : Type*} (s : Finset ι) (d : ι → Nat) :
    (s.filter (fun a => d a = 0)).card = ∑ a ∈ s, if d a = 0 then 1 else 0 := by
  simpa only [Nat.cast_id] using (Finset.sum_boole (R := Nat) (fun a => d a = 0) s).symm

theorem digit_sum {ι : Type*} (s : Finset ι) (d : ι → Nat) (B t : Nat)
    (h : s.card < B) :
    ((∑ a ∈ s, B^(d a)) / B^t) % B = (s.filter (fun a => d a = t)).card := by
  classical
  induction t generalizing s d with
  | zero =>
    have he : (∑ a ∈ s, B^d a) =
        (s.filter (fun a => d a = 0)).card +
          B * ∑ a ∈ s, (if d a = 0 then 0 else B^(d a-1)) := by
      rw [zero_count s d, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      cases ha : d a <;> simp [pow_succ']
    have hc := lt_of_le_of_lt (Finset.card_filter_le s (fun a => d a = 0)) h
    simp [he, Nat.mod_eq_of_lt hc]
  | succ t ih =>
    let pos := s.filter (fun a => 0 < d a)
    let ones := (s.filter (fun a => d a = 0)).card
    have hc : ones < B := lt_of_le_of_lt (Finset.card_filter_le s _) h
    have he : (∑ a ∈ s, B^d a) = ones + B * ∑ a ∈ pos, B^(d a-1) := by
      unfold ones pos
      rw [zero_count s d, Finset.sum_filter, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      cases ha : d a <;> simp [pow_succ']
    rw [he, pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt hc, zero_add, ih pos (fun a => d a-1)
        (lt_of_le_of_lt (Finset.card_filter_le s _) h)]
    congr 1
    ext a
    simp only [pos, Finset.mem_filter]
    constructor
    · rintro ⟨⟨ha, hp⟩, heq⟩
      exact ⟨ha, by omega⟩
    · rintro ⟨ha, heq⟩
      exact ⟨⟨ha, by omega⟩, by omega⟩

open BoundedCompositions

/-- Integer evaluated by the arithmetic checker. -/
def productCode {n : Nat} (B : Nat) (b : Fin n → Nat) : Nat :=
  ∏ i, ∑ a ∈ Finset.range (b i), B^a

theorem bounded_digit {n : Nat} (B t : Nat) (b : Fin n → Nat) (h : (∏ i, b i) < B) :
    (productCode B b / B^t) % B = boundedTupleCount n t b := by
  classical
  let domain := Fintype.piFinset (fun i => Finset.range (b i))
  have hc : domain.card < B := by simpa [domain,Fintype.card_piFinset] using h
  have he : productCode B b = ∑ f ∈ domain, B^(∑ i, f i) := by
    unfold productCode
    rw [Finset.prod_univ_sum]
    exact Finset.sum_congr rfl (fun f _ => (Finset.prod_pow_eq_pow_sum _ _ _))
  rw [he, digit_sum _ _ _ _ hc, ← Fintype.card_coe]
  unfold boundedTupleCount
  apply Fintype.card_congr
  exact {
    toFun := fun x => ⟨⟨x.val,(Finset.mem_filter.mp x.property).2⟩,
      fun i => Finset.mem_range.mp ((Fintype.mem_piFinset.mp
        (Finset.mem_filter.mp x.property).1) i)⟩
    invFun := fun x => ⟨x.val.val, Finset.mem_filter.mpr ⟨
      Fintype.mem_piFinset.mpr (fun i => Finset.mem_range.mpr (x.property i)),
      x.val.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end PoissonDAG.PackedCounts
