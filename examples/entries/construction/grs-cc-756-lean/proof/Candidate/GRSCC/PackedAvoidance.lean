import Mathlib.Tactic.IntervalCases
import PoissonDAG.Probability.PackedCounts
import Candidate.GRSCC.MaskedTraversal

/-! Six geometric factors encode all bounded words in one integer. The digit
at degree sixteen counts the allowed words. This computes each same-slot and
different-slot avoidance factor from the same finite experiment. -/
namespace PoissonDAG.GRSCC.Small

open PoissonDAG.BoundedCompositions

abbrev radix : Nat := 1048576

def factor : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1048577
  | 3 => 1099512676353
  | 4 => 1152922604119523329
  | 5 => 1208926972537233294229505
  | 6 => 1267651809155201938729997434881
  | 7 => 1329229263436725028105745790277779457
  | 8 => 1393797904137427383071010497786312871903233
  | 9 => 1461503031128807055631067903726780805968804446209
  | k+10 => ∑ i ∈ Finset.range (k+10), radix^i

private theorem factor_eq (n : Nat) : factor n = ∑ i ∈ Finset.range n, radix^i := by
  by_cases h : n < 10
  · interval_cases n <;> decide +kernel
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 10 ≤ n)
    rw [Nat.add_comm]
    rfl

def six (f : CodePosition → Nat) : Nat :=
  f 0 * (f 1 * (f 2 * (f 3 * (f 4 * f 5))))

private theorem six_eq (f : CodePosition → Nat) : six f = ∏ j, f j := by
  simp [six, Fin.prod_univ_succ]

def packedAvoidance (b : CodePosition → Nat) : Int :=
  if six b < radix then ((six (fun j => factor (b j)) / radix^16 % radix : Nat) : Int)
  else compositionFormula b

theorem packedAvoidance_eq (b : CodePosition → Nat) :
    packedAvoidance b = compositionFormula b := by
  unfold packedAvoidance
  split_ifs with h
  · have he : six (fun j => factor (b j)) = PackedCounts.productCode radix b := by
      simp only [six_eq, factor_eq, PackedCounts.productCode]
    rw [he, PackedCounts.bounded_digit _ _ _ (six_eq b ▸ h)]
    change (boundedTupleCount6 b : Int) = _
    rw [boundedTupleCount6_eq, compositionFormula]
    apply Finset.sum_congr rfl
    intro T _
    split_ifs <;> simp only [Nat.choose_eq_fast_choose, Nat.cast_zero]
  · rfl

def packedMoment (m v mask : Nat) (b : CodePosition → Nat) : Int :=
  subsetSign mask * packedAvoidance b ^ v *
    (∑ depth : Depth, if depthPosition depth ∈ requirementsOfMask mask then 0 else
      (2 : Int) ^ (4 - depth.val) * packedAvoidance (prefixBound b depth)) ^ (m-v)

def packedLeaf (m v mask : Nat) (digits : List Nat) : Int :=
  let count := completionFormula (6-(selectedPositions mask).length) (16-digits.sum)
  if count = 0 then 0 else count * packedMoment m v mask (listBound (selectedPositions mask) digits)

theorem packedLeaf_eq (m v mask : Nat) : packedLeaf m v mask = traversalLeaf m v mask := by
  funext digits
  simp only [packedLeaf, traversalLeaf, packedMoment, momentFromBounds, packedAvoidance_eq]

def packedNumerator (m v : Nat) : Int :=
  ((List.range 63).map (fun mask => PrunedDigits.fold (selectedPositions mask).length 16
    (packedLeaf m v mask))).sum

theorem packedNumerator_eq (m v : Nat) : packedNumerator m v = guardedNumerator m v := by
  rw [← traversalNumerator_eq_guarded]
  simp only [packedNumerator, traversalNumerator, packedLeaf_eq]

theorem localCover_of_packed (m v cap : Nat) (hv : 0 < v) (hvm : v ≤ m)
    (check : packedNumerator m v * 1000000 ≤
      (cap : Int) * (15597 ^ (m+1) * 31 ^ (m-v) : Nat)) :
    localCover m v ≤ (cap : Rat) / 1000000 := by
  apply localCover_le_cap m v cap hv hvm
  rwa [groupedNumerator_eq_guarded, ← packedNumerator_eq]

end PoissonDAG.GRSCC.Small
