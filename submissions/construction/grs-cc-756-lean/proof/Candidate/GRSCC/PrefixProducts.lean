import Candidate.GRSCC.PackedAvoidance
import Mathlib.Tactic.FinCases

namespace PoissonDAG.GRSCC.Small

/-- The six depth digits sum to 16. The base is larger than the total
number of words in any six intervals of length at most nine. -/
def histogramDigit (x : Nat) : Int := (x / radix^16 % radix : Nat)

private theorem small_box (b : CodePosition → Nat) (h : ∀ j,b j ≤ 9) :
    six b < radix := by
  apply lt_of_le_of_lt (b := six (fun _ => 9))
  · unfold six
    gcongr <;> exact h _
  · decide +kernel

private theorem box_count (b : CodePosition → Nat) (h : ∀ j,b j ≤ 9) :
    packedAvoidance b = histogramDigit (six (fun i => factor (b i))) := by
  simp only [packedAvoidance,if_pos (small_box b h),histogramDigit]

/-- The jth component counts words that avoid the selected coordinates
before the first differing slot bit. Prefix products are shared by all five
positions. A sixth product counts same-slot words. -/
def supplierCounts (mask : Nat) (b : CodePosition → Nat) : Int × Int :=
  let f := factor 9
  let x := factor (b 0)
  let y := x * factor (b 1)
  let z := y * factor (b 2)
  let u := z * factor (b 3)
  let all := u * factor (b 4) * factor (b 5)
  let cell (j : Nat) (power : Nat) (prod : Nat) :=
    if mask.testBit j then 0 else (2 : Int)^power * histogramDigit (prod*f^(6-j))
  (histogramDigit all,cell 0 4 1 + cell 1 3 x + cell 2 2 y + cell 3 1 z + cell 4 0 u)

private theorem prefix_small (b : CodePosition → Nat) (h : ∀ j,b j ≤ 9) (d : Depth) :
    ∀ j, prefixBound b d j ≤ 9 := by intro j; unfold prefixBound; split <;> simp [h]

theorem supply_fst (mask : Nat) (b : CodePosition → Nat) (h : ∀ j,b j ≤ 9) :
    (supplierCounts mask b).1 = packedAvoidance b := by
  rw [box_count b h]
  unfold supplierCounts six
  dsimp only
  congr 1 <;> ac_rfl

theorem supply_snd (mask : Nat) (b : CodePosition → Nat) (h : ∀ j,b j ≤ 9) :
    (supplierCounts mask b).2 =
      ∑ d : Depth, if depthPosition d ∈ requirementsOfMask mask then 0 else
        (2:Int)^(4-d.val) * packedAvoidance (prefixBound b d) := by
  simp_rw [box_count _ (prefix_small b h _)]
  simp [supplierCounts, Fin.sum_univ_succ, requirementsOfMask,depthPosition,
    six,prefixBound,Fin.reduceFinMk, Nat.mul_assoc, pow_succ, Int.add_assoc]

def directLeaf (m v mask : Nat) (digits : List Nat) : Int :=
  let s := selectedPositions mask
  let n := completionFormula (6-s.length) (16-digits.sum)
  if n = 0 then 0 else
    let b := listBound s digits
    if decide (∀ i : CodePosition, b i ≤ 9) then
      let x := supplierCounts mask b
      n * (subsetSign mask * x.1^v * x.2^(m-v))
    else n * packedMoment m v mask b

theorem directLeaf_eq (m v mask : Nat) : directLeaf m v mask = packedLeaf m v mask := by
  funext digits
  unfold directLeaf packedLeaf
  dsimp only
  split
  · rfl
  · split
    next small =>
      have h := of_decide_eq_true small
      simp only [supply_fst _ _ h,supply_snd _ _ h,packedMoment]
    next => rfl

def directMask (m v mask : Nat) : Int :=
  PrunedDigits.fold (selectedPositions mask).length 16 (directLeaf m v mask)

theorem direct_of_sum (m v cap : Nat) (hv : 0 < v) (hvm : v ≤ m)
    (checked : ((List.range 63).map (directMask m v)).sum * 1000000 ≤
      (cap : Int) * (15597^(m+1)*31^(m-v) : Nat)) :
    localCover m v ≤ (cap : Rat)/1000000 := by
  apply localCover_of_packed m v cap hv hvm
  have id : ((List.range 63).map (directMask m v)).sum = packedNumerator m v := by
    unfold packedNumerator
    apply congrArg List.sum
    apply List.map_congr_left
    intro mask _
    unfold directMask
    rw [directLeaf_eq]
  rw [← id]
  exact checked

end PoissonDAG.GRSCC.Small
