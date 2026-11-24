import PoissonDAG.Constructions.GRSCC.MaskedCounts
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 100000
set_option maxRecDepth 1000

/-!
# A pruned list traversal of masked positive assignments

The executable recurrence enumerates positive natural-number digits directly.
Its generic sum theorem is separate from the GRS-CC specialization. The existing
composition formula, different-history moment, and completion formula are
unchanged; no table or numerical checkpoint enters the correspondence.
-/

namespace PoissonDAG.PrunedDigits

/-- Choose positive digits at most eight, pruning by the remaining sum budget. -/
def fold : Nat → Nat → (List Nat → Int) → Int
  | 0, _, weight => weight []
  | n + 1, budget, weight =>
      ((List.range (min 8 budget)).map (fun digit =>
        fold n (budget - (digit + 1)) (fun tail => weight ((digit + 1) :: tail)))).sum

def tupleDigits {n : Nat} (a : Fin n → Fin 8) : List Nat :=
  List.ofFn (fun i => (a i).val + 1)

theorem tupleDigits_cons {n : Nat} (head : Fin 8) (tail : Fin n → Fin 8) :
    tupleDigits (Fin.cons head tail) = (head.val + 1) :: tupleDigits tail := by
  simp [tupleDigits, List.ofFn_succ]

private theorem sum_range_min (budget : Nat) (weight : Nat → Int) :
    ((List.range (min 8 budget)).map weight).sum =
      ∑ digit : Fin 8, if digit.val < budget then weight digit.val else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun digit => if digit < budget then weight digit else 0)]
  have hsub : Finset.range (min 8 budget) ⊆ Finset.range 8 := by
    intro digit hdigit
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp hdigit) (Nat.min_le_left _ _))
  calc
    _ = ∑ digit ∈ Finset.range (min 8 budget), weight digit := by
      rw [← List.sum_toFinset weight List.nodup_range, List.toFinset_range]
    _ = ∑ digit ∈ Finset.range (min 8 budget),
        if digit < budget then weight digit else 0 := by
      apply Finset.sum_congr rfl
      intro digit hdigit
      rw [if_pos (lt_of_lt_of_le (Finset.mem_range.mp hdigit) (Nat.min_le_right _ _))]
    _ = _ := Finset.sum_subset hsub (by
      intro digit hdigit hnot
      have hnotmin : ¬digit < min 8 budget := by simpa only [Finset.mem_range] using hnot
      have hlarge : ¬digit < budget := by
        intro hsmall
        exact hnotmin (lt_min (Finset.mem_range.mp hdigit) hsmall)
      exact if_neg hlarge)

/-- The recurrence is exactly the guarded sum over all bounded tuples. -/
theorem fold_eq_sum (n budget : Nat) (weight : List Nat → Int) :
    fold n budget weight =
      ∑ a : Fin n → Fin 8,
        if (tupleDigits a).sum ≤ budget then weight (tupleDigits a) else 0 := by
  induction n generalizing budget weight with
  | zero => simp [fold, tupleDigits]
  | succ n ih =>
      let term : (Fin (n + 1) → Fin 8) → Int := fun a =>
        if (tupleDigits a).sum ≤ budget then weight (tupleDigits a) else 0
      have hsplit : (∑ a, term a) =
          ∑ head : Fin 8, ∑ tail : Fin n → Fin 8, term (Fin.cons head tail) := by
        calc
          _ = ∑ pair : Fin 8 × (Fin n → Fin 8), term (Fin.cons pair.1 pair.2) := by
            symm
            exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 8))
              _ _ (fun _ => rfl)
          _ = _ := Fintype.sum_prod_type _
      change fold (n + 1) budget weight = ∑ a, term a
      rw [hsplit, fold, sum_range_min]
      apply Finset.sum_congr rfl
      intro head _
      by_cases hhead : head.val < budget
      · rw [if_pos hhead, ih]
        apply Finset.sum_congr rfl
        intro tail _
        change
          (if (tupleDigits tail).sum ≤ budget - (head.val + 1) then
            weight ((head.val + 1) :: tupleDigits tail) else 0) =
          (if (tupleDigits (Fin.cons head tail)).sum ≤ budget then
            weight (tupleDigits (Fin.cons head tail)) else 0)
        rw [tupleDigits_cons, List.sum_cons]
        have hguard : (tupleDigits tail).sum ≤ budget - (head.val + 1) ↔
            head.val + 1 + (tupleDigits tail).sum ≤ budget := by omega
        simp only [hguard]
      · rw [if_neg hhead]
        symm
        apply Finset.sum_eq_zero
        intro tail _
        change (if (tupleDigits (Fin.cons head tail)).sum ≤ budget then
          weight (tupleDigits (Fin.cons head tail)) else 0) = 0
        rw [tupleDigits_cons, List.sum_cons, if_neg (by omega)]

end PoissonDAG.PrunedDigits

namespace PoissonDAG.GRSCC.Small

open PoissonDAG.PrunedDigits

def selectedPositions (mask : Nat) : List CodePosition :=
  (List.finRange 6).filter (fun j => mask.testBit j.val)

theorem selectedPositions_mem (mask : Nat) (j : CodePosition) :
    j ∈ selectedPositions mask ↔ j ∈ requirementsOfMask mask := by
  simp [selectedPositions, requirementsOfMask]

theorem selectedPositions_nodup (mask : Nat) : (selectedPositions mask).Nodup :=
  (List.nodup_finRange 6).filter _

theorem selectedPositions_toFinset (mask : Nat) :
    (selectedPositions mask).toFinset = requirementsOfMask mask := by
  ext j
  exact List.mem_toFinset.trans (selectedPositions_mem mask j)

theorem selectedPositions_length (mask : Nat) :
    (selectedPositions mask).length = (requirementsOfMask mask).card := by
  calc
    _ = (selectedPositions mask).toFinset.card :=
      (List.toFinset_card_of_nodup (selectedPositions_nodup mask)).symm
    _ = _ := congrArg Finset.card (selectedPositions_toFinset mask)

private def positionEquiv (mask : Nat) :
    Fin (selectedPositions mask).length ≃ requirementsOfMask mask :=
  (List.Nodup.getEquiv (selectedPositions mask) (selectedPositions_nodup mask)).trans
    (Equiv.subtypeEquivRight (fun j => selectedPositions_mem mask j))

private def orderedAssignmentEquiv (mask : Nat) :
    (requirementsOfMask mask → Fin 8) ≃ (Fin (selectedPositions mask).length → Fin 8) where
  toFun a i := a (positionEquiv mask i)
  invFun a j := a ((positionEquiv mask).symm j)
  left_inv a := by funext j; simp only [Equiv.apply_symm_apply]
  right_inv a := by funext i; simp only [Equiv.symm_apply_apply]

def assignmentDigits (mask : Nat) (a : requirementsOfMask mask → Fin 8) : List Nat :=
  (selectedPositions mask).map (assignmentBound (requirementsOfMask mask) a)

private theorem assignmentDigits_eq_tuple (mask : Nat)
    (a : requirementsOfMask mask → Fin 8) :
    assignmentDigits mask a = tupleDigits (orderedAssignmentEquiv mask a) := by
  calc
    _ = List.ofFn (fun i : Fin (selectedPositions mask).length =>
        assignmentBound (requirementsOfMask mask) a ((selectedPositions mask).get i)) :=
      (List.ofFn_getElem_eq_map (selectedPositions mask) _).symm
    _ = _ := by
      congr 1
      funext i
      change assignmentBound (requirementsOfMask mask) a (positionEquiv mask i).val =
        (a (positionEquiv mask i)).val + 1
      simp only [assignmentBound, dif_pos (positionEquiv mask i).property, Subtype.coe_eta]

theorem assignmentDigits_sum (mask : Nat) (a : requirementsOfMask mask → Fin 8) :
    (assignmentDigits mask a).sum = assignmentSum (requirementsOfMask mask) a := by
  calc
    _ = ∑ j ∈ (selectedPositions mask).toFinset,
        assignmentBound (requirementsOfMask mask) a j :=
      (List.sum_toFinset _ (selectedPositions_nodup mask)).symm
    _ = ∑ j ∈ requirementsOfMask mask, assignmentBound (requirementsOfMask mask) a j := by
      rw [selectedPositions_toFinset]
    _ = ∑ j : requirementsOfMask mask, assignmentBound (requirementsOfMask mask) a j.val :=
      (Finset.sum_coe_sort _ _).symm
    _ = assignmentSum (requirementsOfMask mask) a := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [assignmentBound, dif_pos j.property, Subtype.coe_eta]

theorem fold_eq_assignments (mask budget : Nat) (weight : List Nat → Int) :
    fold (selectedPositions mask).length budget weight =
      ∑ a : requirementsOfMask mask → Fin 8,
        if assignmentSum (requirementsOfMask mask) a ≤ budget then
          weight (assignmentDigits mask a) else 0 := by
  rw [fold_eq_sum]
  symm
  apply Fintype.sum_equiv (orderedAssignmentEquiv mask)
  intro a
  rw [← assignmentDigits_eq_tuple, assignmentDigits_sum]

/-- Lookup along a position list, with nine on every unassigned position. -/
def listBound : List CodePosition → List Nat → CodePosition → Nat
  | [], _, _ => 9
  | _ :: _, [], _ => 9
  | position :: positions, digit :: digits, j =>
      if j = position then digit else listBound positions digits j

theorem listBound_map (positions : List CodePosition) (bound : CodePosition → Nat)
    (j : CodePosition) :
    listBound positions (positions.map bound) j = if j ∈ positions then bound j else 9 := by
  induction positions with
  | nil => simp [listBound]
  | cons position positions ih =>
      by_cases hj : j = position
      · subst j
        simp [listBound]
      · simp [listBound, hj, ih]

theorem listBound_assignmentDigits (mask : Nat) (a : requirementsOfMask mask → Fin 8) :
    listBound (selectedPositions mask) (assignmentDigits mask a) =
      assignmentBound (requirementsOfMask mask) a := by
  funext j
  rw [assignmentDigits, listBound_map]
  by_cases hj : j ∈ selectedPositions mask
  · rw [if_pos hj]
  · have hnot : j ∉ requirementsOfMask mask := (selectedPositions_mem mask j).not.mp hj
    simp only [if_neg hj, assignmentBound, dif_neg hnot]

/-- The existing moment expression with its bounded-coordinate function supplied
directly. Neither bounded-composition factor is changed. -/
def momentFromBounds (m v mask : Nat) (bound : CodePosition → Nat) : Int :=
  subsetSign mask * compositionFormula bound ^ v *
    (∑ depth : Depth, if depthPosition depth ∈ requirementsOfMask mask then 0 else
      (2 : Int) ^ (4 - depth.val) * compositionFormula (prefixBound bound depth)) ^ (m - v)

def traversalLeaf (m v mask : Nat) (digits : List Nat) : Int :=
  let completions := completionFormula (6 - (selectedPositions mask).length) (16 - digits.sum)
  if completions = 0 then 0 else completions *
    momentFromBounds m v mask (listBound (selectedPositions mask) digits)

theorem traversalLeaf_assignmentDigits (m v mask : Nat)
    (a : requirementsOfMask mask → Fin 8) :
    traversalLeaf m v mask (assignmentDigits mask a) =
      let completions := completionFormula
        (Fintype.card (FreePositions (requirementsOfMask mask)))
        (16 - assignmentSum (requirementsOfMask mask) a)
      if completions = 0 then 0 else completions * maskedMoment m v mask a := by
  simp only [traversalLeaf, selectedPositions_length, assignmentDigits_sum, freePositions_card]
  rw [listBound_assignmentDigits]
  rfl

def traversalNumerator (m v : Nat) : Int :=
  ((List.range 63).map (fun mask =>
    fold (selectedPositions mask).length 16 (traversalLeaf m v mask))).sum

theorem traversalNumerator_eq_guarded (m v : Nat) :
    traversalNumerator m v = guardedNumerator m v := by
  unfold traversalNumerator
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]
  unfold guardedNumerator
  apply Finset.sum_congr rfl
  intro mask _
  rw [fold_eq_assignments]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hsum : assignmentSum (requirementsOfMask mask.val) a ≤ 16
  · simp only [if_pos hsum]
    exact traversalLeaf_assignmentDigits m v mask.val a
  · simp only [if_neg hsum]

def traversalCapCheck (m v cap : Nat) : Bool :=
  decide (traversalNumerator m v * 1000000 ≤
    (cap : Int) * (15597 ^ (m + 1) * 31 ^ (m - v) : Nat))

theorem traversalCapCheck_eq (m v cap : Nat) :
    traversalCapCheck m v cap = localCapCheck m v cap := by
  simp only [traversalCapCheck, localCapCheck, traversalNumerator_eq_guarded]

theorem traversalCapCheck_sound (m v cap : Nat) (hv : 0 < v) (hvalid : v ≤ m)
    (hcheck : traversalCapCheck m v cap = true) :
    localCover m v ≤ (cap : Rat) / 1000000 := by
  apply localCapCheck_sound m v cap hv hvalid
  rw [← traversalCapCheck_eq]
  exact hcheck

end PoissonDAG.GRSCC.Small
