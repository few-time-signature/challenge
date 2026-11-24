import PoissonDAG.Constructions.PORS.SingleRefinedSupport
import PoissonDAG.Constructions.PORS.LiteralCosts
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

namespace PoissonDAG.PORS.PrunedCount

/-- Addresses of individual leaves, with the two children of every branch disjoint. -/
def Leaf : Shape → Type
  | .leaf => Unit
  | .branch l r => Leaf l ⊕ Leaf r

instance leafFintype : (s : Shape) → Fintype (Leaf s)
  | .leaf => inferInstanceAs (Fintype Unit)
  | .branch l r =>
    letI := leafFintype l
    letI := leafFintype r
    inferInstanceAs (Fintype (Leaf l ⊕ Leaf r))

theorem card_leaf (s : Shape) : Fintype.card (Leaf s) = s.leaves := by
  induction s with
  | leaf => rfl
  | branch l r il ir =>
    change Fintype.card (Leaf l ⊕ Leaf r) = l.leaves + r.leaves
    rw [Fintype.card_sum, il, ir]

/-- Exactly one extra sibling is transmitted if exactly one child is active. -/
def extraSibling (a b : Nat) := if (a = 0 ∨ b = 0) ∧ a+b ≠ 0 then 1 else 0

def siblings : (s : Shape) → Finset (Leaf s) → Nat
  | .leaf, _ => 0
  | .branch l r, u =>
    siblings l u.toLeft + siblings r u.toRight + extraSibling u.toLeft.card u.toRight.card

@[simp] theorem siblings_empty (s : Shape) : siblings s ∅ = 0 := by
  induction s with
  | leaf => rfl
  | branch l r il ir =>
    let u : Finset (Leaf (.branch l r)) := ∅
    have hl : u.toLeft = ∅ := by
      ext x
      simp [u]
      exact Finset.notMem_empty (Sum.inl x : Leaf l ⊕ Leaf r)
    have hr : u.toRight = ∅ := by
      ext x
      simp [u]
      exact Finset.notMem_empty (Sum.inr x : Leaf l ⊕ Leaf r)
    change siblings l u.toLeft + siblings r u.toRight + extraSibling u.toLeft.card u.toRight.card = 0
    rw [hl, hr, il, ir] <;> rfl

/-- Every subset of the specified cardinality contributes its own monomial. -/
def pack (s : Shape) (B j : Nat) :=
  ∑ u ∈ (Finset.univ : Finset (Leaf s)).powersetCard j, B^(siblings s u)

private theorem pack_ite (s : Shape) (B j : Nat) :
    pack s B j = ∑ u : Finset (Leaf s), if u.card = j then B^(siblings s u) else 0 := by
  classical
  rw [← Finset.sum_filter, Finset.univ_filter_card_eq] <;> rfl

@[simp] theorem pack_zero (s : Shape) (B : Nat) : pack s B 0 = 1 := by
  classical
  simp [pack]

private theorem single_split (a b L R B j : Nat) (hj : 0 < j) :
    (if a+b = j then L*R*B^(extraSibling a b) else 0) =
      ∑ i ∈ Finset.range (j+1),
        (if a=i then L else 0) * (if b=j-i then R else 0) *
          (if i=0 ∨ i=j then B else 1) := by
  classical
  by_cases hab : a ≤ j
  · rw [Finset.sum_eq_single a]
    · by_cases he : a+b = j
      · have hb : b = j-a := by omega
        have hz : (a=0 ∨ b=0) ↔ (a=0 ∨ a=j) := by omega
        rw [if_pos he, if_pos rfl, if_pos hb]
        by_cases ha : a=0 ∨ a=j
        · simp [extraSibling, hz.mpr ha, he, hj.ne', ha]
        · have hn : ¬(a=0 ∨ b=0) := fun hh => ha (hz.mp hh)
          simp [extraSibling, hn, ha]
      · have hn : b ≠ j-a := by omega
        simp [he, hn]
    · intro i hi hia
      simp [Ne.symm hia]
    · intro ha
      exact (ha (Finset.mem_range.mpr (by omega))).elim
  · have he : a+b ≠ j := by omega
    rw [if_neg he]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [show a ≠ i by omega]

private theorem pack_branch (l r : Shape) (B j : Nat) (hj : 0 < j) :
    pack (.branch l r) B j =
      ∑ i ∈ Finset.range (j+1),
        pack l B i * pack r B (j-i) * (if i=0 ∨ i=j then B else 1) := by
  classical
  let term := fun (u : Finset (Leaf l)) (v : Finset (Leaf r)) (i : Nat) =>
    (if u.card=i then B^(siblings l u) else 0) *
      (if v.card=j-i then B^(siblings r v) else 0) * (if i=0 ∨ i=j then B else 1)
  calc
    _ = ∑ u : Finset (Leaf l), ∑ v : Finset (Leaf r),
        (if u.card+v.card=j then
          B^(siblings l u) * B^(siblings r v) * B^(extraSibling u.card v.card) else 0) := by
      let w := fun z : Finset (Leaf l) × Finset (Leaf r) =>
        if z.1.card+z.2.card=j then
          B^(siblings l z.1) * B^(siblings r z.2) * B^(extraSibling z.1.card z.2.card) else 0
      rw [pack_ite]
      trans ∑ z, w z
      · apply Fintype.sum_equiv Finset.sumEquiv.toEquiv
        intro u
        change (if u.card=j then B^(siblings (.branch l r) u) else 0) =
          if u.toLeft.card+u.toRight.card=j then
            B^(siblings l u.toLeft) * B^(siblings r u.toRight) *
              B^(extraSibling u.toLeft.card u.toRight.card) else 0
        simp only [Finset.card_toLeft_add_card_toRight, siblings, pow_add]
      · exact Fintype.sum_prod_type w
    _ = ∑ u : Finset (Leaf l), ∑ v : Finset (Leaf r), ∑ i ∈ Finset.range (j+1),
          term u v i := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro v _
      exact single_split _ _ _ _ _ _ hj
    _ = ∑ u : Finset (Leaf l), ∑ i ∈ Finset.range (j+1), ∑ v : Finset (Leaf r),
          term u v i := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [pack_ite, Finset.sum_mul, Finset.mul_sum, term]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)

private def mergeRow (k B : Nat) (left right : List Nat) : List Nat :=
  (List.range (k+1)).map fun j =>
    if j=0 then 1 else ((List.range (j+1)).map (fun i =>
      left[i]?.getD 0 * right[j-i]?.getD 0 * (if i=0 ∨ i=j then B else 1))).sum

private def table (k B : Nat) : Shape → List Nat
  | .leaf => [1,1]
  | .branch l r => mergeRow k B (table k B l) (table k B r)

private theorem sum_range (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem table_lookup (s : Shape) (B k j : Nat) (h : j ≤ k) :
    (table k B s)[j]?.getD 0 = pack s B j := by
  induction s generalizing j with
  | leaf =>
    have hp : pack .leaf B j = Nat.choose 1 j := by
      simp [pack, siblings, card_leaf, Shape.leaves]
    rw [hp]
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ j => rw [Nat.choose_eq_zero_of_lt (by omega)] <;> rfl
  | branch l r il ir =>
    simp only [table, mergeRow, List.getElem?_map, List.getElem?_range (show j<k+1 by omega),
      Option.map_some, Option.getD_some]
    by_cases hj : j=0
    · subst j
      simp
    · rw [if_neg hj, sum_range, pack_branch l r B j (by omega)]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [il i (by omega), ir (j-i) (by omega)]

private theorem table_untouched (k B h : Nat) :
    table k B (Literal.leftShape h 0) = packedLevels k B h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [Literal.leftShape, Nat.min_zero, Nat.zero_sub, table, ih] <;> rfl

private theorem table_full (k B h : Nat) :
    table k B (Literal.leftShape h (2^h)) = packedLevels k B (h+1) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    have hmin : min (2^h) (2^(h+1)) = 2^h := Nat.min_eq_left (by rw [pow_succ]; omega)
    have hsub : 2^(h+1) - 2^h = 2^h := by rw [pow_succ]; omega
    simp only [Literal.leftShape, hmin, hsub, table, ih] <;> rfl

theorem table_leftFilled (k B h extra : Nat) :
    table k B (Literal.leftShape h extra) = leftFilled k B h extra := by
  induction h generalizing extra with
  | zero => by_cases hn : extra=0 <;> simp [Literal.leftShape, leftFilled, hn] <;> rfl
  | succ h ih =>
    by_cases hz : extra=0
    · subst extra
      rw [table_untouched]
      simp [leftFilled]
    · by_cases hf : extra=2^(h+1)
      · subst extra
        rw [table_full]
        simp [leftFilled, hz]
      · simp only [Literal.leftShape, leftFilled, hz, hf, if_false, table, ih] <;> rfl

/-- The cached recurrence is the sum over distinct leaf subsets of the actual literal shape. -/
theorem packed_leftFilled (k B h extra j : Nat) (hj : j ≤ k) :
    (leftFilled k B h extra)[j]?.getD 0 = pack (Literal.leftShape h extra) B j := by
  rw [← table_leftFilled]
  exact table_lookup _ B k j hj

/-- With strictly fewer than B-1 supports, truncating in base B and reducing
modulo B-1 extracts the number of all supports up to the given degree. -/
theorem truncated_card {α : Type*} (domain : Finset α) (d : α → Nat) (B M : Nat)
    (capacity : domain.card < B-1) :
    ((∑ a ∈ domain, B^(d a)) % B^(M+1)) % (B-1) =
      (domain.filter (fun a => d a ≤ M)).card := by
  classical
  let low := domain.filter (fun a => d a ≤ M)
  have hb : 1 ≤ B := by omega
  have hcard : low.card < B-1 :=
    lt_of_le_of_lt (Finset.card_filter_le _ _) capacity
  have htrim : (∑ a ∈ domain, B^(d a)) ≡ ∑ a ∈ low, B^(d a) [MOD B^(M+1)] := by
    dsimp only [low]
    rw [Finset.sum_filter]
    apply Nat.ModEq.sum
    intro a _
    by_cases ha : d a ≤ M
    · rw [if_pos ha]
    · rw [if_neg ha]
      exact (pow_dvd_pow B (show M+1 ≤ d a by omega)).modEq_zero_nat
  have hbound : (∑ a ∈ low, B^(d a)) < B^(M+1) := by
    calc
      _ ≤ low.card * B^M := by
        have hh := low.sum_le_card_nsmul (fun a => B^(d a)) (B^M) (fun a ha =>
          pow_le_pow_right₀ hb ((Finset.mem_filter.mp ha).2))
        simpa using hh
      _ < B * B^M := Nat.mul_lt_mul_of_pos_right (by omega) (pow_pos (by omega) _)
      _ = _ := (pow_succ' B M).symm
  have hfirst : (∑ a ∈ domain, B^(d a)) % B^(M+1) = ∑ a ∈ low, B^(d a) :=
    Eq.trans htrim (Nat.mod_eq_of_lt hbound)
  have hbase : B ≡ 1 [MOD B-1] :=
    ((Nat.modEq_iff_dvd' hb).mpr (dvd_refl (B-1))).symm
  have hflat : (∑ a ∈ low, B^(d a)) ≡ low.card [MOD B-1] := by
    have hh : (∑ a ∈ low, B^(d a)) ≡ ∑ _a ∈ low, (1 : Nat) [MOD B-1] :=
      Nat.ModEq.sum (fun a _ => by simpa using hbase.pow (d a))
    simpa using hh
  rw [hfirst]
  exact Eq.trans hflat (Nat.mod_eq_of_lt hcard)

/-- The exact surviving support count for the first production row, using the
actual left-filled child tree. The supports are ordinary subsets, before the
Boolean rank decoder maps raw input words to them. -/
theorem single_support_count :
    let s := Literal.shape SingleRefined.p.t
    (((Finset.univ : Finset (Leaf s)).powersetCard SingleRefined.p.k).filter
      (fun u => siblings s u ≤ SingleRefined.p.M)).card = SingleRefined.p.acceptedWords := by
  let p := SingleRefined.p
  let s := Literal.shape p.t
  let B := 2^(p.r+2)
  let domain := (Finset.univ : Finset (Leaf s)).powersetCard p.k
  have ht : 0 < p.t := by decide +kernel
  have capacity : domain.card < B-1 := by
    dsimp only [domain, s]
    rw [Finset.card_powersetCard, Finset.card_univ, card_leaf, Literal.shape_card _ ht,
      Nat.choose_eq_fast_choose]
    decide +kernel
  have hshape : s = Literal.leftShape 18 229376 := by
    change Literal.leftShape (Nat.log2 p.t) (p.t-2^(Nat.log2 p.t)) = _
    rw [show Nat.log2 p.t = 18 by decide +kernel, show p.t-2^18 = 229376 by decide +kernel]
  have hp := packed_leftFilled p.k B 18 229376 p.k (le_refl _)
  rw [← hshape] at hp
  change (domain.filter (fun u => siblings s u ≤ p.M)).card = p.acceptedWords
  calc
    _ = (pack s B p.k % B^(p.M+1)) % (B-1) :=
      (truncated_card domain (siblings s) B p.M capacity).symm
    _ = p.leftFilledWords 18 229376 := by
      unfold Row.leftFilledWords
      change _ = (((leftFilled p.k B 18 229376)[p.k]?.getD 0)^p.K %
          B^(p.M+1) % (B-1)) * (p.buckets*p.depthCount)^p.K
      rw [hp]
      simp only [show p.K=1 by rfl, show p.buckets=1 by rfl,
        show p.depthCount=1 by rfl, pow_one, one_mul, mul_one]
    _ = _ := SingleRefined.accepted_word_count_replay.2

/-- Number leaves in the offset order used by Literal.atShape. -/
def leafIndex : (s : Shape) → Leaf s ≃ Fin s.leaves
  | .leaf => finOneEquiv.symm
  | .branch l r => ((leafIndex l).sumCongr (leafIndex r)).trans finSumFinEquiv

@[simp] theorem leafIndex_left (l r : Shape) (x : Leaf l) :
    (leafIndex (.branch l r) (.inl x)).val = (leafIndex l x).val := rfl

@[simp] theorem leafIndex_right (l r : Shape) (x : Leaf r) :
    (leafIndex (.branch l r) (.inr x)).val = l.leaves + (leafIndex r x).val := rfl

end PoissonDAG.PORS.PrunedCount
