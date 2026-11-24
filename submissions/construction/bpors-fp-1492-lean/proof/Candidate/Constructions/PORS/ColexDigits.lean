import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find

/-! Natural-number specification of the descending binary search in
`RankGates.unrank`. Each accepted colex rank recovers its value from its
selected leaves. The circuit-to-integer correspondence is a separate lemma. -/
namespace PoissonDAG.PORS.Colex

/-- Test the remaining bits from most to least significant. The current prefix
has zero bits in all the remaining positions. -/
def liftBits (test : Nat → Bool) : Nat → Nat → Nat
  | 0, base => base
  | n+1, base =>
    let next := base + 2^n
    liftBits test n (if test next then next else base)

theorem liftBits_exact {test : Nat → Bool} {limit : Nat}
    (spec : ∀ n, test n = true ↔ n ≤ limit) (n base : Nat)
    (lo : base ≤ limit) (hi : limit < base + 2^n) :
    liftBits test n base = limit := by
  induction n generalizing base with
  | zero => simp only [Nat.pow_zero] at hi; simp only [liftBits]; omega
  | succ n ih =>
    rw [Nat.pow_succ] at hi
    simp only [liftBits]
    split
    next h => exact ih _ ((spec _).mp h) (by omega)
    next h =>
      have hn := mt (spec _).mpr h
      exact ih _ lo (by omega)

def largest (t j r : Nat) :=
  Nat.findGreatest (fun v => v.choose j ≤ r) (t-1)

private theorem fits {t k r : Nat} :
    (largest t (k+1) r).choose (k+1) ≤ r := by
  unfold largest
  exact Nat.findGreatest_spec (P := fun v => v.choose (k+1) ≤ r) (m := 0) (Nat.zero_le _) (show (0 : Nat).choose (k+1) ≤ r by simp)

theorem search_spec {t k r : Nat} (ht : 0 < t) (v : Nat) :
    (v.choose (k+1) ≤ r ∧ v < t) ↔ v ≤ largest t (k+1) r := by
  constructor
  · rintro ⟨hc,hv⟩
    exact Nat.le_findGreatest (by omega) hc
  · intro hv
    have hb : largest t (k+1) r ≤ t-1 := Nat.findGreatest_le _
    exact ⟨(Nat.choose_le_choose _ hv).trans fits, by omega⟩

theorem search_eq {t k r : Nat} (ht : 0 < t) :
    liftBits (fun v => decide (v.choose (k+1) ≤ r ∧ v<t))
        (Nat.log2 (t-1)+1) 0 = largest t (k+1) r := by
  apply liftBits_exact
  · intro v; simpa using search_spec (k := k) (r := r) ht v
  · omega
  · have hb : largest t (k+1) r ≤ t-1 := Nat.findGreatest_le _
    have hp : t-1 < 2^(Nat.log2 (t-1)+1) := by
      by_cases h : t-1 = 0
      · simp [h]
      · exact (Nat.log2_lt h).mp (Nat.lt_succ_self _)
    omega

/-- The next colex rank is strictly below the number of k-subsets of [0,v).
This strict inequality is what forces the following digit to be smaller. -/
theorem remainder_bound {t n k r : Nat} (hn : n ≤ t) (hr : r < n.choose (k+1)) :
    let v := largest t (k+1) r
    v < n ∧ r-v.choose (k+1) < v.choose k := by
  let v := largest t (k+1) r
  have hc : v.choose (k+1) ≤ r := fits
  have hv : v < n := by
    by_contra! h
    exact (not_le_of_gt hr) ((Nat.choose_le_choose _ h).trans hc)
  have hnext : r < (v+1).choose (k+1) := by
    by_contra! h
    by_cases hvt : v+1 < t
    · have hlarge : v+1 ≤ v :=
        (search_spec (k := k) (r := r) (by omega : 0<t) _).mp ⟨h,hvt⟩
      omega
    · have : v+1=n := by omega
      rw [this] at h
      omega
  rw [Nat.choose_succ_succ'] at hnext
  change v<n ∧ r-v.choose (k+1)<v.choose k
  exact ⟨hv,by omega⟩

/-- Digits in the order the greedy decoder discovers them (largest first). -/
def digits (t : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k+1, r =>
    let v := largest t (k+1) r
    v :: digits t k (r-v.choose (k+1))

def encode : List Nat → Nat
  | [] => 0
  | v :: tail => v.choose (tail.length+1) + encode tail

@[simp] theorem digits_length (t k r : Nat) : (digits t k r).length = k := by
  induction k generalizing r <;> simp [digits, *]

theorem digits_spec {t n k r : Nat} (hn : n ≤ t) (hr : r < n.choose k) :
    encode (digits t k r) = r ∧ (∀ v ∈ digits t k r, v < n) ∧
      (digits t k r).Pairwise (· > ·) := by
  induction k generalizing n r with
  | zero =>
    simp only [Nat.choose_zero_right] at hr
    have hz : r = 0 := by omega
    simp [digits, encode, hz]
  | succ k ih =>
    let v := largest t (k+1) r
    obtain ⟨hv, remLt⟩ := remainder_bound hn hr
    obtain ⟨henc, hlt, hsort⟩ := ih (le_trans (Nat.le_of_lt hv) hn) remLt
    have hc : v.choose (k+1) ≤ r := fits
    change encode (v :: digits t k (r-v.choose (k+1))) = r ∧ _
    refine ⟨?_, ?_, ?_⟩
    · simp only [encode, digits_length]
      exact (congrArg (v.choose (k+1) + ·) henc).trans (Nat.add_sub_of_le hc)
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hv
      · exact (hlt z hz).trans hv
    · exact List.pairwise_cons.mpr ⟨hlt, hsort⟩

theorem digits_injective {t k x y : Nat} (hx : x < t.choose k) (hy : y < t.choose k)
    (h : digits t k x = digits t k y) : x = y :=
  (digits_spec (Nat.le_refl t) hx).1.symm.trans <|
    (congrArg encode h).trans (digits_spec (Nat.le_refl t) hy).1

end PoissonDAG.PORS.Colex
