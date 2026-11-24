import PoissonDAG.Constructions.PORS.RankGates
import PoissonDAG.Constructions.PORS.SingleRefinedRow
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PoissonDAG.PORS.RankBounds

/-- The sum after processing the first i multiplier bits, truncating both
each shifted addend and the running sum to the word modulus. -/
def shiftSum (m a b : Nat) : Nat → Nat
  | 0 => 0
  | i+1 => (shiftSum m a b i + if b.testBit i then (a*2^i)%m else 0) % m

theorem shiftSum_eq (m a b i : Nat) : shiftSum m a b i = (a*(b%2^i))%m := by
  induction i with
  | zero => simp [shiftSum, Nat.mod_one]
  | succ i ih =>
    rw [shiftSum, ih, Nat.pow_succ, Nat.mod_mul (x := b) (a := 2^i) (b := 2)]
    by_cases hb : b / 2^i % 2 = 1
    · simp [Nat.testBit_eq_decide_div_mod_eq, hb, Nat.mul_add]
    · have hz : b / 2^i % 2 = 0 := by omega
      simp [Nat.testBit_eq_decide_div_mod_eq, hb, hz]

theorem shiftSum_full (m a b w : Nat) (hb : b < 2^w) :
    shiftSum m a b w = (a*b)%m := by rw [shiftSum_eq, Nat.mod_eq_of_lt hb]

/-- One digit of restoring division. The shifted remainder and the
subtraction are the two word-sized intermediate values. -/
def restoreStep (m d : Nat) (state : Nat × Nat) (bit : Nat) : Nat × Nat :=
  let shifted := (2*state.2+bit)%m
  if d ≤ shifted then (2*state.1+1, (shifted+m-d)%m) else (2*state.1, shifted)

theorem shifted_fits {m d r bit : Nat} (guard : 2*d ≤ m) (hr : r < d) (hb : bit < 2) :
    2*r+bit < m := by omega

theorem restoreStep_eq (m d x b : Nat) (hd : 0 < d) (guard : 2*d ≤ m) (hb : b < 2) :
    restoreStep m d (x/d,x%d) b = ((2*x+b)/d,(2*x+b)%d) := by
  let z := 2*(x%d)+b
  have hr := Nat.mod_lt x hd
  have hz : z < 2*d := by dsimp [z]; omega
  have fit : z < m := hz.trans_le guard
  have split : z + d*(2*(x/d)) = 2*x+b := by
    dsimp [z]
    have hx := Nat.mod_add_div x d
    nlinarith only [hx]
  change (if d ≤ z%m then (2*(x/d)+1, (z%m+m-d)%m) else (2*(x/d), z%m)) = _
  rw [Nat.mod_eq_of_lt fit]
  by_cases hz' : d ≤ z
  · rw [if_pos hz', show z+m-d = (z-d)+m by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show z-d < m by omega)]
    have hsub : z-d+d = z := by omega
    have correct := (Nat.div_mod_unique (a := 2*x+b) (d := 2*(x/d)+1) (c := z-d) hd).mpr
      ⟨by rw [Nat.mul_add, Nat.mul_one]; omega, by omega⟩
    rw [correct.1, correct.2]
  · rw [if_neg hz']
    have correct := (Nat.div_mod_unique (a := 2*x+b) (d := 2*(x/d)) (c := z) hd).mpr
      ⟨split, by omega⟩
    rw [correct.1, correct.2]

/-- The w-digit division trace, in most-significant-first order. The
recursive call processes the prefix, and the final step appends the low bit. -/
def restoreWidth (m d : Nat) : Nat → Nat → Nat × Nat
  | 0, _ => (0,0)
  | w+1, x => restoreStep m d (restoreWidth m d w (x/2)) (x%2)

theorem restoreWidth_eq (m d : Nat) (hd : 0 < d) (guard : 2*d ≤ m)
    (w x : Nat) (hx : x < 2^w) : restoreWidth m d w x = (x/d,x%d) := by
  induction w generalizing x with
  | zero =>
    have hz : x = 0 := by simpa only [pow_zero, Nat.lt_one_iff] using hx
    simp [restoreWidth, hz]
  | succ w ih =>
    have hsmall : x / 2 < 2^w := (Nat.div_lt_iff_lt_mul (by decide)).mpr
      (by simpa only [pow_succ] using hx)
    rw [restoreWidth, ih _ hsmall, restoreStep_eq m d _ _ hd guard (Nat.mod_lt _ (by decide)),
      Nat.div_add_mod]

/-- After processing the high bits down through i+1, the literal quotient
word has zeros at all as-yet-unwritten positions. Setting bit i therefore adds
either zero or 2^i, as expressed by this identity. -/
theorem quotient_bit_step (m d x i : Nat) (hd : 0 < d) (guard : 2*d ≤ m) :
    let pref := x/2^(i+1)
    let bit := x/2^i % 2
    let old := (pref/d)*2^(i+1)
    let shifted := 2*(pref%d)+bit
    old + (if d ≤ shifted then 2^i else 0) = ((x/2^i)/d)*2^i := by
  let pref := x/2^(i+1)
  let b := x/2^i % 2
  let z := 2*(pref%d)+b
  have hb : b < 2 := Nat.mod_lt _ (by decide)
  have fit : z < m := shifted_fits guard (Nat.mod_lt _ hd) hb
  have join : 2*pref+b = x/2^i := by
    unfold pref b
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_add_mod]
  have eq := congrArg Prod.fst (restoreStep_eq m d pref b hd guard hb)
  change (pref/d)*2^(i+1)+(if d ≤ z then 2^i else 0) = _
  change (if d ≤ z%m then (2*(pref/d)+1, (z%m+m-d)%m) else
    (2*(pref/d),z%m)).1 = (2*pref+b)/d at eq
  rw [Nat.mod_eq_of_lt fit, join] at eq
  by_cases h : d ≤ z <;> simp only [h, if_true, if_false, Prod.fst] at eq ⊢ <;>
    rw [← eq, Nat.pow_succ] <;> ring

/-- Integer interpretation of the product in binomWord. The subtracting
operand wraps for h > v, when the preceding zero factor has already set the
whole product to zero. -/
def fallingWord (m v : Nat) : Nat → Nat
  | 0 => 1
  | j+1 => (fallingWord m v j * ((v+m-j)%m))%m

theorem fallingWord_eq (m v j : Nat) (hv : v < m)
    (fits : ∀ i ≤ j, v.descFactorial i < m) : fallingWord m v j = v.descFactorial j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [fallingWord, ih (fun i h => fits i (Nat.le_step h))]
    by_cases hj : j ≤ v
    · rw [show v+m-j = (v-j)+m by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show v-j < m by omega), Nat.mul_comm, ← Nat.descFactorial_succ]
      exact Nat.mod_eq_of_lt (fits _ le_rfl)
    · have hzero : v.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [Nat.descFactorial_succ, hzero]

open SingleRefined

/-- Includes candidates at or above t, which the unranker tests before its
range gate rejects them. They still have at most 19 bits. -/
theorem single_width : RankGates.width p = 202 ∧ p.t = 491520 ∧
    Nat.log2 (p.t-1)+1 = 19 := by decide +kernel

theorem single_falling_fits {v j : Nat} (hv : v < 2^19) (hj : j ≤ 9) :
    v.descFactorial j < 2^(RankGates.width p) := by
  calc
    _ ≤ v^j := Nat.descFactorial_le_pow _ _
    _ ≤ (2^19)^j := Nat.pow_le_pow_left hv.le _
    _ ≤ (2^19)^9 := Nat.pow_le_pow_right (by decide) hj
    _ < _ := by rw [single_width.1]; decide +kernel

theorem single_factorial_guard {j : Nat} (hj : j ≤ 9) :
    2 * j.factorial ≤ 2^(RankGates.width p) :=
  (Nat.mul_le_mul_left 2 (Nat.factorial_le hj)).trans (by rw [single_width.1]; decide +kernel)

theorem single_rank_divisor_guard : 0 < p.supports ∧ 2*p.supports ≤ 2^(RankGates.width p) := by
  decide +kernel

/-- For a single-row lifting candidate, the width-limited falling product
and restoring division return exactly the mathematical binomial coefficient. -/
theorem single_binomial_value (v j : Nat) (hv : v < 2^19) (hj : j ≤ 9) :
    let w := RankGates.width p
    restoreWidth (2^w) j.factorial w (fallingWord (2^w) v j) = (v.choose j, 0) := by
  dsimp only
  have hvw : v < 2^(RankGates.width p) := hv.trans_le (by rw [single_width.1]; decide +kernel)
  rw [fallingWord_eq _ _ _ hvw (fun i hi => single_falling_fits hv (hi.trans hj)),
    restoreWidth_eq _ _ (Nat.factorial_pos _) (single_factorial_guard hj) _ _
      (single_falling_fits hv hj), ← Nat.choose_eq_descFactorial_div_factorial]
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_mod_right]

end PoissonDAG.PORS.RankBounds
