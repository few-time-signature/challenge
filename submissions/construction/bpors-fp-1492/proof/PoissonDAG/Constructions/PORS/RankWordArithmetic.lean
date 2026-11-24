import PoissonDAG.Constructions.PORS.RankBounds
import PoissonDAG.Constructions.PORS.WordSemantics

namespace PoissonDAG.PORS.RankGates

/-- A word of exactly w valid wires with the indicated unsigned value. -/
structure Holds (raw : Nat) (p : Array Gate) (w : Nat) (a : Word) (value : Nat) : Prop where
  size : a.size = w
  valid : ∀ j ∈ a.toList, j < p.size
  value_eq : wordValue raw p a = value

theorem Holds.fits {raw p w a x} (h : Holds raw p w a x) : x < 2^w := by
  have bound := digitsValue_lt (a.toList.map (wireValue raw p))
  simpa only [← h.value_eq, wordValue, List.length_map, Array.length_toList, h.size] using bound

theorem Holds.mono {raw p q w a x} (h : Holds raw p w a x) (e : Extends raw p q) :
    Holds raw q w a x := by
  have fixed : a.toList.map (wireValue raw q) = a.toList.map (wireValue raw p) :=
    List.map_congr_left fun i hi => e.stable i (h.valid i hi)
  refine ⟨h.size, fun i hi => (h.valid i hi).trans_le e.size_le, ?_⟩
  simpa only [wordValue, fixed] using h.value_eq

theorem holds_literal {raw p} (s : Seeded raw p) (w n : Nat) :
    Holds raw p w (lit w n) (n % 2^w) :=
  ⟨by simp [lit], (lit_word s w n).1, wordValue_lit s w n⟩

theorem Holds.shift {raw p w a x} (s : Seeded raw p) (h : Holds raw p w a x) (i : Nat) :
    Holds raw p w (shl a i) ((x*2^i)%2^w) :=
  ⟨by simp [shl, h.size], (shl_word s a i h.valid).1,
    by rw [wordValue_shl s a i h.valid, h.value_eq, h.size]⟩

theorem holds_mux {raw p w sel b a c x y} (s : Seeded raw p) (hs : HasBit raw p sel b)
    (ha : Holds raw p w a x) (hc : Holds raw p w c y) :
    Builds raw p (muxw sel a c) (fun q out => Holds raw q w out (if b then x else y)) := by
  obtain ⟨e, sz, wires, hv⟩ := muxw_nat s hs a c ha.valid hc.valid
  refine ⟨e, sz.trans ha.size, wires, ?_⟩
  rw [hv, ha.value_eq, ha.size, ← hc.size, wordValueAt_size, hc.value_eq]

theorem holds_add {raw p w a b x y} (s : Seeded raw p)
    (ha : Holds raw p w a x) (hb : Holds raw p w b y) :
    Builds raw p (do let z ← addSub a b false; return z.1)
      (fun q out => Holds raw q w out ((x+y)%2^w)) := by
  refine (addSub_nat raw p a b false s ha.valid hb.valid).bind ?_
  intro q z _ facts
  obtain ⟨sz, wires, _, hv⟩ := facts
  have hy : wordValueAt raw p b a.size = y := by
    rw [ha.size, ← hb.size, wordValueAt_size, hb.value_eq]
  change wordValue raw q z.1 + 2^a.size * (wireValue raw q z.2).toNat =
    wordValueAt raw p a a.size + wordValueAt raw p b a.size at hv
  rw [wordValueAt_size, ha.value_eq, hy, ha.size] at hv
  have fit : wordValue raw q z.1 < 2^w :=
    (show Holds raw q w z.1 (wordValue raw q z.1) from ⟨sz.trans ha.size, wires, rfl⟩).fits
  apply builds_pure
  refine ⟨sz.trans ha.size, wires, ?_⟩
  calc
    _ = wordValue raw q z.1 % 2^w := (Nat.mod_eq_of_lt fit).symm
    _ = (wordValue raw q z.1 + 2^w * (wireValue raw q z.2).toNat) % 2^w :=
      (Nat.add_mul_mod_self_left _ _ _).symm
    _ = _ := congrArg (· % 2^w) hv

theorem holds_sub {raw p w a b x y} (s : Seeded raw p)
    (ha : Holds raw p w a x) (hb : Holds raw p w b y) :
    Builds raw p (addSub a b true) (fun q z =>
      Holds raw q w z.1 ((x+2^w-y)%2^w) ∧ HasBit raw q z.2 (decide (y ≤ x))) := by
  obtain ⟨e, sz, wires, carry, hv⟩ := addSub_nat raw p a b true s ha.valid hb.valid
  have hy : wordValueAt raw p b a.size = y := by
    rw [ha.size, ← hb.size, wordValueAt_size, hb.value_eq]
  change wordValue raw _ _ = (wordValueAt raw p a a.size + 2^a.size -
    wordValueAt raw p b a.size)%2^a.size ∧ wireValue raw _ _ =
    decide (wordValueAt raw p b a.size ≤ wordValueAt raw p a a.size) at hv
  rw [wordValueAt_size, ha.value_eq, hy, ha.size] at hv
  exact ⟨e, ⟨sz.trans ha.size, wires, hv.1⟩, ⟨carry, hv.2⟩⟩

private def multiplyLoop (a b : Word) (indices : List Nat) (initial : Word) : Build Word := do
  let mut out := initial
  for i in indices do
    let flag := bit b i
    if flag != 0 then
      let part ← muxw flag (shl a i) (lit a.size 0)
      out := (← addSub out part false).1
  return out

private def multiplyStep (m x y : Nat) (out i : Nat) :=
  (out + if y.testBit i then (x*2^i)%m else 0)%m

private theorem multiplyLoop_spec {raw w a b x y} (indices : List Nat) (p : Array Gate)
    (out : Word) (z : Nat) (s : Seeded raw p) (ha : Holds raw p w a x)
    (hb : Holds raw p w b y) (ho : Holds raw p w out z) :
    Builds raw p (multiplyLoop a b indices out) (fun q result =>
      Holds raw q w result (indices.foldl (multiplyStep (2^w) x y) z)) := by
  induction indices generalizing p out z with
  | nil =>
    simpa [multiplyLoop] using
      (builds_pure (raw := raw) (x := out) (post := fun q r => Holds raw q w r z) ho)
  | cons i is ih =>
    have bitSpec : HasBit raw p (bit b i) (y.testBit i) := by
      rw [← hb.value_eq, testBit_wordValue s]
      exact bit_valid s b hb.valid i
    by_cases hf : bit b i = 0
    · have zero : y.testBit i = false := bitSpec.2.symm.trans (by simpa only [hf] using s.1.2)
      simpa [multiplyLoop, List.forIn_cons, hf, multiplyStep, zero, Nat.mod_eq_of_lt ho.fits]
        using ih p out z s ha hb ho
    · have he : multiplyLoop a b (i::is) out =
          (muxw (bit b i) (shl a i) (lit a.size 0) >>= fun part =>
            (do let z' ← addSub out part false; return z'.1) >>= fun next =>
              multiplyLoop a b is next) := by
        simp [multiplyLoop, List.forIn_cons, hf, bind_assoc]
      rw [he]
      have zero : Holds raw p w (lit a.size 0) 0 := by
        simpa only [ha.size, Nat.zero_mod] using holds_literal s a.size 0
      refine (holds_mux s bitSpec (Holds.shift s ha i) zero).bind fun q part eq hp => ?_
      refine (holds_add (s.mono eq) (ho.mono eq) hp).bind fun r next er hn => ?_
      exact ih r next _ (s.mono (eq.trans er)) (ha.mono (eq.trans er)) (hb.mono (eq.trans er)) hn

private theorem fold_multiplyStep (m x y n : Nat) :
    (List.range n).foldl (multiplyStep m x y) 0 = RankBounds.shiftSum m x y n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.foldl_append, ih, RankBounds.shiftSum, multiplyStep]

/-- Unsigned multiplication, modulo 2^w, for the actual literal gate builder. -/
theorem times_nat {raw p w a b x y} (s : Seeded raw p)
    (ha : Holds raw p w a x) (hb : Holds raw p w b y) :
    Builds raw p (times a b) (fun q out => Holds raw q w out ((x*y)%2^w)) := by
  have he : times a b = multiplyLoop a b (List.range b.size) (lit a.size 0) := by
    simp [times, multiplyLoop, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.range_eq_range']
  have zeros : Holds raw p w (lit a.size 0) 0 := by
    simpa only [ha.size, Nat.zero_mod] using holds_literal s a.size 0
  rw [he]
  simpa only [fold_multiplyStep, hb.size, RankBounds.shiftSum_full _ _ _ _ hb.fits] using
    multiplyLoop_spec (List.range b.size) p _ 0 s ha hb zeros

theorem Holds.set_clear_bit {raw p w a x i wire b} (s : Seeded raw p)
    (ha : Holds raw p w a x) (hi : i < w) (old : x.testBit i = false)
    (hv : HasBit raw p wire b) :
    Holds raw p w (a.set! i wire) (x+2^i*b.toNat) := by
  refine ⟨by simpa using ha.size, set_valid a i hv ha.valid, ?_⟩
  have he := wordValue_set a (by simpa only [ha.size] using hi) hv
  rw [← testBit_wordValue s, ha.value_eq, old, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at he
  exact he

private theorem read_digit (x i : Nat) : (x.testBit i).toNat = x / 2^i % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : x / 2^i % 2 = 1
  · simp [h]
  · simp [show x / 2^i % 2 = 0 by omega]

private def divisionCell (a : Word) (d i : Nat) (quot rem : Word)
    (next : Word → Word → Build α) : Build α := do
  let shifted := (shl rem 1).set! 0 (bit a i)
  let (diff,ge) ← addSub shifted (lit a.size d) true
  let rem ← muxw ge diff shifted
  next (quot.set! i ge) rem

private theorem divisionCell_spec {raw p w a x d i quot rem} (s : Seeded raw p)
    (ha : Holds raw p w a x) (hi : i < w) (hd : 0 < d) (guard : 2*d ≤ 2^w)
    (hq : Holds raw p w quot ((x/2^(i+1)/d)*2^(i+1)))
    (hr : Holds raw p w rem (x/2^(i+1)%d))
    (next : Word → Word → Build α) (post : Array Gate → α → Prop)
    (k : ∀ q qword rword, Extends raw p q →
      Holds raw q w qword ((x/2^i/d)*2^i) → Holds raw q w rword (x/2^i%d) →
      Builds raw q (next qword rword) post) :
    Builds raw p (divisionCell a d i quot rem next) post := by
  let pref := x/2^(i+1)
  let b := x/2^i%2
  let z := 2*(pref%d)+b
  have hb : b < 2 := Nat.mod_lt _ (by decide)
  have hrem := Nat.mod_lt pref hd
  have fit : z < 2^w := RankBounds.shifted_fits guard hrem hb
  have prodFits : (pref%d)*2 < 2^w := by dsimp [z] at fit; omega
  have high : 0 < w := by omega
  have shiftSpec : Holds raw p w (shl rem 1) ((pref%d)*2) := by
    have hs := Holds.shift s hr 1
    change Holds raw p w (shl rem 1) (((pref%d)*2)%2^w) at hs
    rwa [Nat.mod_eq_of_lt prodFits] at hs
  have clear : ((pref%d)*2).testBit 0 = false := by
    change ((pref%d)*2^1).testBit 0 = false
    simp [Nat.testBit_mul_two_pow]
  have src : HasBit raw p (bit a i) (x.testBit i) := by
    rw [← ha.value_eq, testBit_wordValue s]
    exact bit_valid s a ha.valid i
  have hw : Holds raw p w ((shl rem 1).set! 0 (bit a i)) z := by
    simpa only [pow_zero, Nat.one_mul, read_digit, Nat.mul_comm (pref%d) 2, z, b] using
      Holds.set_clear_bit s shiftSpec high clear src
  have dword : Holds raw p w (lit a.size d) d := by
    simpa only [ha.size, Nat.mod_eq_of_lt (show d < 2^w by omega)] using holds_literal s a.size d
  have join : 2*pref+b = x/2^i := by
    unfold pref b
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.div_add_mod]
  have goodRem : (if decide (d ≤ z) then (z+2^w-d)%2^w else z) = x/2^i%d := by
    have he := congrArg Prod.snd (RankBounds.restoreStep_eq (2^w) d pref b hd guard hb)
    change (if d ≤ z%(2^w) then (2*(pref/d)+1,(z%(2^w)+2^w-d)%2^w)
      else (2*(pref/d),z%(2^w))).2 = (2*pref+b)%d at he
    rw [Nat.mod_eq_of_lt fit, join] at he
    by_cases h : d ≤ z <;> simpa [h] using he
  have goodQuot : (pref/d)*2^(i+1)+2^i*(decide (d ≤ z)).toNat = (x/2^i/d)*2^i := by
    have he := RankBounds.quotient_bit_step (2^w) d x i hd guard
    change (pref/d)*2^(i+1)+(if d ≤ z then 2^i else 0) = _ at he
    by_cases h : d ≤ z <;> simpa [h] using he
  have oldClear : ((pref/d)*2^(i+1)).testBit i = false := by simp [Nat.testBit_mul_two_pow]
  unfold divisionCell
  refine (holds_sub s hw dword).bind fun q pair eq hpair => ?_
  refine (holds_mux (s.mono eq) hpair.2 hpair.1 (hw.mono eq)).bind fun r rem' er hresult => ?_
  have hquot := Holds.set_clear_bit (s.mono (eq.trans er)) (hq.mono (eq.trans er)) hi
    oldClear (hpair.2.mono er)
  apply k r _ _ (eq.trans er)
  · rw [← goodQuot]
    exact hquot
  · simpa only [goodRem] using hresult

private def divisionLoop (a : Word) (d : Nat) (indices : List Nat) (q0 r0 : Word) :
    Build (Word × Word) := do
  let mut rem := r0
  let mut quot := q0
  for i in indices do
    let shifted := (shl rem 1).set! 0 (bit a i)
    let (diff,ge) ← addSub shifted (lit a.size d) true
    rem ← muxw ge diff shifted
    quot := quot.set! i ge
  return (quot,rem)

private theorem divisionLoop_spec {raw w a x d} (n : Nat) (hn : n ≤ w)
    (hd : 0 < d) (guard : 2*d ≤ 2^w) (p : Array Gate) (quot rem : Word)
    (s : Seeded raw p) (ha : Holds raw p w a x)
    (hq : Holds raw p w quot ((x/2^n/d)*2^n)) (hr : Holds raw p w rem (x/2^n%d)) :
    Builds raw p (divisionLoop a d (List.range n).reverse quot rem)
      (fun q out => Holds raw q w out.1 (x/d) ∧ Holds raw q w out.2 (x%d)) := by
  induction n generalizing p quot rem with
  | zero =>
    have hz : Holds raw p w quot (x/d) ∧ Holds raw p w rem (x%d) := by simpa using And.intro hq hr
    simpa [divisionLoop] using (builds_pure (x := (quot,rem))
      (post := fun r out => Holds raw r w out.1 (x/d) ∧ Holds raw r w out.2 (x%d)) hz)
  | succ i ih =>
    have cell : divisionLoop a d (List.range (i+1)).reverse quot rem =
        divisionCell a d i quot rem (divisionLoop a d (List.range i).reverse) := by
      simp [List.range_succ, divisionLoop, divisionCell, List.forIn_cons, bind_assoc]
    rw [cell]
    apply divisionCell_spec s ha (by omega) hd guard hq hr
    intro q qo re eq hqo hre
    exact ih (by omega) q qo re (s.mono eq) (ha.mono eq) hqo hre

/-- The literal fixed-divisor gate loop computes unsigned quotient and
remainder. The guard allows one bit for doubling the previous remainder. -/
theorem divmod_nat {raw p w a x} (s : Seeded raw p) (ha : Holds raw p w a x)
    (d : Nat) (hd : 0 < d) (guard : 2*d ≤ 2^w) :
    Builds raw p (divmod a d) (fun q out =>
      Holds raw q w out.1 (x/d) ∧ Holds raw q w out.2 (x%d)) := by
  have zero : Holds raw p w (lit a.size 0) 0 := by
    simpa only [ha.size, Nat.zero_mod] using holds_literal s a.size 0
  by_cases hd1 : d = 1
  · subst d
    simpa [divmod, Nat.mod_one] using (builds_pure (raw := raw) (x := (a,lit a.size 0))
      (post := fun q out => Holds raw q w out.1 x ∧ Holds raw q w out.2 0) (And.intro ha zero))
  have order : (List.range a.size).reverse = (List.range a.size).map (fun j => a.size-1-j) := by
    simpa only [Nat.zero_add, ← List.range_eq_range'] using
      (List.reverse_range' (s := 0) (n := a.size))
  have he : divmod a d = divisionLoop a d (List.range a.size).reverse (lit a.size 0) (lit a.size 0) := by
    rw [order]
    simp [divmod, hd1, divisionLoop, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, List.range_eq_range', List.forIn_map]
  rw [he, ha.size]
  have h0 : Holds raw p w (lit w 0) 0 := by simpa [ha.size] using zero
  apply divisionLoop_spec w le_rfl hd guard p _ _ s ha <;>
    simpa only [Nat.div_eq_of_lt ha.fits, Nat.zero_div, Nat.zero_mul, Nat.zero_mod] using h0

private def fallingLoop (a : Word) (indices : List Nat) (initial : Word) : Build Word := do
  let mut prod := initial
  for h in indices do
    prod ← times prod (← addSub a (lit a.size h) true).1
  return prod

private def factorStep (m v : Nat) (prod h : Nat) :=
  (prod*((v+m-h)%m))%m

private theorem fallingLoop_spec {raw w a v} (indices : List Nat)
    (small : ∀ h ∈ indices, h < 2^w) (p : Array Gate) (initial : Word) (initialValue : Nat)
    (s : Seeded raw p) (ha : Holds raw p w a v) (hp : Holds raw p w initial initialValue) :
    Builds raw p (fallingLoop a indices initial) (fun q out =>
      Holds raw q w out (indices.foldl (factorStep (2^w) v) initialValue)) := by
  induction indices generalizing p initial initialValue with
  | nil =>
    simpa [fallingLoop] using (builds_pure (x := initial)
      (post := fun q out => Holds raw q w out initialValue) hp)
  | cons i is ih =>
    have he : fallingLoop a (i::is) initial =
        (addSub a (lit a.size i) true >>= fun pair =>
          times initial pair.1 >>= fun prod => fallingLoop a is prod) := by
      simp [fallingLoop, List.forIn_cons, bind_assoc]
    have literal : Holds raw p w (lit a.size i) i := by
      simpa only [ha.size, Nat.mod_eq_of_lt (small i (by simp))] using holds_literal s a.size i
    rw [he]
    refine (holds_sub s ha literal).bind fun q pair eq hpair => ?_
    refine (times_nat (s.mono eq) (hp.mono eq) hpair.1).bind fun r out er hprod => ?_
    exact ih (fun h hh => small h (List.mem_cons_of_mem _ hh)) r out _
      (s.mono (eq.trans er)) (ha.mono (eq.trans er)) hprod

private theorem fold_factorStep (m v j : Nat) :
    (List.range j).foldl (factorStep m v) 1 = RankBounds.fallingWord m v j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [List.range_succ, List.foldl_append, ih, factorStep, RankBounds.fallingWord]

/-- The literal falling product is exact when its factors and partial products
fit the word and restoring division has its guard bit for the factorial. -/
theorem binomWord_nat {raw p w a v} (s : Seeded raw p) (ha : Holds raw p w a v) (j : Nat)
    (oneFit : 1 < 2^w) (degreeFit : j ≤ 2^w)
    (products : ∀ i ≤ j, v.descFactorial i < 2^w) (guard : 2*j.factorial ≤ 2^w) :
    Builds raw p (binomWord a j) (fun q out => Holds raw q w out (v.choose j)) := by
  have small : ∀ i ∈ List.range j, i < 2^w :=
    fun _ hi => (List.mem_range.mp hi).trans_le degreeFit
  have one : Holds raw p w (lit a.size 1) 1 := by
    have ht := holds_literal s a.size 1
    rw [ha.size, Nat.mod_eq_of_lt oneFit] at ht
    rwa [ha.size]
  have he : binomWord a j = (fallingLoop a (List.range j) (lit a.size 1) >>= fun prod =>
      do let pair ← divmod prod j.factorial; return pair.1) := by
    simp [binomWord, fallingLoop, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.range_eq_range']
  rw [he]
  refine (fallingLoop_spec (List.range j) small p _ 1 s ha one).bind fun q prod eq hprod => ?_
  have hfall : RankBounds.fallingWord (2^w) v j = v.descFactorial j :=
    RankBounds.fallingWord_eq _ _ _ ha.fits products
  rw [fold_factorStep, hfall] at hprod
  refine (divmod_nat (s.mono eq) hprod j.factorial (Nat.factorial_pos j) guard).bind
    fun r pair _ hpair => ?_
  apply builds_pure
  simpa only [← Nat.choose_eq_descFactorial_div_factorial] using hpair.1

/-- Every candidate in the production 19-bit search, including candidates
subsequently rejected by the range gate, meets the arithmetic hypotheses. -/
theorem single_binomWord_nat {raw p a v} (s : Seeded raw p)
    (ha : Holds raw p (width SingleRefined.p) a v) (j : Nat) (hj : j ≤ 9) (hv : v < 2^19) :
    Builds raw p (binomWord a j) (fun q out =>
      Holds raw q (width SingleRefined.p) out (v.choose j)) := by
  apply binomWord_nat s ha j
  · rw [RankBounds.single_width.1]; decide
  · exact hj.trans (by rw [RankBounds.single_width.1]; decide)
  · exact fun i hi => RankBounds.single_falling_fits hv (hi.trans hj)
  · exact RankBounds.single_factorial_guard hj

end PoissonDAG.PORS.RankGates
