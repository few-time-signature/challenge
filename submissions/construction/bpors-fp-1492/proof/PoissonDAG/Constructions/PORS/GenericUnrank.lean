import PoissonDAG.Constructions.PORS.ColexDigits
import PoissonDAG.Constructions.PORS.RankWordArithmetic

namespace PoissonDAG.PORS.RankGates
namespace GenericUnrank

/-- The number of bits tested by the production lifting loop, and the bounds
needed to store the tested index and the leaf count in the allocated word. -/
structure Config where
  leafCount : Nat
  digits : Nat
  wordWidth : Nat
  levels : Nat
  leaf_pos : 0 < leafCount
  levels_eq : Nat.log2 (leafCount-1)+1 = levels
  levels_fit : levels ≤ wordWidth
  leaf_word : leafCount < 2^wordWidth
  leaf_bound : leafCount ≤ 2^levels

variable (cfg : Config)

/-- The coefficient arithmetic must cover every tested bit prefix. -/
def BinomCorrect : Prop :=
  ∀ {raw p a v j}, Seeded raw p → Holds raw p cfg.wordWidth a v → v < 2^cfg.levels → j ≤ cfg.digits →
    Builds raw p (binomWord a j) (fun q out => Holds raw q cfg.wordWidth out (v.choose j))

/-- It suffices to check the largest possible falling product and the
largest factorial divisor across all calls of the unranker. -/
structure ArithmeticBounds : Prop where
  one_fit : 1 < 2^cfg.wordWidth
  degree_fit : cfg.digits ≤ 2^cfg.wordWidth
  product_fit : (2^cfg.levels)^cfg.digits < 2^cfg.wordWidth
  divisor_guard : 2*cfg.digits.factorial ≤ 2^cfg.wordWidth

theorem binom_correct (bounds : ArithmeticBounds cfg) : BinomCorrect cfg := by
  intro raw p a v j seed word hv hj
  apply binomWord_nat seed word j bounds.one_fit (hj.trans bounds.degree_fit)
  · intro i hi
    calc
      v.descFactorial i ≤ v^i := Nat.descFactorial_le_pow _ _
      _ ≤ (2^cfg.levels)^i := Nat.pow_le_pow_left hv.le _
      _ ≤ (2^cfg.levels)^cfg.digits := Nat.pow_le_pow_right (Nat.two_pow_pos _) (hi.trans hj)
      _ < 2^cfg.wordWidth := bounds.product_fit
  · exact (Nat.mul_le_mul_left 2 (Nat.factorial_le hj)).trans bounds.divisor_guard

private def test (j r v : Nat) := decide (v.choose j ≤ r ∧ v<cfg.leafCount)

private def probe (wordWidth j i : Nat) (rem v : Word) : Build Word := do
  let candidate := v.set! i 1
  let coeff ← binomWord candidate j
  let (_,ge) ← addSub rem coeff true
  let (_,past) ← addSub candidate (lit wordWidth cfg.leafCount) true
  muxw (← both ge (← neg past)) candidate v

private theorem probe_spec (coeffOK : BinomCorrect cfg) {raw p j i rem r a v}
    (seed : Seeded raw p) (remOK : Holds raw p cfg.wordWidth rem r) (word : Holds raw p cfg.wordWidth a v)
    (hj : j ≤ cfg.digits) (hi : i < cfg.levels) (clear : v.testBit i = false)
    (fits : v+2^i < 2^cfg.levels) :
    Builds raw p (probe cfg cfg.wordWidth j i rem a) (fun q out =>
      Holds raw q cfg.wordWidth out (if test cfg j r (v+2^i) then v+2^i else v)) := by
  have hw : i < cfg.wordWidth := hi.trans_le cfg.levels_fit
  have cand : Holds raw p cfg.wordWidth (a.set! i 1) (v+2^i) := by
    simpa only [Bool.toNat_true, Nat.mul_one] using Holds.set_clear_bit seed word hw clear seed.2
  unfold probe
  refine (coeffOK seed cand fits hj).bind fun q c e hc => ?_
  refine (holds_sub (seed.mono e) (remOK.mono e) hc).bind fun q' g e' hg => ?_
  have ef := e.trans e'
  have bound : Holds raw q' cfg.wordWidth (lit cfg.wordWidth cfg.leafCount) cfg.leafCount := by
    simpa only [Nat.mod_eq_of_lt cfg.leaf_word] using holds_literal (seed.mono ef) cfg.wordWidth cfg.leafCount
  refine (holds_sub (seed.mono ef) (cand.mono ef) bound).bind fun q'' b e'' hb => ?_
  have ef' := ef.trans e''
  refine (neg_bit (seed.mono ef') hb.2).bind fun q3 allow e3 hallow => ?_
  have e3' := ef'.trans e3
  refine (both_bit (seed.mono e3') (hg.2.mono (e''.trans e3)) hallow).bind fun q4 ok e4 hok => ?_
  have e4' := e3'.trans e4
  simpa [test, Bool.and_eq_true, Nat.not_le] using
    holds_mux (seed.mono e4') hok (cand.mono e4') (word.mono e4')

private def scan (wordWidth j levels : Nat) (rem : Word) (indices : List Nat) (start : Word) : Build Word := do
  let mut v := start
  for h in indices do v ← probe cfg wordWidth j (levels-1-h) rem v
  return v

/-- An interval of bit positions refines the pure greedy search in ColexDigits. -/
private theorem scan_spec (coeffOK : BinomCorrect cfg) {j raw r} (rem : Word) (hj : j ≤ cfg.digits)
    (n beginAt : Nat) (total : beginAt+n=cfg.levels) (p : Array Gate) (a : Word) (v : Nat)
    (seed : Seeded raw p) (remOK : Holds raw p cfg.wordWidth rem r) (word : Holds raw p cfg.wordWidth a v)
    (clear : ∀ i<n, v.testBit i=false) (cap : v+2^n ≤ 2^cfg.levels) :
    Builds raw p (scan cfg cfg.wordWidth j cfg.levels rem (List.range' beginAt n) a)
      (fun q out => Holds raw q cfg.wordWidth out (Colex.liftBits (test cfg j r) n v)) := by
  induction n generalizing beginAt p a v with
  | zero => simpa [scan,Colex.liftBits] using
      (builds_pure (raw := raw) (x := a) (post := fun q z => Holds raw q cfg.wordWidth z v) word)
  | succ n ih =>
    have hcap := cap
    rw [Nat.pow_succ] at hcap
    have hp : 0 < 2^n := Nat.two_pow_pos _
    have hi : cfg.levels-1-beginAt=n := by omega
    have he : scan cfg cfg.wordWidth j cfg.levels rem (List.range' beginAt (n+1)) a =
        (probe cfg cfg.wordWidth j n rem a >>= fun z => scan cfg cfg.wordWidth j cfg.levels rem (List.range' (beginAt+1) n) z) := by
      simp [scan, List.range'_succ, hi]
    rw [he]
    refine (probe_spec cfg coeffOK seed remOK word hj (by omega) (clear _ (by omega)) (by omega)).bind ?_
    intro q z e hz
    apply ih (beginAt+1) (by omega) q z _ (seed.mono e) (remOK.mono e) hz
    · intro i h
      split
      · simpa [Nat.add_comm v, Nat.testBit_two_pow_add_gt h] using clear i (by omega)
      · exact clear i (by omega)
    · split <;> omega

private def search (j : Nat) (rem : Word) : Build Word :=
  scan cfg cfg.wordWidth j cfg.levels rem (List.range cfg.levels) (lit rem.size 0)

theorem search_spec (coeffOK : BinomCorrect cfg) {j raw p rem r}
    (hj : j+1 ≤ cfg.digits) (seed : Seeded raw p) (remOK : Holds raw p cfg.wordWidth rem r) :
    Builds raw p (search cfg (j+1) rem)
      (fun q out => Holds raw q cfg.wordWidth out (Colex.largest cfg.leafCount (j+1) r)) := by
  have h0 : Holds raw p cfg.wordWidth (lit rem.size 0) 0 := by
    rw [remOK.size]; simpa using holds_literal seed cfg.wordWidth 0
  have hx := scan_spec cfg coeffOK rem hj cfg.levels 0 (by simp) p _ 0 seed remOK h0
    (by simp) (by simp)
  have he := Colex.search_eq (k := j) (r := r) cfg.leaf_pos
  change Colex.liftBits (test cfg (j+1) r) (Nat.log2 (cfg.leafCount-1)+1) 0 = Colex.largest cfg.leafCount (j+1) r at he
  rw [cfg.levels_eq] at he
  unfold search
  rw [List.range_eq_range', ← he]
  exact hx

private def rounds (rank : Word) (indices : List Nat) (rem0 : Word)
    (already : List Word) : Build (List Word) := do
  let mut rem := rem0
  let mut selected := already
  for idx in indices do
    let j := cfg.digits-idx
    let v ← scan cfg rank.size j cfg.levels rem (List.range cfg.levels) (lit rank.size 0)
    rem := (← addSub rem (← binomWord v j) true).1
    selected := v :: selected
  return selected

private theorem unrank_rounds (rank : Word) :
    unrank cfg.leafCount cfg.digits rank = rounds cfg rank (List.range cfg.digits) rank [] := by
  have h : Nat.log2 (cfg.leafCount-1)+1 = cfg.levels := cfg.levels_eq
  simp [unrank,rounds,scan,probe,h,Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size,List.range_eq_range']

private theorem list_mono {raw p q words values} (e : Extends raw p q)
    (h : List.Forall₂ (Holds raw p cfg.wordWidth) words values) :
    List.Forall₂ (Holds raw q cfg.wordWidth) words values :=
  List.Forall₂.imp (fun _ _ hw => hw.mono e) h

private theorem rounds_spec (coeffOK : BinomCorrect cfg) {raw} (rank : Word) (hrank : rank.size=cfg.wordWidth)
    (left start : Nat) (hsum : left+start=cfg.digits) (n : Nat) (hn : n≤cfg.leafCount)
    (p : Array Gate) (rem : Word) (r : Nat) (hr : r < n.choose left)
    (ws : List Word) (vs : List Nat) (seed : Seeded raw p) (remOK : Holds raw p cfg.wordWidth rem r)
    (saved : List.Forall₂ (Holds raw p cfg.wordWidth) ws vs) :
    Builds raw p (rounds cfg rank (List.range' start left) rem ws) (fun q out =>
      List.Forall₂ (Holds raw q cfg.wordWidth) out ((Colex.digits cfg.leafCount left r).reverse ++ vs)) := by
  induction left generalizing start n p rem r ws vs with
  | zero =>
    simpa [rounds,Colex.digits] using
      (builds_pure (raw := raw) (x := ws)
        (post := fun q out => List.Forall₂ (Holds raw q cfg.wordWidth) out vs) saved)
  | succ k ih =>
    let v := Colex.largest cfg.leafCount (k+1) r
    have hstep := Colex.remainder_bound hn hr
    have low : v<n := hstep.1
    have bound : v<2^cfg.levels := low.trans_le (hn.trans cfg.leaf_bound)
    have fit : v.choose (k+1) ≤ r := ((Colex.search_spec (k := k) (r := r)
      cfg.leaf_pos v).mpr le_rfl).1
    have hj : cfg.digits-start=k+1 := by omega
    have he : rounds cfg rank (List.range' start (k+1)) rem ws =
        (search cfg (k+1) rem >>= fun d => binomWord d (k+1) >>= fun coeff =>
          addSub rem coeff true >>= fun next =>
            rounds cfg rank (List.range' (start+1) k) next.1 (d :: ws)) := by
      simp [rounds,search,List.range'_succ,List.forIn_cons,hj,hrank,remOK.size,bind_assoc]
    rw [he]
    refine (search_spec cfg coeffOK (by omega) seed remOK).bind fun q d e hd => ?_
    refine (coeffOK (seed.mono e) hd bound (by omega)).bind fun q' c e' hc => ?_
    have ef := e.trans e'
    refine (holds_sub (seed.mono ef) (remOK.mono ef) hc).bind fun q'' next e'' hnext => ?_
    have full := ef.trans e''
    have rfits := remOK.fits
    have remE : (r+2^cfg.wordWidth-v.choose (k+1)) % 2^cfg.wordWidth = r-v.choose (k+1) := by
      rw [show r+2^cfg.wordWidth-v.choose (k+1)=r-v.choose (k+1)+2^cfg.wordWidth by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    have remN : Holds raw q'' cfg.wordWidth next.1 (r-v.choose (k+1)) := remE ▸ hnext.1
    have all : List.Forall₂ (Holds raw q'' cfg.wordWidth) (d::ws) (v::vs) :=
      .cons (hd.mono (e'.trans e'')) (list_mono cfg full saved)
    simpa only [Colex.digits, List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih (start+1) (by omega) v (low.le.trans hn) q'' next.1 _ hstep.2 _ _
        (seed.mono full) remN all

/-- At every accepted rank the source builder returns the sorted colex digits. -/
theorem unrank_spec (coeffOK : BinomCorrect cfg) {raw p rank r} (seed : Seeded raw p) (word : Holds raw p cfg.wordWidth rank r)
    (hr : r<cfg.leafCount.choose cfg.digits) :
    Builds raw p (unrank cfg.leafCount cfg.digits rank) (fun q out =>
      List.Forall₂ (Holds raw q cfg.wordWidth) out (Colex.digits cfg.leafCount cfg.digits r).reverse) := by
  rw [unrank_rounds cfg,List.range_eq_range']
  simpa using rounds_spec cfg coeffOK rank word.size cfg.digits 0 rfl cfg.leafCount le_rfl p rank r hr [] [] seed word .nil

end GenericUnrank
end PoissonDAG.PORS.RankGates
