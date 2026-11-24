import Candidate.Constructions.PORS.ColexDigits
import Candidate.Constructions.PORS.RankWordArithmetic

namespace PoissonDAG.PORS.RankGates
namespace SingleUnrank

abbrev w := width SingleRefined.p
abbrev t := SingleRefined.p.t

/-- Exact interface of a binomial probe in the nine-digit production decoder.
The lifting search may probe beyond the last leaf, up to a 19-bit index. -/
def BinomCorrect : Prop :=
  ∀ {raw p a v j}, Seeded raw p → Holds raw p w a v → v < 2^19 → j ≤ 9 →
    Builds raw p (binomWord a j) (fun q out => Holds raw q w out (v.choose j))

private def test (j r v : Nat) := decide (v.choose j ≤ r ∧ v<t)

private def probe (wordWidth j i : Nat) (rem v : Word) : Build Word := do
  let candidate := v.set! i 1
  let coeff ← binomWord candidate j
  let (_,ge) ← addSub rem coeff true
  let (_,past) ← addSub candidate (lit wordWidth t) true
  muxw (← both ge (← neg past)) candidate v

private theorem probe_spec (coeffOK : BinomCorrect) {raw p j i rem r a v}
    (seed : Seeded raw p) (remOK : Holds raw p w rem r) (word : Holds raw p w a v)
    (hj : j ≤ 9) (hi : i < 19) (clear : v.testBit i = false)
    (fits : v+2^i < 2^19) :
    Builds raw p (probe w j i rem a) (fun q out =>
      Holds raw q w out (if test j r (v+2^i) then v+2^i else v)) := by
  have hw : i < w := by
    change i < width SingleRefined.p
    rw [RankBounds.single_width.1]
    omega
  have cand : Holds raw p w (a.set! i 1) (v+2^i) := by
    simpa only [Bool.toNat_true, Nat.mul_one] using Holds.set_clear_bit seed word hw clear seed.2
  unfold probe
  refine (coeffOK seed cand fits hj).bind fun q c e hc => ?_
  refine (holds_sub (seed.mono e) (remOK.mono e) hc).bind fun q' g e' hg => ?_
  have ef := e.trans e'
  have bound : Holds raw q' w (lit w t) t := by
    simpa only [Nat.mod_eq_of_lt (by decide +kernel : t < 2^w)] using holds_literal (seed.mono ef) w t
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
  for h in indices do v ← probe wordWidth j (levels-1-h) rem v
  return v

/-- An interval of bit positions refines the pure greedy search in ColexDigits. -/
private theorem scan_spec (coeffOK : BinomCorrect) {j raw r} (rem : Word) (hj : j ≤ 9)
    (n beginAt : Nat) (total : beginAt+n=19) (p : Array Gate) (a : Word) (v : Nat)
    (seed : Seeded raw p) (remOK : Holds raw p w rem r) (word : Holds raw p w a v)
    (clear : ∀ i<n, v.testBit i=false) (cap : v+2^n ≤ 2^19) :
    Builds raw p (scan w j 19 rem (List.range' beginAt n) a)
      (fun q out => Holds raw q w out (Colex.liftBits (test j r) n v)) := by
  induction n generalizing beginAt p a v with
  | zero => simpa [scan,Colex.liftBits] using
      (builds_pure (raw := raw) (x := a) (post := fun q z => Holds raw q w z v) word)
  | succ n ih =>
    have hcap := cap
    rw [Nat.pow_succ] at hcap
    have hp : 0 < 2^n := Nat.two_pow_pos _
    have hi : 19-1-beginAt=n := by omega
    have he : scan w j 19 rem (List.range' beginAt (n+1)) a =
        (probe w j n rem a >>= fun z => scan w j 19 rem (List.range' (beginAt+1) n) z) := by
      simp [scan, List.range'_succ, hi]
    rw [he]
    refine (probe_spec coeffOK seed remOK word hj (by omega) (clear _ (by omega)) (by omega)).bind ?_
    intro q z e hz
    apply ih (beginAt+1) (by omega) q z _ (seed.mono e) (remOK.mono e) hz
    · intro i h
      split
      · simpa [Nat.add_comm v, Nat.testBit_two_pow_add_gt h] using clear i (by omega)
      · exact clear i (by omega)
    · split <;> omega

private def search (j : Nat) (rem : Word) : Build Word :=
  scan w j 19 rem (List.range 19) (lit rem.size 0)

theorem search_spec (coeffOK : BinomCorrect) {j raw p rem r}
    (hj : j+1 ≤ 9) (seed : Seeded raw p) (remOK : Holds raw p w rem r) :
    Builds raw p (search (j+1) rem)
      (fun q out => Holds raw q w out (Colex.largest t (j+1) r)) := by
  have h0 : Holds raw p w (lit rem.size 0) 0 := by
    rw [remOK.size]; simpa using holds_literal seed w 0
  have hx := scan_spec coeffOK rem hj 19 0 (by decide) p _ 0 seed remOK h0
    (by simp) (by simp)
  have he := Colex.search_eq (k := j) (r := r) (by decide : 0<t)
  change Colex.liftBits (test (j+1) r) (Nat.log2 (t-1)+1) 0 = Colex.largest t (j+1) r at he
  rw [RankBounds.single_width.2.2] at he
  unfold search
  rw [List.range_eq_range', ← he]
  exact hx

private def rounds (rank : Word) (indices : List Nat) (rem0 : Word)
    (already : List Word) : Build (List Word) := do
  let mut rem := rem0
  let mut selected := already
  for idx in indices do
    let j := 9-idx
    let v ← scan rank.size j 19 rem (List.range 19) (lit rank.size 0)
    rem := (← addSub rem (← binomWord v j) true).1
    selected := v :: selected
  return selected

private theorem unrank_rounds (rank : Word) :
    unrank t 9 rank = rounds rank (List.range 9) rank [] := by
  have h : Nat.log2 (t-1)+1 = 19 := RankBounds.single_width.2.2
  simp [unrank,rounds,scan,probe,h,Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size,List.range_eq_range']

private theorem list_mono {raw p q words values} (e : Extends raw p q)
    (h : List.Forall₂ (Holds raw p w) words values) :
    List.Forall₂ (Holds raw q w) words values :=
  List.Forall₂.imp (fun _ _ hw => hw.mono e) h

private theorem rounds_spec (coeffOK : BinomCorrect) {raw} (rank : Word) (hrank : rank.size=w)
    (left start : Nat) (hsum : left+start=9) (n : Nat) (hn : n≤t)
    (p : Array Gate) (rem : Word) (r : Nat) (hr : r < n.choose left)
    (ws : List Word) (vs : List Nat) (seed : Seeded raw p) (remOK : Holds raw p w rem r)
    (saved : List.Forall₂ (Holds raw p w) ws vs) :
    Builds raw p (rounds rank (List.range' start left) rem ws) (fun q out =>
      List.Forall₂ (Holds raw q w) out ((Colex.digits t left r).reverse ++ vs)) := by
  induction left generalizing start n p rem r ws vs with
  | zero =>
    simpa [rounds,Colex.digits] using
      (builds_pure (raw := raw) (x := ws)
        (post := fun q out => List.Forall₂ (Holds raw q w) out vs) saved)
  | succ k ih =>
    let v := Colex.largest t (k+1) r
    have hstep := Colex.remainder_bound hn hr
    have low : v<n := hstep.1
    have bound : v<2^19 := low.trans_le (hn.trans (by decide))
    have fit : v.choose (k+1) ≤ r := ((Colex.search_spec (k := k) (r := r)
      (by decide : 0<t) v).mpr le_rfl).1
    have hj : 9-start=k+1 := by omega
    have he : rounds rank (List.range' start (k+1)) rem ws =
        (search (k+1) rem >>= fun d => binomWord d (k+1) >>= fun coeff =>
          addSub rem coeff true >>= fun next =>
            rounds rank (List.range' (start+1) k) next.1 (d :: ws)) := by
      simp [rounds,search,List.range'_succ,List.forIn_cons,hj,hrank,remOK.size,bind_assoc]
    rw [he]
    refine (search_spec coeffOK (by omega) seed remOK).bind fun q d e hd => ?_
    refine (coeffOK (seed.mono e) hd bound (by omega)).bind fun q' c e' hc => ?_
    have ef := e.trans e'
    refine (holds_sub (seed.mono ef) (remOK.mono ef) hc).bind fun q'' next e'' hnext => ?_
    have full := ef.trans e''
    have rfits := remOK.fits
    have remE : (r+2^w-v.choose (k+1)) % 2^w = r-v.choose (k+1) := by
      rw [show r+2^w-v.choose (k+1)=r-v.choose (k+1)+2^w by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    have remN : Holds raw q'' w next.1 (r-v.choose (k+1)) := remE ▸ hnext.1
    have all : List.Forall₂ (Holds raw q'' w) (d::ws) (v::vs) :=
      .cons (hd.mono (e'.trans e'')) (list_mono full saved)
    simpa only [Colex.digits, List.reverse_cons, List.append_assoc, List.singleton_append] using
      ih (start+1) (by omega) v (low.le.trans hn) q'' next.1 _ hstep.2 _ _
        (seed.mono full) remN all

/-- The literal combinadic unranker returns exactly the sorted nine leaf IDs. -/
theorem unrank_spec {raw p rank r} (seed : Seeded raw p) (word : Holds raw p w rank r)
    (hr : r<t.choose 9) :
    Builds raw p (unrank t 9 rank) (fun q out =>
      List.Forall₂ (Holds raw q w) out (Colex.digits t 9 r).reverse) := by
  have coeffOK : BinomCorrect := fun seed h hv hj => single_binomWord_nat seed h _ hj hv
  rw [unrank_rounds,List.range_eq_range']
  simpa using rounds_spec coeffOK rank word.size 9 0 rfl t le_rfl p rank r hr [] [] seed word .nil

end SingleUnrank
end PoissonDAG.PORS.RankGates
