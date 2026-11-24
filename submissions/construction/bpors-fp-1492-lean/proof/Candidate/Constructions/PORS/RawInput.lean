import Candidate.Constructions.PORS.RankWordArithmetic

namespace PoissonDAG.PORS.RankGates

/-- The input-gate loop at the start of the literal decoder. -/
private def loadList (indices : List Nat) (initial : Word) : Build Word := do
  let mut out := initial
  for i in indices do out := out.set! i (← emit (.input i))
  return out

def loadRaw (r w : Nat) : Build Word := loadList (List.range r) (lit w 0)

theorem loadRaw_loop (r w : Nat) : loadRaw r w = (do
    let mut out := lit w 0
    for i in [:r] do out := out.set! i (← emit (.input i))
    return out) := by
  simp [loadRaw, loadList, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range_eq_range']

private theorem mod_next_bit (x i : Nat) :
    x % 2^(i+1) = x % 2^i + 2^i*(x.testBit i).toNat := by
  rw [Nat.pow_succ, Nat.mod_mul (x := x) (a := 2^i) (b := 2)]
  rcases Nat.mod_two_eq_zero_or_one (x/2^i) with h | h <;>
    simp [Nat.testBit_eq_decide_div_mod_eq, h]

private theorem loadList_range {raw width} (count : Nat) (start : Nat) (p : Array Gate)
    (out : Word) (s : Seeded raw p) (hw : Holds raw p width out (raw % 2^start))
    (bound : start+count ≤ width) :
    Builds raw p (loadList (List.range' start count) out)
      (fun q result => Holds raw q width result (raw % 2^(start+count))) := by
  induction count generalizing p out start with
  | zero =>
    simpa [loadList] using
      (builds_pure (raw := raw) (x := out) (post := fun q a => Holds raw q width a
        (raw % 2^start)) hw)
  | succ n ih =>
    have step : loadList (List.range' start (n+1)) out =
        (emit (.input start) >>= fun wire =>
          loadList (List.range' (start+1) n) (out.set! start wire)) := by
      simp [loadList, List.range'_succ, List.forIn_cons, bind_assoc]
    rw [step]
    refine (emit_bit raw p (.input start)).bind fun q wire e hwire => ?_
    have hw' := hw.mono e
    have hs : start < out.size := by rw [hw.size]; omega
    have he : wireValue raw q (bit out start) = false := by
      rw [← testBit_wordValue (s.mono e), hw'.value_eq]
      exact Nat.testBit_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
    have hbit : HasBit raw q wire (raw.testBit start) := hwire
    have newval := wordValue_set out hs hbit
    rw [he, Bool.toNat_false, Nat.mul_zero, Nat.add_zero, hw'.value_eq,
      ← mod_next_bit] at newval
    have newWord : Holds raw q width (out.set! start wire) (raw % 2^(start+1)) :=
      ⟨by simpa using hw.size, set_valid out start hbit hw'.valid, newval⟩
    simpa only [Nat.succ_add, Nat.add_succ] using
      ih (start+1) q _ (s.mono e) newWord (by omega)

theorem loadRaw_nat {raw p} (s : Seeded raw p) (r w : Nat) (h : r ≤ w) :
    Builds raw p (loadRaw r w) (fun q a => Holds raw q w a (raw % 2^r)) := by
  have zero : Holds raw p w (lit w 0) (raw % 2^0) := by
    simpa [Nat.mod_one] using holds_literal s w 0
  simpa [loadRaw, List.range_eq_range'] using
    loadList_range r 0 p (lit w 0) s zero (by simpa using h)

private theorem divmod_one (a : Word) : divmod a 1 = pure (a, lit a.size 0) := by
  simp [divmod]

/-- Single-row parameters remove both unit-radix divisions and the depth
unranking branch. The remaining quotient decides rank validity. -/
theorem decode_single_program :
    decode SingleRefined.p = (do
      let raw ← loadRaw SingleRefined.p.r (width SingleRefined.p)
      let (quot,rank) ← divmod raw SingleRefined.p.supports
      let leaves ← unrank SingleRefined.p.t SingleRefined.p.k rank
      let valid ← eqw quot (lit (width SingleRefined.p) 0)
      return (valid, [⟨lit quot.size 0, leaves,
        List.replicate SingleRefined.p.k (lit (width SingleRefined.p) 0)⟩])) := by
  have hK : SingleRefined.p.K = 1 := rfl
  have hd : SingleRefined.p.depthCount = 1 := rfl
  have hb : SingleRefined.p.buckets = 1 := rfl
  have hc : SingleRefined.p.cap = 0 := rfl
  simp [decode, loadRaw, loadList, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.range_eq_range', hK, hd, hb, hc, divmod_one, bind_assoc]

end PoissonDAG.PORS.RankGates
