import Candidate.Constructions.PORS.LiteralMaskGates

namespace PoissonDAG.PORS.LiteralMaskSemantics

open RankGates Literal

private def eqLoop (a b : Word) (is : List Nat) (initial : Nat) : Build Nat := do
  let mut mismatch := initial
  for i in is do
    mismatch ← either mismatch (← parity (bit a i) (bit b i))
  neg mismatch

private theorem eqw_loop (a b : Word) :
    eqw a b = eqLoop a b (List.range a.size) 0 := by
  simp [eqw, eqLoop, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range_eq_range']

private theorem eqLoop_cons (a b : Word) (i : Nat) (is : List Nat) (m : Nat) :
    eqLoop a b (i::is) m = (do
      let x ← parity (bit a i) (bit b i)
      let m' ← either m x
      eqLoop a b is m') := by
  simp [eqLoop, List.forIn_cons, bind_assoc] <;> rfl

private theorem eqLoop_spec (a b : Word) (av bv : Nat → Bool) (is : List Nat)
    (raw : Nat) (p : Array Gate) (m : Nat) (v : Bool) (seed : Seeded raw p)
    (ha : ∀ i, HasBit raw p (bit a i) (av i)) (hb : ∀ i, HasBit raw p (bit b i) (bv i))
    (hm : HasBit raw p m v) : BuildsBit raw p (eqLoop a b is m)
      ((!v) && is.all (fun i => av i == bv i)) := by
  induction is generalizing p m v with
  | nil => simpa [eqLoop] using neg_bit seed hm
  | cons i is ih =>
    rw [eqLoop_cons]
    refine (parity_bit seed (ha i) (hb i)).bind fun q x e hx => ?_
    refine (either_bit (seed.mono e) (hm.mono e) hx).bind fun q' m' e' hm' => ?_
    have E := e.trans e'
    have h := ih q' m' _ (seed.mono E) (fun j => (ha j).mono E) (fun j => (hb j).mono E) hm'
    have he : (!(v || xor (av i) (bv i)) && is.all (fun j => av j == bv j)) =
        ((!v) && (i::is).all (fun j => av j == bv j)) := by
      cases v <;> cases h1 : av i <;> cases h2 : bv i <;> simp [h1,h2]
    rwa [he] at h

private theorem all_bits_eq (is : List Nat) (av bv : Nat → Bool) :
    is.all (fun i => av i == bv i) =
      decide (digitsValue (is.map av) = digitsValue (is.map bv)) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    apply Bool.eq_iff_iff.mpr
    cases h1 : av i <;> cases h2 : bv i <;>
      simp [ih, h1, h2, digitsValue] <;> omega

/-- The literal equality circuit compares all bits of equal-width operands. -/
theorem eqw_number {raw p w a b x y} (seed : Seeded raw p)
    (ha : Number raw p w a x) (hb : Number raw p w b y) :
    BuildsBit raw p (eqw a b) (decide (x=y)) := by
  rw [eqw_loop]
  have h := eqLoop_spec a b _ _ (List.range a.size) raw p 0 false seed
    (bit_valid seed a ha.valid) (bit_valid seed b hb.valid) seed.1
  simp only [Bool.not_false, Bool.true_and, all_bits_eq] at h
  change BuildsBit raw p _ (decide (wordValueAt raw p a a.size = wordValueAt raw p b a.size)) at h
  have hy : wordValueAt raw p b a.size = y := by
    rw [show a.size=b.size from ha.size.trans hb.size.symm, wordValueAt_size, hb.value]
  rwa [wordValueAt_size, ha.value, hy] at h

theorem literal_number {raw p} (seed : Seeded raw p) (w n : Nat) (bound : n<2^w) :
    Number raw p w (lit w n) n :=
  ⟨by simp [lit], (lit_word seed w n).1, (wordValue_lit seed w n).trans (Nat.mod_eq_of_lt bound)⟩

def leafView (selected : Bool) : View :=
  ⟨selected, [(selected,false)], (false,selected), 0⟩

private def leafLoop (w i : Nat) (pairs : List (Word×Word)) (sel : Nat)
    (opens : Array Nat) : Build Part := do
  let mut selected := sel
  let mut openings := opens
  for (s,e) in pairs do
    let here ← eqw s (lit w i)
    selected ← either selected here
    for v in [:1] do
      let hit ← both here (← eqw e (lit w 0))
      openings := openings.set! v (← either (bit openings v) hit)
  let mut known := 0
  let mut marks := #[]
  for v in [:2] do
    let offer := bit openings v
    marks := marks.push (offer,known)
    known ← either known offer
  return ⟨selected,marks,lit w 0⟩

private theorem leaf_as_loop (row : Row) (hc : row.cap=0) (d : Digits) (i : Nat) :
    atLeaf row d i = leafLoop (width row) i (d.leaves.zip d.depths) 0 #[0,0] := by
  have rep : Array.replicate 2 (0 : Nat) = #[0,0] := by decide +kernel
  simp [atLeaf, leafLoop, hc, rep]

private theorem leafLoop_nil (w i sel arm : Nat) :
    leafLoop w i [] sel #[arm,0] = (do
      let known ← either 0 arm
      let _ ← either known 0
      return ⟨sel,#[(arm,0),(0,known)],lit w 0⟩) := by
  simp [leafLoop, List.forIn_cons, List.range'_succ, bind_assoc, bit] <;> rfl

private theorem leafLoop_cons (w i : Nat) (s e : Word) (xs : List (Word×Word)) (sel arm : Nat) :
    leafLoop w i ((s,e)::xs) sel #[arm,0] = (do
      let here ← eqw s (lit w i)
      let selected ← either sel here
      let zero ← eqw e (lit w 0)
      let hit ← both here zero
      let armed ← either arm hit
      leafLoop w i xs selected #[armed,0]) := by
  have reset (x y : Nat) : (#[x,0] : Array Nat).setIfInBounds 0 y = #[y,0] := by
    apply Array.toList_inj.mp
    simp
  simp [leafLoop, List.forIn_cons, List.range'_succ, bind_assoc, bit, reset] <;> rfl

/-- The paired decoder words contain support indices and zero chain depths. -/
def LeafDigits (raw : Nat) (p : Array Gate) (w : Nat) (pairs : List (Word×Word))
    (xs : List Nat) := List.Forall₂ (fun se x => Number raw p w se.1 x ∧ Number raw p w se.2 0) pairs xs

theorem LeafDigits.mono {raw p q w pairs xs} (h : LeafDigits raw p w pairs xs)
    (e : Extends raw p q) : LeafDigits raw q w pairs xs :=
  List.Forall₂.imp (fun _ _ hh => ⟨hh.1.mono e, hh.2.mono e⟩) h

private theorem leafLoop_spec (w i raw : Nat) (pairs : List (Word×Word)) (xs : List Nat)
    (p : Array Gate) (seed : Seeded raw p) (sel arm : Nat) (A : Bool)
    (hs : HasBit raw p sel A) (ho : HasBit raw p arm A)
    (digits : LeafDigits raw p w pairs xs) (ib : i<2^w) :
    Builds raw p (leafLoop w i pairs sel #[arm,0])
      (fun q v => Represents raw q w v (leafView (A || decide (i ∈ xs)))) := by
  induction pairs generalizing p xs sel arm A with
  | nil =>
    cases digits
    rw [leafLoop_nil]
    refine (either_bit seed seed.1 ho).bind fun q known e hknown => ?_
    have hk : HasBit raw q known A := by simpa using hknown
    refine (either_bit (seed.mono e) hk (seed.mono e).1).bind fun q' _ e' _ => ?_
    apply builds_pure
    have E := e.trans e'
    simp only [List.not_mem_nil, decide_false, Bool.or_false]
    refine Represents.mk (hs.mono E) ?_ (literal_number (seed.mono E) w 0 (by positivity))
    refine Exists.intro (#[(arm,0)] : Array (Nat×Nat)) (Exists.intro (0,known) ?_)
    refine ⟨rfl, ?_, (seed.mono E).1, hk.mono e'⟩
    exact .cons ⟨ho.mono E,(seed.mono E).1⟩ .nil
  | cons pair pairs ih =>
    rcases pair with ⟨s,depth⟩
    cases xs with
    | nil => cases digits
    | cons x xs =>
      have hcons := List.forall₂_cons.mp digits
      rw [leafLoop_cons]
      refine (eqw_number seed hcons.1.1 (literal_number seed w i ib)).bind fun q1 here e1 hh => ?_
      refine (either_bit (seed.mono e1) (hs.mono e1) hh).bind fun q2 sel' e2 hsel => ?_
      have e02 := e1.trans e2
      refine (eqw_number (seed.mono e02) (hcons.1.2.mono e02)
        (literal_number (seed.mono e02) w 0 (by positivity))).bind fun q3 zero e3 hz => ?_
      have e03 := e02.trans e3
      have htrue : HasBit raw q3 zero true := by simpa using hz
      refine (both_bit (seed.mono e03) (hh.mono (e2.trans e3)) htrue).bind fun q4 hit e4 hm => ?_
      have e04 := e03.trans e4
      have hhit : HasBit raw q4 hit (decide (x=i)) := by simpa using hm
      refine (either_bit (seed.mono e04) (ho.mono e04) hhit).bind fun q5 arm' e5 harm => ?_
      have E := e04.trans e5
      have rest : LeafDigits raw p w pairs xs := hcons.2
      have h := ih xs q5 (seed.mono E) sel' arm' _
        (hsel.mono ((e3.trans e4).trans e5)) harm (rest.mono E)
      simpa [List.mem_cons, eq_comm, Bool.or_assoc] using h

/-- With zero chain capacity the actual leaf builder supplies a secret and
plans its unary hash exactly when the decoded support contains this index. -/
theorem atLeaf_single {raw p} (seed : Seeded raw p) (d : Digits) (xs : List Nat)
    (digits : LeafDigits raw p (width SingleRefined.p) (d.leaves.zip d.depths) xs)
    (i : Nat) (ib : i<2^(width SingleRefined.p)) :
    Builds raw p (atLeaf SingleRefined.p d i) (fun q v =>
      Represents raw q (width SingleRefined.p) v (leafView (decide (i ∈ xs)))) := by
  rw [leaf_as_loop _ (by rfl)]
  simpa using leafLoop_spec (width SingleRefined.p) i raw _ xs p seed 0 0 false
    seed.1 seed.1 digits ib

/-- Any zero-capacity row runs the same unary-leaf builder at its prescribed
word width. The selected index and its absolute comparison must fit that width. -/
theorem atLeaf_chainless (row : Row) (capacity : row.cap=0) {raw p} (seed : Seeded raw p)
    (d : Digits) (xs : List Nat)
    (digits : LeafDigits raw p (width row) (d.leaves.zip d.depths) xs)
    (i : Nat) (ib : i<2^(width row)) :
    Builds raw p (atLeaf row d i) (fun q v =>
      Represents raw q (width row) v (leafView (decide (i ∈ xs)))) := by
  rw [leaf_as_loop row capacity]
  simpa using leafLoop_spec (width row) i raw _ xs p seed 0 0 false
    seed.1 seed.1 digits ib

end PoissonDAG.PORS.LiteralMaskSemantics
