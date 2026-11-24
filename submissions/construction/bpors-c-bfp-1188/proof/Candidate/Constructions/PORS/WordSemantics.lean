import Candidate.Constructions.PORS.WireSemantics
import PoissonDAG.Constructions.PORS.RankGates

namespace PoissonDAG.PORS.RankGates

/-- Interpretation of a source-program address on a fixed raw input. -/
def wireValue (raw : Nat) (p : Array Gate) (i : Nat) : Bool :=
  get (executeGates raw p.toList) i

/-- The address exists and its protected evaluation is the indicated bit. -/
def HasBit (raw : Nat) (p : Array Gate) (i : Nat) (v : Bool) : Prop :=
  i < p.size ∧ wireValue raw p i = v

/-- All previously allocated wires keep their values as the builder runs. -/
structure Extends (raw : Nat) (p q : Array Gate) : Prop where
  size_le : p.size ≤ q.size
  stable : ∀ i, i < p.size → wireValue raw q i = wireValue raw p i

theorem Extends.refl (raw : Nat) (p : Array Gate) : Extends raw p p :=
  ⟨le_rfl, fun _ _ => rfl⟩

theorem Extends.trans {raw : Nat} {p q r : Array Gate}
    (a : Extends raw p q) (b : Extends raw q r) : Extends raw p r :=
  ⟨a.size_le.trans b.size_le, fun i hi =>
    (b.stable i (Nat.lt_of_lt_of_le hi a.size_le)).trans (a.stable i hi)⟩

theorem HasBit.mono {raw i v} {p q : Array Gate}
    (h : HasBit raw p i v) (e : Extends raw p q) : HasBit raw q i v :=
  ⟨Nat.lt_of_lt_of_le h.1 e.size_le, (e.stable i h.1).trans h.2⟩

def Seeded (raw : Nat) (p : Array Gate) : Prop :=
  HasBit raw p 0 false ∧ HasBit raw p 1 true

theorem Seeded.mono {raw} {p q : Array Gate}
    (h : Seeded raw p) (e : Extends raw p q) : Seeded raw q :=
  ⟨h.1.mono e, h.2.mono e⟩

theorem initial_seeded (raw : Nat) : Seeded raw #[.constant false, .constant true] := by
  exact ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩⟩

/-- Semantic postcondition of the actual state-monad computation. -/
def Builds (raw : Nat) (p : Array Gate) (m : Build α)
    (post : Array Gate → α → Prop) : Prop :=
  Extends raw p (m.run p).2 ∧ post (m.run p).2 (m.run p).1

theorem builds_pure {raw p} {x : α} {post : Array Gate → α → Prop}
    (h : post p x) : Builds raw p (pure x) post := ⟨Extends.refl _ _, h⟩

theorem Builds.bind {raw p} {m : Build α} {f : α → Build β}
    {middle : Array Gate → α → Prop} {post : Array Gate → β → Prop}
    (h : Builds raw p m middle)
    (k : ∀ q x, Extends raw p q → middle q x → Builds raw q (f x) post) :
    Builds raw p (m >>= f) post := by
  have s := k (m.run p).2 (m.run p).1 h.1 h.2
  exact ⟨h.1.trans s.1, s.2⟩

abbrev BuildsBit (raw : Nat) (p : Array Gate) (m : Build Nat) (v : Bool) :=
  Builds raw p m (fun q i => HasBit raw q i v)

private theorem execute_push (raw : Nat) (p : Array Gate) (g : Gate) :
    executeGates raw (p.push g).toList = executeGates raw p.toList ++
      [evalGate raw (executeGates raw p.toList) g] := by
  simp [executeGates, List.foldl_append]

theorem emit_bit (raw : Nat) (p : Array Gate) (g : Gate) :
    BuildsBit raw p (emit g) (evalGate raw (executeGates raw p.toList) g) := by
  change Extends raw p (p.push g) ∧ HasBit raw (p.push g) p.size _
  have hn : (executeGates raw p.toList).length = p.size := by simp [executeGates_length]
  constructor
  · refine ⟨by simp, ?_⟩
    intro i hi
    have h : i < (executeGates raw p.toList).length := hn.symm ▸ hi
    simp only [wireValue, execute_push, get, List.getElem?_append_left h]
  · refine ⟨by simp, ?_⟩
    simp only [wireValue, execute_push, get]
    simp [hn]

theorem neg_bit {raw p x a} (s : Seeded raw p) (hx : HasBit raw p x a) :
    BuildsBit raw p (neg x) (!a) := by
  rcases hx with ⟨hx, rfl⟩
  unfold neg
  split
  · rename_i h
    subst x
    apply builds_pure
    simpa [s.1.2] using s.2
  split
  · rename_i h
    subst x
    apply builds_pure
    simpa [s.2.2] using s.1
  exact emit_bit raw p (.neg x)

theorem both_bit {raw p x y a b} (s : Seeded raw p)
    (hx : HasBit raw p x a) (hy : HasBit raw p y b) :
    BuildsBit raw p (both x y) (a && b) := by
  rcases hx with ⟨hx, rfl⟩
  rcases hy with ⟨hy, rfl⟩
  unfold both
  split
  · rename_i h
    rcases h with h | h
    · subst x; apply builds_pure; simpa [s.1.2] using s.1
    · subst y; apply builds_pure; simpa [s.1.2] using s.1
  split
  · rename_i h
    subst x; apply builds_pure
    simpa [s.2.2] using (show HasBit raw p y (wireValue raw p y) from ⟨hy, rfl⟩)
  split
  · rename_i h
    rcases h with h | h
    · subst y; apply builds_pure
      simpa [s.2.2] using (show HasBit raw p x (wireValue raw p x) from ⟨hx, rfl⟩)
    · subst y; apply builds_pure
      simpa using (show HasBit raw p x (wireValue raw p x) from ⟨hx, rfl⟩)
  exact emit_bit raw p (.conj x y)

theorem parity_bit {raw p x y a b} (s : Seeded raw p)
    (hx : HasBit raw p x a) (hy : HasBit raw p y b) :
    BuildsBit raw p (parity x y) (xor a b) := by
  rcases hx with ⟨hx, rfl⟩
  rcases hy with ⟨hy, rfl⟩
  unfold parity
  split
  · rename_i h
    subst x; apply builds_pure
    simpa [s.1.2] using (show HasBit raw p y (wireValue raw p y) from ⟨hy, rfl⟩)
  split
  · rename_i h
    subst y; apply builds_pure
    simpa [s.1.2] using (show HasBit raw p x (wireValue raw p x) from ⟨hx, rfl⟩)
  split
  · rename_i h
    subst y; apply builds_pure; simpa [Bool.xor_self] using s.1
  exact emit_bit raw p (.xor x y)

theorem mux_bit {raw p sel x y choose a b} (s : Seeded raw p)
    (hs : HasBit raw p sel choose) (hx : HasBit raw p x a) (hy : HasBit raw p y b) :
    BuildsBit raw p (mux sel x y) (if choose then a else b) := by
  by_cases h1 : sel = 1
  · subst sel
    have hv : choose = true := hs.2.symm.trans s.2.2
    simpa [mux, hv] using (builds_pure (raw := raw) (x := x)
      (post := fun q j => HasBit raw q j a) hx)
  by_cases h0 : sel = 0
  · subst sel
    have hv : choose = false := hs.2.symm.trans s.1.2
    simpa [mux, hv] using (builds_pure (raw := raw) (x := y)
      (post := fun q j => HasBit raw q j b) hy)
  by_cases he : x = y
  · subst y
    have hv : a = b := hx.2.symm.trans hy.2
    simpa [mux, h1, hv] using (builds_pure (raw := raw) (x := x)
      (post := fun q j => HasBit raw q j b) hy)
  simp only [mux, if_neg h1, if_neg (not_or_intro h0 he)]
  refine (parity_bit s hx hy).bind fun q diff e hd => ?_
  refine (both_bit (s.mono e) (hs.mono e) hd).bind fun r gate f hg => ?_
  have hb : xor b (choose && xor a b) = (if choose then a else b) := by
    cases choose <;> cases a <;> cases b <;> rfl
  simpa only [hb] using parity_bit (s.mono (e.trans f)) (hy.mono (e.trans f)) hg

/-- The continuation receives the sum and carry wire produced by one
iteration of the literal add/subtract loop. -/
def adderCell (x y c : Nat) (subtract : Bool) (next : Nat → Nat → Build α) : Build α :=
  (if subtract then neg y else pure y) >>= fun y => do
    let xy ← parity x y
    let digit ← parity xy c
    let carry ← parity (← both x y) (← both xy c)
    next digit carry

def sumBit (a b c : Bool) := xor (xor a b) c
def carryBit (a b c : Bool) := xor (a && b) (xor a b && c)

theorem adderCell_spec {raw p x y c a b v} (s : Seeded raw p)
    (hx : HasBit raw p x a) (hy : HasBit raw p y b) (hc : HasBit raw p c v)
    (sub : Bool) (next : Nat → Nat → Build α) (post : Array Gate → α → Prop)
    (k : ∀ q digit carry, Extends raw p q →
      HasBit raw q digit (sumBit a (if sub then !b else b) v) →
      HasBit raw q carry (carryBit a (if sub then !b else b) v) →
      Builds raw q (next digit carry) post) :
    Builds raw p (adderCell x y c sub next) post := by
  let b' := if sub then !b else b
  have selectY : BuildsBit raw p (if sub then neg y else pure y) b' := by
    cases sub
    · exact builds_pure hy
    · exact neg_bit s hy
  unfold adderCell
  refine selectY.bind fun q1 y' e1 hy' => ?_
  refine (parity_bit (s.mono e1) (hx.mono e1) hy').bind fun q2 xy e2 hxy => ?_
  have e02 := e1.trans e2
  refine (parity_bit (s.mono e02) hxy (hc.mono e02)).bind fun q3 digit e3 hd => ?_
  have e03 := e02.trans e3
  refine (both_bit (s.mono e03) (hx.mono e03) (hy'.mono (e2.trans e3))).bind
    fun q4 base e4 hb => ?_
  have e04 := e03.trans e4
  refine (both_bit (s.mono e04) (hxy.mono (e3.trans e4)) (hc.mono e04)).bind
    fun q5 prop e5 hp => ?_
  have e05 := e04.trans e5
  refine (parity_bit (s.mono e05) (hb.mono e5) hp).bind fun q6 carry e6 hcarry => ?_
  exact k q6 digit carry (e05.trans e6) (hd.mono ((e4.trans e5).trans e6)) hcarry

/-- Arithmetic content of the two gates that produce the sum and carry. -/
theorem sumBit_carryBit (a b c : Bool) :
    (sumBit a b c).toNat + 2 * (carryBit a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

/-- Boolean digits are stored least significant first. -/
def HasWord (raw : Nat) (p : Array Gate) (w : Word) (bs : List Bool) : Prop :=
  (∀ j ∈ w.toList, j < p.size) ∧ w.toList.map (wireValue raw p) = bs

theorem HasWord.mono {raw p q w bs} (h : HasWord raw p w bs) (e : Extends raw p q) :
    HasWord raw q w bs := by
  refine ⟨fun j hj => Nat.lt_of_lt_of_le (h.1 j hj) e.size_le, ?_⟩
  exact (List.map_congr_left fun j hj => e.stable j (h.1 j hj)).trans h.2

theorem HasWord.push {raw p w bs i v} (h : HasWord raw p w bs) (hv : HasBit raw p i v) :
    HasWord raw p (w.push i) (bs ++ [v]) := by
  constructor
  · intro j hj
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hj
    rcases hj with hj | rfl
    · exact h.1 j hj
    · exact hv.1
  · simp [h.2, hv.2]

/-- Boolean recurrence for the literal ripple-carry loop. -/
def ripple (a b : Nat → Bool) (sub : Bool) : List Nat → Bool → List Bool × Bool
  | [], c => ([], c)
  | i :: is, c =>
    let y := if sub then !(b i) else b i
    let tail := ripple a b sub is (carryBit (a i) y c)
    (sumBit (a i) y c :: tail.1, tail.2)

/-- The same builder loop with an arbitrary remaining list of bit indices.
`addSub_loop` identifies it with the protected call site. -/
private def addLoop (a b : Word) (sub : Bool) (indices : List Nat)
    (cin : Nat) (output : Word) : Build (Word × Nat) := do
  let mut carry := cin
  let mut out := output
  for i in indices do
    let x := bit a i
    let y ← if sub then neg (bit b i) else pure (bit b i)
    let xy ← parity x y
    out := out.push (← parity xy carry)
    carry ← parity (← both x y) (← both xy carry)
  return (out,carry)

private theorem addSub_loop (a b : Word) (sub : Bool) :
    addSub a b sub = addLoop a b sub (List.range a.size) (if sub then 1 else 0) #[] := by
  simp [addSub, addLoop, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range_eq_range']

private theorem addLoop_cons (a b : Word) (sub : Bool) (i : Nat) (is : List Nat)
    (cin : Nat) (out : Word) :
    addLoop a b sub (i::is) cin out =
      adderCell (bit a i) (bit b i) cin sub
        (fun d c => addLoop a b sub is c (out.push d)) := by
  cases sub <;> simp [addLoop, adderCell, List.forIn_cons, bind_assoc]

private theorem addLoop_spec (a b : Word) (av bv : Nat → Bool) (sub : Bool)
    (indices : List Nat) (raw : Nat) (p : Array Gate) (cin : Nat) (cv : Bool)
    (out : Word) (bs : List Bool) (s : Seeded raw p)
    (ha : ∀ i, HasBit raw p (bit a i) (av i))
    (hb : ∀ i, HasBit raw p (bit b i) (bv i))
    (hc : HasBit raw p cin cv) (hw : HasWord raw p out bs) :
    Builds raw p (addLoop a b sub indices cin out) (fun q pair =>
      HasWord raw q pair.1 (bs ++ (ripple av bv sub indices cv).1) ∧
      HasBit raw q pair.2 (ripple av bv sub indices cv).2) := by
  induction indices generalizing p cin cv out bs with
  | nil =>
    simpa [addLoop, ripple] using
      (builds_pure (raw := raw) (x := (out, cin))
        (post := fun q pair => HasWord raw q pair.1 bs ∧ HasBit raw q pair.2 cv) ⟨hw, hc⟩)
  | cons i is ih =>
    rw [addLoop_cons]
    apply adderCell_spec s (ha i) (hb i) hc
    intro q d c eq hd hcarry
    simpa [ripple, List.append_assoc] using
      ih q c _ (out.push d) _ (s.mono eq) (fun j => (ha j).mono eq)
        (fun j => (hb j).mono eq) hcarry ((hw.mono eq).push hd)

/-- Every output wire and the final carry of the actual optimized builder
agree with the Boolean ripple recurrence, at every word width. -/
theorem addSub_bits (a b : Word) (av bv : Nat → Bool) (sub : Bool)
    (raw : Nat) (p : Array Gate) (s : Seeded raw p)
    (ha : ∀ i, HasBit raw p (bit a i) (av i))
    (hb : ∀ i, HasBit raw p (bit b i) (bv i)) :
    Builds raw p (addSub a b sub) (fun q pair =>
      HasWord raw q pair.1 (ripple av bv sub (List.range a.size) sub).1 ∧
      HasBit raw q pair.2 (ripple av bv sub (List.range a.size) sub).2) := by
  rw [addSub_loop]
  have hc : HasBit raw p (if sub then 1 else 0) sub := by
    cases sub
    · exact s.1
    · exact s.2
  have hw : HasWord raw p #[] [] := ⟨by simp, rfl⟩
  simpa using addLoop_spec a b av bv sub (List.range a.size) raw p _ sub #[] [] s ha hb hc hw

def digitsValue : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * digitsValue bs

theorem digitsValue_lt (bs : List Bool) : digitsValue bs < 2^bs.length := by
  induction bs with
  | nil => decide
  | cons b bs ih => cases b <;> simp [digitsValue, Nat.pow_succ] <;> omega

theorem ripple_length (av bv : Nat → Bool) (sub : Bool) (is : List Nat) (c : Bool) :
    (ripple av bv sub is c).1.length = is.length := by
  induction is generalizing c with
  | nil => rfl
  | cons i is ih => simp [ripple, ih]

/-- Exact base-two identity, with the last carry weighted by the word modulus. -/
theorem ripple_total (av bv : Nat → Bool) (sub : Bool) (is : List Nat) (c : Bool) :
    digitsValue (ripple av bv sub is c).1 + 2^is.length * (ripple av bv sub is c).2.toNat =
      digitsValue (is.map av) + digitsValue (is.map (fun i => if sub then !(bv i) else bv i)) +
        c.toNat := by
  induction is generalizing c with
  | nil => simp [ripple, digitsValue]
  | cons i is ih =>
    let y := if sub then !(bv i) else bv i
    let c' := carryBit (av i) y c
    let t := ripple av bv sub is c'
    let xTail := digitsValue (is.map av)
    let yTail := digitsValue (is.map (fun j => if sub then !(bv j) else bv j))
    have ht : digitsValue t.1 + 2^is.length * t.2.toNat = xTail + yTail + c'.toNat := ih c'
    have hbit : (sumBit (av i) y c).toNat + 2 * c'.toNat =
        (av i).toNat + y.toNat + c.toNat := sumBit_carryBit _ _ _
    change (sumBit (av i) y c).toNat + 2 * digitsValue t.1 +
      2^(is.length+1) * t.2.toNat =
      (av i).toNat + 2*xTail + (y.toNat + 2*yTail) + c.toNat
    calc
      _ = (sumBit (av i) y c).toNat + 2*(digitsValue t.1 + 2^is.length*t.2.toNat) := by
        rw [Nat.pow_succ]; ring
      _ = _ := by rw [ht]; omega

theorem digitsValue_complement (bs : List Bool) :
    digitsValue (bs.map (!·)) + digitsValue bs + 1 = 2^bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [digitsValue, Nat.pow_succ] <;> omega

/-- Subtraction realizes a modular difference and sets the carry precisely
when the unsigned first operand is at least the second. -/
theorem ripple_subtract (av bv : Nat → Bool) (is : List Nat) :
    let result := ripple av bv true is true
    let x := digitsValue (is.map av)
    let y := digitsValue (is.map bv)
    let m := 2^is.length
    digitsValue result.1 = (x+m-y) % m ∧ result.2 = decide (y ≤ x) := by
  let result := ripple av bv true is true
  let x := digitsValue (is.map av)
  let y := digitsValue (is.map bv)
  let m := 2^is.length
  let y' := digitsValue (is.map (fun j => !(bv j)))
  change digitsValue result.1 = (x+m-y) % m ∧ result.2 = decide (y ≤ x)
  have ht : digitsValue result.1 + m * result.2.toNat = x + y' + 1 := by
    simpa [result, x, m, y'] using ripple_total av bv true is true
  have hy : y' + y + 1 = m := by
    simpa [y', y, m, List.map_map, Function.comp_def] using digitsValue_complement (is.map bv)
  have hb : digitsValue result.1 < m := by
    simpa [result, m, ripple_length] using digitsValue_lt result.1
  cases hc : result.2 with
  | false =>
    simp only [hc, Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at ht
    have he : x+m-y = digitsValue result.1 := by omega
    have hyx : ¬y ≤ x := by omega
    simp [he, Nat.mod_eq_of_lt hb, hyx]
  | true =>
    simp only [hc, Bool.toNat_true, Nat.mul_one] at ht
    have he : x+m-y = digitsValue result.1 + m := by omega
    have hyx : y ≤ x := by omega
    simp [he, Nat.mod_eq_of_lt hb, hyx]

def wordValue (raw : Nat) (p : Array Gate) (w : Word) : Nat :=
  digitsValue (w.toList.map (wireValue raw p))

theorem wordValue_lt (raw : Nat) (p : Array Gate) (w : Word) :
    wordValue raw p w < 2^w.size := by
  simpa [wordValue] using digitsValue_lt (w.toList.map (wireValue raw p))

/-- Read exactly the requested input width, with the builder's ordinary zero
extension or truncation if the operand widths differ. -/
def wordValueAt (raw : Nat) (p : Array Gate) (w : Word) (width : Nat) : Nat :=
  digitsValue ((List.range width).map (fun i => wireValue raw p (bit w i)))

@[simp] theorem wordValueAt_size (raw : Nat) (p : Array Gate) (w : Word) :
    wordValueAt raw p w w.size = wordValue raw p w := by
  unfold wordValueAt wordValue
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi _
    have h : i < w.size := by simpa using hi
    simp [bit, Array.getElem?_eq_getElem h]

private theorem digitsValue_append_false (bs : List Bool) :
    digitsValue (bs ++ [false]) = digitsValue bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [digitsValue, ih]

theorem wordValueAt_of_le {raw p} (s : Seeded raw p) (w : Word) (width : Nat)
    (h : w.size ≤ width) : wordValueAt raw p w width = wordValue raw p w := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp
  | succ k ih =>
    have hnone : w[w.size+k]? = none := Array.getElem?_eq_none (by omega)
    have hz : wireValue raw p (bit w (w.size+k)) = false := by
      simpa only [bit, hnone, Option.getD_none] using s.1.2
    calc
      _ = wordValueAt raw p w (w.size+k) := by
        unfold wordValueAt
        rw [Nat.add_succ, List.range_succ, List.map_append, List.map_singleton, hz,
          digitsValue_append_false]
      _ = _ := ih (by omega)

theorem digitsValue_testBit (n w : Nat) :
    digitsValue ((List.range w).map n.testBit) = n % 2^w := by
  induction w generalizing n with
  | zero => simp [digitsValue, Nat.mod_one]
  | succ w ih =>
    have hbit : (n.testBit 0).toNat = n % 2 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [Nat.testBit_zero, h]
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Nat.testBit_succ,
      digitsValue, hbit, ih]
    rw [Nat.pow_succ, Nat.mul_comm (2^w) 2, Nat.mod_mul]

theorem lit_word {raw p} (s : Seeded raw p) (w n : Nat) :
    HasWord raw p (lit w n) ((List.range w).map n.testBit) := by
  constructor
  · intro j hj
    change j ∈ (List.range w).map (fun i => if n.testBit i then 1 else 0) at hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    cases n.testBit i
    · exact s.1.1
    · exact s.2.1
  · change ((List.range w).map (fun i => if n.testBit i then 1 else 0)).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    cases h : n.testBit i <;> simp [h, s.1.2, s.2.2]

theorem wordValue_lit {raw p} (s : Seeded raw p) (w n : Nat) :
    wordValue raw p (lit w n) = n % 2^w := by
  unfold wordValue
  rw [(lit_word s w n).2, digitsValue_testBit]

theorem bit_valid {raw p} (s : Seeded raw p) (w : Word)
    (h : ∀ j ∈ w.toList, j < p.size) (i : Nat) :
    HasBit raw p (bit w i) (wireValue raw p (bit w i)) := by
  refine ⟨?_, rfl⟩
  cases hw : w[i]? with
  | none => simpa [bit, hw] using s.1.1
  | some j =>
    have hm : j ∈ w.toList := List.mem_of_getElem? (by simpa using hw : w.toList[i]? = some j)
    simpa [bit, hw] using h j hm

/-- Operational arithmetic specification of `RankGates.addSub`. Both modes
produce the first operand's width and return valid wires in an extending
program. Addition has exact carry accounting; subtraction returns the modular
difference and the unsigned comparison bit. -/
theorem addSub_nat (raw : Nat) (p : Array Gate) (a b : Word) (sub : Bool)
    (s : Seeded raw p) (ha : ∀ j ∈ a.toList, j < p.size)
    (hb : ∀ j ∈ b.toList, j < p.size) :
    Builds raw p (addSub a b sub) (fun q pair =>
      let x := wordValueAt raw p a a.size
      let y := wordValueAt raw p b a.size
      let m := 2^a.size
      pair.1.size = a.size ∧ (∀ j ∈ pair.1.toList, j < q.size) ∧ pair.2 < q.size ∧
        if sub then
          wordValue raw q pair.1 = (x+m-y)%m ∧ wireValue raw q pair.2 = decide (y ≤ x)
        else
          wordValue raw q pair.1 + m*(wireValue raw q pair.2).toNat = x+y) := by
  let av := fun i => wireValue raw p (bit a i)
  let bv := fun i => wireValue raw p (bit b i)
  have h := addSub_bits a b av bv sub raw p s (bit_valid s a ha) (bit_valid s b hb)
  rcases h with ⟨ext, hw, hc⟩
  refine ⟨ext, ?_, hw.1, hc.1, ?_⟩
  · simpa [ripple_length] using congrArg List.length hw.2
  · unfold wordValue wordValueAt
    rw [hw.2, hc.2]
    cases sub
    · simpa [av, bv] using ripple_total av bv false (List.range a.size) false
    · simpa [av, bv] using ripple_subtract av bv (List.range a.size)

theorem testBit_digitsValue (bs : List Bool) (j : Nat) :
    (digitsValue bs).testBit j = bs[j]?.getD false := by
  induction bs generalizing j with
  | nil => simp [digitsValue]
  | cons b bs ih =>
    cases j with
    | zero => cases b <;> simp [digitsValue, Nat.testBit_zero]
    | succ j =>
      rw [Nat.testBit_succ]
      have he : digitsValue (b :: bs) / 2 = digitsValue bs := by
        cases b <;> simp [digitsValue, Nat.add_mul_div_left]
      simp [he, ih]

theorem testBit_wordValue {raw p} (s : Seeded raw p) (w : Word) (j : Nat) :
    (wordValue raw p w).testBit j = wireValue raw p (bit w j) := by
  cases h : w[j]? <;> simp [wordValue, testBit_digitsValue, List.getElem?_map, bit, h, s.1.2]

theorem shl_word {raw p} (s : Seeded raw p) (w : Word) (k : Nat)
    (hw : ∀ j ∈ w.toList, j < p.size) :
    HasWord raw p (shl w k) ((List.range w.size).map ((wordValue raw p w) <<< k).testBit) := by
  constructor
  · intro j hj
    change j ∈ (List.range w.size).map (fun i => if i<k then 0 else bit w (i-k)) at hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    split
    · exact s.1.1
    · exact (bit_valid s w hw _).1
  · change ((List.range w.size).map _).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    by_cases h : i < k
    · simp [h, Nat.not_le_of_lt h, s.1.2]
    · simp [h, Nat.le_of_not_gt h, testBit_wordValue s]

theorem wordValue_shl {raw p} (s : Seeded raw p) (w : Word) (k : Nat)
    (hw : ∀ j ∈ w.toList, j < p.size) :
    wordValue raw p (shl w k) = (wordValue raw p w * 2^k) % 2^w.size := by
  change digitsValue ((shl w k).toList.map (wireValue raw p)) = _
  rw [(shl_word s w k hw).2, digitsValue_testBit, Nat.shiftLeft_eq]

theorem wordValue_stable {raw p q} (e : Extends raw p q) (w : Word)
    (hw : ∀ j ∈ w.toList, j < p.size) : wordValue raw q w = wordValue raw p w := by
  unfold wordValue
  exact congrArg digitsValue (List.map_congr_left fun j hj => e.stable j (hw j hj))

private theorem digitsValue_set (bs : List Bool) (i : Nat) (v : Bool) (hi : i < bs.length) :
    digitsValue (bs.set i v) + 2^i * bs[i].toNat =
      digitsValue bs + 2^i * v.toNat := by
  induction bs generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
    cases i with
    | zero => simp [digitsValue]; omega
    | succ i =>
      have h : i < bs.length := Nat.lt_of_succ_lt_succ hi
      change b.toNat + 2*digitsValue (bs.set i v) + 2^(i+1)*bs[i].toNat =
        b.toNat + 2*digitsValue bs + 2^(i+1)*v.toNat
      calc
        _ = b.toNat + 2*(digitsValue (bs.set i v) + 2^i*bs[i].toNat) := by
          rw [Nat.pow_succ]; ring
        _ = _ := by rw [ih i h, Nat.pow_succ]; ring

/-- Replacing bit i exchanges its old and new contributions at weight 2^i. -/
theorem wordValue_set {raw p i wire v} (w : Word) (hi : i < w.size)
    (h : HasBit raw p wire v) :
    wordValue raw p (w.set! i wire) + 2^i * (wireValue raw p (bit w i)).toNat =
      wordValue raw p w + 2^i * v.toNat := by
  have hv := digitsValue_set (w.toList.map (wireValue raw p)) i v (by simpa using hi)
  rw [List.getElem_map, Array.getElem_toList] at hv
  simpa [wordValue, bit, Array.getElem?_eq_getElem hi, h.2] using hv

theorem set_valid {raw p wire v} (w : Word) (i : Nat) (h : HasBit raw p wire v)
    (hw : ∀ j ∈ w.toList, j < p.size) :
    ∀ j ∈ (w.set! i wire).toList, j < p.size := by
  intro j hj
  have hm : j ∈ w.toList.set i wire := by simpa using hj
  rcases List.mem_or_eq_of_mem_set hm with hm | rfl
  · exact hw j hm
  · exact h.1

private def muxLoop (sel : Nat) (a b : Word) (indices : List Nat) (out : Word) : Build Word := do
  let mut out := out
  for i in indices do out := out.push (← mux sel (bit a i) (bit b i))
  return out

private theorem muxLoop_spec {raw sel choose} (a b : Word) (av bv : Nat → Bool)
    (indices : List Nat) (p : Array Gate) (out : Word) (xs : List Bool) (s : Seeded raw p)
    (hs : HasBit raw p sel choose)
    (ha : ∀ i, HasBit raw p (bit a i) (av i)) (hb : ∀ i, HasBit raw p (bit b i) (bv i))
    (hw : HasWord raw p out xs) :
    Builds raw p (muxLoop sel a b indices out) (fun q result =>
      HasWord raw q result (xs ++ indices.map (fun i => if choose then av i else bv i))) := by
  induction indices generalizing p out xs with
  | nil =>
    simpa [muxLoop] using (builds_pure (raw := raw) (x := out)
      (post := fun q w => HasWord raw q w xs) hw)
  | cons i is ih =>
    have he : muxLoop sel a b (i :: is) out =
        (mux sel (bit a i) (bit b i) >>= fun d => muxLoop sel a b is (out.push d)) := by
      simp [muxLoop]
    rw [he]
    refine (mux_bit s hs (ha i) (hb i)).bind fun q d e hd => ?_
    simpa [List.append_assoc] using ih q (out.push d) _ (s.mono e) (hs.mono e)
      (fun j => (ha j).mono e) (fun j => (hb j).mono e) ((hw.mono e).push hd)

theorem muxw_nat {raw p sel choose} (s : Seeded raw p) (hs : HasBit raw p sel choose)
    (a b : Word) (ha : ∀ j ∈ a.toList, j < p.size) (hb : ∀ j ∈ b.toList, j < p.size) :
    Builds raw p (muxw sel a b) (fun q out =>
      out.size = a.size ∧ (∀ j ∈ out.toList, j < q.size) ∧
      wordValue raw q out = (if choose then wordValue raw p a else wordValueAt raw p b a.size)) := by
  have he : muxw sel a b = muxLoop sel a b (List.range a.size) #[] := by
    simp [muxw, muxLoop, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.range_eq_range']
  rw [he]
  have empty : HasWord raw p #[] [] := ⟨by simp, rfl⟩
  have h := muxLoop_spec a b _ _ (List.range a.size) p #[] [] s hs
    (bit_valid s a ha) (bit_valid s b hb) empty
  rcases h with ⟨ext, hw⟩
  refine ⟨ext, ?_, hw.1, ?_⟩
  · simpa using congrArg List.length hw.2
  · change digitsValue _ = _
    rw [hw.2]
    cases choose <;> simp [← wordValueAt_size raw p a, wordValueAt]

end PoissonDAG.PORS.RankGates
