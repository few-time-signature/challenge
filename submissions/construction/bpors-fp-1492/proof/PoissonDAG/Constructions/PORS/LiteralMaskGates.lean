import PoissonDAG.Constructions.PORS.Literal
import PoissonDAG.Constructions.PORS.WordSemantics
import Mathlib.Data.List.Forall2

namespace PoissonDAG.PORS.LiteralMaskSemantics

open RankGates Literal

theorem either_bit {raw p x y a b} (s : Seeded raw p)
    (hx : HasBit raw p x a) (hy : HasBit raw p y b) :
    BuildsBit raw p (either x y) (a || b) := by
  rcases hx with ⟨hx, rfl⟩
  rcases hy with ⟨hy, rfl⟩
  have X : HasBit raw p x (wireValue raw p x) := ⟨hx,rfl⟩
  have Y : HasBit raw p y (wireValue raw p y) := ⟨hy,rfl⟩
  unfold either
  split
  · rename_i h
    rcases h with h|h
    · subst x; apply builds_pure; simpa [s.2.2] using s.2
    · subst y; apply builds_pure; simpa [s.2.2] using s.2
  split
  · rename_i h
    subst x; apply builds_pure; simpa [s.1.2] using Y
  split
  · rename_i h
    rcases h with h|h
    · subst y; apply builds_pure; simpa [s.1.2] using X
    · subst y; apply builds_pure; simpa using X
  refine (neg_bit s X).bind fun q1 nx e1 hnx => ?_
  refine (neg_bit (s.mono e1) (Y.mono e1)).bind fun q2 ny e2 hny => ?_
  have e02 := e1.trans e2
  refine (both_bit (s.mono e02) (hnx.mono e2) hny).bind fun q3 nxy e3 hxy => ?_
  simpa using neg_bit (s.mono (e02.trans e3)) hxy

structure Number (raw : Nat) (p : Array Gate) (w : Nat) (a : Word) (n : Nat) : Prop where
  size : a.size = w
  valid : ∀ i ∈ a.toList, i < p.size
  value : wordValue raw p a = n

theorem Number.mono {raw p q w a n} (h : Number raw p w a n) (e : Extends raw p q) :
    Number raw q w a n := by
  refine ⟨h.size, fun i hi => Nat.lt_of_lt_of_le (h.valid i hi) e.size_le, ?_⟩
  unfold wordValue
  rw [List.map_congr_left (fun i hi => e.stable i (h.valid i hi))]
  exact h.value

private theorem add_exact {raw p w a b x y} (seed : Seeded raw p)
    (ha : Number raw p w a x) (hb : Number raw p w b y) (bound : x+y < 2^w) :
    Builds raw p (addSub a b false) (fun q v => Number raw q w v.1 (x+y)) := by
  have hh := addSub_nat raw p a b false seed ha.valid hb.valid
  refine ⟨hh.1, ?_⟩
  obtain ⟨hsize, hvalid, _, hval⟩ := hh.2
  refine ⟨hsize.trans ha.size,hvalid,?_⟩
  let z := (addSub a b false).run p
  have total : wordValue raw z.2 z.1.1 + 2^a.size*(wireValue raw z.2 z.1.2).toNat =
      wordValueAt raw p a a.size + wordValueAt raw p b a.size := hval
  have X : wordValueAt raw p a a.size = x := (wordValueAt_size _ _ _).trans ha.value
  have Y : wordValueAt raw p b a.size = y := by
    rw [show a.size=b.size from ha.size.trans hb.size.symm, wordValueAt_size, hb.value]
  rw [X,Y,ha.size] at total
  change wordValue raw z.2 z.1.1 = x+y
  cases carry : wireValue raw z.2 z.1.2 <;>
    simp only [carry,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at total <;>
    omega

private theorem lit_zero_list (w : Nat) : (lit w 0).toList = List.replicate w 0 := by
  apply List.ext_getElem
  · simp [lit]
  · intro i hi _
    simp [lit]

private theorem digits_false (w : Nat) : digitsValue (List.replicate w false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simp [List.replicate_succ, digitsValue, ih]

private theorem inc_number {raw p w i b} (seed : Seeded raw p) (hw : 0<w)
    (hi : HasBit raw p i b) : Number raw p w ((lit w 0).set! 0 i) b.toNat := by
  cases w with
  | zero => omega
  | succ w =>
    have he : ((lit (w+1) 0).set! 0 i).toList = i :: List.replicate w 0 := by
      simp [lit_zero_list, List.replicate_succ]
    constructor
    · simp [lit]
    · intro j hj
      rw [he] at hj
      rcases List.mem_cons.mp hj with rfl|ht
      · exact hi.1
      · have hj0 : j=0 := (List.eq_of_mem_replicate ht)
        simpa [hj0] using seed.1.1
    · unfold wordValue
      rw [he]
      simp [hi.2, seed.1.2, digitsValue, digits_false]

def increment (countHere : Bool) (l r : Bool) := if countHere then (xor l r).toNat else 0

private def sumCount (countHere : Bool) (l r : Part) : Build Word := do
  let mut count := (← addSub l.siblings r.siblings false).1
  if countHere then
    let inc := (lit count.size 0).set! 0 (← parity l.active r.active)
    count := (← addSub count inc false).1
  return count

private theorem sumCount_spec {raw p w x y A B} {l r : Part} (seed : Seeded raw p) (hw : 0<w)
    (hl : Number raw p w l.siblings x) (hr : Number raw p w r.siblings y)
    (ha : HasBit raw p l.active A) (hb : HasBit raw p r.active B)
    (countHere : Bool) (bound : x+y+increment countHere A B < 2^w) :
    Builds raw p (sumCount countHere l r) (fun q out => Number raw q w out (x+y+increment countHere A B)) := by
  have sum := add_exact seed hl hr (by omega)
  cases countHere with
  | false =>
    unfold sumCount
    refine sum.bind fun q pair _ h => ?_
    apply builds_pure
    simpa [increment] using h
  | true =>
    unfold sumCount
    refine sum.bind fun q pair e h => ?_
    refine (parity_bit (seed.mono e) (ha.mono e) (hb.mono e)).bind fun q' i e' hi => ?_
    have inc : Number raw q' w ((lit pair.1.size 0).set! 0 i) (increment true A B) := by
      simpa only [h.size,increment,if_true] using inc_number (seed.mono (e.trans e')) hw hi
    have s2 := add_exact (seed.mono (e.trans e')) (h.mono e') inc bound
    exact s2.bind (f := fun pair' => pure pair'.1)
      (post := fun q'' out => Number raw q'' w out (x+y+increment true A B))
      (fun _ _ _ ok => builds_pure ok)

/-- Boolean data for one subtree, with its root mark stored separately because
the parent may change that mark when the sibling is active. -/
structure View where
  active : Bool
  prefixMarks : List (Bool×Bool)
  root : Bool×Bool
  count : Nat

def joinView (countHere : Bool) (l r : View) : View :=
  ⟨l.active || r.active,
    (l.prefixMarks ++ [(l.root.1 || (!l.active && r.active), l.root.2)]) ++
      (r.prefixMarks ++ [(r.root.1 || (!r.active && l.active), r.root.2)]),
    (false,l.active || r.active), l.count+r.count+increment countHere l.active r.active⟩

def PairBits (raw : Nat) (p : Array Gate) (u : Nat×Nat) (b : Bool×Bool) : Prop :=
  HasBit raw p u.1 b.1 ∧ HasBit raw p u.2 b.2

def Marks (raw : Nat) (p : Array Gate) (u : Array (Nat×Nat)) (bs : List (Bool×Bool)) : Prop :=
  List.Forall₂ (PairBits raw p) u.toList bs

theorem Marks.mono {raw p q u bs} (h : Marks raw p u bs) (e : Extends raw p q) :
    Marks raw q u bs := List.Forall₂.imp (fun _ _ hj => ⟨hj.1.mono e, hj.2.mono e⟩) h

structure Represents (raw : Nat) (p : Array Gate) (w : Nat) (a : Part) (v : View) : Prop where
  active : HasBit raw p a.active v.active
  marks : ∃ (pre : Array (Nat×Nat)) (last : Nat×Nat), a.marks=pre.push last ∧
    Marks raw p pre v.prefixMarks ∧ PairBits raw p last v.root
  count : Number raw p w a.siblings v.count

theorem Represents.mono {raw p q w a v} (h : Represents raw p w a v) (e : Extends raw p q) :
    Represents raw q w a v := by
  obtain ⟨pre,last,hm,hp,hr⟩ := h.marks
  exact ⟨h.active.mono e, ⟨pre,last,hm,hp.mono e,hr.1.mono e,hr.2.mono e⟩, h.count.mono e⟩

private def controls (l r : Part) : Build (Nat×Nat×Nat) := do
  let ls ← both (← neg l.active) r.active
  let rs ← both (← neg r.active) l.active
  let a ← either l.active r.active
  let lm ← either l.marks.back!.1 ls
  let rm ← either r.marks.back!.1 rs
  return (a,lm,rm)

private theorem controls_spec {raw p A B L R} {l r : Part} (seed : Seeded raw p)
    (ha : HasBit raw p l.active A) (hb : HasBit raw p r.active B)
    (hl : HasBit raw p l.marks.back!.1 L) (hr : HasBit raw p r.marks.back!.1 R) :
    Builds raw p (controls l r) (fun q v => HasBit raw q v.1 (A || B) ∧
      HasBit raw q v.2.1 (L || (!A && B)) ∧ HasBit raw q v.2.2 (R || (!B && A))) := by
  unfold controls
  refine (neg_bit seed ha).bind fun q1 na e1 hna => ?_
  refine (both_bit (seed.mono e1) hna (hb.mono e1)).bind fun q2 ls e2 hls => ?_
  have e02 := e1.trans e2
  refine (neg_bit (seed.mono e02) (hb.mono e02)).bind fun q3 nb e3 hnb => ?_
  have e03 := e02.trans e3
  refine (both_bit (seed.mono e03) hnb (ha.mono e03)).bind fun q4 rs e4 hrs => ?_
  have e04 := e03.trans e4
  refine (either_bit (seed.mono e04) (ha.mono e04) (hb.mono e04)).bind fun q5 a e5 hA => ?_
  have e05 := e04.trans e5
  refine (either_bit (seed.mono e05) (hl.mono e05) (hls.mono ((e3.trans e4).trans e5))).bind
    fun q6 lm e6 hlm => ?_
  have e06 := e05.trans e6
  refine (either_bit (seed.mono e06) (hr.mono e06) (hrs.mono (e5.trans e6))).bind
    fun q7 rm e7 hrm => ?_
  exact builds_pure ⟨hA.mono (e6.trans e7), hlm.mono e7, hrm⟩

private def finish (l r : Part) (c : Nat×Nat×Nat) (n : Word) : Part :=
  let lmark := l.marks.set! (l.marks.size-1) (c.2.1,l.marks.back!.2)
  let rmark := r.marks.set! (r.marks.size-1) (c.2.2,r.marks.back!.2)
  ⟨c.1,(lmark++rmark).push (0,c.1),n⟩

private theorem merge_as_parts (countHere : Bool) (l r : Part) :
    merge countHere l r = (do
      let c ← controls l r
      let n ← sumCount countHere l r
      pure (finish l r c n)) := by
  cases countHere <;> rfl

private theorem reset_last {α : Type} [Inhabited α] (p : Array α) (x y : α) :
    (p.push x).set! ((p.push x).size-1) y = p.push y := by
  simp [Array.setIfInBounds, Array.set_push]

/-- The literal gate builder correctly forces both child-root marks and
updates its actual sibling counter. -/
theorem merge_spec {raw p w l r L R} (seed : Seeded raw p) (hw : 0<w)
    (hl : Represents raw p w l L) (hr : Represents raw p w r R) (countHere : Bool)
    (bound : (joinView countHere L R).count < 2^w) :
    Builds raw p (merge countHere l r) (fun q v => Represents raw q w v (joinView countHere L R)) := by
  obtain ⟨lp,lw,el,pl,wl⟩ := hl.marks
  obtain ⟨rp,rw,er,pr,wr⟩ := hr.marks
  rw [merge_as_parts]
  refine (controls_spec seed hl.active hr.active
    (by simpa [el] using wl.1) (by simpa [er] using wr.1)).bind fun q c e hc => ?_
  refine (sumCount_spec (seed.mono e) hw (hl.count.mono e) (hr.count.mono e)
    (hl.active.mono e) (hr.active.mono e) countHere bound).bind fun q' n e' hn => ?_
  apply builds_pure
  have E := e.trans e'
  refine ⟨hc.1.mono e', ?_, hn⟩
  refine ⟨(lp.push (c.2.1,lw.2)) ++ (rp.push (c.2.2,rw.2)), (0,c.1), ?_, ?_,
    (seed.mono E).1, hc.1.mono e'⟩
  · simp only [finish, el, er, Array.back!_push, reset_last]
  · change List.Forall₂ _ _ _
    simp only [Array.toList_append, Array.toList_push, joinView]
    have H1 : PairBits raw q' (c.2.1,lw.2) (L.root.1 || (!L.active && R.active), L.root.2) :=
      ⟨hc.2.1.mono e',wl.2.mono E⟩
    have H2 : PairBits raw q' (c.2.2,rw.2) (R.root.1 || (!R.active && L.active), R.root.2) :=
      ⟨hc.2.2.mono e',wr.2.mono E⟩
    exact List.rel_append (List.rel_append (pl.mono E) (.cons H1 .nil))
      (List.rel_append (pr.mono E) (.cons H2 .nil))

/-- Evaluate the reference masks in the same postorder as the builder. -/
def shapeView (countHere : Bool) (leaf : Nat → View) : Shape → Nat → View
  | .leaf, off => leaf off
  | .branch l r, off => joinView countHere (shapeView countHere leaf l off)
      (shapeView countHere leaf r (off+l.leaves))

/-- The word-width condition is imposed only on the branches of this execution. -/
def Fits (countHere : Bool) (v : Nat → View) (w : Nat) : Shape → Nat → Prop
  | .leaf, _ => True
  | .branch l r, off => (shapeView countHere v (.branch l r) off).count < 2^w ∧
      Fits countHere v w l off ∧ Fits countHere v w r (off+l.leaves)

theorem atShape_spec (countHere : Bool) (leaf : Nat → Build Part) (v : Nat → View)
    (s : Shape) (off raw : Nat) (p : Array Gate) (w : Nat) (seed : Seeded raw p) (hw : 0<w)
    (atLeafSpec : ∀ i, off ≤ i → i < off+s.leaves → ∀ q, Extends raw p q →
      Builds raw q (leaf i) (fun q' a => Represents raw q' w a (v i)))
    (bound : Fits countHere v w s off) :
    Builds raw p (atShape countHere leaf s off) (fun q a => Represents raw q w a (shapeView countHere v s off)) := by
  induction s generalizing p off with
  | leaf => exact atLeafSpec off le_rfl (by simp [Shape.leaves]) p (Extends.refl _ _)
  | branch l r il ir =>
    unfold atShape
    simp only [Shape.leaves] at atLeafSpec
    refine (il off p seed (fun i hlo hhi q e => atLeafSpec i hlo (by omega) q e)
      bound.2.1).bind fun q a eq ha => ?_
    refine (ir (off+l.leaves) q (seed.mono eq)
      (fun i hlo hhi q' e => atLeafSpec i (by omega) (by omega) q' (eq.trans e))
      bound.2.2).bind fun q' b eq' hb => ?_
    exact merge_spec (seed.mono (eq.trans eq')) hw (ha.mono eq') hb countHere bound.1

end PoissonDAG.PORS.LiteralMaskSemantics
