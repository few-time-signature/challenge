import Candidate.Constructions.PORS.LiteralMaskLeaf
import Candidate.Constructions.PORS.LiteralMaskSemantics
import PoissonDAG.Constructions.PORS.ChainRefinedRow

section

namespace PoissonDAG.PORS.ChainLeafGates

open RankGates Literal LiteralMaskSemantics

structure Bits (raw : Nat) (p : Array Gate) (a : Word) (n : Nat) (f : Nat → Bool) : Prop where
  size : a.size=n
  value : ∀ j, j<n → HasBit raw p (bit a j) (f j)

theorem Bits.mono {raw p q a n f} (h : Bits raw p a n f) (e : Extends raw p q) :
    Bits raw q a n f := ⟨h.size, fun j hj => (h.value j hj).mono e⟩

private theorem Bits.write {raw p a n f i x v} (h : Bits raw p a n f)
    (hi : i<n) (hx : HasBit raw p x v) :
    Bits raw p (a.set! i x) n (fun j => if i=j then v else f j) := by
  refine ⟨by simp [h.size],?_⟩
  intro j hj
  by_cases he : i=j
  · subst j
    have hb : i<a.size := h.size.symm ▸ hi
    simpa only [bit,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt hb,
      Option.getD_some,if_pos rfl,if_true] using hx
  · simpa only [bit,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne he,if_neg he]
      using h.value j hj

theorem zero_bits {raw p} (seed : Seeded raw p) (n : Nat) :
    Bits raw p (Array.replicate n 0) n (fun _ => false) := by
  refine ⟨by simp,?_⟩
  intro j hj
  simpa [bit, Array.getElem?_replicate, hj] using seed.1

/-- One decoded pair updates all possible chain positions. -/
def depthLoop (w cap : Nat) (depth : Word) (here : Nat) (is : List Nat) (initial : Word) :
    Build Word := do
  let mut openings := initial
  for v in is do
    let hit ← both here (← eqw depth (lit w (cap-v)))
    openings := openings.set! v (← either (bit openings v) hit)
  return openings

private theorem depthLoop_cons (w cap : Nat) (depth : Word) (here v : Nat) (is : List Nat)
    (a : Word) : depthLoop w cap depth here (v::is) a = (do
      let digit ← eqw depth (lit w (cap-v))
      let hit ← both here digit
      let out ← either (bit a v) hit
      depthLoop w cap depth here is (a.set! v out)) := by
  simp [depthLoop,List.forIn_cons,bind_assoc]

def updated (f : Nat → Bool) (is : List Nat) (cap d : Nat) (here : Bool) (j : Nat) :=
  f j || (decide (j∈is) && (here && decide (d=cap-j)))

private theorem depth_spec (w cap n d raw : Nat) (p : Array Gate) (seed : Seeded raw p)
    (depth : Word) (hd : Number raw p w depth d) (here : Nat) (H : Bool) (hh : HasBit raw p here H)
    (is : List Nat) (a : Word) (f : Nat → Bool) (ha : Bits raw p a n f)
    (bounds : ∀ j ∈ is, j<n) (room : cap<2^w) :
    Builds raw p (depthLoop w cap depth here is a) (fun q out => Bits raw q out n (updated f is cap d H)) := by
  induction is generalizing p a f with
  | nil =>
    have he : updated f [] cap d H = f := by funext j; simp [updated]
    rw [he]
    simpa [depthLoop] using (builds_pure (raw := raw) (x := a) (post := fun q out => Bits raw q out n f) ha)
  | cons v vs ih =>
    rw [depthLoop_cons]
    have hv := bounds v (by simp)
    refine (eqw_number seed hd (literal_number seed w (cap-v) (by omega))).bind
      fun q1 digit e1 he => ?_
    refine (both_bit (seed.mono e1) (hh.mono e1) he).bind fun q2 hit e2 hm => ?_
    have E := e1.trans e2
    refine (either_bit (seed.mono E) ((ha.value v hv).mono E) hm).bind fun q3 out e3 ho => ?_
    have F := E.trans e3
    have upd := (ha.mono F).write hv ho
    have tail := ih q3 (seed.mono F) (hd.mono F) (hh.mono F) _ _ upd
      (fun j hj => bounds j (by simp [hj]))
    have law : updated (fun j => if v=j then f v || (H && decide (d=cap-v)) else f j)
        vs cap d H = updated f (v::vs) cap d H := by
      funext j
      by_cases h : v=j
      · subst j
        by_cases hj : v ∈ vs <;> simp [updated,hj]
      · simp [updated,List.mem_cons,h,Ne.symm h]
    rwa [law] at tail

def paired (raw : Nat) (p : Array Gate) (w : Nat) (pairs : List (Word×Word)) (xs : List (Nat×Nat)) :=
  List.Forall₂ (fun wd x => Number raw p w wd.1 x.1 ∧ Number raw p w wd.2 x.2) pairs xs

theorem paired_mono {raw p q w pairs xs} (h : paired raw p w pairs xs) (e : Extends raw p q) :
    paired raw q w pairs xs := List.Forall₂.imp (fun _ _ v => ⟨v.1.mono e,v.2.mono e⟩) h

def live (xs : List (Nat×Nat)) (i : Nat) := xs.any fun d => decide (d.1=i)
def offer (cap i : Nat) (xs : List (Nat×Nat)) (j : Nat) :=
  decide (j ≤ cap) && xs.any (fun d => decide (d.1=i) && decide (d.2=cap-j))

def pairsLoop (w cap i : Nat) (pairs : List (Word×Word)) (sel : Nat) (starts : Word) : Build (Nat×Word) := do
  let mut selected := sel
  let mut openings := starts
  for (s,e) in pairs do
    let here ← eqw s (lit w i)
    selected ← either selected here
    openings ← depthLoop w cap e here (List.range (cap+1)) openings
  return (selected,openings)

private theorem pairsLoop_cons (w cap i : Nat) (s d : Word) (rest : List (Word×Word))
    (sel : Nat) (starts : Word) : pairsLoop w cap i ((s,d)::rest) sel starts = (do
      let here ← eqw s (lit w i)
      let sel' ← either sel here
      let starts' ← depthLoop w cap d here (List.range (cap+1)) starts
      pairsLoop w cap i rest sel' starts') := by
  simp [pairsLoop,List.forIn_cons,bind_assoc]

theorem pairs_spec (w cap i raw : Nat) (pairs : List (Word×Word)) (xs : List (Nat×Nat))
    (p : Array Gate) (seed : Seeded raw p) (ds : paired raw p w pairs xs)
    (sel : Nat) (S : Bool) (hs : HasBit raw p sel S) (a : Word) (f : Nat → Bool)
    (ha : Bits raw p a (cap+2) f) (ic : i<2^w) (cc : cap<2^w) :
    Builds raw p (pairsLoop w cap i pairs sel a) (fun q out =>
      HasBit raw q out.1 (S || live xs i) ∧ Bits raw q out.2 (cap+2) (fun j => f j || offer cap i xs j)) := by
  induction pairs generalizing p xs sel S a f with
  | nil =>
    cases ds
    have hf : (fun j => f j || offer cap i [] j) = f := by funext j; simp [offer]
    rw [hf]
    simpa [live,pairsLoop] using
      (builds_pure (raw := raw) (x := (sel,a))
        (post := fun q v => HasBit raw q v.1 S ∧ Bits raw q v.2 (cap+2) f) ⟨hs,ha⟩)
  | cons z zs ih =>
    rcases z with ⟨s,d⟩
    cases xs with
    | nil => cases ds
    | cons z xs =>
      obtain ⟨head,tail⟩ := List.forall₂_cons.mp ds
      rw [pairsLoop_cons]
      refine (eqw_number seed head.1 (literal_number seed w i ic)).bind fun q1 here e1 hh => ?_
      refine (either_bit (seed.mono e1) (hs.mono e1) hh).bind fun q2 sel' e2 hs' => ?_
      have E := e1.trans e2
      refine (depth_spec w cap (cap+2) z.2 raw q2 (seed.mono E) d (head.2.mono E)
        here _ (hh.mono e2) (List.range (cap+1)) a f (ha.mono E)
        (fun j hj => by have := List.mem_range.mp hj; omega) cc).bind fun q3 opened e3 hOpen => ?_
      have F := E.trans e3
      have ht : paired raw p w zs xs := tail
      have h := ih xs q3 (seed.mono F) (paired_mono ht F) sel' _ (hs'.mono e3) opened _ hOpen
      have he : (fun j => updated f (List.range (cap+1)) cap z.2 (decide (z.1=i)) j || offer cap i xs j) =
          (fun j => f j || offer cap i (z::xs) j) := by
        funext j
        by_cases hj : j ≤ cap
        · simp [updated,offer,List.mem_range,show j<cap+1 by omega,hj,Bool.or_assoc]
        · simp [updated,offer,List.mem_range,show ¬j<cap+1 by omega,hj]
      rw [he] at h
      simpa [live,Bool.or_assoc] using h

end PoissonDAG.PORS.ChainLeafGates
end

section

namespace PoissonDAG.PORS.ChainLeafGates

open RankGates Literal LiteralMaskSemantics

/-- The second mark records whether some strictly earlier position was offered. -/
def scan (f : Nat → Bool) : List Nat → Bool → List (Bool×Bool) × Bool
  | [], k => ([], k)
  | v::vs, k =>
    let tail := scan f vs (k || f v)
    ((f v,k)::tail.1,tail.2)

theorem scan_append (f : Nat → Bool) (xs ys : List Nat) (k : Bool) :
    scan f (xs++ys) k =
      ((scan f xs k).1 ++ (scan f ys (scan f xs k).2).1,
       (scan f ys (scan f xs k).2).2) := by
  induction xs generalizing k with
  | nil => simp [scan]
  | cons x xs ih => simp [scan,ih]

private def markLoop (opens : Word) (is : List Nat) (start : Nat) (acc : Array (Nat×Nat)) :
    Build (Array (Nat×Nat) × Nat) := do
  let mut known := start
  let mut marks := acc
  for v in is do
    let offered := bit opens v
    marks := marks.push (offered,known)
    known ← either known offered
  return (marks,known)

private theorem markLoop_cons (opens : Word) (v : Nat) (vs : List Nat) (k : Nat)
    (acc : Array (Nat×Nat)) :
    markLoop opens (v::vs) k acc = (do
      let next ← either k (bit opens v)
      markLoop opens vs next (acc.push (bit opens v,k))) := by
  simp [markLoop,List.forIn_cons,bind_assoc] <;> rfl

private theorem mark_spec (raw n : Nat) (p : Array Gate) (seed : Seeded raw p)
    (opens : Word) (f : Nat → Bool) (bits : Bits raw p opens n f)
    (is : List Nat) (bounds : ∀ j ∈ is, j<n)
    (k : Nat) (b : Bool) (hk : HasBit raw p k b)
    (acc : Array (Nat×Nat)) (pre : List (Bool×Bool)) (hpre : Marks raw p acc pre) :
    Builds raw p (markLoop opens is k acc) (fun q out =>
      Marks raw q out.1 (pre++(scan f is b).1) ∧ HasBit raw q out.2 (scan f is b).2) := by
  induction is generalizing p k b acc pre with
  | nil =>
    simpa [markLoop,scan] using
      (builds_pure (raw := raw) (x := (acc,k))
        (post := fun q z => Marks raw q z.1 pre ∧ HasBit raw q z.2 b) ⟨hpre,hk⟩)
  | cons v vs ih =>
    rw [markLoop_cons]
    have hv := bits.value v (bounds v (by simp))
    refine (either_bit seed hk hv).bind fun q next e hn => ?_
    have hmore : Marks raw q (acc.push (bit opens v,k)) (pre++[(f v,b)]) := by
      change List.Forall₂ _ _ _
      rw [Array.toList_push]
      exact List.rel_append (hpre.mono e) (.cons ⟨hv.mono e,hk.mono e⟩ .nil)
    simpa only [scan,List.append_assoc,List.singleton_append] using
      ih q (seed.mono e) (bits.mono e) (fun j hj => bounds j (by simp [hj]))
        next _ hn _ _ hmore

private theorem atLeaf_loops (row : Row) (d : Digits) (i : Nat) :
    atLeaf row d i = (do
      let (selected,opens) ← pairsLoop (width row) row.cap i (d.leaves.zip d.depths) 0
        (Array.replicate (row.cap+2) 0)
      let (marks,_) ← markLoop opens (List.range (row.cap+2)) 0 #[]
      return ⟨selected,marks,lit (width row) 0⟩) := by
  simp [atLeaf,pairsLoop,depthLoop,markLoop,Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size,List.range_eq_range',bind_assoc] <;> rfl

/-- At the chain root no label is offered. The root plan bit is the OR of
all offers strictly below the root. -/
def chainView (cap i : Nat) (xs : List (Nat×Nat)) : View :=
  let pre := scan (offer cap i xs) (List.range (cap+1)) false
  ⟨live xs i,pre.1,(false,pre.2),0⟩

theorem scan_marks (cap i : Nat) (xs : List (Nat×Nat)) :
    (scan (offer cap i xs) (List.range (cap+2)) false).1 =
      (chainView cap i xs).prefixMarks ++ [(chainView cap i xs).root] := by
  rw [List.range_succ (n := cap+1),scan_append]
  simp [scan,chainView,offer]

/-- The protected leaf builder realizes every mark and the active flag for the
decoded list of leaf/residual pairs, at any chain capacity fitting the word. -/
theorem atLeaf_chain (row : Row) {raw p} (seed : Seeded raw p) (d : Digits)
    (xs : List (Nat×Nat)) (digits : paired raw p (width row) (d.leaves.zip d.depths) xs)
    (i : Nat) (hi : i<2^(width row)) (hc : row.cap<2^(width row)) :
    Builds raw p (atLeaf row d i) (fun q out =>
      Represents raw q (width row) out (chainView row.cap i xs)) := by
  rw [atLeaf_loops]
  refine (pairs_spec _ _ _ _ _ _ p seed digits 0 false seed.1 _
    (fun _ => false) (zero_bits seed _) hi hc).bind fun q sel e hs => ?_
  have bits : Bits raw q sel.2 (row.cap+2) (offer row.cap i xs) := by simpa using hs.2
  have active : HasBit raw q sel.1 (live xs i) := by simpa using hs.1
  refine (mark_spec raw (row.cap+2) q (seed.mono e) _ _ bits (List.range (row.cap+2))
    (fun j hj => List.mem_range.mp hj) 0 false (seed.mono e).1 #[] [] .nil).bind
    fun q' out e' hmarks => ?_
  apply builds_pure
  have all : Marks raw q' out.1 ((chainView row.cap i xs).prefixMarks ++ [(chainView row.cap i xs).root]) := by
    simpa only [List.nil_append, scan_marks] using hmarks.1
  obtain ⟨ws,x,he,hws,hx⟩ := last_pair _ _ _ all
  refine ⟨active.mono e',⟨ws.toArray,x,?_,?_,hx⟩,literal_number (seed.mono (e.trans e')) _ 0 (by positivity)⟩
  · apply Array.toList_inj.mp
    simpa using he
  · simpa [Marks] using hws

end PoissonDAG.PORS.ChainLeafGates
end
