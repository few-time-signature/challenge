import Candidate.Constructions.PORS.RowUnrank
import Candidate.Constructions.PORS.ChainDepths

namespace PoissonDAG.PORS.RankGates.DepthGaps

def values (top next : Nat) : List Nat → List Nat
  | [] => [top-next]
  | x :: xs => (x-next) :: values top (x+1) xs

private def Ordered (top next : Nat) : List Nat → Prop
  | [] => next ≤ top
  | x :: xs => next ≤ x ∧ x < top ∧ Ordered top (x+1) xs

def loop (width top : Nat) (bars : List Word) (initial : Word) (acc : List Word) : Build (List Word) := do
  let mut depths := acc
  let mut next := initial
  for bar in bars do
    depths := (← addSub bar next true).1 :: depths
    next := (← addSub bar (lit width 1) false).1
  return ((← addSub (lit width top) next true).1 :: depths).reverse

private theorem list_mono {raw p q w ws xs} (e : Extends raw p q)
    (h : List.Forall₂ (Holds raw p w) ws xs) : List.Forall₂ (Holds raw q w) ws xs :=
  List.Forall₂.imp (fun _ _ hw => hw.mono e) h

private theorem related_snoc {R : α → β → Prop} {xs ys x y}
    (h : List.Forall₂ R xs ys) (last : R x y) : List.Forall₂ R (xs ++ [x]) (ys ++ [y]) := by
  induction h with
  | nil => exact .cons last .nil
  | cons hhead _ ih => exact .cons hhead ih

theorem reverse_related {R : α → β → Prop} {xs ys} (h : List.Forall₂ R xs ys) :
    List.Forall₂ R xs.reverse ys.reverse := by
  induction h with
  | nil => exact .nil
  | cons hhead _ ih => simpa only [List.reverse_cons] using related_snoc ih hhead

private theorem diff_eq {a b m : Nat} (le : b ≤ a) (fit : a < m) :
    (a+m-b)%m = a-b := by
  rw [show a+m-b = a-b+m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem loop_spec {raw w top} (oneFit : 1 < 2^w) (topFit : top < 2^w)
    (p : Array Gate) (bars : List Word) (xs : List Nat) (initial : Word) (next : Nat)
    (acc : List Word) (prev : List Nat) (s : Seeded raw p) (hn : Holds raw p w initial next)
    (hb : List.Forall₂ (Holds raw p w) bars xs) (ordered : Ordered top next xs)
    (ha : List.Forall₂ (Holds raw p w) acc prev) :
    Builds raw p (loop w top bars initial acc) (fun q out =>
      List.Forall₂ (Holds raw q w) out (prev.reverse ++ values top next xs)) := by
  induction bars generalizing p xs initial next acc prev with
  | nil =>
    cases hb
    have litTop : Holds raw p w (lit w top) top := by
      simpa only [Nat.mod_eq_of_lt topFit] using holds_literal s w top
    have he : loop w top [] initial acc = (do
        let z ← addSub (lit w top) initial true
        return (z.1 :: acc).reverse) := by simp [loop]
    rw [he]
    refine (holds_sub s litTop hn).bind fun q z e h => ?_
    apply builds_pure
    have hdiff : Holds raw q w z.1 (top-next) := diff_eq ordered topFit ▸ h.1
    have hlist := List.Forall₂.cons hdiff (list_mono e ha)
    simpa [values] using reverse_related hlist
  | cons bar bars ih =>
    cases xs with
    | nil => cases hb
    | cons x xs =>
      obtain ⟨hbar, hbars⟩ := List.forall₂_cons.mp hb
      obtain ⟨lower, upper, htail⟩ := ordered
      have he : loop w top (bar::bars) initial acc = (do
          let delta ← addSub bar initial true
          let nxt ← (do let z ← addSub bar (lit w 1) false; return z.1)
          loop w top bars nxt (delta.1::acc)) := by
        simp [loop, List.forIn_cons, bind_assoc]
      rw [he]
      refine (holds_sub s hbar hn).bind fun q delta e hdelta => ?_
      have hd : Holds raw q w delta.1 (x-next) := diff_eq lower hbar.fits ▸ hdelta.1
      have hone : Holds raw q w (lit w 1) 1 := by
        simpa only [Nat.mod_eq_of_lt oneFit] using holds_literal (s.mono e) w 1
      have step : Builds raw q (do let z ← addSub bar (lit w 1) false; return z.1)
          (fun v z => Holds raw v w z (x+1)) := by
        have h := holds_add (s.mono e) (hbar.mono e) hone
        rw [Nat.mod_eq_of_lt (show x+1 < 2^w by omega)] at h
        exact h
      refine step.bind fun r nxt f hnext => ?_
      have ef := e.trans f
      have saved := List.Forall₂.cons (hd.mono f) (list_mono ef ha)
      simpa [values, List.append_assoc] using
        ih r xs nxt (x+1) _ _ (s.mono ef) hnext (list_mono ef hbars) htail saved

def wordProgram (row : Row) (depthRank : Word) : Build (List Word) := do
  if row.cap=0 then return List.replicate row.k (lit (width row) 0)
  let bars ← unrank (row.E+row.k-1) (row.k-1) depthRank
  loop (width row) (row.E+row.k-1) bars (lit (width row) 0) []

def chainValues (r : Nat) :=
  values 35 0 (Colex.digits 35 3 r).reverse

theorem chainValues_eq_profile (r : Fin ((35 : Nat).choose 3)) :
    let profile := ChainDepths.profileOfRank 32 r
    chainValues r.val = [profile.a, profile.b, profile.c, profile.d] := by
  have h := ChainDepths.digits_ofRank (E := 32) r
  change Colex.digits 35 3 r.val = _ at h
  simp [chainValues, h, values, ChainDepths.profileOfRank, ChainDepths.gaps]

theorem bucket_program {raw p d} (s : Seeded raw p) :
    Builds raw p (wordProgram BucketRefined.p d) (fun q out =>
      List.Forall₂ (Holds raw q (width BucketRefined.p)) out (List.replicate BucketRefined.p.k 0)) := by
  have hc : BucketRefined.p.cap=0 := rfl
  simp only [wordProgram, hc]
  apply builds_pure
  have hz : Holds raw p (width BucketRefined.p) (lit (width BucketRefined.p) 0) 0 := by
    simpa only [Nat.zero_mod] using holds_literal s (width BucketRefined.p) 0
  generalize BucketRefined.p.k = k
  induction k with
  | zero => exact .nil
  | succ k ih => exact .cons hz ih

theorem chain_program {raw p d r} (s : Seeded raw p)
    (hd : Holds raw p (width ChainRefined.p) d r) (hr : r < ChainRefined.p.depthCount) :
    Builds raw p (wordProgram ChainRefined.p d) (fun q out =>
      List.Forall₂ (Holds raw q (width ChainRefined.p)) out (chainValues r)) := by
  let w := width ChainRefined.p
  have hr' : r < (35 : Nat).choose 3 := by
    have h := ChainDepths.chain_depth_ranks.2
    exact h.symm ▸ hr
  have hsep : r < (ChainRefined.p.E+ChainRefined.p.k-1).choose (ChainRefined.p.k-1) := hr'
  have hc : ¬ChainRefined.p.cap=0 := by decide
  simp only [wordProgram, if_neg hc]
  refine (RowUnrank.chain_separators s hd hsep).bind fun q bars e hb => ?_
  let u : Fin ((32+3).choose 3) := ⟨r, hr'⟩
  let B := ChainDepths.ofRank 32 u
  have shape : Colex.digits 35 3 r = [B.z, B.y, B.x] := ChainDepths.digits_ofRank u
  have order : Ordered 35 0 (Colex.digits 35 3 r).reverse := by
    rw [shape]
    have hxy := B.xy
    have hyz := B.yz
    have hbound := B.bound
    simp [Ordered] <;> omega
  have sz : 1 < 2^w := by decide
  have tz : 35 < 2^w := by decide
  have hz : Holds raw q w (lit w 0) 0 := by simpa only [Nat.zero_mod] using holds_literal (s.mono e) w 0
  change Builds raw q (loop w 35 bars (lit w 0) []) (fun v out => List.Forall₂ (Holds raw v w) out (chainValues r))
  simpa only [List.reverse_nil, List.nil_append, chainValues] using
    loop_spec sz tz q bars (Colex.digits 35 3 r).reverse _ 0 [] [] (s.mono e) hz hb order .nil

end PoissonDAG.PORS.RankGates.DepthGaps
