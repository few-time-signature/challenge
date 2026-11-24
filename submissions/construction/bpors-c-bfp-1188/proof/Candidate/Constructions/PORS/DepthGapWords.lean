import Candidate.Constructions.PORS.ColexSupport
import PoissonDAG.Constructions.PORS.ChainRefinedRow
import Candidate.Constructions.PORS.RowUnrank

section

namespace PoissonDAG.PORS.ChainDepths

/-- The four chain digits in their assigned (increasing leaf) order. -/
@[ext] structure Profile (E : Nat) where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  total : a+b+c+d=E

@[ext] structure Bars (E : Nat) where
  x : Nat
  y : Nat
  z : Nat
  xy : x<y
  yz : y<z
  bound : z<E+3

def gaps {E : Nat} (s : Bars E) : Profile E where
  a := s.x
  b := s.y-(s.x+1)
  c := s.z-(s.y+1)
  d := (E+3)-(s.z+1)
  total := by have := s.xy; have := s.yz; have := s.bound; omega

def separators {E : Nat} (v : Profile E) : Bars E where
  x := v.a
  y := v.a+v.b+1
  z := v.a+v.b+v.c+2
  xy := by omega
  yz := by omega
  bound := by have := v.total; omega

def barsEquiv (E : Nat) : Bars E ≃ Profile E where
  toFun := gaps
  invFun := separators
  left_inv s := by
    have := s.xy; have := s.yz
    ext <;> simp [separators,gaps] <;> omega
  right_inv v := by
    have := v.total
    ext <;> simp [separators,gaps] <;> omega

private theorem three {α} {l : List α} (h : l.length=3) : ∃ z y x, l=[z,y,x] := by
  cases l with
  | nil => simp at h
  | cons z l =>
    cases l with
    | nil => simp at h
    | cons y l =>
      cases l with
      | nil => simp at h
      | cons x l =>
        have h0 : l.length=0 := by simpa using h
        exact ⟨z,y,x,by rw [List.length_eq_zero_iff.mp h0]⟩

def ofRank (E : Nat) (r : Fin ((E+3).choose 3)) : Bars E :=
  let d := Colex.digits (E+3) 3 r.val
  have shape : ∃ z y x, d=[z,y,x] := three (Colex.digits_length _ _ _)
  have spec := Colex.digits_spec (Nat.le_refl _) r.isLt
  have order : d[2]! < d[1]! ∧ d[1]! < d[0]! ∧ d[0]! < E+3 := by
    obtain ⟨z,y,x,h⟩ := shape
    have sorted : d.Pairwise (· > ·) := spec.2.2
    have bound := spec.2.1 z (by change z ∈ d; simp [h])
    simp [h] at sorted ⊢
    omega
  ⟨d[2]!,d[1]!,d[0]!,order.1,order.2.1,order.2.2⟩

theorem digits_ofRank {E : Nat} (r : Fin ((E+3).choose 3)) :
    Colex.digits (E+3) 3 r.val = [(ofRank E r).z,(ofRank E r).y,(ofRank E r).x] := by
  obtain ⟨z,y,x,h⟩ := three (Colex.digits_length (E+3) 3 r.val)
  simp [ofRank,h]

theorem rank_bijective (E : Nat) : Function.Bijective (ofRank E) := by
  constructor
  · intro r t he
    apply Fin.ext
    apply Colex.digits_injective r.isLt t.isLt
    rw [digits_ofRank r,digits_ofRank t,he]
  · intro s
    let ds := [s.z,s.y,s.x]
    have ord : ds.Pairwise (· > ·) := by
      have := s.xy; have := s.yz; simp [ds]; omega
    have valid : ds.toFinset ∈ (Finset.range (E+3)).powersetCard 3 := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_,by rw [List.toFinset_card_of_nodup ord.nodup]; rfl⟩
      intro i hi
      have := s.xy; have := s.yz; have := s.bound
      simp [ds] at hi
      exact Finset.mem_range.mpr (by rcases hi with h|h|h <;> omega)
    obtain ⟨r,hr⟩ := (Colex.support_bijective (E+3) 3).2 ⟨_,valid⟩
    have hset : (Colex.digits (E+3) 3 r.val).toFinset = ds.toFinset := congrArg Subtype.val hr
    have hd := (Colex.digits_spec (Nat.le_refl _) r.isLt).2.2.eq_of_mem_iff ord
      (fun i => by simpa only [List.mem_toFinset] using (Finset.ext_iff.mp hset i))
    rw [digits_ofRank r] at hd
    have coords : (ofRank E r).z = s.z ∧ (ofRank E r).y = s.y ∧ (ofRank E r).x = s.x := by
      simpa [ds] using hd
    exact ⟨r, Bars.ext coords.2.2 coords.2.1 coords.1⟩

/-- Every chain-depth rank represents exactly one profile of total 32. -/
def profileOfRank (E : Nat) (r : Fin ((E+3).choose 3)) := gaps (ofRank E r)

theorem chain_depth_ranks : Function.Bijective (profileOfRank 32) ∧
    (32+3).choose 3 = ChainRefined.p.depthCount :=
  ⟨(barsEquiv 32).bijective.comp (rank_bijective 32),by decide +kernel⟩

end PoissonDAG.PORS.ChainDepths
end

section

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
end
