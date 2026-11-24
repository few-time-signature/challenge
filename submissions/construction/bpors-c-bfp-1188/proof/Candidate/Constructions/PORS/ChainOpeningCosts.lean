import Candidate.Constructions.PORS.ChainCoordGates
import Candidate.Constructions.PORS.ChainLeafOpening
import Candidate.Constructions.PORS.BucketCoordRoute
import Candidate.Constructions.PORS.BucketOpeningCosts

section

namespace PoissonDAG.PORS.ChainCoord

open LiteralMaskSemantics ChainLeafGates PrunedCount

/-- Looking up a depth recovers its selected pair when leaf addresses are distinct. -/
theorem lookup_mem (xs : List (Nat×Nat)) (distinct : (xs.map Prod.fst).Nodup) (i e : Nat) :
    xs.lookup i=some e ↔ (i,e)∈xs := by
  induction xs with
  | nil => simp
  | cons z xs ih =>
    obtain ⟨j,d⟩ := z
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
    by_cases h : i=j
    · subst j
      have absent : (i,e)∉xs := fun mem => fresh (List.mem_map.mpr ⟨(i,e),mem,rfl⟩)
      simp [absent,eq_comm]
    · simpa [List.lookup_cons,beq_false_of_ne h,h,Ne.symm h] using ih tail

def start (cap : Nat) (xs : List (Nat×Nat)) (i : Nat) : Option (Opening (chain (cap+1))) :=
  (xs.lookup i).map (fun e => openChain (cap+1) (cap-e))

/-- The actual pair list determines the chain stopping positions in the inner
tree. No mask agreement is required as an input. -/
theorem inner_route (cap : Nat) (xs : List (Nat×Nat)) (s : Shape) (off : Nat)
    (distinct : (xs.map Prod.fst).Nodup) (bound : ∀ i e, (i,e)∈xs → e ≤ cap)
    (active : (inner cap xs s off).active=true) :
    ∃ a, openSelected (chain (cap+1)) (start cap xs) s off=some a ∧
      (inner cap xs s off).prefixMarks ++ [(inner cap xs s off).root]=a.marks := by
  let v := fun i => chainView cap i xs
  have correct (i : Nat) : (v i).active=(start cap xs i).isSome ∧
      ∀ other, withSibling (v i) other =
        match start cap xs i with
        | some a => a.marks
        | none => List.replicate ((chain (cap+1)).nodes-1) (false,false) ++ [(other,false)] := by
    cases hd : xs.lookup i with
    | none =>
      have absent (d) : (i,d)∉xs := fun h => by
        have h' := (lookup_mem xs distinct i d).mpr h
        simp [hd] at h'
      simpa [start,hd,chain_nodes,v] using absent_leaf cap i xs absent
    | some e =>
      have atIndex (d) : (i,d)∈xs ↔ d=e := by
        rw [← lookup_mem xs distinct i d,hd]
        simp [eq_comm]
      have he := bound i e ((atIndex e).mpr rfl)
      simpa [start,hd,v] using selected_leaf cap i e xs atIndex he
  apply BucketCoord.route_from_leaves (chain (cap+1)) (start cap xs) v (fun i => (correct i).1) _ s off true active
  intro i other
  have h := (correct i).2 other
  cases ho : start cap xs i <;> simp only [ho] at h ⊢ <;> exact h

/-- The selected bucket carries the actual chain openings and all stopped
siblings on its outer path. The native counter counts only inner siblings. -/
theorem routed_coord (cap : Nat) (xs : List (Nat×Nat)) (child outer : Shape) (idx : Nat)
    (distinct : (xs.map Prod.fst).Nodup) (bound : ∀ i e, (i,e)∈xs → e ≤ cap)
    (u : Finset (Leaf child)) (agree : ∀ x, live xs (leafIndex child x).val=true ↔ x∈u)
    (nonempty : 0<u.card) (idx_lt : idx<outer.leaves) :
    let v := BucketCoord.coordView outer (inner cap xs child 0) idx
    v.count=siblings child u ∧ v.active=true ∧
      ∃ a, routedOpening .leaf outer child cap (fun _ => idx) (fun _ j => xs.lookup j) = some a ∧
        v.prefixMarks ++ [v.root]=a.marks := by
  have H := inner_support cap xs child 0 u (by simpa using agree)
  have active : (inner cap xs child 0).active=true := by simpa [nonempty] using H.1
  obtain ⟨innerOpen,hInner,marks⟩ := inner_route cap xs child 0 distinct bound active
  obtain ⟨a,hOuter,hMarks⟩ := BucketCoord.outer_route outer 0 idx innerOpen _ active marks
    ⟨by omega,by simpa using idx_lt⟩
  refine ⟨H.2,?_,a,?_,hMarks⟩
  · change (BucketCoord.outerView outer (inner cap xs child 0) idx 0).active=true
    simp [BucketCoord.outer_active,active,idx_lt]
  · change openSelected _ (fun j => if j=idx then
        openSelected (chain (cap+1)) (start cap xs) child 0 else none) outer 0=some a
    rw [hInner]
    exact hOuter

end PoissonDAG.PORS.ChainCoord
end

section

namespace PoissonDAG.PORS.ChainCoord

open ChainLeafGates PrunedCount

set_option allowUnsafeReducibility true in
attribute [local reducible] Leaf Shape.fill

/-- Sum decoded residuals whose leaf indices lie in a subtree interval. -/
def mass (lo n : Nat) : List (Nat×Nat) → Nat
  | [] => 0
  | x::xs => (if lo ≤ x.1 ∧ x.1<lo+n then x.2 else 0) + mass lo n xs

private theorem mass_split (lo n m : Nat) (xs : List (Nat×Nat)) :
    mass lo (n+m) xs = mass lo n xs + mass (lo+n) m xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mass,ih]
    split_ifs <;> omega

private theorem mass_one (off : Nat) (xs : List (Nat×Nat)) (distinct : (xs.map Prod.fst).Nodup) :
    mass off 1 xs = (xs.lookup off).getD 0 := by
  induction xs with
  | nil => rfl
  | cons z xs ih =>
    rcases z with ⟨j,e⟩
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
    rw [mass,ih tail]
    by_cases h : off=j
    · subst j
      have hn : xs.lookup off=none := by
        cases he : xs.lookup off with
        | none => rfl
        | some d =>
          have hd := (lookup_mem xs tail off d).mp he
          exact (fresh (List.mem_map.mpr ⟨(off,d),hd,rfl⟩)).elim
      simp [hn]
    · simp [List.lookup_cons,beq_false_of_ne h]
      omega

theorem mass_all (n : Nat) (xs : List (Nat×Nat)) (room : ∀ x ∈ xs, x.1<n) :
    mass 0 n xs=(xs.map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [mass,room x (by simp),ih (fun y hy => room y (by simp [hy]))]

private def supply {t : Tree} (a : Opening t) := weight (a.marks.map Prod.fst)
private def work {t : Tree} (a : Opening t) := weight (a.marks.map Prod.snd)

private theorem stopS (t : Tree) : supply (.stop t)=1 := by
  simp [supply,Opening.marks,weight,List.count_replicate]
private theorem stopW (t : Tree) : work (.stop t)=0 := by
  simp [work,Opening.marks,weight,List.count_replicate]
private theorem joinS {l r : Tree} (a : Opening l) (b : Opening r) :
    supply (.join a b)=supply a+supply b := by simp [supply,Opening.marks,weight]
private theorem joinW {l r : Tree} (a : Opening l) (b : Opening r) :
    work (.join a b)=work a+work b+1 := by simp [work,Opening.marks,weight,Nat.add_assoc]

private def Stats (cap : Nat) (s : Shape) (u : Finset (Leaf s)) (E : Nat) :
    Option (Opening (s.fill (chain (cap+1)))) → Prop
  | none => u.card=0 ∧ siblings s u=0 ∧ E=0
  | some a => 0<u.card ∧ supply a=u.card+siblings s u ∧ work a+1=2*u.card+siblings s u+E

private theorem stats (cap : Nat) (xs : List (Nat×Nat)) (distinct : (xs.map Prod.fst).Nodup)
    (bound : ∀ i e, (i,e)∈xs → e ≤ cap) (s : Shape) (off : Nat) (u : Finset (Leaf s))
    (agree : SingleOpeningCosts.Agrees s off (xs.lookup ·) u) :
    Stats cap s u (mass off s.leaves xs) (openSelected (chain (cap+1)) (start cap xs) s off) := by
  induction s generalizing off with
  | leaf =>
    change Finset Unit at u
    have ha := agree ()
    change (xs.lookup (off+0)).isSome=true ↔ ()∈u at ha
    rw [Nat.add_zero] at ha
    cases hd : xs.lookup off with
    | none =>
      have he : u=∅ := by
        ext x
        cases x
        simp [hd] at ha
        simp [ha]
      subst u
      simp [openSelected,start,hd,Stats,siblings,Shape.leaves,mass_one off xs distinct]
    | some e =>
      have he : u={()} := by
        ext x
        cases x
        simp [hd] at ha
        simp [ha]
      subst u
      obtain ⟨hs,hw⟩ := residual_weights cap e (bound off e ((lookup_mem xs distinct off e).mp hd))
      simp [openSelected,start,hd,Stats,siblings,Shape.leaves,mass_one off xs distinct,
        supply,work,hs,hw,Nat.add_comm]
      omega
  | branch l r il ir =>
    change Finset (Leaf l ⊕ Leaf r) at u
    have al : SingleOpeningCosts.Agrees l off (xs.lookup ·) u.toLeft := by
      intro x
      rw [Finset.mem_toLeft]
      exact agree (.inl x)
    have ar : SingleOpeningCosts.Agrees r (off+l.leaves) (xs.lookup ·) u.toRight := by
      intro x
      rw [Finset.mem_toRight,Nat.add_assoc]
      exact agree (.inr x)
    have hl := il off u.toLeft al
    have hr := ir (off+l.leaves) u.toRight ar
    have hcard : u.toLeft.card+u.toRight.card=u.card := Finset.card_toLeft_add_card_toRight
    cases el : openSelected (chain (cap+1)) (start cap xs) l off <;>
      cases er : openSelected (chain (cap+1)) (start cap xs) r (off+l.leaves) <;>
      simp only [openSelected,el,er,Stats,Shape.fill] at hl hr ⊢ <;>
      simp only [siblings,extraSibling,joinS,joinW,stopS,stopW,Shape.leaves,mass_split] <;>
      split_ifs <;> (repeat' constructor) <;> omega

theorem coord_weights (cap : Nat) (xs : List (Nat×Nat)) (child outer : Shape) (idx : Nat)
    (distinct : (xs.map Prod.fst).Nodup) (bound : ∀ i e, (i,e)∈xs → e ≤ cap)
    (room : ∀ x ∈ xs, x.1<child.leaves) (u : Finset (Leaf child))
    (agree : SingleOpeningCosts.Agrees child 0 (xs.lookup ·) u)
    (nonempty : 0<u.card) (idx_lt : idx<outer.leaves)
    {out : Opening (outer.fill (child.fill (chain (cap+1))))}
    (route : routedOpening .leaf outer child cap (fun _=>idx) (fun _ j => xs.lookup j) = some out) :
    weight (out.marks.map Prod.fst) = u.card+siblings child u+BucketCoord.pathDepth outer idx ∧
    weight (out.marks.map Prod.snd)+1 = 2*u.card+siblings child u+(xs.map Prod.snd).sum+
      BucketCoord.pathDepth outer idx := by
  have h := stats cap xs distinct bound child 0 u agree
  change openSelected _ (fun j => if j=idx then
    openSelected (chain (cap+1)) (start cap xs) child 0 else none) outer 0=some out at route
  cases ha : openSelected (chain (cap+1)) (start cap xs) child 0 with
  | none =>
    simp only [ha,Stats] at h
    omega
  | some a =>
    simp only [ha,Stats,mass_all child.leaves xs room,supply,work] at h
    rw [ha] at route
    have pw := BucketCoord.path_weights outer idx 0 a ⟨by omega,by simpa using idx_lt⟩ route
    simp only [Nat.sub_zero] at pw
    omega

open ChainRefined in
theorem production_weights (xs : List (Nat×Nat)) (idx : Nat)
    (distinct : (xs.map Prod.fst).Nodup) (bound : ∀ i e, (i,e)∈xs → e ≤ 32)
    (room : ∀ x ∈ xs, x.1<24) (u : Finset (Leaf (Literal.shape p.t)))
    (agree : SingleOpeningCosts.Agrees (Literal.shape p.t) 0 (xs.lookup ·) u)
    (hk : u.card=4) (E : (xs.map Prod.snd).sum=32) (idx_lt : idx<p.buckets)
    {out : Opening ((Literal.shape p.buckets).fill ((Literal.shape p.t).fill (chain (p.cap+1))))}
    (route : routedOpening .leaf (Literal.shape p.buckets) (Literal.shape p.t) p.cap
      (fun _=>idx) (fun _ j => xs.lookup j)=some out) :
    weight (out.marks.map Prod.fst) = 14+siblings (Literal.shape p.t) u ∧
    weight (out.marks.map Prod.snd) = 49+siblings (Literal.shape p.t) u := by
  have ho : (Literal.shape p.buckets).leaves=p.buckets := Literal.shape_card _ (by decide +kernel)
  have hc : (Literal.shape p.t).leaves=24 := Literal.shape_card _ (by decide +kernel)
  have hp : Literal.shape p.buckets=Literal.leftShape 10 0 := rfl
  have path : BucketCoord.pathDepth (Literal.shape p.buckets) idx=10 := by rw [hp,BucketCoord.complete_depth]
  have h := coord_weights p.cap xs (Literal.shape p.t) (Literal.shape p.buckets) idx distinct bound
    (fun x hx => by rw [hc]; exact room x hx) u agree (by omega) (by rwa [ho]) route
  rw [path,E,hk] at h
  omega

end PoissonDAG.PORS.ChainCoord
end
