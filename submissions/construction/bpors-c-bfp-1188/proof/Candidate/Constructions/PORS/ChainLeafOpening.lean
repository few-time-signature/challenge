import Candidate.Constructions.PORS.ChainLeafMarks

namespace PoissonDAG.PORS.ChainLeafGates

open LiteralMaskSemantics

private theorem idle_scan (f : Nat → Bool) (js : List Nat) (b : Bool)
    (empty : ∀ j ∈ js, f j=false) :
    scan f js b = (List.replicate js.length (false,b),b) := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp [scan,empty j (by simp),ih (fun x hx => empty x (by simp [hx])),List.replicate_succ]

/-- A chain opened at position t offers one label after t blank nodes, then
hashes at each of the remaining positions. -/
def oneLabel (t extra : Nat) : List (Bool×Bool) :=
  (List.replicate t (false,false) ++ [(true,false)]) ++ List.replicate extra (false,true)

private theorem oneLabel_succ (t k : Nat) :
    oneLabel t (k+1) = oneLabel t k ++ [(false,true)] := by
  unfold oneLabel
  simp only [List.replicate_succ' (n := k), List.append_assoc]

private theorem single_scan (t k : Nat) :
    scan (fun j => decide (j=t)) (List.range (t+k+1)) false = (oneLabel t k,true) := by
  induction k with
  | zero =>
    have idle := idle_scan (fun j => decide (j=t)) (List.range t) false (fun j hj => by
      have := List.mem_range.mp hj
      simp [show j≠t by omega])
    simp only [Nat.add_zero,List.range_succ (n := t),scan_append,idle,List.length_range,scan,
      decide_true,Bool.false_or]
    simp [oneLabel]
  | succ k ih =>
    have ne : t+k+1≠t := by omega
    rw [show t+(k+1)+1=(t+k+1)+1 by omega,List.range_succ (n := t+k+1),scan_append,ih]
    simp [scan,ne,oneLabel_succ]

theorem openChain_marks (t k : Nat) : (openChain (t+k) t).marks=oneLabel t k := by
  induction k with
  | zero =>
    cases t <;> simp [openChain,Opening.marks,chain_nodes,chain,Tree.nodes,oneLabel]
  | succ k ih =>
    have gt : ¬ t+k+1 ≤ t := by omega
    rw [show t+(k+1)=t+k+1 by omega]
    simp only [openChain,if_neg gt,Opening.marks,ih,oneLabel_succ]

theorem residual_weights (cap e : Nat) (he : e ≤ cap) :
    let a := openChain (cap+1) (cap-e)
    weight (a.marks.map Prod.fst)=1 ∧ weight (a.marks.map Prod.snd)=e+1 := by
  have hc : cap-e+(e+1)=cap+1 := by omega
  have h := openChain_marks (cap-e) (e+1)
  rw [hc] at h
  simp [h,oneLabel,weight,List.count_replicate]

private theorem live_iff (xs : List (Nat×Nat)) (i : Nat) :
    live xs i=true ↔ ∃ e, (i,e)∈xs := by
  simp only [live,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨j,e⟩,h,rfl⟩
    exact ⟨e,h⟩
  · rintro ⟨e,h⟩
    exact ⟨(i,e),h,rfl⟩

private theorem offer_iff (cap i j : Nat) (xs : List (Nat×Nat)) :
    offer cap i xs j=true ↔ j ≤ cap ∧ (i,cap-j)∈xs := by
  simp only [offer,Bool.and_eq_true,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hj,⟨l,e⟩,h,hl,he⟩
    change l=i at hl
    change e=cap-j at he
    subst l
    subst e
    exact ⟨hj,h⟩
  · rintro ⟨hj,h⟩
    exact ⟨hj,(i,cap-j),h,rfl,rfl⟩

theorem selected_leaf (cap i e : Nat) (xs : List (Nat×Nat))
    (atIndex : ∀ d, (i,d)∈xs ↔ d=e) (he : e ≤ cap) :
    (chainView cap i xs).active=true ∧ ∀ other,
      withSibling (chainView cap i xs) other = (openChain (cap+1) (cap-e)).marks := by
  have act := (live_iff xs i).mpr ⟨e,(atIndex e).mpr rfl⟩
  refine ⟨act,fun other => ?_⟩
  have hf : offer cap i xs = fun j => decide (j=cap-e) := by
    funext j
    apply Bool.eq_iff_iff.mpr
    rw [offer_iff,atIndex,decide_eq_true_eq]
    omega
  have ss := single_scan (cap-e) (e+1)
  have ht : cap-e+(e+1)=cap+1 := by omega
  rw [ht] at ss
  have sm := scan_marks cap i xs
  rw [hf] at sm
  rw [ss] at sm
  have op := openChain_marks (cap-e) (e+1)
  rw [ht] at op
  have m := sm.symm.trans op.symm
  simpa [withSibling,chainView,act] using m

theorem absent_leaf (cap i : Nat) (xs : List (Nat×Nat)) (absent : ∀ d, (i,d)∉xs) :
    (chainView cap i xs).active=false ∧ ∀ other, withSibling (chainView cap i xs) other =
      List.replicate (cap+1) (false,false) ++ [(other,false)] := by
  have act : live xs i=false := by
    cases h : live xs i with
    | false => rfl
    | true =>
      obtain ⟨d,hd⟩ := (live_iff xs i).mp h
      exact (absent d hd).elim
  have hf (j) : offer cap i xs j=false := by
    cases h : offer cap i xs j with
    | false => rfl
    | true => exact (absent _ ((offer_iff _ _ _ _).mp h).2).elim
  have idle := idle_scan (offer cap i xs) (List.range (cap+1)) false (fun j _ => hf j)
  exact ⟨act,fun other => by simp [withSibling,chainView,idle,act]⟩

end PoissonDAG.PORS.ChainLeafGates
