import PoissonDAG.Constructions.PORS.ColexSupport
import PoissonDAG.Constructions.PORS.ChainRefinedRow

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
