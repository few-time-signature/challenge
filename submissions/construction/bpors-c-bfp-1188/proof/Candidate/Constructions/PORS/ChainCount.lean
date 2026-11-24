import Candidate.Constructions.PORS.ChainPacking
import Candidate.Probability.UniformAverage

namespace PoissonDAG.PORS.ChainCount
open ChainRows ChainSupplier ChainPacking FiniteKernels ChainRefined

abbrev Hist (m : Nat) := Fin m → Rank
abbrev Guest (A : Type) := A × Rank

noncomputable def requests {A L : Type} [DecidableEq L] (order : A → Fin 4 ↪ L) (g : Guest A) :=
  ChainLift.requests (order g.1) (rankTuple g.2).val

def Delivers {A L : Type} {m : Nat} (order : A → Fin 4 ↪ L) (slots : Fin m → Fin 4 ↪ L)
    (h : Hist m) (g : Guest A) :=
  ∀ t : Fin 4, ∃ pos : Fin m × Fin 4, slots pos.1 pos.2 = order g.1 t ∧
    (rankTuple g.2).val t ≤ (rankTuple (h pos.1)).val pos.2

noncomputable instance {A L : Type} [DecidableEq L] {m : Nat} (order : A → Fin 4 ↪ L)
    (slots : Fin m → Fin 4 ↪ L) (h : Hist m) (g : Guest A) : Decidable (Delivers order slots h g) := by
  unfold Delivers
  infer_instance

section
variable {A L : Type} [DecidableEq L] {m : Nat} (order : A → Fin 4 ↪ L) (slots : Fin m → Fin 4 ↪ L)
abbrev Cases := {x : Hist m × Guest A // Delivers order slots x.1 x.2}

private def leaf (pos : Fin m × Fin 4) : L := slots pos.1 pos.2
private noncomputable def available (h : Hist m) (pos : Fin m × Fin 4) := (rankTuple (h pos.1)).val pos.2

private noncomputable def trace (x : Cases order slots) : W m :=
  ChainLift.witness (leaf slots) (available x.val.1) (order x.val.2.1) (rankTuple x.val.2.2).val
    (rankTuple x.val.2.2).property x.property

private theorem ok (x : Cases order slots) : Fits (trace order slots x) x.val.1 :=
  ChainLift.witness_ok (leaf slots) (available x.val.1) (order x.val.2.1) (rankTuple x.val.2.2).val
    (rankTuple x.val.2.2).property x.property

private noncomputable def codes (x : Cases order slots) := code (trace order slots x) x.val.1 (ok order slots x)

private theorem recovery (x : Cases order slots) (l : L) (d : Nat) :
    (l,d)∈requests order x.val.2 ↔ ∃ z : Fin m × Fin 4,
      leaf slots z=l ∧ offered (codes order slots x z.1) z.2=some d := by
  let w := trace order slots x
  have recovered : ChainLift.recover (leaf slots) w=requests order x.val.2 :=
    ChainLift.recover_witness _ _ _ _ _ x.property
  rw [← recovered]
  constructor
  · intro hm
    obtain ⟨z,_,id⟩ := Finset.mem_image.mp hm
    refine ⟨z.val,congrArg Prod.fst id,?_⟩
    change offered (code w _ _ z.val.1) z.val.2=some d
    rw [code_offered,dif_pos z.property]
    exact congrArg some (congrArg Prod.snd id)
  · rintro ⟨z,he,hs⟩
    change offered (code w _ _ z.1) z.2=some d at hs
    rw [code_offered] at hs
    split at hs
    next mem =>
      refine Finset.mem_image.mpr ⟨⟨z,mem⟩,Finset.mem_univ _,?_⟩
      exact Prod.ext he (Option.some.inj hs)
    next => contradiction

private noncomputable def compression (unique : Function.Injective (requests order)) :
    Cases order slots ↪ Packet m where
  toFun x := pack (codes order slots x) (code_valid _ _ _)
  inj' x y h := by
    have hc := congrArg unpack h
    rw [unpack_pack,unpack_pack] at hc
    apply Subtype.ext
    apply Prod.ext
    · funext j
      exact ((code_history _ _ _ j).symm.trans
        (congrArg history (congrFun hc j))).trans (code_history _ _ _ j)
    · apply unique
      ext pair
      obtain ⟨l,d⟩ := pair
      rw [recovery order slots x l d,recovery order slots y l d,hc]

theorem count [Fintype A] (unique : Function.Injective (requests order)) :
    (Finset.univ.filter (fun z : Hist m × Guest A => Delivers order slots z.1 z.2)).card ≤
      Fintype.card (Packet m) := by
  classical
  let e := compression order slots unique
  have inject : ↥(Finset.univ.filter (fun z : Hist m × Guest A => Delivers order slots z.1 z.2)) ↪
      Cases order slots := ⟨fun z => ⟨z.val,(Finset.mem_filter.mp z.property).2⟩,
        fun _ _ h => Subtype.ext (congrArg (fun v : Cases order slots => v.val) h)⟩
  simpa only [Fintype.card_coe] using Fintype.card_le_of_embedding (inject.trans e)
end

private theorem summand (m t D n : Nat) (t4 : t≤4) (pos : 0<D) :
    (m.choose t*n*D^(m-t) : ℚ) / (D:ℚ)^m =
      (m.choose t*n*D^(4-t) : ℚ) / (D:ℚ)^4 := by
  by_cases stop : m<t
  · simp [Nat.choose_eq_zero_of_lt stop]
  · have nz : (D:ℚ)≠0 := by exact_mod_cast pos.ne'
    have splitM : (D:ℚ)^m=(D:ℚ)^(m-t)*(D:ℚ)^t := by rw [←pow_add]; congr 1; omega
    have split4 : (D:ℚ)^4=(D:ℚ)^(4-t)*(D:ℚ)^t := by rw [←pow_add]; congr 1; omega
    rw [splitM,split4]
    field_simp

theorem average_bound {A L : Type} [Fintype A] [DecidableEq L] {m : Nat}
    (order : A → Fin 4 ↪ L) (slots : Fin m → Fin 4 ↪ L)
    (card : Fintype.card A=p.supports) (unique : Function.Injective (requests order)) :
    average (fun x : Hist m × Guest A => if Delivers order slots x.1 x.2 then (1:ℚ) else 0) ≤
      p.simplexChild coefs m := by
  classical
  let X := Hist m × Guest A
  let cut := (Finset.univ : Finset X).filter (fun x => Delivers order slots x.1 x.2)
  have hpop : Fintype.card X=p.depthCount^m*(p.supports*p.depthCount) := by
    simp only [X,Hist,Guest,Fintype.card_prod,Fintype.card_fun,card,Fintype.card_fin,ChainDepths.chain_depth_ranks.2]
  change _ ≤ min _ _
  unfold average
  rw [Finset.sum_boole]
  change (cut.card:ℚ) / Fintype.card X ≤ _
  apply le_min
  · have pos : (0:ℚ)<Fintype.card X := by rw [hpop]; norm_cast; exact Nat.mul_pos (Nat.pow_pos (by decide)) (by decide +kernel)
    exact (div_le_one pos).mpr (by exact_mod_cast Finset.card_le_univ cut)
  · have upper := count order slots unique
    have scale : (cut.card:ℚ) ≤ Fintype.card (Packet m) := by exact_mod_cast upper
    apply (div_le_div_of_nonneg_right scale (Nat.cast_nonneg _)).trans_eq
    rw [packet_card,hpop]
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_sum]
    rw [←div_div,Finset.sum_div]
    have eqs := Finset.sum_congr (s₁:=(Finset.univ : Finset (Fin 4))) rfl
      (fun t _ => summand m (t.val+1) p.depthCount (coefs[t.val]?.getD 0)
        (by have := t.isLt; omega) (by decide))
    rw [eqs]
    rw [← Finset.sum_div,div_div]
    simp only [show p.k=4 by rfl]
    have sumN (f : Nat → Nat) : (∑ t : Fin 4,f t.val) = ((List.range 4).map f).sum := by
      simp [Fin.sum_univ_succ,List.range_succ,Nat.add_assoc]
    rw [← sumN (fun i => Nat.fast_choose m (i+1) * coefs[i]?.getD 0 * p.depthCount^(4-(i+1)))]
    simp only [← Nat.choose_eq_fast_choose,Nat.cast_sum,Nat.cast_mul,Nat.cast_pow]
    congr 1
    ring

end PoissonDAG.PORS.ChainCount
