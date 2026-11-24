import Candidate.Constructions.PORS.ChainCount
import Candidate.Probability.UniformMatching

namespace PoissonDAG.PORS.ChainColumn
open FiniteKernels UniformMatching ChainCount ChainRows ChainRefined
noncomputable section

abbrev Draw (A : Type) (q : Nat) := Sample p.buckets q × (Hist q × Guest A)

def possible {A L : Type} {q : Nat} (order : A → Fin 4 ↪ L) (support : Fin q → Fin 4 ↪ L)
    (x : Draw A q) : Prop := ∀ t : Fin 4, ∃ h : Fin q, ∃ l : Fin 4,
    x.1.2 h=x.1.1 ∧ support h l=order x.2.2.1 t ∧
    (ChainSupplier.rankTuple x.2.2.2).val t ≤ (ChainSupplier.rankTuple (x.2.1 h)).val l

def hit {A L : Type} [DecidableEq L] {q : Nat} (order : A → Fin 4 ↪ L) (support : Fin q → Fin 4 ↪ L)
    (x : Draw A q) : ℚ := by
  classical
  exact if possible order support x then 1 else 0

private def matched {q : Nat} (b : Sample p.buckets q) :=
  Fintype.equivFinOfCardEq (Fintype.card_coe (matchingSet b))

attribute [local irreducible] Row.simplexChild ChainSupplier.rankTuple

set_option maxHeartbeats 1000000 in
private theorem average_instance {A : Type} (i j : Fintype A) (f : A → ℚ) :
    @average A i f = @average A j f := by cases Subsingleton.elim i j; rfl

private theorem fixed {A L : Type} [Fintype A] [DecidableEq L] {q : Nat}
    (order : A → Fin 4 ↪ L) (support : Fin q → Fin 4 ↪ L) (card : Fintype.card A=p.supports)
    (inj : Function.Injective (requests order)) (b : Sample p.buckets q) :
    average (fun x : Hist q × Guest A => hit order support (b,x)) ≤ p.simplexChild coefs (matchingSet b).card := by
  classical
  letI : Nonempty Rank := ⟨⟨0,by decide +kernel⟩⟩
  let S := matchingSet b
  let e : ↥S ≃ Fin S.card := matched b
  let restricted (z : Fin S.card) := support (e.symm z).val
  let F (h : Hist S.card) (t : Guest A) : ℚ := if Delivers order restricted h t then 1 else 0
  have project : average (fun x : Hist q × Guest A => hit order support (b,x)) ≤
      average (fun h : Hist q => average (fun t => F (fun z => h (e.symm z).val) t)) := by
    rw [average_prod]
    apply average_mono; intro h
    apply average_mono; intro t
    unfold hit
    split
    next yes =>
      have done : Delivers order restricted (fun z => h (e.symm z).val) t := by
        intro i
        obtain ⟨j,l,tag,leaf,weight⟩ := yes i
        let jj : S := ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,tag⟩⟩
        exact ⟨(e jj,l),by simpa [restricted,jj] using leaf,by simpa [jj] using weight⟩
      simp [F,done]
    next => dsimp [F]; split <;> norm_num
  apply project.trans
  let G (z : (↥S → Rank)) := average (fun t => F (fun j => z (e.symm j)) t)
  have first := average_restrict (A:=Rank) (fun j => j∈S) G
  have second := average_equiv (Equiv.arrowCongr e (Equiv.refl Rank)) G
    (fun h => average (F h)) (fun _ => rfl)
  apply first.le.trans
  apply (average_instance _ _ G).le.trans
  apply second.le.trans
  rw [← average_prod (fun x : Hist S.card × Guest A => F x.1 x.2)]
  exact average_bound order restricted card inj

private theorem fin_sum (n : Nat) (f : Nat → ℚ) :
    (∑ x : Fin n,f x.val) = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.sum_univ_castSucc,List.range_succ,ih]

theorem averaged {A L : Type} [Fintype A] [DecidableEq L] {q : Nat}
    (order : A → Fin 4 ↪ L) (support : Fin q → Fin 4 ↪ L) (card : Fintype.card A=p.supports)
    (inj : Function.Injective (requests order)) :
    average (hit order support) ≤ p.simplexBucket coefs q := by
  rw [average_prod]
  apply (average_mono (fixed order support card inj)).trans_eq
  have pos : 0<p.buckets := Nat.two_pow_pos _
  have nz : (p.buckets : ℚ) ≠ 0 := by exact_mod_cast pos.ne'
  have h := average_cardinality pos q (fun n => p.simplexChild coefs n.val)
  change average (fun b : Sample p.buckets q => p.simplexChild coefs (matchingSet b).card) = _ at h
  rw [h,Row.simplexBucket]
  let f (m : Nat) := ((Nat.fast_choose q m*(p.buckets-1)^(q-m):Nat):ℚ)*p.simplexChild coefs m
  change _ = ((List.range (q+1)).map f).sum / _
  rw [←fin_sum,Finset.sum_div]
  apply Finset.sum_congr rfl; intro m _
  rw [← byCount_eq_probability pos q m.val (by have := m.isLt; omega),byCount_eq_count]
  dsimp only [f]
  rw [← Nat.choose_eq_fast_choose]
  push_cast
  field_simp [nz]

end
end PoissonDAG.PORS.ChainColumn
