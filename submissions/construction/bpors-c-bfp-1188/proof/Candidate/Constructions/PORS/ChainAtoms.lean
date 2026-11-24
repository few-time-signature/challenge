import Candidate.Constructions.PORS.ChainSupplier
import PoissonDAG.Constructions.PORS.ChainRefinedCoefficients
import Candidate.Probability.PackedCounts
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace PoissonDAG.PORS.ChainAtoms
open BoundedCompositions ChainSupplier ChainRefined

abbrev Mask (i : Nat) := ↥((Finset.univ : Finset (Fin 4)).powersetCard i)

noncomputable def order {i : Nat} (s : Mask i) : Fin i ≃ ↥s.val :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]; exact (Finset.mem_powersetCard.mp s.property).2)).symm

noncomputable def place {i : Nat} (s : Mask i) : Fin i ↪ Fin 4 :=
  (order s).toEmbedding.trans (Function.Embedding.subtype _)

abbrev Atom (i d : Nat) :=
  Σ s : Mask i, Σ v : NatTuple i d, ↥(ranksAbove (demand (place s) v.val))

theorem atom_card (i d : Nat) (positive : 0<i) (fits : d≤32) :
    Fintype.card (Atom i d) = simplexAtom 4 32 i d := by
  classical
  simp only [Atom,Fintype.card_sigma,Fintype.card_coe]
  simp_rw [local_choices i d positive fits]
  simp only [Finset.sum_const,Finset.card_univ,Mask,Fintype.card_coe,Finset.card_powersetCard,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,simplexAtom,← Nat.choose_eq_fast_choose]
  rw [Nat.mul_assoc]
  rfl

abbrev Kind := Fin 4 × Fin 33
abbrev Letter := Σ k : Kind, Atom (k.1.val+1) k.2.val
def deg (k : Kind) : Nat := k.1.val + 1 + 17*k.2.val
def base : Nat := 2^256
def goal : Nat := 4+17*32

private def basis : Nat := ∑ k : Kind, simplexAtom 4 32 (k.1.val+1) k.2.val * base^deg k
private def mass : Nat := ∑ k : Kind, simplexAtom 4 32 (k.1.val+1) k.2.val

private theorem weighted_fibers {K : Type} [Fintype K] (A : K → Type) [∀ k, Fintype (A k)]
    (w f : K → Nat) (card : ∀ k, Fintype.card (A k) = w k) :
    (∑ a : Sigma A, f a.1) = ∑ k, w k * f k := by
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,card]

private theorem sum_letter (f : Kind → Nat) :
    (∑ a : Letter, f a.1) = ∑ k : Kind, simplexAtom 4 32 (k.1.val+1) k.2.val * f k :=
  weighted_fibers (fun k : Kind => Atom (k.1.val+1) k.2.val) _ f
    (fun k => atom_card _ _ (Nat.succ_pos _) (by have := k.2.isLt; omega))

private theorem letter_count : Fintype.card Letter = mass := by
  rw [Fintype.card_sigma]
  unfold mass
  exact Finset.sum_congr rfl (fun k _ => atom_card _ _ (Nat.succ_pos _) (by have := k.2.isLt; omega))

noncomputable def words (j : Nat) := Finset.univ.filter (fun w : Fin j → Letter =>
  ∑ n, deg (w n).1 = goal)

private theorem word_digit {A : Type} [Fintype A] (d : A → Nat) (j b t : Nat)
    (bound : Fintype.card A ^ j < b) :
    (Finset.univ.filter (fun w : Fin j → A => ∑ i, d (w i) = t)).card =
      (∑ a : A, b^d a)^j/b^t%b := by
  classical
  have size : (Finset.univ : Finset (Fin j → A)).card < b := by
    simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin] using bound
  have he : (∑ a : A, b^d a)^j = ∑ x : Fin j → A, b^(∑ i, d (x i)) := by
    rw [Finset.sum_pow']
    simp only [Fintype.piFinset_univ,Finset.prod_pow_eq_pow_sum]
  rw [he,PackedCounts.digit_sum _ _ _ _ size]

private theorem packed (j : Nat) (bound : mass^j<base) :
    (words j).card = basis^j/base^goal%base := by
  have h : (∑ a : Letter, base^deg a.1) = basis := sum_letter (fun k => base^deg k)
  exact (word_digit (fun a : Letter => deg a.1) j base goal (by rw [letter_count]; exact bound)).trans
    (congrArg (fun n => n^j/base^goal%base) h)

/-- The numeric test uses only 132 types of single-supplier contribution.
One bivariate coefficient checks all residual distributions for each j. -/
private def finite (f : Nat → Nat → Nat) :=
  ((List.range 4).map fun i => ((List.range 33).map (f (i+1))).sum).sum

private theorem fin_sum (n : Nat) (f : Nat → Nat) :
    (∑ x : Fin n,f x.val) = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih => simp [Fin.sum_univ_castSucc,List.range_succ,ih]

private theorem grid (f : Nat → Nat → Nat) :
    (∑ k : Kind,f (k.1.val+1) k.2.val) = finite f := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x : Fin 4, ((List.range 33).map (f (x.val+1))).sum :=
      Finset.sum_congr rfl (fun x _ => fin_sum 33 (f (x.val+1)))
    _ = _ := fin_sum 4 (fun i => ((List.range 33).map (f (i+1))).sum)

def packedBasis := finite (fun i d => simplexAtom 4 32 i d * base^(i+17*d))
def totalMass := finite (fun i d => simplexAtom 4 32 i d)

private theorem basis_eq : basis=packedBasis := grid (fun i d => simplexAtom 4 32 i d * base^(i+17*d))
private theorem mass_eq : mass=totalMass := grid (simplexAtom 4 32)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem numeric : totalMass^4<base ∧
    ((List.range 4).map (fun a => packedBasis^(a+1)/base^goal%base)) = coefs := by
  decide +kernel

theorem counted (j : Nat) (positive : 0<j) (small : j≤4) :
    (words j).card = coefs[j-1]?.getD 0 := by
  have pos : 0<totalMass := by decide +kernel
  have bound := (Nat.pow_le_pow_right pos small).trans_lt numeric.1
  rw [packed j (mass_eq.symm ▸ bound),basis_eq,← numeric.2]
  have hj : j-1 < 4 := by omega
  simp only [List.getElem?_map,List.getElem?_range hj,Option.map_some,Option.getD_some,show j-1+1=j by omega]

end PoissonDAG.PORS.ChainAtoms
