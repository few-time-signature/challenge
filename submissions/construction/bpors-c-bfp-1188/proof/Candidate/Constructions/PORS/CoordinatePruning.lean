import Candidate.Constructions.PORS.PrunedCount
import PoissonDAG.Constructions.PORS.BucketRefinedSupport
import PoissonDAG.Constructions.PORS.ChainRefinedSupport
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace PoissonDAG.PORS.CoordinatePruning
open PrunedCount

def tuples (s : Shape) (k K : Nat) :=
  Fintype.piFinset (fun _ : Fin K => (Finset.univ : Finset (Leaf s)).powersetCard k)

def survivors (s : Shape) (k K M : Nat) :=
  (tuples s k K).filter (fun x => (∑ i, siblings s (x i)) ≤ M)

/-- Raising the child polynomial to K counts ordered supports, including
the correlations introduced by applying a single total sibling cutoff. -/
theorem count (s : Shape) (k K M B : Nat) (room : (s.leaves.choose k)^K < B-1) :
    (survivors s k K M).card = ((pack s B k)^K % B^(M+1)) % (B-1) := by
  classical
  have cap : (tuples s k K).card < B-1 := by
    simpa only [tuples,Fintype.card_piFinset_const,Finset.card_powersetCard,Finset.card_univ,
      card_leaf] using room
  rw [pack, Finset.sum_pow']
  simp only [Finset.prod_pow_eq_pow_sum]
  exact (truncated_card (tuples s k K) (fun x => ∑ i, siblings s (x i)) B M cap).symm

/-- Every surviving support tuple has the same number of independent
bucket and depth choices. -/
def configurations (s : Shape) (p : Row) :=
  (survivors s p.k p.K p.M) ×ˢ
    (Finset.univ : Finset (Fin p.K → Fin (p.buckets * p.depthCount)))

theorem count_row (p : Row) (h extra : Nat) (ht : 0 < p.t)
    (shapeEq : Literal.shape p.t = Literal.leftShape h extra)
    (room : p.supports^p.K < 2^(p.r+2)-1)
    (replay : p.leftFilledWords h extra = p.acceptedWords) :
    (configurations (Literal.shape p.t) p).card = p.acceptedWords := by
  have cap : ((Literal.shape p.t).leaves.choose p.k)^p.K < 2^(p.r+2)-1 := by
    rw [Literal.shape_card _ ht,Nat.choose_eq_fast_choose]; exact room
  have hp := packed_leftFilled p.k (2^(p.r+2)) h extra p.k le_rfl
  rw [← shapeEq] at hp
  rw [configurations, Finset.card_product, count _ _ _ _ _ cap, ← hp, ← replay]
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Row.leftFilledWords]

private theorem shape_at (n h extra : Nat) (hl : n.log2=h) (he : n-2^h=extra) :
    Literal.shape n = Literal.leftShape h extra := by simp only [Literal.shape, hl, he]

theorem bucket_configurations :
    (configurations (Literal.shape BucketRefined.p.t) BucketRefined.p).card =
      BucketRefined.p.acceptedWords :=
  count_row _ 10 768 (by decide) (shape_at _ _ _ (by decide) (by decide))
    (by decide +kernel) BucketRefined.accepted_word_count_replay.2

theorem chain_configurations :
    (configurations (Literal.shape ChainRefined.p.t) ChainRefined.p).card =
      ChainRefined.p.acceptedWords :=
  count_row _ 4 8 (by decide) (shape_at _ _ _ (by decide) (by decide))
    (by decide +kernel) ChainRefined.accepted_word_count_replay.2

end PoissonDAG.PORS.CoordinatePruning
