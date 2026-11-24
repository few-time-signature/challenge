import Candidate.Constructions.PORS.GenericUnrank
import PoissonDAG.Constructions.PORS.BucketRefinedRow
import PoissonDAG.Constructions.PORS.ChainRefinedRow

namespace PoissonDAG.PORS.RankGates.RowUnrank
open GenericUnrank

private def config (t k w L : Nat) (bounds : 0<t ∧ Nat.log2 (t-1)+1 = L ∧
    L ≤ w ∧ t < 2^w ∧ t ≤ 2^L) : Config :=
  ⟨t, k, w, L, bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2.1, bounds.2.2.2.2⟩

def bucketSupport := config BucketRefined.p.t BucketRefined.p.k (width BucketRefined.p) 11
  (by decide +kernel)

def chainSupport := config ChainRefined.p.t ChainRefined.p.k (width ChainRefined.p) 5
  (by decide +kernel)

def chainSeparators := config (ChainRefined.p.E+ChainRefined.p.k-1) (ChainRefined.p.k-1)
  (width ChainRefined.p) 6 (by decide +kernel)

private theorem bucketBounds : ArithmeticBounds bucketSupport := by
  constructor <;> decide +kernel

private theorem chainBounds : ArithmeticBounds chainSupport := by
  constructor <;> decide +kernel

private theorem separatorBounds : ArithmeticBounds chainSeparators := by
  constructor <;> decide +kernel

theorem bucket_support {raw p a r} (seed : Seeded raw p)
    (word : Holds raw p (width BucketRefined.p) a r) (hr : r < BucketRefined.p.t.choose BucketRefined.p.k) :
    Builds raw p (unrank BucketRefined.p.t BucketRefined.p.k a) (fun q out =>
      List.Forall₂ (Holds raw q (width BucketRefined.p)) out
        (Colex.digits BucketRefined.p.t BucketRefined.p.k r).reverse) :=
  unrank_spec bucketSupport (binom_correct _ bucketBounds) seed word hr

theorem chain_support {raw p a r} (seed : Seeded raw p)
    (word : Holds raw p (width ChainRefined.p) a r) (hr : r < ChainRefined.p.t.choose ChainRefined.p.k) :
    Builds raw p (unrank ChainRefined.p.t ChainRefined.p.k a) (fun q out =>
      List.Forall₂ (Holds raw q (width ChainRefined.p)) out
        (Colex.digits ChainRefined.p.t ChainRefined.p.k r).reverse) :=
  unrank_spec chainSupport (binom_correct _ chainBounds) seed word hr

theorem chain_separators {raw p a r} (seed : Seeded raw p)
    (word : Holds raw p (width ChainRefined.p) a r)
    (hr : r < (ChainRefined.p.E+ChainRefined.p.k-1).choose (ChainRefined.p.k-1)) :
    Builds raw p (unrank (ChainRefined.p.E+ChainRefined.p.k-1) (ChainRefined.p.k-1) a) (fun q out =>
      List.Forall₂ (Holds raw q (width ChainRefined.p)) out
        (Colex.digits (ChainRefined.p.E+ChainRefined.p.k-1) (ChainRefined.p.k-1) r).reverse) :=
  unrank_spec chainSeparators (binom_correct _ separatorBounds) seed word hr

end PoissonDAG.PORS.RankGates.RowUnrank
