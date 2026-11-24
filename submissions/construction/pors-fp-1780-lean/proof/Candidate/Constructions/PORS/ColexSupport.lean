import Candidate.Constructions.PORS.ColexDigits
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Sort

namespace PoissonDAG.PORS.Colex

/-- The arithmetic colex decoder visits each k-subset once, so forced pruning
may count unordered supports directly instead of enumerating raw words. -/
def support (t k r : Nat) := (digits t k r).toFinset

theorem support_mem {t k r : Nat} (hr : r < t.choose k) :
    support t k r ∈ (Finset.range t).powersetCard k := by
  obtain ⟨_,below,sorted⟩ := digits_spec (Nat.le_refl t) hr
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro i hi
    exact Finset.mem_range.mpr (below _ (List.mem_toFinset.mp hi))
  · rw [support,List.toFinset_card_of_nodup sorted.nodup,digits_length]

theorem support_injective {t k x y : Nat} (hx : x < t.choose k) (hy : y < t.choose k)
    (h : support t k x = support t k y) : x = y := by
  apply digits_injective hx hy
  apply List.Pairwise.eq_of_mem_iff (digits_spec (Nat.le_refl t) hx).2.2
    (digits_spec (Nat.le_refl t) hy).2.2
  exact fun i => by simpa [support] using (Finset.ext_iff.mp h i)

def supportOfRank (t k : Nat) (r : Fin (t.choose k)) :
    {s // s ∈ (Finset.range t).powersetCard k} := ⟨support t k r, support_mem r.isLt⟩

theorem support_bijective (t k : Nat) : Function.Bijective (supportOfRank t k) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y h
    apply Fin.ext
    exact support_injective x.isLt y.isLt (congrArg Subtype.val h)
  · simp [Finset.card_powersetCard]

end PoissonDAG.PORS.Colex
