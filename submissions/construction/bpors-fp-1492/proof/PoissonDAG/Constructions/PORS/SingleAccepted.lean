import PoissonDAG.Constructions.PORS.ColexSupport
import PoissonDAG.Constructions.PORS.PrunedCount
import PoissonDAG.Constructions.PORS.LiteralReadout

namespace PoissonDAG.PORS.SingleAccepted
open PrunedCount

/-- Tree leaf IDs are the natural offsets read by the literal encoder. -/
def address (s : Shape) : Leaf s ↪ Nat :=
  (leafIndex s).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩

def leafSupport (s : Shape) (k raw : Nat) : Finset (Leaf s) :=
  Finset.univ.filter (fun l => address s l ∈ Colex.support s.leaves k raw)

theorem address_image (s : Shape) (k raw : Nat) (hr : raw < s.leaves.choose k) :
    (leafSupport s k raw).map (address s) = Colex.support s.leaves k raw := by
  ext n
  constructor
  · intro hn
    obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hn
    exact (Finset.mem_filter.mp hl).2
  · intro hn
    have hlt := Finset.mem_range.mp ((Finset.mem_powersetCard.mp (Colex.support_mem hr)).1 hn)
    let l := (leafIndex s).symm ⟨n,hlt⟩
    have he : address s l = n := congrArg Fin.val ((leafIndex s).apply_symm_apply _)
    exact Finset.mem_map.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm ▸ hn⟩,he⟩

private theorem address_bounded (s : Shape) (u : Finset (Leaf s)) :
    u.map (address s) ⊆ Finset.range s.leaves := by
  intro n hn
  obtain ⟨l,_,rfl⟩ := Finset.mem_map.mp hn
  exact Finset.mem_range.mpr ((leafIndex s) l).isLt

/-- Restrict the colex bijection to the pruned supports. The only circuit
hypothesis specifies the Boolean acceptance bit on a raw input, pointwise. -/
theorem length_of_gate {scheme : Scheme} (s : Shape) (k M : Nat)
    (fits : s.leaves.choose k ≤ 2^scheme.encoder.inputs)
    (gate : ∀ raw < 2^scheme.encoder.inputs,
      scheme.accept raw = true ↔ raw < s.leaves.choose k ∧ siblings s (leafSupport s k raw) ≤ M) :
    scheme.accepted.length =
      (((Finset.univ : Finset (Leaf s)).powersetCard k).filter (fun u => siblings s u ≤ M)).card := by
  classical
  have nodup : scheme.accepted.Nodup := List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup nodup]
  apply Finset.card_bij (fun raw _ => leafSupport s k raw)
  · intro raw h
    have hm := List.mem_filter.mp (List.mem_toFinset.mp h)
    have hr := List.mem_range.mp hm.1
    obtain ⟨hd, hM⟩ := (gate raw hr).mp hm.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,?_⟩,hM⟩
    have hw := (Finset.mem_powersetCard.mp (Colex.support_mem hd)).2
    rwa [← address_image s k raw hd, Finset.card_map] at hw
  · intro a ha b hb hab
    have am := List.mem_filter.mp (List.mem_toFinset.mp ha)
    have bm := List.mem_filter.mp (List.mem_toFinset.mp hb)
    have ra := ((gate a (List.mem_range.mp am.1)).mp am.2).1
    have rb := ((gate b (List.mem_range.mp bm.1)).mp bm.2).1
    apply Colex.support_injective ra rb
    rw [← address_image s k a ra, ← address_image s k b rb, hab]
  · intro u hu
    obtain ⟨hcard,hM⟩ := Finset.mem_filter.mp hu
    have w := (Finset.mem_powersetCard.mp hcard).2
    have hdom : u.map (address s) ∈ (Finset.range s.leaves).powersetCard k :=
      Finset.mem_powersetCard.mpr ⟨address_bounded s u, by simpa using w⟩
    obtain ⟨raw, he⟩ := (Colex.support_bijective s.leaves k).2 ⟨_,hdom⟩
    have eqs : leafSupport s k raw = u := by
      apply Finset.map_injective (address s)
      rw [address_image s k raw raw.isLt]
      exact congrArg Subtype.val he
    have hr := raw.isLt.trans_le fits
    exact ⟨raw,List.mem_toFinset.mpr (List.mem_filter.mpr
      ⟨List.mem_range.mpr hr, (gate raw hr).mpr ⟨raw.isLt,eqs.symm ▸ hM⟩⟩),eqs⟩

private theorem row_capacity (row : Row) (ht : 0<row.t)
    (cap : Nat.fast_choose row.t row.k ≤ 2^row.r) :
    (Literal.shape row.t).leaves.choose row.k ≤ 2^row.r := by
  rwa [Literal.shape_card _ ht, Nat.choose_eq_fast_choose]

private theorem specialize (scheme : Scheme) (s : Shape) (k M bits total : Nat)
    (widthEq : scheme.encoder.inputs = bits) (fits : s.leaves.choose k ≤ 2^bits)
    (count : (((Finset.univ : Finset (Leaf s)).powersetCard k).filter
      (fun u => siblings s u ≤ M)).card = total)
    (gate : ∀ raw < 2^bits, scheme.accept raw = true ↔
      raw < s.leaves.choose k ∧ siblings s (leafSupport s k raw) ≤ M) :
    scheme.accepted.length = total :=
  (length_of_gate (scheme := scheme) s k M (by simpa only [widthEq] using fits)
    (by simpa only [widthEq] using gate)).trans count

attribute [local irreducible] Literal.scheme Scheme.accepted Literal.shape

/-- The pointwise acceptance bit identifies the protected raw-word count. -/
theorem single_count
    (gate : ∀ raw < 2^SingleRefined.p.r,
      let s := Literal.shape SingleRefined.p.t
      Literal.single.accept raw = true ↔ raw < s.leaves.choose SingleRefined.p.k ∧
        siblings s (leafSupport s SingleRefined.p.k raw) ≤ SingleRefined.p.M) :
    Literal.single.accepted.length = SingleRefined.p.acceptedWords :=
  specialize Literal.single (Literal.shape SingleRefined.p.t) SingleRefined.p.k
    SingleRefined.p.M SingleRefined.p.r SingleRefined.p.acceptedWords
    (Literal.literal_inputs SingleRefined.p) (row_capacity SingleRefined.p
      (by decide) (by decide +kernel)) single_support_count gate

end PoissonDAG.PORS.SingleAccepted
