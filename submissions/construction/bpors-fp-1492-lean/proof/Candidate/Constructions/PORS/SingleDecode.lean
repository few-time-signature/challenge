import Candidate.Constructions.PORS.RawInput
import Candidate.Constructions.PORS.UnrankSemantics
import Candidate.Constructions.PORS.LiteralMaskLeaf

namespace PoissonDAG.PORS.RankGates

private theorem zero_depths {raw p} (s : Seeded raw p) (w k : Nat) :
    List.Forall₂ (Holds raw p w) (List.replicate k (lit w 0)) (List.replicate k 0) := by
  induction k with
  | zero => exact .nil
  | succ k ih =>
    exact List.Forall₂.cons (by simpa only [Nat.zero_mod] using holds_literal s w 0) ih

/-- All literals used by the first row have a single coordinate. Its rank
gate checks the support range, its bucket is zero, its leaves are the colex
digits in increasing order, and every depth is zero. -/
def SingleDecodeSpec (raw : Nat) (q : Array Gate) (result : Nat × List Digits) : Prop :=
  let row := SingleRefined.p
  let w := width row
  ∃ d : Digits, result.2 = [d] ∧ HasBit raw q result.1 (decide (raw < row.supports)) ∧
    Holds raw q w d.bucket 0 ∧
    List.Forall₂ (Holds raw q w) d.leaves (Colex.digits row.t row.k (raw%row.supports)).reverse ∧
    List.Forall₂ (Holds raw q w) d.depths (List.replicate row.k 0)

/-- Pairing a decoded support with its zero depths gives exactly the input
relation of the literal leaf-mask builder. -/
theorem decoded_leafDigits {raw p w} {leaves depths : List Word} {xs : List Nat}
    (hl : List.Forall₂ (Holds raw p w) leaves xs)
    (hd : List.Forall₂ (Holds raw p w) depths (List.replicate xs.length 0)) :
    LiteralMaskSemantics.LeafDigits raw p w (leaves.zip depths) xs := by
  induction hl generalizing depths with
  | nil => exact .nil
  | cons hval htail ih =>
    cases depths with
    | nil => cases hd
    | cons d ds =>
      obtain ⟨hz, hds⟩ := List.forall₂_cons.mp hd
      exact .cons ⟨⟨hval.size, hval.valid, hval.value_eq⟩, ⟨hz.size, hz.valid, hz.value_eq⟩⟩
        (ih hds)

theorem SingleDecodeSpec.mask_inputs {raw q result} (h : SingleDecodeSpec raw q result) :
    let row := SingleRefined.p
    ∃ d : Digits, result.2 = [d] ∧ HasBit raw q result.1 (decide (raw < row.supports)) ∧
      LiteralMaskSemantics.Number raw q (width row) d.bucket 0 ∧
      LiteralMaskSemantics.LeafDigits raw q (width row) (d.leaves.zip d.depths)
        (Colex.digits row.t row.k (raw%row.supports)).reverse := by
  obtain ⟨d, he, hv, hb, hl, hd⟩ := h
  exact ⟨d, he, hv, ⟨hb.size, hb.valid, hb.value_eq⟩,
    decoded_leafDigits hl (by simpa using hd)⟩

theorem decode_single_of_unrank {raw p} (s : Seeded raw p) (hr : raw < 2^SingleRefined.p.r)
    (unrank_spec : ∀ (q : Array Gate) (rank : Word) (r : Nat), Seeded raw q →
      Holds raw q (width SingleRefined.p) rank r → r < SingleRefined.p.supports →
      Builds raw q (unrank SingleRefined.p.t SingleRefined.p.k rank) (fun v leaves =>
        List.Forall₂ (Holds raw v (width SingleRefined.p)) leaves
          (Colex.digits SingleRefined.p.t SingleRefined.p.k r).reverse)) :
    Builds raw p (decode SingleRefined.p) (SingleDecodeSpec raw) := by
  let row := SingleRefined.p
  let w := width row
  have hw : row.r ≤ w := by
    change SingleRefined.p.r ≤ width SingleRefined.p
    rw [RankBounds.single_width.1]
    decide
  have hpos : 0 < row.supports := RankBounds.single_rank_divisor_guard.1
  have hguard : 2*row.supports ≤ 2^w := RankBounds.single_rank_divisor_guard.2
  rw [decode_single_program]
  have load : Builds raw p (loadRaw row.r w) (fun q word => Holds raw q w word raw) := by
    have h := loadRaw_nat s row.r w hw
    rw [Nat.mod_eq_of_lt (show raw < 2^row.r from hr)] at h
    exact h
  refine load.bind fun q word e hword => ?_
  refine (divmod_nat (s.mono e) hword row.supports hpos hguard).bind ?_
  intro q' pair f hpair
  rcases pair with ⟨quot, rank⟩
  obtain ⟨hq, hrank⟩ := hpair
  have s' := s.mono (e.trans f)
  refine (unrank_spec q' rank (raw % row.supports) s' hrank (Nat.mod_lt _ hpos)).bind ?_
  intro q'' leaves g hleaves
  have s'' := s'.mono g
  have hquot := hq.mono g
  have hz : Holds raw q'' w (lit w 0) 0 := by
    simpa only [Nat.zero_mod] using holds_literal s'' w 0
  have validGate := LiteralMaskSemantics.eqw_number s''
    (show LiteralMaskSemantics.Number raw q'' w quot (raw/row.supports) from
      ⟨hquot.size, hquot.valid, hquot.value_eq⟩)
    (show LiteralMaskSemantics.Number raw q'' w (lit w 0) 0 from
      ⟨hz.size, hz.valid, hz.value_eq⟩)
  refine validGate.bind fun final valid h hv => ?_
  apply builds_pure
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.div_eq_zero_iff_lt hpos] using hv
  · simpa only [hq.size] using hz.mono h
  · exact List.Forall₂.imp (fun _ _ hl => hl.mono h) hleaves
  · exact zero_depths (s''.mono h) w row.k

theorem decode_single {raw p} (s : Seeded raw p) (hr : raw < 2^SingleRefined.p.r) :
    Builds raw p (decode SingleRefined.p) (SingleDecodeSpec raw) := by
  apply decode_single_of_unrank s hr
  intro q rank r seed hword hrank
  apply SingleUnrank.unrank_spec seed hword
  change r < SingleRefined.p.t.choose SingleRefined.p.k
  rw [Nat.choose_eq_fast_choose]
  exact hrank

end PoissonDAG.PORS.RankGates
