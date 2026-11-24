import PoissonDAG.Constructions.PORS.Literal
import Candidate.Constructions.GRSCC.Covering
import PoissonDAG.Probability.Counting
import Candidate.Probability.SchemeExperiment
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup

namespace PoissonDAG.PORS.SingleCover

/-- The actual private source vertices disclosed by an output. The public
root is excluded because the protected covering experiment grants it for free. -/
def sources (s : Scheme) (raw : Nat) : Finset Nat :=
  (Finset.range s.graph.length).filter (fun v =>
    s.graph[v]? = some .source ∧ s.graph.length - 1 ≠ v ∧ get (s.frontier raw) v = true)

/-- The unrestricted closure can only supply a private source that occurred
in a history disclosure. The proof applies the singleton backward barrier. -/
theorem covered_source_has_supplier (s : Scheme) (history : List Nat) (target v : Nat)
    (arity : s.encoder.outputs.length = 1 + 2 * s.graph.length)
    (hv : v ∈ sources s target) (hc : s.covered history target = true) :
    ∃ raw ∈ history, v ∈ sources s raw := by
  obtain ⟨hindex, hsource, hroot, hfront⟩ := Finset.mem_filter.mp hv
  have barrier : GRSCC.BackwardBarrier s.graph (fun i => i = v) := by
    intro node i hm hi
    subst i
    have hn := List.mk_mem_zipIdx_iff_getElem?.mp hm
    have he : node = .source := Option.some.inj (hn.symm.trans hsource)
    subst node
    trivial
  obtain ⟨raw, hr, ha⟩ := GRSCC.covered_requires_barrier_hit s history target v
    arity barrier hroot (Finset.mem_range.mp hindex) rfl hfront hc
  obtain ⟨j, hj, hjv⟩ := GRSCC.not_avoids_witness ha
  exact ⟨raw, hr, Finset.mem_filter.mpr ⟨hindex, hsource, hroot, hj ▸ hjv⟩⟩

/-- The two decoder properties used by the counting argument. Only accepted
raw words enter either statement. -/
structure SourceCode (s : Scheme) (k : Nat) : Prop where
  weight : ∀ raw ∈ s.accepted, (sources s raw).card = k
  injective : ∀ x ∈ s.accepted, ∀ y ∈ s.accepted, sources s x = sources s y → x = y

def hits (s : Scheme) (history : List Nat) : Finset (Fin s.accepted.length) :=
  Finset.univ.filter (fun i => s.covered history s.accepted[i] = true)

/-- For a fixed, with-replacement accepted history the map from a covered
target to its disclosed sources embeds the targets into the k-subsets of the
pooled sources. Repeated suppliers only decrease the size of this pool. -/
theorem fixed_history_count (s : Scheme) (k q : Nat)
    (arity : s.encoder.outputs.length = 1 + 2 * s.graph.length) (code : SourceCode s k)
    (sample : Fin q → Fin s.accepted.length) :
    (hits s (indexHistory s.accepted sample)).card ≤ (k * q).choose k := by
  classical
  let history := indexHistory s.accepted sample
  let support := fun i : Fin s.accepted.length => sources s s.accepted[i]
  let pool := Finset.univ.biUnion (fun i : Fin q => support (sample i))
  have pool_card : pool.card ≤ k * q := by
    have hb := Finset.card_biUnion_le_card_mul Finset.univ
      (fun i : Fin q => support (sample i)) k
      (fun i _ => (code.weight _ (List.getElem_mem (sample i).isLt)).le)
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.mul_comm q k] using hb
  have image_in : Set.MapsTo support (hits s history) (pool.powersetCard k) := by
    intro target ht
    have covered := (Finset.mem_filter.mp ht).2
    refine Finset.mem_powersetCard.mpr ⟨?_, code.weight _ (List.getElem_mem target.isLt)⟩
    intro v hv
    obtain ⟨raw, hr, hs⟩ := covered_source_has_supplier s history s.accepted[target] v
      arity hv covered
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hs⟩
  have unique : Function.Injective support := by
    intro i j he
    have hn : s.accepted.Nodup := List.Nodup.filter _ List.nodup_range
    apply hn.injective_get
    exact code.injective _ (List.getElem_mem i.isLt) _ (List.getElem_mem j.isLt) he
  calc
    _ ≤ (pool.powersetCard k).card := Finset.card_le_card_of_injOn support image_in unique.injOn
    _ = pool.card.choose k := Finset.card_powersetCard _ _
    _ ≤ _ := Nat.choose_le_choose _ pool_card

/-- Cancel the history normalizer after a uniform pointwise target count.
The denominator that survives is the size of the raw target space. -/
theorem coefficient_of_count (s : Scheme) (q : Nat) (bound : ℚ)
    (positive : 0 < s.accepted.length)
    (count : ∀ sample : Fin q → Fin s.accepted.length,
      ((hits s (indexHistory s.accepted sample)).card : ℚ) ≤ bound) :
    s.coverCoefficient q ≤ bound / 2 ^ s.encoder.inputs := by
  classical
  have ha : (s.accepted.length : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt positive
  have hr : (2 : ℚ) ^ s.encoder.inputs ≠ 0 := by positivity
  have havg : s.acceptedCoverProbability q ≤
      (∑ _ : Fin q → Fin s.accepted.length, bound) / (s.accepted.length : ℚ) ^ (q+1) := by
    unfold Scheme.acceptedCoverProbability
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply Finset.sum_le_sum
    intro sample _
    rw [Finset.sum_boole]
    exact count sample
  rw [s.coverCoefficient_eq_acceptedProbability positive]
  apply (mul_le_mul_of_nonneg_left havg (tau_nonneg s)).trans
  apply le_of_eq
  simp only [Scheme.tau, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, pow_succ]
  field_simp [ha, hr] <;> ring

/-- Both caps hold for the same protected experiment. -/
theorem coefficient_le (s : Scheme) (k q : Nat)
    (arity : s.encoder.outputs.length = 1 + 2 * s.graph.length)
    (positive : 0 < s.accepted.length) (code : SourceCode s k) :
    s.coverCoefficient q ≤ min ((s.accepted.length : ℚ) / 2 ^ s.encoder.inputs)
      (((k * q).choose k : ℚ) / 2 ^ s.encoder.inputs) := by
  apply le_min
  · apply coefficient_of_count s q _ positive
    intro sample
    have h := Finset.card_le_univ (hits s (indexHistory s.accepted sample))
    exact_mod_cast (show (hits s (indexHistory s.accepted sample)).card ≤ s.accepted.length by
      simpa only [Fintype.card_fin] using h)
  · apply coefficient_of_count s q _ positive
    intro sample
    exact_mod_cast fixed_history_count s k q arity code sample

open SingleRefined

private theorem single_child (q : Nat) :
    p.child q = min 1 (((9*q).choose 9 : ℚ) / p.supports) := by
  have hdenN : 1 ≤ p.supports := by decide +kernel
  have hden : (1 : ℚ) ≤ p.supports := by exact_mod_cast hdenN
  by_cases h0 : q = 0
  · subst q
    simp [Row.child, Nat.choose_eq_zero_of_lt (by decide : 0 < 9)]
  by_cases h1 : q = 1
  · subst q
    have hsmall : (1 : ℚ) / p.supports ≤ 1 :=
      (div_le_one (lt_of_lt_of_le (by norm_num) hden)).mpr hden
    simpa [Row.child, show p.depthCount = 1 from rfl] using hsmall
  · simp only [Row.child, if_neg h0, if_neg h1, show p.k = 9 from rfl,
      Nat.choose_eq_fast_choose]

/-- The single row has one coordinate, one bucket and one depth. Its raw
envelope is exactly the lesser of the accepted-word cap and the k-subset cap,
each divided by the full raw space. This includes q = 0 and q = 1. -/
theorem single_rawEnvelope (q : Nat) :
    p.rawEnvelope q = min ((p.acceptedWords : ℚ) / 2 ^ p.r)
      (((9*q).choose 9 : ℚ) / 2 ^ p.r) := by
  have hdom : p.domain = p.supports := by
    simp only [Row.domain, show p.buckets = 1 from rfl, show p.depthCount = 1 from rfl,
      show p.K = 1 from rfl, one_mul, mul_one, pow_one]
  have hposN : 0 < p.supports := by decide +kernel
  have hboundN : p.acceptedWords ≤ p.supports := by decide +kernel
  have hpos : (0 : ℚ) < p.supports := by exact_mod_cast hposN
  have hbound : (p.acceptedWords : ℚ) ≤ p.supports := by exact_mod_cast hboundN
  have hr : 0 < (2 : ℚ) ^ p.r := by positivity
  have cancel : ((p.supports : ℚ) / 2 ^ p.r) * (((9*q).choose 9 : ℚ) / p.supports) =
      ((9*q).choose 9 : ℚ) / 2 ^ p.r := by field_simp [hpos.ne', hr.ne'] <;> ring
  simp only [Row.rawEnvelope, Row.bucketEnvelope, show p.b = 0 from rfl, if_true,
    show p.K = 1 from rfl, pow_one, hdom, single_child,
    mul_min_of_nonneg _ _ (div_nonneg hpos.le hr.le), mul_one, cancel, ← min_assoc,
    min_eq_left (div_le_div_of_nonneg_right hbound hr.le)]

theorem historicalCount_of_shape (s : Scheme)
    (arity : s.encoder.outputs.length = 1 + 2 * s.graph.length)
    (bits : s.encoder.inputs = p.r) (count : s.accepted.length = p.acceptedWords)
    (code : SourceCode s 9) (q : Nat) : s.coverCoefficient q ≤ p.rawEnvelope q := by
  have hp : 0 < s.accepted.length := by rw [count]; exact (by decide : 0 < p.acceptedWords)
  have bound := coefficient_le s 9 q arity hp code
  rw [single_rawEnvelope]
  simpa only [count, bits] using bound

end PoissonDAG.PORS.SingleCover
