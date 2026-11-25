import PoissonDAG.Bounds.OneHistory
import PoissonDAG.Bounds.CostFacts
import PoissonDAG.Probability.PoissonCuts

/-! # The 99-byte universal lower bound

This result targets the original `UniversalLowerBound` over the executable
scheme. The verification budget remains an expectation bound throughout.
-/

namespace PoissonDAG

theorem chainCount_five_bound : chainCount (2^24) 5 ≤ 2^96 := by
  norm_num [chainCount, Finset.sum_range_succ,
    Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem chainCount_six_bound : chainCount (2^24) 6 < 2^115 := by
  norm_num [chainCount, Finset.sum_range_succ,
    Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem openingLowerBound : UniversalLowerBound 99 := by
  intro s he
  have hw := he.1
  have hc := he.2.1
  have hnodes := eligible_generation_bound he
  have ht := tau_pos hw
  have hwords := s.maxWords_pos hw hc
  have hdpos : 0 < chainCount s.graph.length s.maxWords := chainCount_pos hwords
  have hdposQ : (0 : ℚ) < (chainCount s.graph.length s.maxWords : Nat) := by
    exact_mod_cast hdpos
  have hlow := s.oneHistory_lower hw hc
  have hupper := eligible_one_history_upper he
  have hproduct : s.tau ≤ s.coverCoefficient 1 *
      (2 * (chainCount s.graph.length s.maxWords : ℚ)) :=
    (div_le_iff₀ (by positivity)).mp hlow
  by_contra hsize
  have hsize' : s.size ≤ 98 := by omega
  have hsize_eq : s.size = (s.counterBits+7)/8 + 16*s.maxWords := rfl
  have hL : s.maxWords ≤ 6 := by omega
  by_cases hL5 : s.maxWords ≤ 5
  · have hD : chainCount s.graph.length s.maxWords ≤ 2^96 :=
      (chainCount_mono_nodes hnodes _).trans
        ((chainCount_mono_words _ hL5).trans chainCount_five_bound)
    have hDQ : (chainCount s.graph.length s.maxWords : ℚ) ≤ 2^96 := by exact_mod_cast hD
    have hf := eligible_acceptance_floor he
    have hp := mul_lt_mul_of_pos_right hupper (by positivity :
      (0 : ℚ) < 2*(chainCount s.graph.length s.maxWords : ℚ))
    have hb : 3*((1 : ℚ)/2^128)*(2*(chainCount s.graph.length s.maxWords : ℚ)) ≤
        3*((1 : ℚ)/2^128)*(2*2^96) := by gcongr
    norm_num at hb hp hf
    linarith
  · have hL6 : s.maxWords = 6 := by omega
    have hcounter : s.counterBits ≤ 16 := by omega
    have hf := counter_small_acceptance_floor hw hcounter he.2.2.1
    have hD : chainCount s.graph.length s.maxWords < 2^115 := by
      rw [hL6]
      exact (chainCount_mono_nodes hnodes _).trans_lt chainCount_six_bound
    have hDQ : (chainCount s.graph.length s.maxWords : ℚ) < 2^115 := by exact_mod_cast hD
    have hp := mul_lt_mul_of_pos_right hupper (by positivity :
      (0 : ℚ) < 2*(chainCount s.graph.length s.maxWords : ℚ))
    have hb : 3*((1 : ℚ)/2^128)*(2*(chainCount s.graph.length s.maxWords : ℚ)) <
        3*((1 : ℚ)/2^128)*(2*2^115) := by gcongr
    norm_num at hb hp hf
    linarith

end PoissonDAG
