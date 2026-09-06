import Erdos.Problem1144.HarperCandidateCovarianceCosineEnvelope
import Erdos.Problem1144.HarperCandidateCovarianceHalfDensityMoments

open Finset MeasureTheory
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Exact decomposition of the half-density exponent. In particular,
the two negative second harmonics have not been discarded. -/
theorem candidate_halfDensityPair_exponent_eq_cosinePrefixes (y : ℕ) (t v : ℝ) :
    (∑ p ∈ (y + 1).primesBelow, candidateHalfDensityPairPrimeExponent p t v) =
      candidatePrimeCosinePrefix y 0 / 2 - candidatePrimeCosinePrefix y (2 * t) / 4 -
        candidatePrimeCosinePrefix y (2 * v) / 4 +
        candidatePrimeCosinePrefix y (t - v) / 2 +
        candidatePrimeCosinePrefix y (t + v) / 2 := by
  unfold candidateHalfDensityPairPrimeExponent candidatePrimeCosinePrefix
  simp only [zero_mul, Real.cos_zero, Finset.sum_div,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- A logarithmic envelope for the literal signed exponent on a retained
annulus. The constants and initial index are absolute; the two singular
interaction channels remain separately clipped at the exact Euler cutoff. -/
theorem candidate_exists_halfDensityPair_exponent_gapEnvelope_bound :
    ∃ C > 0, ∃ J : ℕ, ∀ start stop : ℕ, J ≤ start → start ≤ stop →
      ∀ h M t v : ℝ, 0 < h → h ≤ |t| → h ≤ |v| → |t| ≤ M → |v| ≤ M →
        2 * M ≤ candidateCovarianceHeightWindow start →
        (∑ p ∈ (Problem520.harperBlockEndpoint stop + 1).primesBelow,
          candidateHalfDensityPairPrimeExponent p t v) ≤
          2 * C + Real.log (Real.log (Problem520.harperBlockEndpoint stop : ℝ)) / 2 +
            Real.log (max (Real.log (Problem520.harperBlockEndpoint start : ℝ)) (1 / h)) / 2 +
            Real.log (candidateCovarianceGapEnvelope start stop |t - v|) / 2 +
            Real.log (candidateCovarianceGapEnvelope start stop |t + v|) / 2 := by
  obtain ⟨C, hC, J, hcos⟩ := candidate_exists_primeCosinePrefix_gapEnvelope_bound
  refine ⟨C, hC, J, ?_⟩
  intro start stop hstart hss h M t v hh hht hhv htM hvM hwin
  have hL : 0 < Real.log (Problem520.harperBlockEndpoint stop : ℝ) :=
    zero_lt_one.trans_le (Problem520.one_le_log_harperBlockEndpoint stop)
  have hwindow : 0 ≤ candidateCovarianceHeightWindow start := by
    unfold candidateCovarianceHeightWindow
    positivity
  have h0 := hcos start stop hstart hss 0 (by simpa using hwindow)
  have ht := hcos start stop hstart hss (2 * t) (by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  have hv := hcos start stop hstart hss (2 * v) (by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  have hd := hcos start stop hstart hss (t - v)
    ((abs_sub t v).trans (by linarith))
  have hs := hcos start stop hstart hss (t + v)
    ((abs_add_le t v).trans (by linarith))
  have hg0 : Real.log (candidateCovarianceGapEnvelope start stop |(0 : ℝ)|) ≤
      Real.log (Real.log (Problem520.harperBlockEndpoint stop : ℝ)) :=
    Real.log_le_log (zero_lt_one.trans_le (candidate_one_le_gapEnvelope _ _ _))
      (candidate_gapEnvelope_le_top _ _ _)
  have hgt : Real.log (candidateCovarianceGapEnvelope start stop |2 * t|) ≤
      Real.log (max (Real.log (Problem520.harperBlockEndpoint start : ℝ)) (1 / h)) :=
    Real.log_le_log (zero_lt_one.trans_le (candidate_one_le_gapEnvelope _ _ _))
      (candidate_gapEnvelope_two_height_le start stop h t hh hht)
  have hgv : Real.log (candidateCovarianceGapEnvelope start stop |2 * v|) ≤
      Real.log (max (Real.log (Problem520.harperBlockEndpoint start : ℝ)) (1 / h)) :=
    Real.log_le_log (zero_lt_one.trans_le (candidate_one_le_gapEnvelope _ _ _))
      (candidate_gapEnvelope_two_height_le start stop h v hh hhv)
  rw [candidate_halfDensityPair_exponent_eq_cosinePrefixes]
  have htlo := (abs_le.mp ht).1
  have hvlo := (abs_le.mp hv).1
  have h0hi := (abs_le.mp h0).2
  have hdhi := (abs_le.mp hd).2
  have hshi := (abs_le.mp hs).2
  linarith

private theorem exp_half_log_eq_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- Actual unscreened Euler half-density moment on the retained annulus.
This is the two-channel square-root bound used for the far-pair kernel
integral; its constant is independent of every cutoff and height. -/
theorem candidate_exists_halfDensityPair_gapEnvelope_moment_bound :
    ∃ C > 0, ∃ J : ℕ, ∀ start stop : ℕ, J ≤ start → start ≤ stop →
      ∀ h M t v : ℝ, 0 < h → h ≤ |t| → h ≤ |v| → |t| ≤ M → |v| ≤ M →
        2 * M ≤ candidateCovarianceHeightWindow start →
        (∫ ω, Real.sqrt (Problem520.harperEulerDensity
          (Problem520.harperBlockEndpoint stop) ω t) *
          Real.sqrt (Problem520.harperEulerDensity
            (Problem520.harperBlockEndpoint stop) ω v) ∂Problem520.μ) ≤
          C * Real.sqrt (Real.log (Problem520.harperBlockEndpoint stop : ℝ)) *
            Real.sqrt (max (Real.log (Problem520.harperBlockEndpoint start : ℝ)) (1 / h)) *
            Real.sqrt (candidateCovarianceGapEnvelope start stop |t - v|) *
            Real.sqrt (candidateCovarianceGapEnvelope start stop |t + v|) := by
  obtain ⟨D, hD, hm⟩ := candidate_exists_halfDensity_pair_moment_le
  obtain ⟨C, hC, J, he⟩ := candidate_exists_halfDensityPair_exponent_gapEnvelope_bound
  refine ⟨D * Real.exp (2 * C), by positivity, J, ?_⟩
  intro start stop hstart hss h M t v hh hht hhv htM hvM hwin
  have hE := Real.exp_le_exp.mpr (he start stop hstart hss h M t v hh hht hhv htM hvM hwin)
  have hL : 0 < Real.log (Problem520.harperBlockEndpoint stop : ℝ) :=
    zero_lt_one.trans_le (Problem520.one_le_log_harperBlockEndpoint stop)
  have hA : 0 < max (Real.log (Problem520.harperBlockEndpoint start : ℝ)) (1 / h) :=
    (zero_lt_one.trans_le (Problem520.one_le_log_harperBlockEndpoint start)).trans_le
      (le_max_left _ _)
  have hG (x : ℝ) : 0 < candidateCovarianceGapEnvelope start stop x :=
    zero_lt_one.trans_le (candidate_one_le_gapEnvelope _ _ _)
  simp only [Real.exp_add, exp_half_log_eq_sqrt hL, exp_half_log_eq_sqrt hA,
    exp_half_log_eq_sqrt (hG |t - v|), exp_half_log_eq_sqrt (hG |t + v|)] at hE
  exact (hm (Problem520.harperBlockEndpoint stop) t v).trans
    ((mul_le_mul_of_nonneg_left hE hD.le).trans_eq (by ring))

end
end Erdos.Problem1144
