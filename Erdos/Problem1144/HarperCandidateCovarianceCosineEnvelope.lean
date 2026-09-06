import Erdos.Problem1144.HarperCandidateCovarianceGapEnvelope

open Finset
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The full reciprocal-prime cosine sum at the literal Euler cutoff. -/
def candidatePrimeCosinePrefix (y : ℕ) (τ : ℝ) : ℝ :=
  ∑ p ∈ (y + 1).primesBelow, Real.cos (τ * Real.log (p : ℝ)) / p

theorem candidate_abs_primeCosinePrefix_le_reciprocalPrefix (y : ℕ) (τ : ℝ) :
    |candidatePrimeCosinePrefix y τ| ≤ Problem520.primeReciprocalPrefix y := by
  unfold candidatePrimeCosinePrefix Problem520.primeReciprocalPrefix
  calc
    _ ≤ ∑ p ∈ (y + 1).primesBelow,
        |Real.cos (τ * Real.log (p : ℝ)) / p| := abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun p hp => by
      rw [abs_div, show |(p : ℝ)| = (p : ℝ) from abs_of_nonneg (Nat.cast_nonneg p)]
      simpa only [one_div] using div_le_div_of_nonneg_right
        (Real.abs_cos_le_one (τ * Real.log (p : ℝ))) (Nat.cast_nonneg p)

/-- Every clipped logarithmic gap scale is at least one. In particular,
its logarithm and square root can be used without exceptional zero cases. -/
theorem candidate_one_le_gapEnvelope (start stop : ℕ) (g : ℝ) :
    1 ≤ candidateCovarianceGapEnvelope start stop g := by
  exact le_min (Problem520.one_le_log_harperBlockEndpoint stop)
    ((Problem520.one_le_log_harperBlockEndpoint start).trans (le_max_left _ _))

/-- Both self-frequency channels on an annulus have a bound independent
of the terminal Euler cutoff. -/
theorem candidate_gapEnvelope_two_height_le (start stop : ℕ) (h t : ℝ)
    (hh : 0 < h) (ht : h ≤ |t|) :
    candidateCovarianceGapEnvelope start stop |2 * t| ≤
      max (Real.log (Problem520.harperBlockEndpoint start : ℝ)) (1 / h) := by
  apply (min_le_right _ _).trans
  apply max_le_max le_rfl
  have hden : 2 * h ≤ max |2 * t|
      (Problem520.invLog (Problem520.harperBlockEndpoint stop)) := by
    apply le_trans _ (le_max_left _ _)
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  calc
    2 / max |2 * t| (Problem520.invLog (Problem520.harperBlockEndpoint stop)) ≤
        2 / (2 * h) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = 1 / h := by ring

/-- Uniform full-prime cancellation in the growing height window. The
same clipped gap envelope used for the ordered moments controls the
absolute cosine sum, including zero and microscopic frequencies. -/
theorem candidate_exists_primeCosinePrefix_gapEnvelope_bound :
    ∃ C > 0, ∃ J : ℕ, ∀ start stop : ℕ, J ≤ start → start ≤ stop →
      ∀ τ : ℝ, |τ| ≤ candidateCovarianceHeightWindow start →
        |candidatePrimeCosinePrefix (Problem520.harperBlockEndpoint stop) τ| ≤
          C + Real.log (candidateCovarianceGapEnvelope start stop |τ|) := by
  obtain ⟨D, hD, J, htail⟩ := candidate_exists_growingHeight_primeTail_bound
  let C₀ : ℝ := 1 - Real.log (Real.log 2) +
    2 * (Real.log 4 + 4) / Real.log 2
  have hprefix (j : ℕ) (τ : ℝ) :
      |candidatePrimeCosinePrefix (Problem520.harperBlockEndpoint j) τ| ≤
        |C₀| + Real.log (Real.log (Problem520.harperBlockEndpoint j : ℝ)) := by
    have hy : 2 ≤ Problem520.harperBlockEndpoint j :=
      (by norm_num : 2 ≤ 16).trans (Problem520.harperBlockEndpoint_ge_sixteen j)
    have h := Problem520.primeReciprocalPrefix_le_logLog_add_const hy
    change Problem520.primeReciprocalPrefix (Problem520.harperBlockEndpoint j) ≤
      Real.log (Real.log (Problem520.harperBlockEndpoint j : ℝ)) + C₀ at h
    have ha := candidate_abs_primeCosinePrefix_le_reciprocalPrefix
      (Problem520.harperBlockEndpoint j) τ
    linarith [le_abs_self C₀]
  refine ⟨|C₀| + 4 + D, by positivity, J, ?_⟩
  intro start stop hstart hss τ hτwin
  let j := candidateCovarianceGapCutoff start stop |τ|
  obtain ⟨hsj, hjs, hfit, _⟩ := candidate_covarianceGapCutoff_spec start stop hss |τ|
  have hlogj : 0 < Real.log (Problem520.harperBlockEndpoint j : ℝ) :=
    zero_lt_one.trans_le (Problem520.one_le_log_harperBlockEndpoint j)
  have hlog : Real.log (Real.log (Problem520.harperBlockEndpoint j : ℝ)) ≤
      Real.log (candidateCovarianceGapEnvelope start stop |τ|) :=
    Real.log_le_log hlogj (candidate_log_gapCutoff_le_envelope start stop hss |τ|)
  by_cases heq : j = stop
  · have hp := hprefix j τ
    rw [heq] at hp hlog
    linarith
  · have hjlt : j < stop := lt_of_le_of_ne hjs heq
    have hellfit : Problem520.invLog (Problem520.harperBlockEndpoint j) ≤ |τ| := hfit hjlt
    have hτpos : 0 < |τ| :=
      (Problem520.invLog_harperBlockEndpoint_pos j).trans_le hellfit
    have hτne : τ ≠ 0 := abs_pos.mp hτpos
    have hBj : Problem520.harperBlockEndpoint j ≤ Problem520.harperBlockEndpoint stop :=
      Problem520.monotone_harperBlockEndpoint hjs
    have ht := htail j (Problem520.harperBlockEndpoint stop) (hstart.trans hsj) hBj τ hτne
      (hτwin.trans (candidateCovarianceHeightWindow_monotone hsj))
    have hell0 := (Problem520.invLog_harperBlockEndpoint_pos j).le
    have hell1 := Problem520.invLog_harperBlockEndpoint_le_one j
    have ht₁ : (4 / |τ|) * Problem520.invLog (Problem520.harperBlockEndpoint j) ≤ 4 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hτpos]
      nlinarith
    have ht₂ : D * Problem520.invLog (Problem520.harperBlockEndpoint j) ^ 2 ≤ D := by
      nlinarith [mul_nonneg hD.le (show
        0 ≤ 1 - Problem520.invLog (Problem520.harperBlockEndpoint j) ^ 2 by nlinarith)]
    have hsplit : candidatePrimeCosinePrefix (Problem520.harperBlockEndpoint stop) τ =
        candidatePrimeCosinePrefix (Problem520.harperBlockEndpoint j) τ +
          ∑ p ∈ (Ioc (Problem520.harperBlockEndpoint j)
            (Problem520.harperBlockEndpoint stop)).filter Nat.Prime,
            Real.cos (τ * Real.log (p : ℝ)) / p := by
      unfold candidatePrimeCosinePrefix
      rw [Problem520.primesBelow_succ_eq_union_freshPrimes hBj,
        Finset.sum_union (Problem520.primesBelow_succ_disjoint_freshPrimes _ _),
        Problem520.freshPrimes_eq_Ioc_filter_prime]
    rw [hsplit]
    have ha := abs_add_le
      (candidatePrimeCosinePrefix (Problem520.harperBlockEndpoint j) τ)
      (∑ p ∈ (Ioc (Problem520.harperBlockEndpoint j)
        (Problem520.harperBlockEndpoint stop)).filter Nat.Prime,
        Real.cos (τ * Real.log (p : ℝ)) / p)
    have hp := hprefix j τ
    linarith

end
end Erdos.Problem1144
