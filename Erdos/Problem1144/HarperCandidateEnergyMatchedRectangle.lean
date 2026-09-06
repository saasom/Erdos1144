import Erdos.Problem1144.HarperCandidateEnergyRegression

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

/-- Smoothing retains the actual covariance in the Gaussian, so only the
shifted characteristic approximation contributes an error. -/
theorem candidate_rankinScheduledSmoothRectangle_sub_matched_le
    (y j : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s T l r b d : ℝ) (hT : 0 < T)
    (hfrequency : 4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))
    (hA : 0 < harperRankinTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) a ha t s t t) :
    |harperBivariateSmoothRectangle (Problem520.harperFejerMeasureScaled T)
      (harperRankinTwoHeightPrimeBlockVectorLaw y (Problem520.harperScheduledPrimeBlock y j)
        a ha t s) l r b d -
      harperBivariateSmoothRectangle (Problem520.harperFejerMeasureScaled T)
        (candidateRankinMatchedGaussianLaw y
          (Problem520.harperScheduledPrimeBlock y j) a ha t s) l r b d| ≤
      (2 * Real.pi)⁻¹ ^ 2 * |r - l| * |d - b| *
        ((Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
          (512 * T ^ 5 + 128 * T ^ 6)) := by
  let q := (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbound := abs_harperBivariateSmoothRectangle_sub_le_of_identity_quadratic
    (harperRankinTwoHeightPrimeBlockVectorLaw y (Problem520.harperScheduledPrimeBlock y j) a ha t s)
    (candidateRankinMatchedGaussianLaw y
      (Problem520.harperScheduledPrimeBlock y j) a ha t s)
    T (q * (32 * T + 8 * T ^ 2)) l r b d hT.le (by positivity)
    (harperBivariateFejerRectangleIdentity_of_pos _ _ hT) ?_
  · convert hbound using 1 <;> dsimp only [q] <;> ring
  · intro z hz
    have hz1 : |z.1| ≤ T := abs_le.mpr ⟨by linarith [hz.1.1], hz.1.2⟩
    have hz2 : |z.2| ≤ T := abs_le.mpr ⟨by linarith [hz.2.1], hz.2.2⟩
    have hf : 2 * (|z.1| + |z.2|) ≤ Real.sqrt (Problem520.harperBlockEndpoint j : ℝ) := by linarith
    have hbase :
        ‖harperBivariateCharacteristic (harperRankinTwoHeightPrimeBlockVectorLaw y
            (Problem520.harperScheduledPrimeBlock y j) a ha t s) z -
          harperBivariateCharacteristic (candidateRankinMatchedGaussianLaw y
            (Problem520.harperScheduledPrimeBlock y j) a ha t s) z‖ ≤
          q * (16 * (|z.1| + |z.2|) ^ 3 + 2 * (|z.1| + |z.2|) ^ 4) := by
      rw [show z = (z.1, z.2) from rfl,
        candidate_rankinBivariateCharacteristic_matchedGaussianLaw _ _ _ _ _ _ _ _ hA]
      exact norm_charFunDual_harperRankinTwoHeightScheduledVectorLaw_sub_gaussian_le
        y j a ha t s z.1 z.2 hf
    refine hbase.trans ?_
    let L := |z.1| + |z.2|
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hLT : L ≤ 2 * T := by dsimp [L]; linarith
    have hL3 : L ^ 3 ≤ (2 * T) * L ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hLT (sq_nonneg L)]
    have hL4 : L ^ 4 ≤ (4 * T ^ 2) * L ^ 2 := by
      have hL2 : L ^ 2 ≤ 4 * T ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hL2 (sq_nonneg L)]
    have hpoly := add_le_add (mul_le_mul_of_nonneg_left hL3 (by norm_num : (0 : ℝ) ≤ 16))
      (mul_le_mul_of_nonneg_left hL4 (by norm_num : (0 : ℝ) ≤ 2))
    have h1 := mul_le_mul_of_nonneg_left hpoly hq
    change q * (16 * L ^ 3 + 2 * L ^ 4) ≤
      (q * (32 * T + 8 * T ^ 2)) * L ^ 2
    nlinarith

/-- Actual half-open rectangle comparison obtained by Fourier smoothing
and unsmoothing. The Gaussian retains the full shifted covariance. -/
theorem candidate_rankinScheduledRectangleMass_le_matched_explicit
    (y j : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (t s T R : ℝ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hT : 0 < T) (hR : 2 ≤ R)
    (hfrequency : 4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))
    (hA : 0 < harperRankinTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) σ hσ t s t t) :
    (1 - 2 / R) ^ 2 * (harperRankinTwoHeightPrimeBlockVectorLaw y
      (Problem520.harperScheduledPrimeBlock y j) σ hσ t s).real (Ioc a b ×ˢ Ioc c d) ≤
      (candidateRankinMatchedGaussianLaw y
        (Problem520.harperScheduledPrimeBlock y j) σ hσ t s).real
        (Ioc (a - 2 * (R / T)) (b + 2 * (R / T)) ×ˢ
          Ioc (c - 2 * (R / T)) (d + 2 * (R / T))) + 2 / R +
        (2 * Real.pi)⁻¹ ^ 2 * |(b + R / T) - (a - R / T)| *
          |(d + R / T) - (c - R / T)| *
          ((Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
            (512 * T ^ 5 + 128 * T ^ 6)) := by
  let P := harperRankinTwoHeightPrimeBlockVectorLaw y
    (Problem520.harperScheduledPrimeBlock y j) σ hσ t s
  let Q := candidateRankinMatchedGaussianLaw y
    (Problem520.harperScheduledPrimeBlock y j) σ hσ t s
  let κ := Problem520.harperFejerMeasureScaled T
  have hδ : 0 ≤ R / T := div_nonneg (by linarith) hT.le
  have hα : 2 / R ≤ 1 := (div_le_one (by linarith)).mpr hR
  have htail := harperFejerMeasureScaled_tail_le_two_div hT hR
  have hlo := one_sub_sq_mul_rectangleMass_le_smoothExpanded κ P hab hcd hδ hα htail
  have hmid := candidate_rankinScheduledSmoothRectangle_sub_matched_le y j σ hσ t s T
    (a - R / T) (b + R / T) (c - R / T) (d + R / T) hT hfrequency hA
  have hup := smoothRectangle_le_expandedRectangleMass_add_tail κ Q
    (a := a - R / T) (b := b + R / T) (c := c - R / T) (d := d + R / T)
    (delta := R / T) (alpha := 2 / R)
    (by linarith) (by linarith) hδ (by positivity) htail
  have heq :
      (Ioc ((a - R / T) - R / T) ((b + R / T) + R / T) ×ˢ
        Ioc ((c - R / T) - R / T) ((d + R / T) + R / T)) =
      (Ioc (a - 2 * (R / T)) (b + 2 * (R / T)) ×ˢ
        Ioc (c - 2 * (R / T)) (d + 2 * (R / T))) := by ring_nf
  rw [heq] at hup
  have hmidOne := le_of_abs_le hmid
  change (1 - 2 / R) ^ 2 * P.real (Ioc a b ×ˢ Ioc c d) ≤ _
  dsimp only [P, Q, κ] at hlo hup ⊢
  linarith

end Erdos.Problem1144
