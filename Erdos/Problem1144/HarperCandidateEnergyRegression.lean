import Erdos.Problem1144.HarperCandidateEnergyTwoHeightRectangle
import Erdos.Problem1144.HarperBivariateRelativeCell

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos.Problem1144

theorem candidate_rankinRegressionResidualVariance_nonneg
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real)
    (ha : 0 < harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t) :
    0 ≤ harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s s s -
      harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t s ^ (2 : Nat) /
        harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t := by
  let a := harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t
  let b := harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s s s
  let q := harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t s
  have hproj := harperRankinTwoHeightProjectedBlockVariance_nonneg
    y S σ hσ t s q (-a)
  rw [harperRankinTwoHeightProjectedBlockVariance_eq_coordinateCovariance] at hproj
  have hdet : 0 ≤ a * b - q ^ (2 : Nat) := by
    have hmul : 0 ≤ a * (a * b - q ^ (2 : Nat)) := by
      dsimp only [a, b, q] at hproj ⊢
      nlinarith
    nlinarith [hmul, show 0 < a by simpa only [a] using ha]
  have ha0 : harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t ≠ 0 :=
    ne_of_gt ha
  have heq :
      harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s s s -
          harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t s ^ (2 : Nat) /
            harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t =
        (harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t *
              harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s s s -
            harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t s ^ (2 : Nat)) /
          harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t := by
    field_simp [ha0]
  rw [heq]
  exact div_nonneg hdet ha.le

/-- Literal shifted regression coefficient. -/
noncomputable def candidateRankinRegressionCoefficient
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : ℝ) : ℝ :=
  harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t s /
    harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t

/-- The actual residual variance, truncated only to define the law also when
its first marginal variance is zero. The truncation vanishes whenever that
marginal is positive. -/
noncomputable def candidateRankinRegressionResidualVariance
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : ℝ) : ℝ≥0 :=
  (harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s s s -
    harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t s ^ 2 /
      harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t).toNNReal

theorem candidate_coe_rankinRegressionResidualVariance
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : ℝ)
    (hA : 0 < harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t) :
    (candidateRankinRegressionResidualVariance y S σ hσ t s : ℝ) =
      harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s s s -
        harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t s ^ 2 /
          harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t := by
  exact Real.coe_toNNReal _
    (candidate_rankinRegressionResidualVariance_nonneg y S σ hσ t s hA)

/-- The covariance-matched Gaussian for the actual shifted block. -/
noncomputable def candidateRankinMatchedGaussianLaw
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : ℝ) : Measure (ℝ × ℝ) :=
  harperGaussianRegressionBlockLaw
    (candidateRankinTwoHeightCoordinateVarianceNNReal y S σ hσ t s t)
    (candidateRankinRegressionResidualVariance y S σ hσ t s)
    (candidateRankinRegressionCoefficient y S σ hσ t s)

instance candidateRankinMatchedGaussianLaw_isProbabilityMeasure
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s : ℝ) :
    IsProbabilityMeasure (candidateRankinMatchedGaussianLaw y S σ hσ t s) := by
  unfold candidateRankinMatchedGaussianLaw
  infer_instance

/-- Exact characteristic identity, with the literal shifted projected variance. -/
theorem candidate_rankinBivariateCharacteristic_matchedGaussianLaw
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (σ : ℝ) (hσ : 0 ≤ σ) (t s v w : ℝ)
    (hA : 0 < harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t) :
    harperBivariateCharacteristic (candidateRankinMatchedGaussianLaw y S σ hσ t s) (v, w) =
      Complex.exp (-((harperRankinTwoHeightProjectedBlockVariance y S σ hσ t s v w / 2 : ℝ) : ℂ)) := by
  unfold candidateRankinMatchedGaussianLaw
  rw [harperBivariateCharacteristic_gaussianRegressionBlockLaw,
    coe_candidateRankinTwoHeightCoordinateVarianceNNReal,
    candidate_coe_rankinRegressionResidualVariance y S σ hσ t s hA,
    harperRankinTwoHeightProjectedBlockVariance_eq_coordinateCovariance]
  congr 3
  unfold candidateRankinRegressionCoefficient
  field_simp
  <;> ring

/-- The existing radial closeness margin already suffices for the generic
Gaussian cell-density and regression ballot estimates. -/
theorem candidate_regression_parameters_of_shifted_window
    {A B C : ℝ} (hA : 13 / 48 ≤ A) (hA' : A ≤ 7 / 16)
    (hB : 13 / 48 ≤ B) (hB' : B ≤ 7 / 16) (hC : |C| ≤ 1 / 16) :
    0 < A ∧ 1 / 4 ≤ A ∧ A ≤ 1 / 2 ∧
      1 / 4 ≤ B - C ^ 2 / A ∧ B - C ^ 2 / A ≤ 1 / 2 ∧ |C / A| ≤ 3 / 8 := by
  have hA0 : 0 < A := by linarith
  have hCsq : C ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by
    rw [sq_le_sq]
    simpa using hC
  have hdiv0 : 0 ≤ C ^ 2 / A := div_nonneg (sq_nonneg _) hA0.le
  have hdiv : C ^ 2 / A ≤ 3 / 208 := by
    rw [div_le_iff₀ hA0]
    nlinarith
  refine ⟨hA0, by linarith, by linarith, by linarith, by linarith, ?_⟩
  rw [abs_div, abs_of_pos hA0, div_le_iff₀ hA0]
  linarith

/-- The radial covariance approximation has one start for every Rankin parameter. -/
theorem candidate_exists_uniformStart_rankinCovariance_close :
    ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V →
      ∃ gap : ℕ, ∀ j y : ℕ, J ≤ j →
        Problem520.harperBlockEndpoint (j + gap + 1) ≤ y →
          ∀ ha : 0 ≤ 4 * V / Real.log (y : ℝ), ∀ t s u v : ℝ,
            |harperRankinTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j)
                  (4 * V / Real.log (y : ℝ))
                  ha
                  t s u v -
                harperTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j) t s u v| <
              (1 / 16 : ℝ) := by
  obtain ⟨Jmass, hmass⟩ :=
    Problem520.exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
      (by norm_num : (0 : ℝ) < 1 / 1000)
  obtain ⟨c, hc, C, hC, Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  have hsquareTendsto : Tendsto Problem520.harperScheduledSquareEnvelope
      atTop (nhds 0) :=
    Problem520.summable_harperScheduledSquareEnvelope.tendsto_atTop_zero
  have hsquareEventually : ∀ᶠ j : ℕ in atTop,
      Problem520.harperScheduledSquareEnvelope j <
        (1 / 32768 : ℝ) :=
    (tendsto_order.mp hsquareTendsto).2 _ (by norm_num)
  obtain ⟨Jsquare, hsquare⟩ := eventually_atTop.1 hsquareEventually
  refine ⟨max Jmass (max Jerr Jsquare), ?_⟩
  intro V hV
  obtain ⟨gap, hgap⟩ := exists_harperRankinStrongRadialGap V
  refine ⟨gap, ?_⟩
  intro j y hj hy ha t s u v
  have hjmass : Jmass ≤ j := by omega
  have hjerr : Jerr ≤ j := by omega
  have hjsquare : Jsquare ≤ j := by omega
  have hyNear : Problem520.harperBlockEndpoint (j + 1) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hyOne : (1 : ℕ) < y := by
    have hbase :=
      Problem520.harperBlockEndpoint_ge_sixteen (j + gap + 1)
    omega
  have hclose :=
    abs_harperRankinTwoHeightBlockCoordinateCovariance_sub_critical_le
      y (Problem520.harperScheduledPrimeBlock y j) ha
      (fun p hpS ↦ by
        have :=
          Problem520.sixtyFour_le_prime_of_mem_harperScheduledPrimeBlock hpS
        omega)
      (fun p hpS ↦
        harperRankinScheduledPrime_radialWeight_of_strongGap
          hgap hy p hpS)
      t s u v
  have hmassj := hmass j hjmass y hyNear
  change |Problem520.harperScheduledReciprocalMass y j - Real.log 2| <
    (1 / 1000 : ℝ) at hmassj
  have hmassUpper :
      Problem520.harperScheduledReciprocalMass y j <
        (901 / 1000 : ℝ) := by
    have := lt_of_abs_lt hmassj
    nlinarith [Real.log_two_lt_d9]
  have hsquareBound :
      Problem520.harperScheduledSquareMass y j ≤
        Problem520.harperScheduledSquareEnvelope j :=
    (herr j hjerr y hyNear).2.2
  have hsquareSmall := hsquare j hjsquare
  change |harperRankinTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j)
        (4 * V / Real.log (y : ℝ)) ha t s u v -
      harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s u v| ≤
    (1 / 20 : ℝ) * Problem520.harperScheduledReciprocalMass y j +
      512 * Problem520.harperScheduledSquareMass y j at hclose
  nlinarith


/-- The actual matched Gaussian parameters hold at an absolute start,
independent of path length, retaining the terminal radial gap. -/
theorem candidate_exists_gap_rankinMatchedGaussian_parameters
    : ∃ J : ℕ, ∀ V : ℝ, 0 ≤ V → ∃ gap : ℕ, ∀ shell j y : ℕ, J + (shell + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + gap + 1) ≤ y →
        ∀ hσ : 0 ≤ 4 * V / Real.log (y : ℝ),
          ∀ t ∈ harperLowerVerticalBand, ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : ℝ) ^ (shell + 1) < |t - s| →
              let σ := 4 * V / Real.log (y : ℝ)
              let S := Problem520.harperScheduledPrimeBlock y j
              0 < harperRankinTwoHeightBlockCoordinateCovariance y S σ hσ t s t t ∧
                1 / 4 ≤ (candidateRankinTwoHeightCoordinateVarianceNNReal y S σ hσ t s t : ℝ) ∧
                (candidateRankinTwoHeightCoordinateVarianceNNReal y S σ hσ t s t : ℝ) ≤ 1 / 2 ∧
                1 / 4 ≤ (candidateRankinRegressionResidualVariance y S σ hσ t s : ℝ) ∧
                (candidateRankinRegressionResidualVariance y S σ hσ t s : ℝ) ≤ 1 / 2 ∧
                |candidateRankinRegressionCoefficient y S σ hσ t s| ≤ 3 / 8 := by
  obtain ⟨Jclose, hclose⟩ := candidate_exists_uniformStart_rankinCovariance_close
  obtain ⟨Jvar, hvar⟩ := exists_eventually_harperTwoHeightScheduledCoordinateVariance_third_threeEighths
  obtain ⟨Jcov, hcov⟩ := candidate_exists_rankinScheduledCovariance_postCoherence_small
    (by norm_num : (0 : ℝ) < 1 / 16)
  refine ⟨max Jclose (max Jvar Jcov), ?_⟩
  intro V hV
  obtain ⟨gap, hclose⟩ := hclose V hV
  refine ⟨gap, ?_⟩
  intro shell j y hj hy hσ t ht s hs hsep
  have hnear : Problem520.harperBlockEndpoint (j + 1) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hct := hclose j y (by omega) hy hσ t s t t
  have hcs := hclose j y (by omega) hy hσ t s s s
  have hvt := hvar j (by omega) y hnear t ht s hs t ht
  have hvs := hvar j (by omega) y hnear t ht s hs s hs
  have hc := hcov shell j y (by omega) hnear _ hσ t ht s hs hsep
  have hp := candidate_regression_parameters_of_shifted_window
    (A := harperRankinTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) _ hσ t s t t)
    (B := harperRankinTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) _ hσ t s s s)
    (C := harperRankinTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) _ hσ t s t s)
    (by linarith [(abs_lt.mp hct).1]) (by linarith [(abs_lt.mp hct).2])
    (by linarith [(abs_lt.mp hcs).1]) (by linarith [(abs_lt.mp hcs).2]) hc.le
  dsimp only
  rw [candidate_coe_rankinRegressionResidualVariance _ _ _ _ _ _ hp.1]
  exact hp

end Erdos.Problem1144
