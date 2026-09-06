import Erdos.Problem1144.HarperCandidateStationaryTailVariance

open MeasureTheory Set

namespace Erdos.Problem1144

/-- The actual covariance omitted when the complete stationary white-noise
integral is restricted to prime times `v ≥ T`. -/
noncomputable def candidateStationaryExtensionCovariance {ι : Type*}
    (ω : Omega) (u : ι → ℝ) (T W : ℝ) : Matrix ι ι ℝ :=
  candidateWeightedGram (volume.restrict (Iio T))
    (fun i v => harperCandidateLogProcess ω (u i - v) *
      Real.exp (-(W / T) * (u i - v))) (fun _ => 1 / T)

private theorem candidate_integral_sub_left_Iio (f : ℝ → ℝ) (u T : ℝ) :
    (∫ v in Iio T, f (u - v)) = ∫ t in Ioi (u - T), f t := by
  rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioi]
  have h := integral_sub_left_eq_self ((Ioi (u - T)).indicator f) volume u
  convert h using 1
  congr 1
  funext v
  by_cases hv : v < T
  · have hu : u - T < u - v := by linarith
    simp [hv, hu]
  · have hu : ¬u - T < u - v := by linarith
    simp [hv, hu]

/-- The omitted covariance diagonal is the exact one-sided damped integral
starting at `u_i − T`, before it is bounded by the common tail. -/
theorem candidateStationaryExtensionCovariance_diag {ι : Type*}
    (ω : Omega) (u : ι → ℝ) (T W : ℝ) (i : ι) :
    candidateStationaryExtensionCovariance ω u T W i i =
      (1 / T) * ∫ t in Ioi (u i - T), Real.exp (-2 * W * t / T) *
        harperCandidateLogProcess ω t ^ 2 := by
  unfold candidateStationaryExtensionCovariance candidateWeightedGram
  rw [← integral_const_mul]
  have he (t : ℝ) : Real.exp (-(W / T) * t) ^ 2 = Real.exp (-2 * W * t / T) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hform : (fun v : ℝ => (1 / T) *
      (harperCandidateLogProcess ω (u i - v) * Real.exp (-(W / T) * (u i - v))) *
      (harperCandidateLogProcess ω (u i - v) * Real.exp (-(W / T) * (u i - v)))) =
      (fun v => (1 / T) * (Real.exp (-2 * W * (u i - v) / T) *
        harperCandidateLogProcess ω (u i - v) ^ 2)) := by
    funext v
    rw [show (1 / T) *
        (harperCandidateLogProcess ω (u i - v) * Real.exp (-(W / T) * (u i - v))) *
        (harperCandidateLogProcess ω (u i - v) * Real.exp (-(W / T) * (u i - v))) =
        (1 / T) * harperCandidateLogProcess ω (u i - v) ^ 2 *
          Real.exp (-(W / T) * (u i - v)) ^ 2 by ring, he]
    ring
  rw [hform, integral_const_mul, integral_const_mul]
  congr 1
  exact candidate_integral_sub_left_Iio
    (fun t => Real.exp (-2 * W * t / T) * harperCandidateLogProcess ω t ^ 2) (u i) T

/-- Equation (23), simultaneously for every grid above `(1+c)T`, under
every fixed cylinder. The needed damped integrability is proved. -/
theorem candidateCylinderLaw_ae_stationaryExtension_diag_le
    (s : Finset ℕ) (η : s → Bool) {c T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ (m : ℕ) (u : Fin m → ℝ),
      (∀ i, (1 + c) * T ≤ u i) → ∀ i,
        candidateStationaryExtensionCovariance ω u T W i i ≤
          candidateCompleteStationaryTailVariance ω c T W := by
  filter_upwards [candidateCylinderLaw_ae_damped_L1_L2 s η (div_pos hW hT)] with ω hω
  have ha : Integrable (fun t => Real.exp (-2 * W * t / T) *
      harperCandidateLogProcess ω t ^ 2) := by
    have h := (memLp_two_iff_integrable_sq hω.1.2.1).mp hω.1.2
    convert h using 1
    funext t
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  intro m u hu i
  rw [candidateStationaryExtensionCovariance_diag]
  unfold candidateCompleteStationaryTailVariance
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply setIntegral_mono_set ha.integrableOn
    (ae_of_all _ fun _ => by positivity)
  exact ae_of_all _ fun t ht => lt_of_le_of_lt (by nlinarith [hu i]) ht

end Erdos.Problem1144
