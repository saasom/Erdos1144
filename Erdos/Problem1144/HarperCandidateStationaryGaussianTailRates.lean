import Erdos.Problem1144.HarperCandidateStationaryGaussianTails

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology

namespace Erdos.Problem1144

private theorem log_schedule_card_le {κ T : ℝ} (hT : 2 ≤ T)
    (hm : 0 < candidateScheduleM κ T) (hcard : (candidateScheduleM κ T : ℝ) ≤ T) :
    Real.log (2 * (candidateScheduleM κ T : ℝ)) ≤ 2 * Real.log T := by
  have hTpos : 0 < T := by linarith
  have hmpos : (0 : ℝ) < candidateScheduleM κ T := Nat.cast_pos.mpr hm
  have h := Real.log_le_log (by positivity : 0 < 2 * (candidateScheduleM κ T : ℝ))
    (mul_le_mul_of_nonneg_left hcard (by norm_num : (0 : ℝ) ≤ 2))
  rw [Real.log_mul (by norm_num) hTpos.ne'] at h
  have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
  linarith

/-- Every finite grid of the candidate's scheduled size has negligible
squarefree high-frequency Gaussian error. The cutoff is the literal
`(log T)^2`, and the bound is uniform in all grid locations. -/
theorem candidate_eventually_squarefreeHighCovariance_tail_lt
    (s : Finset ℕ) (η : s → Bool) {κ r δ : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ u : Fin (candidateScheduleM κ T) → ℝ,
      Integrable (fun ω => candidateGaussianMaximumTail
        (candidateSquarefreeHighCovariance ω (candidateScheduleW κ T / T)
          (Real.log T ^ 2) u) r) (candidateCylinderLaw s η) ∧
      (∫ ω, candidateGaussianMaximumTail
        (candidateSquarefreeHighCovariance ω (candidateScheduleW κ T / T)
          (Real.log T ^ 2) u) r ∂candidateCylinderLaw s η) < δ := by
  have hprob : 0 < mu.real (candidateCylinder s η) :=
    ENNReal.toReal_pos (mu_candidateCylinder_ne_zero s η) (measure_ne_top _ _)
  have hm : Tendsto (fun T : ℝ => (candidateScheduleM κ T : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (candidateScheduleM_tendsto hκ)
  have hz := (Real.tendsto_log_atTop.const_div_atTop
    (12 / (Real.pi * mu.real (candidateCylinder s η) * r ^ 2))).add
      ((hm.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop 1)
  simp only [zero_add] at hz
  filter_upwards [hz.eventually (gt_mem_nhds hδ), eventually_ge_atTop (2 : ℝ),
    (candidateScheduleW_tendsto hκ).eventually_gt_atTop 0,
    (candidateScheduleM_tendsto hκ).eventually_gt_atTop 0,
    candidateScheduleM_eventually_le_time hκ,
    (candidateSchedule_half_damping_tendsto_zero hκ).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with T hsmall hT hW hmpos hcard hσhalf
  intro u
  have hTpos : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hσ : 0 < candidateScheduleW κ T / T := by positivity
  have hσone : candidateScheduleW κ T / T ≤ 1 := by
    have he : candidateScheduleW κ T / T =
        2 * (candidateScheduleW κ T / (2 * T)) := by ring
    rw [he]
    linarith
  have h := candidate_integral_squarefreeHighCovariance_tail_le s η hmpos u
    hσ (sq_pos_of_pos hlog) hr
  refine ⟨h.1, lt_of_le_of_lt (h.2.trans ?_) hsmall⟩
  apply add_le_add _ le_rfl
  calc
    _ ≤ (8 * Real.log T) * ((3 / 2) /
        (Real.pi * Real.log T ^ 2 * mu.real (candidateCylinder s η))) / r ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg r)
      apply mul_le_mul
      · nlinarith [log_schedule_card_le hT hmpos hcard]
      · exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      · positivity
      · positivity
    _ = (12 / (Real.pi * mu.real (candidateCylinder s η) * r ^ 2)) / Real.log T := by
      field_simp
      ring

/-- The actual omitted complete stationary Gaussian maximum is negligible,
uniformly over every scheduled-size grid above `(1+c)T`. The fractional
energy input is the proved unconditional complete-energy theorem. -/
theorem candidate_eventually_stationaryExtension_tail_lt
    (s : Finset ℕ) (η : s → Bool) {c κ r δ : ℝ}
    (hc : 0 ≤ c) (hκ : 0 < κ) (hgap : 2 < c * κ) (hr : 0 < r) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ u : Fin (candidateScheduleM κ T) → ℝ,
      (∀ i, (1 + c) * T ≤ u i) →
      Integrable (fun ω => candidateGaussianMaximumTail
        (candidateStationaryExtensionCovariance ω u T (candidateScheduleW κ T)) r)
        (candidateCylinderLaw s η) ∧
      (∫ ω, candidateGaussianMaximumTail
        (candidateStationaryExtensionCovariance ω u T (candidateScheduleW κ T)) r
          ∂candidateCylinderLaw s η) < δ := by
  obtain ⟨C, _, hMoment⟩ := candidate_exists_dampedCompleteEnergy_uniform_eighth_moment
  let Cq := C / mu.real (candidateCylinder s η)
  have hm : Tendsto (fun T : ℝ => (candidateScheduleM κ T : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (candidateScheduleM_tendsto hκ)
  have hmain := (candidate_stationary_tail_log_power_tendsto_zero 2
    (c := c / 2) hκ (by norm_num; nlinarith)).const_mul (16 / r ^ 2)
  have hn := (hm.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop 1
  have hpow : Tendsto (fun T : ℝ => Real.log T ^ (1 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp Real.tendsto_log_atTop
  have hz := (hmain.add hn).add (hpow.const_div_atTop Cq)
  simp only [mul_zero, zero_add] at hz
  filter_upwards [hz.eventually (gt_mem_nhds hδ), eventually_ge_atTop (2 : ℝ),
    (candidateScheduleW_tendsto hκ).eventually_gt_atTop 0,
    (candidateScheduleM_tendsto hκ).eventually_gt_atTop 0,
    candidateScheduleM_eventually_le_time hκ,
    (candidateSchedule_half_damping_tendsto_zero hκ).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))]
      with T hsmall hT hW hmpos hcard hσhalf
  intro u hu
  have hTpos : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hσ : 0 < candidateScheduleW κ T / (2 * T) := by positivity
  have hM := hMoment _ ⟨hσ, hσhalf.le⟩
  have hcond := candidateCylinderLaw_integral_nonneg_le s η hM.1
    (fun ω => Real.rpow_nonneg (candidateDampedCompleteEnergy_nonneg hσ.le ω) _)
  have hMomBound : (∫ ω,
      candidateDampedCompleteEnergy (candidateScheduleW κ T / (2 * T)) ω ^ (1 / 8 : ℝ)
        ∂candidateCylinderLaw s η) ≤ Cq :=
    hcond.2.trans (div_le_div_of_nonneg_right hM.2 measureReal_nonneg)
  have h := candidate_integral_stationaryExtension_tail_le_energy_moment s η hmpos u
    hc hTpos hW hlog (by norm_num : (0 : ℝ) < 1 / 8) hr hu hcond.1
  refine ⟨h.1, lt_of_le_of_lt (h.2.trans ?_) hsmall⟩
  apply add_le_add
  · apply add_le_add _ le_rfl
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (show 4 * Real.log (2 * (candidateScheduleM κ T : ℝ)) ≤ 8 * Real.log T by
          nlinarith [log_schedule_card_le hT hmpos hcard])
        (by positivity : 0 ≤ 2 * Real.exp (-c * candidateScheduleW κ T) /
          candidateScheduleW κ T * Real.log T)) (sq_nonneg r)
    convert hh using 1
    rw [show -2 * (c / 2) * candidateScheduleW κ T = -c * candidateScheduleW κ T by ring]
    ring
  · exact div_le_div_of_nonneg_right hMomBound (Real.rpow_nonneg hlog.le _)

end Erdos.Problem1144
