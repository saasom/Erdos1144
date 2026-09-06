import Erdos.Problem1144.HarperCandidateDampedCompleteEnergy
import Erdos.Problem1144.HarperCandidateStationaryTailDecay
import Erdos.Problem1144.HarperCandidateGaussianAssembly

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace Erdos.Problem1144

/-- The half-damping entering the integrated-energy tail bound tends to zero
on the actual schedule. -/
theorem candidateSchedule_half_damping_tendsto_zero {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun T : ℝ => candidateScheduleW κ T / (2 * T)) atTop (𝓝 0) := by
  have h := (candidateScheduleW_sq_div_tendsto hκ).div_const 2
  simp only [zero_div] at h
  apply squeeze_zero' _ _ h
  · filter_upwards [(candidateScheduleW_tendsto hκ).eventually_ge_atTop 1,
      eventually_gt_atTop (0 : ℝ)] with T hW hT
    positivity
  · filter_upwards [(candidateScheduleW_tendsto hκ).eventually_ge_atTop 1,
      eventually_gt_atTop (0 : ℝ)] with T hW hT
    rw [div_div, mul_comm T 2]
    apply div_le_div_of_nonneg_right (by nlinarith) (by positivity)

/-- Uniform fractional energy moments on one cylinder make the actual
omitted Gaussian maximum vanish. The cap is `log T`; hence `c*κ>2`
absorbs its cost and the Gaussian logarithmic grid factor. -/
theorem candidate_stationary_gaussian_maximum_tendsto_zero_of_energy_moment
    {Ξ : ℝ → Type*} [∀ T, MeasurableSpace (Ξ T)]
    {P : (T : ℝ) → Measure (Ξ T)} [∀ T, IsProbabilityMeasure (P T)]
    (s : Finset ℕ) (η : s → Bool) {c κ q C r : ℝ}
    (hc : 0 ≤ c) (hκ : 0 < κ) (hq : 0 < q)
    (hgap : 2 < c * κ) (hr : 0 < r)
    (X : (T : ℝ) → Fin (candidateScheduleM κ T) → Omega × Ξ T → ℝ)
    (v : (T : ℝ) → Omega → Fin (candidateScheduleM κ T) → ℝ≥0)
    (hXm : ∀ T i, Measurable (X T i))
    (hX : ∀ T ω i, (P T).map (fun ξ => X T i (ω, ξ)) = gaussianReal 0 (v T ω i))
    (hv : ∀ᶠ T in atTop, ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ i,
      (v T ω i : ℝ) ≤ candidateCompleteStationaryTailVariance ω c T (candidateScheduleW κ T))
    (hMoment : ∀ᶠ T : ℝ in atTop,
      Integrable (fun ω => candidateDampedCompleteEnergy (candidateScheduleW κ T / (2 * T)) ω ^ q)
        (candidateCylinderLaw s η) ∧
      (∫ ω, candidateDampedCompleteEnergy (candidateScheduleW κ T / (2 * T)) ω ^ q
        ∂candidateCylinderLaw s η) ≤ C) :
    Tendsto (fun T : ℝ => ((candidateCylinderLaw s η).prod (P T)).real
      {z | ∃ i, r ≤ |X T i z|}) atTop (𝓝 0) := by
  have hmain := (candidate_stationary_tail_log_power_tendsto_zero 2
    (c := c / 2) hκ (by norm_num; nlinarith)).const_mul (16 / r ^ 2)
  have hm : Tendsto (fun T : ℝ => (candidateScheduleM κ T : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (candidateScheduleM_tendsto hκ)
  have hn := (hm.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop 1
  have hpow : Tendsto (fun T : ℝ => Real.log T ^ q) atTop atTop :=
    (tendsto_rpow_atTop hq).comp Real.tendsto_log_atTop
  have hbad := hpow.const_div_atTop C
  have htotal := (hmain.add hn).add hbad
  simp only [mul_zero, zero_add] at htotal
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ htotal
  filter_upwards [eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_gt_atTop 0,
    (candidateScheduleW_tendsto hκ).eventually_gt_atTop 0,
    (candidateScheduleM_tendsto hκ).eventually_ge_atTop 1,
    candidateScheduleM_eventually_le_time hκ, hv, hMoment]
    with T hT hlog hW hmpos hmle hvT hMom
  have hTpos : 0 < T := by linarith
  letI : Nonempty (Fin (candidateScheduleM κ T)) := ⟨⟨0, by omega⟩⟩
  have h := candidate_stationary_gaussian_maximum_le_energy_moment
    s η hc hTpos hW hlog hq hr (hXm T) (hX T) hvT hMom.1
  simp only [Fintype.card_fin] at h
  have hlogcard : Real.log (2 * (candidateScheduleM κ T : ℝ)) ≤ 2 * Real.log T := by
    have hlog' := Real.log_le_log (by positivity : 0 < 2 * (candidateScheduleM κ T : ℝ))
      (mul_le_mul_of_nonneg_left hmle (by norm_num : (0 : ℝ) ≤ 2))
    rw [Real.log_mul (by norm_num) hTpos.ne'] at hlog'
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
    linarith
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) ?_)
  · have hcoef : 4 * Real.log (2 * (candidateScheduleM κ T : ℝ)) ≤ 8 * Real.log T := by linarith
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef
        (by positivity : 0 ≤ 2 * Real.exp (-c * candidateScheduleW κ T) /
          candidateScheduleW κ T * Real.log T)) (sq_nonneg r)
    convert hh using 1
    rw [show -2 * (c / 2) * candidateScheduleW κ T = -c * candidateScheduleW κ T by ring]
    ring
  · exact div_le_div_of_nonneg_right hMom.2 (Real.rpow_nonneg hlog.le q)

/-- A uniform fractional moment under the original sign law transfers to
every fixed cylinder and discharges the stationary Gaussian tail step.
The displayed complete-energy moment is the sole arithmetic premise here. -/
theorem candidate_stationary_gaussian_maximum_tendsto_zero_of_uniform_energy_moment
    {Ξ : ℝ → Type*} [∀ T, MeasurableSpace (Ξ T)]
    {P : (T : ℝ) → Measure (Ξ T)} [∀ T, IsProbabilityMeasure (P T)]
    (s : Finset ℕ) (η : s → Bool) {c κ q C σ₀ r : ℝ}
    (hc : 0 ≤ c) (hκ : 0 < κ) (hq : 0 < q) (hσ₀ : 0 < σ₀)
    (hgap : 2 < c * κ) (hr : 0 < r)
    (hMoment : ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      Integrable (fun ω => candidateDampedCompleteEnergy σ ω ^ q) mu ∧
      (∫ ω, candidateDampedCompleteEnergy σ ω ^ q ∂mu) ≤ C)
    (X : (T : ℝ) → Fin (candidateScheduleM κ T) → Omega × Ξ T → ℝ)
    (v : (T : ℝ) → Omega → Fin (candidateScheduleM κ T) → ℝ≥0)
    (hXm : ∀ T i, Measurable (X T i))
    (hX : ∀ T ω i, (P T).map (fun ξ => X T i (ω, ξ)) = gaussianReal 0 (v T ω i))
    (hv : ∀ᶠ T in atTop, ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ i,
      (v T ω i : ℝ) ≤ candidateCompleteStationaryTailVariance ω c T (candidateScheduleW κ T)) :
    Tendsto (fun T : ℝ => ((candidateCylinderLaw s η).prod (P T)).real
      {z | ∃ i, r ≤ |X T i z|}) atTop (𝓝 0) := by
  apply candidate_stationary_gaussian_maximum_tendsto_zero_of_energy_moment
    s η hc hκ hq hgap hr X v hXm hX hv
  filter_upwards [(candidateSchedule_half_damping_tendsto_zero hκ).eventually
      (gt_mem_nhds hσ₀), (candidateScheduleW_tendsto hκ).eventually_gt_atTop 0,
      eventually_gt_atTop (0 : ℝ)] with T hupper hW hT
  have hσ : 0 < candidateScheduleW κ T / (2 * T) := by positivity
  have hm := hMoment _ ⟨hσ, hupper.le⟩
  have hcond := candidateCylinderLaw_integral_nonneg_le s η hm.1
    (fun ω => Real.rpow_nonneg (candidateDampedCompleteEnergy_nonneg hσ.le ω) q)
  exact ⟨hcond.1, hcond.2.trans (div_le_div_of_nonneg_right hm.2 measureReal_nonneg)⟩

end Erdos.Problem1144
