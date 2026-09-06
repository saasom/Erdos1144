import Erdos.Problem1144.HarperCandidateCovarianceNearExpectationRate
import Erdos.Problem1144.HarperCandidateCovarianceFarScheduledRate
import Erdos.Problem1144.HarperCandidateCovarianceDegreeMeasurability

open Filter MeasureTheory
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The actual common near/far degree event on the canonical covariance
schedule. The raw Fourier threshold retains its exact `(2π)^2` factor;
the half-size real degree budget leaves room for integer rounding. -/
def candidateCovarianceScheduledDegreeControl (J : ℕ) (β κ T : ℝ) : Set Problem520.Omega :=
  candidateCovarianceDegreeControlEvent
    (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
    (candidateCovarianceScheduleStrong J T) (Real.log T)
    (candidateCovarianceScheduleLowerHeight T) (candidateCovarianceScheduleHeight T)
    T (β * T) (candidateCovarianceScheduleWidth T) (candidateCovarianceScheduleOrder T)
    (candidateScheduleM κ T) ((2 * Real.pi) ^ 2 * Real.log T ^ (-(3 : ℝ) / 5))
    (T ^ ((4 : ℝ) / 5) / 2)

/-- Exact measurability requires only the cutoff ordering already provided
eventually by the rounded schedule. -/
theorem candidate_measurableSet_scheduledDegreeControl (J : ℕ) (β κ T : ℝ)
    (horder : candidateCovarianceScheduleStart J T ≤ candidateEulerTopIndex T) :
    MeasurableSet (candidateCovarianceScheduledDegreeControl J β κ T) :=
  candidate_measurableSet_degreeControlEvent _ _ _ horder _ _ _ _ _ _ _ _ _ _

theorem candidate_eventually_measurableSet_scheduledDegreeControl (J : ℕ) (β κ : ℝ) :
    ∀ᶠ T : ℝ in atTop, MeasurableSet (candidateCovarianceScheduledDegreeControl J β κ T) := by
  filter_upwards [candidate_eventually_covarianceSchedule_room J 0] with T hT
  exact candidate_measurableSet_scheduledDegreeControl J β κ T (by simpa using hT)

/-- The actual common covariance degree event has probability tending to
one on every fixed cylinder. Both Markov terms are discharged by the proved
near and far rates; there is no covariance or moment hypothesis. -/
theorem candidate_exists_scheduledDegreeControl_cylinder_failure_tendsto_zero :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ β κ : ℝ, 1 ≤ β → 0 < κ →
      ∀ s : Finset ℕ, ∀ η : s → Bool,
      Tendsto (fun T : ℝ => (candidateCylinderLaw s η).real
        (candidateCovarianceScheduledDegreeControl J β κ T)ᶜ) atTop (𝓝 0) := by
  obtain ⟨JN, hnear⟩ := candidate_exists_scheduledNearRow_candidateGrid_tendsto_zero
  obtain ⟨JF, hfar⟩ := candidate_exists_scheduledFarMass_threshold_tendsto_zero
  refine ⟨max JN JF, ?_⟩
  intro J hJ β κ hβ hκ s η
  let c : ℝ := (2 * Real.pi) ^ 2
  have hc : 0 < c := by dsimp only [c]; positivity
  let near (T : ℝ) := ∫ ω, candidateEulerBandNearRowEnvelope
    (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
    (candidateCovarianceScheduleStrong J T) (Real.log T)
    (candidateCovarianceScheduleHeight T) T (β * T)
    (candidateCovarianceScheduleWidth T) (candidateCovarianceScheduleOrder T)
    (candidateScheduleM κ T) ω ∂Problem520.μ
  let far (T : ℝ) := ∫ ω, candidateEulerBandFarMass (candidateEulerTopCutoff T) T (β * T)
    (candidateCovarianceScheduleLowerHeight T) (candidateCovarianceScheduleHeight T)
    (candidateCovarianceScheduleWidth T) ω ∂Problem520.μ
  let raw (T : ℝ) := c * Real.log T ^ (-(3 : ℝ) / 5)
  let budget (T : ℝ) := T ^ ((4 : ℝ) / 5) / 2
  have hn := hnear J ((le_max_left _ _).trans hJ) β c κ hβ hc hκ
  have hf := hfar J ((le_max_right _ _).trans hJ) β hβ
  have hn' : Tendsto (fun T : ℝ => near T /
      (budget T * (raw T / 2) ^ (2 * candidateCovarianceScheduleOrder T))) atTop (𝓝 0) := by
    convert hn.const_mul (2 : ℝ) using 1
    · ext T
      dsimp only [near, budget, raw]
      ring
    · simp
  have hf' : Tendsto (fun T : ℝ => far T / (raw T / 2)) atTop (𝓝 0) := by
    have hh := hf.const_mul (2 / c)
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hq : 0 < Real.log T := Real.log_pos hT
    change (2 / c) * (far T * Real.log T ^ ((3 : ℝ) / 5)) = far T / (raw T / 2)
    dsimp only [raw]
    rw [show -(3 : ℝ) / 5 = -((3 : ℝ) / 5) by ring, Real.rpow_neg hq.le]
    field_simp
  have hsum := (hn'.add hf').div_const (Problem520.μ.real (candidateCylinder s η))
  simp only [zero_add, zero_div] at hsum
  apply squeeze_zero' (g := fun T : ℝ =>
    (near T / (budget T * (raw T / 2) ^ (2 * candidateCovarianceScheduleOrder T)) +
      far T / (raw T / 2)) / Problem520.μ.real (candidateCylinder s η))
  · exact Filter.Eventually.of_forall fun _ => measureReal_nonneg
  · filter_upwards [candidate_eventually_covarianceSchedule_room J 0,
      eventually_gt_atTop (1 : ℝ)] with T horder hT
    have hTp : 0 < T := by linarith
    have hq : 0 < Real.log T := Real.log_pos hT
    have hTB : T ≤ β * T := by nlinarith only [mul_le_mul_of_nonneg_right hβ hTp.le]
    exact candidate_degreeControl_cylinder_failure_le s η
      (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
      (candidateCovarianceScheduleStrong J T) (by simpa using horder) (Real.log T)
      (candidateCovarianceScheduleLowerHeight T) (candidateCovarianceScheduleHeight T)
      (candidateCovarianceScheduleWidth T) hTp hTB (by positivity)
      (by positivity) (candidateCovarianceScheduleOrder T) (candidateScheduleM κ T)
  · exact hsum

/-- The chosen real degree budget is eventually below the integer degree
used in finite Gaussian thinning. -/
theorem candidate_eventually_covarianceSchedule_degreeBudget_le_floor :
    ∀ᶠ T : ℝ in atTop,
      T ^ ((4 : ℝ) / 5) / 2 ≤ (⌊T ^ ((4 : ℝ) / 5)⌋₊ : ℝ) := by
  filter_upwards [(tendsto_rpow_atTop (by norm_num : 0 < (4 : ℝ) / 5)).eventually_ge_atTop 2]
    with T hT
  have hf := Nat.lt_floor_add_one (T ^ ((4 : ℝ) / 5))
  linarith

/-- Any actual cardinal controlled by the scheduled real budget therefore
satisfies the rounded natural degree bound, uniformly in that cardinal. -/
theorem candidate_eventually_covarianceSchedule_card_le_floor :
    ∀ᶠ T : ℝ in atTop, ∀ n : ℕ,
      (n : ℝ) ≤ T ^ ((4 : ℝ) / 5) / 2 → n ≤ ⌊T ^ ((4 : ℝ) / 5)⌋₊ := by
  filter_upwards [candidate_eventually_covarianceSchedule_degreeBudget_le_floor] with T hT
  intro n hn
  exact_mod_cast hn.trans hT

end
end Erdos.Problem1144
