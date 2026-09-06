import Erdos.Problem1144.HarperCandidateCovarianceScheduledDegree

open Filter MeasureTheory
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The canonical screen degree event with an independent grid cardinality.
This permits changing the white comparison time while preserving the selector. -/
def candidateCovarianceScheduledGridDegreeControl (J : ℕ) (β T : ℝ) (n : ℕ) :
    Set Omega :=
  candidateCovarianceDegreeControlEvent
    (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
    (candidateCovarianceScheduleStrong J T) (Real.log T)
    (candidateCovarianceScheduleLowerHeight T) (candidateCovarianceScheduleHeight T)
    T (β * T) (candidateCovarianceScheduleWidth T) (candidateCovarianceScheduleOrder T)
    n ((2 * Real.pi) ^ 2 * Real.log T ^ (-(3 : ℝ) / 5)) (T ^ ((4 : ℝ) / 5) / 2)

theorem candidate_measurableSet_scheduledGridDegreeControl (J : ℕ) (β T : ℝ) (n : ℕ)
    (horder : candidateCovarianceScheduleStart J T ≤ candidateEulerTopIndex T) :
    MeasurableSet (candidateCovarianceScheduledGridDegreeControl J β T n) :=
  candidate_measurableSet_degreeControlEvent _ _ _ horder _ _ _ _ _ _ _ _ _ _

private theorem grid_degree_selection_rate :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ β : ℝ, 1 ≤ β →
      ∀ N : ℝ → ℕ, (∀ᶠ T : ℝ in atTop, (N T : ℝ) ≤ T) →
      ∀ s : Finset ℕ, ∀ η : s → Bool,
      Tendsto (fun T : ℝ => (candidateCylinderLaw s η).real
        (candidateCovarianceScheduledGridDegreeControl J β T (N T))ᶜ) atTop (𝓝 0) := by
  obtain ⟨JN, hnear⟩ := candidate_exists_scheduledNearRow_threshold_tendsto_zero
  obtain ⟨JF, hfar⟩ := candidate_exists_scheduledFarMass_threshold_tendsto_zero
  refine ⟨max JN JF, ?_⟩
  intro J hJ β hβ N hN s η
  let c : ℝ := (2 * Real.pi) ^ 2
  have hc : 0 < c := by dsimp only [c]; positivity
  let near (T : ℝ) := ∫ ω, candidateEulerBandNearRowEnvelope
    (candidateCovarianceScheduleStart J T) (candidateEulerTopIndex T)
    (candidateCovarianceScheduleStrong J T) (Real.log T)
    (candidateCovarianceScheduleHeight T) T (β * T)
    (candidateCovarianceScheduleWidth T) (candidateCovarianceScheduleOrder T)
    (N T) ω ∂Problem520.μ
  let far (T : ℝ) := ∫ ω, candidateEulerBandFarMass (candidateEulerTopCutoff T) T (β * T)
    (candidateCovarianceScheduleLowerHeight T) (candidateCovarianceScheduleHeight T)
    (candidateCovarianceScheduleWidth T) ω ∂Problem520.μ
  let raw (T : ℝ) := c * Real.log T ^ (-(3 : ℝ) / 5)
  let budget (T : ℝ) := T ^ ((4 : ℝ) / 5) / 2
  have hn := hnear J ((le_max_left _ _).trans hJ) β c 1 hβ hc (by norm_num) N (by simpa using hN)
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
      (by positivity) (candidateCovarianceScheduleOrder T) (N T)
  · exact hsum

/-- The actual covariance failure is uniformly small for every grid of at
most T points. Its probability, near moments, and far moments are all proved. -/
theorem candidate_exists_scheduledGridDegreeControl_uniform_failure :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ β : ℝ, 1 ≤ β →
      ∀ (s : Finset ℕ) (η : s → Bool) (ε : ℝ), 0 < ε →
      ∀ᶠ T : ℝ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T →
        (candidateCylinderLaw s η).real
          (candidateCovarianceScheduledGridDegreeControl J β T n)ᶜ ≤ ε := by
  classical
  obtain ⟨J₀, hrate⟩ := grid_degree_selection_rate
  refine ⟨J₀, ?_⟩
  intro J hJ β hβ s η ε hε
  let bad (T : ℝ) (n : ℕ) : Prop := (n : ℝ) ≤ T ∧
    ¬(candidateCylinderLaw s η).real
      (candidateCovarianceScheduledGridDegreeControl J β T n)ᶜ ≤ ε
  let N (T : ℝ) : ℕ := if h : ∃ n, bad T n then h.choose else 0
  have hN : ∀ᶠ T : ℝ in atTop, (N T : ℝ) ≤ T := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    dsimp only [N]
    split_ifs with h
    · exact h.choose_spec.1
    · simpa using hT
  have hh := (hrate J hJ β hβ N hN s η).eventually (gt_mem_nhds hε)
  filter_upwards [hh] with T hT
  intro n hn
  by_contra hbad
  have hex : ∃ n, bad T n := ⟨n, hn, hbad⟩
  have hchosen : ¬(candidateCylinderLaw s η).real
      (candidateCovarianceScheduledGridDegreeControl J β T (N T))ᶜ ≤ ε := by
    simpa only [N, dif_pos hex] using hex.choose_spec.2
  exact hchosen hT.le

end
end Erdos.Problem1144
