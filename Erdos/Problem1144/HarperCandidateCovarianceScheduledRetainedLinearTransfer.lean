import Erdos.Problem1144.HarperCandidateCovarianceScheduledRetained

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The retained-to-white crossing transfer is uniform over arbitrary
finite grids of at most linear cardinality, including the translated grids
at the smaller stationary time scale. The explicit lower cardinality pays
the exact Gaussian residual `1/(2n)`; all other losses vanish with time. -/
theorem candidate_exists_scheduledRetained_white_crossing_linear_grid :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ α β : ℝ,
      α ≤ β → β < 4 / 3 → ∀ (s : Finset ℕ) (η : s → Bool)
      (ε : ℝ), 0 < ε → ∀ᶠ T : ℝ in atTop,
      ∀ n : ℕ, 1 / ε ≤ (n : ℝ) → (n : ℝ) ≤ T → ∀ u : Fin n → ℝ,
      (∀ i, u i ∈ Icc (α * T) (β * T)) →
      ∀ selector : Omega → Finset (Fin n),
        (∀ i, MeasurableSet {ω | i ∈ selector ω}) → ∀ K : ℝ,
      (∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector
        (K + Real.log (Real.log T) ^ 3 + T ^ (-(1 : ℝ) / 2)) ω
        ∂candidateCylinderLaw s η) ≤
      (∫ ω, candidateComparisonWhiteCrossing true u T selector K ω
        ∂candidateCylinderLaw s η) + ε := by
  obtain ⟨J₀, herr⟩ := candidate_exists_scheduledRetainedError_decay
  obtain ⟨C, hC, hperron⟩ := candidate_exists_topEulerBandWhiteTotalError_bound
  refine ⟨J₀, ?_⟩
  intro J hJ α β hαβ hβ s η ε hε
  let d := mu.real (candidateCylinder s η)
  let E := fun T => ∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂mu
  let mesh := fun T => (candidateCylinderLaw s η).real
    (candidateCovarianceCommonMeshEvent (candidateCovarianceScheduleStart J T)
      (candidateCovarianceScheduleLength J T) (candidateCovarianceScheduleHeight T)
      (Real.log T))ᶜ
  have hd : 0 < d := ENNReal.toReal_pos (mu_candidateCylinder_ne_zero s η) (measure_ne_top _ _)
  have he : Tendsto (fun T => 8 * Real.log T * E T /
      (d * Real.log (Real.log T) ^ 6)) atTop (𝓝 0) := by
    have hh := (herr J hJ).2.const_mul (8 / d)
    simp only [mul_zero] at hh
    convert hh using 1
    funext T
    dsimp only [E]
    ring
  have hp : Tendsto (fun T : ℝ => C / (d * T)) atTop (𝓝 0) := by
    have hh : Tendsto (fun T : ℝ => (C / d) / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa only [div_div] using hh
  have hmesh : Tendsto mesh atTop (𝓝 0) :=
    candidate_cylinder_scheduledCommonMesh_failure_tendsto_zero J s η
  have hl := (hmesh.add he).add hp
  simp only [add_zero] at hl
  have hε2 : 0 < ε / 2 := by positivity
  filter_upwards [hl.eventually (gt_mem_nhds hε2),
    candidate_eventually_covarianceSchedule_height_le_cubic J,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0,
    eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    eventually_ge_atTop (2 : ℝ)] with T hsmall hH hlog hTbase hT2
  intro n hnlow hn u hpoints selector hselector K
  have hn0R : (0 : ℝ) < n := (one_div_pos.mpr hε).trans_le hnlow
  have hn0 : 0 < n := by exact_mod_cast hn0R
  letI : NeZero n := ⟨by omega⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hT : 0 < T := by linarith
  have hs : 0 < Real.log (Real.log T) := hlog
  have hEn : 0 ≤ E T := integral_nonneg fun ω =>
    candidate_retainedError_nonneg _ _ _ _ _ _ hT.le _ ω
  have hu (i : Fin n) : u i ≤ β * T := (hpoints i).2
  have hu2 (i : Fin n) : u i ≤ 3 / 2 * T :=
    (hu i).trans (mul_le_mul_of_nonneg_right (by linarith : β ≤ 3 / 2) hT.le)
  have hy (i : Fin n) : ⌊Real.exp (u i - T)⌋₊ ≤ candidateEulerTopCutoff T :=
    candidateEulerTopCutoff_covers_prefix hTbase (hu2 i)
  have hlogn : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log T := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * (n : ℝ))
      (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 2))
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne'] at hh
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT2
    linarith
  have hscreen : 4 * Real.log (2 * (n : ℝ)) * E T /
      (d * (Real.log (Real.log T) ^ 3) ^ 2) ≤
      8 * Real.log T * E T / (d * Real.log (Real.log T) ^ 6) := by
    rw [show (Real.log (Real.log T) ^ 3) ^ 2 = Real.log (Real.log T) ^ 6 by ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlogn (by norm_num : (0 : ℝ) ≤ 4)) hEn
    exact hh.trans_eq (by ring)
  have htotal := hperron u T (T ^ 3) (β * T) hTbase (pow_pos hT _) hu2 hu
  simp only [Fintype.card_fin] at htotal
  have hgap : (T ^ (-(1 : ℝ) / 2)) ^ 2 = T⁻¹ := by
    rw [← Real.rpow_natCast (T ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hT.le]
    norm_num [Real.rpow_neg_one]
  have hperronBound : (∫ ω, candidateEulerBandWhiteTotalError (candidateEulerTopCutoff T)
      u (T ^ 3) T (β * T) ω ∂mu) / (d * (T ^ (-(1 : ℝ) / 2)) ^ 2) ≤ C / (d * T) := by
    rw [hgap]
    calc
      _ ≤ (C * (n : ℝ) / T ^ 3) / (d * T⁻¹) :=
        div_le_div_of_nonneg_right htotal (by positivity)
      _ = C * (n : ℝ) / (d * T ^ 2) := by field_simp
      _ ≤ C * T / (d * T ^ 2) := by gcongr
      _ = C / (d * T) := by field_simp
  have hresidual : 1 / (2 * (n : ℝ)) ≤ ε / 2 := by
    have hh := (div_le_iff₀ hε).mp hnlow
    apply (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
    nlinarith
  have hb := candidate_retainedEuler_white_selected_crossing_le s η
    (candidateEulerTopCutoff T) (candidateCovarianceScheduleStart J T)
    (candidateCovarianceScheduleLength J T) (candidateCovarianceScheduleDepth T)
    (candidateCovarianceScheduleHeight T) (Real.log T) (candidateCovarianceScheduleSelected J T)
    u hH (pow_pos hT 3) hT (β * T) hu hy selector hselector K
    (pow_pos hs 3) (Real.rpow_pos_of_pos hT (-(1 : ℝ) / 2))
  simp only [Fintype.card_fin] at hb
  change (∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector
    (K + Real.log (Real.log T) ^ 3 + T ^ (-(1 : ℝ) / 2)) ω ∂candidateCylinderLaw s η) ≤
    (∫ ω, candidateComparisonWhiteCrossing true u T selector K ω ∂candidateCylinderLaw s η) +
    mesh T + 4 * Real.log (2 * (n : ℝ)) * E T / (d * (Real.log (Real.log T) ^ 3) ^ 2) +
    1 / (2 * (n : ℝ)) + (∫ ω, candidateEulerBandWhiteTotalError (candidateEulerTopCutoff T)
      u (T ^ 3) T (β * T) ω ∂mu) / (d * (T ^ (-(1 : ℝ) / 2)) ^ 2) at hb
  change mesh T + 8 * Real.log T * E T / (d * Real.log (Real.log T) ^ 6) +
    C / (d * T) < ε / 2 at hsmall
  linarith

end
end Erdos.Problem1144
