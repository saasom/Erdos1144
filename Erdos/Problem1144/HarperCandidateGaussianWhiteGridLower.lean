import Erdos.Problem1144.HarperCandidateCovarianceScheduledGridLower
import Erdos.Problem1144.HarperCandidateCovarianceScheduledRetainedVariance
import Erdos.Problem1144.HarperCandidateCovarianceScheduledRetainedLinearTransfer

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

private theorem retained_crossing_integrable {n : ℕ}
    (Q : Measure Omega) [IsProbabilityMeasure Q] (J : ℕ) (β : ℝ) (u : Fin n → ℝ)
    {T : ℝ} (hT : 0 < T) (selector : Omega → Finset (Fin n))
    (hs : ∀ i, MeasurableSet {ω | i ∈ selector ω}) (K : ℝ) :
    Integrable (candidateCovarianceScheduledRetainedCrossing J β u T selector K) Q := by
  let S := candidateCovarianceRetainedFrequencySet
    (candidateCovarianceScheduleStart J T) (candidateCovarianceScheduleLength J T)
    (candidateCovarianceScheduleDepth T) (candidateCovarianceScheduleHeight T)
    (Real.log T) (candidateCovarianceScheduleSelected J T)
  let f := fun (i : Fin n) ω => candidateEulerScreenWhiteKernel
    (candidateEulerTopCutoff T) ω (S ω) T (β * T) (u i)
  have hm (i : Fin n) : Measurable (Function.uncurry (f i)) :=
    candidate_measurable_eulerScreenWhiteKernel_joint _ S
      (candidate_measurableSet_retainedFrequencyGraph _ _ _ _ _ _) _ _ _
  have h2 (ω : Omega) (i : Fin n) : MemLp (f i ω) 2 :=
    candidate_memLp_eulerScreenWhiteKernel _ ω
      (candidate_measurableSet_retainedFrequencySet _ _ _ _ _ _ ω)
      (candidateCovarianceScheduleHeight T)
      (candidate_retainedFrequencySet_subset_band _ _ _ _ _ _ ω le_rfl) _ _ hT
  exact candidate_integrable_gaussian_selected_probability Q
    (candidate_measurable_random_gram volume f hm)
    (fun ω => candidateWeightedGram_posSemidef volume (fun i => f i ω) (fun _ => 1)
      (fun i j => by simpa only [one_mul] using (h2 ω i).integrable_mul (h2 ω j))
      (ae_of_all _ fun _ => Or.inl zero_le_one)) selector hs K

private theorem retained_crossing_antitone {n : ℕ}
    (Q : Measure Omega) [IsProbabilityMeasure Q] (J : ℕ) (β : ℝ) (u : Fin n → ℝ)
    {T : ℝ} (hT : 0 < T) (selector : Omega → Finset (Fin n))
    (hs : ∀ i, MeasurableSet {ω | i ∈ selector ω}) {K L : ℝ} (hKL : K ≤ L) :
    (∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector L ω ∂Q) ≤
      ∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector K ω ∂Q := by
  apply integral_mono (retained_crossing_integrable Q J β u hT selector hs L)
    (retained_crossing_integrable Q J β u hT selector hs K)
  intro ω
  exact measureReal_mono fun _ ⟨i, hi, hx⟩ => ⟨i, hi, hKL.trans_lt hx⟩

/-- The squarefree white law has a fixed positive crossing mass at every
fixed iterated-logarithm threshold. This is uniform over all affine grids
with at most T coordinates and every measurable selector containing at least
2*T^(9/10) points. All variance, degree, screen and Perron losses are paid. -/
theorem candidate_exists_squarefreeWhite_linear_grid_crossing :
    ∃ p : ℝ, 0 < p ∧ ∀ α β : ℝ, 1 < α → α ≤ β → β < 4 / 3 →
      ∀ (s : Finset ℕ) (η : s → Bool) (A : ℝ), 0 ≤ A → ∀ ℓ : ℕ,
      ∀ᶠ T : ℝ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T → ∀ origin : ℝ,
      (∀ i : Fin n, origin + i * (2 * Real.pi) ∈ Icc (α * T) (β * T)) →
      ∀ selector : Omega → Finset (Fin n),
      (∀ i, MeasurableSet {ω | i ∈ selector ω}) →
      (∀ ω, 2 * T ^ ((9 : ℝ) / 10) ≤ (selector ω).card) →
      p ≤ ∫ ω, candidateComparisonWhiteCrossing true
        (fun i : Fin n => origin + i * (2 * Real.pi)) T selector
        (A * Real.log (1 + Real.log T) ^ ℓ) ω ∂candidateCylinderLaw s η := by
  obtain ⟨δ, hδ, JV, hvar⟩ :=
    candidate_exists_scheduledRetainedVariance_probability_linear_grid
  obtain ⟨JD, hdeg⟩ := candidate_exists_scheduledGridDegreeControl_uniform_failure
  obtain ⟨JC, hcomp⟩ := candidate_exists_scheduledRetained_white_crossing_linear_grid
  let J := max JV (max JD JC)
  have hJV : JV ≤ J := le_max_left _ _
  have hJD : JD ≤ J := (le_max_left _ _).trans (le_max_right _ _)
  have hJC : JC ≤ J := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ / 16, by positivity, ?_⟩
  intro α β hα hαβ hβ s η A hA ℓ
  obtain ⟨v, hv, hvar⟩ := hvar J hJV α β hα hαβ hβ s η
  have hβ1 : 1 ≤ β := hα.le.trans hαβ
  have hnlarge := ((tendsto_rpow_atTop (by norm_num : 0 < (9 : ℝ) / 10)).const_mul_atTop
    (by norm_num : (0 : ℝ) < 2)).eventually_ge_atTop (1 / (δ / 16))
  filter_upwards [hvar (δ / 4) (by positivity),
    hdeg J hJD β hβ1 s η (δ / 4) (by positivity),
    hcomp J hJC α β hαβ hβ s η (δ / 16) (by positivity),
    candidate_eventually_grid_gaussian_size hv (A + 2) (max ℓ 3),
    candidate_eventually_covarianceThreshold_le_retained_half_variance hv,
    candidate_eventually_covarianceSchedule_degreeBudget_le_floor,
    candidate_eventually_covarianceSchedule_room J 0,
    candidate_eventually_loglog_threshold_add_comparison_margins_le hA ℓ,
    hnlarge, eventually_gt_atTop (1 : ℝ)]
    with T hvarT hdegT hcompT hsizeT hθ hdegree horder hmargin hnlarge hT
  intro n hn origin hpoints selector hselector hcard
  let u := fun i : Fin n => origin + i * (2 * Real.pi)
  let K := A * Real.log (1 + Real.log T) ^ ℓ
  let L := (A + 2) * Real.log (1 + Real.log T) ^ (max ℓ 3)
  have hT0 : 0 < T := by linarith
  have hq : 0 < Real.log T := Real.log_pos hT
  have hlog : 0 ≤ Real.log (1 + Real.log T) := Real.log_nonneg (by linarith)
  have hvT : 0 < (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 4 := by positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hlow := candidate_scheduledGrid_retained_crossing_lower (candidateCylinderLaw s η)
    J β T n origin selector hselector hT hβ1 hvT hL
    (by simpa using horder) (by convert hθ using 1 <;> ring) hdegree
    (fun ω => hsizeT (selector ω).card (hcard ω))
  have hvprob := hvarT n hn u hpoints
  have hdprob := hdegT n hn
  have hret : δ / 8 ≤
      ∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector L ω
        ∂candidateCylinderLaw s η := by
    change (_ - _) / 4 ≤
      ∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector L ω
        ∂candidateCylinderLaw s η at hlow
    linarith
  have hnlow : 1 / (δ / 16) ≤ (n : ℝ) := by
    have hc : ((selector (fun _ => false)).card : ℝ) ≤ n := by
      have hh : (selector (fun _ => false)).card ≤ n := by
        simpa only [Fintype.card_fin] using
          (Finset.card_le_univ (s := selector (fun _ => false)))
      exact_mod_cast hh
    exact hnlarge.trans ((hcard (fun _ => false)).trans hc)
  have htransfer := hcompT n hnlow hn u hpoints selector hselector K
  have hm := retained_crossing_antitone (candidateCylinderLaw s η) J β u hT0
    selector hselector hmargin
  change (∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector L ω
      ∂candidateCylinderLaw s η) ≤
    ∫ ω, candidateCovarianceScheduledRetainedCrossing J β u T selector
      (K + Real.log (Real.log T) ^ 3 + T ^ (-(1 : ℝ) / 2)) ω
      ∂candidateCylinderLaw s η at hm
  change δ / 16 ≤ ∫ ω, candidateComparisonWhiteCrossing true u T selector K ω
    ∂candidateCylinderLaw s η
  linarith

end
end Erdos.Problem1144
