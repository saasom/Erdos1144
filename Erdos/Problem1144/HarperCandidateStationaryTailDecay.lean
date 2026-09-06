import Erdos.Problem1144.HarperCandidateStationaryTailGaussian
import Erdos.Problem1144.HarperCandidateStationaryTailCovariance

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace Erdos.Problem1144

/-- The exact logarithmic decay calculation behind the admissible choice of
`κ`. For `γ = 1`, Gaussian maxima require the case `n = 3`. -/
theorem candidate_stationary_tail_log_power_tendsto_zero
    (n : ℕ) {c κ : ℝ} (hκ : 0 < κ) (hgap : (n : ℝ) < 2 * c * κ) :
    Tendsto (fun T : ℝ => Real.log T ^ n *
      Real.exp (-2 * c * candidateScheduleW κ T) / candidateScheduleW κ T)
      atTop (𝓝 0) := by
  have hx := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have he : Tendsto (fun T : ℝ =>
      Real.exp (-(2 * c * κ - n) * Real.log (Real.log T))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (hx.const_mul_atTop (sub_pos.mpr hgap)))
    simpa only [neg_mul] using h
  have hi := tendsto_inv_atTop_zero.comp (candidateScheduleW_tendsto hκ)
  have h := he.mul hi
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT
  have hp : Real.log T ^ n = Real.exp ((n : ℝ) * Real.log (Real.log T)) := by
    rw [Real.exp_nat_mul, Real.exp_log hT]
  rw [hp, div_eq_mul_inv, ← Real.exp_add]
  congr 2
  unfold candidateScheduleW
  ring

private theorem candidate_stationary_gaussian_error_budget_tendsto
    {c κ K r q : ℝ} (hκ : 0 < κ) (hgap : 3 / 2 < c * κ) :
    Tendsto (fun T : ℝ =>
      8 * Real.log T *
        (2 * K ^ 2 * candidateStationaryTailConstant c * Real.log T ^ 2 *
          Real.exp (-2 * c * candidateScheduleW κ T) / candidateScheduleW κ T +
          Real.exp (-2 * c * candidateScheduleW κ T) / (candidateScheduleW κ T * q)) /
          r ^ 2 + 1 / (2 * (candidateScheduleM κ T : ℝ))) atTop (𝓝 0) := by
  have h3 := (candidate_stationary_tail_log_power_tendsto_zero 3 (c := c) hκ (by norm_num; linarith)).const_mul (16 * K ^ 2 * candidateStationaryTailConstant c / r ^ 2)
  have h1 := (candidate_stationary_tail_log_power_tendsto_zero 1 (c := c) hκ (by norm_num; linarith)).const_mul (8 / (q * r ^ 2))
  have hm : Tendsto (fun T : ℝ => (candidateScheduleM κ T : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (candidateScheduleM_tendsto hκ)
  have hn := (hm.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).const_div_atTop 1
  have h := (h3.add h1).add hn
  simp only [mul_zero, zero_add] at h
  convert h using 1
  funext T
  simp only [div_eq_mul_inv, mul_inv_rev, pow_succ, pow_zero, mul_one]
  ring

/-- On every fixed measurable weighted-bound event, the actual omitted
stationary Gaussian field vanishes uniformly in probability along the
candidate's exact grid size and damping schedule. The only arithmetic
premise is the displayed weighted bound; no Atherfold theorem is asserted. -/
theorem candidate_stationary_gaussian_maximum_tendsto_zero_on_weighted_event
    {Ξ : ℝ → Type*} [∀ T, MeasurableSpace (Ξ T)]
    {P : (T : ℝ) → Measure (Ξ T)} [∀ T, IsProbabilityMeasure (P T)]
    (s : Finset ℕ) (η : s → Bool) {E : Set Omega} (hE : MeasurableSet E)
    {c κ K r : ℝ} (hc : 0 ≤ c) (hκ : 0 < κ) (hK : 0 ≤ K)
    (hgap : 3 / 2 < c * κ) (hr : 0 < r)
    (hR : ∀ᵐ ω ∂candidateCylinderLaw s η, ω ∈ E → CandidateWeightedLogBound ω K)
    (X : (T : ℝ) → Fin (candidateScheduleM κ T) → Omega × Ξ T → ℝ)
    (v : (T : ℝ) → Omega → Fin (candidateScheduleM κ T) → ℝ≥0)
    (hXm : ∀ T i, Measurable (X T i))
    (hX : ∀ T ω i, (P T).map (fun ξ => X T i (ω, ξ)) = gaussianReal 0 (v T ω i))
    (hv : ∀ᶠ T in atTop, ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ i,
      (v T ω i : ℝ) ≤ candidateCompleteStationaryTailVariance ω c T (candidateScheduleW κ T)) :
    Tendsto (fun T : ℝ => ((candidateCylinderLaw s η).prod (P T)).real
      {z | z.1 ∈ E ∧ ∃ i, r ≤ |X T i z|}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _
    (candidate_stationary_gaussian_error_budget_tendsto
      (K := K) (r := r) (q := mu.real (candidateCylinder s η)) hκ hgap)
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    (candidateScheduleW_tendsto hκ).eventually_ge_atTop 1,
    (candidateScheduleM_tendsto hκ).eventually_ge_atTop 1, hv] with T hT hj hW hm hvT
  have hTpos : 0 < T := by linarith
  have hmpos : 0 < candidateScheduleM κ T := by omega
  letI : Nonempty (Fin (candidateScheduleM κ T)) := ⟨⟨0, hmpos⟩⟩
  have hbound := candidate_stationary_gaussian_maximum_on_weighted_event_le
    s η hE hc (by linarith) hj hW hK hr hR (hXm T) (hX T) hvT
  simp only [Fintype.card_fin] at hbound
  apply hbound.trans
  have hmle : (candidateScheduleM κ T : ℝ) ≤ T := by
    apply (Nat.floor_le (by unfold candidateScheduleD; positivity)).trans
    have hD : candidateScheduleD κ T ≤ T := by
      apply (div_le_iff₀ (by positivity : 0 < candidateScheduleW κ T ^ 2)).mpr
      nlinarith [sq_nonneg (candidateScheduleW κ T - 1)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr
    have hp : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    exact hD.trans (le_mul_of_one_le_right hTpos.le hp)
  have hlog : Real.log (2 * (candidateScheduleM κ T : ℝ)) ≤ 2 * Real.log T := by
    have h := Real.log_le_log (by positivity : 0 < 2 * (candidateScheduleM κ T : ℝ))
      (mul_le_mul_of_nonneg_left hmle (by norm_num : (0 : ℝ) ≤ 2))
    rw [Real.log_mul (by norm_num) hTpos.ne'] at h
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
    linarith
  have hlog0 : 0 ≤ Real.log (2 * (candidateScheduleM κ T : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2 * candidateScheduleM κ T))
  have hq : 0 ≤ mu.real (candidateCylinder s η) := measureReal_nonneg
  have hC : 0 ≤ candidateStationaryTailConstant c := by
    unfold candidateStationaryTailConstant
    positivity
  have hcoef : 4 * Real.log (2 * (candidateScheduleM κ T : ℝ)) ≤ 8 * Real.log T :=
    by linarith
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (sq_nonneg r)
  exact mul_le_mul_of_nonneg_right hcoef (by positivity)

end Erdos.Problem1144
