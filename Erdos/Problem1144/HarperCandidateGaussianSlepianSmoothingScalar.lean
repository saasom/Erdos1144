import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- A decreasing smooth approximation of the closed one-sided event `x ≤ K`.
The shift by one makes the value exactly one at the boundary. -/
noncomputable def candidateSlepianCutoff (K ε x : ℝ) : ℝ :=
  Real.smoothTransition ((K - x) / ε + 1)

theorem candidate_slepianCutoff_contDiff (K ε : ℝ) {r : ℕ∞} :
    ContDiff ℝ r (candidateSlepianCutoff K ε) := by
  unfold candidateSlepianCutoff
  fun_prop

theorem candidate_slepianCutoff_nonneg (K ε x : ℝ) :
    0 ≤ candidateSlepianCutoff K ε x := Real.smoothTransition.nonneg _

theorem candidate_slepianCutoff_le_one (K ε x : ℝ) :
    candidateSlepianCutoff K ε x ≤ 1 := Real.smoothTransition.le_one _

theorem candidate_slepianCutoff_one {K ε x : ℝ} (hε : 0 < ε) (hx : x ≤ K) :
    candidateSlepianCutoff K ε x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h := div_nonneg (sub_nonneg.mpr hx) hε.le
  linarith

theorem candidate_slepianCutoff_zero {K ε x : ℝ} (hε : 0 < ε) (hx : K + ε ≤ x) :
    candidateSlepianCutoff K ε x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h : (K - x) / ε ≤ -1 := (div_le_iff₀ hε).mpr (by linarith)
  linarith

theorem candidate_slepianCutoff_antitone (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Antitone (candidateSlepianCutoff K ε) := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  exact add_le_add (div_le_div_of_nonneg_right (sub_le_sub_left hxy K) hε.le) le_rfl

theorem candidate_slepianCutoff_deriv_nonpos (K : ℝ) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    deriv (candidateSlepianCutoff K ε) x ≤ 0 :=
  (candidate_slepianCutoff_antitone K hε).deriv_nonpos

/-- The derivative vanishes outside the transition interval. -/
theorem candidate_slepianCutoff_deriv_hasCompactSupport (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (deriv (candidateSlepianCutoff K ε)) := by
  apply HasCompactSupport.intro (K := Icc K (K + ε)) isCompact_Icc
  intro x hx
  have hx' : x < K ∨ K + ε < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hx
  rcases hx' with hx | hx
  · apply HasDerivAt.deriv
    apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact candidate_slepianCutoff_one hε hy.le
  · apply HasDerivAt.deriv
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact candidate_slepianCutoff_zero hε hy.le

/-- Both derivatives needed by finite Gaussian interpolation are globally
bounded. The bounds may depend on the positive smoothing width. -/
theorem candidate_slepianCutoff_derivative_bounds (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
      ‖deriv (candidateSlepianCutoff K ε) x‖ ≤ B ∧
      ‖deriv (deriv (candidateSlepianCutoff K ε)) x‖ ≤ B := by
  have hc := candidate_slepianCutoff_deriv_hasCompactSupport K hε
  have hd : ContDiff ℝ 2 (candidateSlepianCutoff K ε) := candidate_slepianCutoff_contDiff K ε
  have hd' : ContDiff ℝ 1 (deriv (candidateSlepianCutoff K ε)) := hd.deriv'
  obtain ⟨B₁, hB₁⟩ := hc.exists_bound_of_continuous (hd.continuous_deriv (by norm_num))
  obtain ⟨B₂, hB₂⟩ := hc.deriv.exists_bound_of_continuous (hd'.continuous_deriv (by norm_num))
  refine ⟨max 0 (max B₁ B₂), le_max_left _ _, fun x ↦ ⟨?_, ?_⟩⟩
  · exact (hB₁ x).trans ((le_max_left B₁ B₂).trans (le_max_right _ _))
  · exact (hB₂ x).trans ((le_max_right B₁ B₂).trans (le_max_right _ _))

/-- At every scalar point the cutoff sequence is eventually exactly the
closed-event indicator, including points on the threshold. -/
theorem candidate_slepianCutoff_eventually_eq (K x : ℝ) :
    ∀ᶠ n : ℕ in atTop, candidateSlepianCutoff K (((n : ℝ) + 1)⁻¹) x =
      if x ≤ K then 1 else 0 := by
  have hε (n : ℕ) : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
  by_cases hx : x ≤ K
  · exact Eventually.of_forall fun n ↦ by
      rw [if_pos hx]
      exact candidate_slepianCutoff_one (hε n) hx
  · have hx' : 0 < x - K := sub_pos.mpr (lt_of_not_ge hx)
    have he : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).comp
          (tendsto_add_atTop_nat 1)
    filter_upwards [(tendsto_order.mp he).2 (x - K) hx'] with n hn
    rw [if_neg hx]
    exact candidate_slepianCutoff_zero (hε n) (by linarith)

theorem candidate_slepianCutoff_tendsto (K x : ℝ) :
    Tendsto (fun n : ℕ ↦ candidateSlepianCutoff K (((n : ℝ) + 1)⁻¹) x) atTop
      (𝓝 (if x ≤ K then 1 else 0)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [candidate_slepianCutoff_eventually_eq K x] with n hn
  exact hn.symm

/-- Products of cutoffs converge at every vector to the closed lower-box
indicator. No hypothesis excluding boundary atoms is needed. -/
theorem candidate_slepianCutoff_product_tendsto {ι : Type*} [Fintype ι]
    (K : ℝ) (x : ι → ℝ) :
    Tendsto (fun n : ℕ ↦ ∏ i, candidateSlepianCutoff K (((n : ℝ) + 1)⁻¹) (x i)) atTop
      (𝓝 (if ∀ i, x i ≤ K then 1 else 0)) := by
  classical
  have he : ∀ᶠ n : ℕ in atTop, ∀ i : ι,
      candidateSlepianCutoff K (((n : ℝ) + 1)⁻¹) (x i) = if x i ≤ K then 1 else 0 :=
    eventually_all.mpr fun i ↦ candidate_slepianCutoff_eventually_eq K (x i)
  have hp : (∏ i : ι, if x i ≤ K then (1 : ℝ) else 0) =
      if ∀ i, x i ≤ K then 1 else 0 := by
    by_cases hx : ∀ i, x i ≤ K
    · simp [hx]
    · rw [if_neg hx]
      push_neg at hx
      obtain ⟨i, hi⟩ := hx
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg (not_le.mpr hi))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  simpa only [hn] using hp.symm

/-- Dominated convergence for the actual finite product test under any
finite measure and any measurable random vector. Its limit is the probability
of the closed lower box, without continuity assumptions on the law. -/
theorem candidate_integral_slepianCutoff_product_tendsto
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (K : ℝ) :
    Tendsto (fun n : ℕ ↦ ∫ ω, ∏ i, candidateSlepianCutoff K (((n : ℝ) + 1)⁻¹) (X i ω) ∂μ)
      atTop (𝓝 (μ.real {ω | ∀ i, X i ω ≤ K})) := by
  classical
  let E : Set Ω := {ω | ∀ i, X i ω ≤ K}
  have hE : MeasurableSet E := by
    simp only [E, setOf_forall]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le (hX i) measurable_const
  have hlim (ω : Ω) :
      Tendsto (fun n : ℕ ↦ ∏ i, candidateSlepianCutoff K (((n : ℝ) + 1)⁻¹) (X i ω))
        atTop (𝓝 (E.indicator (fun _ ↦ (1 : ℝ)) ω)) := by
    simpa only [E, indicator_apply, mem_setOf_eq] using
      candidate_slepianCutoff_product_tendsto K (fun i ↦ X i ω)
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ : Ω ↦ (1 : ℝ))
    (fun n ↦ (Finset.measurable_prod _ fun i _ ↦
      ((candidate_slepianCutoff_contDiff K (((n : ℝ) + 1)⁻¹) (r := 0)).continuous.measurable.comp
        (hX i))).aestronglyMeasurable)
    (integrable_const (μ := μ) 1)
    (fun n ↦ ae_of_all _ fun ω ↦ ?_)
    (ae_of_all _ hlim)
  · simpa only [Function.comp_def, integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one] using h
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ ↦
    candidate_slepianCutoff_nonneg K _ (X i ω))]
  exact Finset.prod_le_one (fun i _ ↦ candidate_slepianCutoff_nonneg K _ (X i ω))
    (fun i _ ↦ candidate_slepianCutoff_le_one K _ (X i ω))

end Erdos.Problem1144
