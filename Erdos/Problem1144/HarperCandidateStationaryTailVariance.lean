import Erdos.Problem1144.HarperCandidateStationaryTailArithmetic
import Erdos.Problem1144.HarperCandidateStationaryTailIntegral

open MeasureTheory Set

namespace Erdos.Problem1144

/-- The common variance bound in candidate equation (23). -/
noncomputable def candidateCompleteStationaryTailVariance (ω : Omega) (c T W : ℝ) : ℝ :=
  (1 / T) * ∫ t in Ioi (c * T), Real.exp (-2 * W * t / T) *
    harperCandidateLogProcess ω t ^ 2

/-- The square-error contribution in equation (24), including its factor two. -/
noncomputable def candidateStationarySquareErrorVariance (ω : Omega) (c T W : ℝ) : ℝ :=
  (2 / T) * ∫ t in Ioi (c * T), Real.exp (-2 * W * t / T) *
    candidateLogSquareError ω t ^ 2

theorem measurable_candidateCompleteStationaryTailVariance (c T W : ℝ) :
    Measurable fun ω => candidateCompleteStationaryTailVariance ω c T W := by
  have hm : Measurable fun z : Omega × ℝ =>
      Real.exp (-2 * W * z.2 / T) * harperCandidateLogProcess z.1 z.2 ^ 2 :=
    (by fun_prop : Measurable fun z : Omega × ℝ => Real.exp (-2 * W * z.2 / T)).mul
      (measurable_harperCandidateLogProcess.pow_const 2)
  exact measurable_const.mul (StronglyMeasurable.integral_prod_right
    (f := fun ω t => Real.exp (-2 * W * t / T) * harperCandidateLogProcess ω t ^ 2)
    hm.stronglyMeasurable (ν := volume.restrict (Ioi (c * T)))).measurable

theorem measurable_candidateStationarySquareErrorVariance (c T W : ℝ) :
    Measurable fun ω => candidateStationarySquareErrorVariance ω c T W := by
  have hm : Measurable fun z : Omega × ℝ =>
      Real.exp (-2 * W * z.2 / T) * candidateLogSquareError z.1 z.2 ^ 2 :=
    (by fun_prop : Measurable fun z : Omega × ℝ => Real.exp (-2 * W * z.2 / T)).mul
      (measurable_candidateLogSquareError.pow_const 2)
  exact measurable_const.mul (StronglyMeasurable.integral_prod_right
    (f := fun ω t => Real.exp (-2 * W * t / T) * candidateLogSquareError ω t ^ 2)
    hm.stronglyMeasurable (ν := volume.restrict (Ioi (c * T)))).measurable

theorem candidateStationarySquareErrorVariance_nonneg
    (ω : Omega) (c W : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ candidateStationarySquareErrorVariance ω c T W := by
  unfold candidateStationarySquareErrorVariance
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => by positivity)

private theorem candidate_squareError_tail_product_integrable
    (c : ℝ) {T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    Integrable (fun z : ℝ × Omega => Real.exp (-2 * W * z.1 / T) *
      candidateLogSquareError z.2 z.1 ^ 2) ((volume.restrict (Ioi (c * T))).prod mu) := by
  have hm : Measurable fun z : ℝ × Omega => Real.exp (-2 * W * z.1 / T) *
      candidateLogSquareError z.2 z.1 ^ 2 :=
    (by fun_prop : Measurable fun z : ℝ × Omega => Real.exp (-2 * W * z.1 / T)).mul
      ((measurable_candidateLogSquareError.comp measurable_swap).pow_const 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun t => (candidate_integrable_logSquareError_sq t).const_mul (Real.exp (-2 * W * t / T))
  · have he : IntegrableOn (fun t => Real.exp (-2 * W * t / T)) (Ioi (c * T)) := by
      simpa only [div_mul_eq_mul_div] using
        integrableOn_exp_mul_Ioi (a := -2 * W / T) (div_neg_of_neg_of_pos (by nlinarith) hT) (c * T)
    apply he.mono' hm.norm.aestronglyMeasurable.integral_prod_right'
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)),
      integral_const_mul]
    exact mul_le_of_le_one_right (Real.exp_pos _).le
      (candidate_integral_logSquareError_sq_le_one t)

/-- The literal error tail is integrable and has the exact exponential
first-moment bound in equation (24). -/
theorem candidate_integral_stationarySquareErrorVariance_le
    (c : ℝ) {T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    Integrable (fun ω => candidateStationarySquareErrorVariance ω c T W) mu ∧
      (∫ ω, candidateStationarySquareErrorVariance ω c T W ∂mu) ≤
        Real.exp (-2 * c * W) / W := by
  have hp := candidate_squareError_tail_product_integrable c hT hW
  refine ⟨hp.integral_prod_right.const_mul _, ?_⟩
  unfold candidateStationarySquareErrorVariance
  rw [integral_const_mul, ← integral_integral_swap hp]
  have he : IntegrableOn (fun t => Real.exp (-2 * W * t / T)) (Ioi (c * T)) := by
    simpa only [div_mul_eq_mul_div] using
      integrableOn_exp_mul_Ioi (a := -2 * W / T) (div_neg_of_neg_of_pos (by nlinarith) hT) (c * T)
  have hle := integral_mono_ae hp.integral_prod_left he
    (by filter_upwards [] with t
        rw [integral_const_mul]
        exact mul_le_of_le_one_right (Real.exp_pos _).le
          (candidate_integral_logSquareError_sq_le_one t))
  apply (mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2 / T)).trans_eq
  have hexp : (fun t : ℝ => Real.exp (-2 * W * t / T)) =
      (fun t => Real.exp ((-2 * W / T) * t)) := by funext t; congr 1; ring
  rw [hexp, integral_exp_mul_Ioi (div_neg_of_neg_of_pos (by nlinarith) hT)]
  have hphase : (-2 * W / T) * (c * T) = -2 * c * W := by field_simp
  rw [hphase]
  field_simp

/-- Conditioning costs only the reciprocal mass of the fixed cylinder. -/
theorem candidateCylinderLaw_integral_stationarySquareErrorVariance_le
    (s : Finset ℕ) (η : s → Bool) (c : ℝ) {T W : ℝ}
    (hT : 0 < T) (hW : 0 < W) :
    Integrable (fun ω => candidateStationarySquareErrorVariance ω c T W)
      (candidateCylinderLaw s η) ∧
    (∫ ω, candidateStationarySquareErrorVariance ω c T W ∂candidateCylinderLaw s η) ≤
      Real.exp (-2 * c * W) / (W * mu.real (candidateCylinder s η)) := by
  have hi := candidate_integral_stationarySquareErrorVariance_le c hT hW
  have h := candidateCylinderLaw_integral_nonneg_le s η hi.1
    (fun ω => candidateStationarySquareErrorVariance_nonneg ω c W hT.le)
  refine ⟨h.1, h.2.trans ?_⟩
  simpa only [div_div] using div_le_div_of_nonneg_right hi.2
    (measureReal_nonneg (μ := mu) (s := candidateCylinder s η))

/-- Candidate equation (24), conditional only on the explicit weighted
bound. The error integrability and complete-path regularity are proved. -/
theorem candidateCylinderLaw_ae_stationaryTailVariance_le_of_weighted_bound
    (s : Finset ℕ) (η : s → Bool) {c T W K : ℝ}
    (hc : 0 ≤ c) (hT : 1 ≤ T) (hj : 1 ≤ Real.log T)
    (hW : 1 ≤ W) (hK : 0 ≤ K) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, CandidateWeightedLogBound ω K →
      candidateCompleteStationaryTailVariance ω c T W ≤
        2 * K ^ 2 * candidateStationaryTailConstant c * Real.log T ^ 2 *
          Real.exp (-2 * c * W) / W + candidateStationarySquareErrorVariance ω c T W := by
  have hTpos : 0 < T := by linarith
  have hWpos : 0 < W := by linarith
  have herr : ∀ᵐ ω ∂candidateCylinderLaw s η, IntegrableOn
      (fun t => Real.exp (-2 * W * t / T) * candidateLogSquareError ω t ^ 2)
      (Ioi (c * T)) := ProbabilityTheory.cond_absolutelyContinuous.ae_le
        (candidate_squareError_tail_product_integrable c hTpos hWpos).prod_left_ae
  have hpaths := candidateCylinderLaw_ae_damped_L1_L2 s η (div_pos hWpos hTpos)
  filter_upwards [herr, hpaths] with ω he hpath
  intro hR
  have ha : IntegrableOn (fun t => Real.exp (-2 * W * t / T) *
      harperCandidateLogProcess ω t ^ 2) (Ioi (c * T)) := by
    have h := (memLp_two_iff_integrable_sq hpath.1.2.1).mp hpath.1.2
    convert h.integrableOn using 1
    funext t
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  have hl := candidate_stationary_log_square_tail_bound hc hT hj hW
  have hu := (hl.1.const_mul (2 * K ^ 2)).add (he.const_mul 2)
  have hbound := integral_mono_ae ha hu
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 ≤ t := (mul_nonneg hc hTpos.le).trans ht.le
        have h := mul_le_mul_of_nonneg_left
          (candidateLogProcess_sq_le_of_weighted_bound hK hR ht0)
          (Real.exp_pos (-2 * W * t / T)).le
        convert h using 1 <;> dsimp only [Pi.add_apply] <;> ring)
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hl.1.const_mul (2 * K ^ 2)) (he.const_mul 2),
    integral_const_mul, integral_const_mul] at hbound
  have hscaled := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 1 / T)
  have hlog := mul_le_mul_of_nonneg_left hl.2 (by positivity : 0 ≤ 2 * K ^ 2)
  unfold candidateCompleteStationaryTailVariance candidateStationarySquareErrorVariance
  linear_combination hscaled + hlog

end Erdos.Problem1144
