import Erdos.Problem1144.HarperCandidateGaussianLowerTail
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped Topology

namespace Erdos.Problem1144

/-- If the squared threshold is negligible compared with the logarithm of
the number of coordinates, the standard-normal tail budget diverges. No
sign restriction on the threshold is needed for this deterministic estimate. -/
theorem candidate_tendsto_mul_gaussianPDFReal_atTop
    {α : Type*} {l : Filter α} {m K : α → ℝ}
    (hm : Tendsto m l atTop)
    (hK : (fun t ↦ K t ^ 2) =o[l] (fun t ↦ Real.log (m t))) :
    Tendsto (fun t ↦ m t * gaussianPDFReal 0 1 (Real.sqrt 2 * K t + 1)) l atTop := by
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹
  have hc : 0 < c := by dsimp only [c]; positivity
  have hlog : Tendsto (fun t ↦ Real.log (m t)) l atTop := Real.tendsto_log_atTop.comp hm
  have hhalf : Tendsto (fun t ↦ (1 / 2 : ℝ) * Real.log (m t) - 1) l atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right l (-1 : ℝ) (hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have hsmall : Tendsto (fun t ↦ c * Real.exp ((1 / 2 : ℝ) * Real.log (m t) - 1)) l atTop :=
    (Real.tendsto_exp_atTop.comp hhalf).const_mul_atTop hc
  apply tendsto_atTop_mono' l _ hsmall
  filter_upwards [hm.eventually_ge_atTop 1,
    hK.bound (by norm_num : (0 : ℝ) < 1 / 4)] with t hm1 hk
  have hm0 : 0 < m t := by linarith
  have hlog0 : 0 ≤ Real.log (m t) := Real.log_nonneg hm1
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (K t)), abs_of_nonneg hlog0] at hk
  have hs : (Real.sqrt 2 * K t) ^ 2 = 2 * K t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hquad : (Real.sqrt 2 * K t + 1) ^ 2 / 2 ≤ 2 * K t ^ 2 + 1 := by
    nlinarith [sq_nonneg (Real.sqrt 2 * K t - 1)]
  have he : (1 / 2 : ℝ) * Real.log (m t) - 1 ≤
      Real.log (m t) - (Real.sqrt 2 * K t + 1) ^ 2 / 2 := by linarith
  calc
    _ ≤ c * Real.exp (Real.log (m t) - (Real.sqrt 2 * K t + 1) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hc.le
    _ = m t * gaussianPDFReal 0 1 (Real.sqrt 2 * K t + 1) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hm0]
      simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, c]
      rw [neg_div]
      ring

end Erdos.Problem1144
