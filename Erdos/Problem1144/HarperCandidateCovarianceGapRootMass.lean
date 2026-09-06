import Erdos.Problem1144.HarperCandidateCovarianceResonanceSliceGapMass
import Erdos.Problem520.HarperGaussianWalk

open MeasureTheory Set
open scoped Interval

namespace Erdos.Problem1144
noncomputable section

private theorem integral_abs_eq_twice {f : ℝ → ℝ} (hf : Continuous f)
    {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in Icc (-R) R, f |x|) = 2 * ∫ x in Icc (0 : ℝ) R, f x := by
  let g := fun x : ℝ => f |x|
  have hg : Continuous g := hf.comp continuous_abs
  have he : (∫ x in (-R)..(0 : ℝ), g x) = ∫ x in (0 : ℝ)..R, g x := by
    simpa only [g, abs_neg, neg_zero] using
      (intervalIntegral.integral_comp_neg (f := g) (a := (0 : ℝ)) (b := R)).symm
  have hp : (∫ x in (0 : ℝ)..R, g x) = ∫ x in (0 : ℝ)..R, f x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := (uIcc_of_le hR ▸ hx).1
    simp only [g, abs_of_nonneg hx0]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  change (∫ x in (-R)..R, g x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (-R) 0) (hg.intervalIntegrable 0 R), he, hp,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR]
  ring

/-- Cauchy--Schwarz integrates the actual square-root gap envelope with
only a logarithmic dependence on the top Euler cutoff. This includes the
sum-frequency channel at zero. -/
theorem candidate_integral_sqrt_gapEnvelope_abs_le (start stop : ℕ)
    {R : ℝ} (hR : 0 ≤ R) :
    let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
    let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
    let U := A * R + 3 * Real.log (1 + L * R)
    (∫ x in Icc (-R) R, Real.sqrt (candidateCovarianceGapEnvelope start stop |x|)) ≤
      2 * (Real.sqrt R * Real.sqrt U) := by
  let G := candidateCovarianceGapEnvelope start stop
  have hc := candidate_continuous_gapEnvelope start stop
  have hcs := Problem520.integral_sqrt_le_sqrt_measure_mul_integral
    (volume.restrict (Icc (0 : ℝ) R)) hc.measurable
    (ae_of_all _ fun x => candidate_gapEnvelope_nonneg start stop x) hc.integrableOn_Icc
  have hcs' : (∫ x in Icc (0 : ℝ) R, Real.sqrt (G x)) ≤
      Real.sqrt R * Real.sqrt (∫ x in Icc (0 : ℝ) R, G x) := by
    simpa only [measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
      sub_zero, ENNReal.toReal_ofReal hR] using hcs
  dsimp only
  rw [integral_abs_eq_twice hc.sqrt hR]
  exact mul_le_mul_of_nonneg_left
    (hcs'.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (candidate_integral_gapEnvelope_le start stop hR))
      (Real.sqrt_nonneg R))) (by norm_num)

end
end Erdos.Problem1144
