import Erdos.Problem1144.HarperCandidateScheduleThinning
import Erdos.Problem1144.HarperCandidateGaussianVarianceAsymptotics

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace Erdos.Problem1144

/-- The actual retained factory and rounded degree supply the Gaussian size
test for every fixed iterated-logarithm threshold at the retained variance floor. -/
theorem candidateSchedule_eventually_retained_gaussian_size
    {κ ρ v : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hv : 0 < v)
    (A : ℝ) (ℓ : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ∀ (F : Omega → Fin (candidateScheduleM κ T) → ℝ) (b : ℝ) (ω : Omega),
      Real.log 2 ≤ (candidateRetainedIndices F b ρ ω).card /
        (⌊T ^ ((4 : ℝ) / 5)⌋₊ + 1 : ℝ) * gaussianPDFReal 0 1
          (Real.sqrt 2 * ((A * Real.log (1 + Real.log T) ^ ℓ) /
            Real.sqrt ((v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 4)) + 1) := by
  have hc := candidateSchedule_retained_card_div_degree_ge_rpow hκ hρ hρ1
    (a := (4 : ℝ) / 5) (γ := (1 : ℝ) / 10) (by norm_num) (by norm_num)
  have hg := (candidate_tendsto_polynomialSize_gaussianPDF_loglog_threshold
    (v := v / 4) (γ := (1 : ℝ) / 10) (by positivity) (by norm_num) A ℓ).eventually_ge_atTop
      (Real.log 2)
  filter_upwards [hc, hg, eventually_gt_atTop (0 : ℝ)] with T hc hg hT
  intro F b ω
  have hcard := hc F b ω ⌊T ^ ((4 : ℝ) / 5)⌋₊
    (Nat.floor_le (Real.rpow_nonneg hT.le _))
  have hh := hg.trans (mul_le_mul_of_nonneg_right hcard (gaussianPDFReal_nonneg _ _ _))
  simpa only [show v / 4 * (1 + Real.log T) ^ (-(1 : ℝ) / 2) =
    (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 4 by ring] using hh

/-- The two comparison margins fit within another fixed iterated-logarithm
threshold. The exponent three is the one already paid by the deletion rate. -/
theorem candidate_eventually_loglog_threshold_add_comparison_margins_le
    {A : ℝ} (hA : 0 ≤ A) (ℓ : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      A * Real.log (1 + Real.log T) ^ ℓ + Real.log (Real.log T) ^ 3 +
        T ^ (-(1 : ℝ) / 2) ≤ (A + 2) * Real.log (1 + Real.log T) ^ (max ℓ 3) := by
  have hL : Tendsto (fun T : ℝ => Real.log (1 + Real.log T)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left atTop 1 Real.tendsto_log_atTop)
  filter_upwards [hL.eventually_ge_atTop 1, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℝ)] with T hL hq hT
  have hq0 : 0 < Real.log T := by linarith
  have hlog : Real.log (Real.log T) ≤ Real.log (1 + Real.log T) :=
    Real.log_le_log hq0 (by linarith)
  have hp := pow_le_pow_right₀ hL (le_max_left ℓ 3)
  have hp3 := pow_le_pow_right₀ hL (le_max_right ℓ 3)
  have hmargin : Real.log (Real.log T) ^ 3 ≤ Real.log (1 + Real.log T) ^ (max ℓ 3) :=
    (pow_le_pow_left₀ (Real.log_nonneg hq) hlog 3).trans hp3
  have hsmall : T ^ (-(1 : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hT (by norm_num)
  have hone : 1 ≤ Real.log (1 + Real.log T) ^ (max ℓ 3) := one_le_pow₀ hL
  nlinarith [mul_le_mul_of_nonneg_left hp hA]

end Erdos.Problem1144
