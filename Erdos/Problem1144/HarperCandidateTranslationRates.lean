import Erdos.Problem1144.HarperCandidateTranslationWhiteStep
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-!
# Uniform vanishing of the literal logarithmic step error

The finite-bin estimates retain a polynomial loss in the macroscopic
horizon. An exponentially fine mesh dominates every such fixed loss.
-/

/-- A deliberately coarse polynomial envelope for the explicit bin error.
The sharper finite-scale estimate remains available in the preceding module. -/
theorem candidate_whiteStep_bound_le_polynomial
    {T h D N : ℝ} (hT : 1 ≤ T) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hD : 0 ≤ D) (hN : 0 ≤ N) (hND : N ≤ D * T) :
    (4 / T) * h * (1 + N * Real.exp h) * (1 + (D * T + 1)) +
      (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * N * (1 + (D * T + 1)) ≤
        (D + 2) * (4 * (D + 1) * Real.exp 1 + 3 * D) * h * T ^ 2 := by
  have hT0 : 0 < T := by linarith
  have hT3 : 1 ≤ T ^ 3 := one_le_pow₀ hT
  have hq1 : 4 / T ≤ 4 := (div_le_iff₀ hT0).mpr (by linarith)
  have hq2 : h ^ 2 / T ≤ h ^ 2 := (div_le_iff₀ hT0).mpr (by nlinarith [sq_nonneg h])
  have hq3 : 2 * h ^ 2 / T ^ 3 ≤ 2 * h ^ 2 :=
    (div_le_iff₀ (by positivity : 0 < T ^ 3)).mpr (by nlinarith [sq_nonneg h])
  have hq : h ^ 2 / T + 2 * h ^ 2 / T ^ 3 ≤ 3 * h := by nlinarith
  have he : Real.exp h ≤ Real.exp 1 := Real.exp_le_exp.mpr hh1
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have hB : 1 + N * Real.exp h ≤ (D + 1) * Real.exp 1 * T := by
    have hm := mul_le_mul hND he (Real.exp_pos h).le (mul_nonneg hD hT0.le)
    have heT : 1 ≤ Real.exp 1 * T := by
      nlinarith [mul_nonneg (sub_nonneg.mpr he1) (sub_nonneg.mpr hT)]
    nlinarith
  have hL : 1 + (D * T + 1) ≤ (D + 2) * T := by nlinarith
  have hlead := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_right hq1 hh) hB
      (by positivity : 0 ≤ 1 + N * Real.exp h) (by positivity : 0 ≤ 4 * h))
    hL (by positivity : 0 ≤ 1 + (D * T + 1))
    (by positivity : 0 ≤ 4 * h * ((D + 1) * Real.exp 1 * T))
  have htail := mul_le_mul
    (mul_le_mul hq hND hN (by positivity : 0 ≤ 3 * h))
    hL (by positivity : 0 ≤ 1 + (D * T + 1))
    (by positivity : 0 ≤ 3 * h * (D * T))
  nlinarith

/-- Every polynomial multiple of the candidate's mesh width tends to zero. -/
theorem candidate_tendsto_rpow_mul_mesh (q : ℝ) {ν : ℝ} (hν : 0 < ν) :
    Tendsto (fun T : ℝ ↦ T ^ q * Real.exp (-(T ^ ν))) atTop (𝓝 0) := by
  have he := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (q / ν) 1 (by norm_num)).comp
    (tendsto_rpow_atTop hν)
  apply he.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  dsimp only [Function.comp_def]
  rw [← Real.rpow_mul hT.le, mul_div_cancel₀ q hν.ne']
  simp

/-- Uniform superpolynomial decay for the literal white-noise step error.
Both the coordinate and number of bins may vary with the scale. -/
theorem candidate_eventually_scaled_whiteStepSquare_lt
    (D q : ℝ) {ν ε : ℝ} (hD : 0 ≤ D) (hν : 0 < ν) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, ∀ n : ℕ,
      t - T ≤ D * T → (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      T ^ q * (∫ ω, (∑ j ∈ Finset.range n,
        ∫ x in Ioc (T + (j : ℝ) * Real.exp (-(T ^ ν)))
          (T + (j : ℝ) * Real.exp (-(T ^ ν)) + Real.exp (-(T ^ ν))),
          (harperCandidateLogProcess ω (t - x) / Real.sqrt x -
            harperCandidateLogProcess ω
              (t - (T + (j : ℝ) * Real.exp (-(T ^ ν)) + Real.exp (-(T ^ ν)))) /
                Real.sqrt (T + (j : ℝ) * Real.exp (-(T ^ ν)) +
                  Real.exp (-(T ^ ν)))) ^ 2) ∂mu) < ε := by
  let C := (D + 2) * (4 * (D + 1) * Real.exp 1 + 3 * D)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hrate : Tendsto (fun T : ℝ ↦ C * (T ^ (q + 2) * Real.exp (-(T ^ ν))))
      atTop (𝓝 0) := by simpa using (candidate_tendsto_rpow_mul_mesh (q + 2) hν).const_mul C
  filter_upwards [eventually_ge_atTop (1 : ℝ), (tendsto_order.mp hrate).2 ε hε] with T hT hrateT
  intro t n ht hn
  let h := Real.exp (-(T ^ ν))
  have hh : 0 ≤ h := (Real.exp_pos _).le
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (Real.rpow_nonneg (by linarith : 0 ≤ T) ν))
  have hT0 : 0 < T := by linarith
  have hfinite := candidate_integral_sum_whiteStepSquare_le (t := t) (T := T) (h := h)
    (L := D * T + 1) (n := n) hT0 hh (by linarith) (by positivity)
  have hpoly := candidate_whiteStep_bound_le_polynomial hT hh hh1 hD
    (mul_nonneg (Nat.cast_nonneg n) hh) hn
  have hbound := hfinite.trans hpoly
  have hm := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hT0.le q)
  apply hm.trans_lt
  have heq : T ^ q * (C * h * T ^ 2) = C * (T ^ (q + 2) * h) := by
    rw [Real.rpow_add hT0, Real.rpow_two]
    ring
  change T ^ q * (C * h * T ^ 2) < ε
  rw [heq]
  exact hrateT

end Erdos.Problem1144
