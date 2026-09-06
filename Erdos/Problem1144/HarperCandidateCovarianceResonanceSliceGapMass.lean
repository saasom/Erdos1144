import Erdos.Problem1144.HarperCandidateCovarianceGapEnvelope
import Erdos.Problem1144.HarperCandidateCovarianceResonanceSliceCoordinate
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory Set
open scoped Interval

namespace Erdos.Problem1144

private theorem clipped_reciprocal_le {L g : ℝ} (hL : 0 < L) (hg : 0 ≤ g) :
    min L (2 / max g L⁻¹) ≤ 3 * L / (1 + L * g) := by
  let H := min L (2 / max g L⁻¹)
  have hmax : 0 < max g L⁻¹ := (inv_pos.mpr hL).trans_le (le_max_right _ _)
  have hH : 0 ≤ H := le_min hL.le (div_nonneg (by norm_num) hmax.le)
  have hHL : H ≤ L := min_le_left _ _
  have hHg : H * g ≤ 2 := by
    calc
      _ ≤ H * max g L⁻¹ := mul_le_mul_of_nonneg_left (le_max_left _ _) hH
      _ ≤ 2 := (le_div_iff₀ hmax).mp (min_le_right _ _)
  apply (le_div_iff₀ (by positivity : 0 < 1 + L * g)).mpr
  have h := mul_le_mul_of_nonneg_left hHg hL.le
  dsimp [H] at *
  nlinarith

private theorem min_max_le_add_min {L A R : ℝ} (hL : 0 ≤ L) (hA : 0 ≤ A) (hR : 0 ≤ R) :
    min L (max A R) ≤ A + min L R := by
  by_cases hAR : A ≤ R
  · rw [max_eq_right hAR]
    exact le_add_of_nonneg_left hA
  · rw [max_eq_left (le_of_not_ge hAR)]
    exact (min_le_right _ _).trans (le_add_of_nonneg_right (le_min hL hR))

/-- The actual clipped Euler gap envelope has a nonsingular logarithmically
integrable majorant, including all microscopic gaps. -/
theorem candidate_gapEnvelope_le_regularized_reciprocal
    (start stop : ℕ) {g : ℝ} (hg : 0 ≤ g) :
    candidateCovarianceGapEnvelope start stop g ≤
      Real.log (Problem520.harperBlockEndpoint start : ℝ) +
        3 * Real.log (Problem520.harperBlockEndpoint stop : ℝ) /
          (1 + Real.log (Problem520.harperBlockEndpoint stop : ℝ) * g) := by
  let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
  let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (Problem520.one_le_log_harperBlockEndpoint stop)
  have hA : 0 ≤ A := (Problem520.one_le_log_harperBlockEndpoint start).trans' (by norm_num)
  have hmax : 0 < max g L⁻¹ := (inv_pos.mpr hL).trans_le (le_max_right _ _)
  change min L (max A (2 / max g L⁻¹)) ≤ _
  exact (min_max_le_add_min hL.le hA (div_nonneg (by norm_num) hmax.le)).trans
    (add_le_add (le_refl _) (clipped_reciprocal_le hL hg))

/-- On a positive gap the same literal envelope fits the reciprocal-plus-
constant resonance slice estimate, with coefficient exactly two. -/
theorem candidate_gapEnvelope_le_reciprocal
    (start stop : ℕ) {g : ℝ} (hg : 0 < g) :
    candidateCovarianceGapEnvelope start stop g ≤
      Real.log (Problem520.harperBlockEndpoint start : ℝ) + 2 / g := by
  have hA : 0 ≤ Real.log (Problem520.harperBlockEndpoint start : ℝ) :=
    (Problem520.one_le_log_harperBlockEndpoint start).trans' (by norm_num)
  unfold candidateCovarianceGapEnvelope
  apply (min_le_right _ _).trans
  apply max_le
  · exact le_add_of_nonneg_right (by positivity)
  · exact (div_le_div_of_nonneg_left (by norm_num) hg (le_max_left _ _)).trans
      (le_add_of_nonneg_left hA)

private theorem regularized_reciprocal_integral {L M : ℝ} (hL : 0 < L) (hM : 0 ≤ M) :
    (∫ g in Icc (0 : ℝ) M, L / (1 + L * g)) = Real.log (1 + L * M) := by
  have hder (x : ℝ) (hx : x ∈ uIcc (0 : ℝ) M) :
      HasDerivAt (fun t => Real.log (1 + L * t)) (L / (1 + L * x)) x := by
    have hx0 : 0 ≤ x := (uIcc_of_le hM ▸ hx).1
    have hpos : 0 < 1 + L * x := by positivity
    convert (((hasDerivAt_const x (1 : ℝ)).add
      ((hasDerivAt_id x).const_mul L)).log hpos.ne') using 1 <;> dsimp <;> ring
  have hi : IntervalIntegrable (fun g : ℝ => L / (1 + L * g)) volume 0 M := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      have hx0 : 0 ≤ x := (uIcc_of_le hM ▸ hx).1
      positivity
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hM,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder hi]
  simp

/-- Explicit full interval mass of the actual bounded reciprocal Euler gap
envelope. This supplies the other-coordinate factors in weighted Fubini. -/
theorem candidate_integral_gapEnvelope_le (start stop : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    (∫ g in Icc (0 : ℝ) M, candidateCovarianceGapEnvelope start stop g) ≤
      Real.log (Problem520.harperBlockEndpoint start : ℝ) * M +
        3 * Real.log (1 + Real.log (Problem520.harperBlockEndpoint stop : ℝ) * M) := by
  let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
  let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (Problem520.one_le_log_harperBlockEndpoint stop)
  have hr : IntegrableOn (fun g : ℝ => L / (1 + L * g)) (Icc 0 M) := by
    apply ContinuousOn.integrableOn_Icc
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      have hx0 := hx.1
      positivity
  have heq : (fun g : ℝ => A + 3 * L / (1 + L * g)) =
      fun g => A + 3 * (L / (1 + L * g)) := by funext g; ring
  calc
    _ ≤ ∫ g in Icc (0 : ℝ) M, A + 3 * L / (1 + L * g) := by
      apply setIntegral_mono_on (candidate_continuous_gapEnvelope start stop |>.integrableOn_Icc)
        (by rw [heq]; exact (integrable_const A).add (hr.const_mul 3)) measurableSet_Icc
      intro g hg
      exact candidate_gapEnvelope_le_regularized_reciprocal start stop hg.1
    _ = _ := by
      rw [heq, integral_add (integrable_const A) (hr.const_mul 3), integral_const_mul,
        regularized_reciprocal_integral hL hM, setIntegral_const, smul_eq_mul,
        Real.volume_real_Icc_of_le hM]
      dsimp [A, L]
      ring

end Erdos.Problem1144
