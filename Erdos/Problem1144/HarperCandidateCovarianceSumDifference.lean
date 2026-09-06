import Erdos.Problem1144.HarperCandidateCovarianceGapCoordinates
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set

namespace Erdos.Problem1144
noncomputable section

/-- Difference and sum frequencies retain both Rademacher correlation
channels. Their change of variables has inverse Jacobian one half. -/
def candidateCovarianceSumDifference (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 - z.2, z.1 + z.2)

theorem candidate_measurableEmbedding_sumDifference :
    MeasurableEmbedding candidateCovarianceSumDifference := by
  apply Continuous.measurableEmbedding (by unfold candidateCovarianceSumDifference; fun_prop)
  intro x y h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [candidateCovarianceSumDifference] at h₁ h₂
  ext <;> linarith

theorem candidate_measurePreserving_sumDifference :
    MeasurePreserving candidateCovarianceSumDifference
      (volume.prod volume) ((ENNReal.ofReal (1 / 2 : ℝ)) • (volume.prod volume)) := by
  let c := ENNReal.ofReal (1 / 2 : ℝ)
  have hs : MeasurePreserving (fun x : ℝ => 2 * x) volume (c • volume) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [c] using Real.map_volume_mul_left (by norm_num : (2 : ℝ) ≠ 0)
  have h := (measurePreserving_prod_add volume (c • volume)).comp
    (((MeasurePreserving.id volume).prod hs).comp
      (measurePreserving_sub_prod volume volume))
  rw [Measure.prod_smul_right] at h
  convert h using 1
  funext z
  dsimp [candidateCovarianceSumDifference, Function.comp_def]
  congr 1
  ring

/-- Actual integrability after the sum/difference substitution. -/
theorem candidate_integrable_sumDifference_product {f g : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun z : ℝ × ℝ => f (z.1 - z.2) * g (z.1 + z.2))
      (volume.prod volume) := by
  have hi := (hf.mul_prod hg).smul_measure (ENNReal.ofReal_ne_top :
    ENNReal.ofReal (1 / 2 : ℝ) ≠ ⊤)
  exact candidate_measurePreserving_sumDifference.integrable_comp_of_integrable hi

/-- Exact product integral in both correlation channels, including the
Jacobian factor. -/
theorem candidate_integral_sumDifference_product (f g : ℝ → ℝ) :
    (∫ z : ℝ × ℝ, f (z.1 - z.2) * g (z.1 + z.2) ∂volume.prod volume) =
      (1 / 2 : ℝ) * (∫ u, f u) * (∫ v, g v) := by
  have h := candidate_measurePreserving_sumDifference.integral_comp
    candidate_measurableEmbedding_sumDifference (fun z => f z.1 * g z.2)
  dsimp only [candidateCovarianceSumDifference] at h
  rw [integral_smul_measure, integral_prod_mul] at h
  simpa [ENNReal.toReal_ofReal, smul_eq_mul, mul_assoc] using h

end
end Erdos.Problem1144
