import Erdos.Problem1144.HarperCandidateCovarianceScreenWhiteKernel

open MeasureTheory Set

namespace Erdos.Problem1144
noncomputable section

/-- A measurable random frequency screen has measurable height sections. -/
theorem candidate_measurableSet_randomScreen_section (S : Omega → Set ℝ)
    (hS : MeasurableSet {z : Omega × ℝ | z.2 ∈ S z.1}) (ω : Omega) :
    MeasurableSet (S ω) := by
  exact hS.preimage (measurable_const.prodMk measurable_id)

private theorem measurable_screenInverse_joint (A : Omega → ℝ → ℂ)
    (hAm : Measurable (Function.uncurry A)) (S : Omega → Set ℝ)
    (hS : MeasurableSet {z : Omega × ℝ | z.2 ∈ S z.1}) :
    Measurable (fun z : Omega × ℝ => candidateCovarianceScreenInverse (A z.1) (S z.1) z.2) := by
  have hm : Measurable (fun z : (Omega × ℝ) × ℝ => (z.1.1, z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hE : MeasurableSet {z : (Omega × ℝ) × ℝ | z.2 ∈ S z.1.1} := hS.preimage hm
  have hA : Measurable (fun z : (Omega × ℝ) × ℝ => A z.1.1 z.2) := hAm.comp hm
  have hp : Measurable (fun z : (Omega × ℝ) × ℝ =>
      candidateCovariancePhase (z.1.2 * z.2)) := by
    unfold candidateCovariancePhase
    fun_prop
  let f : (Omega × ℝ) × ℝ → ℂ := fun z =>
    (S z.1.1).indicator (fun τ => A z.1.1 τ * candidateCovariancePhase (z.1.2 * τ)) z.2
  have hf : Measurable f := by
    exact (hA.mul hp).indicator hE
  have hi := StronglyMeasurable.integral_prod_right
    (f := fun (z : Omega × ℝ) τ => f (z, τ)) (ν := volume) hf.stronglyMeasurable
  have hc := hi.measurable.const_mul (2 * Real.pi : ℂ)⁻¹
  have he (z : Omega × ℝ) : (∫ τ, f (z, τ)) =
      ∫ τ in S z.1, A z.1 τ * candidateCovariancePhase (z.2 * τ) := by
    dsimp only [f]
    rw [integral_indicator (candidate_measurableSet_randomScreen_section S hS z.1)]
  simpa only [he, candidateCovarianceScreenInverse] using hc

/-- The literal inverse on a random measurable frequency screen is jointly
measurable in the signs and the time endpoint. No pathwise continuity of the
screen, exceptional-set selection, or random Gaussian construction is needed. -/
theorem candidate_measurable_eulerScreenInverse_joint (Y : ℕ) (S : Omega → Set ℝ)
    (hS : MeasurableSet {z : Omega × ℝ | z.2 ∈ S z.1}) :
    Measurable (fun z : Omega × ℝ =>
      candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 z.1) (S z.1) z.2) :=
  measurable_screenInverse_joint (candidateEulerAngularApprox Y 0)
    (measurable_candidateEulerAngularApprox Y 0) S hS

/-- Actual random screened kernels satisfy the joint measurability required
by the averaged finite-dimensional Gaussian Gram comparison. -/
theorem candidate_measurable_eulerScreenWhiteKernel_joint (Y : ℕ) (S : Omega → Set ℝ)
    (hS : MeasurableSet {z : Omega × ℝ | z.2 ∈ S z.1}) (T B u : ℝ) :
    Measurable (fun z : Omega × ℝ => candidateEulerScreenWhiteKernel Y z.1 (S z.1) T B u z.2) := by
  have hm : Measurable (fun z : Omega × ℝ => (z.1, u - z.2)) :=
    measurable_fst.prodMk (measurable_const.sub measurable_snd)
  have hi := (candidate_measurable_eulerScreenInverse_joint Y S hS).comp hm
  have hv : Measurable (fun z : Omega × ℝ =>
      (candidateCovarianceScreenInverse (candidateEulerAngularApprox Y 0 z.1)
        (S z.1) (u - z.2)).re / Real.sqrt z.2) :=
    hi.re.div (Real.continuous_sqrt.measurable.comp measurable_snd)
  have he : MeasurableSet {z : Omega × ℝ | z.2 ∈ Ioc T B} :=
    measurableSet_Ioc.preimage measurable_snd
  exact hv.indicator he

end
end Erdos.Problem1144
