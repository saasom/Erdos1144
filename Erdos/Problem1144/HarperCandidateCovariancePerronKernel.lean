import Erdos.Problem1144.HarperCandidateEulerLimitFinite
import Erdos.Problem1144.HarperCandidateCovariance

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The angular Fourier phase, with no hidden `2π` rescaling. -/
def candidateCovariancePhase (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * Complex.I)

private theorem phase_add (x y : ℝ) :
    candidateCovariancePhase (x + y) = candidateCovariancePhase x * candidateCovariancePhase y := by
  simp only [candidateCovariancePhase, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem phase_conj (x : ℝ) :
    starRingEnd ℂ (candidateCovariancePhase x) = candidateCovariancePhase (-x) := by
  rw [candidateCovariancePhase, ← Complex.exp_conj]
  simp [candidateCovariancePhase]

private theorem phase_norm (x : ℝ) : ‖candidateCovariancePhase x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I x

/-- The actual Fourier transform of a scalar logarithmic-prime measure. -/
def candidateCovarianceMeasureKernel (ρ : Measure ℝ) (w : ℝ → ℂ) (h : ℝ) : ℂ :=
  ∫ r, w r * candidateCovariancePhase (-h * r) ∂ρ

/-- Inverse angular transform restricted to the literal frequency interval. -/
def candidateCovarianceBandInverse (A : ℝ → ℂ) (H u : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ τ in Icc (-H) H, A τ * candidateCovariancePhase (u * τ)

/-- The exact continuous kernel for the white field on a logarithmic interval.
Its weight is reciprocal logarithmic time, not a constant substitute. -/
def candidateCovarianceWhiteKernel (T B h : ℝ) : ℂ :=
  candidateCovarianceMeasureKernel (volume.restrict (Icc T B))
    (fun r => ((1 / r : ℝ) : ℂ)) h

/-- Weighted covariance of finite frequency inverse transforms is exactly a
double integral against the literal measure kernel. Fubini is justified by
an integrable product majorant, independently of any covariance estimate. -/
theorem candidate_band_covariance_eq_measureKernel
    (ρ : Measure ℝ) [SFinite ρ] (w A : ℝ → ℂ) (H u v : ℝ)
    (hwm : Measurable w) (hwi : Integrable w ρ)
    (hAm : Measurable A) (hAi : IntegrableOn A (Icc (-H) H)) :
    (∫ r, w r * candidateCovarianceBandInverse A H (u - r) *
      starRingEnd ℂ (candidateCovarianceBandInverse A H (v - r)) ∂ρ) =
    (2 * Real.pi : ℂ)⁻¹ ^ 2 * ∫ z : ℝ × ℝ,
      A z.1 * starRingEnd ℂ (A z.2) * candidateCovariancePhase (u * z.1 - v * z.2) *
        candidateCovarianceMeasureKernel ρ w (z.1 - z.2)
        ∂(volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H)) := by
  let ν : Measure ℝ := volume.restrict (Icc (-H) H)
  let Q : ℝ → ℝ × ℝ → ℂ := fun r z =>
    w r * (A z.1 * candidateCovariancePhase ((u - r) * z.1)) *
      starRingEnd ℂ (A z.2 * candidateCovariancePhase ((v - r) * z.2))
  have hQm : Measurable (Function.uncurry Q) := by
    have ha₁ : Measurable (fun z : ℝ × (ℝ × ℝ) => A z.2.1) := hAm.comp measurable_snd.fst
    have ha₂ : Measurable (fun z : ℝ × (ℝ × ℝ) => A z.2.2) := hAm.comp measurable_snd.snd
    have hw : Measurable (fun z : ℝ × (ℝ × ℝ) => w z.1) := hwm.comp measurable_fst
    unfold Q Function.uncurry candidateCovariancePhase
    fun_prop
  have hQi : Integrable (Function.uncurry Q) (ρ.prod (ν.prod ν)) := by
    apply (hwi.norm.mul_prod (hAi.norm.mul_prod hAi.norm)).mono' hQm.aestronglyMeasurable
    exact ae_of_all _ fun z => by
      simp only [Function.uncurry, Q, norm_mul, Complex.norm_conj, phase_norm, mul_one]
      exact le_of_eq (by ring)
  have hQleft (r : ℝ) : (∫ z : ℝ × ℝ, Q r z ∂ν.prod ν) =
      w r * (∫ τ, A τ * candidateCovariancePhase ((u - r) * τ) ∂ν) *
        starRingEnd ℂ (∫ τ, A τ * candidateCovariancePhase ((v - r) * τ) ∂ν) := by
    unfold Q
    simp_rw [mul_assoc (w r)]
    calc
      _ = w r * ∫ z : ℝ × ℝ,
          (A z.1 * candidateCovariancePhase ((u - r) * z.1)) *
            starRingEnd ℂ (A z.2 * candidateCovariancePhase ((v - r) * z.2)) ∂ν.prod ν :=
        integral_const_mul _ _
      _ = _ := by
        apply congrArg (fun z : ℂ => w r * z)
        have hp := integral_prod_mul (μ := ν) (ν := ν)
          (fun τ => A τ * candidateCovariancePhase ((u - r) * τ))
          (fun τ => starRingEnd ℂ (A τ * candidateCovariancePhase ((v - r) * τ)))
        rw [integral_conj] at hp
        exact hp
  have hQright (z : ℝ × ℝ) : (∫ r, Q r z ∂ρ) =
      A z.1 * starRingEnd ℂ (A z.2) * candidateCovariancePhase (u * z.1 - v * z.2) *
        candidateCovarianceMeasureKernel ρ w (z.1 - z.2) := by
    have he (r : ℝ) : Q r z =
        (A z.1 * starRingEnd ℂ (A z.2) * candidateCovariancePhase (u * z.1 - v * z.2)) *
          (w r * candidateCovariancePhase (-(z.1 - z.2) * r)) := by
      have hp : candidateCovariancePhase ((u - r) * z.1) *
          candidateCovariancePhase (-((v - r) * z.2)) =
          candidateCovariancePhase (u * z.1 - v * z.2) *
            candidateCovariancePhase (-(z.1 - z.2) * r) := by
        rw [← phase_add, ← phase_add]
        congr 1
        ring
      simp only [Q, map_mul, phase_conj]
      calc
        _ = (w r * A z.1 * starRingEnd ℂ (A z.2)) *
            (candidateCovariancePhase ((u - r) * z.1) *
              candidateCovariancePhase (-((v - r) * z.2))) := by ring
        _ = _ := by rw [hp]; ring
    simp_rw [he]
    exact integral_const_mul _ _
  have hswap := integral_integral_swap hQi
  simp_rw [hQleft, hQright] at hswap
  calc
    _ = (2 * Real.pi : ℂ)⁻¹ ^ 2 *
        ∫ r, w r * (∫ τ, A τ * candidateCovariancePhase ((u - r) * τ) ∂ν) *
          starRingEnd ℂ (∫ τ, A τ * candidateCovariancePhase ((v - r) * τ) ∂ν) ∂ρ := by
      calc
        _ = ∫ r, (2 * Real.pi : ℂ)⁻¹ ^ 2 *
            (w r * (∫ τ, A τ * candidateCovariancePhase ((u - r) * τ) ∂ν) *
              starRingEnd ℂ (∫ τ, A τ * candidateCovariancePhase ((v - r) * τ) ∂ν)) ∂ρ := by
          apply integral_congr_ae
          exact ae_of_all _ fun r => by
            simp only [candidateCovarianceBandInverse, map_mul, map_inv₀,
              map_ofNat, Complex.conj_ofReal]
            ring
        _ = _ := integral_const_mul _ _
    _ = _ := by rw [hswap]

/-- The actual critical finite Euler transform is continuous at every height. -/
theorem candidate_continuous_criticalEulerAngularApprox (Y : ℕ) (ω : Omega) :
    Continuous (candidateEulerAngularApprox Y 0 ω) := by
  unfold candidateEulerAngularApprox
  apply Continuous.div
  · unfold harperRankinDirichletPolynomial
    fun_prop
  · fun_prop
  · intro τ he
    have h := congrArg Complex.re he
    norm_num at h

private theorem weight_integrable {T B : ℝ} (hT : 0 < T) :
    Integrable (fun r => ((1 / r : ℝ) : ℂ)) (volume.restrict (Icc T B)) := by
  apply ContinuousOn.integrableOn_Icc
  apply Complex.continuous_ofReal.comp_continuousOn
  exact continuousOn_const.div continuousOn_id fun r hr => (hT.trans_le hr.1).ne'

/-- The literal finite squarefree Euler product has the expected white
covariance double-integral representation at every finite frequency cutoff.
The remaining approximation is solely the removal of that cutoff. -/
theorem candidate_finiteEuler_white_band_covariance_eq
    (Y : ℕ) (ω : Omega) (H u v B : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ r in Icc T B, ((1 / r : ℝ) : ℂ) *
      candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (u - r) *
      starRingEnd ℂ
        (candidateCovarianceBandInverse (candidateEulerAngularApprox Y 0 ω) H (v - r))) =
    (2 * Real.pi : ℂ)⁻¹ ^ 2 * ∫ z : ℝ × ℝ,
      candidateEulerAngularApprox Y 0 ω z.1 *
        starRingEnd ℂ (candidateEulerAngularApprox Y 0 ω z.2) *
        candidateCovariancePhase (u * z.1 - v * z.2) *
        candidateCovarianceWhiteKernel T B (z.1 - z.2)
        ∂(volume.restrict (Icc (-H) H)).prod (volume.restrict (Icc (-H) H)) := by
  apply candidate_band_covariance_eq_measureKernel
  · fun_prop
  · exact weight_integrable hT
  · exact (candidate_continuous_criticalEulerAngularApprox Y ω).measurable
  · exact (candidate_continuous_criticalEulerAngularApprox Y ω).integrableOn_Icc

end
end Erdos.Problem1144
