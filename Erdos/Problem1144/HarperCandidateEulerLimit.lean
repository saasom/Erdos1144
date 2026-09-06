import Erdos.Problem1144.HarperCandidateEulerLimitFinite
import Mathlib.Probability.Distributions.Gaussian.Real

open Finset MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators Topology ENNReal

namespace Erdos.Problem1144
noncomputable section

private theorem integral_norm_le_half_power {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Ω → ℂ}
    (hm : AEStronglyMeasurable F P) (h₂ : Integrable (fun ω => ‖F ω‖ ^ 2) P) :
    (∫ ω, ‖F ω‖ ∂P) ≤ (∫ ω, ‖F ω‖ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  have hLp : MemLp F 2 P := (memLp_two_iff_integrable_sq_norm hm).mpr h₂
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P)
    (Real.holderConjugate_iff.mpr (by norm_num) : Real.HolderConjugate 2 2)
    (ae_of_all P fun ω => norm_nonneg (F ω))
    (ae_of_all P fun _ => (by norm_num : (0 : ℝ) ≤ 1))
    (by simpa using hLp.norm) (by simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 P))
  simpa only [mul_one, Real.rpow_two, one_pow, integral_const, probReal_univ,
    one_smul, Real.one_rpow, mul_one] using h

private theorem integrable_of_sq {F : Omega → ℂ}
    (hm : AEStronglyMeasurable F mu) (h₂ : Integrable (fun ω => ‖F ω‖ ^ 2) mu) :
    Integrable F mu := ((memLp_two_iff_integrable_sq_norm hm).mpr h₂).integrable (by norm_num)

private theorem measurable_integer (N : ℕ) (σ τ : ℝ) :
    Measurable fun ω => ∑ n ∈ Finset.Icc 1 N,
      candidateEulerDirichletCoefficient σ τ n * (gSquarefree ω n : ℂ) := by
  exact Finset.measurable_sum _ fun n _ => measurable_const.mul
    (Complex.measurable_ofReal.comp (measurable_gSquarefree n))

private theorem measurable_euler (Y : ℕ) (σ τ : ℝ) :
    Measurable fun ω => candidateEulerAngularApprox Y σ ω τ := by
  exact Measurable.of_uncurry_right
    (f := fun ω τ => candidateEulerAngularApprox Y σ ω τ)
    (measurable_candidateEulerAngularApprox Y σ)

private theorem measurable_full (σ τ : ℝ) :
    Measurable fun ω => candidateSquarefreeAngularFourier ω σ τ := by
  exact Measurable.of_uncurry_right
    (f := fun ω τ => candidateSquarefreeAngularFourier ω σ τ)
    (measurable_candidateSquarefreeAngularFourier σ)

/-- At every frequency, the finite prime Euler transform converges to the
literal squarefree angular Fourier integral in mean absolute distance. -/
theorem candidate_tendsto_eulerAngularApprox_L1 {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    Tendsto (fun Y : ℕ => ∫ ω,
      ‖candidateEulerAngularApprox Y σ ω τ - candidateSquarefreeAngularFourier ω σ τ‖ ∂mu)
      atTop (𝓝 0) := by
  let D (Y : ℕ) (ω : Omega) := ∑ n ∈ Finset.Icc 1 Y,
    candidateEulerDirichletCoefficient σ τ n * (gSquarefree ω n : ℂ)
  have hD (Y : ℕ) : Integrable (D Y) mu := integrable_of_sq
    (measurable_integer Y σ τ).aestronglyMeasurable
    (candidate_integrable_complex_squarefree_sum_norm_sq _ _)
  have hE (Y : ℕ) : Integrable (fun ω => candidateEulerAngularApprox Y σ ω τ) mu :=
    integrable_of_sq (measurable_euler Y σ τ).aestronglyMeasurable
      (candidate_integrable_eulerAngularApprox_sq Y σ τ)
  have hG : Integrable (fun ω => candidateSquarefreeAngularFourier ω σ τ) mu :=
    integrable_of_sq (measurable_full σ τ).aestronglyMeasurable
      (candidate_squarefree_fourier_second_moment hσ τ).1
  have htail : Tendsto (fun Y : ℕ => ∫ ω,
      ‖candidateEulerAngularApprox Y σ ω τ - D Y ω‖ ∂mu) atTop (𝓝 0) := by
    have hden : 0 < (σ + 1 / 2) ^ 2 + τ ^ 2 := by positivity
    have hb := (candidateEulerTailMass_tendsto hσ).div_const ((σ + 1 / 2) ^ 2 + τ ^ 2)
    simp only [zero_div] at hb
    have hl := (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).tendsto 0 |>.comp hb
    simp only [zero_div, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hl
    apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _ hl
    apply Eventually.of_forall
    intro Y
    exact (integral_norm_le_half_power ((hE Y).sub (hD Y)).aestronglyMeasurable
      (candidate_integrable_euler_sub_integer_sq Y σ τ)).trans
      (Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _)
        (candidate_integral_euler_sub_integer_sq_le Y hσ τ) (by norm_num))
  have hint : Tendsto (fun Y : ℕ => ∫ ω,
      ‖D Y ω - candidateSquarefreeAngularFourier ω σ τ‖ ∂mu) atTop (𝓝 0) := by
    simpa only [candidate_squarefreeLogApprox_fourier_eq _ _ hσ τ,
      candidateEulerDirichletCoefficient, D, candidateSquarefreeAngularFourier] using
      candidate_tendsto_squarefreeLogApprox_fourier_L1 hσ τ
  have hsum := htail.add hint
  simp only [zero_add] at hsum
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _ hsum
  apply Eventually.of_forall
  intro Y
  calc
    _ ≤ ∫ ω, ‖candidateEulerAngularApprox Y σ ω τ - D Y ω‖ +
        ‖D Y ω - candidateSquarefreeAngularFourier ω σ τ‖ ∂mu :=
      integral_mono ((hE Y).sub hG).norm
        (((hE Y).sub (hD Y)).norm.add ((hD Y).sub hG).norm)
        (fun ω => norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ = _ := by
      simpa only [Pi.sub_apply] using
        integral_add ((hE Y).sub (hD Y)).norm ((hD Y).sub hG).norm

/-- The same ordinary Dirichlet mass bounds every finite prime transform. -/
theorem candidate_integral_eulerAngularApprox_sq_le (Y : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (τ : ℝ) :
    (∫ ω, ‖candidateEulerAngularApprox Y σ ω τ‖ ^ 2 ∂mu) ≤
      (∑' n : ℕ, (n : ℝ) ^ (-(1 + 2 * σ))) / ((σ + 1 / 2) ^ 2 + τ ^ 2) := by
  simp_rw [candidateEulerAngularApprox_eq_sum]
  refine (candidate_integral_complex_squarefree_sum_norm_sq_le _ _
    (fun n hn => (candidateEulerSupport_mem hn).1)).trans ?_
  calc
    (∑ n ∈ candidateEulerSupport Y, ‖candidateEulerDirichletCoefficient σ τ n‖ ^ 2) =
        (∑ n ∈ candidateEulerSupport Y, (n : ℝ) ^ (-(1 + 2 * σ))) /
          ((σ + 1 / 2) ^ 2 + τ ^ 2) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun n hn =>
        candidate_squarefree_dirichletCoefficient_norm_sq σ τ (candidateEulerSupport_mem hn).1
    _ ≤ _ := div_le_div_of_nonneg_right
      ((Real.summable_nat_rpow.mpr (by linarith : -(1 + 2 * σ) < -1)).sum_le_tsum _
        (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)) (by positivity)

private theorem integral_norm_bound {σ : ℝ} (hσ : 0 < σ) (τ : ℝ)
    {F : Omega → ℂ} (hm : AEStronglyMeasurable F mu)
    (h₂ : Integrable (fun ω => ‖F ω‖ ^ 2) mu)
    (hb : (∫ ω, ‖F ω‖ ^ 2 ∂mu) ≤
      (∑' n : ℕ, (n : ℝ) ^ (-(1 + 2 * σ))) / ((σ + 1 / 2) ^ 2 + τ ^ 2)) :
    (∫ ω, ‖F ω‖ ∂mu) ≤
      ((∑' n : ℕ, (n : ℝ) ^ (-(1 + 2 * σ))) / (σ + 1 / 2) ^ 2) ^ (1 / 2 : ℝ) := by
  refine (integral_norm_le_half_power hm h₂).trans
    (Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) (hb.trans ?_) (by norm_num))
  exact div_le_div_of_nonneg_left (tsum_nonneg fun _ => Real.rpow_nonneg (by positivity) _)
    (by positivity) (le_add_of_nonneg_right (sq_nonneg τ))

/-- Integrating the Fourier error against any probability law in frequency
still gives genuine mean-L1 convergence. This will provide a single subsequence
simultaneously for almost every sign configuration and Lebesgue frequency. -/
theorem candidate_eulerAngularApprox_product_L1
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {σ : ℝ} (hσ : 0 < σ) :
    (∀ Y : ℕ, Integrable (fun z : Omega × ℝ =>
      candidateEulerAngularApprox Y σ z.1 z.2 -
        candidateSquarefreeAngularFourier z.1 σ z.2) (mu.prod ν)) ∧
    Tendsto (fun Y : ℕ => ∫ z : Omega × ℝ,
      ‖candidateEulerAngularApprox Y σ z.1 z.2 -
        candidateSquarefreeAngularFourier z.1 σ z.2‖ ∂mu.prod ν) atTop (𝓝 0) := by
  let F (Y : ℕ) (z : Omega × ℝ) := candidateEulerAngularApprox Y σ z.1 z.2
  let G (z : Omega × ℝ) := candidateSquarefreeAngularFourier z.1 σ z.2
  let B := ((∑' n : ℕ, (n : ℝ) ^ (-(1 + 2 * σ))) / (σ + 1 / 2) ^ 2) ^ (1 / 2 : ℝ)
  have hB : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  have hFm (Y : ℕ) : Measurable (F Y) := measurable_candidateEulerAngularApprox Y σ
  have hGm : Measurable G := measurable_candidateSquarefreeAngularFourier σ
  have hFi (Y : ℕ) (τ : ℝ) : Integrable (fun ω => F Y (ω, τ)) mu :=
    integrable_of_sq (measurable_euler Y σ τ).aestronglyMeasurable
      (candidate_integrable_eulerAngularApprox_sq Y σ τ)
  have hGi (τ : ℝ) : Integrable (fun ω => G (ω, τ)) mu :=
    integrable_of_sq (measurable_full σ τ).aestronglyMeasurable
      (candidate_squarefree_fourier_second_moment hσ τ).1
  have hFb (Y : ℕ) (τ : ℝ) : (∫ ω, ‖F Y (ω, τ)‖ ∂mu) ≤ B :=
    integral_norm_bound hσ τ (measurable_euler Y σ τ).aestronglyMeasurable
      (candidate_integrable_eulerAngularApprox_sq Y σ τ)
      (candidate_integral_eulerAngularApprox_sq_le Y hσ τ)
  have hGb (τ : ℝ) : (∫ ω, ‖G (ω, τ)‖ ∂mu) ≤ B :=
    integral_norm_bound hσ τ (measurable_full σ τ).aestronglyMeasurable
      (candidate_squarefree_fourier_second_moment hσ τ).1
      (candidate_squarefree_fourier_second_moment hσ τ).2
  have hFprod (Y : ℕ) : Integrable (F Y) (mu.prod ν) := by
    apply (integrable_prod_iff' (hFm Y).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (hFi Y), ?_⟩
    apply (integrable_const B).mono'
      ((hFm Y).norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
    exact ae_of_all _ fun τ => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hFb Y τ
  have hGprod : Integrable G (mu.prod ν) := by
    apply (integrable_prod_iff' hGm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hGi, ?_⟩
    apply (integrable_const B).mono'
      (hGm.norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable
    exact ae_of_all _ fun τ => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hGb τ
  have he (Y : ℕ) (τ : ℝ) : (∫ ω, ‖F Y (ω, τ) - G (ω, τ)‖ ∂mu) ≤ 2 * B := by
    calc
      _ ≤ ∫ ω, ‖F Y (ω, τ)‖ + ‖G (ω, τ)‖ ∂mu :=
        integral_mono ((hFi Y τ).sub (hGi τ)).norm ((hFi Y τ).norm.add (hGi τ).norm)
          (fun ω => norm_sub_le _ _)
      _ = (∫ ω, ‖F Y (ω, τ)‖ ∂mu) + ∫ ω, ‖G (ω, τ)‖ ∂mu :=
        integral_add (hFi Y τ).norm (hGi τ).norm
      _ ≤ 2 * B := by linarith [hFb Y τ, hGb τ]
  have hl := tendsto_integral_of_dominated_convergence (μ := ν) (fun _ : ℝ => 2 * B)
    (fun Y => (((hFm Y).sub hGm).norm.stronglyMeasurable.integral_prod_left).aestronglyMeasurable)
    (integrable_const _) (fun Y => ae_of_all _ fun τ => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact he Y τ)
    (ae_of_all _ fun τ => candidate_tendsto_eulerAngularApprox_L1 hσ τ)
  simp only [integral_zero] at hl
  refine ⟨fun Y => (hFprod Y).sub hGprod, ?_⟩
  convert hl using 1
  funext Y
  exact integral_prod_symm _ ((hFprod Y).sub hGprod).norm

/-- A single sequence of prime cutoffs gives the actual Euler/Fourier limit
for almost every pair of signs and Lebesgue frequency. The auxiliary Gaussian
measure used in extracting the sequence is equivalent to volume. -/
theorem candidate_exists_eulerAngularApprox_ae_subsequence {σ : ℝ} (hσ : 0 < σ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂mu, ∀ᵐ τ ∂volume,
      Tendsto (fun n => candidateEulerAngularApprox (ns n) σ ω τ) atTop
        (𝓝 (candidateSquarefreeAngularFourier ω σ τ)) := by
  let ν := gaussianReal 0 1
  let F (Y : ℕ) (z : Omega × ℝ) := candidateEulerAngularApprox Y σ z.1 z.2
  let G (z : Omega × ℝ) := candidateSquarefreeAngularFourier z.1 σ z.2
  have hFm (Y : ℕ) : Measurable (F Y) := measurable_candidateEulerAngularApprox Y σ
  have hGm : Measurable G := measurable_candidateSquarefreeAngularFourier σ
  have hpacket := candidate_eulerAngularApprox_product_L1 ν hσ
  have hlim := hpacket.2
  have hLp : Tendsto (fun Y => eLpNorm (F Y - G) 1 (mu.prod ν)) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.tendsto 0 |>.comp hlim
    simp only [ENNReal.ofReal_zero] at h
    convert h using 1
    funext Y
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact (ofReal_integral_norm_eq_lintegral_enorm (hpacket.1 Y)).symm
  have hm := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (fun Y => (hFm Y).aestronglyMeasurable) hGm.aestronglyMeasurable hLp
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have habs : mu.prod (volume : Measure ℝ) ≪ mu.prod ν :=
    (Measure.AbsolutelyContinuous.refl mu).prod (gaussianReal_absolutelyContinuous' 0 (by norm_num))
  exact ⟨ns, hns, Measure.ae_ae_of_ae_prod (habs.ae_le hae)⟩

end
end Erdos.Problem1144
