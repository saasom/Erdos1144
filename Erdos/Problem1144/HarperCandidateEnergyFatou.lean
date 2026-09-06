import Erdos.Problem1144.HarperCandidateEnergyFatouIdentity
import Mathlib.Topology.Order.LiminfLimsup

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Erdos.Problem1144
noncomputable section

/-- The actual complete energy is almost surely bounded by the lower limit
of finite squarefree Euler energies multiplied by the full zeta weight.
The sequence of prime cutoffs is constructed from actual Fourier convergence. -/
theorem candidate_exists_dampedEnergy_le_finiteSpectral_liminf {σ : ℝ}
    (hσ : σ ∈ Ioc (0 : ℝ) (1 / 2)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂mu,
      ENNReal.ofReal (candidateDampedCompleteEnergy σ ω) ≤
        liminf (fun n => ENNReal.ofReal (candidateFiniteSpectralEnergy (ns n) σ ω)) atTop := by
  obtain ⟨ns, hns, hlim⟩ := candidate_exists_eulerAngularApprox_ae_subsequence hσ.1
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hlim, candidate_ae_dampedEnergy_fourier_identity hσ.1] with ω hω hid
  let G : ℝ → ℝ := fun τ => σ * ‖riemannZeta ((1 + 2 * σ : ℝ) +
    (2 * τ : ℝ) * Complex.I) * candidateSquarefreeAngularFourier ω σ τ‖ ^ 2
  let F : ℕ → ℝ → ℝ := fun n τ => σ * (candidateCompleteZetaWeight σ τ *
    harperRankinEulerDensity (ns n) (2 * σ) ω τ)
  have hGi : Integrable G := hid.1.const_mul σ
  have hG0 (τ : ℝ) : 0 ≤ G τ := mul_nonneg hσ.1.le (sq_nonneg _)
  have hFi (n : ℕ) : Integrable (F n) :=
    (candidate_integrable_weight_mul_euler (ns n) (2 * σ) ω
      (candidate_integrable_complete_zeta_weight hσ)).const_mul σ
  have hF0 (n : ℕ) (τ : ℝ) : 0 ≤ F n τ := mul_nonneg hσ.1.le
    (mul_nonneg (candidateCompleteZetaWeight_nonneg σ τ)
      (harperRankinEulerDensity_nonneg _ _ _ _))
  have hFint (n : ℕ) : (∫⁻ τ, ENNReal.ofReal (F n τ)) =
      ENNReal.ofReal (candidateFiniteSpectralEnergy (ns n) σ ω) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi n) (ae_of_all _ (hF0 n))]
    congr 1
    exact integral_const_mul σ _
  have hconv : ∀ᵐ τ ∂volume, Tendsto (fun n => ENNReal.ofReal (F n τ)) atTop
      (𝓝 (ENNReal.ofReal (G τ))) := by
    filter_upwards [hω] with τ hτ
    have h := ENNReal.continuous_ofReal.tendsto _ |>.comp
      (((hτ.const_mul (riemannZeta ((1 + 2 * σ : ℝ) +
        (2 * τ : ℝ) * Complex.I))).norm.pow 2).const_mul σ)
    simpa only [F, G, candidate_euler_weight_eq_norm _ hσ.1.le] using h
  have hfatou : ENNReal.ofReal (∫ τ, G τ) ≤
      liminf (fun n => ENNReal.ofReal (candidateFiniteSpectralEnergy (ns n) σ ω)) atTop := by
    rw [ofReal_integral_eq_lintegral_ofReal hGi (ae_of_all _ hG0)]
    calc
      _ = ∫⁻ τ, liminf (fun n => ENNReal.ofReal (F n τ)) atTop := by
        apply lintegral_congr_ae
        exact hconv.mono fun _ h => h.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ τ, ENNReal.ofReal (F n τ)) atTop :=
        lintegral_liminf_le' fun n => (hFi n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ = _ := by simp only [hFint]
  apply (ENNReal.ofReal_le_ofReal (show candidateDampedCompleteEnergy σ ω ≤ ∫ τ, G τ from ?_)).trans hfatou
  have hU := candidateDampedCompleteEnergy_nonneg hσ.1.le ω
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have he : (∫ τ, G τ) = 2 * Real.pi * candidateDampedCompleteEnergy σ ω := by
    rw [integral_const_mul]
    exact hid.2.symm
  rw [he]
  nlinarith

/-- A proved eventual moment bound for the finite Euler energies passes to
the literal complete damped process. Fatou supplies integrability as well as
the bound; no infinite-Euler, pathwise, or complete-energy premise is assumed. -/
theorem candidate_dampedEnergy_moment_le_of_finiteSpectral
    {σ q C : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) (1 / 2)) (hq : 0 < q)
    (hbound : ∀ᶠ Y : ℕ in atTop,
      (∫ ω, candidateFiniteSpectralEnergy Y σ ω ^ q ∂mu) ≤ C) :
    Integrable (fun ω => candidateDampedCompleteEnergy σ ω ^ q) mu ∧
      (∫ ω, candidateDampedCompleteEnergy σ ω ^ q ∂mu) ≤ C := by
  obtain ⟨ns, hns, hfatou⟩ := candidate_exists_dampedEnergy_le_finiteSpectral_liminf hσ
  have hC : 0 ≤ C := by
    obtain ⟨Y, hY⟩ := hbound.exists
    exact (integral_nonneg fun ω => Real.rpow_nonneg
      (candidateFiniteSpectralEnergy_nonneg Y hσ.1.le ω) q).trans hY
  have hpow : Monotone (fun x : ℝ≥0∞ => x ^ q) :=
    fun _ _ h => ENNReal.rpow_le_rpow h hq.le
  have hpoint : ∀ᵐ ω ∂mu, ENNReal.ofReal (candidateDampedCompleteEnergy σ ω ^ q) ≤
      liminf (fun n => ENNReal.ofReal (candidateFiniteSpectralEnergy (ns n) σ ω ^ q)) atTop := by
    filter_upwards [hfatou] with ω hω
    have h := ENNReal.rpow_le_rpow hω hq.le
    rw [ENNReal.ofReal_rpow_of_nonneg (candidateDampedCompleteEnergy_nonneg hσ.1.le ω) hq.le,
      hpow.map_liminf_of_continuousAt _ ENNReal.continuous_rpow_const.continuousAt] at h
    simpa only [Function.comp_def, ENNReal.ofReal_rpow_of_nonneg
      (candidateFiniteSpectralEnergy_nonneg _ hσ.1.le ω) hq.le] using h
  have hb : (∫⁻ ω, ENNReal.ofReal (candidateDampedCompleteEnergy σ ω ^ q) ∂mu) ≤
      ENNReal.ofReal C := by
    calc
      _ ≤ ∫⁻ ω, liminf (fun n =>
          ENNReal.ofReal (candidateFiniteSpectralEnergy (ns n) σ ω ^ q)) atTop ∂mu :=
        lintegral_mono_ae hpoint
      _ ≤ liminf (fun n => ∫⁻ ω,
          ENNReal.ofReal (candidateFiniteSpectralEnergy (ns n) σ ω ^ q) ∂mu) atTop :=
        lintegral_liminf_le' fun n =>
          (candidate_integrable_finiteSpectralEnergy_rpow (ns n) σ q).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ ≤ ENNReal.ofReal C := by
        apply liminf_le_of_frequently_le'
        apply Filter.Eventually.frequently
        filter_upwards [hns.tendsto_atTop.eventually hbound] with n hn
        have hiN : Integrable (fun ω : Omega => candidateFiniteSpectralEnergy (ns n) σ ω ^ q) mu :=
          candidate_integrable_finiteSpectralEnergy_rpow (ns n) σ q
        rw [← ofReal_integral_eq_lintegral_ofReal hiN
          (ae_of_all _ fun ω => Real.rpow_nonneg
            (candidateFiniteSpectralEnergy_nonneg _ hσ.1.le ω) q)]
        exact ENNReal.ofReal_le_ofReal hn
  have hm : AEStronglyMeasurable (fun ω => candidateDampedCompleteEnergy σ ω ^ q) mu :=
    ((Real.continuous_rpow_const hq.le).measurable.comp
      (measurable_candidateDampedCompleteEnergy σ)).aestronglyMeasurable
  have hi : Integrable (fun ω => candidateDampedCompleteEnergy σ ω ^ q) mu := by
    refine ⟨hm, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    have he (ω : Omega) : ‖candidateDampedCompleteEnergy σ ω ^ q‖ₑ =
        ENNReal.ofReal (candidateDampedCompleteEnergy σ ω ^ q) := by
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg
        (Real.rpow_nonneg (candidateDampedCompleteEnergy_nonneg hσ.1.le ω) q)]
    simp_rw [he]
    exact hb.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun ω => Real.rpow_nonneg (candidateDampedCompleteEnergy_nonneg hσ.1.le ω) q)]
  exact hb

end
end Erdos.Problem1144
