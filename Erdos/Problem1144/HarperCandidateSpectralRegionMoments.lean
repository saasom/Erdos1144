import Erdos.Problem1144.HarperCandidateFiniteSpectralEnergy

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Actual finite spectral energy in a specified frequency region. -/
def candidateFiniteSpectralRegionEnergy (y : ℕ) (σ : ℝ) (S : Set ℝ)
    (ω : Problem520.Omega) : ℝ :=
  σ * ∫ t in S, candidateCompleteZetaWeight σ t *
    harperRankinEulerDensity y (2 * σ) ω t

theorem candidateFiniteSpectralRegionEnergy_nonneg (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (S : Set ℝ) (ω : Problem520.Omega) :
    0 ≤ candidateFiniteSpectralRegionEnergy y σ S ω :=
  mul_nonneg hσ (integral_nonneg fun t =>
    mul_nonneg (candidateCompleteZetaWeight_nonneg σ t)
      (harperRankinEulerDensity_nonneg y (2 * σ) ω t))

theorem candidate_integrable_finiteSpectralRegionEnergy_rpow
    (y : ℕ) (σ q : ℝ) (S : Set ℝ) :
    Integrable (fun ω => candidateFiniteSpectralRegionEnergy y σ S ω ^ q)
      Problem520.μ :=
  candidate_integrable_euler_functional y (2 * σ)
    (fun f => (σ * ∫ t in S, candidateCompleteZetaWeight σ t * f t) ^ q)

theorem candidate_integrable_finiteSpectralRegionEnergy
    (y : ℕ) (σ : ℝ) (S : Set ℝ) :
    Integrable (candidateFiniteSpectralRegionEnergy y σ S) Problem520.μ :=
  candidate_integrable_euler_functional y (2 * σ)
    (fun f => σ * ∫ t in S, candidateCompleteZetaWeight σ t * f t)

/-- Exact frequency-region first moment of the full-zeta weighted product. -/
theorem candidate_integral_finiteSpectralRegionEnergy (y : ℕ) {σ : ℝ}
    (hσ : σ ∈ Ioc (0 : ℝ) (1 / 2)) {S : Set ℝ} (hS : MeasurableSet S) :
    (∫ ω, candidateFiniteSpectralRegionEnergy y σ S ω ∂Problem520.μ) =
      σ * ((∫ t in S, candidateCompleteZetaWeight σ t) *
        harperRankinPrimeEnergyNormalizer y (2 * σ)) := by
  have hi := (candidate_integrable_complete_zeta_weight hσ).indicator hS
  have he (ω : Problem520.Omega) :
      (∫ t in S, candidateCompleteZetaWeight σ t *
          harperRankinEulerDensity y (2 * σ) ω t) =
        ∫ t, S.indicator (candidateCompleteZetaWeight σ) t *
          harperRankinEulerDensity y (2 * σ) ω t := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      by_cases ht : t ∈ S <;> simp [ht]
  unfold candidateFiniteSpectralRegionEnergy
  simp_rw [he]
  rw [integral_const_mul, candidate_integral_weight_mul_euler y (2 * σ) hi,
    integral_indicator hS]

/-- Outside a fixed central interval, the finite spectral energy has a
uniform first moment and hence a uniform eighth moment. -/
theorem candidate_exists_finiteSpectralRegion_high_moment {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Ioc (0 : ℝ) (1 / 2), ∀ y : ℕ,
      (∫ ω, candidateFiniteSpectralRegionEnergy y σ {t | η ≤ |t|} ω ^
        (1 / 8 : ℝ) ∂Problem520.μ) ≤ C := by
  obtain ⟨C, hC, hb⟩ := candidate_complete_zeta_weight_high_integral_bounded hη
  refine ⟨C ^ (1 / 8 : ℝ), Real.rpow_nonneg hC _, ?_⟩
  intro σ hσ y
  have hσpos := hσ.1
  let S : Set ℝ := {t | η ≤ |t|}
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hi := candidate_integrable_finiteSpectralRegionEnergy y σ S
  have hip := candidate_integrable_finiteSpectralRegionEnergy_rpow y σ (1 / 8 : ℝ) S
  have hj := (Real.concaveOn_rpow (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 / 8 : ℝ) ≤ 1)).le_map_integral
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 8)).continuousOn
    isClosed_Ici (ae_of_all Problem520.μ
      (candidateFiniteSpectralRegionEnergy_nonneg y hσ.1.le S)) hi hip
  apply hj.trans
  apply Real.rpow_le_rpow
    (integral_nonneg (candidateFiniteSpectralRegionEnergy_nonneg y hσ.1.le S))
    _ (by norm_num)
  rw [candidate_integral_finiteSpectralRegionEnergy y hσ hS]
  have hnorm := candidate_rankinNormalizer_upper y (by positivity : 0 < 2 * σ)
  have hn0 := (harperRankinPrimeEnergyNormalizer_pos y (2 * σ)).le
  have hw0 : 0 ≤ ∫ t in S, candidateCompleteZetaWeight σ t :=
    integral_nonneg (candidateCompleteZetaWeight_nonneg σ)
  calc
    _ ≤ σ * (C * (1 + 1 / (2 * σ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (hb σ hσ).2 hnorm hn0 hC) hσpos.le
    _ = C * (σ + 1 / 2) := by field_simp [hσpos.ne']
    _ ≤ C := by nlinarith [hσ.2]

/-- A literal interval weight bound transfers the already proved scaled
Euler moment to the full-zeta weighted interval energy. -/
theorem candidate_finiteSpectralRegion_interval_moment_le
    {σ U u v B : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) (1 / 2))
    (hU : 0 < U) (hU1 : U ≤ 1 / 4) (hσU : σ ≤ U)
    (huv : u ≤ v) (hlen : v - u ≤ U)
    (hwindow : ∀ t ∈ Icc u v, |t| ≤ 2 * U) (hB : 0 ≤ B)
    (hweight : ∀ t ∈ Icc u v,
      σ * candidateCompleteZetaWeight σ t ≤ B * (2 * σ / U ^ 2))
    {y : ℕ} (hy : ⌊Real.exp (1 / (2 * U))⌋₊ ≤ y) :
    (∫ ω, candidateFiniteSpectralRegionEnergy y σ (Icc u v) ω ^
      (1 / 8 : ℝ) ∂Problem520.μ) ≤
        B ^ (1 / 8 : ℝ) * candidateEulerIntervalMomentConstant * U ^ (1 / 16 : ℝ) := by
  have hσpos := hσ.1
  have hpoint (ω : Problem520.Omega) :
      candidateFiniteSpectralRegionEnergy y σ (Icc u v) ω ≤
        B * (2 * σ / U ^ 2 * candidateShiftedEulerIntervalEnergy y (2 * σ) u v ω) := by
    unfold candidateFiniteSpectralRegionEnergy candidateShiftedEulerIntervalEnergy
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    have hc := candidate_continuous_shifted_euler_density y (2 * σ) ω
    apply setIntegral_mono_on
      (((continuous_candidateCompleteZetaWeight hσ.1).mul hc).const_mul σ).integrableOn_Icc
      ((hc.const_mul (2 * σ / U ^ 2)).const_mul B).integrableOn_Icc
      measurableSet_Icc
    intro t ht
    change σ * (candidateCompleteZetaWeight σ t *
      harperRankinEulerDensity y (2 * σ) ω t) ≤ _
    nlinarith [mul_le_mul_of_nonneg_right (hweight t ht)
      (harperRankinEulerDensity_nonneg y (2 * σ) ω t)]
  have hscalar : 0 ≤ 2 * σ / U ^ 2 := by positivity
  have hpow (ω : Problem520.Omega) :
      candidateFiniteSpectralRegionEnergy y σ (Icc u v) ω ^ (1 / 8 : ℝ) ≤
        B ^ (1 / 8 : ℝ) *
          (2 * σ / U ^ 2 * candidateShiftedEulerIntervalEnergy y (2 * σ) u v ω) ^
            (1 / 8 : ℝ) := by
    rw [← Real.mul_rpow hB (mul_nonneg hscalar
      (candidate_shifted_euler_interval_nonneg y (2 * σ) u v ω))]
    exact Real.rpow_le_rpow
      (candidateFiniteSpectralRegionEnergy_nonneg y hσ.1.le _ ω) (hpoint ω) (by norm_num)
  have hiR := candidate_integrable_euler_functional y (2 * σ)
    (fun f => B ^ (1 / 8 : ℝ) *
      (2 * σ / U ^ 2 * ∫ t in Icc u v, f t) ^ (1 / 8 : ℝ))
  have hiL := candidate_integrable_finiteSpectralRegionEnergy_rpow y σ (1 / 8 : ℝ) (Icc u v)
  refine (integral_mono hiL hiR hpow).trans ?_
  rw [integral_const_mul]
  have hb := candidate_integral_shifted_euler_interval_scaled_le hU hU1
    (by positivity : 0 < 2 * σ) (by linarith : 2 * σ ≤ 2 * U)
    huv hlen hwindow hy
  exact (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hB _)).trans_eq (by ring)

/-- A common eighth-moment coefficient works on every small interval whose
size is at most four times its damped distance from the zeta pole. -/
theorem candidate_exists_finiteSpectralRegion_small_moment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Ioc (0 : ℝ) (1 / 8),
      ∀ U ∈ Ioc (0 : ℝ) (1 / 4), σ ≤ U → ∀ u v : ℝ,
      u ≤ v → v - u ≤ U → (∀ t ∈ Icc u v, |t| ≤ 2 * U) →
      (∀ t ∈ Icc u v, U ≤ 4 * (σ + |t|)) → ∀ y : ℕ,
      ⌊Real.exp (1 / (2 * U))⌋₊ ≤ y →
      (∫ ω, candidateFiniteSpectralRegionEnergy y σ (Icc u v) ω ^
        (1 / 8 : ℝ) ∂Problem520.μ) ≤ C * U ^ (1 / 16 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := candidate_complete_zeta_weight_central_upper
  have hCI : 0 ≤ candidateEulerIntervalMomentConstant := by
    have hc := candidateRankinNormalizerConstant_pos
    unfold candidateEulerIntervalMomentConstant
    positivity
  refine ⟨(8 * C) ^ (1 / 8 : ℝ) * candidateEulerIntervalMomentConstant,
    mul_nonneg (Real.rpow_nonneg (by positivity) _) hCI, ?_⟩
  intro σ hσ U hU hσU u v huv hlen hwindow hsep y hy
  have hσ' : σ ∈ Ioc (0 : ℝ) (1 / 2) := ⟨hσ.1, by linarith [hσ.2]⟩
  apply candidate_finiteSpectralRegion_interval_moment_le hσ' hU.1 hU.2 hσU
    huv hlen hwindow (by positivity) _ hy
  intro t ht
  have hd : 0 < σ + |t| := add_pos_of_pos_of_nonneg hσ.1 (abs_nonneg t)
  have hw := hb σ hσ' t (by linarith [hwindow t ht, hU.2])
  have hs : U ^ 2 ≤ 16 * (σ + |t|) ^ 2 := by
    nlinarith [hsep t ht, sq_nonneg (4 * (σ + |t|) - U)]
  have hd' : C / (σ + |t|) ^ 2 ≤ 16 * C / U ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hd) (sq_pos_of_pos hU.1)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs hC.le]
  calc
    _ ≤ σ * (16 * C / U ^ 2) := mul_le_mul_of_nonneg_left (hw.trans hd') hσ.1.le
    _ = (8 * C) * (2 * σ / U ^ 2) := by ring

end
end Erdos.Problem1144
