import Erdos.Problem1144.HarperCandidateWeightedEulerIntervalBounds
import Erdos.Problem1144.HarperCandidateZetaUpper
import Erdos.Problem1144.HarperRankinRestrictedGraph

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The full deterministic zeta weight multiplied by the literal finite
squarefree Euler density. The prime cutoff does not truncate zeta. -/
def candidateFiniteSpectralEnergy (y : ℕ) (σ : ℝ) (ω : Problem520.Omega) : ℝ :=
  σ * ∫ t : ℝ, candidateCompleteZetaWeight σ t *
    harperRankinEulerDensity y (2 * σ) ω t

/-- Every real observable of the finite Euler path factors through a finite
prime cube, even when the observable involves an improper integral. -/
theorem candidate_measurable_euler_functional (y : ℕ) (a : ℝ)
    (F : (ℝ → ℝ) → ℝ) :
    Measurable (fun ω => F (harperRankinEulerDensity y a ω)) := by
  have he : (fun ω => F (harperRankinEulerDensity y a ω)) =
      (fun η : Problem520.HarperPrimeCube y =>
        F (fun t => harperRankinCubeDensity y a t η)) ∘
        Problem520.harperPrimeRestriction y := by
    funext ω
    simp only [Function.comp_def, harperRankinCubeDensity_harperPrimeRestriction]
  rw [he]
  exact (measurable_of_finite _).comp (Problem520.measurable_harperPrimeRestriction y)

theorem candidate_integrable_euler_functional (y : ℕ) (a : ℝ)
    (F : (ℝ → ℝ) → ℝ) :
    Integrable (fun ω => F (harperRankinEulerDensity y a ω)) Problem520.μ := by
  have hmp : MeasurePreserving (Problem520.harperPrimeRestriction y) Problem520.μ
      (Problem520.harperFairCubeLaw y) :=
    ⟨Problem520.measurable_harperPrimeRestriction y, Problem520.map_harperPrimeRestriction_mu y⟩
  have h := hmp.integrable_comp_of_integrable
    (g := fun η : Problem520.HarperPrimeCube y =>
      F (fun t => harperRankinCubeDensity y a t η)) Integrable.of_finite
  simpa only [Function.comp_def, harperRankinCubeDensity_harperPrimeRestriction] using h

theorem candidate_integral_euler_functional (y : ℕ) (a : ℝ)
    (F : (ℝ → ℝ) → ℝ) :
    (∫ ω, F (harperRankinEulerDensity y a ω) ∂Problem520.μ) =
      ∫ η, F (fun t => harperRankinCubeDensity y a t η)
        ∂Problem520.harperFairCubeLaw y := by
  simpa only [harperRankinCubeDensity_harperPrimeRestriction] using
    Problem520.integral_comp_harperPrimeRestriction_mu y
      (fun η => F (fun t => harperRankinCubeDensity y a t η))

/-- Exact first moment of the shifted density under the original sign law. -/
theorem candidate_integral_shifted_euler_density (y : ℕ) (a t : ℝ) :
    (∫ ω, harperRankinEulerDensity y a ω t ∂Problem520.μ) =
      harperRankinPrimeEnergyNormalizer y a := by
  have h := integral_harperRankinTiltedCubeLaw_eq_omega y a t (fun _ => 1)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one,
    normalizedHarperRankinEulerDensity, integral_div] at h
  exact (div_eq_one_iff_eq (harperRankinPrimeEnergyNormalizer_pos y a).ne').mp h.symm

/-- A finite Euler factor preserves integrability of an arbitrary frequency
weight, by its already proved uniform deterministic bound. -/
theorem candidate_integrable_weight_mul_euler (y : ℕ) (a : ℝ)
    (ω : Problem520.Omega) {w : ℝ → ℝ} (hw : Integrable w) :
    Integrable (fun t => w t * harperRankinEulerDensity y a ω t) := by
  apply (hw.norm.mul_const (harperRankinEulerDensityUniformBound y a)).mono'
    (hw.aestronglyMeasurable.mul
      (candidate_continuous_shifted_euler_density y a ω).aestronglyMeasurable)
  exact ae_of_all _ fun t => by
    change ‖w t * harperRankinEulerDensity y a ω t‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs (harperRankinEulerDensity y a ω t),
      abs_of_nonneg (harperRankinEulerDensity_nonneg y a ω t)]
    exact mul_le_mul_of_nonneg_left (harperRankinEulerDensity_le_uniformBound y a ω t)
      (norm_nonneg _)

/-- Frequency integration and the finite-prime expectation commute. -/
theorem candidate_integral_weight_mul_euler (y : ℕ) (a : ℝ)
    {w : ℝ → ℝ} (hw : Integrable w) :
    (∫ ω, (∫ t, w t * harperRankinEulerDensity y a ω t) ∂Problem520.μ) =
      (∫ t, w t) * harperRankinPrimeEnergyNormalizer y a := by
  rw [candidate_integral_euler_functional y a (fun f => ∫ t, w t * f t)]
  let P := Problem520.harperFairCubeLaw y
  have hi (η : Problem520.HarperPrimeCube y) :
      Integrable (fun t => w t * harperRankinCubeDensity y a t η) := by
    let ω : Problem520.Omega := fun n =>
      if h : n ∈ (y + 1).primesBelow then η ⟨n, h⟩ else false
    have he : Problem520.harperPrimeRestriction y ω = η := by
      funext p
      simp [Problem520.harperPrimeRestriction, ω, p.2]
    simpa only [← he, harperRankinCubeDensity_harperPrimeRestriction] using
      candidate_integrable_weight_mul_euler y a ω hw
  have hswap : (∫ η, (∫ t, w t * harperRankinCubeDensity y a t η) ∂P) =
      ∫ t, ∫ η, w t * harperRankinCubeDensity y a t η ∂P := by
    simp_rw [integral_fintype (Integrable.of_finite : Integrable _ P), smul_eq_mul]
    rw [integral_finset_sum _ (fun η _ => (hi η).const_mul _)]
    simp_rw [integral_const_mul]
  rw [hswap]
  simp_rw [integral_const_mul]
  have he (t : ℝ) : (∫ η, harperRankinCubeDensity y a t η ∂P) =
      harperRankinPrimeEnergyNormalizer y a := by
    rw [← candidate_integral_euler_functional y a (fun f => f t)]
    exact candidate_integral_shifted_euler_density y a t
  simp_rw [he]
  exact integral_mul_const _ _

/-- For each positive damping in the working strip the full zeta weight
is integrable, including its central interval. -/
theorem candidate_integrable_complete_zeta_weight {σ : ℝ}
    (hσ : σ ∈ Ioc (0 : ℝ) (1 / 2)) :
    Integrable (candidateCompleteZetaWeight σ) := by
  obtain ⟨C, hC, hb⟩ := candidate_complete_zeta_weight_high_integral_bounded
    (by norm_num : (0 : ℝ) < 1)
  have hi : IntegrableOn (candidateCompleteZetaWeight σ) (Icc (-1 : ℝ) 1) :=
    (continuous_candidateCompleteZetaWeight hσ.1).integrableOn_Icc
  have hu := hi.union (hb σ hσ).1
  have he : Icc (-1 : ℝ) 1 ∪ {t : ℝ | 1 ≤ |t|} = univ := by
    ext t
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases ht : 1 ≤ |t|
    · exact Or.inr ht
    · exact Or.inl (abs_le.mp (le_of_lt (lt_of_not_ge ht)))
  rwa [he, integrableOn_univ] at hu

theorem candidateFiniteSpectralEnergy_nonneg (y : ℕ) {σ : ℝ}
    (hσ : 0 ≤ σ) (ω : Problem520.Omega) :
    0 ≤ candidateFiniteSpectralEnergy y σ ω :=
  mul_nonneg hσ (integral_nonneg fun t =>
    mul_nonneg (candidateCompleteZetaWeight_nonneg σ t)
      (harperRankinEulerDensity_nonneg y (2 * σ) ω t))

theorem candidate_measurable_finiteSpectralEnergy (y : ℕ) (σ : ℝ) :
    Measurable (candidateFiniteSpectralEnergy y σ) :=
  candidate_measurable_euler_functional y (2 * σ)
    (fun f => σ * ∫ t, candidateCompleteZetaWeight σ t * f t)

theorem candidate_integrable_finiteSpectralEnergy_rpow (y : ℕ) (σ q : ℝ) :
    Integrable (fun ω => candidateFiniteSpectralEnergy y σ ω ^ q) Problem520.μ :=
  candidate_integrable_euler_functional y (2 * σ)
    (fun f => (σ * ∫ t, candidateCompleteZetaWeight σ t * f t) ^ q)

end
end Erdos.Problem1144
