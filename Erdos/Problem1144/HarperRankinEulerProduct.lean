import Erdos.Problem1144.HarperRankinBlockIndependence
import Erdos.Problem520.HarperTiltedOmega

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The shifted Euler density on the infinite sign space

This is the `Omega`-level interface for the finite Rankin-tilted cube.  It
identifies the shifted density with its finite restriction and proves the
exact event change of measure needed by a restricted-energy construction.
-/

/-- Squared finite Euler product on the Rankin-shifted line. -/
noncomputable def harperRankinEulerDensity
    (y : ℕ) (a : ℝ) (omega : Problem520.Omega) (t : ℝ) : ℝ :=
  ∏ p ∈ (y + 1).primesBelow, harperRankinEulerFactor omega p a t

theorem harperRankinEulerDensity_nonneg
    (y : ℕ) (a : ℝ) (omega : Problem520.Omega) (t : ℝ) :
    0 ≤ harperRankinEulerDensity y a omega t := by
  unfold harperRankinEulerDensity
  exact Finset.prod_nonneg fun p hp ↦
    harperRankinEulerFactor_nonneg omega p a t

/-- Product normalizer in ordinary prime-finset form. -/
noncomputable def harperRankinPrimeEnergyNormalizer
    (y : ℕ) (a : ℝ) : ℝ :=
  ∏ p ∈ (y + 1).primesBelow, harperRankinEulerNormalizer p a

theorem harperRankinPrimeEnergyNormalizer_pos (y : ℕ) (a : ℝ) :
    0 < harperRankinPrimeEnergyNormalizer y a := by
  unfold harperRankinPrimeEnergyNormalizer
  exact Finset.prod_pos fun p hp ↦ harperRankinEulerNormalizer_pos p a

/-- Normalized shifted density on `Omega`. -/
noncomputable def normalizedHarperRankinEulerDensity
    (y : ℕ) (a : ℝ) (omega : Problem520.Omega) (t : ℝ) : ℝ :=
  harperRankinEulerDensity y a omega t /
    harperRankinPrimeEnergyNormalizer y a

theorem normalizedHarperRankinEulerDensity_nonneg
    (y : ℕ) (a : ℝ) (omega : Problem520.Omega) (t : ℝ) :
    0 ≤ normalizedHarperRankinEulerDensity y a omega t := by
  exact div_nonneg (harperRankinEulerDensity_nonneg y a omega t)
    (harperRankinPrimeEnergyNormalizer_pos y a).le

theorem harperRankinPrimeEnergyNormalizer_eq_cube
    (y : ℕ) (a : ℝ) :
    harperRankinPrimeEnergyNormalizer y a =
      harperRankinEnergyNormalizer y a := by
  unfold harperRankinPrimeEnergyNormalizer harperRankinEnergyNormalizer
  exact (Finset.prod_coe_sort ((y + 1).primesBelow)
    (fun p ↦ harperRankinEulerNormalizer p a)).symm

theorem harperRankinCubeDensity_harperPrimeRestriction
    (y : ℕ) (a t : ℝ) (omega : Problem520.Omega) :
    harperRankinCubeDensity y a t
        (Problem520.harperPrimeRestriction y omega) =
      harperRankinEulerDensity y a omega t := by
  unfold harperRankinCubeDensity harperRankinEulerDensity
    harperRankinCoordinateFactor
  calc
    (∏ p : Problem520.HarperPrimeIndex y,
        harperRankinEulerFactor
          (fun _ ↦ Problem520.harperPrimeRestriction y omega p) p.1 a t) =
        ∏ p : Problem520.HarperPrimeIndex y,
          harperRankinEulerFactor omega p.1 a t := by
      apply Finset.prod_congr rfl
      intro p hp
      simp [harperRankinEulerFactor, Problem520.ε,
        Problem520.harperPrimeRestriction]
    _ = ∏ p ∈ (y + 1).primesBelow,
        harperRankinEulerFactor omega p a t :=
      Finset.prod_coe_sort ((y + 1).primesBelow)
        (fun p ↦ harperRankinEulerFactor omega p a t)

theorem normalizedHarperRankinCubeDensity_harperPrimeRestriction
    (y : ℕ) (a t : ℝ) (omega : Problem520.Omega) :
    normalizedHarperRankinCubeDensity y a t
        (Problem520.harperPrimeRestriction y omega) =
      normalizedHarperRankinEulerDensity y a omega t := by
  unfold normalizedHarperRankinCubeDensity
    normalizedHarperRankinEulerDensity
  rw [harperRankinCubeDensity_harperPrimeRestriction,
    harperRankinPrimeEnergyNormalizer_eq_cube]

/-- Exact shifted change of measure for every finite-coordinate observable. -/
theorem integral_harperRankinTiltedCubeLaw_eq_omega
    (y : ℕ) (a t : ℝ)
    (g : Problem520.HarperPrimeCube y → ℝ) :
    (∫ eta, g eta ∂harperRankinTiltedCubeLaw y a t) =
      ∫ omega,
        normalizedHarperRankinEulerDensity y a omega t *
          g (Problem520.harperPrimeRestriction y omega) ∂Problem520.μ := by
  calc
    (∫ eta, g eta ∂harperRankinTiltedCubeLaw y a t) =
        ∫ eta, normalizedHarperRankinCubeDensity y a t eta * g eta
          ∂Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦
            Problem520.coin) :=
      integral_harperRankinTiltedCubeLaw_eq y a t g
    _ = ∫ omega,
        normalizedHarperRankinEulerDensity y a omega t *
          g (Problem520.harperPrimeRestriction y omega) ∂Problem520.μ := by
      rw [← Problem520.integral_comp_harperPrimeRestriction_mu y
        (fun eta ↦ normalizedHarperRankinCubeDensity y a t eta * g eta)]
      apply integral_congr_ae
      exact ae_of_all Problem520.μ fun omega ↦ by
        change normalizedHarperRankinCubeDensity y a t
            (Problem520.harperPrimeRestriction y omega) *
              g (Problem520.harperPrimeRestriction y omega) =
          normalizedHarperRankinEulerDensity y a omega t *
            g (Problem520.harperPrimeRestriction y omega)
        rw [normalizedHarperRankinCubeDensity_harperPrimeRestriction]

/-- Event form of the exact shifted change of measure. -/
theorem harperRankinTiltedCubeLaw_real_apply_eq_omega
    (y : ℕ) (a t : ℝ)
    (A : Set (Problem520.HarperPrimeCube y)) :
    (harperRankinTiltedCubeLaw y a t).real A =
      ∫ omega in Problem520.harperPrimeRestriction y ⁻¹' A,
        normalizedHarperRankinEulerDensity y a omega t ∂Problem520.μ := by
  have hA : MeasurableSet A := Set.toFinite A |>.measurableSet
  have hpre : MeasurableSet
      (Problem520.harperPrimeRestriction y ⁻¹' A) :=
    hA.preimage (Problem520.measurable_harperPrimeRestriction y)
  rw [← integral_indicator_one (μ := harperRankinTiltedCubeLaw y a t) hA,
    integral_harperRankinTiltedCubeLaw_eq_omega]
  rw [← integral_indicator hpre]
  apply integral_congr_ae
  exact ae_of_all Problem520.μ fun omega ↦ by
    by_cases hmem : Problem520.harperPrimeRestriction y omega ∈ A
    · simp [Set.indicator_of_mem, hmem]
    · simp [Set.indicator_of_notMem, hmem]

#print axioms Erdos.Problem1144.integral_harperRankinTiltedCubeLaw_eq_omega
#print axioms Erdos.Problem1144.harperRankinTiltedCubeLaw_real_apply_eq_omega

end

end Problem1144
end Erdos
