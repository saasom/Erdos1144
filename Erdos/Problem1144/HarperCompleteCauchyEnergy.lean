import Erdos.Problem1144.HarperCompleteEulerBridge

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem1144

/-!
# From the fixed vertical band to the complete Cauchy energy

The positive-probability theorem in `HarperCompleteEulerBridge` gives mass on
the fixed band `[1/3,1/2]`.  The first deterministic step toward the fresh
variance is to retain that mass after inserting the Cauchy kernel used by
Harman--Parseval.  This file proves that step, including genuine global
integrability of the complete Euler density against the kernel.
-/

/-- A sign-independent pointwise upper bound for one square correction. -/
noncomputable def harperSquareCorrectionUniformFactor (p : ℕ) : ℝ :=
  ((1 - (p : ℝ)⁻¹) ^ 2)⁻¹

/-- The corresponding finite-product upper bound. -/
noncomputable def harperSquareCorrectionUniformBound (y : ℕ) : ℝ :=
  ∏ p ∈ (y + 1).primesBelow, harperSquareCorrectionUniformFactor p

theorem sq_one_sub_inv_le_harperSquareCorrectionDenominator
    {p : ℕ} (hp : p.Prime) (t : ℝ) :
    (1 - (p : ℝ)⁻¹) ^ 2 ≤
      harperSquareCorrectionDenominator p t := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcos := Real.cos_le_one (2 * (t * Real.log (p : ℝ)))
  unfold harperSquareCorrectionDenominator
  rw [div_eq_mul_inv]
  nlinarith [inv_nonneg.mpr hpR.le]

theorem harperSquareCorrectionUniformFactor_pos
    {p : ℕ} (hp : p.Prime) :
    0 < harperSquareCorrectionUniformFactor p := by
  unfold harperSquareCorrectionUniformFactor
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hinv : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ (by positivity)).2 hpR
  exact inv_pos.mpr (sq_pos_of_pos (sub_pos.mpr hinv))

theorem harperSquareCorrectionFactor_le_uniformFactor
    (omega : Omega) {p : ℕ} (hp : p.Prime) (t : ℝ) :
    harperSquareCorrectionFactor omega p t ≤
      harperSquareCorrectionUniformFactor p := by
  rw [harperSquareCorrectionFactor_eq omega hp.pos t]
  exact inv_anti₀
    (sq_pos_of_pos (by
      have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      exact sub_pos.mpr ((inv_lt_one₀ (by positivity)).2 hpR)))
    (sq_one_sub_inv_le_harperSquareCorrectionDenominator hp t)

theorem harperSquareCorrectionDensity_le_uniformBound
    (y : ℕ) (omega : Omega) (t : ℝ) :
    harperSquareCorrectionDensity y omega t ≤
      harperSquareCorrectionUniformBound y := by
  classical
  unfold harperSquareCorrectionDensity harperSquareCorrectionUniformBound
  apply Finset.prod_le_prod
  · intro p hp
    exact Complex.normSq_nonneg _
  · intro p hp
    exact harperSquareCorrectionFactor_le_uniformFactor omega
      (Nat.prime_of_mem_primesBelow hp) t

theorem harperSquareCorrectionUniformBound_nonneg (y : ℕ) :
    0 ≤ harperSquareCorrectionUniformBound y := by
  classical
  unfold harperSquareCorrectionUniformBound
  apply Finset.prod_nonneg
  intro p hp
  exact (harperSquareCorrectionUniformFactor_pos
    (Nat.prime_of_mem_primesBelow hp)).le

/-- A deterministic finite bound for the complete density on the whole
vertical line. -/
noncomputable def harperCompleteEulerDensityUniformBound (y : ℕ) : ℝ :=
  harperSquareCorrectionUniformBound y *
    Problem520.harperEulerDensityUniformBound y

theorem harperCompleteEulerDensity_le_uniformBound
    (y : ℕ) (omega : Omega) (t : ℝ) :
    harperCompleteEulerDensity y omega t ≤
      harperCompleteEulerDensityUniformBound y := by
  rw [harperCompleteEulerDensity_eq_square_mul_squarefree]
  unfold harperCompleteEulerDensityUniformBound
  exact mul_le_mul
    (harperSquareCorrectionDensity_le_uniformBound y omega t)
    (Problem520.harperEulerDensity_le_uniformBound y omega t)
    (Problem520.harperEulerDensity_nonneg y omega t)
    (harperSquareCorrectionUniformBound_nonneg y)

theorem harperCompleteEulerDensityUniformBound_nonneg (y : ℕ) :
    0 ≤ harperCompleteEulerDensityUniformBound y := by
  unfold harperCompleteEulerDensityUniformBound
  exact mul_nonneg (harperSquareCorrectionUniformBound_nonneg y)
    (Problem520.harperEulerDensityUniformBound_nonneg y)

/-- The complete density is genuinely integrable after inserting the Cauchy
kernel; the Bochner integral below therefore does not use the nonintegrable
function convention. -/
theorem integrable_harperCompleteEulerDensity_div_cauchyKernel
    (y : ℕ) (omega : Omega) :
    Integrable (fun t : ℝ ↦
      harperCompleteEulerDensity y omega t /
        ((1 / 4 : ℝ) + t ^ 2)) := by
  let B : ℝ := harperCompleteEulerDensityUniformBound y
  let kernel : ℝ → ℝ := fun t ↦ 1 / ((1 / 4 : ℝ) + t ^ 2)
  have hkernel : Integrable kernel := by
    simpa only [kernel, show ((1 / 2 : ℝ) ^ 2) = 1 / 4 by norm_num] using
      Problem520.integrable_one_div_harperCauchyKernel
  have hmajor : Integrable (fun t ↦ B * kernel t) := hkernel.const_mul B
  apply hmajor.mono'
  · exact (continuous_harperCompleteEulerDensity_vertical y omega).measurable
      |>.div (by fun_prop) |>.aestronglyMeasurable
  · exact ae_of_all _ fun t ↦ by
      have hden : 0 < (1 / 4 : ℝ) + t ^ 2 := by positivity
      have htarget : 0 ≤ harperCompleteEulerDensity y omega t /
          ((1 / 4 : ℝ) + t ^ 2) :=
        div_nonneg (harperCompleteEulerDensity_nonneg y omega t) hden.le
      have hupper : harperCompleteEulerDensity y omega t /
            ((1 / 4 : ℝ) + t ^ 2) ≤
          B / ((1 / 4 : ℝ) + t ^ 2) :=
        (div_le_div_iff_of_pos_right hden).2
          (harperCompleteEulerDensity_le_uniformBound y omega t)
      rw [Real.norm_eq_abs, abs_of_nonneg htarget]
      simpa only [B, kernel, div_eq_mul_inv, one_mul] using hupper

/-- Complete vertical energy with the Cauchy weight and the same logarithmic
normalization as the fixed-band energy. -/
noncomputable def harperCompleteCauchyEnergy
    (y : ℕ) (omega : Omega) : ℝ :=
  (∫ t : ℝ, harperCompleteEulerDensity y omega t /
      ((1 / 4 : ℝ) + t ^ 2)) / Real.log (y : ℝ)

/-- On `[1/3,1/2]` the Cauchy denominator is at most `1/2`.  Hence the full
Cauchy energy retains at least twice the unweighted fixed-band mass. -/
theorem two_mul_harperCompleteLowerBandEnergy_le_cauchyEnergy
    {y : ℕ} (hy : 1 < y) (omega : Omega) :
    2 * harperCompleteEulerSetEnergy
        y harperLowerVerticalBand omega ≤
      harperCompleteCauchyEnergy y omega := by
  let density : ℝ → ℝ := fun t ↦ harperCompleteEulerDensity y omega t
  let weighted : ℝ → ℝ := fun t ↦
    density t / ((1 / 4 : ℝ) + t ^ 2)
  have hdensity : IntegrableOn density harperLowerVerticalBand := by
    simpa only [density] using
      integrableOn_harperCompleteEulerDensity_lowerBand y omega
  have hweighted : Integrable weighted := by
    simpa only [weighted, density] using
      integrable_harperCompleteEulerDensity_div_cauchyKernel y omega
  have hpoint : ∀ t ∈ harperLowerVerticalBand,
      2 * density t ≤ weighted t := by
    intro t ht
    have htBounds : (1 : ℝ) / 3 ≤ t ∧ t ≤ (1 : ℝ) / 2 := ht
    have hden : 0 < (1 / 4 : ℝ) + t ^ 2 := by positivity
    have hdenHalf : (1 / 4 : ℝ) + t ^ 2 ≤ 1 / 2 := by
      nlinarith [sq_nonneg t]
    have hnonneg := harperCompleteEulerDensity_nonneg y omega t
    dsimp only [weighted]
    exact (le_div_iff₀ hden).2 (by nlinarith)
  have hband :
      (∫ t in harperLowerVerticalBand, 2 * density t) ≤
        ∫ t in harperLowerVerticalBand, weighted t :=
    setIntegral_mono_on (hdensity.const_mul 2) hweighted.integrableOn
      measurableSet_harperLowerVerticalBand hpoint
  have hfull :
      (∫ t in harperLowerVerticalBand, weighted t) ≤ ∫ t, weighted t :=
    setIntegral_le_integral hweighted
      (ae_of_all _ fun t ↦ div_nonneg
        (harperCompleteEulerDensity_nonneg y omega t) (by positivity))
  rw [integral_const_mul] at hband
  have hlog : 0 ≤ Real.log (y : ℝ) :=
    (Real.log_pos (by exact_mod_cast hy)).le
  unfold harperCompleteEulerSetEnergy harperCompleteCauchyEnergy
  change 2 * ((∫ t in harperLowerVerticalBand, density t) /
      Real.log (y : ℝ)) ≤ (∫ t, weighted t) / Real.log (y : ℝ)
  calc
    2 * ((∫ t in harperLowerVerticalBand, density t) /
        Real.log (y : ℝ)) =
      (2 * ∫ t in harperLowerVerticalBand, density t) /
        Real.log (y : ℝ) := by ring
    _ ≤ (∫ t, weighted t) / Real.log (y : ℝ) :=
      div_le_div_of_nonneg_right (hband.trans hfull) hlog

/-- Consequently the complete Cauchy energy itself has the same unconditional
fixed-probability critical lower tail along scheduled cutoffs. -/
theorem exists_harperCompleteCauchyEnergy_fixedProbability_unconditional :
    ∃ delta : ℝ, 0 < delta ∧ ∃ c : ℝ, 0 < c ∧ ∃ start : ℕ,
      ∀ n : ℕ,
        delta ≤ Problem520.μ.real
          {omega |
            c * harperInitialCriticalScale
                (Problem520.harperBlockEndpoint (start + n)) ≤
              harperCompleteCauchyEnergy
                (Problem520.harperBlockEndpoint (start + n)) omega} := by
  obtain ⟨delta, hdelta, c, hc, start, hband⟩ :=
    exists_harperCompleteLowerVerticalBandEnergy_fixedProbability_unconditional
  refine ⟨delta, hdelta, 2 * c, mul_pos (by norm_num) hc, start, ?_⟩
  intro n
  let y : ℕ := Problem520.harperBlockEndpoint (start + n)
  have hy : 1 < y := by
    have := Problem520.harperBlockEndpoint_ge_sixteen (start + n)
    omega
  have hsubset :
      {omega |
        c * harperInitialCriticalScale y ≤
          harperCompleteEulerSetEnergy
            y harperLowerVerticalBand omega} ⊆
      {omega |
        (2 * c) * harperInitialCriticalScale y ≤
          harperCompleteCauchyEnergy y omega} := by
    intro omega homega
    have htransfer :=
      two_mul_harperCompleteLowerBandEnergy_le_cauchyEnergy hy omega
    calc
      (2 * c) * harperInitialCriticalScale y =
          2 * (c * harperInitialCriticalScale y) := by ring
      _ ≤ 2 * harperCompleteEulerSetEnergy
          y harperLowerVerticalBand omega :=
        mul_le_mul_of_nonneg_left homega (by norm_num)
      _ ≤ harperCompleteCauchyEnergy y omega := htransfer
  change delta ≤ Problem520.μ.real
    {omega |
      (2 * c) * harperInitialCriticalScale y ≤
        harperCompleteCauchyEnergy y omega}
  exact (hband n).trans (measureReal_mono hsubset)

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.integrable_harperCompleteEulerDensity_div_cauchyKernel
#print axioms Erdos.Problem1144.two_mul_harperCompleteLowerBandEnergy_le_cauchyEnergy
#print axioms Erdos.Problem1144.exists_harperCompleteCauchyEnergy_fixedProbability_unconditional
