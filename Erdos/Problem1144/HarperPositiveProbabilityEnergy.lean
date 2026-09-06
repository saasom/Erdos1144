import Erdos.Problem1144.FractionalMomentPositiveProbability
import Erdos.Problem520.HarperUnconditionalInitialMoment

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Erdos
namespace Problem1144

/-!
# Reusing the Problem 520 Harper moment at positive probability

The unconditional Problem 520 theorem already supplies the sharp upper
`2/3` moment of the normalized smooth energy.  The only new multiplicative-
chaos input needed for a fixed positive probability is therefore the matching
lower `1/2` moment packaged below.
-/

/-- The critical deterministic scale for the normalized Harper energy. -/
noncomputable def harperInitialCriticalScale (y : ℕ) : ℝ :=
  (1 + Problem520.logLogNat y) ^ (-(1 : ℝ) / 2)

theorem harperInitialCriticalScale_pos {y : ℕ} (hy : 4 ≤ y) :
    0 < harperInitialCriticalScale y := by
  exact Real.rpow_pos_of_pos
    (Problem520.one_add_logLogNat_pos_of_four_le hy) _

theorem harperInitialCriticalScale_rpow_twoThird
    {y : ℕ} (hy : 4 ≤ y) :
    harperInitialCriticalScale y ^ ((2 : ℝ) / 3) =
      1 / (1 + Problem520.logLogNat y) ^ ((1 : ℝ) / 3) := by
  have hL : 0 < 1 + Problem520.logLogNat y :=
    Problem520.one_add_logLogNat_pos_of_four_le hy
  unfold harperInitialCriticalScale
  rw [← Real.rpow_mul hL.le]
  have hexp : (-(1 : ℝ) / 2) * ((2 : ℝ) / 3) =
      -((1 : ℝ) / 3) := by ring
  rw [hexp, Real.rpow_neg hL.le]
  simp only [one_div]

/-- The one genuinely new moment input.  It asserts the sharp lower
square-root moment at the same scale as the already proved upper `2/3`
moment. -/
def HarperRademacherInitialHalfMomentLowerBound (c : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y → 4 ≤ y →
    c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2) ≤
      ∫ omega,
        Problem520.harperInitialNormalizedEnergy y omega ^ ((1 : ℝ) / 2)
          ∂Problem520.μ

/-- Premise spelling out the remaining deep analytic checkpoint. -/
def HarperRademacherInitialHalfMomentLowerStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ,
    HarperRademacherInitialHalfMomentLowerBound c Y

theorem harperInitialNormalizedEnergy_nonneg
    {y : ℕ} (hy : 1 < y) (omega : Problem520.Omega) :
    0 ≤ Problem520.harperInitialNormalizedEnergy y omega := by
  rw [← Problem520.caichNormalizedEnergy_initial_eq_harper 1 1 y hy omega]
  exact Problem520.caichNormalizedEnergy_nonneg hy omega

theorem stronglyMeasurable_harperInitialNormalizedEnergy (y : ℕ) :
    StronglyMeasurable
      (Problem520.harperInitialNormalizedEnergy y) := by
  unfold Problem520.harperInitialNormalizedEnergy
  have hH : StronglyMeasurable
      (fun omega : Problem520.Omega ↦ Problem520.smoothEnergy omega y) :=
    (Problem520.stronglyMeasurable_smoothEnergy y).mono
      (Filtration.piFinset.le _)
  exact (hH.const_mul (2 * Real.pi)).div stronglyMeasurable_const

theorem measurableSet_halfMomentLargeEvent_harperInitial
    (y : ℕ) (a : ℝ) :
    MeasurableSet (halfMomentLargeEvent
      (Problem520.harperInitialNormalizedEnergy y) a) := by
  unfold halfMomentLargeEvent
  exact measurableSet_le measurable_const
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).measurable.comp
      (stronglyMeasurable_harperInitialNormalizedEnergy y).measurable)

theorem integrable_harperInitialNormalizedEnergy_half
    {y : ℕ} (hy : 1 < y) :
    Integrable (fun omega ↦
      Problem520.harperInitialNormalizedEnergy y omega ^ ((1 : ℝ) / 2))
        Problem520.μ := by
  exact Problem520.integrable_rpow_of_integrable_nonneg
    (Problem520.integrable_harperInitialNormalizedEnergy y)
    (harperInitialNormalizedEnergy_nonneg hy) (by norm_num) (by norm_num)

/-- One-scale composition of a sharp lower half moment with the existing
sharp upper two-thirds moment. -/
theorem harperInitialCriticalEnergy_probability_lower
    {c C : ℝ} {Yhalf Ytwo y : ℕ}
    (hc : 0 < c) (hC : 0 < C)
    (hhalf : HarperRademacherInitialHalfMomentLowerBound c Yhalf)
    (htwo : Problem520.HarperRademacherInitialMomentBound C Ytwo)
    (hyHalf : Yhalf ≤ y) (hyTwo : Ytwo ≤ y) (hy : 4 ≤ y) :
    (c / (2 * C ^ ((3 : ℝ) / 4))) ^ (4 : ℝ) ≤
      Problem520.μ.real
        (halfMomentLargeEvent
          (Problem520.harperInitialNormalizedEnergy y)
          (c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2))) := by
  let Z : Problem520.Omega → ℝ :=
    Problem520.harperInitialNormalizedEnergy y
  let K : ℝ := harperInitialCriticalScale y
  have hy1 : 1 < y := by omega
  have hZnonneg : ∀ omega, 0 ≤ Z omega :=
    harperInitialNormalizedEnergy_nonneg hy1
  have hZint : Integrable Z Problem520.μ :=
    Problem520.integrable_harperInitialNormalizedEnergy y
  have hhalfInt : Integrable
      (fun omega ↦ Z omega ^ ((1 : ℝ) / 2)) Problem520.μ :=
    integrable_harperInitialNormalizedEnergy_half hy1
  have htwoInt : Integrable
      (fun omega ↦ Z omega ^ ((2 : ℝ) / 3)) Problem520.μ := by
    simpa only [Z, Problem520.harperTwoThird] using
      Problem520.integrable_harperInitialNormalizedEnergy_twoThird hy1
  have hhalfLp : MemLp (fun omega ↦ Z omega ^ ((1 : ℝ) / 2))
      (ENNReal.ofReal ((4 : ℝ) / 3)) Problem520.μ := by
    have h := Problem520.memLp_rpow_of_integrable_rpow
      (ν := Problem520.μ) (Z := Z)
      (q := (1 : ℝ) / 2) (r := (2 : ℝ) / 3)
      (by norm_num) (by norm_num) hZint hZnonneg htwoInt
    norm_num at h ⊢
    exact h
  have htwoScale :
      (∫ omega, Z omega ^ ((2 : ℝ) / 3) ∂Problem520.μ) ≤
        C * K ^ ((2 : ℝ) / 3) := by
    calc
      (∫ omega, Z omega ^ ((2 : ℝ) / 3) ∂Problem520.μ) ≤
          C / (1 + Problem520.logLogNat y) ^ ((1 : ℝ) / 3) :=
        htwo y hyTwo (by omega)
      _ = C * K ^ ((2 : ℝ) / 3) := by
        rw [harperInitialCriticalScale_rpow_twoThird hy]
        ring
  exact criticalScale_halfMoment_twoThird_probability_lower
    (nu := Problem520.μ) (Z := Z) (c := c) (C := C) (K := K)
    (measurableSet_halfMomentLargeEvent_harperInitial y
      (c * K ^ ((1 : ℝ) / 2)))
    hZnonneg hhalfInt hhalfLp hc hC (harperInitialCriticalScale_pos hy)
    (hhalf y hyHalf hy) htwoScale

/-- The unconditional Problem 520 upper moment plus the single lower-half-
moment statement produce a scale-uniform positive probability. -/
theorem exists_harperInitialCriticalEnergy_fixedProbability
    (hhalfStatement : HarperRademacherInitialHalfMomentLowerStatement) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ y : ℕ,
      Y ≤ y →
      delta ≤ Problem520.μ.real
        (halfMomentLargeEvent
          (Problem520.harperInitialNormalizedEnergy y)
          (c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2))) := by
  obtain ⟨c, hc, Yhalf, hhalf⟩ := hhalfStatement
  obtain ⟨C, hC, Ytwo, hYtwo, htwo⟩ :=
    Problem520.harperRademacherInitialMomentStatement_unconditional
  let delta : ℝ := (c / (2 * C ^ ((3 : ℝ) / 4))) ^ (4 : ℝ)
  have hdelta : 0 < delta := by
    exact Real.rpow_pos_of_pos
      (div_pos hc (mul_pos (by norm_num) (Real.rpow_pos_of_pos hC _))) _
  refine ⟨delta, hdelta, c, hc, max 4 (max Yhalf Ytwo), ?_⟩
  intro y hy
  have hy4 : 4 ≤ y := (le_max_left _ _).trans hy
  have hyBoth : max Yhalf Ytwo ≤ y := (le_max_right _ _).trans hy
  have hyHalf : Yhalf ≤ y := (le_max_left _ _).trans hyBoth
  have hyTwo : Ytwo ≤ y := (le_max_right _ _).trans hyBoth
  simpa only [delta] using harperInitialCriticalEnergy_probability_lower
    hc hC hhalf htwo hyHalf hyTwo hy4

end Problem1144
end Erdos
