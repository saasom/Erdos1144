import Erdos.Problem1144.HarperTwoHeightGaussianLaw
import Mathlib.MeasureTheory.Integral.Prod

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Exact product-Fejer inversion

This discharges the last formal hypothesis in the bivariate smoothed-cell
comparison.  The key simplification relative to a CDF inversion is that a
bounded interval has a uniformly bounded Fourier multiplier.  Consequently
no moment hypothesis is required for either bivariate probability law.
-/

theorem measurable_harperFejerIntervalMultiplier
    (T a b : Real) :
    Measurable (harperFejerIntervalMultiplier T a b) := by
  unfold harperFejerIntervalMultiplier
  apply Measurable.ite (measurableSet_singleton 0)
    measurable_const
  exact ((((Complex.measurable_exp.comp (by fun_prop)).sub
    (Complex.measurable_exp.comp (by fun_prop))).mul
      (Complex.continuous_ofReal.measurable.comp
        (Problem520.continuous_harperFejerTriangle.measurable.comp
          (by fun_prop)))).div (by fun_prop))

/-- The Fourier integrand of a translated bounded interval. -/
noncomputable def harperFejerTranslatedIntervalIntegrand
    (T a b x v : Real) : Complex :=
  Complex.exp (((v * x : Real) : Complex) * Complex.I) *
    harperFejerIntervalMultiplier T a b v

theorem measurable_harperFejerTranslatedIntervalIntegrand
    (T a b x : Real) :
    Measurable (harperFejerTranslatedIntervalIntegrand T a b x) := by
  exact (Complex.measurable_exp.comp (by fun_prop)).mul
    (measurable_harperFejerIntervalMultiplier T a b)

theorem norm_harperFejerTranslatedIntervalIntegrand_le
    (T a b x v : Real) :
    ‖harperFejerTranslatedIntervalIntegrand T a b x v‖ ≤ |b - a| := by
  unfold harperFejerTranslatedIntervalIntegrand
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact norm_harperFejerIntervalMultiplier_le T a b v

/-- A translated Fejer-smoothed interval mass is the compactly supported
Fourier integral with the static interval multiplier. -/
theorem cdf_harperFejerMeasureScaled_translatedInterval_eq_fourier
    {T : Real} (hT : 0 < T) (a b x : Real) :
    (((cdf (Problem520.harperFejerMeasureScaled T) (b - x) -
        cdf (Problem520.harperFejerMeasureScaled T) (a - x) : Real) :
          Complex)) =
      ((((2 * Real.pi : Real)⁻¹ : Real) : Complex) *
        ∫ v in Icc (-T) T,
          harperFejerTranslatedIntervalIntegrand T a b x v) := by
  rw [Problem520.cdf_harperFejerMeasureScaled_sub_eq_fourier hT]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (volume.ae_ne 0)] with v hv
  rw [if_neg hv]
  unfold harperFejerTranslatedIntervalIntegrand
    harperFejerIntervalMultiplier
  rw [if_neg hv]
  have hbphase :
      Complex.exp (((-v * (b - x) : Real) : Complex) * Complex.I) =
        Complex.exp (((v * x : Real) : Complex) * Complex.I) *
          Complex.exp (((-v * b : Real) : Complex) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have haphase :
      Complex.exp (((-v * (a - x) : Real) : Complex) * Complex.I) =
        Complex.exp (((v * x : Real) : Complex) * Complex.I) *
          Complex.exp (((-v * a : Real) : Complex) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hbphase, haphase]
  ring

/-- Spatial phase times the two bounded interval multipliers. -/
noncomputable def harperBivariateSpatialRectangleIntegrand
    (T a b c d : Real) (x z : Real × Real) : Complex :=
  Complex.exp
      ((((z.1 * x.1 + z.2 * x.2 : Real) : Complex) * Complex.I)) *
    harperFejerIntervalMultiplier T a b z.1 *
      harperFejerIntervalMultiplier T c d z.2

theorem measurable_harperBivariateSpatialRectangleIntegrand
    (T a b c d : Real) :
    Measurable (Function.uncurry
      (harperBivariateSpatialRectangleIntegrand T a b c d)) := by
  exact (((Complex.measurable_exp.comp (by fun_prop)).mul
    ((measurable_harperFejerIntervalMultiplier T a b).comp
      measurable_snd.fst)).mul
        ((measurable_harperFejerIntervalMultiplier T c d).comp
          measurable_snd.snd))

theorem norm_harperBivariateSpatialRectangleIntegrand_le
    (T a b c d : Real) (x z : Real × Real) :
    ‖harperBivariateSpatialRectangleIntegrand T a b c d x z‖ ≤
      |b - a| * |d - c| := by
  unfold harperBivariateSpatialRectangleIntegrand
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact mul_le_mul
    (norm_harperFejerIntervalMultiplier_le T a b z.1)
    (norm_harperFejerIntervalMultiplier_le T c d z.2)
    (norm_nonneg _) (abs_nonneg _)

/-- Pointwise product of two translated Fejer interval masses as a double
Fourier integral. -/
theorem cdf_harperFejerMeasureScaled_translatedRectangle_eq_fourier
    {T : Real} (hT : 0 < T) (a b c d : Real) (x : Real × Real) :
    ((((cdf (Problem520.harperFejerMeasureScaled T) (b - x.1) -
          cdf (Problem520.harperFejerMeasureScaled T) (a - x.1)) *
        (cdf (Problem520.harperFejerMeasureScaled T) (d - x.2) -
          cdf (Problem520.harperFejerMeasureScaled T) (c - x.2)) : Real) :
            Complex)) =
      ((((2 * Real.pi : Real)⁻¹ : Real) : Complex) ^ (2 : Nat)) *
        ∫ z in Icc (-T) T ×ˢ Icc (-T) T,
          harperBivariateSpatialRectangleIntegrand T a b c d x z := by
  let q : Complex := (((2 * Real.pi : Real)⁻¹ : Real) : Complex)
  let f : Real → Complex :=
    harperFejerTranslatedIntervalIntegrand T a b x.1
  let g : Real → Complex :=
    harperFejerTranslatedIntervalIntegrand T c d x.2
  have hf := cdf_harperFejerMeasureScaled_translatedInterval_eq_fourier
    hT a b x.1
  have hg := cdf_harperFejerMeasureScaled_translatedInterval_eq_fourier
    hT c d x.2
  rw [Complex.ofReal_mul, hf, hg]
  change (q * ∫ v in Icc (-T) T, f v) *
      (q * ∫ w in Icc (-T) T, g w) = _
  calc
    _ = q ^ (2 : Nat) *
        ((∫ v in Icc (-T) T, f v) * ∫ w in Icc (-T) T, g w) := by
      ring
    _ = q ^ (2 : Nat) *
        ∫ z in Icc (-T) T ×ˢ Icc (-T) T,
          f z.1 * g z.2 := by
      congr 1
      simpa only [Measure.volume_eq_prod] using
        (setIntegral_prod_mul (μ := volume) (ν := volume)
          f g (Icc (-T) T) (Icc (-T) T)).symm
    _ = q ^ (2 : Nat) *
        ∫ z in Icc (-T) T ×ˢ Icc (-T) T,
          harperBivariateSpatialRectangleIntegrand T a b c d x z := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      unfold f g harperFejerTranslatedIntervalIntegrand
        harperBivariateSpatialRectangleIntegrand
      have hexp :
          Complex.exp (((z.1 * x.1 : Real) : Complex) * Complex.I) *
              Complex.exp (((z.2 * x.2 : Real) : Complex) * Complex.I) =
            Complex.exp
              ((((z.1 * x.1 + z.2 * x.2 : Real) : Complex) *
                Complex.I)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [show
          Complex.exp (((z.1 * x.1 : Real) : Complex) * Complex.I) *
                harperFejerIntervalMultiplier T a b z.1 *
              (Complex.exp (((z.2 * x.2 : Real) : Complex) * Complex.I) *
                harperFejerIntervalMultiplier T c d z.2) =
            (Complex.exp (((z.1 * x.1 : Real) : Complex) * Complex.I) *
              Complex.exp (((z.2 * x.2 : Real) : Complex) * Complex.I)) *
                harperFejerIntervalMultiplier T a b z.1 *
                  harperFejerIntervalMultiplier T c d z.2 by ring,
        hexp]
    _ = _ := by rfl

theorem integral_harperBivariateSpatialRectangleIntegrand
    (mu : Measure (Real × Real))
    (T a b c d : Real) (z : Real × Real) :
    (∫ x, harperBivariateSpatialRectangleIntegrand T a b c d x z ∂mu) =
      harperBivariateCharacteristic mu z *
        harperFejerIntervalMultiplier T a b z.1 *
          harperFejerIntervalMultiplier T c d z.2 := by
  let phase : (Real × Real) → Complex := fun x ↦
    Complex.exp
      ((((z.1 * x.1 + z.2 * x.2 : Real) : Complex) * Complex.I))
  let m₁ := harperFejerIntervalMultiplier T a b z.1
  let m₂ := harperFejerIntervalMultiplier T c d z.2
  have hphase : (∫ x, phase x ∂mu) = harperBivariateCharacteristic mu z := by
    unfold harperBivariateCharacteristic
    rw [charFunDual_apply]
    apply integral_congr_ae
    filter_upwards with x
    rw [harperTwoHeightProjection_apply]
  change (∫ x, (phase x * m₁) * m₂ ∂mu) =
    harperBivariateCharacteristic mu z * m₁ * m₂
  calc
    _ = (∫ x, phase x * m₁ ∂mu) * m₂ :=
      integral_mul_const m₂ (fun x ↦ phase x * m₁)
    _ = ((∫ x, phase x ∂mu) * m₁) * m₂ :=
      congrArg (fun u : Complex ↦ u * m₂)
        (integral_mul_const m₁ phase)
    _ = _ := by rw [hphase]

/-- Absolute integrability needed for the spatial/frequency Fubini swap.
The spatial measure is a probability law and the frequency box is compact,
while both interval multipliers are uniformly bounded. -/
theorem integrable_harperBivariateSpatialRectangleIntegrand
    (mu : Measure (Real × Real)) [IsProbabilityMeasure mu]
    (T a b c d : Real) :
    Integrable (Function.uncurry
      (harperBivariateSpatialRectangleIntegrand T a b c d))
      (mu.prod (volume.restrict (Icc (-T) T ×ˢ Icc (-T) T))) := by
  let box : Set (Real × Real) := Icc (-T) T ×ˢ Icc (-T) T
  have hbox : volume box < ∞ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  letI : IsFiniteMeasure (volume.restrict box) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hbox⟩
  let M : Real := |b - a| * |d - c|
  change Integrable (Function.uncurry
      (harperBivariateSpatialRectangleIntegrand T a b c d))
    (mu.prod (volume.restrict box))
  have hconst : Integrable
      (fun _ : (Real × Real) × (Real × Real) ↦ M)
      (mu.prod (volume.restrict box)) := integrable_const M
  refine hconst.mono'
      (measurable_harperBivariateSpatialRectangleIntegrand
        T a b c d).aestronglyMeasurable ?_
  filter_upwards with q
  have hbound := norm_harperBivariateSpatialRectangleIntegrand_le
    T a b c d q.1 q.2
  simpa only [M] using hbound

/-- Exact Fourier formula for one bivariate probability law. -/
theorem harperBivariateSmoothRectangle_eq_fourier
    (mu : Measure (Real × Real)) [IsProbabilityMeasure mu]
    {T : Real} (hT : 0 < T) (a b c d : Real) :
    (((harperBivariateSmoothRectangle
      (Problem520.harperFejerMeasureScaled T) mu a b c d : Real) :
        Complex)) =
      ((((2 * Real.pi : Real)⁻¹ : Real) : Complex) ^ (2 : Nat)) *
        ∫ z in Icc (-T) T ×ˢ Icc (-T) T,
          harperBivariateCharacteristic mu z *
            harperFejerIntervalMultiplier T a b z.1 *
              harperFejerIntervalMultiplier T c d z.2 := by
  let q : Complex := (((2 * Real.pi : Real)⁻¹ : Real) : Complex)
  let box : Set (Real × Real) := Icc (-T) T ×ˢ Icc (-T) T
  let F : (Real × Real) → (Real × Real) → Complex :=
    harperBivariateSpatialRectangleIntegrand T a b c d
  have hFint : Integrable (Function.uncurry F)
      (mu.prod (volume.restrict box)) := by
    exact integrable_harperBivariateSpatialRectangleIntegrand
      mu T a b c d
  have hswap :
      (∫ x, ∫ z in box, F x z ∂volume ∂mu) =
        ∫ z in box, ∫ x, F x z ∂mu ∂volume := by
    exact integral_integral_swap hFint
  unfold harperBivariateSmoothRectangle
  rw [show
      (((∫ x,
        (cdf (Problem520.harperFejerMeasureScaled T) (b - x.1) -
          cdf (Problem520.harperFejerMeasureScaled T) (a - x.1)) *
        (cdf (Problem520.harperFejerMeasureScaled T) (d - x.2) -
          cdf (Problem520.harperFejerMeasureScaled T) (c - x.2))
          ∂mu : Real) : Complex)) =
        ∫ x,
          ((((cdf (Problem520.harperFejerMeasureScaled T) (b - x.1) -
            cdf (Problem520.harperFejerMeasureScaled T) (a - x.1)) *
          (cdf (Problem520.harperFejerMeasureScaled T) (d - x.2) -
            cdf (Problem520.harperFejerMeasureScaled T) (c - x.2)) :
              Real) : Complex)) ∂mu by
        exact (@integral_ofReal (Real × Real) _ mu Complex _
          (fun x ↦
            (cdf (Problem520.harperFejerMeasureScaled T) (b - x.1) -
              cdf (Problem520.harperFejerMeasureScaled T) (a - x.1)) *
            (cdf (Problem520.harperFejerMeasureScaled T) (d - x.2) -
              cdf (Problem520.harperFejerMeasureScaled T)
                (c - x.2)))).symm]
  calc
    _ = ∫ x, q ^ (2 : Nat) * ∫ z in box, F x z ∂volume ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      simpa only [q, box, F] using
        cdf_harperFejerMeasureScaled_translatedRectangle_eq_fourier
          hT a b c d x
    _ = q ^ (2 : Nat) *
        (∫ x, ∫ z in box, F x z ∂volume ∂mu) := by
      exact integral_const_mul (q ^ (2 : Nat))
        (fun x ↦ ∫ z in box, F x z ∂volume)
    _ = q ^ (2 : Nat) *
        (∫ z in box, ∫ x, F x z ∂mu ∂volume) := by rw [hswap]
    _ = q ^ (2 : Nat) *
        ∫ z in box,
          harperBivariateCharacteristic mu z *
            harperFejerIntervalMultiplier T a b z.1 *
              harperFejerIntervalMultiplier T c d z.2 ∂volume := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      exact integral_harperBivariateSpatialRectangleIntegrand
        mu T a b c d z
    _ = _ := by rfl

/-- Product-Fejer inversion for a difference of arbitrary bivariate
probability laws.  Bounded interval multipliers remove any need for moment
hypotheses. -/
theorem harperBivariateFejerRectangleIdentity_of_pos
    (mu nu : Measure (Real × Real))
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {T : Real} (hT : 0 < T) :
    HarperBivariateFejerRectangleIdentity mu nu T := by
  intro a b c d
  let box : Set (Real × Real) := Icc (-T) T ×ˢ Icc (-T) T
  let fmu : (Real × Real) → Complex := fun z ↦
    harperBivariateCharacteristic mu z *
      harperFejerIntervalMultiplier T a b z.1 *
        harperFejerIntervalMultiplier T c d z.2
  let fnu : (Real × Real) → Complex := fun z ↦
    harperBivariateCharacteristic nu z *
      harperFejerIntervalMultiplier T a b z.1 *
        harperFejerIntervalMultiplier T c d z.2
  have hmuSpatial := integrable_harperBivariateSpatialRectangleIntegrand
    mu T a b c d
  have hnuSpatial := integrable_harperBivariateSpatialRectangleIntegrand
    nu T a b c d
  have hmuFreq : Integrable fmu (volume.restrict box) := by
    apply hmuSpatial.integral_prod_right.congr
    exact ae_of_all _ fun z ↦
      integral_harperBivariateSpatialRectangleIntegrand
        mu T a b c d z
  have hnuFreq : Integrable fnu (volume.restrict box) := by
    apply hnuSpatial.integral_prod_right.congr
    exact ae_of_all _ fun z ↦
      integral_harperBivariateSpatialRectangleIntegrand
        nu T a b c d z
  have hmu := harperBivariateSmoothRectangle_eq_fourier
    mu hT a b c d
  have hnu := harperBivariateSmoothRectangle_eq_fourier
    nu hT a b c d
  rw [show
      (((harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T) mu a b c d -
        harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T) nu a b c d : Real) :
            Complex)) =
        ((harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T) mu a b c d : Real) :
            Complex) -
        ((harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T) nu a b c d : Real) :
            Complex) by push_cast; rfl]
  rw [hmu, hnu]
  calc
    _ = ((((2 * Real.pi : Real)⁻¹ : Real) : Complex) ^ (2 : Nat)) *
        ((∫ z in box, fmu z) - ∫ z in box, fnu z) := by
      dsimp only [box, fmu, fnu]
      ring
    _ = ((((2 * Real.pi : Real)⁻¹ : Real) : Complex) ^ (2 : Nat)) *
        ∫ z in box, fmu z - fnu z := by
      rw [integral_sub hmuFreq hnuFreq]
    _ = ((((2 * Real.pi : Real)⁻¹ : Real) : Complex) ^ (2 : Nat)) *
        ∫ z in box,
          harperBivariateFejerRectangleIntegrand
            (harperBivariateCharacteristic mu)
            (harperBivariateCharacteristic nu) T a b c d z := by
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      unfold fmu fnu harperBivariateFejerRectangleIntegrand
      ring
    _ = _ := by rfl

/-- The exact identity needed by the scheduled Rademacher/Gaussian pair. -/
theorem harperScheduledTwoHeightFejerRectangleIdentity
    (y j : Nat) (t s : Real) {T : Real} (hT : 0 < T) :
    HarperBivariateFejerRectangleIdentity
      (harperTwoHeightPrimeBlockVectorLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s)
      (harperTwoHeightGaussianLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s) T :=
  harperBivariateFejerRectangleIdentity_of_pos _ _ hT

/-- Fully unconditional scheduled two-height smoothed rectangle comparison:
the actual Rademacher law, covariance-matched Gaussian law, and exact Fejer
inversion are all instantiated. -/
theorem abs_harperScheduledTwoHeightSmoothRectangle_sub_gaussianLaw_le_unconditional
    (y j : Nat) (t s T a b c d : Real)
    (hT : 0 < T)
    (hfrequency :
      4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : Real)) :
    |harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T)
          (harperTwoHeightPrimeBlockVectorLaw y
            (Problem520.harperScheduledPrimeBlock y j) t s) a b c d -
        harperBivariateSmoothRectangle
          (Problem520.harperFejerMeasureScaled T)
          (harperTwoHeightGaussianLaw y
            (Problem520.harperScheduledPrimeBlock y j) t s) a b c d| ≤
      (2 * Real.pi)⁻¹ ^ (2 : Nat) * |b - a| * |d - c| *
        (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
          (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) := by
  exact abs_harperScheduledTwoHeightSmoothRectangle_sub_gaussianLaw_le
    y j t s T a b c d hT.le hfrequency
    (harperScheduledTwoHeightFejerRectangleIdentity y j t s hT)

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.cdf_harperFejerMeasureScaled_translatedInterval_eq_fourier
#print axioms Erdos.Problem1144.cdf_harperFejerMeasureScaled_translatedRectangle_eq_fourier
#print axioms Erdos.Problem1144.harperBivariateSmoothRectangle_eq_fourier
#print axioms Erdos.Problem1144.harperBivariateFejerRectangleIdentity_of_pos
#print axioms Erdos.Problem1144.abs_harperScheduledTwoHeightSmoothRectangle_sub_gaussianLaw_le_unconditional
