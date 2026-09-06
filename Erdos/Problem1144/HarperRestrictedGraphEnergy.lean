import Erdos.Problem1144.RestrictedEnergyHalfMoment
import Erdos.Problem520.HarperRestrictedVerticalSet

open MeasureTheory Set
open scoped ENNReal

namespace Erdos
namespace Problem1144

/-!
# Barrier-restricted vertical Harper energy

This file defines the concrete restricted energy used by Harper's lower-
moment argument.  A measurable set in `(height, sign world)` selects the
vertical points whose Euler-product path stays inside the barrier.
-/

/-- The fixed Rademacher height band.  Staying away from zero suppresses the
extra doubled-frequency terms in two-height tilted calculations. -/
def harperLowerVerticalBand : Set Real :=
  Set.Icc ((1 : Real) / 3) ((1 : Real) / 2)

theorem measurableSet_harperLowerVerticalBand :
    MeasurableSet harperLowerVerticalBand := measurableSet_Icc

/-- The normalized Euler energy retained by a measurable joint barrier
event `G`. -/
noncomputable def harperRestrictedGraphEnergy
    (y : Nat) (G : Set (Real × Problem520.Omega))
    (omega : Problem520.Omega) : Real :=
  (∫ t in harperLowerVerticalBand,
      G.indicator
        (fun w : Real × Problem520.Omega =>
          Problem520.harperEulerDensity y w.2 w.1) (t, omega)) /
    Real.log (y : Real)

theorem harperRestrictedGraphEnergy_nonneg
    {y : Nat} (hy : 1 < y) (G : Set (Real × Problem520.Omega))
    (omega : Problem520.Omega) :
    0 <= harperRestrictedGraphEnergy y G omega := by
  unfold harperRestrictedGraphEnergy
  apply div_nonneg
  · exact setIntegral_nonneg measurableSet_harperLowerVerticalBand
      fun t _ht => Set.indicator_nonneg
        (fun w _hw => Problem520.harperEulerDensity_nonneg y w.2 w.1) (t, omega)
  · exact (Real.log_pos (by exact_mod_cast hy)).le

theorem integrableOn_harperRestrictedGraphDensity
    (y : Nat) {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G) (omega : Problem520.Omega) :
    IntegrableOn
      (fun t => G.indicator
        (fun w : Real × Problem520.Omega =>
          Problem520.harperEulerDensity y w.2 w.1) (t, omega))
      harperLowerVerticalBand := by
  let fiber : Set Real := {t | (t, omega) ∈ G}
  have hfiber : MeasurableSet fiber := by
    exact hG.preimage (measurable_id.prodMk measurable_const)
  have hbase : IntegrableOn
      (fun t => Problem520.harperEulerDensity y omega t)
      harperLowerVerticalBand := by
    have hunit := Problem520.integrableOn_harperEulerDensity_unitInterval
      y true 0 omega
    apply hunit.mono_set
    intro t ht
    change (1 : Real) / 3 <= t ∧ t <= (1 : Real) / 2 at ht
    have hmem : t ∈ Set.Ico (0 : Real) 1 := by
      constructor <;> linarith
    simpa [Problem520.harperEulerUnitInterval] using hmem
  have hindicator :
      (fun t => G.indicator
          (fun w : Real × Problem520.Omega =>
            Problem520.harperEulerDensity y w.2 w.1) (t, omega)) =
        fiber.indicator
          (fun t => Problem520.harperEulerDensity y omega t) := by
    funext t
    by_cases ht : (t, omega) ∈ G
    · simp [fiber, ht]
    · simp [fiber, ht]
  rw [hindicator]
  exact hbase.indicator hfiber

/-- The restricted energy is integrable for every measurable joint barrier
event. -/
theorem integrable_harperRestrictedGraphEnergy
    {y : Nat} {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G) :
    Integrable (harperRestrictedGraphEnergy y G) Problem520.μ := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let F : Real × Problem520.Omega -> Real := fun w =>
    G.indicator
      (fun z : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y z.2 z.1) w
  have hfinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  have hbase : Integrable
      (fun w : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y w.2 w.1)
      ((volume.restrict harperLowerVerticalBand).prod Problem520.μ) :=
    Problem520.integrable_harperEulerDensity_prod_restrict y
      measurableSet_harperLowerVerticalBand hfinite
  have hF : Integrable F (nu.prod Problem520.μ) := by
    simpa only [nu, F] using hbase.indicator hG
  have hinner : Integrable
      (fun omega => ∫ t, F (t, omega) ∂nu) Problem520.μ :=
    hF.integral_prod_right
  simpa only [harperRestrictedGraphEnergy, nu, F] using
    hinner.div_const (Real.log (y : Real))

theorem harperRestrictedGraphEnergy_le_uniformBound
    {y : Nat} (hy : 1 < y) {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G) (omega : Problem520.Omega) :
    harperRestrictedGraphEnergy y G omega <=
      Problem520.harperEulerDensityUniformBound y / Real.log (y : Real) := by
  let restricted : Real -> Real := fun t =>
    G.indicator
      (fun w : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y w.2 w.1) (t, omega)
  let U : Real := Problem520.harperEulerDensityUniformBound y
  have hrestricted : IntegrableOn restricted harperLowerVerticalBand := by
    simpa only [restricted] using
      integrableOn_harperRestrictedGraphDensity y hG omega
  have hfinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  have hconst : IntegrableOn (fun _t : Real => U) harperLowerVerticalBand :=
    integrableOn_const hfinite
  have hpoint (t : Real) (_ht : t ∈ harperLowerVerticalBand) :
      restricted t <= U := by
    by_cases hmem : (t, omega) ∈ G
    · simpa only [restricted, Set.indicator_of_mem hmem, U] using
        Problem520.harperEulerDensity_le_uniformBound y omega t
    · simp [restricted, hmem, U,
        Problem520.harperEulerDensityUniformBound_nonneg]
  have hint :
      (∫ t in harperLowerVerticalBand, restricted t) <=
        ∫ _t in harperLowerVerticalBand, U :=
    setIntegral_mono_on hrestricted hconst
      measurableSet_harperLowerVerticalBand hpoint
  have hvolume : volume.real harperLowerVerticalBand <= 1 := by
    norm_num [harperLowerVerticalBand, Measure.real, Real.volume_Icc]
  have hU : 0 <= U :=
    Problem520.harperEulerDensityUniformBound_nonneg y
  have hnum : (∫ t in harperLowerVerticalBand, restricted t) <= U := by
    calc
      (∫ t in harperLowerVerticalBand, restricted t) <=
          ∫ _t in harperLowerVerticalBand, U := hint
      _ = volume.real harperLowerVerticalBand * U := by simp
      _ <= 1 * U := mul_le_mul_of_nonneg_right hvolume hU
      _ = U := one_mul U
  have hlog : 0 <= Real.log (y : Real) :=
    (Real.log_pos (by exact_mod_cast hy)).le
  unfold harperRestrictedGraphEnergy
  change (∫ t in harperLowerVerticalBand, restricted t) /
      Real.log (y : Real) <= U / Real.log (y : Real)
  exact div_le_div_of_nonneg_right hnum hlog

/-- At every finite prime cutoff the restricted energy has an integrable
square.  This is a soft boundedness fact, not part of the deep second-moment
estimate. -/
theorem integrable_sq_harperRestrictedGraphEnergy
    {y : Nat} (hy : 1 < y) {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G) :
    Integrable (fun omega =>
      harperRestrictedGraphEnergy y G omega ^ (2 : Nat)) Problem520.μ := by
  let C : Real :=
    Problem520.harperEulerDensityUniformBound y / Real.log (y : Real)
  have hRint := integrable_harperRestrictedGraphEnergy (y := y) hG
  apply Integrable.of_bound (hRint.aestronglyMeasurable.pow 2) (C ^ 2)
  exact ae_of_all Problem520.μ fun omega => by
    have hnonneg := harperRestrictedGraphEnergy_nonneg hy G omega
    have hle : harperRestrictedGraphEnergy y G omega <= C := by
      simpa only [C] using
        harperRestrictedGraphEnergy_le_uniformBound hy hG omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hnonneg hle 2

theorem harperRestrictedGraphEnergy_le_initial
    {y : Nat} (hy : 1 < y) {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G) (omega : Problem520.Omega) :
    harperRestrictedGraphEnergy y G omega <=
      Problem520.harperInitialNormalizedEnergy y omega := by
  have hlog : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast hy)
  let density : Real -> Real := fun t =>
    Problem520.harperEulerDensity y omega t
  let weighted : Real -> Real := fun t =>
    density t / ((1 / 4 : Real) + t ^ 2)
  let restricted : Real -> Real := fun t =>
    G.indicator
      (fun w : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y w.2 w.1) (t, omega)
  have hrestricted : IntegrableOn restricted harperLowerVerticalBand := by
    simpa only [restricted] using
      integrableOn_harperRestrictedGraphDensity y hG omega
  have hweighted : Integrable weighted := by
    simpa only [weighted, density] using
      Problem520.integrable_harperEulerDensity_div_cauchyKernel y omega
  have hpoint (t : Real) (ht : t ∈ harperLowerVerticalBand) :
      restricted t <= weighted t := by
    have htBounds : (1 : Real) / 3 <= t ∧ t <= (1 : Real) / 2 := ht
    have ht0 : 0 <= t := by linarith
    have hden : 0 < (1 / 4 : Real) + t ^ 2 := by positivity
    have hdenOne : (1 / 4 : Real) + t ^ 2 <= 1 := by
      nlinarith [sq_nonneg t]
    have hdensity : 0 <= density t :=
      Problem520.harperEulerDensity_nonneg y omega t
    have hleWeighted : density t <= weighted t := by
      dsimp only [weighted]
      exact (le_div_iff₀ hden).2 (by nlinarith)
    have hrestrictedDensity : restricted t <= density t := by
      by_cases hmem : (t, omega) ∈ G
      · simp [restricted, density, hmem]
      · simp [restricted, hmem, hdensity]
    exact hrestrictedDensity.trans hleWeighted
  have hband :
      (∫ t in harperLowerVerticalBand, restricted t) <=
        ∫ t in harperLowerVerticalBand, weighted t := by
    exact setIntegral_mono_on hrestricted hweighted.integrableOn
      measurableSet_harperLowerVerticalBand hpoint
  have hfull :
      (∫ t in harperLowerVerticalBand, weighted t) <= ∫ t, weighted t := by
    exact setIntegral_le_integral hweighted
      (ae_of_all _ fun t => div_nonneg
        (Problem520.harperEulerDensity_nonneg y omega t) (by positivity))
  rw [Problem520.harperInitialNormalizedEnergy_eq_verticalIntegral]
  norm_num [show ((1 / 2 : Real) ^ 2) = 1 / 4 by norm_num]
  unfold harperRestrictedGraphEnergy
  change (∫ t in harperLowerVerticalBand, restricted t) /
      Real.log (y : Real) <= (∫ t, weighted t) / Real.log (y : Real)
  exact div_le_div_of_nonneg_right (hband.trans hfull) hlog.le

/-! ## Exact one-height tilted first moment -/

/-- Fubini and the exact tilted change of measure identify the first moment
of the graph-restricted energy with the vertical average of the one-height
tilted barrier probabilities. -/
theorem integral_harperRestrictedGraphEnergy_eq_tiltedProbabilities
    {y : Nat} {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G)
    (A : Real -> Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t) :
    (∫ omega, harperRestrictedGraphEnergy y G omega ∂Problem520.μ) =
      (Problem520.primeEnergyNormalizer y / Real.log (y : Real)) *
        ∫ t in harperLowerVerticalBand,
          (Problem520.harperTiltedCubeLaw y t).real (A t) := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let F : Real × Problem520.Omega -> Real := fun w =>
    G.indicator
      (fun z : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y z.2 z.1) w
  have hfinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  have hbase : Integrable
      (fun w : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y w.2 w.1)
      ((volume.restrict harperLowerVerticalBand).prod Problem520.μ) :=
    Problem520.integrable_harperEulerDensity_prod_restrict y
      measurableSet_harperLowerVerticalBand hfinite
  have hF : Integrable F (nu.prod Problem520.μ) := by
    simpa only [nu, F] using hbase.indicator hG
  have hswap :
      (∫ omega, ∫ t, F (t, omega) ∂nu ∂Problem520.μ) =
        ∫ t, ∫ omega, F (t, omega) ∂Problem520.μ ∂nu :=
    (integral_prod_symm F hF).symm.trans (integral_prod F hF)
  have hinner (t : Real) :
      (∫ omega, F (t, omega) ∂Problem520.μ) =
        Problem520.primeEnergyNormalizer y *
          (Problem520.harperTiltedCubeLaw y t).real (A t) := by
    let P : Set Problem520.Omega :=
      Problem520.harperPrimeRestriction y ⁻¹' A t
    have hA : MeasurableSet (A t) := Set.toFinite (A t) |>.measurableSet
    have hP : MeasurableSet P :=
      hA.preimage (Problem520.measurable_harperPrimeRestriction y)
    have hfun : (fun omega => F (t, omega)) =
        P.indicator (fun omega =>
          Problem520.harperEulerDensity y omega t) := by
      funext omega
      by_cases hmem : omega ∈ P
      · have hGmem : (t, omega) ∈ G := (hsection t omega).2 hmem
        simp [F, P, hmem, hGmem]
      · have hGnot : (t, omega) ∉ G := by
          intro hmemG
          exact hmem ((hsection t omega).1 hmemG)
        simp [F, P, hmem, hGnot]
    rw [hfun, integral_indicator hP]
    have hdensity :
        (fun omega => Problem520.harperEulerDensity y omega t) =
          fun omega => Problem520.primeEnergyNormalizer y *
            Problem520.normalizedHarperEulerDensity y omega t := by
      funext omega
      unfold Problem520.normalizedHarperEulerDensity
      field_simp [(Problem520.primeEnergyNormalizer_pos y).ne']
    rw [hdensity, integral_const_mul]
    rw [Problem520.harperTiltedCubeLaw_real_apply_eq_omega]
  have houter :
      (∫ t, ∫ omega, F (t, omega) ∂Problem520.μ ∂nu) =
        Problem520.primeEnergyNormalizer y *
          ∫ t in harperLowerVerticalBand,
            (Problem520.harperTiltedCubeLaw y t).real (A t) := by
    rw [show (fun t => ∫ omega, F (t, omega) ∂Problem520.μ) =
        fun t => Problem520.primeEnergyNormalizer y *
          (Problem520.harperTiltedCubeLaw y t).real (A t) by
      funext t
      exact hinner t]
    rw [integral_const_mul]
  have hraw :
      (∫ omega, ∫ t, F (t, omega) ∂nu ∂Problem520.μ) =
        Problem520.primeEnergyNormalizer y *
          ∫ t in harperLowerVerticalBand,
            (Problem520.harperTiltedCubeLaw y t).real (A t) :=
    hswap.trans houter
  unfold harperRestrictedGraphEnergy
  rw [integral_div]
  change (∫ omega, ∫ t, F (t, omega) ∂nu ∂Problem520.μ) /
      Real.log (y : Real) = _
  rw [hraw]
  ring

/-- The varying one-height tilted probabilities are integrable whenever they
come from measurable sections of a measurable joint barrier. -/
theorem integrableOn_harperTiltedCubeLaw_real_of_graph
    {y : Nat} {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G)
    (A : Real -> Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t) :
    IntegrableOn
      (fun t => (Problem520.harperTiltedCubeLaw y t).real (A t))
      harperLowerVerticalBand := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let F : Real × Problem520.Omega -> Real := fun w =>
    G.indicator
      (fun z : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y z.2 z.1) w
  have hfinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  have hbase : Integrable
      (fun w : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y w.2 w.1)
      ((volume.restrict harperLowerVerticalBand).prod Problem520.μ) :=
    Problem520.integrable_harperEulerDensity_prod_restrict y
      measurableSet_harperLowerVerticalBand hfinite
  have hF : Integrable F (nu.prod Problem520.μ) := by
    simpa only [nu, F] using hbase.indicator hG
  have hinner (t : Real) :
      (∫ omega, F (t, omega) ∂Problem520.μ) =
        Problem520.primeEnergyNormalizer y *
          (Problem520.harperTiltedCubeLaw y t).real (A t) := by
    let P : Set Problem520.Omega :=
      Problem520.harperPrimeRestriction y ⁻¹' A t
    have hA : MeasurableSet (A t) := Set.toFinite (A t) |>.measurableSet
    have hP : MeasurableSet P :=
      hA.preimage (Problem520.measurable_harperPrimeRestriction y)
    have hfun : (fun omega => F (t, omega)) =
        P.indicator (fun omega =>
          Problem520.harperEulerDensity y omega t) := by
      funext omega
      by_cases hmem : omega ∈ P
      · have hGmem : (t, omega) ∈ G := (hsection t omega).2 hmem
        simp [F, P, hmem, hGmem]
      · have hGnot : (t, omega) ∉ G := by
          intro hmemG
          exact hmem ((hsection t omega).1 hmemG)
        simp [F, P, hmem, hGnot]
    rw [hfun, integral_indicator hP]
    have hdensity :
        (fun omega => Problem520.harperEulerDensity y omega t) =
          fun omega => Problem520.primeEnergyNormalizer y *
            Problem520.normalizedHarperEulerDensity y omega t := by
      funext omega
      unfold Problem520.normalizedHarperEulerDensity
      field_simp [(Problem520.primeEnergyNormalizer_pos y).ne']
    rw [hdensity, integral_const_mul]
    rw [Problem520.harperTiltedCubeLaw_real_apply_eq_omega]
  have hmul : Integrable
      (fun t => Problem520.primeEnergyNormalizer y *
        (Problem520.harperTiltedCubeLaw y t).real (A t)) nu := by
    rw [← show (fun t => ∫ omega, F (t, omega) ∂Problem520.μ) =
        (fun t => Problem520.primeEnergyNormalizer y *
          (Problem520.harperTiltedCubeLaw y t).real (A t)) by
      funext t
      exact hinner t]
    exact hF.integral_prod_left
  have hdiv := hmul.div_const (Problem520.primeEnergyNormalizer y)
  simpa only [nu, mul_div_cancel_left₀ _
    (Problem520.primeEnergyNormalizer_pos y).ne'] using hdiv

/-- A uniform one-height tilted ballot lower bound on the fixed vertical band
already gives the required first moment, with the explicit harmless factor
`1 / 12`.  The factor is `1 / 2` from the elementary Mertens lower bound and
`1 / 6` from the length of the band. -/
theorem integral_harperRestrictedGraphEnergy_lower_of_tiltedProbabilities
    {y : Nat} (hy : 2 ≤ y) {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G)
    (A : Real -> Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t)
    {delta K : Real} (hdelta : 0 ≤ delta) (hK : 0 ≤ K)
    (hprob : ∀ t ∈ harperLowerVerticalBand,
      delta * K ≤ (Problem520.harperTiltedCubeLaw y t).real (A t)) :
    (delta / 12) * K ≤
      ∫ omega, harperRestrictedGraphEnergy y G omega ∂Problem520.μ := by
  have hlog : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hratio : (1 / 2 : Real) ≤
      Problem520.primeEnergyNormalizer y / Real.log (y : Real) := by
    exact (le_div_iff₀ hlog).2
      (Problem520.half_mul_log_le_primeEnergyNormalizer hy)
  have hprobInt := integrableOn_harperTiltedCubeLaw_real_of_graph
    hG A hsection
  have hconstInt : IntegrableOn (fun _t : Real => delta * K)
      harperLowerVerticalBand := by
    exact integrableOn_const (by
      simp [harperLowerVerticalBand, Real.volume_Icc])
  have hintegral : (delta * K) / 6 ≤
      ∫ t in harperLowerVerticalBand,
        (Problem520.harperTiltedCubeLaw y t).real (A t) := by
    have hmono := setIntegral_mono_on hconstInt hprobInt
      measurableSet_harperLowerVerticalBand hprob
    calc
      (delta * K) / 6 =
          ∫ _t in harperLowerVerticalBand, delta * K := by
        norm_num [harperLowerVerticalBand, Real.volume_Icc] <;> ring
      _ ≤ _ := hmono
  rw [integral_harperRestrictedGraphEnergy_eq_tiltedProbabilities
    hG A hsection]
  have hnonneg : 0 ≤ (delta * K) / 6 := by positivity
  calc
    (delta / 12) * K = (1 / 2 : Real) * ((delta * K) / 6) := by ring
    _ ≤ (Problem520.primeEnergyNormalizer y / Real.log (y : Real)) *
          ((delta * K) / 6) :=
      mul_le_mul_of_nonneg_right hratio hnonneg
    _ ≤ (Problem520.primeEnergyNormalizer y / Real.log (y : Real)) *
          ∫ t in harperLowerVerticalBand,
            (Problem520.harperTiltedCubeLaw y t).real (A t) :=
      mul_le_mul_of_nonneg_left hintegral (by positivity)

/-! ## Concrete certificate handoff -/

/-- The sharp remaining analytic input in tilted-probability form.  It asks
for one measurable barrier graph whose one-height sections have probability
at least a constant times the critical scale, and whose retained energy has
the matching second moment. -/
def HarperRestrictedGraphBallotSecondStatement : Prop :=
  ∃ delta C : Real, 0 < delta ∧ 0 < C ∧ ∃ Y : Nat, ∀ y : Nat,
    Y <= y -> 4 <= y ->
      ∃ G : Set (Real × Problem520.Omega),
        ∃ A : Real -> Set (Problem520.HarperPrimeCube y),
          MeasurableSet G ∧
          (∀ t omega,
            (t, omega) ∈ G ↔
              Problem520.harperPrimeRestriction y omega ∈ A t) ∧
          (∀ t ∈ harperLowerVerticalBand,
            delta * harperInitialCriticalScale y <=
              (Problem520.harperTiltedCubeLaw y t).real (A t)) ∧
          (∫ omega,
              harperRestrictedGraphEnergy y G omega ^ (2 : Nat)
                ∂Problem520.μ) <=
            (C * harperInitialCriticalScale y) ^ (2 : Nat)

/-- The remaining analytic theorem, now specialized to an actual measurable
barrier-restricted vertical Euler energy. -/
def HarperRestrictedGraphFirstSecondStatement : Prop :=
  ∃ c C : Real, 0 < c ∧ 0 < C ∧ ∃ Y : Nat, ∀ y : Nat,
    Y <= y -> 4 <= y ->
      ∃ G : Set (Real × Problem520.Omega), MeasurableSet G ∧
        c * harperInitialCriticalScale y <=
          ∫ omega, harperRestrictedGraphEnergy y G omega ∂Problem520.μ ∧
        (∫ omega,
            harperRestrictedGraphEnergy y G omega ^ (2 : Nat)
              ∂Problem520.μ) <=
          (C * harperInitialCriticalScale y) ^ (2 : Nat)

/-- The tilted one-height ballot estimate plus the two-height second-moment
estimate imply the concrete first/second-moment certificate. -/
theorem harperRestrictedGraphFirstSecondStatement_of_ballotSecond
    (hballot : HarperRestrictedGraphBallotSecondStatement) :
    HarperRestrictedGraphFirstSecondStatement := by
  obtain ⟨delta, C, hdelta, hC, Y, hcert⟩ := hballot
  refine ⟨delta / 12, C, by positivity, hC, Y, ?_⟩
  intro y hyY hy4
  obtain ⟨G, A, hG, hsection, hprob, hsecond⟩ := hcert y hyY hy4
  refine ⟨G, hG, ?_, hsecond⟩
  exact integral_harperRestrictedGraphEnergy_lower_of_tiltedProbabilities
    (by omega) hG A hsection hdelta.le
      (harperInitialCriticalScale_pos hy4).le hprob

/-- All soft properties of the restricted energy—positivity, domination by
the full energy, and first/square integrability—are automatic.  Therefore
only the two displayed moment estimates remain analytic. -/
theorem harperRestrictedEnergyFirstSecondStatement_of_graph
    (hgraph : HarperRestrictedGraphFirstSecondStatement) :
    HarperRestrictedEnergyFirstSecondStatement := by
  obtain ⟨c, C, hc, hC, Y, hcert⟩ := hgraph
  refine ⟨c, C, hc, hC, Y, ?_⟩
  intro y hyY hy4
  obtain ⟨G, hG, hfirst, hsecond⟩ := hcert y hyY hy4
  let R : Problem520.Omega -> Real := harperRestrictedGraphEnergy y G
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact harperRestrictedGraphEnergy_nonneg (by omega) G
  · exact harperRestrictedGraphEnergy_le_initial (by omega) hG
  · exact integrable_harperRestrictedGraphEnergy (y := y) hG
  · exact integrable_sq_harperRestrictedGraphEnergy (by omega) hG
  · simpa only [R] using hfirst
  · simpa only [R] using hsecond

/-- Final direct handoff from the concrete graph first/second-moment theorem
to the lower half moment used by positive probability. -/
theorem harperRademacherInitialHalfMomentLowerStatement_of_restrictedGraph
    (hgraph : HarperRestrictedGraphFirstSecondStatement) :
    HarperRademacherInitialHalfMomentLowerStatement :=
  harperRademacherInitialHalfMomentLowerStatement_of_restrictedEnergy
    (harperRestrictedEnergyFirstSecondStatement_of_graph hgraph)

/-- End-to-end handoff from the one-height ballot and two-height moment input
to the sole new lower fractional moment. -/
theorem harperRademacherInitialHalfMomentLowerStatement_of_ballotSecond
    (hballot : HarperRestrictedGraphBallotSecondStatement) :
    HarperRademacherInitialHalfMomentLowerStatement :=
  harperRademacherInitialHalfMomentLowerStatement_of_restrictedGraph
    (harperRestrictedGraphFirstSecondStatement_of_ballotSecond hballot)

end Problem1144
end Erdos
