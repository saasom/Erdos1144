import Erdos.Problem1144.HarperLogBallotCertificate
import Erdos.Problem520.LargestPrimeDecomposition

open MeasureTheory Set

namespace Erdos
namespace Problem1144

/-!
# Squarefree Harper energy on the actual fresh-coefficient range

For the exact split `X = y^3`, a fresh coefficient at an endpoint below
`X*y` only uses partial sums below `y`.  This file defines that true prefix
energy and records its deterministic relation to the already formalized full
Harper smooth energy.
-/

/-- Every positive integer at most `N` is `y`-smooth when `N ≤ y`, so the
smooth squarefree sum is the ordinary squarefree partial sum throughout the
coefficient range. -/
theorem squarefreePartialSum_eq_Ψ_of_le
    (omega : Problem520.Omega) {N y : ℕ} (hNy : N ≤ y) :
    Problem520.partialSum omega N = Problem520.Ψ omega N y := by
  classical
  have hsmooth : Nat.smoothNumbersUpTo N (y + 1) =
      (Finset.range N).image Nat.succ := by
    ext n
    rw [Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨hnN, hsmooth⟩
      have hn0 : 0 < n := Nat.pos_of_ne_zero
        (Nat.ne_zero_of_mem_smoothNumbers hsmooth)
      rw [Finset.mem_image]
      exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro hn
      rw [Finset.mem_image] at hn
      rcases hn with ⟨k, hk, rfl⟩
      have hklt : k < N := Finset.mem_range.mp hk
      exact ⟨by omega,
        Nat.mem_smoothNumbers_of_lt (Nat.succ_pos k) (by omega)⟩
  unfold Problem520.partialSum Problem520.Ψ
  rw [hsmooth, Finset.sum_image]
  exact Nat.succ_injective.injOn

/-- The real-cutoff squarefree smooth sum is the ordinary partial sum at
every nonnegative point below the smoothness cutoff. -/
theorem ΨReal_eq_squarefreePartialSum_of_le
    (omega : Problem520.Omega) {z : ℝ} {y : ℕ}
    (hzy : z ≤ (y : ℝ)) :
    Problem520.ΨReal omega z y =
      Problem520.partialSum omega ⌊z⌋₊ := by
  have hfloor : ⌊z⌋₊ ≤ y := Nat.floor_le_of_le hzy
  unfold Problem520.ΨReal
  exact (squarefreePartialSum_eq_Ψ_of_le omega hfloor).symm

/-- The inverse-square energy on exactly the coefficient range `[1,y]`.
The half-open convention is immaterial for integration and matches the
existing step-function interfaces. -/
noncomputable def harperSquarefreeCoefficientPrefixEnergy
    (y : ℕ) (omega : Problem520.Omega) : ℝ :=
  ∫ z in Set.Ioc (1 : ℝ) (y : ℝ),
    |Problem520.ΨReal omega z y| ^ 2 / z ^ 2

theorem integrableOn_harperSquarefreeCoefficientPrefixEnergy
    (y : ℕ) (omega : Problem520.Omega) :
    IntegrableOn
      (fun z : ℝ ↦ |Problem520.ΨReal omega z y| ^ 2 / z ^ 2)
      (Set.Ioc (1 : ℝ) (y : ℝ)) := by
  exact (Problem520.integrableOn_smoothEnergy_integrand omega y).mono_set
    (by
      intro z hz
      exact (show (0 : ℝ) < z by linarith [hz.1]))

theorem harperSquarefreeCoefficientPrefixEnergy_nonneg
    (y : ℕ) (omega : Problem520.Omega) :
    0 ≤ harperSquarefreeCoefficientPrefixEnergy y omega := by
  unfold harperSquarefreeCoefficientPrefixEnergy
  exact integral_nonneg fun z ↦ div_nonneg (sq_nonneg _) (sq_nonneg _)

set_option maxHeartbeats 800000 in
-- Joint-measurability elaboration expands the infinite product sample space.
theorem measurable_harperSquarefreeCoefficientPrefixEnergy (y : ℕ) :
    Measurable fun omega : Problem520.Omega ↦
      harperSquarefreeCoefficientPrefixEnergy y omega := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (1 : ℝ) (y : ℝ))
  let F : Problem520.Omega × ℝ → ℝ := fun w ↦
    |Problem520.ΨReal w.1 w.2 y| ^ 2 / w.2 ^ 2
  have hswap : Measurable fun w : Problem520.Omega × ℝ ↦ (w.2, w.1) :=
    measurable_snd.prodMk measurable_fst
  have hΨ : Measurable fun w : Problem520.Omega × ℝ ↦
      Problem520.ΨReal w.1 w.2 y :=
    (Problem520.measurable_ΨReal_joint y).comp hswap
  have hF : Measurable F := by
    exact ((continuous_abs.measurable.comp hΨ).pow_const 2).div
      (measurable_snd.pow_const 2)
  have hinner : Measurable fun omega : Problem520.Omega ↦
      ∫ z, F (omega, z) ∂ν :=
    hF.stronglyMeasurable.integral_prod_right.measurable
  simpa only [harperSquarefreeCoefficientPrefixEnergy, ν, F] using hinner

/-- The weighted absolute partial-sum mass whose lower first moment suffices
for the coefficient-scale energy theorem. -/
noncomputable def harperSquarefreeCoefficientWeightedL1
    (y : ℕ) (omega : Problem520.Omega) : ℝ :=
  ∫ z in Set.Ioc (1 : ℝ) (y : ℝ),
    |Problem520.ΨReal omega z y| / z * (1 / Real.sqrt z)

theorem harperSquarefreeCoefficientWeightedL1_nonneg
    (y : ℕ) (omega : Problem520.Omega) :
    0 ≤ harperSquarefreeCoefficientWeightedL1 y omega := by
  unfold harperSquarefreeCoefficientWeightedL1
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  exact mul_nonneg (div_nonneg (abs_nonneg _) (by linarith [hz.1]))
    (div_nonneg (by norm_num) (Real.sqrt_nonneg _))

set_option maxHeartbeats 800000 in
-- Joint-measurability elaboration expands the infinite product sample space.
theorem measurable_harperSquarefreeCoefficientWeightedL1 (y : ℕ) :
    Measurable fun omega : Problem520.Omega ↦
      harperSquarefreeCoefficientWeightedL1 y omega := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (1 : ℝ) (y : ℝ))
  let F : Problem520.Omega × ℝ → ℝ := fun w ↦
    |Problem520.ΨReal w.1 w.2 y| / w.2 * (1 / Real.sqrt w.2)
  have hswap : Measurable fun w : Problem520.Omega × ℝ ↦ (w.2, w.1) :=
    measurable_snd.prodMk measurable_fst
  have hΨ : Measurable fun w : Problem520.Omega × ℝ ↦
      Problem520.ΨReal w.1 w.2 y :=
    (Problem520.measurable_ΨReal_joint y).comp hswap
  have hF : Measurable F := by
    exact (hΨ.abs.div measurable_snd).mul
      (measurable_const.div
        (Real.continuous_sqrt.measurable.comp measurable_snd))
  have hinner : Measurable fun omega : Problem520.Omega ↦
      ∫ z, F (omega, z) ∂ν :=
    hF.stronglyMeasurable.integral_prod_right.measurable
  simpa only [harperSquarefreeCoefficientWeightedL1, ν, F] using hinner

/-- Cauchy--Schwarz on the exact coefficient range.  This is the deterministic
bridge from the localized energy problem to a weighted first absolute moment
of the ordinary squarefree partial sums. -/
theorem coefficientWeightedL1_le_sqrt_prefixEnergy_mul_sqrt_log
    (y : ℕ) (omega : Problem520.Omega) (hy : 1 < y) :
    harperSquarefreeCoefficientWeightedL1 y omega ≤
      Real.sqrt (harperSquarefreeCoefficientPrefixEnergy y omega) *
        Real.sqrt (Real.log (y : ℝ)) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (1 : ℝ) (y : ℝ))
  let f : ℝ → ℝ := fun z ↦ |Problem520.ΨReal omega z y| / z
  let g : ℝ → ℝ := fun z ↦ 1 / Real.sqrt z
  have hfmeas : AEStronglyMeasurable f ν := by
    have hfm : Measurable f :=
      (Problem520.measurable_ΨReal_cutoff omega y).abs.div measurable_id
    exact hfm.aestronglyMeasurable
  have hfSq : Integrable (fun z ↦ f z ^ 2) ν := by
    simpa only [f, div_pow] using
      integrableOn_harperSquarefreeCoefficientPrefixEnergy y omega
  have hfLp : MemLp f 2 ν :=
    (memLp_two_iff_integrable_sq hfmeas).2 hfSq
  have hgmeas : AEStronglyMeasurable g ν := by
    exact (measurable_const.div
      (Real.continuous_sqrt.measurable.comp measurable_id)).aestronglyMeasurable
  have hinv : IntegrableOn (fun z : ℝ ↦ z⁻¹) (Set.Ioc (1 : ℝ) (y : ℝ)) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le
      (by exact_mod_cast hy.le)]
    exact intervalIntegral.intervalIntegrable_inv
      (fun z hz ↦ by
        rw [uIcc_of_le (by exact_mod_cast hy.le)] at hz
        linarith [hz.1]) continuous_id.continuousOn
  have hgSq : Integrable (fun z ↦ g z ^ 2) ν := by
    apply hinv.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    have hz0 : 0 ≤ z := by linarith [hz.1]
    simp only [g, one_div, inv_pow]
    rw [Real.sq_sqrt hz0]
  have hgLp : MemLp g 2 ν :=
    (memLp_two_iff_integrable_sq hgmeas).2 hgSq
  have hfLp' : MemLp f (ENNReal.ofReal (2 : ℝ)) ν := by simpa using hfLp
  have hgLp' : MemLp g (ENNReal.ofReal (2 : ℝ)) ν := by simpa using hgLp
  have hfnonneg : 0 ≤ᵐ[ν] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    exact div_nonneg (abs_nonneg _) (by linarith [hz.1])
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (f := f) (g := g) (μ := ν)
    hfnonneg
    (Filter.Eventually.of_forall fun z ↦ div_nonneg (by norm_num)
      (Real.sqrt_nonneg _))
    hfLp' hgLp'
  have hfIntegral :
      (∫ z, f z ^ (2 : ℝ) ∂ν) =
        harperSquarefreeCoefficientPrefixEnergy y omega := by
    simp only [Real.rpow_two]
    change (∫ z in Set.Ioc (1 : ℝ) (y : ℝ),
      (|Problem520.ΨReal omega z y| / z) ^ 2) = _
    simp only [div_pow]
    rfl
  have hgIntegral : (∫ z, g z ^ (2 : ℝ) ∂ν) = Real.log (y : ℝ) := by
    simp only [Real.rpow_two]
    change (∫ z in Set.Ioc (1 : ℝ) (y : ℝ), (1 / Real.sqrt z) ^ 2) = _
    calc
      (∫ z in Set.Ioc (1 : ℝ) (y : ℝ), (1 / Real.sqrt z) ^ 2) =
          ∫ z in Set.Ioc (1 : ℝ) (y : ℝ), z⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro z hz
        have hz0 : 0 ≤ z := by linarith [hz.1]
        simp only [one_div, inv_pow]
        rw [Real.sq_sqrt hz0]
      _ = ∫ z in (1 : ℝ)..(y : ℝ), z⁻¹ := by
        rw [intervalIntegral.integral_of_le (by exact_mod_cast hy.le)]
      _ = Real.log (y : ℝ) := by
        rw [integral_inv_of_pos (by norm_num)
          (by exact_mod_cast Nat.zero_lt_of_lt hy)]
        simp
  rw [hfIntegral, hgIntegral] at hholder
  norm_num [Real.sqrt_eq_rpow, harperSquarefreeCoefficientWeightedL1,
    ν, f, g] at hholder ⊢
  exact hholder

/-- The coefficient-range energy is a literal nonnegative sub-integral of
the full Harper smooth energy. -/
theorem harperSquarefreeCoefficientPrefixEnergy_le_smoothEnergy
    (y : ℕ) (omega : Problem520.Omega) :
    harperSquarefreeCoefficientPrefixEnergy y omega ≤
      Problem520.smoothEnergy omega y := by
  unfold harperSquarefreeCoefficientPrefixEnergy Problem520.smoothEnergy
  apply setIntegral_mono_set
    (Problem520.integrableOn_smoothEnergy_integrand omega y)
  · exact Filter.Eventually.of_forall fun z ↦
      div_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact Filter.Eventually.of_forall fun z hz ↦ by
      exact (show (0 : ℝ) < z by linarith [hz.1])

/-- Endpoint form: on the coefficient range, the new energy is exactly the
inverse-square energy of the ordinary squarefree partial-sum step function. -/
theorem harperSquarefreeCoefficientPrefixEnergy_eq_partialSum
    (y : ℕ) (omega : Problem520.Omega) :
    harperSquarefreeCoefficientPrefixEnergy y omega =
      ∫ z in Set.Ioc (1 : ℝ) (y : ℝ),
        |Problem520.partialSum omega ⌊z⌋₊| ^ 2 / z ^ 2 := by
  unfold harperSquarefreeCoefficientPrefixEnergy
  apply setIntegral_congr_fun measurableSet_Ioc
  intro z hz
  change |Problem520.ΨReal omega z y| ^ 2 / z ^ 2 =
    |Problem520.partialSum omega ⌊z⌋₊| ^ 2 / z ^ 2
  rw [ΨReal_eq_squarefreePartialSum_of_le omega hz.2]

/-- Critical normalization used by the existing half-moment/two-thirds-
moment positive-probability lemma. -/
noncomputable def harperSquarefreeCoefficientNormalizedEnergy
    (y : ℕ) (omega : Problem520.Omega) : ℝ :=
  (2 * Real.pi) * harperSquarefreeCoefficientPrefixEnergy y omega /
    Real.log (y : ℝ)

theorem harperSquarefreeCoefficientNormalizedEnergy_nonneg
    {y : ℕ} (hy : 1 < y) (omega : Problem520.Omega) :
    0 ≤ harperSquarefreeCoefficientNormalizedEnergy y omega := by
  unfold harperSquarefreeCoefficientNormalizedEnergy
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (harperSquarefreeCoefficientPrefixEnergy_nonneg y omega))
    (Real.log_pos (by exact_mod_cast hy)).le

/-- After division by the logarithmic length of the coefficient interval,
the weighted absolute partial-sum mass is bounded pointwise by the square
root of the normalized coefficient energy.  The harmless factor `2π` in
the normalization only strengthens the estimate. -/
theorem weightedL1_div_log_le_normalizedEnergy_half
    (y : ℕ) (omega : Problem520.Omega) (hy : 1 < y) :
    harperSquarefreeCoefficientWeightedL1 y omega / Real.log (y : ℝ) ≤
      harperSquarefreeCoefficientNormalizedEnergy y omega ^ ((1 : ℝ) / 2) := by
  let W : ℝ := harperSquarefreeCoefficientWeightedL1 y omega
  let E : ℝ := harperSquarefreeCoefficientPrefixEnergy y omega
  let L : ℝ := Real.log (y : ℝ)
  let Z : ℝ := harperSquarefreeCoefficientNormalizedEnergy y omega
  have hW0 : 0 ≤ W := harperSquarefreeCoefficientWeightedL1_nonneg y omega
  have hE0 : 0 ≤ E := harperSquarefreeCoefficientPrefixEnergy_nonneg y omega
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hy)
  have hZ0 : 0 ≤ Z :=
    harperSquarefreeCoefficientNormalizedEnergy_nonneg hy omega
  have hCauchy : W ≤ Real.sqrt E * Real.sqrt L := by
    simpa only [W, E, L] using
      coefficientWeightedL1_le_sqrt_prefixEnergy_mul_sqrt_log y omega hy
  have hright0 : 0 ≤ Real.sqrt E * Real.sqrt L :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hWsq : W ^ 2 ≤ E * L := by
    have hsquare := (sq_le_sq₀ hW0 hright0).2 hCauchy
    rw [mul_pow, Real.sq_sqrt hE0, Real.sq_sqrt hL.le] at hsquare
    exact hsquare
  have hquot0 : 0 ≤ W / L := div_nonneg hW0 hL.le
  have hquotSq : (W / L) ^ 2 ≤ Z := by
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hZE : Z = (2 * Real.pi) * E / L := by
      simp only [Z, E, L, harperSquarefreeCoefficientNormalizedEnergy]
    rw [hZE, div_pow]
    have hfirst : W ^ 2 / L ^ 2 ≤ E / L := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hL) hL).2
      nlinarith [hWsq]
    have hscale : E ≤ (2 * Real.pi) * E := by nlinarith
    exact hfirst.trans (div_le_div_of_nonneg_right hscale hL.le)
  have hsqrt : Real.sqrt Z = Z ^ ((1 : ℝ) / 2) :=
    Real.sqrt_eq_rpow Z
  rw [← hsqrt]
  exact (sq_le_sq₀ hquot0 (Real.sqrt_nonneg Z)).1 (by
    rw [Real.sq_sqrt hZ0]
    exact hquotSq)

theorem measurable_harperSquarefreeCoefficientNormalizedEnergy (y : ℕ) :
    Measurable fun omega : Problem520.Omega ↦
      harperSquarefreeCoefficientNormalizedEnergy y omega := by
  unfold harperSquarefreeCoefficientNormalizedEnergy
  exact ((measurable_harperSquarefreeCoefficientPrefixEnergy y).const_mul
    (2 * Real.pi)).div measurable_const

/-- The normalized coefficient-range energy is pointwise bounded by the full
normalized Harper energy, so its upper `2/3` moment needs no new analysis. -/
theorem harperSquarefreeCoefficientNormalizedEnergy_le_initial
    {y : ℕ} (hy : 1 < y) (omega : Problem520.Omega) :
    harperSquarefreeCoefficientNormalizedEnergy y omega ≤
      Problem520.harperInitialNormalizedEnergy y omega := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  unfold harperSquarefreeCoefficientNormalizedEnergy
    Problem520.harperInitialNormalizedEnergy
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (harperSquarefreeCoefficientPrefixEnergy_le_smoothEnergy y omega)
      (mul_nonneg (by norm_num) Real.pi_pos.le)) hlog.le

theorem integrable_harperSquarefreeCoefficientNormalizedEnergy
    {y : ℕ} (hy : 1 < y) :
    Integrable (harperSquarefreeCoefficientNormalizedEnergy y) Problem520.μ := by
  apply (Problem520.integrable_harperInitialNormalizedEnergy y).mono'
  · exact (measurable_harperSquarefreeCoefficientNormalizedEnergy y).aestronglyMeasurable
  · exact ae_of_all _ fun omega ↦ by
      have hZ0 := harperSquarefreeCoefficientNormalizedEnergy_nonneg hy omega
      have hH0 := Problem1144.harperInitialNormalizedEnergy_nonneg hy omega
      simpa only [Real.norm_eq_abs, abs_of_nonneg hZ0, abs_of_nonneg hH0] using
        harperSquarefreeCoefficientNormalizedEnergy_le_initial hy omega

theorem integrable_harperSquarefreeCoefficientNormalizedEnergy_half
    {y : ℕ} (hy : 1 < y) :
    Integrable (fun omega ↦
      harperSquarefreeCoefficientNormalizedEnergy y omega ^ ((1 : ℝ) / 2))
        Problem520.μ := by
  exact Problem520.integrable_rpow_of_integrable_nonneg
    (integrable_harperSquarefreeCoefficientNormalizedEnergy hy)
    (harperSquarefreeCoefficientNormalizedEnergy_nonneg hy)
    (by norm_num) (by norm_num)

theorem integrable_harperSquarefreeCoefficientWeightedL1_div_log
    {y : ℕ} (hy : 1 < y) :
    Integrable (fun omega ↦
      harperSquarefreeCoefficientWeightedL1 y omega / Real.log (y : ℝ))
        Problem520.μ := by
  apply (integrable_harperSquarefreeCoefficientNormalizedEnergy_half hy).mono'
  · exact ((measurable_harperSquarefreeCoefficientWeightedL1 y).div
      measurable_const).aestronglyMeasurable
  · exact ae_of_all _ fun omega ↦ by
      have hleft0 : 0 ≤ harperSquarefreeCoefficientWeightedL1 y omega /
          Real.log (y : ℝ) :=
        div_nonneg (harperSquarefreeCoefficientWeightedL1_nonneg y omega)
          (Real.log_pos (by exact_mod_cast hy)).le
      have hright0 : 0 ≤
          harperSquarefreeCoefficientNormalizedEnergy y omega ^ ((1 : ℝ) / 2) :=
        Real.rpow_nonneg
          (harperSquarefreeCoefficientNormalizedEnergy_nonneg hy omega) _
      simpa only [Real.norm_eq_abs, abs_of_nonneg hleft0,
        abs_of_nonneg hright0] using
        weightedL1_div_log_le_normalizedEnergy_half y omega hy

theorem measurableSet_halfMomentLargeEvent_squarefreeCoefficient
    (y : ℕ) (a : ℝ) :
    MeasurableSet (halfMomentLargeEvent
      (harperSquarefreeCoefficientNormalizedEnergy y) a) := by
  unfold halfMomentLargeEvent
  exact measurableSet_le measurable_const
    ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).measurable.comp
      (measurable_harperSquarefreeCoefficientNormalizedEnergy y))

/-- The critical upper `2/3` moment transfers immediately from the full
Harper energy to the coefficient-range energy. -/
theorem integrable_harperSquarefreeCoefficientNormalizedEnergy_twoThird
    {y : ℕ} (hy : 1 < y) :
    Integrable (fun omega : Problem520.Omega ↦
      harperSquarefreeCoefficientNormalizedEnergy y omega ^
        Problem520.harperTwoThird) Problem520.μ := by
  let Z : Problem520.Omega → ℝ := fun omega ↦
    harperSquarefreeCoefficientNormalizedEnergy y omega
  let H : Problem520.Omega → ℝ := fun omega ↦
    Problem520.harperInitialNormalizedEnergy y omega
  have hmajor : Integrable (fun omega ↦ H omega ^ Problem520.harperTwoThird)
      Problem520.μ :=
    Problem520.integrable_harperInitialNormalizedEnergy_twoThird hy
  apply hmajor.mono'
  · exact ((Real.continuous_rpow_const
      (by norm_num [Problem520.harperTwoThird] :
        (0 : ℝ) ≤ Problem520.harperTwoThird)).measurable.comp
        (measurable_harperSquarefreeCoefficientNormalizedEnergy y)).aestronglyMeasurable
  · exact ae_of_all _ fun omega ↦ by
      have hZ0 : 0 ≤ Z omega :=
        harperSquarefreeCoefficientNormalizedEnergy_nonneg hy omega
      have hZH : Z omega ≤ H omega :=
        harperSquarefreeCoefficientNormalizedEnergy_le_initial hy omega
      have hrpow : Z omega ^ Problem520.harperTwoThird ≤
          H omega ^ Problem520.harperTwoThird :=
        Real.rpow_le_rpow hZ0 hZH
          (by norm_num [Problem520.harperTwoThird])
      have hZpow : 0 ≤ Z omega ^ Problem520.harperTwoThird :=
        Real.rpow_nonneg hZ0 _
      have hH0 : 0 ≤ H omega := hZ0.trans hZH
      have hHpow : 0 ≤ H omega ^ Problem520.harperTwoThird :=
        Real.rpow_nonneg hH0 _
      simpa only [Real.norm_eq_abs, abs_of_nonneg hZpow,
        abs_of_nonneg hHpow, Z, H] using hrpow

theorem integral_harperSquarefreeCoefficientNormalizedEnergy_twoThird_le_initial
    {y : ℕ} (hy : 1 < y) :
    (∫ omega,
        harperSquarefreeCoefficientNormalizedEnergy y omega ^
          Problem520.harperTwoThird ∂Problem520.μ) ≤
      ∫ omega,
        Problem520.harperInitialNormalizedEnergy y omega ^
          Problem520.harperTwoThird ∂Problem520.μ := by
  apply integral_mono
    (integrable_harperSquarefreeCoefficientNormalizedEnergy_twoThird hy)
    (Problem520.integrable_harperInitialNormalizedEnergy_twoThird hy)
  intro omega
  exact Real.rpow_le_rpow
    (harperSquarefreeCoefficientNormalizedEnergy_nonneg hy omega)
    (harperSquarefreeCoefficientNormalizedEnergy_le_initial hy omega)
    (by norm_num [Problem520.harperTwoThird])

theorem integral_harperSquarefreeCoefficientNormalizedEnergy_twoThird_le_of_harperBound
    {C : ℝ} {Y y : ℕ}
    (hHarper : Problem520.HarperRademacherInitialMomentBound C Y)
    (hY : Y ≤ y) (hy : 2 ≤ y) :
    (∫ omega,
        harperSquarefreeCoefficientNormalizedEnergy y omega ^
          Problem520.harperTwoThird ∂Problem520.μ) ≤
      C / (1 + Problem520.logLogNat y) ^ ((1 : ℝ) / 3) := by
  exact (integral_harperSquarefreeCoefficientNormalizedEnergy_twoThird_le_initial
    (by omega)).trans (hHarper y hY hy)

/-! ## The one remaining analytic checkpoint and its probability handoff -/

/-- Weighted first-absolute-moment form of the coefficient-scale analytic
checkpoint.  By Tonelli this is the logarithmic average of the one-height
quantities `ℙ |Ψ(z)| / √z`; the present formulation avoids asking the
analytic input for any unnecessary pointwise uniformity in `z`. -/
def HarperSquarefreeCoefficientWeightedL1LowerBound (c : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y → 4 ≤ y →
    c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2) ≤
      ∫ omega,
        harperSquarefreeCoefficientWeightedL1 y omega / Real.log (y : ℝ)
          ∂Problem520.μ

def HarperSquarefreeCoefficientWeightedL1LowerStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ,
    HarperSquarefreeCoefficientWeightedL1LowerBound c Y

/-- Localized lower half moment on the actual fresh-coefficient range. -/
def HarperSquarefreeCoefficientHalfMomentLowerBound (c : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y → 4 ≤ y →
    c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2) ≤
      ∫ omega,
        harperSquarefreeCoefficientNormalizedEnergy y omega ^ ((1 : ℝ) / 2)
          ∂Problem520.μ

def HarperSquarefreeCoefficientHalfMomentLowerStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ,
    HarperSquarefreeCoefficientHalfMomentLowerBound c Y

/-- The weighted one-height first-moment checkpoint implies the formerly
primitive localized energy half-moment checkpoint. -/
theorem harperSquarefreeCoefficientHalfMomentLowerBound_of_weightedL1
    {c : ℝ} {Y : ℕ}
    (hweighted : HarperSquarefreeCoefficientWeightedL1LowerBound c Y) :
    HarperSquarefreeCoefficientHalfMomentLowerBound c Y := by
  intro y hY hy
  refine (hweighted y hY hy).trans ?_
  apply integral_mono
    (integrable_harperSquarefreeCoefficientWeightedL1_div_log (by omega))
    (integrable_harperSquarefreeCoefficientNormalizedEnergy_half (by omega))
  intro omega
  exact weightedL1_div_log_le_normalizedEnergy_half y omega (by omega)

theorem harperSquarefreeCoefficientHalfMomentLowerStatement_of_weightedL1
    (hweighted : HarperSquarefreeCoefficientWeightedL1LowerStatement) :
    HarperSquarefreeCoefficientHalfMomentLowerStatement := by
  obtain ⟨c, hc, Y, hbound⟩ := hweighted
  exact ⟨c, hc, Y,
    harperSquarefreeCoefficientHalfMomentLowerBound_of_weightedL1 hbound⟩

/-- Once the localized half moment is supplied, the already compiled full
upper `2/3` moment yields a scale-uniform positive-probability coefficient
energy event. -/
theorem harperSquarefreeCoefficientCriticalEnergy_probability_lower
    {c C : ℝ} {Yhalf Ytwo y : ℕ}
    (hc : 0 < c) (hC : 0 < C)
    (hhalf : HarperSquarefreeCoefficientHalfMomentLowerBound c Yhalf)
    (htwo : Problem520.HarperRademacherInitialMomentBound C Ytwo)
    (hyHalf : Yhalf ≤ y) (hyTwo : Ytwo ≤ y) (hy : 4 ≤ y) :
    (c / (2 * C ^ ((3 : ℝ) / 4))) ^ (4 : ℝ) ≤
      Problem520.μ.real
        (halfMomentLargeEvent
          (harperSquarefreeCoefficientNormalizedEnergy y)
          (c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2))) := by
  let Z : Problem520.Omega → ℝ :=
    harperSquarefreeCoefficientNormalizedEnergy y
  let K : ℝ := harperInitialCriticalScale y
  have hy1 : 1 < y := by omega
  have hZnonneg : ∀ omega, 0 ≤ Z omega :=
    harperSquarefreeCoefficientNormalizedEnergy_nonneg hy1
  have hZint : Integrable Z Problem520.μ :=
    integrable_harperSquarefreeCoefficientNormalizedEnergy hy1
  have hhalfInt : Integrable
      (fun omega ↦ Z omega ^ ((1 : ℝ) / 2)) Problem520.μ :=
    integrable_harperSquarefreeCoefficientNormalizedEnergy_half hy1
  have htwoInt : Integrable
      (fun omega ↦ Z omega ^ ((2 : ℝ) / 3)) Problem520.μ := by
    simpa only [Z, Problem520.harperTwoThird] using
      integrable_harperSquarefreeCoefficientNormalizedEnergy_twoThird hy1
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
          C / (1 + Problem520.logLogNat y) ^ ((1 : ℝ) / 3) := by
        simpa only [Z, Problem520.harperTwoThird] using
          integral_harperSquarefreeCoefficientNormalizedEnergy_twoThird_le_of_harperBound
            htwo hyTwo (by omega)
      _ = C * K ^ ((2 : ℝ) / 3) := by
        rw [harperInitialCriticalScale_rpow_twoThird hy]
        ring
  exact criticalScale_halfMoment_twoThird_probability_lower
    (nu := Problem520.μ) (Z := Z) (c := c) (C := C) (K := K)
    (measurableSet_halfMomentLargeEvent_squarefreeCoefficient y
      (c * K ^ ((1 : ℝ) / 2)))
    hZnonneg hhalfInt hhalfLp hc hC (harperInitialCriticalScale_pos hy)
    (hhalf y hyHalf hy) htwoScale

theorem exists_harperSquarefreeCoefficientCriticalEnergy_fixedProbability
    (hhalfStatement : HarperSquarefreeCoefficientHalfMomentLowerStatement) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ y : ℕ,
      Y ≤ y →
      delta ≤ Problem520.μ.real
        (halfMomentLargeEvent
          (harperSquarefreeCoefficientNormalizedEnergy y)
          (c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2))) := by
  obtain ⟨c, hc, Yhalf, hhalf⟩ := hhalfStatement
  obtain ⟨C, hC, Ytwo, _hYtwo, htwo⟩ :=
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
  simpa only [delta] using
    harperSquarefreeCoefficientCriticalEnergy_probability_lower
      hc hC hhalf htwo hyHalf hyTwo hy4

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.squarefreePartialSum_eq_Ψ_of_le
#print axioms Erdos.Problem1144.ΨReal_eq_squarefreePartialSum_of_le
#print axioms Erdos.Problem1144.coefficientWeightedL1_le_sqrt_prefixEnergy_mul_sqrt_log
#print axioms Erdos.Problem1144.weightedL1_div_log_le_normalizedEnergy_half
#print axioms Erdos.Problem1144.harperSquarefreeCoefficientPrefixEnergy_le_smoothEnergy
#print axioms Erdos.Problem1144.harperSquarefreeCoefficientPrefixEnergy_eq_partialSum
#print axioms Erdos.Problem1144.harperSquarefreeCoefficientNormalizedEnergy_le_initial
#print axioms Erdos.Problem1144.harperSquarefreeCoefficientHalfMomentLowerBound_of_weightedL1
#print axioms Erdos.Problem1144.integral_harperSquarefreeCoefficientNormalizedEnergy_twoThird_le_of_harperBound
#print axioms Erdos.Problem1144.harperSquarefreeCoefficientCriticalEnergy_probability_lower
#print axioms Erdos.Problem1144.exists_harperSquarefreeCoefficientCriticalEnergy_fixedProbability
