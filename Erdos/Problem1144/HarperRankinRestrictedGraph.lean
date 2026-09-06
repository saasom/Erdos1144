import Erdos.Problem1144.HarperRankinNormalizer

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Restricted shifted Euler energy

This is the one-height assembly for the Rankin-localized coefficient energy.
The logarithmic ballot graph is integrated against the shifted Euler density.
The factor `4/5` exactly absorbs the `5/4` central-band Parseval loss, so the
restricted graph energy is pointwise below the shifted normalized coefficient
energy.
-/

/-- Heights for which a fixed finite sign world obeys the shifted logarithmic
ballot. -/
def harperRankinLogBallotHeightSection
    (y start n : ℕ) (a : ℝ) (eta : Problem520.HarperPrimeCube y) : Set ℝ :=
  {t | eta ∈ harperRankinLogBallotCubeEvent y start n a t}

private theorem continuous_harperRankinLogBallotPartialSum
    (y start n : ℕ) (a : ℝ) (eta : Problem520.HarperPrimeCube y)
    (k : Fin n) :
    Continuous (fun t : ℝ ↦
      Problem520.harperPathPartialSum
        (harperRankinScheduledCenteredBlockVector y start n a t eta) k) := by
  unfold Problem520.harperPathPartialSum
    harperRankinScheduledCenteredBlockVector
    harperRankinCenteredLinearPrimeBlockSum
    harperRankinCenteredLinearPrimeIncrement
    harperRankinLinearPrimeIncrement
    harperRankinTiltBias harperRankinEulerNormalizer
  fun_prop (disch := positivity)

theorem measurableSet_harperRankinLogBallotHeightSection
    (y start n : ℕ) (a : ℝ) (eta : Problem520.HarperPrimeCube y) :
    MeasurableSet (harperRankinLogBallotHeightSection y start n a eta) := by
  rw [show harperRankinLogBallotHeightSection y start n a eta =
      ⋂ k : Fin n, {t : ℝ |
        harper1144LogBallotLowerBarrier start n k ≤
            Problem520.harperPathPartialSum
              (harperRankinScheduledCenteredBlockVector
                y start n a t eta) k ∧
          Problem520.harperPathPartialSum
              (harperRankinScheduledCenteredBlockVector
                y start n a t eta) k ≤
            harper1144LogBallotUpperBarrier n k} by
    ext t
    simp only [harperRankinLogBallotHeightSection,
      harperRankinLogBallotCubeEvent,
      Problem520.mem_harperPartialSumBarrierSet,
      Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]]
  exact MeasurableSet.iInter fun k ↦
    (measurableSet_le measurable_const
      (continuous_harperRankinLogBallotPartialSum
        y start n a eta k).measurable).inter
      (measurableSet_le
        (continuous_harperRankinLogBallotPartialSum
          y start n a eta k).measurable measurable_const)

/-- Joint height/sign graph of the shifted logarithmic ballot. -/
def harperRankinLogBallotGraph
    (y start n : ℕ) (a : ℝ) : Set (ℝ × Problem520.Omega) :=
  {w | Problem520.harperPrimeRestriction y w.2 ∈
    harperRankinLogBallotCubeEvent y start n a w.1}

theorem measurableSet_harperRankinLogBallotGraph
    (y start n : ℕ) (a : ℝ) :
    MeasurableSet (harperRankinLogBallotGraph y start n a) := by
  have heq : harperRankinLogBallotGraph y start n a =
      ⋃ eta : Problem520.HarperPrimeCube y,
        harperRankinLogBallotHeightSection y start n a eta ×ˢ
          ((Problem520.harperPrimeRestriction y) ⁻¹' {eta}) := by
    ext w
    constructor
    · intro hw
      refine Set.mem_iUnion.2
        ⟨Problem520.harperPrimeRestriction y w.2, ?_⟩
      exact ⟨hw, rfl⟩
    · rintro hw
      obtain ⟨eta, heta⟩ := Set.mem_iUnion.1 hw
      change w.1 ∈ harperRankinLogBallotHeightSection y start n a eta ∧
        Problem520.harperPrimeRestriction y w.2 = eta at heta
      change Problem520.harperPrimeRestriction y w.2 ∈
        harperRankinLogBallotCubeEvent y start n a w.1
      rw [heta.2]
      exact heta.1
  rw [heq]
  exact MeasurableSet.iUnion fun eta ↦
    (measurableSet_harperRankinLogBallotHeightSection
      y start n a eta).prod
        ((measurableSet_singleton eta).preimage
          (Problem520.measurable_harperPrimeRestriction y))

theorem measurable_harperRankinEulerDensity_joint (y : ℕ) (a : ℝ) :
    Measurable (fun w : ℝ × Problem520.Omega ↦
      harperRankinEulerDensity y a w.2 w.1) := by
  unfold harperRankinEulerDensity
  apply Finset.measurable_prod
  intro p hp
  unfold harperRankinEulerFactor
  have heps : Measurable (fun w : ℝ × Problem520.Omega ↦
      Problem520.ε w.2 p) :=
    (Problem520.measurable_ε p).comp measurable_snd
  have hcos : Measurable (fun w : ℝ × Problem520.Omega ↦
      Real.cos (w.1 * Real.log (p : ℝ))) := by fun_prop
  have hsin : Measurable (fun w : ℝ × Problem520.Omega ↦
      Real.sin (w.1 * Real.log (p : ℝ))) := by fun_prop
  exact ((measurable_const.add
      ((heps.mul_const (harperRankinEulerRadius p a)).mul hcos)).pow_const 2).add
    (((heps.mul_const (harperRankinEulerRadius p a)).mul hsin).pow_const 2)

/-- A deterministic finite upper bound for the shifted Euler density. -/
noncomputable def harperRankinEulerDensityUniformBound
    (y : ℕ) (a : ℝ) : ℝ :=
  ∏ p ∈ (y + 1).primesBelow, (1 + harperRankinEulerRadius p a) ^ 2

theorem harperRankinEulerDensityUniformBound_nonneg (y : ℕ) (a : ℝ) :
    0 ≤ harperRankinEulerDensityUniformBound y a := by
  unfold harperRankinEulerDensityUniformBound
  positivity

private theorem harperRankinEulerFactor_le_uniform
    (omega : Problem520.Omega) (p : ℕ) (a t : ℝ) :
    harperRankinEulerFactor omega p a t ≤
      (1 + harperRankinEulerRadius p a) ^ 2 := by
  let r : ℝ := harperRankinEulerRadius p a
  have hr : 0 ≤ r := harperRankinEulerRadius_nonneg p a
  have hepscos : Problem520.ε omega p *
      Real.cos (t * Real.log (p : ℝ)) ≤ 1 := by
    calc
      Problem520.ε omega p * Real.cos (t * Real.log (p : ℝ)) ≤
          |Problem520.ε omega p * Real.cos (t * Real.log (p : ℝ))| :=
        le_abs_self _
      _ = |Real.cos (t * Real.log (p : ℝ))| := by
        rw [abs_mul, Problem520.abs_ε, one_mul]
      _ ≤ 1 := Real.abs_cos_le_one _
  rw [harperRankinEulerFactor_eq]
  dsimp only [r] at hr hepscos ⊢
  nlinarith

theorem harperRankinEulerDensity_le_uniformBound
    (y : ℕ) (a : ℝ) (omega : Problem520.Omega) (t : ℝ) :
    harperRankinEulerDensity y a omega t ≤
      harperRankinEulerDensityUniformBound y a := by
  unfold harperRankinEulerDensity harperRankinEulerDensityUniformBound
  exact Finset.prod_le_prod
    (fun p hp ↦ harperRankinEulerFactor_nonneg omega p a t)
    (fun p hp ↦ harperRankinEulerFactor_le_uniform omega p a t)

/-- The shifted restricted energy, scaled so that Parseval gives pointwise
domination by the shifted coefficient energy with constant exactly `1`. -/
noncomputable def harperRankinRestrictedGraphEnergy
    (y : ℕ) (a : ℝ) (G : Set (ℝ × Problem520.Omega))
    (omega : Problem520.Omega) : ℝ :=
  (4 / 5 : ℝ) *
    (∫ t in harperLowerVerticalBand,
      G.indicator (fun w : ℝ × Problem520.Omega ↦
        harperRankinEulerDensity y a w.2 w.1) (t, omega)) /
    Real.log (y : ℝ)

theorem harperRankinRestrictedGraphEnergy_nonneg
    {y : ℕ} (hy : 1 < y) (a : ℝ) (G : Set (ℝ × Problem520.Omega))
    (omega : Problem520.Omega) :
    0 ≤ harperRankinRestrictedGraphEnergy y a G omega := by
  have hlog : 0 ≤ Real.log (y : ℝ) :=
    (Real.log_pos (by exact_mod_cast hy)).le
  have hint : 0 ≤ ∫ t in harperLowerVerticalBand,
      G.indicator (fun w : ℝ × Problem520.Omega ↦
        harperRankinEulerDensity y a w.2 w.1) (t, omega) := by
    exact setIntegral_nonneg measurableSet_harperLowerVerticalBand
      fun t ht ↦ Set.indicator_nonneg
        (fun w hw ↦ harperRankinEulerDensity_nonneg y a w.2 w.1) (t, omega)
  unfold harperRankinRestrictedGraphEnergy
  exact div_nonneg (mul_nonneg (by norm_num) hint) hlog

theorem integrableOn_harperRankinRestrictedGraphDensity
    (y : ℕ) (a : ℝ) {G : Set (ℝ × Problem520.Omega)}
    (hG : MeasurableSet G) (omega : Problem520.Omega) :
    IntegrableOn
      (fun t ↦ G.indicator (fun w : ℝ × Problem520.Omega ↦
        harperRankinEulerDensity y a w.2 w.1) (t, omega))
      harperLowerVerticalBand := by
  let fiber : Set ℝ := {t | (t, omega) ∈ G}
  have hfiber : MeasurableSet fiber :=
    hG.preimage (measurable_id.prodMk measurable_const)
  have hcont : Continuous (fun t ↦ harperRankinEulerDensity y a omega t) := by
    unfold harperRankinEulerDensity harperRankinEulerFactor
    fun_prop
  have hbase : IntegrableOn
      (fun t ↦ harperRankinEulerDensity y a omega t)
      harperLowerVerticalBand := hcont.integrableOn_Icc
  have hindicator :
      (fun t ↦ G.indicator (fun w : ℝ × Problem520.Omega ↦
          harperRankinEulerDensity y a w.2 w.1) (t, omega)) =
        fiber.indicator (fun t ↦ harperRankinEulerDensity y a omega t) := by
    funext t
    by_cases ht : (t, omega) ∈ G <;> simp [fiber, ht]
  rw [hindicator]
  exact hbase.indicator hfiber

private theorem integrable_harperRankinGraphDensity_prod
    (y : ℕ) (a : ℝ) {G : Set (ℝ × Problem520.Omega)}
    (hG : MeasurableSet G) :
    Integrable
      (fun w : ℝ × Problem520.Omega ↦
        G.indicator (fun z : ℝ × Problem520.Omega ↦
          harperRankinEulerDensity y a z.2 z.1) w)
      ((volume.restrict harperLowerVerticalBand).prod Problem520.μ) := by
  let nu : Measure ℝ := volume.restrict harperLowerVerticalBand
  have hfinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  letI : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 hfinite
  let F : ℝ × Problem520.Omega → ℝ := fun w ↦
    G.indicator (fun z : ℝ × Problem520.Omega ↦
      harperRankinEulerDensity y a z.2 z.1) w
  have hFmeas : Measurable F :=
    (measurable_harperRankinEulerDensity_joint y a).indicator hG
  apply Integrable.of_bound hFmeas.aestronglyMeasurable
    (harperRankinEulerDensityUniformBound y a)
  exact ae_of_all _ fun w ↦ by
    by_cases hw : w ∈ G
    · simp only [F, Set.indicator_of_mem hw, Real.norm_eq_abs,
        abs_of_nonneg (harperRankinEulerDensity_nonneg y a w.2 w.1)]
      exact harperRankinEulerDensity_le_uniformBound y a w.2 w.1
    · simp [F, hw, harperRankinEulerDensityUniformBound_nonneg]

theorem integrable_harperRankinRestrictedGraphEnergy
    {y : ℕ} (a : ℝ) {G : Set (ℝ × Problem520.Omega)}
    (hG : MeasurableSet G) :
    Integrable (harperRankinRestrictedGraphEnergy y a G) Problem520.μ := by
  let nu : Measure ℝ := volume.restrict harperLowerVerticalBand
  let F : ℝ × Problem520.Omega → ℝ := fun w ↦
    G.indicator (fun z : ℝ × Problem520.Omega ↦
      harperRankinEulerDensity y a z.2 z.1) w
  have hF : Integrable F (nu.prod Problem520.μ) := by
    simpa only [nu, F] using
      integrable_harperRankinGraphDensity_prod y a hG
  have hinner := hF.integral_prod_right
  simpa only [harperRankinRestrictedGraphEnergy, nu, F] using
    (hinner.const_mul (4 / 5 : ℝ)).div_const (Real.log (y : ℝ))

/-- The restricted shifted graph energy is pointwise below the shifted
normalized coefficient energy. -/
theorem harperRankinRestrictedGraphEnergy_le_shiftedNormalized
    {y : ℕ} (hy : 1 < y) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {G : Set (ℝ × Problem520.Omega)} (hG : MeasurableSet G)
    (omega : Problem520.Omega) :
    harperRankinRestrictedGraphEnergy y a G omega ≤
      harperSquarefreeShiftedNormalizedEnergy y a omega := by
  let restricted : ℝ → ℝ := fun t ↦
    G.indicator (fun w : ℝ × Problem520.Omega ↦
      harperRankinEulerDensity y a w.2 w.1) (t, omega)
  have hrestricted : IntegrableOn restricted harperLowerVerticalBand := by
    simpa only [restricted] using
      integrableOn_harperRankinRestrictedGraphDensity y a hG omega
  have hbase : IntegrableOn
      (fun t ↦ harperRankinEulerDensity y a omega t)
      harperLowerVerticalBand := by
    have hcont : Continuous (fun t ↦ harperRankinEulerDensity y a omega t) := by
      unfold harperRankinEulerDensity harperRankinEulerFactor
      fun_prop
    exact hcont.integrableOn_Icc
  have hpoint (t : ℝ) (_ht : t ∈ harperLowerVerticalBand) :
      restricted t ≤ harperRankinEulerDensity y a omega t := by
    by_cases hmem : (t, omega) ∈ G
    · simp [restricted, hmem]
    · simp [restricted, hmem, harperRankinEulerDensity_nonneg]
  have hnum :
      (∫ t in harperLowerVerticalBand, restricted t) ≤
        (5 / 4 : ℝ) * (2 * Real.pi) *
          harperSquarefreeShiftedSmoothEnergy y a omega :=
    (setIntegral_mono_on hrestricted hbase
      measurableSet_harperLowerVerticalBand hpoint).trans
        (integral_harperLowerVerticalBand_harperRankinEulerDensity_le
          y omega ha ha1)
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  unfold harperRankinRestrictedGraphEnergy
    harperSquarefreeShiftedNormalizedEnergy
  change (4 / 5 : ℝ) *
      (∫ t in harperLowerVerticalBand, restricted t) /
        Real.log (y : ℝ) ≤ _
  apply (div_le_div_iff_of_pos_right hlog).2
  nlinarith

/-! ## Exact first moment -/

theorem integral_harperRankinRestrictedGraphEnergy_eq_tiltedProbabilities
    {y : ℕ} (a : ℝ) {G : Set (ℝ × Problem520.Omega)}
    (hG : MeasurableSet G)
    (A : ℝ → Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t) :
    (∫ omega, harperRankinRestrictedGraphEnergy y a G omega ∂Problem520.μ) =
      (4 / 5 : ℝ) *
        (harperRankinPrimeEnergyNormalizer y a / Real.log (y : ℝ)) *
          ∫ t in harperLowerVerticalBand,
            (harperRankinTiltedCubeLaw y a t).real (A t) := by
  let nu : Measure ℝ := volume.restrict harperLowerVerticalBand
  let F : ℝ × Problem520.Omega → ℝ := fun w ↦
    G.indicator (fun z : ℝ × Problem520.Omega ↦
      harperRankinEulerDensity y a z.2 z.1) w
  have hF : Integrable F (nu.prod Problem520.μ) := by
    simpa only [nu, F] using
      integrable_harperRankinGraphDensity_prod y a hG
  have hswap :
      (∫ omega, ∫ t, F (t, omega) ∂nu ∂Problem520.μ) =
        ∫ t, ∫ omega, F (t, omega) ∂Problem520.μ ∂nu :=
    (integral_prod_symm F hF).symm.trans (integral_prod F hF)
  have hinner (t : ℝ) :
      (∫ omega, F (t, omega) ∂Problem520.μ) =
        harperRankinPrimeEnergyNormalizer y a *
          (harperRankinTiltedCubeLaw y a t).real (A t) := by
    let P : Set Problem520.Omega :=
      Problem520.harperPrimeRestriction y ⁻¹' A t
    have hA : MeasurableSet (A t) := Set.toFinite (A t) |>.measurableSet
    have hP : MeasurableSet P :=
      hA.preimage (Problem520.measurable_harperPrimeRestriction y)
    have hfun : (fun omega ↦ F (t, omega)) =
        P.indicator (fun omega ↦ harperRankinEulerDensity y a omega t) := by
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
        (fun omega ↦ harperRankinEulerDensity y a omega t) =
          fun omega ↦ harperRankinPrimeEnergyNormalizer y a *
            normalizedHarperRankinEulerDensity y a omega t := by
      funext omega
      unfold normalizedHarperRankinEulerDensity
      field_simp [(harperRankinPrimeEnergyNormalizer_pos y a).ne']
    rw [hdensity, integral_const_mul,
      harperRankinTiltedCubeLaw_real_apply_eq_omega]
  have houter :
      (∫ t, ∫ omega, F (t, omega) ∂Problem520.μ ∂nu) =
        harperRankinPrimeEnergyNormalizer y a *
          ∫ t in harperLowerVerticalBand,
            (harperRankinTiltedCubeLaw y a t).real (A t) := by
    rw [show (fun t ↦ ∫ omega, F (t, omega) ∂Problem520.μ) =
        fun t ↦ harperRankinPrimeEnergyNormalizer y a *
          (harperRankinTiltedCubeLaw y a t).real (A t) by
      funext t
      exact hinner t]
    rw [integral_const_mul]
  have hraw := hswap.trans houter
  unfold harperRankinRestrictedGraphEnergy
  rw [integral_div, integral_const_mul]
  change ((4 / 5 : ℝ) *
      (∫ omega, ∫ t, F (t, omega) ∂nu ∂Problem520.μ)) /
        Real.log (y : ℝ) = _
  rw [hraw]
  ring

theorem integrableOn_harperRankinTiltedCubeLaw_real_of_graph
    {y : ℕ} (a : ℝ) {G : Set (ℝ × Problem520.Omega)}
    (hG : MeasurableSet G)
    (A : ℝ → Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t) :
    IntegrableOn
      (fun t ↦ (harperRankinTiltedCubeLaw y a t).real (A t))
      harperLowerVerticalBand := by
  let nu : Measure ℝ := volume.restrict harperLowerVerticalBand
  let F : ℝ × Problem520.Omega → ℝ := fun w ↦
    G.indicator (fun z : ℝ × Problem520.Omega ↦
      harperRankinEulerDensity y a z.2 z.1) w
  have hF : Integrable F (nu.prod Problem520.μ) := by
    simpa only [nu, F] using
      integrable_harperRankinGraphDensity_prod y a hG
  have hinner (t : ℝ) :
      (∫ omega, F (t, omega) ∂Problem520.μ) =
        harperRankinPrimeEnergyNormalizer y a *
          (harperRankinTiltedCubeLaw y a t).real (A t) := by
    let P : Set Problem520.Omega :=
      Problem520.harperPrimeRestriction y ⁻¹' A t
    have hA : MeasurableSet (A t) := Set.toFinite (A t) |>.measurableSet
    have hP : MeasurableSet P :=
      hA.preimage (Problem520.measurable_harperPrimeRestriction y)
    have hfun : (fun omega ↦ F (t, omega)) =
        P.indicator (fun omega ↦ harperRankinEulerDensity y a omega t) := by
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
        (fun omega ↦ harperRankinEulerDensity y a omega t) =
          fun omega ↦ harperRankinPrimeEnergyNormalizer y a *
            normalizedHarperRankinEulerDensity y a omega t := by
      funext omega
      unfold normalizedHarperRankinEulerDensity
      field_simp [(harperRankinPrimeEnergyNormalizer_pos y a).ne']
    rw [hdensity, integral_const_mul,
      harperRankinTiltedCubeLaw_real_apply_eq_omega]
  have hmul : Integrable
      (fun t ↦ harperRankinPrimeEnergyNormalizer y a *
        (harperRankinTiltedCubeLaw y a t).real (A t)) nu := by
    rw [← show (fun t ↦ ∫ omega, F (t, omega) ∂Problem520.μ) =
        fun t ↦ harperRankinPrimeEnergyNormalizer y a *
          (harperRankinTiltedCubeLaw y a t).real (A t) by
      funext t
      exact hinner t]
    exact hF.integral_prod_left
  have hdiv := hmul.div_const (harperRankinPrimeEnergyNormalizer y a)
  simpa only [nu, mul_div_cancel_left₀ _
    (harperRankinPrimeEnergyNormalizer_pos y a).ne'] using hdiv

/-- One-height ballot probabilities on the fixed band give the full shifted
restricted-energy first moment. -/
theorem integral_harperRankinRestrictedGraphEnergy_lower_of_tiltedProbabilities
    {V : ℝ} (hV : 0 ≤ V) {y : ℕ} (hy : 4 ≤ y)
    {G : Set (ℝ × Problem520.Omega)} (hG : MeasurableSet G)
    (A : ℝ → Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t)
    {delta K : ℝ} (hdelta : 0 ≤ delta) (hK : 0 ≤ K)
    (hprob : ∀ t ∈ harperLowerVerticalBand,
      delta * K ≤
        (harperRankinTiltedCubeLaw y
          (4 * V / Real.log (y : ℝ)) t).real (A t)) :
    ((2 / 15 : ℝ) *
        ((1 / 2 : ℝ) *
          Real.exp (-8 * V *
            (1 + (Real.log 4 + 4) / Real.log 4))) * delta) * K ≤
      ∫ omega,
        harperRankinRestrictedGraphEnergy y
          (4 * V / Real.log (y : ℝ)) G omega ∂Problem520.μ := by
  let a : ℝ := 4 * V / Real.log (y : ℝ)
  let cV : ℝ := (1 / 2 : ℝ) *
    Real.exp (-8 * V * (1 + (Real.log 4 + 4) / Real.log 4))
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hnormalizer : cV ≤
      harperRankinPrimeEnergyNormalizer y a / Real.log (y : ℝ) := by
    rw [le_div_iff₀ hlog]
    simpa only [cV, a] using exp_rankinNormalizerConstant_mul_log_le hV hy
  have hprobInt := integrableOn_harperRankinTiltedCubeLaw_real_of_graph
    a hG A hsection
  have hconstInt : IntegrableOn (fun _t : ℝ ↦ delta * K)
      harperLowerVerticalBand := integrableOn_const (by
    simp [harperLowerVerticalBand, Real.volume_Icc])
  have hintegral : (delta * K) / 6 ≤
      ∫ t in harperLowerVerticalBand,
        (harperRankinTiltedCubeLaw y a t).real (A t) := by
    have hmono := setIntegral_mono_on hconstInt hprobInt
      measurableSet_harperLowerVerticalBand (by
        intro t ht
        simpa only [a] using hprob t ht)
    calc
      (delta * K) / 6 =
          ∫ _t in harperLowerVerticalBand, delta * K := by
        norm_num [harperLowerVerticalBand, Real.volume_Icc] <;> ring
      _ ≤ _ := hmono
  rw [integral_harperRankinRestrictedGraphEnergy_eq_tiltedProbabilities
    a hG A hsection]
  have hcV : 0 ≤ cV := by dsimp only [cV]; positivity
  have hprobNonneg : 0 ≤ (delta * K) / 6 := by positivity
  have hnormalizerNonneg :
      0 ≤ harperRankinPrimeEnergyNormalizer y a / Real.log (y : ℝ) :=
    hcV.trans hnormalizer
  calc
    ((2 / 15 : ℝ) * cV * delta) * K =
        (4 / 5 : ℝ) * cV * ((delta * K) / 6) := by ring
    _ ≤ (4 / 5 : ℝ) *
          (harperRankinPrimeEnergyNormalizer y a / Real.log (y : ℝ)) *
            ((delta * K) / 6) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnormalizer (by norm_num)) hprobNonneg
    _ ≤ (4 / 5 : ℝ) *
          (harperRankinPrimeEnergyNormalizer y a / Real.log (y : ℝ)) *
            ∫ t in harperLowerVerticalBand,
              (harperRankinTiltedCubeLaw y a t).real (A t) := by
      exact mul_le_mul_of_nonneg_left hintegral
        (mul_nonneg (by norm_num) hnormalizerNonneg)

/-! ## Concrete one-height certificate -/

/-- The Rankin logarithmic ballot graph has a first moment of the critical
order and is pointwise dominated by the shifted coefficient energy.  Thus
the one-height half of the shifted certificate is completely unconditional. -/
theorem exists_harperRankinLogBallotRestrictedGraph_firstMoment
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → 4 ≤ y →
      let a : ℝ := 4 * V / Real.log (y : ℝ)
      ∃ G : Set (ℝ × Problem520.Omega), MeasurableSet G ∧
        (∀ omega,
          harperRankinRestrictedGraphEnergy y a G omega ≤
            harperSquarefreeShiftedNormalizedEnergy y a omega) ∧
        Integrable (harperRankinRestrictedGraphEnergy y a G) Problem520.μ ∧
        c * harperInitialCriticalScale y ≤
          ∫ omega, harperRankinRestrictedGraphEnergy y a G omega
            ∂Problem520.μ := by
  obtain ⟨delta, hdelta, gap, J, hone⟩ :=
    exists_gap_harperRankinLogBallotFixedStart_cube_ge_criticalScale V hV
  obtain ⟨Ylog, hYlog⟩ := exists_nat_gt (Real.exp (4 * V))
  let Yroom : ℕ := Problem520.harperBlockEndpoint (J + gap + 1)
  let Y : ℕ := max 4 (max Ylog Yroom)
  let cV : ℝ := (1 / 2 : ℝ) *
    Real.exp (-8 * V * (1 + (Real.log 4 + 4) / Real.log 4))
  let c : ℝ := (2 / 15 : ℝ) * cV * delta
  have hcV : 0 < cV := by dsimp only [cV]; positivity
  refine ⟨c, by dsimp only [c]; positivity, Y, ?_⟩
  intro y hyY hy4
  have hyLog : Ylog ≤ y :=
    (le_max_left Ylog Yroom).trans
      ((le_max_right 4 (max Ylog Yroom)).trans hyY)
  have hyRoom : Yroom ≤ y :=
    (le_max_right Ylog Yroom).trans
      ((le_max_right 4 (max Ylog Yroom)).trans hyY)
  let a : ℝ := 4 * V / Real.log (y : ℝ)
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hexpY : Real.exp (4 * V) < (y : ℝ) := by
    exact hYlog.trans_le (by exact_mod_cast hyLog)
  have hfourVlog : 4 * V < Real.log (y : ℝ) := by
    rw [← Real.exp_lt_exp]
    simpa only [Real.exp_log (by positivity : (0 : ℝ) < y)] using hexpY
  have ha1 : a ≤ 1 := by
    dsimp only [a]
    exact (div_le_one hlog).2 hfourVlog.le
  have hroom : J + gap + 5 ≤ Problem520.harperAvailableLogScale y := by
    have hendpoint : Problem520.harperBlockEndpoint (J + gap + 1) ≤ y :=
      hyRoom
    have h := Problem520.add_four_le_harperAvailableLogScale_of_blockEndpoint_le
      hendpoint
    omega
  let n : ℕ := Problem520.harperEconomicalPathLength y J gap
  have hn : 0 < n := by
    dsimp only [n]
    exact Problem520.harperEconomicalPathLength_pos hroom
  have hyne : y ≠ 0 := by omega
  have hfit : Problem520.harperEconomicalStart J gap + 4 ≤
      Problem520.harperAvailableLogScale y := by
    simp only [Problem520.harperEconomicalStart]
    omega
  have hendpoint : Problem520.harperBlockEndpoint (J + n + gap) ≤ y := by
    have h := Problem520.harperBlockEndpoint_economicalStart_add_le
      hyne hfit (m := n) le_rfl
    simpa only [Problem520.harperEconomicalStart, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using h
  let G : Set (ℝ × Problem520.Omega) :=
    harperRankinLogBallotGraph y J n a
  let A : ℝ → Set (Problem520.HarperPrimeCube y) := fun t ↦
    harperRankinLogBallotCubeEvent y J n a t
  have hG : MeasurableSet G := by
    simpa only [G] using measurableSet_harperRankinLogBallotGraph y J n a
  have hprob : ∀ t ∈ harperLowerVerticalBand,
      delta * harperInitialCriticalScale y ≤
        (harperRankinTiltedCubeLaw y a t).real (A t) := by
    intro t ht
    simpa only [a, A] using
      hone J le_rfl n y hn hy4 hendpoint t ht
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · intro omega
    exact harperRankinRestrictedGraphEnergy_le_shiftedNormalized
      (by omega) ha ha1 hG omega
  · exact integrable_harperRankinRestrictedGraphEnergy a hG
  · simpa only [c, cV, a] using
      integral_harperRankinRestrictedGraphEnergy_lower_of_tiltedProbabilities
        hV hy4 hG A (fun t omega ↦ Iff.rfl) hdelta.le
          (harperInitialCriticalScale_pos hy4).le hprob

#print axioms Erdos.Problem1144.measurableSet_harperRankinLogBallotGraph
#print axioms Erdos.Problem1144.harperRankinRestrictedGraphEnergy_le_shiftedNormalized
#print axioms Erdos.Problem1144.integral_harperRankinRestrictedGraphEnergy_eq_tiltedProbabilities
#print axioms Erdos.Problem1144.exists_harperRankinLogBallotRestrictedGraph_firstMoment

end

end Problem1144
end Erdos
