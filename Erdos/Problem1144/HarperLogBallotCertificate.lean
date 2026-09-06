import Erdos.Problem1144.HarperArbitraryCutoffBallot
import Erdos.Problem1144.HarperGaussianFixedStart
import Erdos.Problem1144.HarperTwoHeightRestrictedMass

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Complete logarithmic-ballot certificate

This module performs the last measure-theoretic assembly.  It constructs the
joint height/sign graph for the fixed-start pinched event, proves the exact
two-height mass integrable, and turns the terminal/shell partition bounds
into a full-band restricted second moment.
-/

/-- Heights for which one finite sign world satisfies the pinched event. -/
def harper1144LogBallotHeightSection
    (y start n : Nat) (eta : Problem520.HarperPrimeCube y) : Set Real :=
  {t | eta ∈ harper1144LogBallotCubeEvent y start n t}

theorem measurableSet_harper1144LogBallotHeightSection
    (y start n : Nat) (eta : Problem520.HarperPrimeCube y) :
    MeasurableSet (harper1144LogBallotHeightSection y start n eta) := by
  let path : Real → Fin n → Real := fun t ↦
    Problem520.harperScheduledCenteredBlockVectorVarying
      y start n t (fun _i : Fin n ↦ t) eta
  have hsum (k : Fin n) : Measurable
      (fun t : Real ↦ Problem520.harperPathPartialSum (path t) k) :=
    (continuous_harperScheduledDiagonalPartialSum
      y start n eta k).measurable
  rw [show harper1144LogBallotHeightSection y start n eta =
      ⋂ k : Fin n, {t : Real |
        harper1144LogBallotLowerBarrier start n k ≤
            Problem520.harperPathPartialSum (path t) k ∧
          Problem520.harperPathPartialSum (path t) k ≤
            harper1144LogBallotUpperBarrier n k} by
    ext t
    simp only [harper1144LogBallotHeightSection,
      harper1144LogBallotCubeEvent,
      Problem520.mem_harperPartialSumBarrierSet, Set.mem_setOf_eq,
      Set.mem_iInter, Set.mem_preimage, path]]
  exact MeasurableSet.iInter fun k ↦
    (measurableSet_le measurable_const (hsum k)).inter
      (measurableSet_le (hsum k) measurable_const)

/-- Joint height/sign graph of the fixed-start logarithmic ballot. -/
def harper1144LogBallotGraph
    (y start n : Nat) : Set (Real × Problem520.Omega) :=
  {w | Problem520.harperPrimeRestriction y w.2 ∈
    harper1144LogBallotCubeEvent y start n w.1}

theorem measurableSet_harper1144LogBallotGraph
    (y start n : Nat) :
    MeasurableSet (harper1144LogBallotGraph y start n) := by
  have heq : harper1144LogBallotGraph y start n =
      ⋃ eta : Problem520.HarperPrimeCube y,
        harper1144LogBallotHeightSection y start n eta ×ˢ
          ((Problem520.harperPrimeRestriction y) ⁻¹' {eta}) := by
    ext w
    constructor
    · intro hw
      change Problem520.harperPrimeRestriction y w.2 ∈
        harper1144LogBallotCubeEvent y start n w.1 at hw
      refine Set.mem_iUnion.2
        ⟨Problem520.harperPrimeRestriction y w.2, ?_⟩
      exact ⟨hw, rfl⟩
    · rintro hw
      obtain ⟨eta, heta⟩ := Set.mem_iUnion.1 hw
      change w.1 ∈ harper1144LogBallotHeightSection y start n eta ∧
        Problem520.harperPrimeRestriction y w.2 = eta at heta
      change Problem520.harperPrimeRestriction y w.2 ∈
        harper1144LogBallotCubeEvent y start n w.1
      rw [heta.2]
      exact heta.1
  rw [heq]
  exact MeasurableSet.iUnion fun eta ↦
    (measurableSet_harper1144LogBallotHeightSection
      y start n eta).prod
        ((measurableSet_singleton eta).preimage
          (Problem520.measurable_harperPrimeRestriction y))

theorem mem_harper1144LogBallotGraph_iff
    (y start n : Nat) (t : Real) (omega : Problem520.Omega) :
    (t, omega) ∈ harper1144LogBallotGraph y start n ↔
      Problem520.harperPrimeRestriction y omega ∈
        harper1144LogBallotCubeEvent y start n t := by
  rfl

/-- The exact two-height finite-cube mass associated with any measurable
section graph is integrable over the restricted height square. -/
theorem integrable_harperTwoHeightCubeMass_of_graph
    {y : Nat} {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G)
    (A : Real → Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t) :
    Integrable (fun ts : Real × Real ↦
        harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2))
      ((volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)) := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let F : Real × Problem520.Omega → Real := fun w ↦
    G.indicator
      (fun z : Real × Problem520.Omega ↦
        Problem520.harperEulerDensity y z.2 z.1) w
  let H : (Real × Real) × Problem520.Omega → Real := fun w ↦
    F (w.1.1, w.2) * F (w.1.2, w.2)
  have hfinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  letI : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 hfinite
  have hFmeas : Measurable F := by
    simpa only [F] using
      (Problem520.measurable_harperEulerDensity_joint y).indicator hG
  have hHmeas : Measurable H := by
    apply Measurable.mul
    · exact hFmeas.comp (by fun_prop)
    · exact hFmeas.comp (by fun_prop)
  let U : Real := Problem520.harperEulerDensityUniformBound y
  have hFbounds (w : Real × Problem520.Omega) :
      0 ≤ F w ∧ F w ≤ U := by
    by_cases hw : w ∈ G
    · simp only [F, Set.indicator_of_mem hw]
      exact ⟨Problem520.harperEulerDensity_nonneg y w.2 w.1,
        Problem520.harperEulerDensity_le_uniformBound y w.2 w.1⟩
    · simp [F, hw, U,
        Problem520.harperEulerDensityUniformBound_nonneg]
  have hH : Integrable H ((nu.prod nu).prod Problem520.μ) := by
    apply Integrable.of_bound hHmeas.aestronglyMeasurable (U ^ (2 : Nat))
    exact ae_of_all _ fun w ↦ by
      have hleft := hFbounds (w.1.1, w.2)
      have hright := hFbounds (w.1.2, w.2)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hleft.1 hright.1)]
      rw [pow_two]
      exact mul_le_mul hleft.2 hright.2 hright.1
        (Problem520.harperEulerDensityUniformBound_nonneg y)
  have hinner (ts : Real × Real) :
      (∫ omega, H (ts, omega) ∂Problem520.μ) =
        harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2) := by
    simpa only [H, F] using
      integral_graphIndicator_harperEulerDensity_mul_eq_twoHeightCubeMass
        A hsection ts.1 ts.2
  have hint := hH.integral_prod_left
  have hmass : Integrable (fun ts : Real × Real ↦
      harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2))
      (nu.prod nu) := hint.congr (ae_of_all (nu.prod nu) hinner)
  simpa only [nu] using hmass

/-- A nonnegative integrable function on the lower height square is bounded
by the sum of its terminal-strip and dyadic-shell integrals. -/
theorem integral_le_terminal_add_overlapShells
    (n : Nat) (f : Real × Real → Real)
    (hf : Integrable f
      ((volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)))
    (hfNonneg : ∀ ts, 0 ≤ f ts) :
    (∫ ts, f ts
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) ≤
      (∫ ts in harperTerminalNearDiagonalStrip n, f ts
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) +
        ∑ r ∈ Finset.range n,
          ∫ ts in harper1144OverlapShell r, f ts
            ∂(volume.restrict harperLowerVerticalBand).prod
              (volume.restrict harperLowerVerticalBand) := by
  let mu : Measure (Real × Real) :=
    (volume.restrict harperLowerVerticalBand).prod
      (volume.restrict harperLowerVerticalBand)
  let g : Real × Real → Real := fun ts ↦
    (harperTerminalNearDiagonalStrip n).indicator f ts +
      ∑ r ∈ Finset.range n, (harper1144OverlapShell r).indicator f ts
  have hterminalInt : Integrable
      ((harperTerminalNearDiagonalStrip n).indicator f) mu :=
    hf.indicator (measurableSet_harperTerminalNearDiagonalStrip n)
  have hshellInt (r : Nat) : Integrable
      ((harper1144OverlapShell r).indicator f) mu :=
    hf.indicator (measurableSet_harper1144OverlapShell r)
  have hsumInt : Integrable
      (fun ts ↦ ∑ r ∈ Finset.range n,
        (harper1144OverlapShell r).indicator f ts) mu :=
    integrable_finset_sum (Finset.range n) fun r _hr ↦ hshellInt r
  have hg : Integrable g mu := hterminalInt.add hsumInt
  have hband : ∀ᵐ ts ∂mu,
      ts ∈ harperLowerVerticalBand ×ˢ harperLowerVerticalBand := by
    rw [Measure.ae_prod_mem_iff_ae_ae_mem
      (measurableSet_harperLowerVerticalBand.prod
        measurableSet_harperLowerVerticalBand)]
    filter_upwards [ae_restrict_mem measurableSet_harperLowerVerticalBand]
      with t ht
    filter_upwards [ae_restrict_mem measurableSet_harperLowerVerticalBand]
      with s hs
    exact ⟨ht, hs⟩
  have hle : ∀ᵐ ts ∂mu, f ts ≤ g ts := by
    filter_upwards [hband] with ts hts
    rcases harperLowerVerticalBand_pair_terminal_or_overlapShell n hts with
        hterminal | ⟨r, hr, hshell⟩
    · have hsumNonneg : 0 ≤
          ∑ r ∈ Finset.range n,
            (harper1144OverlapShell r).indicator f ts := by
        exact Finset.sum_nonneg fun r _hr ↦
          Set.indicator_nonneg (fun z _hz ↦ hfNonneg z) ts
      simp only [g, Set.indicator_of_mem hterminal]
      linarith
    · have hrmem : r ∈ Finset.range n := Finset.mem_range.mpr hr
      have htermNonneg : 0 ≤
          (harperTerminalNearDiagonalStrip n).indicator f ts := by
        exact Set.indicator_nonneg (fun z _hz ↦ hfNonneg z) ts
      have hsingle : f ts ≤
          ∑ q ∈ Finset.range n,
            (harper1144OverlapShell q).indicator f ts := by
        calc
          f ts = (harper1144OverlapShell r).indicator f ts := by
            rw [Set.indicator_of_mem hshell]
          _ ≤ ∑ q ∈ Finset.range n,
              (harper1144OverlapShell q).indicator f ts := by
            exact Finset.single_le_sum
              (fun q hq ↦ Set.indicator_nonneg
                (fun z _hz ↦ hfNonneg z) ts) hrmem
      dsimp only [g]
      linarith
  have hmain := integral_mono_ae hf hg hle
  have hterminalEq :
      (∫ ts, (harperTerminalNearDiagonalStrip n).indicator f ts ∂mu) =
        ∫ ts in harperTerminalNearDiagonalStrip n, f ts ∂mu := by
    rw [integral_indicator (measurableSet_harperTerminalNearDiagonalStrip n)]
  have hshellEq (r : Nat) :
      (∫ ts, (harper1144OverlapShell r).indicator f ts ∂mu) =
        ∫ ts in harper1144OverlapShell r, f ts ∂mu := by
    rw [integral_indicator (measurableSet_harper1144OverlapShell r)]
  rw [show (∫ ts, g ts ∂mu) =
      (∫ ts, (harperTerminalNearDiagonalStrip n).indicator f ts ∂mu) +
        ∑ r ∈ Finset.range n,
          ∫ ts, (harper1144OverlapShell r).indicator f ts ∂mu by
    dsimp only [g]
    rw [integral_add hterminalInt hsumInt,
      integral_finset_sum (Finset.range n) (fun r _hr ↦ hshellInt r)]] at hmain
  simpa only [mu, hterminalEq, hshellEq] using hmain

/-! ## Economical maximal path -/

/-- The economical fixed-start path ends at the last completed scheduled
block below the ambient cutoff. -/
theorem harperEconomicalPathLength_fixedStart_envelope
    {y start : Nat}
    (hroom : start + 5 ≤ Problem520.harperAvailableLogScale y) :
    let n := Problem520.harperEconomicalPathLength y start 0
    0 < n ∧
      Problem520.harperBlockEndpoint (start + n) ≤ y ∧
      y < Problem520.harperBlockEndpoint (start + n + 1) := by
  dsimp only
  let n := Problem520.harperEconomicalPathLength y start 0
  have hyne : y ≠ 0 := by
    intro hy
    subst y
    simp [Problem520.harperAvailableLogScale] at hroom
  have hfit : Problem520.harperEconomicalStart start 0 + 4 ≤
      Problem520.harperAvailableLogScale y := by
    simp only [Problem520.harperEconomicalStart]
    omega
  have hn : 0 < n := by
    dsimp only [n]
    exact Problem520.harperEconomicalPathLength_pos hroom
  have hlower : Problem520.harperBlockEndpoint (start + n) ≤ y := by
    have h := Problem520.harperBlockEndpoint_economicalStart_add_le
      hyne hfit (m := n) le_rfl
    simpa only [Problem520.harperEconomicalStart, Nat.add_zero] using h
  have hexact : start + n + 4 =
      Problem520.harperAvailableLogScale y := by
    have h := Problem520.harperEconomicalStart_add_path_add_four_eq hfit
    simpa only [Problem520.harperEconomicalStart, Nat.add_zero, n] using h
  have hupper : y < Problem520.harperBlockEndpoint (start + n + 1) := by
    by_contra hnot
    have hendpoint : Problem520.harperBlockEndpoint (start + n + 1) ≤ y :=
      Nat.le_of_not_gt hnot
    have havail :=
      Problem520.add_four_le_harperAvailableLogScale_of_blockEndpoint_le
        hendpoint
    omega
  exact ⟨hn, hlower, hupper⟩

/-- Squaring the critical scale gives the reciprocal real log-log scale. -/
theorem harperInitialCriticalScale_sq_eq_inv
    {y : Nat} (hy : 4 ≤ y) :
    harperInitialCriticalScale y ^ (2 : Nat) =
      (1 + Problem520.logLogNat y)⁻¹ := by
  have hL : 0 < 1 + Problem520.logLogNat y :=
    Problem520.one_add_logLogNat_pos_of_four_le hy
  unfold harperInitialCriticalScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  have hexp : (-(1 : Real) / 2) * (2 : Nat) = -1 := by norm_num
  rw [hexp, Real.rpow_neg_one]

/-- The fixed-start one-height inverse-square-root estimate dominates the
critical log-log scale whenever the endpoint of the path lies below `y`. -/
theorem exists_harper1144LogBallotFixedStart_oneHeight_ge_criticalScale :
    ∃ delta > 0, ∃ J : Nat, ∀ start : Nat, J ≤ start →
      ∀ n y : Nat, 0 < n → 4 ≤ y →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            delta * harperInitialCriticalScale y ≤
              (Problem520.harperTiltedCubeLaw y t).real
                (harper1144LogBallotCubeEvent y start n t) := by
  obtain ⟨J, hone⟩ :=
    exists_harper1144LogBallotFixedStart_oneHeight_lower
  let a : Real := (3 / 16 : Real) *
    Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget)
  let delta : Real := a / 2
  refine ⟨delta, by dsimp only [delta, a]; positivity, J, ?_⟩
  intro start hstart n y hn hy4 hendpoint t ht
  let L : Real := 1 + Problem520.logLogNat y
  have hL : 0 < L := by
    dsimp only [L]
    exact Problem520.one_add_logLogNat_pos_of_four_le hy4
  have hindex := half_index_le_logLogNat_of_harperBlockEndpoint_le hendpoint
  have hnL : (n : Real) ≤ 4 * L := by
    push_cast at hindex
    have hstartR : 0 ≤ (start : Real) := by positivity
    have hnHalf : (n : Real) / 2 ≤ Problem520.logLogNat y := by
      nlinarith
    have hnR' : 0 < (n : Real) := by exact_mod_cast hn
    dsimp only [L]
    nlinarith
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : Real) ≤ 2 * Real.sqrt L := by
    calc
      Real.sqrt (n : Real) ≤ Real.sqrt (4 * L) :=
        Real.sqrt_le_sqrt hnL
      _ = 2 * Real.sqrt L := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
        norm_num
  have hinv : (2 * Real.sqrt L)⁻¹ ≤
      (Real.sqrt (n : Real))⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.sqrt_pos.2 hnR) hsqrt
  have hcritical : harperInitialCriticalScale y / 2 ≤
      (Real.sqrt (n : Real))⁻¹ := by
    have hrewrite : harperInitialCriticalScale y = (Real.sqrt L)⁻¹ := by
      unfold harperInitialCriticalScale
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hL.le]
      congr 2
      ring
    rw [hrewrite]
    have hsqrtL : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
    calc
      (Real.sqrt L)⁻¹ / 2 = (2 * Real.sqrt L)⁻¹ := by
        field_simp
      _ ≤ (Real.sqrt (n : Real))⁻¹ := hinv
  have hraw := hone start hstart n hn y hendpoint t ht
  calc
    delta * harperInitialCriticalScale y =
        a * (harperInitialCriticalScale y / 2) := by
      dsimp only [delta]
      ring
    _ ≤ a * (Real.sqrt (n : Real))⁻¹ := by
      gcongr
    _ = (3 / 16 : Real) *
          Real.exp (-2 - harper1144GaussianLogFenceCertificateBudget) /
            Real.sqrt (n : Real) := by
      dsimp only [a]
      rw [div_eq_mul_inv]
      ring
    _ ≤ (Problem520.harperTiltedCubeLaw y t).real
          (harper1144LogBallotCubeEvent y start n t) := hraw

/-! ## Full restricted second moment -/

/-- On the maximal fixed-start scheduled path, the complete logarithmic
ballot graph has the critical two-height mass.  The arbitrary final partial
prime block is absorbed by the independent-screen estimate. -/
theorem exists_harper1144LogBallot_economical_twoHeight_mass_le :
    ∃ J : Nat, ∀ start : Nat, J ≤ start →
      ∃ C > 0, ∃ Y : Nat, ∀ y : Nat, Y ≤ y → 4 ≤ y →
        let n := Problem520.harperEconomicalPathLength y start 0
        let A : Real → Set (Problem520.HarperPrimeCube y) := fun t ↦
          harper1144LogBallotCubeEvent y start n t
        (∫ ts,
            harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2)
            ∂(volume.restrict harperLowerVerticalBand).prod
              (volume.restrict harperLowerVerticalBand)) ≤
          ((C * harperInitialCriticalScale y) *
            Real.log (y : Real)) ^ (2 : Nat) := by
  obtain ⟨C₀, hC₀, J, hpartition⟩ :=
    exists_harper1144LogBallot_partitioned_integral_le_envelope
  refine ⟨J, ?_⟩
  intro start hstart
  let K : Real := Real.exp
    (1 - Real.log (Real.log 2) +
      2 * (Real.log 4 + 4) / Real.log 2)
  let B : Real := C₀ * (4 : Real) ^ start
  let C : Real := K * Real.sqrt (3 * B)
  let Y : Nat := Problem520.harperBlockEndpoint (2 * start + 20)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, Y, ?_⟩
  intro y hyY hy4
  dsimp only
  let n : Nat := Problem520.harperEconomicalPathLength y start 0
  let A : Real → Set (Problem520.HarperPrimeCube y) := fun t ↦
    harper1144LogBallotCubeEvent y start n t
  let G : Set (Real × Problem520.Omega) :=
    harper1144LogBallotGraph y start n
  let f : Real × Real → Real := fun ts ↦
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (A ts.1 ∩ A ts.2)
  let mass : Real × Real → Real := fun ts ↦
    harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2)
  let E : Real := Problem520.primeEnergyNormalizer y
  let L : Real := 1 + Problem520.logLogNat y
  have havail : 2 * start + 24 ≤
      Problem520.harperAvailableLogScale y := by
    have hendpoint :
        Problem520.harperBlockEndpoint (2 * start + 20) ≤ y :=
      hyY
    have h :=
      Problem520.add_four_le_harperAvailableLogScale_of_blockEndpoint_le
        hendpoint
    omega
  have hroom : start + 5 ≤ Problem520.harperAvailableLogScale y := by
    omega
  have hnEnvelope := harperEconomicalPathLength_fixedStart_envelope hroom
  change 0 < n ∧
      Problem520.harperBlockEndpoint (start + n) ≤ y ∧
      y < Problem520.harperBlockEndpoint (start + n + 1) at hnEnvelope
  rcases hnEnvelope with ⟨hn, hnLower, hnUpper⟩
  have hnLarge : 10 ≤ n := by
    have hfit : Problem520.harperEconomicalStart start 0 + 4 ≤
        Problem520.harperAvailableLogScale y := by
      simp only [Problem520.harperEconomicalStart, Nat.add_zero]
      omega
    have hexact :=
      Problem520.harperEconomicalStart_add_path_add_four_eq hfit
    simp only [Problem520.harperEconomicalStart, Nat.add_zero, n] at hexact
    omega
  have hhalf : start + 0 ≤
      Problem520.harperAvailableLogScale y / 2 := by omega
  have hscale :=
    Problem520.one_add_logLogNat_le_two_mul_economicalPathLength_add_ten
      (y := y) (J := start) (h := 0) (by omega) hhalf
  change L ≤ 2 * (n : Real) + 10 at hscale
  have hscaleThree : L ≤ 3 * (n : Real) := by
    have hnLargeR : (10 : Real) ≤ (n : Real) := by exact_mod_cast hnLarge
    linarith
  have hL : 0 < L := by
    dsimp only [L]
    exact Problem520.one_add_logLogNat_pos_of_four_le hy4
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  have hinvScale : (n : Real)⁻¹ ≤ 3 * L⁻¹ := by
    have hrecip : (3 * (n : Real))⁻¹ ≤ L⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le hL hscaleThree
    have hnNe : (n : Real) ≠ 0 := hnR.ne'
    calc
      (n : Real)⁻¹ = 3 * (3 * (n : Real))⁻¹ := by
        field_simp
      _ ≤ 3 * L⁻¹ := by gcongr
  have hG : MeasurableSet G := by
    simpa only [G] using measurableSet_harper1144LogBallotGraph y start n
  have hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t := by
    intro t omega
    rfl
  have hmassInt : Integrable mass
      ((volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)) := by
    simpa only [mass] using
      integrable_harperTwoHeightCubeMass_of_graph hG A hsection
  have hE : 0 < E := by
    dsimp only [E]
    exact Problem520.primeEnergyNormalizer_pos y
  have hmassEq (ts : Real × Real) : mass ts = E ^ (2 : Nat) * f ts := by
    dsimp only [mass, f, E]
    rw [harperTwoHeightCubeMass_eq_normalizer_mul_probability,
      harperTwoHeightNormalizer_eq_energy_sq_mul_correlation]
    ring
  have hfInt : Integrable f
      ((volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)) := by
    have hscaled := hmassInt.const_mul (E ^ (2 : Nat))⁻¹
    apply hscaled.congr
    exact ae_of_all _ fun ts ↦ by
      change (E ^ (2 : Nat))⁻¹ * mass ts = f ts
      rw [hmassEq]
      field_simp [hE.ne']
  have hfNonneg (ts : Real × Real) : 0 ≤ f ts := by
    dsimp only [f]
    exact mul_nonneg (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      measureReal_nonneg
  have hfCover := integral_le_terminal_add_overlapShells n f hfInt hfNonneg
  have hfPartition := hpartition start hstart n y hn hnLower hnUpper
  have hfFull :
      (∫ ts, f ts
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) ≤
        B * (n : Real)⁻¹ := by
    exact hfCover.trans (by simpa only [f, A, B] using hfPartition)
  have henergy : E ≤ K * Real.log (y : Real) := by
    simpa only [E, K] using
      Problem520.primeEnergyNormalizer_le_mertensConstant_mul_log
        (show 2 ≤ y by omega)
  have hlog : 0 < Real.log (y : Real) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hcriticalSq := harperInitialCriticalScale_sq_eq_inv hy4
  have hCformula : C ^ (2 : Nat) = K ^ (2 : Nat) * (3 * B) := by
    dsimp only [C]
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 3 * B)]
  calc
    (∫ ts,
        harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2)
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) =
        ∫ ts, mass ts
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand) := by rfl
    _ = E ^ (2 : Nat) *
        ∫ ts, f ts
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ hmassEq
    _ ≤ E ^ (2 : Nat) * (B * (n : Real)⁻¹) := by
      gcongr
    _ ≤ (K * Real.log (y : Real)) ^ (2 : Nat) *
          (B * (3 * L⁻¹)) := by
      have henergySq : E ^ (2 : Nat) ≤
          (K * Real.log (y : Real)) ^ (2 : Nat) := by
        gcongr
      exact mul_le_mul henergySq (mul_le_mul_of_nonneg_left hinvScale hB.le)
        (mul_nonneg hB.le (inv_nonneg.2 hnR.le))
        (sq_nonneg (K * Real.log (y : Real)))
    _ = ((C * harperInitialCriticalScale y) *
          Real.log (y : Real)) ^ (2 : Nat) := by
      have hLcritical : L⁻¹ =
          harperInitialCriticalScale y ^ (2 : Nat) := by
        simpa only [L] using hcriticalSq.symm
      rw [hLcritical]
      calc
        (K * Real.log (y : Real)) ^ (2 : Nat) *
              (B * (3 * harperInitialCriticalScale y ^ (2 : Nat))) =
            (K ^ (2 : Nat) * (3 * B)) *
              harperInitialCriticalScale y ^ (2 : Nat) *
                Real.log (y : Real) ^ (2 : Nat) := by ring
        _ = C ^ (2 : Nat) *
              harperInitialCriticalScale y ^ (2 : Nat) *
                Real.log (y : Real) ^ (2 : Nat) := by rw [← hCformula]
        _ = ((C * harperInitialCriticalScale y) *
              Real.log (y : Real)) ^ (2 : Nat) := by ring

/-! ## Public certificate endpoints -/

/-- The pinched fixed-start graph supplies the complete one-height/two-height
ballot certificate with no analytic hypotheses. -/
theorem harperRestrictedTwoHeightBallotStatement_unconditional :
    HarperRestrictedTwoHeightBallotStatement := by
  obtain ⟨delta, hdelta, Jone, hone⟩ :=
    exists_harper1144LogBallotFixedStart_oneHeight_ge_criticalScale
  obtain ⟨Jtwo, htwo⟩ :=
    exists_harper1144LogBallot_economical_twoHeight_mass_le
  let start : Nat := max Jone Jtwo
  obtain ⟨C, hC, Ytwo, hmass⟩ :=
    htwo start (by dsimp only [start]; exact le_max_right _ _)
  let Yroom : Nat := Problem520.harperBlockEndpoint (2 * start + 20)
  let Y : Nat := max Ytwo Yroom
  refine ⟨delta, C, hdelta, hC, Y, ?_⟩
  intro y hyY hy4
  have hyTwo : Ytwo ≤ y :=
    (le_max_left Ytwo Yroom).trans hyY
  have hyRoom : Yroom ≤ y :=
    (le_max_right Ytwo Yroom).trans hyY
  let n : Nat := Problem520.harperEconomicalPathLength y start 0
  let G : Set (Real × Problem520.Omega) :=
    harper1144LogBallotGraph y start n
  let A : Real → Set (Problem520.HarperPrimeCube y) := fun t ↦
    harper1144LogBallotCubeEvent y start n t
  have havail : 2 * start + 24 ≤
      Problem520.harperAvailableLogScale y := by
    have hendpoint :
        Problem520.harperBlockEndpoint (2 * start + 20) ≤ y :=
      hyRoom
    have h :=
      Problem520.add_four_le_harperAvailableLogScale_of_blockEndpoint_le
        hendpoint
    omega
  have hroom : start + 5 ≤
      Problem520.harperAvailableLogScale y := by omega
  have hnEnvelope := harperEconomicalPathLength_fixedStart_envelope hroom
  change 0 < n ∧
      Problem520.harperBlockEndpoint (start + n) ≤ y ∧
      y < Problem520.harperBlockEndpoint (start + n + 1) at hnEnvelope
  rcases hnEnvelope with ⟨hn, hnLower, _hnUpper⟩
  refine ⟨G, A, ?_, ?_, ?_, ?_⟩
  · simpa only [G] using
      measurableSet_harper1144LogBallotGraph y start n
  · intro t omega
    rfl
  · intro t ht
    have hstartOne : Jone ≤ start := by
      dsimp only [start]
      exact le_max_left _ _
    simpa only [A] using
      hone start hstartOne n y hn hy4 hnLower t ht
  · simpa only [A, n] using hmass y hyTwo hy4

/-- The formerly missing initial half-moment lower bound follows
unconditionally from the completed logarithmic-ballot certificate. -/
theorem harperRademacherInitialHalfMomentLowerStatement_unconditional :
    HarperRademacherInitialHalfMomentLowerStatement :=
  harperRademacherInitialHalfMomentLowerStatement_of_twoHeightBallot
    harperRestrictedTwoHeightBallotStatement_unconditional

/-- The completed pinched-ballot estimate, combined with the already
unconditional upper `2/3` moment, gives a scale-uniform positive probability
of critical Harper energy. -/
theorem exists_harperInitialCriticalEnergy_fixedProbability_unconditional :
    ∃ delta : ℝ, 0 < delta ∧ ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ y : ℕ,
      Y ≤ y →
      delta ≤ Problem520.μ.real
        (halfMomentLargeEvent
          (Problem520.harperInitialNormalizedEnergy y)
          (c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2))) :=
  exists_harperInitialCriticalEnergy_fixedProbability
    harperRademacherInitialHalfMomentLowerStatement_unconditional

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.measurableSet_harper1144LogBallotGraph
#print axioms Erdos.Problem1144.integrable_harperTwoHeightCubeMass_of_graph
#print axioms Erdos.Problem1144.integral_le_terminal_add_overlapShells
#print axioms Erdos.Problem1144.exists_harper1144LogBallotFixedStart_oneHeight_ge_criticalScale
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_economical_twoHeight_mass_le
#print axioms Erdos.Problem1144.harperRestrictedTwoHeightBallotStatement_unconditional
#print axioms Erdos.Problem1144.harperRademacherInitialHalfMomentLowerStatement_unconditional
#print axioms Erdos.Problem1144.exists_harperInitialCriticalEnergy_fixedProbability_unconditional
