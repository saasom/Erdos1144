import Erdos.Problem1144.HarperTerminalComplementCorrelation

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The terminal-capped near-diagonal strip

The two tilted paths are most strongly correlated when their heights differ
by at most the reciprocal terminal frequency.  The strengthened terminal cap
handles exactly this region: its pointwise `2^n / n` cost is integrated over
a strip of width `2^-n`, leaving the sharp `1 / n` contribution.
-/

/-- A symmetric strip of radius `delta` around the diagonal in height space. -/
def harperNearDiagonalStrip (delta : Real) : Set (Real × Real) :=
  {ts | |ts.1 - ts.2| <= delta}

theorem measurableSet_harperNearDiagonalStrip (delta : Real) :
    MeasurableSet (harperNearDiagonalStrip delta) := by
  exact measurableSet_le
    ((measurable_fst.sub measurable_snd).abs) measurable_const

/-- A strip of radius `delta` has product measure at most its full vertical
width `2 * delta` times the measure of the first-coordinate set. -/
theorem measureReal_restrict_prod_harperNearDiagonalStrip_le
    (I : Set Real) (hI : volume I ≠ ∞)
    {delta : Real} (hdelta : 0 ≤ delta) :
    ((volume.restrict I).prod (volume.restrict I)).real
        (harperNearDiagonalStrip delta) ≤
      2 * delta * (volume.restrict I).real Set.univ := by
  let nu : Measure Real := volume.restrict I
  let strip := harperNearDiagonalStrip delta
  have hstrip : MeasurableSet strip :=
    measurableSet_harperNearDiagonalStrip delta
  have hsection (t : Real) :
      Prod.mk t ⁻¹' strip = Set.Icc (t - delta) (t + delta) := by
    ext s
    simp only [strip, harperNearDiagonalStrip, Set.mem_preimage,
      Set.mem_setOf_eq, Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨l, r⟩
      constructor <;> linarith
    · rintro ⟨l, r⟩
      constructor <;> linarith
  have hsectionMeasure (t : Real) :
      nu (Prod.mk t ⁻¹' strip) ≤ ENNReal.ofReal (2 * delta) := by
    rw [hsection]
    calc
      nu (Set.Icc (t - delta) (t + delta)) ≤
          volume (Set.Icc (t - delta) (t + delta)) :=
        Measure.restrict_le_self
          (Set.Icc (t - delta) (t + delta))
      _ = ENNReal.ofReal (2 * delta) := by
        rw [Real.volume_Icc]
        congr 1
        ring
  have hmeasure :
      nu.prod nu strip ≤ ENNReal.ofReal (2 * delta) * nu Set.univ := by
    rw [Measure.prod_apply hstrip]
    calc
      (∫⁻ t, nu (Prod.mk t ⁻¹' strip) ∂nu) ≤
          ∫⁻ _t, ENNReal.ofReal (2 * delta) ∂nu := by
        exact lintegral_mono fun t => hsectionMeasure t
      _ = ENNReal.ofReal (2 * delta) * nu Set.univ :=
        lintegral_const _
  have hnuFinite : nu Set.univ ≠ ∞ := by
    have hle : nu Set.univ ≤ volume I := by
      simp only [nu, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter]
      exact le_rfl
    exact ne_top_of_le_ne_top hI hle
  have hrightFinite :
      ENNReal.ofReal (2 * delta) * nu Set.univ ≠ ∞ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hnuFinite
  have hleftFinite : nu.prod nu strip ≠ ∞ :=
    ne_top_of_le_ne_top hrightFinite hmeasure
  have hreal := ENNReal.toReal_le_toReal hleftFinite hrightFinite |>.mpr hmeasure
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hdelta)] at hreal
  simpa only [Measure.real, nu, strip] using hreal

/-- The concrete reciprocal-frequency strip for a path of length `n`. -/
def harperTerminalNearDiagonalStrip (n : Nat) : Set (Real × Real) :=
  harperNearDiagonalStrip (((2 : Real) ^ n)⁻¹)

theorem measurableSet_harperTerminalNearDiagonalStrip (n : Nat) :
    MeasurableSet (harperTerminalNearDiagonalStrip n) :=
  measurableSet_harperNearDiagonalStrip _

/-- The lower vertical band has length `1/6`, so the concrete strip has
product measure at most `(1/3) * 2^-n`. -/
theorem measureReal_harperTerminalNearDiagonalStrip_le (n : Nat) :
    ((volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)).real
          (harperTerminalNearDiagonalStrip n) ≤
      (1 / 3 : Real) * (((2 : Real) ^ n)⁻¹) := by
  have hbandFinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  have hbase := measureReal_restrict_prod_harperNearDiagonalStrip_le
    harperLowerVerticalBand hbandFinite
      (show 0 ≤ (((2 : Real) ^ n)⁻¹) by positivity)
  have hbandReal :
      (volume.restrict harperLowerVerticalBand).real Set.univ =
        (1 / 6 : Real) := by
    rw [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter]
    simp [harperLowerVerticalBand, Measure.real, Real.volume_Icc]
    norm_num
  rw [hbandReal] at hbase
  change
    ((volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)).real
          (harperNearDiagonalStrip (((2 : Real) ^ n)⁻¹)) ≤
      (1 / 3 : Real) * (((2 : Real) ^ n)⁻¹)
  calc
    _ ≤ 2 * (((2 : Real) ^ n)⁻¹) * (1 / 6 : Real) := hbase
    _ = (1 / 3 : Real) * (((2 : Real) ^ n)⁻¹) := by ring

/-! ## Integrated near-diagonal estimate -/

/-- Any nonnegative two-height integrand bounded by `C * 2^n / n` on the
lower vertical band contributes at most `(C / 3) / n` on the reciprocal
terminal-frequency strip.  This isolates the geometric cancellation from
the particular ballot event used downstream. -/
theorem integral_harperTerminalNearDiagonalStrip_le_of_bound
    (n : Nat) (hn : 0 < n) (f : Real × Real → Real)
    (C : Real) (hC : 0 ≤ C)
    (hfNonneg : ∀ ts, 0 ≤ f ts)
    (hfBound : ∀ ts,
      ts.1 ∈ harperLowerVerticalBand →
      ts.2 ∈ harperLowerVerticalBand →
        f ts ≤ C * (2 : Real) ^ n * (n : Real)⁻¹) :
    (∫ ts in harperTerminalNearDiagonalStrip n, f ts
      ∂( volume.restrict harperLowerVerticalBand).prod
        (volume.restrict harperLowerVerticalBand)) ≤
      (C / 3) * (n : Real)⁻¹ := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let mu : Measure (Real × Real) := nu.prod nu
  let strip := harperTerminalNearDiagonalStrip n
  let M : Real := C * (2 : Real) ^ n * (n : Real)⁻¹
  have hbandFinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  letI : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 hbandFinite
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
  have hstripFinite : mu strip < ∞ := measure_lt_top mu strip
  have hnorm :
      ‖∫ ts in strip, f ts ∂mu‖ ≤ M * mu.real strip := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hstripFinite
    filter_upwards [hband] with ts hts
    intro _hstrip
    rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg ts)]
    exact hfBound ts hts.1 hts.2
  have hstripMeasure :
      mu.real strip ≤ (1 / 3 : Real) * (((2 : Real) ^ n)⁻¹) := by
    simpa only [mu, nu, strip] using
      measureReal_harperTerminalNearDiagonalStrip_le n
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  change (∫ ts in strip, f ts ∂mu) ≤ (C / 3) * (n : Real)⁻¹
  calc
    (∫ ts in strip, f ts ∂mu) ≤
        ‖∫ ts in strip, f ts ∂mu‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ M * mu.real strip := hnorm
    _ ≤ M * ((1 / 3 : Real) * (((2 : Real) ^ n)⁻¹)) :=
      mul_le_mul_of_nonneg_left hstripMeasure hM
    _ = (C / 3) * (n : Real)⁻¹ := by
      dsimp only [M]
      have hpow : (2 : Real) ^ n ≠ 0 := by positivity
      rw [mul_assoc C, mul_assoc C,
        show (2 : Real) ^ n * (n : Real)⁻¹ *
            ((1 / 3 : Real) * ((2 : Real) ^ n)⁻¹) =
          (1 / 3 : Real) * (n : Real)⁻¹ by
            field_simp]
      ring

/-- On the canonical guarded schedule, the complete terminal-capped
two-height integrand contributes only `O(1 / n)` on the reciprocal-frequency
diagonal strip.  This is the exact cancellation

`(2^n / n) * 2^-n = 1 / n`.
-/
theorem exists_harperTerminalGuarded_nearDiagonal_integral_le :
    ∃ C > 0, ∃ J : Nat, ∀ n : Nat, 0 < n →
      let start := harperTerminalGuardStart J n
      let y := Problem520.harperBlockEndpoint (start + n)
      (∫ ts in harperTerminalNearDiagonalStrip n,
          harperTwoHeightCorrelation y ts.1 ts.2 *
            (harperTwoHeightCubeLaw y ts.1 ts.2).real
              (harperTerminalCappedCentralLowerBallotCubeEvent
                    y start n ts.1 ∩
                harperTerminalCappedCentralLowerBallotCubeEvent
                    y start n ts.2)
        ∂( volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) ≤
        C * (n : Real)⁻¹ := by
  obtain ⟨C₀, hC₀, J, hupper⟩ :=
    exists_harperTerminalGuarded_twoHeight_upper
  refine ⟨C₀ / 3, div_pos hC₀ (by norm_num), J, ?_⟩
  intro n hn
  dsimp only
  let start := harperTerminalGuardStart J n
  let y := Problem520.harperBlockEndpoint (start + n)
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let mu : Measure (Real × Real) := nu.prod nu
  let strip := harperTerminalNearDiagonalStrip n
  let f : Real × Real → Real := fun ts ↦
    harperTwoHeightCorrelation y ts.1 ts.2 *
      (harperTwoHeightCubeLaw y ts.1 ts.2).real
        (harperTerminalCappedCentralLowerBallotCubeEvent y start n ts.1 ∩
          harperTerminalCappedCentralLowerBallotCubeEvent y start n ts.2)
  let M : Real := C₀ * (2 : Real) ^ n * (n : Real)⁻¹
  have hbandFinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  letI : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 hbandFinite
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
  have hfNonneg (ts : Real × Real) : 0 ≤ f ts := by
    exact mul_nonneg (harperTwoHeightCorrelation_pos y ts.1 ts.2).le
      measureReal_nonneg
  have hfBound (ts : Real × Real)
      (ht : ts.1 ∈ harperLowerVerticalBand)
      (hs : ts.2 ∈ harperLowerVerticalBand) :
      f ts ≤ M := by
    simpa only [f, M, start, y] using
      hupper n hn ts.1 ht ts.2 hs
  have hstripFinite : mu strip < ∞ := measure_lt_top mu strip
  have hnorm :
      ‖∫ ts in strip, f ts ∂mu‖ ≤ M * mu.real strip := by
    apply norm_setIntegral_le_of_norm_le_const_ae' hstripFinite
    filter_upwards [hband] with ts hts
    intro _hstrip
    rw [Real.norm_eq_abs, abs_of_nonneg (hfNonneg ts)]
    exact hfBound ts hts.1 hts.2
  have hstripMeasure :
      mu.real strip ≤ (1 / 3 : Real) * (((2 : Real) ^ n)⁻¹) := by
    simpa only [mu, nu, strip] using
      measureReal_harperTerminalNearDiagonalStrip_le n
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  change (∫ ts in strip, f ts ∂mu) ≤ (C₀ / 3) * (n : Real)⁻¹
  calc
    (∫ ts in strip, f ts ∂mu) ≤
        ‖∫ ts in strip, f ts ∂mu‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ M * mu.real strip := hnorm
    _ ≤ M * ((1 / 3 : Real) * (((2 : Real) ^ n)⁻¹)) :=
      mul_le_mul_of_nonneg_left hstripMeasure hM
    _ = (C₀ / 3) * (n : Real)⁻¹ := by
      dsimp only [M]
      have hpow : (2 : Real) ^ n ≠ 0 := by positivity
      rw [mul_assoc C₀, mul_assoc C₀,
        show (2 : Real) ^ n * (n : Real)⁻¹ *
            ((1 / 3 : Real) * ((2 : Real) ^ n)⁻¹) =
          (1 / 3 : Real) * (n : Real)⁻¹ by
            field_simp]
      ring

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.measureReal_harperTerminalNearDiagonalStrip_le
#print axioms Erdos.Problem1144.integral_harperTerminalNearDiagonalStrip_le_of_bound
#print axioms Erdos.Problem1144.exists_harperTerminalGuarded_nearDiagonal_integral_le
