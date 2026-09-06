import Erdos.Problem1144.HarperRankinRestrictedGraph

open MeasureTheory Set
open scoped ENNReal

namespace Erdos.Problem1144

theorem candidate_rankinRestrictedGraphEnergy_le_uniformBound
    {y : Nat} (hy : 1 < y) (a : ℝ) {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G) (omega : Problem520.Omega) :
    harperRankinRestrictedGraphEnergy y a G omega <=
      harperRankinEulerDensityUniformBound y a / Real.log (y : Real) := by
  let restricted : Real -> Real := fun t =>
    G.indicator
      (fun w : Real × Problem520.Omega =>
        harperRankinEulerDensity y a w.2 w.1) (t, omega)
  let U : Real := harperRankinEulerDensityUniformBound y a
  have hrestricted : IntegrableOn restricted harperLowerVerticalBand := by
    simpa only [restricted] using
      integrableOn_harperRankinRestrictedGraphDensity y a hG omega
  have hfinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  have hconst : IntegrableOn (fun _t : Real => U) harperLowerVerticalBand :=
    integrableOn_const hfinite
  have hpoint (t : Real) (_ht : t ∈ harperLowerVerticalBand) :
      restricted t <= U := by
    by_cases hmem : (t, omega) ∈ G
    · simpa only [restricted, Set.indicator_of_mem hmem, U] using
        harperRankinEulerDensity_le_uniformBound y a omega t
    · simp [restricted, hmem, U,
        harperRankinEulerDensityUniformBound_nonneg]
  have hint :
      (∫ t in harperLowerVerticalBand, restricted t) <=
        ∫ _t in harperLowerVerticalBand, U :=
    setIntegral_mono_on hrestricted hconst
      measurableSet_harperLowerVerticalBand hpoint
  have hvolume : volume.real harperLowerVerticalBand <= 1 := by
    norm_num [harperLowerVerticalBand, Measure.real, Real.volume_Icc]
  have hU : 0 <= U :=
    harperRankinEulerDensityUniformBound_nonneg y a
  have hnum : (∫ t in harperLowerVerticalBand, restricted t) <= U := by
    calc
      (∫ t in harperLowerVerticalBand, restricted t) <=
          ∫ _t in harperLowerVerticalBand, U := hint
      _ = volume.real harperLowerVerticalBand * U := by simp
      _ <= 1 * U := mul_le_mul_of_nonneg_right hvolume hU
      _ = U := one_mul U
  have hlog : 0 <= Real.log (y : Real) :=
    (Real.log_pos (by exact_mod_cast hy)).le
  unfold harperRankinRestrictedGraphEnergy
  change ((4 / 5 : ℝ) * (∫ t in harperLowerVerticalBand, restricted t)) /
      Real.log (y : Real) <= U / Real.log (y : Real)
  apply div_le_div_of_nonneg_right _ hlog
  calc
    (4 / 5 : ℝ) * (∫ t in harperLowerVerticalBand, restricted t) ≤ (4 / 5 : ℝ) * U :=
      mul_le_mul_of_nonneg_left hnum (by norm_num)
    _ ≤ U := by linarith

/-- At every finite prime cutoff the restricted energy has an integrable
square.  This is a soft boundedness fact, not part of the deep second-moment
estimate. -/
theorem candidate_integrable_sq_rankinRestrictedGraphEnergy
    {y : Nat} (hy : 1 < y) (a : ℝ) {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G) :
    Integrable (fun omega =>
      harperRankinRestrictedGraphEnergy y a G omega ^ (2 : Nat)) Problem520.μ := by
  let C : Real :=
    harperRankinEulerDensityUniformBound y a / Real.log (y : Real)
  have hRint := integrable_harperRankinRestrictedGraphEnergy (y := y) a hG
  apply Integrable.of_bound (hRint.aestronglyMeasurable.pow 2) (C ^ 2)
  exact ae_of_all Problem520.μ fun omega => by
    have hnonneg := harperRankinRestrictedGraphEnergy_nonneg hy a G omega
    have hle : harperRankinRestrictedGraphEnergy y a G omega <= C := by
      simpa only [C] using
        candidate_rankinRestrictedGraphEnergy_le_uniformBound hy a hG omega
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ hnonneg hle 2

end Erdos.Problem1144
