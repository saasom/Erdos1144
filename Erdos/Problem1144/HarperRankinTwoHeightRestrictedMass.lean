import Erdos.Problem1144.HarperRankinRestrictedGraph

open MeasureTheory Set
open scoped ENNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Exact two-height mass for the Rankin-shifted restricted energy

This file identifies the square of the shifted restricted graph energy with
one explicit finite-cube two-height mass.  It contains no estimate: the only
remaining analytic job is to bound this mass for the logarithmic-ballot
sections constructed in `HarperRankinRestrictedGraph`.
-/

/-- The unnormalized product of the shifted Euler densities at two heights,
restricted to a finite-cube event. -/
noncomputable def harperRankinTwoHeightCubeMass
    (y : ℕ) (a t s : ℝ) (A : Set (Problem520.HarperPrimeCube y)) : ℝ :=
  ∫ eta in A,
    harperRankinCubeDensity y a t eta *
      harperRankinCubeDensity y a s eta
    ∂Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦ Problem520.coin)

theorem harperRankinTwoHeightCubeMass_nonneg
    (y : ℕ) (a t s : ℝ)
    (A : Set (Problem520.HarperPrimeCube y)) :
    0 ≤ harperRankinTwoHeightCubeMass y a t s A := by
  unfold harperRankinTwoHeightCubeMass
  exact setIntegral_nonneg (Set.toFinite A).measurableSet fun eta _heta ↦
    mul_nonneg
      (by
        unfold harperRankinCubeDensity harperRankinCoordinateFactor
        exact Finset.prod_nonneg fun p _hp ↦
          harperRankinEulerFactor_nonneg (fun _ ↦ eta p) p.1 a t)
      (by
        unfold harperRankinCubeDensity harperRankinCoordinateFactor
        exact Finset.prod_nonneg fun p _hp ↦
          harperRankinEulerFactor_nonneg (fun _ ↦ eta p) p.1 a s)

/-- Pull the shifted two-height mass back to the infinite Rademacher space. -/
theorem integral_harperRankinEulerDensity_mul_restrict_eq_twoHeightCubeMass
    (y : ℕ) (a t s : ℝ)
    (A : Set (Problem520.HarperPrimeCube y)) :
    (∫ omega in Problem520.harperPrimeRestriction y ⁻¹' A,
        harperRankinEulerDensity y a omega t *
          harperRankinEulerDensity y a omega s ∂Problem520.μ) =
      harperRankinTwoHeightCubeMass y a t s A := by
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have hpre : MeasurableSet
      (Problem520.harperPrimeRestriction y ⁻¹' A) :=
    hA.preimage (Problem520.measurable_harperPrimeRestriction y)
  rw [← integral_indicator hpre, harperRankinTwoHeightCubeMass,
    ← integral_indicator hA]
  rw [← Problem520.integral_comp_harperPrimeRestriction_mu y
    (fun eta ↦ A.indicator (fun eta ↦
      harperRankinCubeDensity y a t eta *
        harperRankinCubeDensity y a s eta) eta)]
  apply integral_congr_ae
  exact ae_of_all Problem520.μ fun omega ↦ by
    by_cases hmem : Problem520.harperPrimeRestriction y omega ∈ A
    · have hpreMem : omega ∈
          Problem520.harperPrimeRestriction y ⁻¹' A := hmem
      simp only [Set.indicator_of_mem hmem,
        Set.indicator_of_mem hpreMem]
      rw [harperRankinCubeDensity_harperPrimeRestriction,
        harperRankinCubeDensity_harperPrimeRestriction]
    · have hpreNot : omega ∉
          Problem520.harperPrimeRestriction y ⁻¹' A := hmem
      simp [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem hpreNot]

/-- On a graph with finite-cube sections, the product of the two retained
shifted densities is exactly the mass of the intersection section. -/
theorem integral_graphIndicator_harperRankinEulerDensity_mul_eq_twoHeightCubeMass
    {y : ℕ} {a : ℝ} {G : Set (ℝ × Problem520.Omega)}
    (A : ℝ → Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t)
    (t s : ℝ) :
    (∫ omega,
        G.indicator
            (fun w : ℝ × Problem520.Omega ↦
              harperRankinEulerDensity y a w.2 w.1) (t, omega) *
          G.indicator
            (fun w : ℝ × Problem520.Omega ↦
              harperRankinEulerDensity y a w.2 w.1) (s, omega)
        ∂Problem520.μ) =
      harperRankinTwoHeightCubeMass y a t s (A t ∩ A s) := by
  have hAt : MeasurableSet (A t) := (Set.toFinite (A t)).measurableSet
  have hAs : MeasurableSet (A s) := (Set.toFinite (A s)).measurableSet
  have hpre : MeasurableSet
      (Problem520.harperPrimeRestriction y ⁻¹' (A t ∩ A s)) :=
    (hAt.inter hAs).preimage
      (Problem520.measurable_harperPrimeRestriction y)
  rw [← integral_harperRankinEulerDensity_mul_restrict_eq_twoHeightCubeMass]
  rw [← integral_indicator hpre]
  apply integral_congr_ae
  exact ae_of_all Problem520.μ fun omega ↦ by
    by_cases ht : (t, omega) ∈ G
    · have htA := (hsection t omega).1 ht
      by_cases hs : (s, omega) ∈ G
      · have hsA := (hsection s omega).1 hs
        simp [ht, hs, htA, hsA]
      · have hsA : Problem520.harperPrimeRestriction y omega ∉ A s := by
          exact fun h ↦ hs ((hsection s omega).2 h)
        simp [ht, hs, hsA]
    · have htA : Problem520.harperPrimeRestriction y omega ∉ A t := by
        exact fun h ↦ ht ((hsection t omega).2 h)
      simp [ht, htA]

/-! ## Exact shifted second moment -/

/-- The square of the shifted restricted energy is the double vertical
integral of the shifted two-height mass, with the visible `(4/5)^2` Parseval
scaling. -/
theorem integral_sq_harperRankinRestrictedGraphEnergy_eq_twoHeightCubeMass
    {y : ℕ} {a : ℝ} {G : Set (ℝ × Problem520.Omega)}
    (hG : MeasurableSet G)
    (A : ℝ → Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t) :
    (∫ omega,
        harperRankinRestrictedGraphEnergy y a G omega ^ (2 : ℕ)
          ∂Problem520.μ) =
      (16 / 25 : ℝ) *
        (∫ ts,
          harperRankinTwoHeightCubeMass y a ts.1 ts.2 (A ts.1 ∩ A ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) /
        Real.log (y : ℝ) ^ (2 : ℕ) := by
  let nu : Measure ℝ := volume.restrict harperLowerVerticalBand
  let F : ℝ × Problem520.Omega → ℝ := fun w ↦
    G.indicator
      (fun z : ℝ × Problem520.Omega ↦
        harperRankinEulerDensity y a z.2 z.1) w
  let H : (ℝ × ℝ) × Problem520.Omega → ℝ := fun w ↦
    F (w.1.1, w.2) * F (w.1.2, w.2)
  have hfinite : volume harperLowerVerticalBand ≠ ∞ := by
    simp [harperLowerVerticalBand, Real.volume_Icc]
  letI : IsFiniteMeasure nu := isFiniteMeasure_restrict.2 hfinite
  have hFmeas : Measurable F := by
    simpa only [F] using
      (measurable_harperRankinEulerDensity_joint y a).indicator hG
  have hHmeas : Measurable H := by
    apply Measurable.mul
    · exact hFmeas.comp (by fun_prop)
    · exact hFmeas.comp (by fun_prop)
  let U : ℝ := harperRankinEulerDensityUniformBound y a
  have hFbounds (w : ℝ × Problem520.Omega) :
      0 ≤ F w ∧ F w ≤ U := by
    by_cases hw : w ∈ G
    · simp only [F, Set.indicator_of_mem hw]
      exact ⟨harperRankinEulerDensity_nonneg y a w.2 w.1,
        harperRankinEulerDensity_le_uniformBound y a w.2 w.1⟩
    · simp [F, hw, U, harperRankinEulerDensityUniformBound_nonneg]
  have hH : Integrable H ((nu.prod nu).prod Problem520.μ) := by
    apply Integrable.of_bound hHmeas.aestronglyMeasurable (U ^ (2 : ℕ))
    exact ae_of_all _ fun w ↦ by
      have hleft := hFbounds (w.1.1, w.2)
      have hright := hFbounds (w.1.2, w.2)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hleft.1 hright.1)]
      rw [pow_two]
      exact mul_le_mul hleft.2 hright.2 hright.1
        (harperRankinEulerDensityUniformBound_nonneg y a)
  have hsquare (omega : Problem520.Omega) :
      (∫ t, F (t, omega) ∂nu) ^ (2 : ℕ) =
        ∫ ts, H (ts, omega) ∂nu.prod nu := by
    have hFt : Integrable (fun t ↦ F (t, omega)) nu := by
      simpa only [F, nu] using
        integrableOn_harperRankinRestrictedGraphDensity y a hG omega
    have hprod : Integrable
        (fun ts : ℝ × ℝ ↦ F (ts.1, omega) * F (ts.2, omega))
        (nu.prod nu) := hFt.mul_prod hFt
    calc
      (∫ t, F (t, omega) ∂nu) ^ (2 : ℕ) =
          (∫ t, F (t, omega) ∂nu) *
            (∫ s, F (s, omega) ∂nu) := by ring
      _ = ∫ t, F (t, omega) *
            (∫ s, F (s, omega) ∂nu) ∂nu := by
          rw [integral_mul_const]
      _ = ∫ t, ∫ s, F (t, omega) * F (s, omega) ∂nu ∂nu := by
          apply integral_congr_ae
          exact ae_of_all nu fun t ↦ by
            change F (t, omega) * (∫ s, F (s, omega) ∂nu) =
              ∫ s, F (t, omega) * F (s, omega) ∂nu
            rw [integral_const_mul]
      _ = ∫ ts, F (ts.1, omega) * F (ts.2, omega)
            ∂nu.prod nu := (integral_prod _ hprod).symm
      _ = ∫ ts, H (ts, omega) ∂nu.prod nu := by rfl
  have hswap :
      (∫ omega, ∫ ts, H (ts, omega) ∂nu.prod nu ∂Problem520.μ) =
        ∫ ts, ∫ omega, H (ts, omega) ∂Problem520.μ ∂nu.prod nu :=
    (integral_prod_symm H hH).symm.trans (integral_prod H hH)
  have hinner (ts : ℝ × ℝ) :
      (∫ omega, H (ts, omega) ∂Problem520.μ) =
        harperRankinTwoHeightCubeMass y a ts.1 ts.2
          (A ts.1 ∩ A ts.2) := by
    simpa only [H, F] using
      integral_graphIndicator_harperRankinEulerDensity_mul_eq_twoHeightCubeMass
        A hsection ts.1 ts.2
  have hraw :
      (∫ omega, ∫ ts, H (ts, omega) ∂nu.prod nu ∂Problem520.μ) =
        ∫ ts,
          harperRankinTwoHeightCubeMass y a ts.1 ts.2
            (A ts.1 ∩ A ts.2) ∂nu.prod nu := by
    rw [hswap]
    apply integral_congr_ae
    exact ae_of_all (nu.prod nu) hinner
  unfold harperRankinRestrictedGraphEnergy
  rw [show (fun omega ↦
      (((4 / 5 : ℝ) *
          (∫ t in harperLowerVerticalBand,
            G.indicator
              (fun w : ℝ × Problem520.Omega ↦
                harperRankinEulerDensity y a w.2 w.1) (t, omega))) /
        Real.log (y : ℝ)) ^ (2 : ℕ)) =
      (fun omega ↦
        (16 / 25 : ℝ) * (∫ ts, H (ts, omega) ∂nu.prod nu) /
          Real.log (y : ℝ) ^ (2 : ℕ)) by
    funext omega
    change (((4 / 5 : ℝ) * (∫ t, F (t, omega) ∂nu)) /
        Real.log (y : ℝ)) ^ (2 : ℕ) = _
    rw [div_pow, mul_pow, hsquare]
    ring]
  rw [integral_div, integral_const_mul, hraw]

#print axioms Erdos.Problem1144.harperRankinTwoHeightCubeMass_nonneg
#print axioms Erdos.Problem1144.integral_harperRankinEulerDensity_mul_restrict_eq_twoHeightCubeMass
#print axioms Erdos.Problem1144.integral_sq_harperRankinRestrictedGraphEnergy_eq_twoHeightCubeMass

end

end Problem1144
end Erdos
