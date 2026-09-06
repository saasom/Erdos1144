import Erdos.Problem1144.HarperRestrictedGraphEnergy
import Erdos.Problem520.HarperTiltedOmega

open MeasureTheory Set
open scoped ENNReal

namespace Erdos
namespace Problem1144

/-!
# Exact two-height restricted Harper mass

The second moment of a vertically restricted Euler energy is governed by a
two-height change of measure.  This file first records that object exactly on
the finite prime cube and proves its pullback identity on the original sign
space.  No estimate is used here.
-/

/-- The unnormalized two-height tilted mass of a finite-cube event.  Its
density is the product of the two squared Euler densities. -/
noncomputable def harperTwoHeightCubeMass
    (y : Nat) (t s : Real) (A : Set (Problem520.HarperPrimeCube y)) : Real :=
  ∫ eta in A,
    Problem520.harperCubeDensity y t eta *
      Problem520.harperCubeDensity y s eta
    ∂Measure.pi (fun _ : Problem520.HarperPrimeIndex y => Problem520.coin)

theorem harperTwoHeightCubeMass_nonneg
    (y : Nat) (t s : Real)
    (A : Set (Problem520.HarperPrimeCube y)) :
    0 <= harperTwoHeightCubeMass y t s A := by
  unfold harperTwoHeightCubeMass
  exact setIntegral_nonneg (Set.toFinite A).measurableSet fun eta _heta =>
    mul_nonneg (Problem520.harperCubeDensity_nonneg y t eta)
      (Problem520.harperCubeDensity_nonneg y s eta)

/-- Exact pullback of the unnormalized two-height tilted mass to the infinite
Rademacher product space. -/
theorem integral_harperEulerDensity_mul_restrict_eq_twoHeightCubeMass
    (y : Nat) (t s : Real)
    (A : Set (Problem520.HarperPrimeCube y)) :
    (∫ omega in Problem520.harperPrimeRestriction y ⁻¹' A,
        Problem520.harperEulerDensity y omega t *
          Problem520.harperEulerDensity y omega s ∂Problem520.μ) =
      harperTwoHeightCubeMass y t s A := by
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  have hpre : MeasurableSet
      (Problem520.harperPrimeRestriction y ⁻¹' A) :=
    hA.preimage (Problem520.measurable_harperPrimeRestriction y)
  rw [← integral_indicator hpre, harperTwoHeightCubeMass,
    ← integral_indicator hA]
  rw [← Problem520.integral_comp_harperPrimeRestriction_mu y
    (fun eta => A.indicator (fun eta =>
      Problem520.harperCubeDensity y t eta *
        Problem520.harperCubeDensity y s eta) eta)]
  apply integral_congr_ae
  exact ae_of_all Problem520.μ fun omega => by
    by_cases hmem : Problem520.harperPrimeRestriction y omega ∈ A
    · have hpreMem : omega ∈
          Problem520.harperPrimeRestriction y ⁻¹' A := hmem
      simp only [Set.indicator_of_mem hmem,
        Set.indicator_of_mem hpreMem]
      rw [Problem520.harperCubeDensity_harperPrimeRestriction,
        Problem520.harperCubeDensity_harperPrimeRestriction]
    · have hpreNot : omega ∉
          Problem520.harperPrimeRestriction y ⁻¹' A := hmem
      simp [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem hpreNot]

/-- For a barrier graph represented by finite-cube sections, the product of
the two retained vertical densities is exactly restricted to the intersection
of the two section events. -/
theorem integral_graphIndicator_harperEulerDensity_mul_eq_twoHeightCubeMass
    {y : Nat} {G : Set (Real × Problem520.Omega)}
    (A : Real -> Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t)
    (t s : Real) :
    (∫ omega,
        G.indicator
            (fun w : Real × Problem520.Omega =>
              Problem520.harperEulerDensity y w.2 w.1) (t, omega) *
          G.indicator
            (fun w : Real × Problem520.Omega =>
              Problem520.harperEulerDensity y w.2 w.1) (s, omega)
        ∂Problem520.μ) =
      harperTwoHeightCubeMass y t s (A t ∩ A s) := by
  have hAt : MeasurableSet (A t) := (Set.toFinite (A t)).measurableSet
  have hAs : MeasurableSet (A s) := (Set.toFinite (A s)).measurableSet
  have hpre : MeasurableSet
      (Problem520.harperPrimeRestriction y ⁻¹' (A t ∩ A s)) :=
    (hAt.inter hAs).preimage
      (Problem520.measurable_harperPrimeRestriction y)
  rw [← integral_harperEulerDensity_mul_restrict_eq_twoHeightCubeMass]
  rw [← integral_indicator hpre]
  apply integral_congr_ae
  exact ae_of_all Problem520.μ fun omega => by
    by_cases ht : (t, omega) ∈ G
    · have htA := (hsection t omega).1 ht
      by_cases hs : (s, omega) ∈ G
      · have hsA := (hsection s omega).1 hs
        simp [ht, hs, htA, hsA]
      · have hsA : Problem520.harperPrimeRestriction y omega ∉ A s := by
          exact fun h => hs ((hsection s omega).2 h)
        simp [ht, hs, hsA]
    · have htA : Problem520.harperPrimeRestriction y omega ∉ A t := by
        exact fun h => ht ((hsection t omega).2 h)
      simp [ht, htA]

/-! ## Exact second-moment identity -/

/-- The square of the concrete restricted energy is exactly the double
vertical integral of the two-height restricted cube mass.  This is the
precise analytic object that the two-height ballot argument must bound. -/
theorem integral_sq_harperRestrictedGraphEnergy_eq_twoHeightCubeMass
    {y : Nat} {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G)
    (A : Real -> Set (Problem520.HarperPrimeCube y))
    (hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t) :
    (∫ omega,
        harperRestrictedGraphEnergy y G omega ^ (2 : Nat)
          ∂Problem520.μ) =
      (∫ ts,
          harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2)
          ∂(volume.restrict harperLowerVerticalBand).prod
            (volume.restrict harperLowerVerticalBand)) /
        Real.log (y : Real) ^ (2 : Nat) := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let F : Real × Problem520.Omega -> Real := fun w =>
    G.indicator
      (fun z : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y z.2 z.1) w
  let H : (Real × Real) × Problem520.Omega -> Real := fun w =>
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
      0 <= F w ∧ F w <= U := by
    by_cases hw : w ∈ G
    · simp only [F, Set.indicator_of_mem hw]
      exact ⟨Problem520.harperEulerDensity_nonneg y w.2 w.1,
        Problem520.harperEulerDensity_le_uniformBound y w.2 w.1⟩
    · simp [F, hw, U,
        Problem520.harperEulerDensityUniformBound_nonneg]
  have hH : Integrable H ((nu.prod nu).prod Problem520.μ) := by
    apply Integrable.of_bound hHmeas.aestronglyMeasurable (U ^ (2 : Nat))
    exact ae_of_all _ fun w => by
      have hleft := hFbounds (w.1.1, w.2)
      have hright := hFbounds (w.1.2, w.2)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hleft.1 hright.1)]
      rw [pow_two]
      exact mul_le_mul hleft.2 hright.2 hright.1
        (Problem520.harperEulerDensityUniformBound_nonneg y)
  have hsquare (omega : Problem520.Omega) :
      (∫ t, F (t, omega) ∂nu) ^ (2 : Nat) =
        ∫ ts, H (ts, omega) ∂nu.prod nu := by
    have hFt : Integrable (fun t => F (t, omega)) nu := by
      simpa only [F, nu] using
        integrableOn_harperRestrictedGraphDensity y hG omega
    have hprod : Integrable
        (fun ts : Real × Real => F (ts.1, omega) * F (ts.2, omega))
        (nu.prod nu) := hFt.mul_prod hFt
    calc
      (∫ t, F (t, omega) ∂nu) ^ (2 : Nat) =
          (∫ t, F (t, omega) ∂nu) *
            (∫ s, F (s, omega) ∂nu) := by ring
      _ = ∫ t, F (t, omega) *
            (∫ s, F (s, omega) ∂nu) ∂nu := by
          rw [integral_mul_const]
      _ = ∫ t, ∫ s, F (t, omega) * F (s, omega) ∂nu ∂nu := by
          apply integral_congr_ae
          exact ae_of_all nu fun t => by
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
  have hinner (ts : Real × Real) :
      (∫ omega, H (ts, omega) ∂Problem520.μ) =
        harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2) := by
    simpa only [H, F] using
      integral_graphIndicator_harperEulerDensity_mul_eq_twoHeightCubeMass
        A hsection ts.1 ts.2
  have hraw :
      (∫ omega, ∫ ts, H (ts, omega) ∂nu.prod nu ∂Problem520.μ) =
        ∫ ts,
          harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2)
          ∂nu.prod nu := by
    rw [hswap]
    apply integral_congr_ae
    exact ae_of_all (nu.prod nu) hinner
  unfold harperRestrictedGraphEnergy
  rw [show (fun omega =>
      ((∫ t in harperLowerVerticalBand,
          G.indicator
            (fun w : Real × Problem520.Omega =>
              Problem520.harperEulerDensity y w.2 w.1) (t, omega)) /
        Real.log (y : Real)) ^ (2 : Nat)) =
      (fun omega =>
        (∫ ts, H (ts, omega) ∂nu.prod nu) /
          Real.log (y : Real) ^ (2 : Nat)) by
    funext omega
    change ((∫ t, F (t, omega) ∂nu) / Real.log (y : Real)) ^
        (2 : Nat) = _
    rw [div_pow, hsquare]]
  rw [integral_div, hraw]

/-! ## Fully explicit remaining ballot statement -/

/-- The remaining multiplicative-chaos theorem, expressed only in terms of
one-height tilted section probabilities and the exact two-height finite-cube
mass.  The logarithm in the last line is precisely the normalization of the
vertical energy. -/
def HarperRestrictedTwoHeightBallotStatement : Prop :=
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
          (∫ ts,
              harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2)
              ∂(volume.restrict harperLowerVerticalBand).prod
                (volume.restrict harperLowerVerticalBand)) <=
            ((C * harperInitialCriticalScale y) *
              Real.log (y : Real)) ^ (2 : Nat)

/-- The explicit one-height/two-height ballot theorem supplies exactly the
first/second-moment certificate required by the fractional-moment argument. -/
theorem harperRestrictedGraphBallotSecondStatement_of_twoHeight
    (htwo : HarperRestrictedTwoHeightBallotStatement) :
    HarperRestrictedGraphBallotSecondStatement := by
  obtain ⟨delta, C, hdelta, hC, Y, hcert⟩ := htwo
  refine ⟨delta, C, hdelta, hC, Y, ?_⟩
  intro y hyY hy4
  obtain ⟨G, A, hG, hsection, hprob, hmass⟩ := hcert y hyY hy4
  refine ⟨G, A, hG, hsection, hprob, ?_⟩
  rw [integral_sq_harperRestrictedGraphEnergy_eq_twoHeightCubeMass
    hG A hsection]
  have hlog : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  apply (div_le_iff₀ (sq_pos_of_pos hlog)).2
  calc
    (∫ ts,
        harperTwoHeightCubeMass y ts.1 ts.2 (A ts.1 ∩ A ts.2)
        ∂(volume.restrict harperLowerVerticalBand).prod
          (volume.restrict harperLowerVerticalBand)) <=
        ((C * harperInitialCriticalScale y) *
          Real.log (y : Real)) ^ (2 : Nat) := hmass
    _ = (C * harperInitialCriticalScale y) ^ (2 : Nat) *
          Real.log (y : Real) ^ (2 : Nat) := by ring

/-- End-to-end handoff from the explicit two-height ballot estimate to the
sole missing lower half moment. -/
theorem harperRademacherInitialHalfMomentLowerStatement_of_twoHeightBallot
    (htwo : HarperRestrictedTwoHeightBallotStatement) :
    HarperRademacherInitialHalfMomentLowerStatement :=
  harperRademacherInitialHalfMomentLowerStatement_of_ballotSecond
    (harperRestrictedGraphBallotSecondStatement_of_twoHeight htwo)

end Problem1144
end Erdos
