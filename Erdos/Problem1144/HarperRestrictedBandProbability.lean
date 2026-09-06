import Erdos.Problem1144.HarperLogBallotCertificate
import Erdos.Problem1144.EndpointSeparationBridge

open MeasureTheory Set
open scoped ENNReal

namespace Erdos
namespace Problem1144

/-!
# Positive probability for the fixed-band Harper energy

The completed logarithmic-ballot proof naturally constructs a nonnegative
Euler-product energy on the fixed height band `[1/3, 1/2]`.  Its first moment
is of critical order and its second moment is of the square of that order.
This file keeps that stronger, localized conclusion instead of immediately
discarding it through the lower-half-moment wrapper.

The final theorem gives fixed positive probability that the *unrestricted*
squarefree Euler energy on this band is at least a constant multiple of the
critical scale.  This is the right input for comparison with the complete
Euler product: on a band bounded away from zero their densities differ only
by the deterministic square-factor multiplier.
-/

/-- Measurability of the concrete graph-restricted energy. -/
theorem measurable_harperRestrictedGraphEnergy
    {y : Nat} {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G) :
    Measurable (harperRestrictedGraphEnergy y G) := by
  let nu : Measure Real := volume.restrict harperLowerVerticalBand
  let F : Real × Problem520.Omega → Real := fun w =>
    G.indicator
      (fun z : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y z.2 z.1) w
  have hF : Measurable F := by
    simpa only [F] using
      (Problem520.measurable_harperEulerDensity_joint y).indicator hG
  have hswap : Measurable
      (fun z : Problem520.Omega × Real => F (z.2, z.1)) :=
    hF.comp (measurable_snd.prodMk measurable_fst)
  have hinner : Measurable (fun omega => ∫ t, F (t, omega) ∂nu) :=
    hswap.stronglyMeasurable.integral_prod_right.measurable
  simpa only [harperRestrictedGraphEnergy, nu, F] using
    hinner.div measurable_const

/-- Removing the barrier graph can only increase the fixed-band energy. -/
theorem harperRestrictedGraphEnergy_le_bandEnergy
    {y : Nat} (hy : 1 < y) {G : Set (Real × Problem520.Omega)}
    (hG : MeasurableSet G) (omega : Problem520.Omega) :
    harperRestrictedGraphEnergy y G omega ≤
      Problem520.harperEulerSetEnergy y harperLowerVerticalBand omega := by
  let restricted : Real → Real := fun t =>
    G.indicator
      (fun w : Real × Problem520.Omega =>
        Problem520.harperEulerDensity y w.2 w.1) (t, omega)
  let density : Real → Real := fun t =>
    Problem520.harperEulerDensity y omega t
  have hrestricted : IntegrableOn restricted harperLowerVerticalBand := by
    simpa only [restricted] using
      integrableOn_harperRestrictedGraphDensity y hG omega
  have hdensity : IntegrableOn density harperLowerVerticalBand := by
    have hunit := Problem520.integrableOn_harperEulerDensity_unitInterval
      y true 0 omega
    apply hunit.mono_set
    intro t ht
    change (1 : Real) / 3 ≤ t ∧ t ≤ (1 : Real) / 2 at ht
    have hmem : t ∈ Set.Ico (0 : Real) 1 := by constructor <;> linarith
    simpa [density, Problem520.harperEulerUnitInterval] using hmem
  have hpoint : ∀ t ∈ harperLowerVerticalBand,
      restricted t ≤ density t := by
    intro t _ht
    by_cases hmem : (t, omega) ∈ G
    · simp [restricted, density, hmem]
    · simp [restricted, density, hmem,
        Problem520.harperEulerDensity_nonneg y omega t]
  have hint :
      (∫ t in harperLowerVerticalBand, restricted t) ≤
        ∫ t in harperLowerVerticalBand, density t :=
    setIntegral_mono_on hrestricted hdensity
      measurableSet_harperLowerVerticalBand hpoint
  have hlog : 0 ≤ Real.log (y : Real) :=
    (Real.log_pos (by exact_mod_cast hy)).le
  unfold harperRestrictedGraphEnergy Problem520.harperEulerSetEnergy
  exact div_le_div_of_nonneg_right hint hlog

/-- The completed two-height theorem already contains an unconditional
first/second-moment certificate for a graph-restricted fixed-band energy. -/
theorem harperRestrictedGraphFirstSecondStatement_unconditional :
    HarperRestrictedGraphFirstSecondStatement :=
  harperRestrictedGraphFirstSecondStatement_of_ballotSecond
    (harperRestrictedGraphBallotSecondStatement_of_twoHeight
      harperRestrictedTwoHeightBallotStatement_unconditional)

/-- Fixed positive probability of critical energy on the literal band
`[1/3,1/2]`.  Unlike the earlier full-energy event, this conclusion retains
the frequency localization used by the ballot proof.
-/
theorem exists_harperLowerVerticalBandEnergy_fixedProbability_unconditional :
    ∃ delta : Real, 0 < delta ∧ ∃ c : Real, 0 < c ∧ ∃ Y : Nat,
      ∀ y : Nat, Y ≤ y → 4 ≤ y →
        delta ≤ Problem520.μ.real
          {omega |
            c * harperInitialCriticalScale y ≤
              Problem520.harperEulerSetEnergy
                y harperLowerVerticalBand omega} := by
  obtain ⟨c, C, hc, hC, Y, hcert⟩ :=
    harperRestrictedGraphFirstSecondStatement_unconditional
  let delta : Real := 1 / (4 * (C / c) ^ 2)
  let c' : Real := c / 2
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hc' : 0 < c' := by dsimp only [c']; positivity
  refine ⟨delta, hdelta, c', hc', Y, ?_⟩
  intro y hyY hy4
  obtain ⟨G, hG, hfirst, hsecond⟩ := hcert y hyY hy4
  let R : Problem520.Omega → Real := harperRestrictedGraphEnergy y G
  let K : Real := harperInitialCriticalScale y
  let m : Real := c * K
  let Z : Problem520.Omega → Real := fun omega => Real.sqrt (R omega)
  let U : Real := Real.sqrt (m / 2)
  let Q : Real := (C / c) ^ 2
  have hK : 0 < K := harperInitialCriticalScale_pos hy4
  have hm : 0 < m := mul_pos hc hK
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hRnonneg : ∀ omega, 0 ≤ R omega := by
    intro omega
    exact harperRestrictedGraphEnergy_nonneg (by omega) G omega
  have hZmeas : Measurable Z := by
    exact Real.continuous_sqrt.measurable.comp
      (measurable_harperRestrictedGraphEnergy hG)
  have hZsq : ∀ omega, Z omega ^ 2 = R omega := by
    intro omega
    exact Real.sq_sqrt (hRnonneg omega)
  have hZfourth : ∀ omega, Z omega ^ 4 = R omega ^ 2 := by
    intro omega
    rw [show Z omega ^ 4 = (Z omega ^ 2) ^ 2 by ring, hZsq]
  have hsecondInt : Integrable (fun omega => Z omega ^ 2) Problem520.μ := by
    apply (integrable_harperRestrictedGraphEnergy (y := y) hG).congr
    exact ae_of_all _ fun omega => (hZsq omega).symm
  have hfourthInt : Integrable (fun omega => Z omega ^ 4) Problem520.μ := by
    apply (integrable_sq_harperRestrictedGraphEnergy
      (show 1 < y by omega) hG).congr
    exact ae_of_all _ fun omega => (hZfourth omega).symm
  have hU : U ^ 2 ≤ m / 2 := by
    rw [show U ^ 2 = m / 2 by
      dsimp only [U]
      exact Real.sq_sqrt (by positivity)]
  have hsecond' : m ≤ ∫ omega, Z omega ^ 2 ∂Problem520.μ := by
    rw [show (fun omega => Z omega ^ 2) = R by funext omega; exact hZsq omega]
    simpa only [m, K, R] using hfirst
  have hfourth' :
      (∫ omega, Z omega ^ 4 ∂Problem520.μ) ≤ Q * m ^ 2 := by
    rw [show (fun omega => Z omega ^ 4) = fun omega => R omega ^ 2 by
      funext omega; exact hZfourth omega]
    calc
      (∫ omega, R omega ^ 2 ∂Problem520.μ) ≤ (C * K) ^ 2 := by
        simpa only [R, K] using hsecond
      _ = Q * m ^ 2 := by
        dsimp only [Q, m]
        field_simp [hc.ne']
  have hpz :
      1 / (4 * Q) ≤ Problem520.μ.real (freshLargeEvent Z U) := by
    have h := measureReal_freshLargeEvent_lower_of_second_fourth
      Z U m Q hZmeas hm hQ hU hsecondInt hfourthInt hsecond' hfourth'
    simpa only [mu, coin, Problem520.μ, Problem520.coin] using h
  have hevent :
      freshLargeEvent Z U = {omega | m / 2 ≤ R omega} := by
    ext omega
    simp only [freshLargeEvent, Set.mem_setOf_eq]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    constructor
    · intro h
      have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      rw [show U ^ 2 = m / 2 by
        dsimp only [U]
        exact Real.sq_sqrt (by positivity), hZsq] at hsquare
      exact hsquare
    · intro h
      simpa only [U, Z] using Real.sqrt_le_sqrt h
  have hsubset : {omega | m / 2 ≤ R omega} ⊆
      {omega |
        c' * harperInitialCriticalScale y ≤
          Problem520.harperEulerSetEnergy
            y harperLowerVerticalBand omega} := by
    intro omega homega
    have hRle := harperRestrictedGraphEnergy_le_bandEnergy
      (show 1 < y by omega) hG omega
    change m / 2 ≤ R omega at homega
    change c' * K ≤ _
    have hthreshold : c' * K = m / 2 := by
      dsimp only [c', m]
      ring
    rw [hthreshold]
    exact homega.trans hRle
  calc
    delta = 1 / (4 * Q) := by rfl
    _ ≤ Problem520.μ.real (freshLargeEvent Z U) := hpz
    _ = Problem520.μ.real {omega | m / 2 ≤ R omega} := by rw [hevent]
    _ ≤ Problem520.μ.real
        {omega |
          c' * harperInitialCriticalScale y ≤
            Problem520.harperEulerSetEnergy
              y harperLowerVerticalBand omega} := measureReal_mono hsubset

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.measurable_harperRestrictedGraphEnergy
#print axioms Erdos.Problem1144.harperRestrictedGraphFirstSecondStatement_unconditional
#print axioms Erdos.Problem1144.exists_harperLowerVerticalBandEnergy_fixedProbability_unconditional
