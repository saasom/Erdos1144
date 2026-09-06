import Erdos.Problem1144.HarperCandidateCovariancePerronTail
import Erdos.Problem520.HarperParsevalTail

open MeasureTheory Set
open scoped Topology

namespace Erdos.Problem1144

/-- The critical angular Fourier density, with its actual Cauchy weight and
with the same height convention as the covariance screens. -/
theorem candidate_criticalEuler_norm_sq_eq_cauchyDensity
    (y : ℕ) (ω : Omega) (t : ℝ) :
    ‖candidateEulerAngularApprox y 0 ω t‖ ^ 2 =
      Problem520.harperEulerDensity y ω t / ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
  rw [candidate_criticalEuler_norm_sq_eq_density]
  congr 1
  unfold harperRankinEulerDensity Problem520.harperEulerDensity
  apply Finset.prod_congr rfl
  intro p hp
  rw [harperRankinEulerFactor_eq, harperRankinEulerRadius_zero,
    Problem520.harperEulerFactor_eq ω (Nat.prime_of_mem_primesBelow hp).pos,
    neg_mul, Real.cos_neg, inv_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
  ring

/-- Exact total mass of the angular Cauchy weight. -/
theorem candidate_integral_angularCauchyWeight :
    (∫ t : ℝ, 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) = 2 * Real.pi := by
  have heq : (fun t : ℝ => 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) =
      fun t : ℝ => 4 * (1 + (2 * t) ^ 2)⁻¹ := by
    funext t
    field_simp
    <;> ring
  rw [heq, integral_const_mul,
    Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) 2,
    integral_univ_inv_one_add_sq]
  norm_num [smul_eq_mul]
  <;> ring

/-- Euler Fourier energy on a measurable graph of frequency deletions. -/
noncomputable def candidateEulerFrequencyMass (y : ℕ) (I : Set ℝ)
    (G : Set (ℝ × Problem520.Omega)) (ω : Problem520.Omega) : ℝ :=
  ∫ t in I, G.indicator (fun z =>
    Problem520.harperEulerDensity y z.2 z.1 / ((1 / 2 : ℝ) ^ 2 + z.1 ^ 2)) (t, ω)

/-- This is literally the squared angular Fourier transform on the
selected graph, rather than an auxiliary density proxy. -/
theorem candidate_eulerFrequencyMass_eq_angular (y : ℕ) (I : Set ℝ)
    (G : Set (ℝ × Problem520.Omega)) (ω : Problem520.Omega) :
    candidateEulerFrequencyMass y I G ω =
      ∫ t in I, G.indicator (fun z => ‖candidateEulerAngularApprox y 0 z.2 z.1‖ ^ 2) (t, ω) := by
  simp_rw [candidate_criticalEuler_norm_sq_eq_cauchyDensity]
  rfl

theorem candidate_measurable_eulerFrequencyMass (y : ℕ) (I : Set ℝ)
    {G : Set (ℝ × Problem520.Omega)} (hG : MeasurableSet G) :
    Measurable (candidateEulerFrequencyMass y I G) :=
  ((Problem520.measurable_harperEulerDensity_div_cauchyKernel_joint y).indicator hG).stronglyMeasurable.integral_prod_left'.measurable

theorem candidate_eulerFrequencyMass_nonneg (y : ℕ) (I : Set ℝ)
    (G : Set (ℝ × Problem520.Omega)) (ω : Problem520.Omega) :
    0 ≤ candidateEulerFrequencyMass y I G ω := by
  apply integral_nonneg
  intro t
  exact Set.indicator_nonneg (fun z _ => div_nonneg
    (Problem520.harperEulerDensity_nonneg y z.2 z.1) (by positivity)) _

/-- Joint integrability holds on every frequency set, including an
unbounded set. The finite-product bound is used only for regularity. -/
theorem candidate_integrable_eulerFrequencyMass_product (y : ℕ) (I : Set ℝ)
    {G : Set (ℝ × Problem520.Omega)} (hG : MeasurableSet G) :
    Integrable (G.indicator (fun z =>
      Problem520.harperEulerDensity y z.2 z.1 / ((1 / 2 : ℝ) ^ 2 + z.1 ^ 2)))
      ((volume.restrict I).prod Problem520.μ) := by
  apply Integrable.indicator _ hG
  have hk := Problem520.integrable_one_div_harperCauchyKernel.integrableOn (s := I)
  have hmajor := (hk.const_mul (Problem520.harperEulerDensityUniformBound y)).mul_prod
    (integrable_const (1 : ℝ) (μ := Problem520.μ))
  apply hmajor.mono'
    (Problem520.measurable_harperEulerDensity_div_cauchyKernel_joint y).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    have hden : 0 < (1 / 2 : ℝ) ^ 2 + z.1 ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (Problem520.harperEulerDensity_nonneg y z.2 z.1) hden.le)]
    simpa only [mul_one, mul_one_div] using
      div_le_div_of_nonneg_right (Problem520.harperEulerDensity_le_uniformBound y z.2 z.1) hden.le

theorem candidate_integrable_eulerFrequencyMass (y : ℕ) (I : Set ℝ)
    {G : Set (ℝ × Problem520.Omega)} (hG : MeasurableSet G) :
    Integrable (candidateEulerFrequencyMass y I G) Problem520.μ :=
  (candidate_integrable_eulerFrequencyMass_product y I hG).integral_prod_right

/-- Exact Fubini exchange for the actual weighted deletion energy. -/
theorem candidate_integral_eulerFrequencyMass_eq (y : ℕ) (I : Set ℝ)
    {G : Set (ℝ × Problem520.Omega)} (hG : MeasurableSet G) :
    (∫ ω, candidateEulerFrequencyMass y I G ω ∂Problem520.μ) =
      ∫ t in I, (∫ ω in {ω | (t, ω) ∈ G},
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) /
          ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
  unfold candidateEulerFrequencyMass
  rw [← integral_integral_swap (f := fun t ω => G.indicator (fun z =>
      Problem520.harperEulerDensity y z.2 z.1 / ((1 / 2 : ℝ) ^ 2 + z.1 ^ 2)) (t, ω))
    (candidate_integrable_eulerFrequencyMass_product y I hG)]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp : Measurable (fun ω : Problem520.Omega => (t, ω)) :=
    measurable_const.prodMk measurable_id
  have hs : MeasurableSet {ω | (t, ω) ∈ G} := hG.preimage hp
  rw [← integral_div, ← integral_indicator hs]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    by_cases h : (t, ω) ∈ G <;> simp [h]

/-- A uniform weighted section estimate integrates with total Cauchy mass
`2*pi`; subdivision into shrinking bands incurs no extra band-count loss. -/
theorem candidate_integral_eulerFrequencyMass_le (y : ℕ) {I : Set ℝ}
    (hI : MeasurableSet I) {G : Set (ℝ × Problem520.Omega)}
    (hG : MeasurableSet G) {B : ℝ} (hB : 0 ≤ B)
    (hsection : ∀ t ∈ I, (∫ ω in {ω | (t, ω) ∈ G},
      Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤ B) :
    (∫ ω, candidateEulerFrequencyMass y I G ω ∂Problem520.μ) ≤
      2 * Real.pi * B := by
  have hi := candidate_integrable_eulerFrequencyMass_product y I hG
  have hbound : ∀ᵐ t ∂volume.restrict I,
      (∫ ω, G.indicator (fun z => Problem520.harperEulerDensity y z.2 z.1 /
        ((1 / 2 : ℝ) ^ 2 + z.1 ^ 2)) (t, ω) ∂Problem520.μ) ≤
          B * (1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) := by
    filter_upwards [ae_restrict_mem hI] with t ht
    have hp : Measurable (fun ω : Problem520.Omega => (t, ω)) :=
      measurable_const.prodMk measurable_id
    have heq : (∫ ω, G.indicator (fun z => Problem520.harperEulerDensity y z.2 z.1 /
      ((1 / 2 : ℝ) ^ 2 + z.1 ^ 2)) (t, ω) ∂Problem520.μ) =
        (∫ ω in {ω | (t, ω) ∈ G}, Problem520.harperEulerDensity y ω t ∂Problem520.μ) /
          ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
      have hs : MeasurableSet {ω | (t, ω) ∈ G} := hG.preimage hp
      rw [← integral_div, ← integral_indicator hs]
      apply integral_congr_ae
      exact ae_of_all _ fun ω => by by_cases h : (t, ω) ∈ G <;> simp [h]
    rw [heq, mul_one_div]
    exact div_le_div_of_nonneg_right (hsection t ht) (by positivity)
  have h := integral_mono_ae hi.integral_prod_left
    (Problem520.integrable_one_div_harperCauchyKernel.integrableOn.const_mul B) hbound
  unfold candidateEulerFrequencyMass
  rw [← integral_integral_swap (f := fun t ω => G.indicator (fun z =>
    Problem520.harperEulerDensity y z.2 z.1 / ((1 / 2 : ℝ) ^ 2 + z.1 ^ 2)) (t, ω)) hi]
  apply h.trans
  rw [integral_const_mul]
  calc
    _ ≤ B * ∫ t : ℝ, 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact setIntegral_le_integral Problem520.integrable_one_div_harperCauchyKernel
        (ae_of_all _ fun t => by positivity)
    _ = _ := by rw [candidate_integral_angularCauchyWeight]; ring

end Erdos.Problem1144
