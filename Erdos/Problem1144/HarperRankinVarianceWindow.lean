import Erdos.Problem1144.HarperRankinCharacteristic
import Erdos.Problem520.HarperCentralBandMoments

open Finset Filter
open scoped BigOperators Topology

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Variance stability on a truncated Rankin-shifted block schedule

The one-height lower bound uses a small positive Rankin shift.  The shifted
one-prime radius loses the exact factor `p ^ (-a)`, while centering under the
shifted tilted law loses `1 - bias^2`.  On scheduled prime blocks the latter
is at least `15/16`.  Thus retaining only blocks on which `p ^ (-a) >= 4/5`
transfers the critical-line variance lower bound `1/3` to the Gaussian
corridor threshold `1/4` exactly.
-/

/-- Exact factorization of the squared Rankin-shifted Euler radius. -/
theorem harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg
    {p : ℕ} (hp : 0 < p) (a : ℝ) :
    harperRankinEulerRadius p a ^ 2 =
      (p : ℝ)⁻¹ * (p : ℝ) ^ (-a) := by
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hpRpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  unfold harperRankinEulerRadius
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpR]
  have hexponent :
      (-(1 + a) / 2) * ((2 : ℕ) : ℝ) = (-1 : ℝ) + (-a) := by
    norm_num
    ring
  rw [hexponent]
  rw [Real.rpow_add hpRpos, Real.rpow_neg_one]

/-- The shifted centered one-prime variance retains at least the product of
the Rankin radial weight and the uniform centering factor. -/
theorem fifteen_sixteenths_mul_weight_mul_cos_sq_div_le_rankinVariance
    {p : ℕ} (hp : 64 ≤ p) {a : ℝ} (ha : 0 ≤ a) (t : ℝ)
    (hweight : (4 / 5 : ℝ) ≤ (p : ℝ) ^ (-a)) :
    (15 / 16 : ℝ) * (4 / 5 : ℝ) *
        (Real.cos (t * Real.log (p : ℝ)) ^ 2 / p) ≤
      harperRankinCenteredLinearPrimeVariance p a t t := by
  have hpPos : 0 < p := by omega
  have hpInvNonneg : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hradial :
      (4 / 5 : ℝ) * (p : ℝ)⁻¹ ≤
        harperRankinEulerRadius p a ^ 2 := by
    rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hpPos a]
    nlinarith [mul_le_mul_of_nonneg_left hweight hpInvNonneg]
  have hbias :=
    fifteen_sixteenths_le_one_sub_harperRankinTiltBias_sq hp ha t
  unfold harperRankinCenteredLinearPrimeVariance
  rw [mul_pow]
  calc
    (15 / 16 : ℝ) * (4 / 5 : ℝ) *
          (Real.cos (t * Real.log (p : ℝ)) ^ 2 / p) =
        ((4 / 5 : ℝ) * (p : ℝ)⁻¹) *
          Real.cos (t * Real.log (p : ℝ)) ^ 2 * (15 / 16 : ℝ) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ harperRankinEulerRadius p a ^ 2 *
          Real.cos (t * Real.log (p : ℝ)) ^ 2 *
            (1 - harperRankinTiltBias p a t ^ 2) := by
      gcongr

/-- A nonnegative Rankin shift never enlarges the uncentered cosine
contribution at one prime. -/
theorem harperRankinCenteredLinearPrimeVariance_le_cos_sq_div
    {p : ℕ} (hp : 1 ≤ p) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) :
    harperRankinCenteredLinearPrimeVariance p a t t ≤
      Real.cos (t * Real.log (p : ℝ)) ^ 2 / p := by
  let r : ℝ := harperRankinEulerRadius p a
  let c : ℝ := Real.cos (t * Real.log (p : ℝ))
  let b : ℝ := harperRankinTiltBias p a t
  have hr : 0 ≤ r := harperRankinEulerRadius_nonneg p a
  have hrle : r ≤ (Real.sqrt (p : ℝ))⁻¹ :=
    harperRankinEulerRadius_le_inv_sqrt hp ha
  have hrSq : r ^ 2 ≤ (Real.sqrt (p : ℝ))⁻¹ ^ 2 :=
    pow_le_pow_left₀ hr hrle 2
  have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hinvSq : (Real.sqrt (p : ℝ))⁻¹ ^ 2 = (p : ℝ)⁻¹ := by
    calc
      (Real.sqrt (p : ℝ))⁻¹ ^ 2 =
          (Real.sqrt (p : ℝ) ^ 2)⁻¹ := by rw [inv_pow]
      _ = (p : ℝ)⁻¹ := by rw [Real.sq_sqrt hpR]
  have hbAbs : |b| ≤ 1 := abs_harperRankinTiltBias_le_one p a t
  have hbSq : b ^ 2 ≤ 1 := by
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg b) hbAbs
  unfold harperRankinCenteredLinearPrimeVariance
  change (r * c) ^ 2 * (1 - b ^ 2) ≤ c ^ 2 / (p : ℝ)
  calc
    (r * c) ^ 2 * (1 - b ^ 2) ≤ (r * c) ^ 2 * 1 := by
      gcongr
      nlinarith [sq_nonneg b]
    _ = r ^ 2 * c ^ 2 := by ring
    _ ≤ (p : ℝ)⁻¹ * c ^ 2 := by
      rw [← hinvSq]
      gcongr
    _ = c ^ 2 / (p : ℝ) := by rw [div_eq_mul_inv]; ring

/-- Termwise Rankin stability on an arbitrary finite prime block. -/
theorem rankinBlockVariance_lower_of_radialWeight
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    {a : ℝ} (ha : 0 ≤ a) (t : ℝ)
    (hprime : ∀ p ∈ S, 64 ≤ p.1)
    (hweight : ∀ p ∈ S, (4 / 5 : ℝ) ≤ (p.1 : ℝ) ^ (-a)) :
    (15 / 16 : ℝ) * (4 / 5 : ℝ) *
        (∑ p ∈ S, Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1) ≤
      harperRankinLinearBlockVariance y S a t t := by
  unfold harperRankinLinearBlockVariance
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hpS
  exact fifteen_sixteenths_mul_weight_mul_cos_sq_div_le_rankinVariance
    (hprime p hpS) ha t (hweight p hpS)

/-- On a scheduled block, the critical lower variance plus the radial-weight
condition imply the shifted Gaussian lower threshold. -/
theorem one_fourth_lt_rankinScheduledBlockVariance_of_weight
    {y j : ℕ} {a : ℝ} (ha : 0 ≤ a) (t : ℝ)
    (hcritical : (1 / 3 : ℝ) <
      Problem520.harperLinearBlockVariance y
        (Problem520.harperScheduledPrimeBlock y j) t t)
    (hweight : ∀ p ∈ Problem520.harperScheduledPrimeBlock y j,
      (4 / 5 : ℝ) ≤ (p.1 : ℝ) ^ (-a)) :
    (1 / 4 : ℝ) < harperRankinLinearBlockVariance y
      (Problem520.harperScheduledPrimeBlock y j) a t t := by
  have hcosine : (1 / 3 : ℝ) <
      ∑ p ∈ Problem520.harperScheduledPrimeBlock y j,
        Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1 :=
    hcritical.trans_le (Problem520.blockVariance_le_cos_sq_sum y j t)
  have hlower := rankinBlockVariance_lower_of_radialWeight y
    (Problem520.harperScheduledPrimeBlock y j) ha t
    (fun p hpS ↦ Problem520.sixtyFour_le_prime_of_mem_harperScheduledPrimeBlock hpS)
    hweight
  norm_num at hlower ⊢
  nlinarith

/-- Uniform shifted variance window on every central-band scheduled block
whose Rankin radial weight is at least `4/5` prime by prime. -/
theorem exists_harperRankinScheduledCentralBandVarianceWindow :
    ∃ J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ a t : ℝ, 0 ≤ a →
          (∀ p ∈ Problem520.harperScheduledPrimeBlock y j,
            (4 / 5 : ℝ) ≤ (p.1 : ℝ) ^ (-a)) →
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            (1 / 4 : ℝ) < harperRankinLinearBlockVariance y
                (Problem520.harperScheduledPrimeBlock y j) a t t ∧
              harperRankinLinearBlockVariance y
                (Problem520.harperScheduledPrimeBlock y j) a t t < 3 / 8 := by
  obtain ⟨Jcritical, hcritical⟩ :=
    Problem520.exists_harperScheduledCentralBandDiagonalVariance_third_threeEighths
  obtain ⟨Jmass, hmass⟩ :=
    Problem520.exists_eventually_harperScheduledPrimeBlock_inv_close_log_two
      (by norm_num : (0 : ℝ) < 1 / 1000)
  obtain ⟨Josc, hosc⟩ :=
    Problem520.exists_harperScheduledCentralBandOscillation_le_milli
  refine ⟨max Jcritical (max Jmass Josc), ?_⟩
  intro d j y hj hy a t ha hweight htLower htUpper
  have hjcritical : Jcritical + d ≤ j := by omega
  have hjmass : Jmass ≤ j := by omega
  have hjosc : Josc + d ≤ j := by omega
  have hcriticalj := hcritical d j y hjcritical hy t htLower htUpper
  constructor
  · exact one_fourth_lt_rankinScheduledBlockVariance_of_weight ha t
      hcriticalj.1 hweight
  · let reciprocalMass : ℝ :=
      ∑ p ∈ Problem520.harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹
    let oscillatoryMass : ℝ :=
      ∑ p ∈ Problem520.harperScheduledPrimeBlock y j,
        Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1
    have hmassj : |reciprocalMass - Real.log 2| < (1 / 1000 : ℝ) :=
      hmass j hjmass y hy
    have hoscj : |oscillatoryMass| ≤ (1 / 1000 : ℝ) := by
      simpa only [oscillatoryMass, Problem520.harperScheduledOscillationMass] using
        hosc d j y hjosc hy t htLower htUpper
    have hblockUpper :
        harperRankinLinearBlockVariance y
            (Problem520.harperScheduledPrimeBlock y j) a t t ≤
          ∑ p ∈ Problem520.harperScheduledPrimeBlock y j,
            Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1 := by
      unfold harperRankinLinearBlockVariance
      apply Finset.sum_le_sum
      intro p hpS
      exact harperRankinCenteredLinearPrimeVariance_le_cos_sq_div
        (show 1 ≤ p.1 by
          have := Problem520.sixtyFour_le_prime_of_mem_harperScheduledPrimeBlock hpS
          omega) ha t
    have hcosineIdentity :
        (∑ p ∈ Problem520.harperScheduledPrimeBlock y j,
            Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1) =
          (1 / 2 : ℝ) * (reciprocalMass + oscillatoryMass) := by
      simpa only [reciprocalMass, oscillatoryMass] using
        Problem520.sum_harperScheduledPrimeBlock_cos_sq_div y j t
    rw [hcosineIdentity] at hblockUpper
    have hmassUpper := lt_of_abs_lt hmassj
    have hoscUpper := le_of_abs_le hoscj
    exact hblockUpper.trans_lt (by
      nlinarith [Real.log_two_lt_d9])

/-! ## Discharging the radial-weight condition by stopping early -/

/-- Every fixed Rankin parameter admits a finite number of top scheduled
blocks whose removal makes the radial loss at most `1/5`. -/
theorem exists_harperRankinRadialGap (V : ℝ) :
    ∃ gap : ℕ, 20 * V ≤ (2 : ℝ) ^ gap := by
  have ht : Tendsto (fun gap : ℕ ↦ (2 : ℝ) ^ gap) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent : ∀ᶠ gap : ℕ in atTop, 20 * V ≤ (2 : ℝ) ^ gap :=
    ht.eventually (eventually_ge_atTop (20 * V))
  obtain ⟨gap, hgap⟩ := eventually_atTop.1 hevent
  exact ⟨gap, hgap gap le_rfl⟩

/-- A stronger fixed radial gap, used by the two-height comparison.  The
larger constant leaves only a `1/20` loss in each prime variance. -/
theorem exists_harperRankinStrongRadialGap (V : ℝ) :
    ∃ gap : ℕ, 80 * V ≤ (2 : ℝ) ^ gap := by
  have ht : Tendsto (fun gap : ℕ ↦ (2 : ℝ) ^ gap) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hevent : ∀ᶠ gap : ℕ in atTop, 80 * V ≤ (2 : ℝ) ^ gap :=
    ht.eventually (eventually_ge_atTop (80 * V))
  obtain ⟨gap, hgap⟩ := eventually_atTop.1 hevent
  exact ⟨gap, hgap gap le_rfl⟩

/-- Moving `gap` scheduled scales upward multiplies the endpoint logarithm
by exactly `2^gap`. -/
theorem log_harperBlockEndpoint_add_gap
    (j gap : ℕ) :
    Real.log (Problem520.harperBlockEndpoint (j + gap + 1) : ℝ) =
      (2 : ℝ) ^ gap *
        Real.log (Problem520.harperBlockEndpoint (j + 1) : ℝ) := by
  rw [Problem520.log_harperBlockEndpoint_eq,
    Problem520.log_harperBlockEndpoint_eq]
  rw [show j + gap + 1 = (j + 1) + gap by omega, pow_add]
  ring

/-- If a scheduled block is a fixed number of scales below the ambient
cutoff, then the conventional Rankin shift retains at least `4/5` of every
prime's radial variance. -/
theorem harperRankinScheduledPrime_radialWeight_of_gap
    {V : ℝ} {gap : ℕ}
    (hgap : 20 * V ≤ (2 : ℝ) ^ gap)
    {j y : ℕ}
    (hy : Problem520.harperBlockEndpoint (j + gap + 1) ≤ y)
    (p : Problem520.HarperPrimeIndex y)
    (hpS : p ∈ Problem520.harperScheduledPrimeBlock y j) :
    (4 / 5 : ℝ) ≤
      (p.1 : ℝ) ^ (-(4 * V / Real.log (y : ℝ))) := by
  have hpNat : 1 ≤ p.1 := by
    have := Problem520.sixtyFour_le_prime_of_mem_harperScheduledPrimeBlock hpS
    omega
  have hpPos : (0 : ℝ) < (p.1 : ℝ) := by positivity
  have hpUpperNat :
      p.1 ≤ Problem520.harperBlockEndpoint (j + 1) :=
    ((Problem520.mem_harperScheduledPrimeBlock p).mp hpS).2
  have hpUpper :
      (p.1 : ℝ) ≤ (Problem520.harperBlockEndpoint (j + 1) : ℝ) := by
    exact_mod_cast hpUpperNat
  have hendpointPos :
      (0 : ℝ) < (Problem520.harperBlockEndpoint (j + 1) : ℝ) := by
    exact_mod_cast Problem520.harperBlockEndpoint_pos (j + 1)
  have hlogp :
      Real.log (p.1 : ℝ) ≤
        Real.log (Problem520.harperBlockEndpoint (j + 1) : ℝ) :=
    Real.log_le_log hpPos hpUpper
  have hlogpNonneg : 0 ≤ Real.log (p.1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hpNat)
  have hfarCast :
      (Problem520.harperBlockEndpoint (j + gap + 1) : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hy
  have hfarPos :
      (0 : ℝ) <
        (Problem520.harperBlockEndpoint (j + gap + 1) : ℝ) := by
    exact_mod_cast Problem520.harperBlockEndpoint_pos (j + gap + 1)
  have hlogFar :
      Real.log (Problem520.harperBlockEndpoint (j + gap + 1) : ℝ) ≤
        Real.log (y : ℝ) :=
    Real.log_le_log hfarPos hfarCast
  have hlogScale :
      (2 : ℝ) ^ gap *
          Real.log (Problem520.harperBlockEndpoint (j + 1) : ℝ) ≤
        Real.log (y : ℝ) := by
    rw [← log_harperBlockEndpoint_add_gap]
    exact hlogFar
  have hlogEndpointNonneg :
      0 ≤ Real.log (Problem520.harperBlockEndpoint (j + 1) : ℝ) :=
    Real.log_nonneg (by
      have hbase := Problem520.harperBlockEndpoint_ge_sixteen (j + 1)
      exact_mod_cast (show 1 ≤ Problem520.harperBlockEndpoint (j + 1) by omega))
  have htwenty :
      20 * V * Real.log (p.1 : ℝ) ≤ Real.log (y : ℝ) := by
    calc
      20 * V * Real.log (p.1 : ℝ) ≤
          (2 : ℝ) ^ gap * Real.log (p.1 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hgap hlogpNonneg
      _ ≤ (2 : ℝ) ^ gap *
          Real.log (Problem520.harperBlockEndpoint (j + 1) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlogp (by positivity)
      _ ≤ Real.log (y : ℝ) := hlogScale
  have hyOne : 1 < y := by
    have hbase := Problem520.harperBlockEndpoint_ge_sixteen (j + gap + 1)
    omega
  have hlogYPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hyOne)
  have hsmall :
      (4 * V / Real.log (y : ℝ)) * Real.log (p.1 : ℝ) ≤
        (1 / 5 : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hlogYPos).2
    nlinarith
  rw [Real.rpow_def_of_pos hpPos]
  have hexp := Real.one_sub_le_exp_neg
    ((4 * V / Real.log (y : ℝ)) * Real.log (p.1 : ℝ))
  calc
    (4 / 5 : ℝ) ≤
        1 - (4 * V / Real.log (y : ℝ)) * Real.log (p.1 : ℝ) := by
      linarith
    _ ≤ Real.exp
        (-((4 * V / Real.log (y : ℝ)) * Real.log (p.1 : ℝ))) := by
      exact hexp
    _ = Real.exp
        (Real.log (p.1 : ℝ) * (-(4 * V / Real.log (y : ℝ)))) := by
      congr 1
      ring

/-- Strong two-height version of the radial estimate: after a fixed larger
gap, the Rankin weight loses at most `1/20` at every prime in the retained
block. -/
theorem harperRankinScheduledPrime_radialWeight_of_strongGap
    {V : ℝ} {gap : ℕ}
    (hgap : 80 * V ≤ (2 : ℝ) ^ gap)
    {j y : ℕ}
    (hy : Problem520.harperBlockEndpoint (j + gap + 1) ≤ y)
    (p : Problem520.HarperPrimeIndex y)
    (hpS : p ∈ Problem520.harperScheduledPrimeBlock y j) :
    (19 / 20 : ℝ) ≤
      (p.1 : ℝ) ^ (-(4 * V / Real.log (y : ℝ))) := by
  have hpNat : 1 ≤ p.1 := by
    have := Problem520.sixtyFour_le_prime_of_mem_harperScheduledPrimeBlock hpS
    omega
  have hpPos : (0 : ℝ) < (p.1 : ℝ) := by positivity
  have hpUpperNat :
      p.1 ≤ Problem520.harperBlockEndpoint (j + 1) :=
    ((Problem520.mem_harperScheduledPrimeBlock p).mp hpS).2
  have hpUpper :
      (p.1 : ℝ) ≤ (Problem520.harperBlockEndpoint (j + 1) : ℝ) := by
    exact_mod_cast hpUpperNat
  have hendpointPos :
      (0 : ℝ) < (Problem520.harperBlockEndpoint (j + 1) : ℝ) := by
    exact_mod_cast Problem520.harperBlockEndpoint_pos (j + 1)
  have hlogp :
      Real.log (p.1 : ℝ) ≤
        Real.log (Problem520.harperBlockEndpoint (j + 1) : ℝ) :=
    Real.log_le_log hpPos hpUpper
  have hlogpNonneg : 0 ≤ Real.log (p.1 : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hpNat)
  have hfarCast :
      (Problem520.harperBlockEndpoint (j + gap + 1) : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hy
  have hfarPos :
      (0 : ℝ) <
        (Problem520.harperBlockEndpoint (j + gap + 1) : ℝ) := by
    exact_mod_cast Problem520.harperBlockEndpoint_pos (j + gap + 1)
  have hlogFar :
      Real.log (Problem520.harperBlockEndpoint (j + gap + 1) : ℝ) ≤
        Real.log (y : ℝ) :=
    Real.log_le_log hfarPos hfarCast
  have hlogScale :
      (2 : ℝ) ^ gap *
          Real.log (Problem520.harperBlockEndpoint (j + 1) : ℝ) ≤
        Real.log (y : ℝ) := by
    rw [← log_harperBlockEndpoint_add_gap]
    exact hlogFar
  have heighty :
      80 * V * Real.log (p.1 : ℝ) ≤ Real.log (y : ℝ) := by
    calc
      80 * V * Real.log (p.1 : ℝ) ≤
          (2 : ℝ) ^ gap * Real.log (p.1 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hgap hlogpNonneg
      _ ≤ (2 : ℝ) ^ gap *
          Real.log (Problem520.harperBlockEndpoint (j + 1) : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlogp (by positivity)
      _ ≤ Real.log (y : ℝ) := hlogScale
  have hyOne : 1 < y := by
    have hbase := Problem520.harperBlockEndpoint_ge_sixteen (j + gap + 1)
    omega
  have hlogYPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hyOne)
  have hsmall :
      (4 * V / Real.log (y : ℝ)) * Real.log (p.1 : ℝ) ≤
        (1 / 20 : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hlogYPos).2
    nlinarith
  rw [Real.rpow_def_of_pos hpPos]
  have hexp := Real.one_sub_le_exp_neg
    ((4 * V / Real.log (y : ℝ)) * Real.log (p.1 : ℝ))
  calc
    (19 / 20 : ℝ) ≤
        1 - (4 * V / Real.log (y : ℝ)) * Real.log (p.1 : ℝ) := by
      linarith
    _ ≤ Real.exp
        (-((4 * V / Real.log (y : ℝ)) * Real.log (p.1 : ℝ))) := by
      exact hexp
    _ = Real.exp
        (Real.log (p.1 : ℝ) * (-(4 * V / Real.log (y : ℝ)))) := by
      congr 1
      ring

/-- Fully arithmetic version of the shifted variance window: for each fixed
`V`, discard finitely many top blocks and the radial-weight premise of
`exists_harperRankinScheduledCentralBandVarianceWindow` is automatic. -/
theorem exists_gap_harperRankinScheduledCentralBandVarianceWindow
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ gap J : ℕ, ∀ d j y : ℕ, J + d ≤ j →
      Problem520.harperBlockEndpoint (j + gap + 1) ≤ y →
        ∀ t : ℝ,
          (1 / 2 : ℝ) ^ (d + 1) < |t| →
          |t| ≤ (1 / 2 : ℝ) ^ d →
            (1 / 4 : ℝ) < harperRankinLinearBlockVariance y
                (Problem520.harperScheduledPrimeBlock y j)
                (4 * V / Real.log (y : ℝ)) t t ∧
              harperRankinLinearBlockVariance y
                (Problem520.harperScheduledPrimeBlock y j)
                (4 * V / Real.log (y : ℝ)) t t < 3 / 8 := by
  obtain ⟨gap, hgap⟩ := exists_harperRankinRadialGap V
  obtain ⟨J, hwindow⟩ := exists_harperRankinScheduledCentralBandVarianceWindow
  refine ⟨gap, J, ?_⟩
  intro d j y hj hy t htLower htUpper
  have hyNear : Problem520.harperBlockEndpoint (j + 1) ≤ y := by
    exact (Problem520.monotone_harperBlockEndpoint (by omega)).trans hy
  have hyOne : 1 < y := by
    have hbase := Problem520.harperBlockEndpoint_ge_sixteen (j + gap + 1)
    omega
  have ha : 0 ≤ 4 * V / Real.log (y : ℝ) := by
    positivity
  exact hwindow d j y hj hyNear
    (4 * V / Real.log (y : ℝ)) t ha
    (fun p hpS ↦
      harperRankinScheduledPrime_radialWeight_of_gap hgap hy p hpS)
    htLower htUpper

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg
#print axioms Erdos.Problem1144.fifteen_sixteenths_mul_weight_mul_cos_sq_div_le_rankinVariance
#print axioms Erdos.Problem1144.rankinBlockVariance_lower_of_radialWeight
#print axioms Erdos.Problem1144.one_fourth_lt_rankinScheduledBlockVariance_of_weight
#print axioms Erdos.Problem1144.exists_harperRankinScheduledCentralBandVarianceWindow
#print axioms Erdos.Problem1144.exists_harperRankinRadialGap
#print axioms Erdos.Problem1144.harperRankinScheduledPrime_radialWeight_of_gap
#print axioms Erdos.Problem1144.exists_harperRankinStrongRadialGap
#print axioms Erdos.Problem1144.harperRankinScheduledPrime_radialWeight_of_strongGap
#print axioms Erdos.Problem1144.exists_gap_harperRankinScheduledCentralBandVarianceWindow
