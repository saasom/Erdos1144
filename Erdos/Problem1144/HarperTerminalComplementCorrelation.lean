import Erdos.Problem1144.HarperGaussianTerminalBallot

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Correlation cost of omitted scheduled blocks

The strengthened terminal-capped ballot supplies four reciprocal powers of the path
length.  This file begins the complementary deterministic estimate: a run of
`n` scheduled prime blocks contributes at most an absolute constant times
`4^n` to the two-height correlation on the lower vertical band.

The factor `4` is sharp at the exponent level.  The difference-frequency
part contributes twice the reciprocal-prime mass, namely
`2 * n * log 2`; the sum-frequency and square terms are summable errors.
-/

/-- Restricted form of the one-prime logarithmic correlation majorant. -/
theorem log_harperSubsetCorrelation_le
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    Real.log (harperSubsetCorrelation y S t s) <=
      ∑ p ∈ S,
        (4 * Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹ +
          12 * (p.1 : Real)⁻¹ ^ (2 : Nat)) := by
  rw [harperSubsetCorrelation, Real.log_prod]
  · exact Finset.sum_le_sum fun p _hp =>
      log_harperTwoHeightPrimeCorrelation_le
        (Nat.prime_of_mem_primesBelow p.property) t s
  · intro p _hp
    exact (harperTwoHeightPrimeCorrelation_pos
      (Nat.prime_of_mem_primesBelow p.property) t s).ne'

/-- The cross-height linear term is bounded by the two diagonal cosine-square
terms.  This is the finite-product Cauchy inequality in the form most useful
for scheduled arithmetic. -/
theorem log_harperSubsetCorrelation_le_diagonalCosineSq
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    Real.log (harperSubsetCorrelation y S t s) <=
      2 * (∑ p ∈ S,
        Real.cos (t * Real.log (p.1 : Real)) ^ (2 : Nat) /
          (p.1 : Real)) +
      2 * (∑ p ∈ S,
        Real.cos (s * Real.log (p.1 : Real)) ^ (2 : Nat) /
          (p.1 : Real)) +
      12 * (∑ p ∈ S, (p.1 : Real)⁻¹ ^ (2 : Nat)) := by
  refine (log_harperSubsetCorrelation_le y S t s).trans ?_
  calc
    (∑ p ∈ S,
        (4 * Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹ +
          12 * (p.1 : Real)⁻¹ ^ (2 : Nat))) <=
      ∑ p ∈ S,
        (2 * (Real.cos (t * Real.log (p.1 : Real)) ^ (2 : Nat) /
              (p.1 : Real)) +
          2 * (Real.cos (s * Real.log (p.1 : Real)) ^ (2 : Nat) /
              (p.1 : Real)) +
          12 * (p.1 : Real)⁻¹ ^ (2 : Nat)) := by
            apply Finset.sum_le_sum
            intro p hp
            have hp0 : (0 : Real) <= (p.1 : Real)⁻¹ := by positivity
            have hsq := sq_nonneg
              (Real.cos (t * Real.log (p.1 : Real)) -
                Real.cos (s * Real.log (p.1 : Real)))
            have hmul : 0 <=
                (Real.cos (t * Real.log (p.1 : Real)) -
                    Real.cos (s * Real.log (p.1 : Real))) ^ (2 : Nat) *
                  (p.1 : Real)⁻¹ := mul_nonneg hsq hp0
            rw [div_eq_mul_inv, div_eq_mul_inv]
            nlinarith
    _ = 2 * (∑ p ∈ S,
          Real.cos (t * Real.log (p.1 : Real)) ^ (2 : Nat) /
            (p.1 : Real)) +
        2 * (∑ p ∈ S,
          Real.cos (s * Real.log (p.1 : Real)) ^ (2 : Nat) /
            (p.1 : Real)) +
        12 * (∑ p ∈ S, (p.1 : Real)⁻¹ ^ (2 : Nat)) := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- Cosine-square decomposition on an arbitrary finite prime-coordinate
set. -/
theorem sum_harperSubset_cos_sq_div
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y)) (t : Real) :
    (∑ p ∈ S,
        Real.cos (t * Real.log (p.1 : Real)) ^ (2 : Nat) /
          (p.1 : Real)) =
      (1 / 2 : Real) *
        ((∑ p ∈ S, (p.1 : Real)⁻¹) +
          ∑ p ∈ S,
            Real.cos ((2 * t) * Real.log (p.1 : Real)) /
              (p.1 : Real)) := by
  rw [mul_add, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show (2 * t) * Real.log (p.1 : Real) =
      2 * (t * Real.log (p.1 : Real)) by ring,
    Real.cos_two_mul]
  ring

/-- Oscillatory mass is additive over a consecutive scheduled range. -/
theorem sum_harperScheduledOscillationMass_eq_rangeFrom
    (y start n : Nat) (tau : Real) :
    (∑ i : Fin n,
        Problem520.harperScheduledOscillationMass y
          (start + (i : Nat)) tau) =
      ∑ p ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
        Real.cos (tau * Real.log (p.1 : Real)) / (p.1 : Real) := by
  unfold Problem520.harperScheduledPrimeRangeFrom
    Problem520.harperScheduledOscillationMass
  rw [Finset.sum_biUnion
    (Problem520.pairwiseDisjoint_harperScheduledPrimeBlock_add
      y start n)]
  exact Fin.sum_univ_eq_sum_range
    (fun i : Nat =>
      ∑ p ∈ Problem520.harperScheduledPrimeBlock y (start + i),
        Real.cos (tau * Real.log (p.1 : Real)) / (p.1 : Real)) n

/-- Inverse-square mass is additive over a consecutive scheduled range. -/
theorem sum_harperScheduledSquareMass_eq_rangeFrom
    (y start n : Nat) :
    (∑ i : Fin n,
        Problem520.harperScheduledSquareMass y (start + (i : Nat))) =
      ∑ p ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
        (p.1 : Real)⁻¹ ^ (2 : Nat) := by
  unfold Problem520.harperScheduledPrimeRangeFrom
    Problem520.harperScheduledSquareMass
  rw [Finset.sum_biUnion
    (Problem520.pairwiseDisjoint_harperScheduledPrimeBlock_add
      y start n)]
  exact Fin.sum_univ_eq_sum_range
    (fun i : Nat =>
      ∑ p ∈ Problem520.harperScheduledPrimeBlock y (start + i),
        (p.1 : Real)⁻¹ ^ (2 : Nat)) n

/-- Product-to-sum decomposition of the linear two-height correlation over
a consecutive scheduled range. -/
theorem sum_harperScheduled_cross_eq_oscillation
    (y start n : Nat) (t s : Real) :
    (∑ p ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
        4 * Real.cos (t * Real.log (p.1 : Real)) *
          Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹) =
      2 * (∑ i : Fin n,
        Problem520.harperScheduledOscillationMass y
          (start + (i : Nat)) (t - s)) +
      2 * (∑ i : Fin n,
        Problem520.harperScheduledOscillationMass y
          (start + (i : Nat)) (t + s)) := by
  rw [sum_harperScheduledOscillationMass_eq_rangeFrom,
    sum_harperScheduledOscillationMass_eq_rangeFrom,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [show (t - s) * Real.log (p.1 : Real) =
      t * Real.log (p.1 : Real) - s * Real.log (p.1 : Real) by ring,
    show (t + s) * Real.log (p.1 : Real) =
      t * Real.log (p.1 : Real) + s * Real.log (p.1 : Real) by ring,
    Real.cos_sub, Real.cos_add]
  ring

/-- After the common-history scale of a dyadic height-gap shell, every
remaining consecutive range has uniformly bounded two-height correlation.
This is the arithmetic `buffer normalizer is bounded` estimate. -/
theorem exists_harperScheduledPostCommonRange_correlation_le_constant :
    ∃ D > 0, ∃ J : Nat,
      ∀ q start n y : Nat, J + (q + 1) ≤ start →
        Problem520.harperBlockEndpoint (start + n) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (q + 1) < |t - s| →
                harperSubsetCorrelation y
                    (Problem520.harperScheduledPrimeRangeFrom y start n)
                    t s ≤ D := by
  obtain ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, hcum⟩ :=
    Problem520.exists_harperScheduledDyadicCumulativeErrorBounds
  let Ttheta : Real :=
    ∑' j : Nat, Problem520.harperScheduledThetaEnvelope c C j
  let Tsquare : Real :=
    ∑' j : Nat, Problem520.harperScheduledSquareEnvelope j
  let K : Real := 4 * (8 + 7 * Ttheta) + 12 * Tsquare
  refine ⟨Real.exp K, Real.exp_pos K, J, ?_⟩
  intro q start n y hstart hy t ht s hs hsep
  let udiff : Real := (t - s) / 2
  let usum : Real := (t + s) / 2
  have hdiffLower : (1 / 2 : Real) ^ ((q + 1) + 1) < |udiff| := by
    calc
      (1 / 2 : Real) ^ ((q + 1) + 1) =
          (1 / 2 : Real) ^ (q + 1) / 2 := by
            rw [pow_succ]
            ring
      _ < |t - s| / 2 := div_lt_div_of_pos_right hsep (by norm_num)
      _ = |udiff| := by
        dsimp only [udiff]
        rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
  have hdiffUpper : |udiff| ≤ 1 := by
    rcases ht with ⟨htl, htu⟩
    rcases hs with ⟨hsl, hsu⟩
    have habs : |t - s| ≤ 1 / 6 := by
      rw [abs_le]
      constructor <;> linarith
    dsimp only [udiff]
    rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    linarith
  have hsumLower : (1 / 2 : Real) ^ (1 + 1) < |usum| := by
    have husumPos : 0 < usum := by
      dsimp only [usum]
      rcases ht with ⟨htl, _htu⟩
      rcases hs with ⟨hsl, _hsu⟩
      linarith
    rw [abs_of_pos husumPos]
    dsimp only [usum]
    norm_num
    rcases ht with ⟨htl, _htu⟩
    rcases hs with ⟨hsl, _hsu⟩
    linarith
  have hsumUpper : |usum| ≤ 1 := by
    have husumNonneg : 0 ≤ usum := by
      dsimp only [usum]
      rcases ht with ⟨htl, _htu⟩
      rcases hs with ⟨hsl, _hsu⟩
      linarith
    rw [abs_of_nonneg husumNonneg]
    dsimp only [usum]
    rcases ht with ⟨_htl, htu⟩
    rcases hs with ⟨_hsl, hsu⟩
    linarith
  have hdiff := hcum (q + 1) start n y hstart hy
    (fun _ : Fin n ↦ udiff) (fun _ : Fin n ↦ udiff)
    (fun _ ↦ hdiffLower) (fun _ ↦ hdiffUpper) (fun _ ↦ by simp)
  have hstartSum : J + 1 ≤ start := by omega
  have hsum := hcum 1 start n y hstartSum hy
    (fun _ : Fin n ↦ usum) (fun _ : Fin n ↦ usum)
    (fun _ ↦ hsumLower) (fun _ ↦ hsumUpper) (fun _ ↦ by simp)
  have hdiffTail :=
    Problem520.harperScheduledDyadicOscillationTail_le hc hC.le
      (show q + 1 ≤ start by omega)
  have hsumTail :=
    Problem520.harperScheduledDyadicOscillationTail_le hc hC.le
      (show 1 ≤ start by omega)
  have hsquareTail := Problem520.harperScheduledErrorTail_le_tsum
    Problem520.harperScheduledSquareEnvelope_nonneg
    Problem520.summable_harperScheduledSquareEnvelope start
  have hOd :
      ∑ i : Fin n,
          Problem520.harperScheduledOscillationMass y
            (start + (i : Nat)) (t - s) ≤ 8 + 7 * Ttheta := by
    calc
      _ ≤ ∑ i : Fin n,
          |Problem520.harperScheduledOscillationMass y
            (start + (i : Nat)) (t - s)| :=
        Finset.sum_le_sum fun i _hi ↦ le_abs_self _
      _ = ∑ i : Fin n,
          |Problem520.harperScheduledOscillationMass y
            (start + (i : Nat)) (2 * udiff)| := by
        congr 1
        funext i
        congr 2
        dsimp only [udiff]
        ring
      _ ≤ Problem520.harperScheduledErrorTail
          (Problem520.harperScheduledDyadicOscillationEnvelope
            (q + 1) c C) start := hdiff.2.1
      _ ≤ 8 + 7 * Ttheta := by simpa only [Ttheta] using hdiffTail
  have hOs :
      ∑ i : Fin n,
          Problem520.harperScheduledOscillationMass y
            (start + (i : Nat)) (t + s) ≤ 8 + 7 * Ttheta := by
    calc
      _ ≤ ∑ i : Fin n,
          |Problem520.harperScheduledOscillationMass y
            (start + (i : Nat)) (t + s)| :=
        Finset.sum_le_sum fun i _hi ↦ le_abs_self _
      _ = ∑ i : Fin n,
          |Problem520.harperScheduledOscillationMass y
            (start + (i : Nat)) (2 * usum)| := by
        congr 1
        funext i
        congr 2
        dsimp only [usum]
        ring
      _ ≤ Problem520.harperScheduledErrorTail
          (Problem520.harperScheduledDyadicOscillationEnvelope 1 c C)
            start := hsum.2.1
      _ ≤ 8 + 7 * Ttheta := by simpa only [Ttheta] using hsumTail
  have hQ :
      (∑ i : Fin n,
        Problem520.harperScheduledSquareMass y (start + (i : Nat))) ≤
          Tsquare := hdiff.2.2.trans (by
            simpa only [Tsquare] using hsquareTail)
  have hlog := log_harperSubsetCorrelation_le y
    (Problem520.harperScheduledPrimeRangeFrom y start n) t s
  rw [Finset.sum_add_distrib,
    sum_harperScheduled_cross_eq_oscillation] at hlog
  have hQset :
      (∑ x ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
          12 * (x.1 : Real)⁻¹ ^ (2 : Nat)) =
        12 * ∑ i : Fin n,
          Problem520.harperScheduledSquareMass y (start + (i : Nat)) := by
    calc
      _ = 12 * (∑ x ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
          (x.1 : Real)⁻¹ ^ (2 : Nat)) := by rw [Finset.mul_sum]
      _ = _ := by rw [sum_harperScheduledSquareMass_eq_rangeFrom]
  rw [hQset] at hlog
  have hlogK : Real.log (harperSubsetCorrelation y
      (Problem520.harperScheduledPrimeRangeFrom y start n) t s) ≤ K := by
    dsimp only [K]
    nlinarith
  rw [← Real.exp_log (harperSubsetCorrelation_pos y
    (Problem520.harperScheduledPrimeRangeFrom y start n) t s)]
  exact Real.exp_le_exp.mpr hlogK

/-- A consecutive run of `n` sufficiently late scheduled blocks costs at
most an absolute constant times `4^n` in two-height correlation, uniformly
on the lower vertical band. -/
theorem exists_harperScheduledRange_correlation_le_four_pow :
    ∃ B > 0, ∃ J : Nat,
      ∀ start n y : Nat, J + 1 <= start ->
        Problem520.harperBlockEndpoint (start + n) <= y ->
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              harperSubsetCorrelation y
                  (Problem520.harperScheduledPrimeRangeFrom y start n)
                  t s <=
                B * (4 : Real) ^ n := by
  obtain ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, hbound⟩ :=
    Problem520.exists_harperScheduledDyadicCumulativeErrorBounds
  let Erec : Real :=
    ∑' j : Nat, Problem520.harperScheduledReciprocalEnvelope c₀ C₀ j
  let Eosc : Real :=
    ∑' j : Nat,
      Problem520.harperScheduledDyadicOscillationEnvelope 1 c C j
  let Esq : Real :=
    ∑' j : Nat, Problem520.harperScheduledSquareEnvelope j
  let K : Real := 2 * Erec + 2 * Eosc + 12 * Esq
  refine ⟨Real.exp K, Real.exp_pos K, J, ?_⟩
  intro start n y hstart hy t ht s hs
  let S := Problem520.harperScheduledPrimeRangeFrom y start n
  let T : Real := ∑ i : Fin n,
    Problem520.harperScheduledReciprocalMass y (start + (i : Nat))
  let Ot : Real := ∑ i : Fin n,
    Problem520.harperScheduledOscillationMass y (start + (i : Nat)) (2 * t)
  let Os : Real := ∑ i : Fin n,
    Problem520.harperScheduledOscillationMass y (start + (i : Nat)) (2 * s)
  let Q : Real := ∑ i : Fin n,
    Problem520.harperScheduledSquareMass y (start + (i : Nat))
  have htBounds : (1 / 4 : Real) < |t| ∧ |t| <= 1 := by
    change (1 / 3 : Real) <= t ∧ t <= 1 / 2 at ht
    have ht0 : 0 <= t := by linarith
    rw [abs_of_nonneg ht0]
    constructor <;> linarith
  have hsBounds : (1 / 4 : Real) < |s| ∧ |s| <= 1 := by
    change (1 / 3 : Real) <= s ∧ s <= 1 / 2 at hs
    have hs0 : 0 <= s := by linarith
    rw [abs_of_nonneg hs0]
    constructor <;> linarith
  have htRaw := hbound 1 start n y hstart hy
    (fun _i : Fin n => t) (fun _i : Fin n => t)
    (fun _i => by norm_num; exact htBounds.1)
    (fun _i => htBounds.2) (fun _i => by simp)
  have hsRaw := hbound 1 start n y hstart hy
    (fun _i : Fin n => s) (fun _i : Fin n => s)
    (fun _i => by norm_num; exact hsBounds.1)
    (fun _i => hsBounds.2) (fun _i => by simp)
  have hrecTail :
      Problem520.harperScheduledErrorTail
          (Problem520.harperScheduledReciprocalEnvelope c₀ C₀) start <=
        Erec := by
    exact Problem520.harperScheduledErrorTail_le_tsum
      (Problem520.harperScheduledReciprocalEnvelope_nonneg hC₀.le)
      (Problem520.summable_harperScheduledReciprocalEnvelope hc₀ hC₀.le)
      start
  have hoscTail :
      Problem520.harperScheduledErrorTail
          (Problem520.harperScheduledDyadicOscillationEnvelope 1 c C) start <=
        Eosc := by
    exact Problem520.harperScheduledErrorTail_le_tsum
      (Problem520.harperScheduledDyadicOscillationEnvelope_nonneg 1 hC.le)
      (Problem520.summable_harperScheduledDyadicOscillationEnvelope
        1 hc hC.le) start
  have hsqTail :
      Problem520.harperScheduledErrorTail
          Problem520.harperScheduledSquareEnvelope start <= Esq := by
    exact Problem520.harperScheduledErrorTail_le_tsum
      Problem520.harperScheduledSquareEnvelope_nonneg
      Problem520.summable_harperScheduledSquareEnvelope start
  have hT : T <= (n : Real) * Real.log 2 + Erec := by
    have h := le_of_abs_le htRaw.1
    dsimp only [T]
    linarith
  have hOt : Ot <= Eosc := by
    have habsSum : |Ot| <= ∑ i : Fin n,
        |Problem520.harperScheduledOscillationMass y
          (start + (i : Nat)) (2 * t)| := by
      dsimp only [Ot]
      exact Finset.abs_sum_le_sum_abs _ _
    exact (le_abs_self Ot).trans
      (habsSum.trans (htRaw.2.1.trans hoscTail))
  have hOs : Os <= Eosc := by
    have habsSum : |Os| <= ∑ i : Fin n,
        |Problem520.harperScheduledOscillationMass y
          (start + (i : Nat)) (2 * s)| := by
      dsimp only [Os]
      exact Finset.abs_sum_le_sum_abs _ _
    exact (le_abs_self Os).trans
      (habsSum.trans (hsRaw.2.1.trans hoscTail))
  have hQ : Q <= Esq := by
    exact htRaw.2.2.trans hsqTail
  have hlog : Real.log (harperSubsetCorrelation y S t s) <=
      2 * (n : Real) * Real.log 2 + K := by
    have hbase := log_harperSubsetCorrelation_le_diagonalCosineSq
      y S t s
    rw [sum_harperSubset_cos_sq_div y S t,
      sum_harperSubset_cos_sq_div y S s] at hbase
    have hTset : (∑ p ∈ S, (p.1 : Real)⁻¹) = T := by
      simpa only [S, T] using
        sum_inv_harperScheduledPrimeRangeFrom_eq y start n
    have hOtset :
        (∑ p ∈ S,
          Real.cos ((2 * t) * Real.log (p.1 : Real)) /
            (p.1 : Real)) = Ot := by
      symm
      simpa only [S, Ot] using
        sum_harperScheduledOscillationMass_eq_rangeFrom y start n (2 * t)
    have hOsset :
        (∑ p ∈ S,
          Real.cos ((2 * s) * Real.log (p.1 : Real)) /
            (p.1 : Real)) = Os := by
      symm
      simpa only [S, Os] using
        sum_harperScheduledOscillationMass_eq_rangeFrom y start n (2 * s)
    have hQset : (∑ p ∈ S, (p.1 : Real)⁻¹ ^ (2 : Nat)) = Q := by
      symm
      simpa only [S, Q] using
        sum_harperScheduledSquareMass_eq_rangeFrom y start n
    rw [hTset, hOtset, hOsset, hQset] at hbase
    dsimp only [K]
    linarith
  rw [← Real.exp_log (harperSubsetCorrelation_pos y S t s)]
  calc
    Real.exp (Real.log (harperSubsetCorrelation y S t s)) <=
        Real.exp (2 * (n : Real) * Real.log 2 + K) :=
      Real.exp_le_exp.mpr hlog
    _ = Real.exp K * (4 : Real) ^ n := by
      rw [show 2 * (n : Real) * Real.log 2 =
          (n : Real) * (2 * Real.log 2) by ring,
        Real.exp_add, Real.exp_nat_mul,
        show Real.exp (2 * Real.log 2) = (4 : Real) by
          rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
            Real.exp_add, Real.exp_log (by norm_num : (0 : Real) < 2)]
          norm_num]
      ring

/-! ## From a scheduled range to the omitted prime prefix -/

/-- Prime coordinates below the lower endpoint of a scheduled path. -/
def harperScheduledPrimePrefix (y start : Nat) :
    Finset (Problem520.HarperPrimeIndex y) :=
  Problem520.harperPrimeCoordinates y
    (fun p => p <= Problem520.harperBlockEndpoint start)

@[simp] theorem mem_harperScheduledPrimePrefix
    {y start : Nat} (p : Problem520.HarperPrimeIndex y) :
    p ∈ harperScheduledPrimePrefix y start ↔
      p.1 <= Problem520.harperBlockEndpoint start := by
  simp [harperScheduledPrimePrefix]

/-- At an exact scheduled cutoff, the complement of a consecutive scheduled
range is literally its lower prime prefix; there is no upper tail. -/
theorem harperScheduledPrimeRangeFrom_compl_eq_prefix_of_endpoint_eq
    {y start n : Nat}
    (hy : Problem520.harperBlockEndpoint (start + n) = y) :
    (Problem520.harperScheduledPrimeRangeFrom y start n)ᶜ =
      harperScheduledPrimePrefix y start := by
  ext p
  have hpY : p.1 <= y := by
    have hp := Nat.mem_primesBelow.mp p.property
    omega
  simp only [Finset.mem_compl,
    Problem520.mem_harperScheduledPrimeRangeFrom,
    mem_harperScheduledPrimePrefix]
  rw [hy]
  omega

/-- At an exact final cutoff, the complement of an initial scheduled range
is the fixed lower prefix together with the later scheduled tail. -/
theorem harperScheduledPrimeRangeFrom_compl_eq_prefix_union_tail
    {y start r n : Nat} (hrn : r ≤ n)
    (hy : Problem520.harperBlockEndpoint (start + n) = y) :
    (Problem520.harperScheduledPrimeRangeFrom y start r)ᶜ =
      harperScheduledPrimePrefix y start ∪
        Problem520.harperScheduledPrimeRangeFrom y (start + r) (n - r) := by
  ext p
  have hpY : p.1 ≤ y := by
    have hp := Nat.mem_primesBelow.mp p.property
    omega
  simp only [Finset.mem_compl, Finset.mem_union,
    Problem520.mem_harperScheduledPrimeRangeFrom,
    mem_harperScheduledPrimePrefix]
  rw [show start + r + (n - r) = start + n by omega, hy]
  omega

/-- A scheduled prime prefix splits into one fixed initial prefix and the
consecutive scheduled range after it. -/
theorem harperScheduledPrimePrefix_eq_union_rangeFrom
    {y J start : Nat} (hJ : J <= start) :
    harperScheduledPrimePrefix y start =
      harperScheduledPrimePrefix y J ∪
        Problem520.harperScheduledPrimeRangeFrom y J (start - J) := by
  have hendpoint : Problem520.harperBlockEndpoint J <=
      Problem520.harperBlockEndpoint start :=
    Problem520.monotone_harperBlockEndpoint hJ
  ext p
  simp only [mem_harperScheduledPrimePrefix, Finset.mem_union,
    Problem520.mem_harperScheduledPrimeRangeFrom]
  rw [show J + (start - J) = start by omega]
  omega

theorem disjoint_harperScheduledPrimePrefix_rangeFrom
    (y J n : Nat) :
    Disjoint (harperScheduledPrimePrefix y J)
      (Problem520.harperScheduledPrimeRangeFrom y J n) := by
  rw [Finset.disjoint_left]
  intro p hpPrefix hpRange
  have hpUpper := (mem_harperScheduledPrimePrefix p).mp hpPrefix
  have hpLower :=
    (Problem520.mem_harperScheduledPrimeRangeFrom p).mp hpRange |>.1
  omega

/-- Restricted correlation is multiplicative on disjoint coordinate sets. -/
theorem harperSubsetCorrelation_union
    (y : Nat) {S T : Finset (Problem520.HarperPrimeIndex y)}
    (hdis : Disjoint S T) (t s : Real) :
    harperSubsetCorrelation y (S ∪ T) t s =
      harperSubsetCorrelation y S t s *
        harperSubsetCorrelation y T t s := by
  unfold harperSubsetCorrelation
  exact Finset.prod_union hdis

/-- A deliberately coarse bound for a fixed finite prefix.  Its only role is
to absorb the finitely many blocks before the strong-PNT schedule begins. -/
theorem harperScheduledPrimePrefix_correlation_le_exp_card
    (y start : Nat) (t s : Real) :
    harperSubsetCorrelation y (harperScheduledPrimePrefix y start) t s <=
      Real.exp
        (16 * ((Problem520.harperBlockEndpoint start + 1 : Nat) : Real)) := by
  let P := harperScheduledPrimePrefix y start
  let e : Problem520.HarperPrimeIndex y ↪ Nat :=
    ⟨fun p => p.1, fun _ _ h => Subtype.ext h⟩
  have hcard : P.card <= Problem520.harperBlockEndpoint start + 1 := by
    have hsubset : P.map e ⊆
        Finset.range (Problem520.harperBlockEndpoint start + 1) := by
      intro q hq
      obtain ⟨p, hpP, rfl⟩ := Finset.mem_map.mp hq
      have hp := (mem_harperScheduledPrimePrefix p).mp hpP
      simpa only [Finset.mem_range, e] using Nat.lt_succ_of_le hp
    have := Finset.card_le_card hsubset
    simpa only [Finset.card_map, Finset.card_range] using this
  have hterm : ∀ p ∈ P,
      4 * Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹ +
          12 * (p.1 : Real)⁻¹ ^ (2 : Nat) <= 16 := by
    intro p hpP
    have hpPrime := Nat.prime_of_mem_primesBelow p.property
    have hpTwo : (2 : Real) <= p.1 := by exact_mod_cast hpPrime.two_le
    have hinv0 : (0 : Real) <= (p.1 : Real)⁻¹ := by positivity
    have hinv1 : (p.1 : Real)⁻¹ <= 1 := by
      exact (inv_le_one₀ (by positivity)).2 (by linarith)
    have hct : |Real.cos (t * Real.log (p.1 : Real))| <= 1 :=
      Real.abs_cos_le_one _
    have hcs : |Real.cos (s * Real.log (p.1 : Real))| <= 1 :=
      Real.abs_cos_le_one _
    have hprod : Real.cos (t * Real.log (p.1 : Real)) *
        Real.cos (s * Real.log (p.1 : Real)) <= 1 := by
      calc
        Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) <=
          |Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real))| := le_abs_self _
        _ = |Real.cos (t * Real.log (p.1 : Real))| *
            |Real.cos (s * Real.log (p.1 : Real))| := abs_mul _ _
        _ <= 1 * 1 := mul_le_mul hct hcs (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hlinear : 4 *
        (Real.cos (t * Real.log (p.1 : Real)) *
          Real.cos (s * Real.log (p.1 : Real))) *
          (p.1 : Real)⁻¹ <= 4 := by
      calc
        4 * (Real.cos (t * Real.log (p.1 : Real)) *
              Real.cos (s * Real.log (p.1 : Real))) *
            (p.1 : Real)⁻¹ <=
          4 * 1 * (p.1 : Real)⁻¹ := by gcongr
        _ <= 4 * 1 * 1 := by gcongr
        _ = 4 := by norm_num
    have hsquare : 12 * (p.1 : Real)⁻¹ ^ (2 : Nat) <= 12 := by
      nlinarith [sq_nonneg ((p.1 : Real)⁻¹),
        mul_self_le_mul_self (by positivity : (0 : Real) <= (p.1 : Real)⁻¹)
          hinv1]
    nlinarith
  have hlog : Real.log (harperSubsetCorrelation y P t s) <=
      16 * ((Problem520.harperBlockEndpoint start + 1 : Nat) : Real) := by
    calc
      Real.log (harperSubsetCorrelation y P t s) <=
          ∑ p ∈ P,
            (4 * Real.cos (t * Real.log (p.1 : Real)) *
                Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹ +
              12 * (p.1 : Real)⁻¹ ^ (2 : Nat)) :=
        log_harperSubsetCorrelation_le y P t s
      _ <= ∑ _p ∈ P, (16 : Real) := Finset.sum_le_sum hterm
      _ = 16 * (P.card : Real) := by simp [mul_comm]
      _ <= 16 * ((Problem520.harperBlockEndpoint start + 1 : Nat) : Real) := by
        gcongr
  rw [← Real.exp_log (harperSubsetCorrelation_pos y P t s)]
  exact Real.exp_le_exp.mpr hlog

/-- The entire omitted lower prefix costs `O(4^start)`.  The constant absorbs
the fixed pre-PNT prefix, while the late scheduled portion uses the sharp
range estimate above. -/
theorem exists_harperScheduledPrimePrefix_correlation_le_four_pow :
    ∃ D > 0, ∃ J₀ : Nat, ∀ start y : Nat, J₀ <= start ->
      Problem520.harperBlockEndpoint start <= y ->
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            harperSubsetCorrelation y
                (harperScheduledPrimePrefix y start) t s <=
              D * (4 : Real) ^ start := by
  obtain ⟨B, hB, J, hrange⟩ :=
    exists_harperScheduledRange_correlation_le_four_pow
  let J₀ : Nat := J + 1
  let D : Real :=
    Real.exp
      (16 * ((Problem520.harperBlockEndpoint J₀ + 1 : Nat) : Real)) * B
  refine ⟨D, mul_pos (Real.exp_pos _) hB, J₀, ?_⟩
  intro start y hstart hy t ht s hs
  let P₀ := harperScheduledPrimePrefix y J₀
  let R := Problem520.harperScheduledPrimeRangeFrom y J₀ (start - J₀)
  have hsplit : harperScheduledPrimePrefix y start = P₀ ∪ R := by
    simpa only [P₀, R] using
      harperScheduledPrimePrefix_eq_union_rangeFrom (y := y) hstart
  have hdis : Disjoint P₀ R := by
    simpa only [P₀, R] using
      disjoint_harperScheduledPrimePrefix_rangeFrom y J₀ (start - J₀)
  have hendpoint : Problem520.harperBlockEndpoint (J₀ + (start - J₀)) <= y := by
    simpa only [show J₀ + (start - J₀) = start by omega] using hy
  have hinitial : harperSubsetCorrelation y P₀ t s <=
      Real.exp
        (16 * ((Problem520.harperBlockEndpoint J₀ + 1 : Nat) : Real)) := by
    simpa only [P₀] using
      harperScheduledPrimePrefix_correlation_le_exp_card y J₀ t s
  have hlate : harperSubsetCorrelation y R t s <=
      B * (4 : Real) ^ (start - J₀) := by
    simpa only [R] using
      hrange J₀ (start - J₀) y (by simp [J₀]) hendpoint t ht s hs
  rw [hsplit, harperSubsetCorrelation_union y hdis]
  calc
    harperSubsetCorrelation y P₀ t s *
        harperSubsetCorrelation y R t s <=
      Real.exp
          (16 * ((Problem520.harperBlockEndpoint J₀ + 1 : Nat) : Real)) *
        (B * (4 : Real) ^ (start - J₀)) := by
          exact mul_le_mul hinitial hlate
            (harperSubsetCorrelation_pos y R t s).le (by positivity)
    _ <= D * (4 : Real) ^ start := by
      dsimp only [D]
      have hpow : (4 : Real) ^ (start - J₀) <= (4 : Real) ^ start := by
        exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le start J₀)
      calc
        Real.exp
              (16 * ((Problem520.harperBlockEndpoint J₀ + 1 : Nat) : Real)) *
            (B * (4 : Real) ^ (start - J₀)) =
          (Real.exp
              (16 * ((Problem520.harperBlockEndpoint J₀ + 1 : Nat) : Real)) *
            B) * (4 : Real) ^ (start - J₀) := by ring
        _ <= (Real.exp
              (16 * ((Problem520.harperBlockEndpoint J₀ + 1 : Nat) : Real)) *
            B) * (4 : Real) ^ start :=
          mul_le_mul_of_nonneg_left hpow
            (mul_nonneg (Real.exp_pos _).le hB.le)

/-- Shell-aware complement bound.  After exposing enough blocks to pass the
common-history cutoff, the upper tail has constant correlation cost; the only
remaining loss is the correlation of the omitted lower prefix, displayed
explicitly as `4^start`. -/
theorem exists_harperScheduledPrefixComplement_shell_le_four_pow_start :
    ∃ D > 0, ∃ J : Nat,
      ∀ q start r n y : Nat, J ≤ start → r ≤ n →
        J + (q + 1) ≤ start + r →
        Problem520.harperBlockEndpoint (start + n) = y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (q + 1) < |t - s| →
                harperSubsetCorrelation y
                    (Problem520.harperScheduledPrimeRangeFrom y start r)ᶜ
                    t s ≤ D * (4 : Real) ^ start := by
  obtain ⟨D₀, hD₀, J₀, hprefix⟩ :=
    exists_harperScheduledPrimePrefix_correlation_le_four_pow
  obtain ⟨D₁, hD₁, J₁, htail⟩ :=
    exists_harperScheduledPostCommonRange_correlation_le_constant
  let D : Real := D₀ * D₁
  let J : Nat := max J₀ J₁
  refine ⟨D, mul_pos hD₀ hD₁, J, ?_⟩
  intro q start r n y hstart hrn hcoh hy t ht s hs hsep
  have hstart₀ : J₀ ≤ start := (le_max_left J₀ J₁).trans hstart
  have hstart₁ : J₁ + (q + 1) ≤ start + r := by
    have hJ₁ : J₁ ≤ J := le_max_right J₀ J₁
    omega
  have hstartEndpoint : Problem520.harperBlockEndpoint start ≤ y :=
    (Problem520.monotone_harperBlockEndpoint (show start ≤ start + n by omega)).trans_eq hy
  have htailEndpoint :
      Problem520.harperBlockEndpoint (start + r + (n - r)) ≤ y := by
    simpa only [show start + r + (n - r) = start + n by omega] using hy.le
  have hpref := hprefix start y hstart₀ hstartEndpoint t ht s hs
  have hlate := htail q (start + r) (n - r) y hstart₁
    htailEndpoint t ht s hs hsep
  have hdis : Disjoint (harperScheduledPrimePrefix y start)
      (Problem520.harperScheduledPrimeRangeFrom y (start + r) (n - r)) := by
    rw [Finset.disjoint_left]
    intro p hpPrefix hpTail
    have hpUpper := (mem_harperScheduledPrimePrefix p).mp hpPrefix
    have hpLower :=
      (Problem520.mem_harperScheduledPrimeRangeFrom p).mp hpTail |>.1
    have hendpointMono : Problem520.harperBlockEndpoint start ≤
        Problem520.harperBlockEndpoint (start + r) :=
      Problem520.monotone_harperBlockEndpoint (by omega)
    omega
  rw [harperScheduledPrimeRangeFrom_compl_eq_prefix_union_tail hrn hy,
    harperSubsetCorrelation_union y hdis]
  calc
    harperSubsetCorrelation y (harperScheduledPrimePrefix y start) t s *
        harperSubsetCorrelation y
          (Problem520.harperScheduledPrimeRangeFrom y (start + r) (n - r))
          t s ≤
      (D₀ * (4 : Real) ^ start) * D₁ :=
        mul_le_mul hpref hlate
          (harperSubsetCorrelation_pos y _ t s).le (by positivity)
    _ = D * (4 : Real) ^ start := by
      dsimp only [D]
      ring

/-- Exact-cutoff form needed by the terminal-capped ballot: all correlation
outside the near-full path is bounded by the lower-prefix guard cost. -/
theorem exists_harperTerminal_complementCorrelation_le_four_pow :
    ∃ D > 0, ∃ J₀ : Nat, ∀ start n y : Nat, J₀ <= start ->
      Problem520.harperBlockEndpoint (start + n) = y ->
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            harperSubsetCorrelation y
                (Problem520.harperScheduledPrimeRangeFrom y start n)ᶜ t s <=
              D * (4 : Real) ^ start := by
  obtain ⟨D, hD, J₀, hprefix⟩ :=
    exists_harperScheduledPrimePrefix_correlation_le_four_pow
  refine ⟨D, hD, J₀, ?_⟩
  intro start n y hstart hy t ht s hs
  rw [harperScheduledPrimeRangeFrom_compl_eq_prefix_of_endpoint_eq hy]
  have hendpoint : Problem520.harperBlockEndpoint start <= y :=
    (Problem520.monotone_harperBlockEndpoint (by omega)).trans_eq hy
  exact hprefix start y hstart hendpoint t ht s hs

/-- Combining terminal likelihood localization with the omitted-prefix
estimate leaves exactly the factor `2^n * 4^start / n^4`. -/
theorem
    exists_harperTerminalCapped_correlation_probability_le_powTwo_mul_four_pow_div_sq :
    ∃ C > 0, ∃ J₀ : Nat, ∀ start n y : Nat, J₀ <= start ->
      0 < n -> Problem520.harperBlockEndpoint (start + n) = y ->
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            harperTwoHeightCorrelation y t s *
                (harperTwoHeightCubeLaw y t s).real
                  (harperTerminalCappedCentralLowerBallotCubeEvent
                      y start n t ∩
                    harperTerminalCappedCentralLowerBallotCubeEvent
                      y start n s) <=
              C * (2 : Real) ^ n * (n : Real)⁻¹ *
                (n : Real)⁻¹ * (n : Real)⁻¹ *
                (n : Real)⁻¹ * (4 : Real) ^ start := by
  obtain ⟨B, hB, Jballot, hballot⟩ :=
    exists_harperTerminalCapped_correlation_probability_le_powTwo_div_compl
  obtain ⟨D, hD, Jcorr, hcorr⟩ :=
    exists_harperTerminal_complementCorrelation_le_four_pow
  let C : Real := B * D
  let J₀ : Nat := max (Jballot + 1) Jcorr
  refine ⟨C, mul_pos hB hD, J₀, ?_⟩
  intro start n y hstart hn hy t ht s hs
  have hstartBallot : Jballot + 1 <= start :=
    (le_max_left _ _).trans hstart
  have hstartCorr : Jcorr <= start :=
    (le_max_right _ _).trans hstart
  have hloc := hballot start n y hstartBallot hn hy.le t ht s hs
  have hcomp := hcorr start n y hstartCorr hy t ht s hs
  calc
    harperTwoHeightCorrelation y t s *
          (harperTwoHeightCubeLaw y t s).real
            (harperTerminalCappedCentralLowerBallotCubeEvent y start n t ∩
              harperTerminalCappedCentralLowerBallotCubeEvent y start n s) <=
        B * (2 : Real) ^ n * (n : Real)⁻¹ * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (n : Real)⁻¹ *
          harperSubsetCorrelation y
            (Problem520.harperScheduledPrimeRangeFrom y start n)ᶜ t s := hloc
    _ <= B * (2 : Real) ^ n * (n : Real)⁻¹ * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (n : Real)⁻¹ *
          (D * (4 : Real) ^ start) := by
      exact mul_le_mul_of_nonneg_left hcomp (by positivity)
    _ = C * (2 : Real) ^ n * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (4 : Real) ^ start := by
      dsimp only [C]
      ring

/-- If the guard is chosen so that `4^start = O(n)`, the strengthened
terminal cap pays for the entire omitted-prefix correlation with two spare
reciprocal powers, and in particular gives the desired `2^n / n` scale. -/
theorem
    exists_harperTerminalCapped_correlation_probability_le_powTwo_div_of_guard :
    ∃ C > 0, ∃ J₀ : Nat, ∀ start n y : Nat, J₀ <= start ->
      0 < n -> Problem520.harperBlockEndpoint (start + n) = y ->
        ∀ G : Real, 0 <= G -> (4 : Real) ^ start <= G * (n : Real) ->
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              harperTwoHeightCorrelation y t s *
                  (harperTwoHeightCubeLaw y t s).real
                    (harperTerminalCappedCentralLowerBallotCubeEvent
                        y start n t ∩
                      harperTerminalCappedCentralLowerBallotCubeEvent
                        y start n s) <=
                (C * G) * (2 : Real) ^ n * (n : Real)⁻¹ := by
  obtain ⟨C, hC, J₀, hmain⟩ :=
    exists_harperTerminalCapped_correlation_probability_le_powTwo_mul_four_pow_div_sq
  refine ⟨C, hC, J₀, ?_⟩
  intro start n y hstart hn hy G hG hguard t ht s hs
  have hbase := hmain start n y hstart hn hy t ht s hs
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  calc
    harperTwoHeightCorrelation y t s *
          (harperTwoHeightCubeLaw y t s).real
            (harperTerminalCappedCentralLowerBallotCubeEvent y start n t ∩
              harperTerminalCappedCentralLowerBallotCubeEvent y start n s) <=
        C * (2 : Real) ^ n * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (4 : Real) ^ start := hbase
    _ <= C * (2 : Real) ^ n * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (G * (n : Real)) := by
      exact mul_le_mul_of_nonneg_left hguard (by positivity)
    _ = (C * G) * (2 : Real) ^ n * (n : Real)⁻¹ *
          (n : Real)⁻¹ * (n : Real)⁻¹ := by
      field_simp
    _ <= (C * G) * (2 : Real) ^ n * (n : Real)⁻¹ := by
      have hnOne : (1 : Real) <= (n : Real) := by exact_mod_cast hn
      have hinvLe : (n : Real)⁻¹ <= 1 :=
        (inv_le_one₀ hnR).2 hnOne
      calc
        (C * G) * (2 : Real) ^ n * (n : Real)⁻¹ *
              (n : Real)⁻¹ * (n : Real)⁻¹ <=
            (C * G) * (2 : Real) ^ n * (n : Real)⁻¹ * 1 * 1 := by
          gcongr
        _ = (C * G) * (2 : Real) ^ n * (n : Real)⁻¹ := by ring

/-! ## The half-logarithmic guard -/

/-- Canonical path start: a fixed analytic threshold plus the base-four
ceiling logarithm of the path length. -/
def harperTerminalGuardStart (J n : Nat) : Nat :=
  J + Nat.clog 4 n

/-- The base-four ceiling is within one factor of four of its argument. -/
theorem pow_clog_four_le_four_mul
    {n : Nat} (hn : 0 < n) :
    4 ^ Nat.clog 4 n <= 4 * n := by
  by_cases hnOne : n <= 1
  · have hnEq : n = 1 := by omega
    subst n
    norm_num
  · have hnTwo : 1 < n := lt_of_not_ge hnOne
    have hclog : 0 < Nat.clog 4 n :=
      Nat.clog_pos (by norm_num) hnTwo
    have hpred : 4 ^ (Nat.clog 4 n).pred < n :=
      Nat.pow_pred_clog_lt_self (by norm_num) hnTwo
    rw [← Nat.succ_pred_eq_of_pos hclog, pow_succ]
    omega

/-- The canonical guard has exactly the growth needed by the complement
correlation theorem. -/
theorem four_pow_harperTerminalGuardStart_le
    (J : Nat) {n : Nat} (hn : 0 < n) :
    (4 : Real) ^ harperTerminalGuardStart J n <=
      (4 : Real) ^ (J + 1) * (n : Real) := by
  have hclogNat := pow_clog_four_le_four_mul hn
  have hclogReal : (4 : Real) ^ Nat.clog 4 n <= 4 * (n : Real) := by
    exact_mod_cast hclogNat
  unfold harperTerminalGuardStart
  rw [pow_add, pow_succ]
  nlinarith [show 0 <= (4 : Real) ^ J by positivity]

/-- The same half-logarithmic guard makes the crude Gaussian moderate-box
tail smaller than one quarter of the ballot mass.  The fixed threshold `12`
is deliberately coarse. -/
theorem harperTerminalGuardStart_gaussian_box_budget
    {J n : Nat} (hJ : 12 <= J) (hn : 0 < n) :
    64 * (1 / 2 : Real) ^ harperTerminalGuardStart J n <=
      (1 / 4 : Real) *
        (Real.exp (-2) / Real.sqrt (n : Real)) := by
  let k := Nat.clog 4 n
  have hnpowNat : n <= 4 ^ k := by
    dsimp only [k]
    exact Nat.le_pow_clog (by norm_num) n
  have hnpowReal : (n : Real) <= (4 : Real) ^ k := by
    exact_mod_cast hnpowNat
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hsqrtPos : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.2 hnR
  have htwoPowPos : 0 < (2 : Real) ^ k := by positivity
  have hsq : ((2 : Real) ^ k) ^ (2 : Nat) = (4 : Real) ^ k := by
    calc
      ((2 : Real) ^ k) ^ (2 : Nat) =
          (2 : Real) ^ (k * 2) := (pow_mul _ k 2).symm
      _ = (2 : Real) ^ (2 * k) := by rw [Nat.mul_comm]
      _ = ((2 : Real) ^ (2 : Nat)) ^ k := pow_mul _ 2 k
      _ = (4 : Real) ^ k := by norm_num
  have hsqrt : Real.sqrt (n : Real) <= (2 : Real) ^ k := by
    rw [Real.sqrt_le_iff]
    exact ⟨htwoPowPos.le, by simpa only [hsq] using hnpowReal⟩
  have hinv : (1 / 2 : Real) ^ k <=
      1 / Real.sqrt (n : Real) := by
    rw [one_div_pow]
    exact one_div_le_one_div_of_le hsqrtPos hsqrt
  have hfixed : (1 / 2 : Real) ^ J <= (1 / 2 : Real) ^ 12 := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hJ
  have hcoeff : 64 * (1 / 2 : Real) ^ J <= 1 / 64 := by
    calc
      64 * (1 / 2 : Real) ^ J <= 64 * (1 / 2 : Real) ^ 12 := by gcongr
      _ = 1 / 64 := by norm_num
  have hexpCoeff : (1 / 64 : Real) <=
      (1 / 4 : Real) * Real.exp (-2) := by
    have h := one_ninth_le_exp_neg_two
    nlinarith
  unfold harperTerminalGuardStart
  rw [pow_add]
  calc
    64 * ((1 / 2 : Real) ^ J * (1 / 2 : Real) ^ k) =
        (64 * (1 / 2 : Real) ^ J) * (1 / 2 : Real) ^ k := by ring
    _ <= (1 / 64 : Real) * (1 / Real.sqrt (n : Real)) := by
      exact mul_le_mul hcoeff hinv (by positivity) (by positivity)
    _ <= ((1 / 4 : Real) * Real.exp (-2)) *
        (1 / Real.sqrt (n : Real)) := by
      exact mul_le_mul_of_nonneg_right hexpCoeff (by positivity)
    _ = (1 / 4 : Real) *
        (Real.exp (-2) / Real.sqrt (n : Real)) := by ring

/-! ## Unconditional scheduled one- and two-height outputs -/

/-- The canonical guarded exact-cutoff schedule satisfies the completed
one-height terminal-ballot lower bound. -/
theorem
    exists_harperTerminalGuarded_oneHeight_lower :
    ∃ J m₀ : Nat, ∀ m : Nat, m₀ <= m ->
      let n := m + m
      let start := harperTerminalGuardStart J n
      let y := Problem520.harperBlockEndpoint (start + n)
      ∀ t ∈ harperLowerVerticalBand,
        (3 / 16 : Real) *
            (Real.exp (-2) / Real.sqrt (n : Real)) <=
          (Problem520.harperTiltedCubeLaw y t).real
            (harperTerminalCappedCentralLowerBallotCubeEvent
              y start n t) := by
  obtain ⟨Jballot, m₀, hballot⟩ :=
    exists_eventually_three_sixteenths_mul_exp_neg_two_div_sqrt_le_harperTiltedCubeLaw_terminalCappedBallot
  let J : Nat := max 12 (Jballot + 1)
  refine ⟨J, max 1 m₀, ?_⟩
  intro m hm
  dsimp only
  let n : Nat := m + m
  let start : Nat := harperTerminalGuardStart J n
  let y : Nat := Problem520.harperBlockEndpoint (start + n)
  have hm₀ : m₀ <= m := (le_max_right 1 m₀).trans hm
  have hmpos : 0 < m := by
    have : 1 <= m := (le_max_left 1 m₀).trans hm
    omega
  have hnpos : 0 < n := by dsimp only [n]; omega
  have hJ12 : 12 <= J := le_max_left _ _
  have hJballot : Jballot + 1 <= J := le_max_right _ _
  have hstart : Jballot + 1 <= start := by
    exact hJballot.trans (Nat.le_add_right J (Nat.clog 4 n))
  have hbudget : 64 * (1 / 2 : Real) ^ start <=
      (1 / 4 : Real) *
        (Real.exp (-2) / Real.sqrt (n : Real)) := by
    simpa only [start] using
      harperTerminalGuardStart_gaussian_box_budget hJ12 hnpos
  intro t ht
  have ht' : (1 / 3 : Real) <= t ∧ t <= 1 / 2 := ht
  have ht0 : 0 <= t := by linarith
  have htLower : (1 / 2 : Real) ^ (1 + 1) < |t| := by
    rw [abs_of_nonneg ht0]
    norm_num
    linarith
  have htUpper : |t| <= (1 / 2 : Real) ^ 1 := by
    rw [abs_of_nonneg ht0]
    norm_num
    exact ht'.2
  have h := hballot 1 start hstart m hm₀ y (by rfl) t
    htLower htUpper
  simpa only [n, start, y] using h hbudget

/-- The canonical guarded exact-cutoff schedule also satisfies the sharp
two-height `2^n / n` bound. -/
theorem
    exists_harperTerminalGuarded_twoHeight_upper :
    ∃ C > 0, ∃ J : Nat, ∀ n : Nat, 0 < n ->
      let start := harperTerminalGuardStart J n
      let y := Problem520.harperBlockEndpoint (start + n)
      ∀ t ∈ harperLowerVerticalBand,
        ∀ s ∈ harperLowerVerticalBand,
          harperTwoHeightCorrelation y t s *
              (harperTwoHeightCubeLaw y t s).real
                (harperTerminalCappedCentralLowerBallotCubeEvent
                    y start n t ∩
                  harperTerminalCappedCentralLowerBallotCubeEvent
                    y start n s) <=
            C * (2 : Real) ^ n * (n : Real)⁻¹ := by
  obtain ⟨C₀, hC₀, J₀, hmain⟩ :=
    exists_harperTerminalCapped_correlation_probability_le_powTwo_div_of_guard
  let J : Nat := J₀
  let G : Real := (4 : Real) ^ (J + 1)
  let C : Real := C₀ * G
  refine ⟨C, mul_pos hC₀ (by positivity), J, ?_⟩
  intro n hn
  dsimp only
  let start := harperTerminalGuardStart J n
  let y := Problem520.harperBlockEndpoint (start + n)
  have hstart : J₀ <= start := by
    exact Nat.le_add_right J₀ (Nat.clog 4 n)
  have hguard : (4 : Real) ^ start <= G * (n : Real) := by
    simpa only [start, G] using
      four_pow_harperTerminalGuardStart_le J hn
  intro t ht s hs
  have h := hmain start n y hstart hn (by rfl) G (by positivity)
    hguard t ht s hs
  simpa only [C, start, y] using h

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.log_harperSubsetCorrelation_le_diagonalCosineSq
#print axioms Erdos.Problem1144.sum_harperScheduled_cross_eq_oscillation
#print axioms Erdos.Problem1144.exists_harperScheduledPostCommonRange_correlation_le_constant
#print axioms Erdos.Problem1144.exists_harperScheduledRange_correlation_le_four_pow
#print axioms Erdos.Problem1144.exists_harperScheduledPrefixComplement_shell_le_four_pow_start
#print axioms Erdos.Problem1144.exists_harperTerminal_complementCorrelation_le_four_pow
#print axioms Erdos.Problem1144.exists_harperTerminalCapped_correlation_probability_le_powTwo_div_of_guard
#print axioms Erdos.Problem1144.harperTerminalGuardStart_gaussian_box_budget
#print axioms Erdos.Problem1144.exists_harperTerminalGuarded_oneHeight_lower
#print axioms Erdos.Problem1144.exists_harperTerminalGuarded_twoHeight_upper
