import Erdos.Problem1144.HarperCandidateEnergyTwoHeightDrift
import Erdos.Problem1144.HarperCandidateEnergyTwoHeightOscillation

open Finset MeasureTheory ProbabilityTheory Set Filter
open Erdos.Problem520
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- Literal radially shifted cosine mass on a scheduled prime block. -/
noncomputable def candidateRankinScheduledOscillation (y j : ℕ) (a τ : ℝ) : ℝ :=
  ∑ p ∈ harperScheduledPrimeBlock y j,
    Real.cos (τ * Real.log (p.1 : ℝ)) / p.1 * (p.1 : ℝ) ^ (-a)

private theorem candidate_rankinScheduledOscillation_eq
    {y j : ℕ} (hy : harperBlockEndpoint (j + 1) ≤ y) (a τ : ℝ) :
    candidateRankinScheduledOscillation y j a τ =
      ∑ p ∈ (Finset.Ioc (harperBlockEndpoint j) (harperBlockEndpoint (j + 1))).filter Nat.Prime,
        Real.cos (τ * Real.log (p : ℝ)) / p * (p : ℝ) ^ (-a) := by
  unfold candidateRankinScheduledOscillation
  let e : HarperPrimeIndex y ↪ ℕ := Function.Embedding.subtype _
  calc
    _ = ∑ p ∈ (harperScheduledPrimeBlock y j).map e,
        Real.cos (τ * Real.log (p : ℝ)) / p * (p : ℝ) ^ (-a) := by
      rw [Finset.sum_map]
      rfl
    _ = _ := by
      rw [map_harperScheduledPrimeBlock_eq_freshPrimes hy,
        freshPrimes_eq_Ioc_filter_prime]

/-- The strong-PNT envelope is uniform over all nonnegative shifts. -/
theorem candidate_exists_rankinScheduledOscillation_rawPNT_bound :
    ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ j : ℕ, J ≤ j → ∀ y : ℕ, harperBlockEndpoint (j + 1) ≤ y →
        ∀ a τ : ℝ, 0 ≤ a → τ ≠ 0 →
          |candidateRankinScheduledOscillation y j a τ| ≤
            harperScheduledRawOscillationEnvelope c C j τ := by
  obtain ⟨c, hc, C, hC, X₀, hX₀two, hosc⟩ :=
    candidate_exists_mediumPNT_rankinPrimeOscillation_bound
  obtain ⟨NX, hNX⟩ := exists_nat_ge X₀
  have hend : Tendsto harperBlockEndpoint atTop atTop :=
    strictMono_harperBlockEndpoint.tendsto_atTop
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 (hend.eventually_ge_atTop NX)
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro j hJj y hy a tau ha htau
  have hNXj : NX ≤ harperBlockEndpoint j := hJ j hJj
  have hXj : X₀ ≤ (harperBlockEndpoint j : ℝ) :=
    hNX.trans (by exact_mod_cast hNXj)
  have hA2 : 2 ≤ harperBlockEndpoint j :=
    (by have := harperBlockEndpoint_ge_sixteen j; omega)
  have hAB : harperBlockEndpoint j ≤ harperBlockEndpoint (j + 1) :=
    monotone_harperBlockEndpoint (by omega)
  rw [candidate_rankinScheduledOscillation_eq hy a tau]
  exact hosc _ _ hXj hA2 hAB a tau ha htau

/-- Uniform dyadic cancellation, including the mesh displacement used by the ballot proof. -/
theorem candidate_exists_rankinScheduledDyadicOscillationBounds :
    ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ d j y : ℕ, J + d ≤ j →
        harperBlockEndpoint (j + 1) ≤ y →
          ∀ a : ℝ, 0 ≤ a → ∀ t u : ℝ,
            (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ 1 →
              |u - t| *
                  Real.log (harperBlockEndpoint (j + 1) : ℝ) ≤ 1 →
                |candidateRankinScheduledOscillation y j a (2 * u)| ≤
                  harperScheduledDyadicOscillationEnvelope d c C j := by
  obtain ⟨c, hc, C, hC, Jraw, hraw⟩ :=
    candidate_exists_rankinScheduledOscillation_rawPNT_bound
  let J := max Jraw 3
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro d j y hj hy a ha t u htLower htUpper hmesh
  have hjRaw : Jraw ≤ j := by
    have : Jraw ≤ J := le_max_left _ _
    omega
  have hjd : d + 3 ≤ j := by
    have : 3 ≤ J := le_max_right _ _
    omega
  let delta : ℝ := harperScheduledThetaEnvelope c C j
  let ell : ℝ := invLog (harperBlockEndpoint j)
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    exact harperScheduledThetaEnvelope_nonneg hC.le j
  have hell0 : 0 ≤ ell := (invLog_harperBlockEndpoint_pos j).le
  have hell1 : ell ≤ 1 := invLog_harperBlockEndpoint_le_one j
  have hlogSucc : 0 < Real.log (harperBlockEndpoint (j + 1) : ℝ) :=
    Real.log_pos (by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 16)
        (harperBlockEndpoint_ge_sixteen (j + 1)))
  have hdisp : |u - t| ≤
      invLog (harperBlockEndpoint (j + 1)) := by
    unfold invLog
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hlogSucc).2 (by simpa using hmesh)
  have hscale := invLog_harperBlockEndpoint_succ_le_dyadic hjd
  have hdispDyadic : |u - t| ≤
      (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ d := hdisp.trans hscale
  have hqpos : 0 < (1 / 2 : ℝ) ^ d := by positivity
  have hreverse := abs_sub_abs_le_abs_sub t u
  rw [abs_sub_comm t u] at hreverse
  have htLower' : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ d < |t| := by
    rw [pow_succ] at htLower
    simpa [mul_comm] using htLower
  have huLower : (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ d < |u| := by
    linarith
  have huPos : 0 < |u| := lt_of_lt_of_le (mul_pos (by norm_num) hqpos) huLower.le
  have hquarterInv :
      ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ d)⁻¹ =
        4 * (2 : ℝ) ^ d := by
    rw [one_div_pow]
    field_simp
  have huInv : |u|⁻¹ ≤ 4 * (2 : ℝ) ^ d := by
    calc
      |u|⁻¹ ≤ ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ d)⁻¹ :=
        inv_anti₀ (mul_pos (by norm_num) hqpos) huLower.le
      _ = 4 * (2 : ℝ) ^ d := hquarterInv
  have hboundary : 2 / |2 * u| ≤ 4 * (2 : ℝ) ^ d := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 / (2 * |u|) = |u|⁻¹ := by field_simp
      _ ≤ 4 * (2 : ℝ) ^ d := huInv
  have hqle : (1 / 2 : ℝ) ^ d ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have huUpper : |u| ≤ 2 := by
    have hutriangle : |u| ≤ |u - t| + |t| := by
      calc
        |u| = |(u - t) + t| := by ring_nf
        _ ≤ |u - t| + |t| := abs_add_le _ _
    linarith
  have htauUpper : |2 * u| ≤ 4 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have htau : 2 * u ≠ 0 := by
    intro hzero
    have : u = 0 := by linarith
    rw [this, abs_zero] at huPos
    exact lt_irrefl 0 huPos
  have hbase := hraw j hjRaw y hy a (2 * u) ha htau
  have hratio :
      ((harperBlockEndpoint (j + 1) : ℝ) /
          harperBlockEndpoint j) = (harperBlockEndpoint j : ℝ) := by
    rw [harperBlockEndpoint_succ]
    push_cast
    have hAne : (harperBlockEndpoint j : ℝ) ≠ 0 := by
      exact_mod_cast (harperBlockEndpoint_pos j).ne'
    field_simp
  have hlogCancel :
      Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
          harperBlockEndpoint j) * ell = 1 := by
    rw [hratio]
    dsimp [ell, invLog]
    exact mul_inv_cancel₀
      (Real.log_pos (by
        exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 16)
          (harperBlockEndpoint_ge_sixteen j))).ne'
  change |candidateRankinScheduledOscillation y j a (2 * u)| ≤ _
  calc
    |candidateRankinScheduledOscillation y j a (2 * u)| ≤
        (2 / |2 * u| + 2 * delta +
          delta * (1 + |2 * u|) *
            Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
              harperBlockEndpoint j)) * ell := by
      simpa only [harperScheduledRawOscillationEnvelope, delta, ell,
        harperScheduledThetaEnvelope] using hbase
    _ = (2 / |2 * u|) * ell + 2 * delta * ell +
        delta * (1 + |2 * u|) *
          (Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
            harperBlockEndpoint j) * ell) := by ring
    _ = (2 / |2 * u|) * ell + 2 * delta * ell +
        delta * (1 + |2 * u|) := by rw [hlogCancel, mul_one]
    _ ≤ (4 * (2 : ℝ) ^ d) * ell + 2 * delta + 5 * delta := by
      have hfirst := mul_le_mul_of_nonneg_right hboundary hell0
      have hsecond : 2 * delta * ell ≤ 2 * delta := by nlinarith
      have hthird : delta * (1 + |2 * u|) ≤ 5 * delta := by
        nlinarith
      linarith
    _ = harperScheduledDyadicOscillationEnvelope d c C j := by
      dsimp [ell, delta, harperScheduledDyadicOscillationEnvelope]
      ring


/-- The shifted covariance is controlled by its two literal weighted
frequency kernels and a summable inverse-square error. -/
theorem candidate_rankinScheduledCovariance_le_of_oscillation
    (y j : ℕ) {a : ℝ} (ha : 0 ≤ a) (t s u v Bdiff Bsum : ℝ)
    (hdiff : |candidateRankinScheduledOscillation y j a (u - v)| ≤ Bdiff)
    (hsum : |candidateRankinScheduledOscillation y j a (u + v)| ≤ Bsum) :
    |harperRankinTwoHeightBlockCoordinateCovariance y
      (harperScheduledPrimeBlock y j) a ha t s u v| ≤
      (1 / 2 : ℝ) * (Bdiff + Bsum) + 256 * harperScheduledSquareMass y j := by
  let C := ∑ p ∈ harperScheduledPrimeBlock y j,
    Real.cos (u * Real.log (p.1 : ℝ)) * Real.cos (v * Real.log (p.1 : ℝ)) *
      (p.1 : ℝ)⁻¹ * (p.1 : ℝ) ^ (-a)
  have happrox : |harperRankinTwoHeightBlockCoordinateCovariance y
      (harperScheduledPrimeBlock y j) a ha t s u v - C| ≤
      256 * harperScheduledSquareMass y j := by
    unfold harperRankinTwoHeightBlockCoordinateCovariance
    dsimp only [C, harperScheduledSquareMass]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    exact abs_harperRankinTwoHeightPrimeCoordinateCovariance_sub_weightedCosine_le
      (Nat.prime_of_mem_primesBelow p.property)
      (sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp) ha t s u v
  have hCeq : C = (1 / 2 : ℝ) *
      (candidateRankinScheduledOscillation y j a (u - v) +
        candidateRankinScheduledOscillation y j a (u + v)) := by
    dsimp only [C, candidateRankinScheduledOscillation]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [cosine_mul_cosine_eq_half_difference_add_sum]
    ring
  have hC : |C| ≤ (1 / 2 : ℝ) * (Bdiff + Bsum) := by
    rw [hCeq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hdiff hsum))
      (by norm_num)
  have htri := abs_sub_le
    (harperRankinTwoHeightBlockCoordinateCovariance y
      (harperScheduledPrimeBlock y j) a ha t s u v) C 0
  rw [sub_zero, sub_zero] at htri
  linarith

theorem candidate_exists_rankinScheduledCovariance_dyadicShell_bound :
    ∃ c > 0, ∃ C > 0, ∃ J : Nat,
      ∀ r j y : Nat, J + (r + 1) ≤ j →
        Problem520.harperBlockEndpoint (j + 1) ≤ y →
          ∀ a : ℝ, ∀ ha : 0 ≤ a, ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (r + 1) < |t - s| →
                |harperRankinTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y j) a ha t s t s| ≤
                  (1 / 2 : Real) *
                    (Problem520.harperScheduledDyadicOscillationEnvelope
                        (r + 1) c C j +
                      Problem520.harperScheduledDyadicOscillationEnvelope
                        1 c C j) +
                    256 * Problem520.harperScheduledSquareMass y j := by
  obtain ⟨c, hc, C, hC, J, hosc⟩ :=
    candidate_exists_rankinScheduledDyadicOscillationBounds
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro r j y hj hy a ha t ht s hs hsep
  have htBand : (1 / 3 : Real) ≤ t ∧ t ≤ 1 / 2 := ht
  have hsBand : (1 / 3 : Real) ≤ s ∧ s ≤ 1 / 2 := hs
  let udiff : Real := (t - s) / 2
  let usum : Real := (t + s) / 2
  have hudiffLower :
      (1 / 2 : Real) ^ ((r + 1) + 1) < |udiff| := by
    calc
      (1 / 2 : Real) ^ ((r + 1) + 1) =
          (1 / 2 : Real) ^ (r + 1) / 2 := by
        rw [pow_succ]
        ring
      _ < |t - s| / 2 := div_lt_div_of_pos_right hsep (by norm_num)
      _ = |udiff| := by
        dsimp only [udiff]
        rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
  have hdiffAbs : |t - s| ≤ (1 / 6 : Real) := by
    rw [abs_le]
    constructor <;> linarith
  have hudiffUpper : |udiff| ≤ 1 := by
    dsimp only [udiff]
    rw [abs_div, abs_of_pos (by norm_num : (0 : Real) < 2)]
    linarith
  have husumPos : 0 < usum := by
    dsimp only [usum]
    linarith
  have husumLower : (1 / 2 : Real) ^ (1 + 1) < |usum| := by
    rw [abs_of_pos husumPos]
    dsimp only [usum]
    norm_num
    linarith
  have husumUpper : |usum| ≤ 1 := by
    rw [abs_of_pos husumPos]
    dsimp only [usum]
    linarith
  have hjSum : J + 1 ≤ j := by omega
  have hdiffBound := hosc (r + 1) j y hj hy a ha udiff udiff
    hudiffLower hudiffUpper (by simp)
  have hsumBound := hosc 1 j y hjSum hy a ha usum usum
    husumLower husumUpper (by simp)
  apply candidate_rankinScheduledCovariance_le_of_oscillation
    y j ha t s t s
  · simpa only [udiff, show 2 * ((t - s) / 2) = t - s by ring] using
      hdiffBound
  · simpa only [usum, show 2 * ((t + s) / 2) = t + s by ring] using
      hsumBound

/-- Fully explicit geometric form of the shell covariance estimate. -/
theorem candidate_exists_rankinScheduledCovariance_postCoherence_geometric :
    ∃ c > 0, ∃ C > 0, ∃ J : Nat,
      ∀ r j y : Nat, J + (r + 1) ≤ j →
        Problem520.harperBlockEndpoint (j + 1) ≤ y →
          ∀ a : ℝ, ∀ ha : 0 ≤ a, ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (r + 1) < |t - s| →
                |harperRankinTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y j) a ha t s t s| ≤
                  2 * (1 / 2 : Real) ^ (j - (r + 1)) +
                    2 * (1 / 2 : Real) ^ (j - 1) +
                    7 * Problem520.harperScheduledThetaEnvelope c C j +
                    256 * Problem520.harperScheduledSquareMass y j := by
  obtain ⟨c, hc, C, hC, J, hcov⟩ :=
    candidate_exists_rankinScheduledCovariance_dyadicShell_bound
  refine ⟨c, hc, C, hC, J, ?_⟩
  intro r j y hj hy a ha t ht s hs hsep
  have hrj : r + 1 ≤ j := by omega
  have h1j : 1 ≤ j := by omega
  have hraw := hcov r j y hj hy a ha t ht s hs hsep
  have hdiff := harperScheduledDyadicOscillationEnvelope_le_geometric
    (c := c) (C := C) hrj
  have hsum := harperScheduledDyadicOscillationEnvelope_le_geometric
    (c := c) (C := C) h1j
  calc
    |harperRankinTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) a ha t s t s| ≤
      (1 / 2 : Real) *
          (Problem520.harperScheduledDyadicOscillationEnvelope
              (r + 1) c C j +
            Problem520.harperScheduledDyadicOscillationEnvelope 1 c C j) +
        256 * Problem520.harperScheduledSquareMass y j := hraw
    _ ≤ (1 / 2 : Real) *
          ((4 * (1 / 2 : Real) ^ (j - (r + 1)) +
              7 * Problem520.harperScheduledThetaEnvelope c C j) +
            (4 * (1 / 2 : Real) ^ (j - 1) +
              7 * Problem520.harperScheduledThetaEnvelope c C j)) +
        256 * Problem520.harperScheduledSquareMass y j := by gcongr
    _ = 2 * (1 / 2 : Real) ^ (j - (r + 1)) +
          2 * (1 / 2 : Real) ^ (j - 1) +
          7 * Problem520.harperScheduledThetaEnvelope c C j +
          256 * Problem520.harperScheduledSquareMass y j := by ring

/-- Uniform small-correlation consequence.  After a fixed additional shift,
every block beyond the shell's coherence index has covariance smaller than
an arbitrary prescribed positive constant. -/
theorem candidate_exists_rankinScheduledCovariance_postCoherence_small
    {ε : Real} (hε : 0 < ε) :
    ∃ J : Nat, ∀ r j y : Nat, J + (r + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ a : ℝ, ∀ ha : 0 ≤ a, ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (r + 1) < |t - s| →
              |harperRankinTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j) a ha t s t s| < ε := by
  obtain ⟨c, hc, C, hC, Jcov, hcov⟩ :=
    candidate_exists_rankinScheduledCovariance_postCoherence_geometric
  obtain ⟨c', hc', C', hC', Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  have hgeomTendsto : Tendsto
      (fun k : Nat ↦ 2 * (1 / 2 : Real) ^ k) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : Real) ≤ 1 / 2)
        (by norm_num : (1 / 2 : Real) < 1))
  have hthetaTendsto : Tendsto
      (Problem520.harperScheduledThetaEnvelope c C) atTop (nhds 0) :=
    (Problem520.summable_harperScheduledThetaEnvelope hc hC.le).tendsto_atTop_zero
  have hsquareTendsto : Tendsto Problem520.harperScheduledSquareEnvelope
      atTop (nhds 0) :=
    Problem520.summable_harperScheduledSquareEnvelope.tendsto_atTop_zero
  have hgeomEventually : ∀ᶠ k : Nat in atTop,
      2 * (1 / 2 : Real) ^ k < ε / 4 :=
    (tendsto_order.mp hgeomTendsto).2 _ (by linarith)
  have hthetaEventually : ∀ᶠ k : Nat in atTop,
      Problem520.harperScheduledThetaEnvelope c C k < ε / 28 :=
    (tendsto_order.mp hthetaTendsto).2 _ (by linarith)
  have hsquareEventually : ∀ᶠ k : Nat in atTop,
      Problem520.harperScheduledSquareEnvelope k < ε / 1024 :=
    (tendsto_order.mp hsquareTendsto).2 _ (by linarith)
  obtain ⟨Jgeom, hgeom⟩ := Filter.eventually_atTop.1 hgeomEventually
  obtain ⟨Jtheta, htheta⟩ := Filter.eventually_atTop.1 hthetaEventually
  obtain ⟨Jsquare, hsquare⟩ := Filter.eventually_atTop.1 hsquareEventually
  let J := max Jcov (max Jerr (max Jgeom (max Jtheta Jsquare)))
  refine ⟨J, ?_⟩
  intro r j y hj hy a ha t ht s hs hsep
  have hJcov : Jcov + (r + 1) ≤ j := by
    have : Jcov ≤ J := le_max_left _ _
    omega
  have hJerr : Jerr ≤ j := by
    have : Jerr ≤ J := (le_max_left Jerr _).trans (le_max_right Jcov _)
    omega
  have hJgeomDiff : Jgeom ≤ j - (r + 1) := by
    have : Jgeom ≤ J :=
      (le_max_left Jgeom _).trans
        ((le_max_right Jerr _).trans (le_max_right Jcov _))
    omega
  have hJgeomSum : Jgeom ≤ j - 1 := by
    have : Jgeom ≤ J :=
      (le_max_left Jgeom _).trans
        ((le_max_right Jerr _).trans (le_max_right Jcov _))
    omega
  have hJtheta : Jtheta ≤ j := by
    have : Jtheta ≤ J :=
      ((le_max_left Jtheta Jsquare).trans (le_max_right Jgeom _)).trans
        ((le_max_right Jerr _).trans (le_max_right Jcov _))
    omega
  have hJsquare : Jsquare ≤ j := by
    have : Jsquare ≤ J :=
      ((le_max_right Jtheta Jsquare).trans (le_max_right Jgeom _)).trans
        ((le_max_right Jerr _).trans (le_max_right Jcov _))
    omega
  have hraw := hcov r j y hJcov hy a ha t ht s hs hsep
  have hgeomDiff := hgeom (j - (r + 1)) hJgeomDiff
  have hgeomSum := hgeom (j - 1) hJgeomSum
  have hthetaSmall := htheta j hJtheta
  have hsquareBound : Problem520.harperScheduledSquareMass y j ≤
      Problem520.harperScheduledSquareEnvelope j :=
    (herr j hJerr y hy).2.2
  have hsquareSmall := hsquare j hJsquare
  nlinarith


/-- Both actual one-height-centered ballot drifts vanish uniformly after coherence,
for every nonnegative radial shift. -/
theorem candidate_exists_rankinScheduledDrifts_postCoherence_small
    {ε : Real} (hε : 0 < ε) :
    ∃ J : Nat, ∀ r j y : Nat, J + (r + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ a : ℝ, ∀ ha : 0 ≤ a, ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (r + 1) < |t - s| →
              |harperRankinTwoHeightCenteredBlockDrift y
                  (Problem520.harperScheduledPrimeBlock y j) a t s t| < ε ∧
                |harperRankinTwoHeightCenteredBlockDrift y
                  (Problem520.harperScheduledPrimeBlock y j) a s t s| < ε := by
  obtain ⟨Jcov, hcov⟩ :=
    candidate_exists_rankinScheduledCovariance_postCoherence_small
      (show 0 < ε / 4 by linarith)
  obtain ⟨c, hc, C, hC, Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  have hsquareTendsto : Tendsto Problem520.harperScheduledSquareEnvelope
      atTop (nhds 0) :=
    Problem520.summable_harperScheduledSquareEnvelope.tendsto_atTop_zero
  have hsquareEventually : ∀ᶠ j : Nat in atTop,
      Problem520.harperScheduledSquareEnvelope j < ε / 2304 :=
    (tendsto_order.mp hsquareTendsto).2 _ (by linarith)
  obtain ⟨Jsquare, hsquare⟩ := Filter.eventually_atTop.1 hsquareEventually
  let J := max Jcov (max Jerr Jsquare)
  refine ⟨J, ?_⟩
  intro r j y hj hy a ha t ht s hs hsep
  have hjCov : Jcov + (r + 1) ≤ j := by
    have : Jcov ≤ J := le_max_left _ _
    omega
  have hjErr : Jerr ≤ j := by
    have : Jerr ≤ J :=
      (le_max_left Jerr Jsquare).trans (le_max_right Jcov _)
    omega
  have hjSquare : Jsquare ≤ j := by
    have : Jsquare ≤ J :=
      (le_max_right Jerr Jsquare).trans (le_max_right Jcov _)
    omega
  have hsquareMass : Problem520.harperScheduledSquareMass y j ≤
      Problem520.harperScheduledSquareEnvelope j :=
    (herr j hjErr y hy).2.2
  have hsquareSmall := hsquare j hjSquare
  have herror : 576 * Problem520.harperScheduledSquareMass y j < ε / 4 := by
    nlinarith
  have hcovFirst := hcov r j y hjCov hy a ha t ht s hs hsep
  have hsepSwap : (1 / 2 : Real) ^ (r + 1) < |s - t| := by
    simpa only [abs_sub_comm] using hsep
  have hcovSecond := hcov r j y hjCov hy a ha s hs t ht hsepSwap
  have hcompareFirst :=
    candidate_rankinTwoHeightScheduledDrift_sub_two_covariance_le
      y j ha t s
  have hcompareSecond :=
    candidate_rankinTwoHeightScheduledDrift_sub_two_covariance_le
      y j ha s t
  have hfirst :
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y j) a t s t| < ε := by
    let D := harperRankinTwoHeightCenteredBlockDrift y
      (Problem520.harperScheduledPrimeBlock y j) a t s t
    let V := harperRankinTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) a ha t s t s
    have htri : |D| ≤ |D - 2 * V| + 2 * |V| := by
      calc
        |D| = |(D - 2 * V) + 2 * V| := by ring_nf
        _ ≤ |D - 2 * V| + |2 * V| := abs_add_le _ _
        _ = |D - 2 * V| + 2 * |V| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    dsimp only [D, V] at htri
    nlinarith
  have hsecond :
      |harperRankinTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y j) a s t s| < ε := by
    let D := harperRankinTwoHeightCenteredBlockDrift y
      (Problem520.harperScheduledPrimeBlock y j) a s t s
    let V := harperRankinTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) a ha s t s t
    have htri : |D| ≤ |D - 2 * V| + 2 * |V| := by
      calc
        |D| = |(D - 2 * V) + 2 * V| := by ring_nf
        _ ≤ |D - 2 * V| + |2 * V| := abs_add_le _ _
        _ = |D - 2 * V| + 2 * |V| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    dsimp only [D, V] at htri
    nlinarith
  exact ⟨hfirst, hsecond⟩


/-- The fixed radial gap retains the two-height marginal variance window
needed by the bivariate local comparison. -/
theorem candidate_exists_gap_rankinScheduledCoordinateVariance_window
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ gap J : ℕ, ∀ j y : ℕ, J ≤ j →
      harperBlockEndpoint (j + gap + 1) ≤ y →
        ∀ ha : 0 ≤ 4 * V / Real.log (y : ℝ),
          ∀ t ∈ harperLowerVerticalBand, ∀ s ∈ harperLowerVerticalBand,
            ∀ u ∈ harperLowerVerticalBand,
              (1 / 4 : ℝ) < harperRankinTwoHeightBlockCoordinateCovariance y
                (harperScheduledPrimeBlock y j) (4 * V / Real.log (y : ℝ)) ha t s u u ∧
              harperRankinTwoHeightBlockCoordinateCovariance y
                (harperScheduledPrimeBlock y j) (4 * V / Real.log (y : ℝ)) ha t s u u < 1 / 2 := by
  obtain ⟨gap, Jshift, hshift⟩ :=
    exists_gap_eventually_harperRankinTwoHeightScheduledCovariance_close V hV
  obtain ⟨Jvar, hvar⟩ :=
    exists_eventually_harperTwoHeightScheduledCoordinateVariance_third_threeEighths
  refine ⟨gap, max Jshift Jvar, ?_⟩
  intro j y hj hy ha t ht s hs u hu
  have hnear : harperBlockEndpoint (j + 1) ≤ y :=
    (monotone_harperBlockEndpoint (by omega)).trans hy
  have hc := hshift j y (by omega) hy ha t s u u
  have hv := hvar j (by omega) y hnear t ht s hs u hu
  have hcl := neg_lt_of_abs_lt hc
  have hcu := lt_of_abs_lt hc
  constructor <;> linarith [hv.1, hv.2]

/-- The actual shifted two-height Gaussian is uniformly nondegenerate
beyond coherence and before the fixed terminal radial gap. -/
theorem candidate_exists_gap_rankinScheduledProjectedVariance_eighth
    (V : ℝ) (hV : 0 ≤ V) :
    ∃ gap J : ℕ, ∀ r j y : ℕ, J + (r + 1) ≤ j →
      harperBlockEndpoint (j + gap + 1) ≤ y →
        ∀ ha : 0 ≤ 4 * V / Real.log (y : ℝ),
          ∀ t ∈ harperLowerVerticalBand, ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : ℝ) ^ (r + 1) < |t - s| → ∀ v w : ℝ,
              (1 / 8 : ℝ) * (v ^ 2 + w ^ 2) ≤
                harperRankinTwoHeightProjectedBlockVariance y
                  (harperScheduledPrimeBlock y j) (4 * V / Real.log (y : ℝ)) ha t s v w := by
  obtain ⟨gap, Jvar, hvar⟩ := candidate_exists_gap_rankinScheduledCoordinateVariance_window V hV
  obtain ⟨Jcov, hcov⟩ := candidate_exists_rankinScheduledCovariance_postCoherence_small
    (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨gap, max Jvar Jcov, ?_⟩
  intro r j y hj hy ha t ht s hs hsep v w
  have hnear : harperBlockEndpoint (j + 1) ≤ y :=
    (monotone_harperBlockEndpoint (by omega)).trans hy
  have htt := (hvar j y (by omega) hy ha t ht s hs t ht).1.le
  have hss := (hvar j y (by omega) hy ha t ht s hs s hs).1.le
  have hts := (hcov r j y (by omega) hnear _ ha t ht s hs hsep).le
  exact harperRankinTwoHeightProjectedBlockVariance_ge_eighth_of_marginals_covariance
    y (harperScheduledPrimeBlock y j) _ ha t s v w htt hss hts

end Erdos.Problem1144
