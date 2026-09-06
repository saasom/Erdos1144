import Erdos.Problem1144.HarperTwoHeightDriftedBlock
import Erdos.Problem1144.HarperTwoHeightCovariance

open Finset MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Post-coherence control of the deterministic two-height drift

The joint tilt changes a one-height-centered increment by twice the bare
cosine-product covariance, up to a summable inverse-square error.  Therefore
the same oscillatory cancellation that decorrelates the Gaussian block also
controls the deterministic translation carried by the literal ballot path.
-/

/-- One-prime joint-centering drift is twice the bare cosine-product kernel,
up to `O(p^-2)`. -/
theorem abs_harperTwoHeightCenteredPrimeDrift_sub_two_cosine_le
    {p : Nat} (hp : p.Prime) (hp16 : 16 ≤ p) (t s : Real) :
    |harperTwoHeightCenteredPrimeDrift p t s t -
        2 * Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * (p : Real)⁻¹| ≤
      64 * (p : Real)⁻¹ ^ (2 : Nat) := by
  let x : Real := (p : Real)⁻¹
  let A : Real := 1 + x
  let qt : Real := harperTwoHeightPrimeCoefficient p t
  let qs : Real := harperTwoHeightPrimeCoefficient p s
  let M : Real := harperTwoHeightPrimeNormalizer p t s
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hxPos : 0 < x := by dsimp only [x]; positivity
  have hxSmall : x ≤ 1 / 16 := by
    dsimp only [x]
    rw [show (1 / 16 : Real) = (16 : Real)⁻¹ by norm_num]
    rw [inv_le_inv₀ hpR (by norm_num : (0 : Real) < 16)]
    exact_mod_cast hp16
  have hAone : (1 : Real) ≤ A := by dsimp only [A]; linarith
  have hAleTwo : A ≤ 2 := by dsimp only [A]; linarith
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hAone
  have hprodFormula : qt * qs =
      Real.cos (t * Real.log (p : Real)) *
        Real.cos (s * Real.log (p : Real)) * x := by
    simpa only [qt, qs, x] using
      harperTwoHeightPrimeCoefficient_mul hp.pos t s
  have hprodAbs : |qt * qs| ≤ x := by
    rw [hprodFormula, abs_mul, abs_mul, abs_of_pos hxPos]
    calc
      |Real.cos (t * Real.log (p : Real))| *
            |Real.cos (s * Real.log (p : Real))| * x ≤
          1 * 1 * x := by
            gcongr <;> exact Real.abs_cos_le_one _
      _ = x := by ring
  have hqtSq : qt ^ (2 : Nat) ≤ x := by
    have hformula := harperTwoHeightPrimeCoefficient_mul hp.pos t t
    have hcosSq : Real.cos (t * Real.log (p : Real)) ^ (2 : Nat) ≤ 1 := by
      nlinarith [Real.neg_one_le_cos (t * Real.log (p : Real)),
        Real.cos_le_one (t * Real.log (p : Real))]
    have heq : qt ^ (2 : Nat) =
        Real.cos (t * Real.log (p : Real)) ^ (2 : Nat) * x := by
      simpa only [qt, x, pow_two] using hformula
    rw [heq]
    simpa using mul_le_mul_of_nonneg_right hcosSq hxPos.le
  have hMformula : M = A ^ (2 : Nat) + 4 * qt * qs := by
    dsimp only [M]
    rw [harperTwoHeightPrimeNormalizer_eq,
      harperCoordinateFactor_false_eq_base_sub hp,
      harperCoordinateFactor_false_eq_base_sub hp,
      harperCoordinateFactor_true_eq_base_add hp,
      harperCoordinateFactor_true_eq_base_add hp]
    dsimp only [A, x, qt, qs, harperTwoHeightPrimeCoefficient]
    ring
  have hA_sq_one : (1 : Real) ≤ A ^ (2 : Nat) := by
    nlinarith [sq_nonneg (A - 1)]
  have hMlower : (3 / 4 : Real) ≤ M := by
    have hprodLower := neg_le_of_abs_le hprodAbs
    rw [hMformula]
    nlinarith
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num) hMlower
  have hDlower : (3 / 4 : Real) ≤ A * M := by
    calc
      (3 / 4 : Real) = 1 * (3 / 4 : Real) := by ring
      _ ≤ A * (3 / 4 : Real) :=
        mul_le_mul_of_nonneg_right hAone (by norm_num)
      _ ≤ A * M := mul_le_mul_of_nonneg_left hMlower hApos.le
  have hA_sq_four : A ^ (2 : Nat) ≤ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAleTwo)
      (show 0 ≤ 2 + A by linarith)]
  let N : Real := A ^ (2 : Nat) - (2 * qt) ^ (2 : Nat)
  let D : Real := A * M
  have hND : N - D =
      A ^ (2 : Nat) * (1 - A) - 4 * qt ^ (2 : Nat) -
        4 * A * (qt * qs) := by
    dsimp only [N, D]
    rw [hMformula]
    ring
  have hOneSubA : |1 - A| = x := by
    have : 1 - A = -x := by dsimp only [A]; ring
    rw [this, abs_neg, abs_of_pos hxPos]
  have htermOne : |A ^ (2 : Nat) * (1 - A)| ≤ 4 * x := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg A), hOneSubA]
    exact mul_le_mul_of_nonneg_right hA_sq_four hxPos.le
  have htermTwo : |4 * qt ^ (2 : Nat)| ≤ 4 * x := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 4),
      abs_of_nonneg (sq_nonneg qt)]
    gcongr
  have htermThree : |4 * A * (qt * qs)| ≤ 8 * x := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 4),
      abs_of_pos hApos]
    calc
      4 * A * |qt * qs| ≤ 4 * 2 * x := by gcongr
      _ = 8 * x := by ring
  have hNDabs : |N - D| ≤ 16 * x := by
    rw [hND]
    calc
      |A ^ (2 : Nat) * (1 - A) - 4 * qt ^ (2 : Nat) -
          4 * A * (qt * qs)| ≤
        |A ^ (2 : Nat) * (1 - A)| + |4 * qt ^ (2 : Nat)| +
          |4 * A * (qt * qs)| := by
            exact (abs_sub _ _).trans
              (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 4 * x + 4 * x + 8 * x := by gcongr
      _ = 16 * x := by ring
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hdrift := harperTwoHeightCenteredPrimeDrift_eq_product hp t s
  have hlead :
      2 * Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * (p : Real)⁻¹ =
        2 * qt * qs := by
    calc
      2 * Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * (p : Real)⁻¹ =
        2 * (Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * x) := by
            dsimp only [x]
            ring
      _ = 2 * (qt * qs) := by rw [← hprodFormula]
      _ = 2 * qt * qs := by ring
  rw [hlead]
  change |harperTwoHeightCenteredPrimeDrift p t s t -
      2 * qt * qs| ≤ 64 * x ^ (2 : Nat)
  rw [hdrift]
  change |2 * qt * qs * N / D - 2 * qt * qs| ≤
    64 * x ^ (2 : Nat)
  have hidentity :
      2 * qt * qs * N / D - 2 * qt * qs =
        (2 * (qt * qs) * (N - D)) / D := by
    field_simp [hDpos.ne']
  rw [hidentity, abs_div, abs_mul, abs_mul, abs_of_pos hDpos,
    abs_of_pos (by norm_num : (0 : Real) < 2)]
  have hnum : 2 * |qt * qs| * |N - D| ≤ 32 * x ^ (2 : Nat) := by
    calc
      2 * |qt * qs| * |N - D| ≤ 2 * x * (16 * x) := by gcongr
      _ = 32 * x ^ (2 : Nat) := by ring
  rw [div_le_iff₀ hDpos]
  calc
    2 * |qt * qs| * |N - D| ≤ 32 * x ^ (2 : Nat) := hnum
    _ ≤ (64 * x ^ (2 : Nat)) * D := by
      have hxSq : 0 ≤ x ^ (2 : Nat) := sq_nonneg x
      have : (1 / 2 : Real) ≤ D := (by norm_num : (1 / 2 : Real) ≤ 3 / 4).trans
        (by simpa only [D] using hDlower)
      nlinarith

/-- Blockwise accumulation of the inverse-square prime error. -/
theorem abs_harperTwoHeightCenteredBlockDrift_sub_two_cosineSum_le
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (h16 : ∀ p ∈ S, 16 ≤ p.1) (t s : Real) :
    |harperTwoHeightCenteredBlockDrift y S t s t -
        2 * ∑ p ∈ S,
          Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹| ≤
      64 * ∑ p ∈ S, (p.1 : Real)⁻¹ ^ (2 : Nat) := by
  unfold harperTwoHeightCenteredBlockDrift
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ S,
        (harperTwoHeightCenteredPrimeDrift p.1 t s t -
          2 * (Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹))| ≤
      ∑ p ∈ S,
        |harperTwoHeightCenteredPrimeDrift p.1 t s t -
          2 * (Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) *
              (p.1 : Real)⁻¹)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, 64 * (p.1 : Real)⁻¹ ^ (2 : Nat) := by
      apply Finset.sum_le_sum
      intro p hpS
      convert
        abs_harperTwoHeightCenteredPrimeDrift_sub_two_cosine_le
          (Nat.prime_of_mem_primesBelow p.property) (h16 p hpS) t s using 1 <;>
        ring
    _ = 64 * ∑ p ∈ S, (p.1 : Real)⁻¹ ^ (2 : Nat) := by
      rw [Finset.mul_sum]

/-- Scheduled block drift is twice the exact centered covariance, up to a
summable inverse-square error. -/
theorem abs_harperTwoHeightScheduledCenteredBlockDrift_sub_two_covariance_le
    (y j : Nat) (t s : Real) :
    |harperTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y j) t s t -
        2 * harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
      576 * Problem520.harperScheduledSquareMass y j := by
  let S := Problem520.harperScheduledPrimeBlock y j
  let C := ∑ p ∈ S,
    Real.cos (t * Real.log (p.1 : Real)) *
      Real.cos (s * Real.log (p.1 : Real)) * (p.1 : Real)⁻¹
  let V := harperTwoHeightBlockCoordinateCovariance y S t s t s
  let E := Problem520.harperScheduledSquareMass y j
  have hdrift :
      |harperTwoHeightCenteredBlockDrift y S t s t - 2 * C| ≤ 64 * E := by
    simpa only [S, C, E, Problem520.harperScheduledSquareMass] using
      abs_harperTwoHeightCenteredBlockDrift_sub_two_cosineSum_le y S
        (fun p hpS ↦
          Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hpS)
        t s
  have hcov : |V - C| ≤ 256 * E := by
    simpa only [S, C, V, E, Problem520.harperScheduledSquareMass] using
      abs_harperTwoHeightBlockCoordinateCovariance_sub_cosineSum_le y S
        (fun p hpS ↦
          Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hpS)
        t s t s
  have hidentity :
      harperTwoHeightCenteredBlockDrift y S t s t - 2 * V =
        (harperTwoHeightCenteredBlockDrift y S t s t - 2 * C) -
          2 * (V - C) := by ring
  rw [hidentity]
  calc
    |(harperTwoHeightCenteredBlockDrift y S t s t - 2 * C) -
        2 * (V - C)| ≤
      |harperTwoHeightCenteredBlockDrift y S t s t - 2 * C| +
        |2 * (V - C)| := abs_sub _ _
    _ ≤ 64 * E + 2 * (256 * E) := by
      gcongr
      rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
      gcongr
    _ = 576 * E := by ring

/-- The two-height tilt bias is symmetric in its two heights. -/
theorem harperTwoHeightTiltBias_comm (p : Nat) (t s : Real) :
    harperTwoHeightTiltBias p t s = harperTwoHeightTiltBias p s t := by
  unfold harperTwoHeightTiltBias harperTwoHeightCoinWeight
    harperTwoHeightPrimeNormalizer
  have hnormalizer :
      (∫ b,
          Problem520.harperCoordinateFactor p t b *
            Problem520.harperCoordinateFactor p s b ∂Problem520.coin) =
        ∫ b,
          Problem520.harperCoordinateFactor p s b *
            Problem520.harperCoordinateFactor p t b ∂Problem520.coin := by
    apply integral_congr_ae
    exact ae_of_all _ fun b ↦ by ring
  rw [hnormalizer]
  ring

theorem harperTwoHeightRelativeBlockDrift_first
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    harperTwoHeightRelativeBlockDrift y S t s t t =
      harperTwoHeightCenteredBlockDrift y S t s t := by
  rfl

theorem harperTwoHeightRelativeBlockDrift_second
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (t s : Real) :
    harperTwoHeightRelativeBlockDrift y S t s s s =
      harperTwoHeightCenteredBlockDrift y S s t s := by
  unfold harperTwoHeightRelativeBlockDrift
    harperTwoHeightCenteredBlockDrift harperTwoHeightCenteredPrimeDrift
  apply Finset.sum_congr rfl
  intro p hpS
  rw [harperTwoHeightTiltBias_comm p.1 t s]

/-- After the dyadic coherence scale, both deterministic ballot-coordinate
drifts are uniformly as small as desired.  This is the drift input needed to
absorb the exact centering translation into a fixed Gaussian barrier margin. -/
theorem exists_eventually_harperTwoHeightScheduledRelativeDrifts_small
    {ε : Real} (hε : 0 < ε) :
    ∃ J : Nat, ∀ r j y : Nat, J + (r + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (r + 1) < |t - s| →
              |harperTwoHeightRelativeBlockDrift y
                  (Problem520.harperScheduledPrimeBlock y j) t s t t| < ε ∧
                |harperTwoHeightRelativeBlockDrift y
                  (Problem520.harperScheduledPrimeBlock y j) t s s s| < ε := by
  obtain ⟨Jcov, hcov⟩ :=
    exists_eventually_harperTwoHeightScheduledCovariance_postCoherence_small
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
  intro r j y hj hy t ht s hs hsep
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
  have hcovFirst := hcov r j y hjCov hy t ht s hs hsep
  have hsepSwap : (1 / 2 : Real) ^ (r + 1) < |s - t| := by
    simpa only [abs_sub_comm] using hsep
  have hcovSecond := hcov r j y hjCov hy s hs t ht hsepSwap
  have hcompareFirst :=
    abs_harperTwoHeightScheduledCenteredBlockDrift_sub_two_covariance_le
      y j t s
  have hcompareSecond :=
    abs_harperTwoHeightScheduledCenteredBlockDrift_sub_two_covariance_le
      y j s t
  have hfirst :
      |harperTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y j) t s t| < ε := by
    let D := harperTwoHeightCenteredBlockDrift y
      (Problem520.harperScheduledPrimeBlock y j) t s t
    let V := harperTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) t s t s
    have htri : |D| ≤ |D - 2 * V| + 2 * |V| := by
      calc
        |D| = |(D - 2 * V) + 2 * V| := by ring_nf
        _ ≤ |D - 2 * V| + |2 * V| := abs_add_le _ _
        _ = |D - 2 * V| + 2 * |V| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    dsimp only [D, V] at htri
    nlinarith
  have hsecond :
      |harperTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y j) s t s| < ε := by
    let D := harperTwoHeightCenteredBlockDrift y
      (Problem520.harperScheduledPrimeBlock y j) s t s
    let V := harperTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) s t s t
    have htri : |D| ≤ |D - 2 * V| + 2 * |V| := by
      calc
        |D| = |(D - 2 * V) + 2 * V| := by ring_nf
        _ ≤ |D - 2 * V| + |2 * V| := abs_add_le _ _
        _ = |D - 2 * V| + 2 * |V| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    dsimp only [D, V] at htri
    nlinarith
  rw [harperTwoHeightRelativeBlockDrift_first,
    harperTwoHeightRelativeBlockDrift_second]
  exact ⟨hfirst, hsecond⟩

/-- A single post-coherence shift supplies the full corridor-comparison
hypotheses and makes both literal ballot drifts at most `n^-2` per block. -/
theorem exists_harperTwoHeightCorridorCutoffBlockHypotheses_with_drift
    {n : Nat} (hn : 4 ≤ n) :
    ∃ J : Nat, ∀ r j y : Nat, J + (r + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (r + 1) < |t - s| →
              4 * (n : Real) ^ (6 : Nat) ≤
                  Real.sqrt (Problem520.harperBlockEndpoint j : Real) ∧
                1048576 * (n : Real) ^ (48 : Nat) ≤
                  Real.sqrt (Problem520.harperBlockEndpoint j : Real) ∧
                |harperTwoHeightBlockCoordinateCovariance y
                    (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
                  1 / (n : Real) ^ (40 : Nat) ∧
                |harperTwoHeightRelativeBlockDrift y
                    (Problem520.harperScheduledPrimeBlock y j) t s t t| ≤
                  1 / (n : Real) ^ (2 : Nat) ∧
                |harperTwoHeightRelativeBlockDrift y
                    (Problem520.harperScheduledPrimeBlock y j) t s s s| ≤
                  1 / (n : Real) ^ (2 : Nat) := by
  obtain ⟨Jcut, hcut⟩ :=
    exists_harperTwoHeightCorridorCutoffBlockHypotheses hn
  have hnPos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have heps : 0 < 1 / (n : Real) ^ (2 : Nat) := by positivity
  obtain ⟨Jdrift, hdrift⟩ :=
    exists_eventually_harperTwoHeightScheduledRelativeDrifts_small heps
  refine ⟨max Jcut Jdrift, ?_⟩
  intro r j y hj hy t ht s hs hsep
  have hjCut : Jcut + (r + 1) ≤ j := by
    have : Jcut ≤ max Jcut Jdrift := le_max_left _ _
    omega
  have hjDrift : Jdrift + (r + 1) ≤ j := by
    have : Jdrift ≤ max Jcut Jdrift := le_max_right _ _
    omega
  have hc := hcut r j y hjCut hy t ht s hs hsep
  have hd := hdrift r j y hjDrift hy t ht s hs hsep
  exact ⟨hc.1, hc.2.1, hc.2.2, hd.1.le, hd.2.le⟩

/-- Summing at most `n` block drifts of size `n^-2` costs at most `n^-1`. -/
theorem abs_sum_le_inv_of_abs_le_inv_sq
    {m n : Nat} (hn : 1 ≤ n) (hm : m ≤ n) (d : Fin m → Real)
    (hd : ∀ i, |d i| ≤ 1 / (n : Real) ^ (2 : Nat)) :
    |∑ i, d i| ≤ 1 / (n : Real) := by
  have hnPos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    |∑ i, d i| ≤ ∑ i, |d i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, 1 / (n : Real) ^ (2 : Nat) := by
      exact Finset.sum_le_sum fun i _hi ↦ hd i
    _ = (m : Real) * (1 / (n : Real) ^ (2 : Nat)) := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    _ ≤ (n : Real) * (1 / (n : Real) ^ (2 : Nat)) := by
      gcongr
    _ = 1 / (n : Real) := by field_simp

#print axioms Erdos.Problem1144.abs_harperTwoHeightCenteredPrimeDrift_sub_two_cosine_le
#print axioms Erdos.Problem1144.abs_harperTwoHeightScheduledCenteredBlockDrift_sub_two_covariance_le
#print axioms Erdos.Problem1144.harperTwoHeightRelativeBlockDrift_second
#print axioms Erdos.Problem1144.exists_eventually_harperTwoHeightScheduledRelativeDrifts_small
#print axioms Erdos.Problem1144.exists_harperTwoHeightCorridorCutoffBlockHypotheses_with_drift
#print axioms Erdos.Problem1144.abs_sum_le_inv_of_abs_le_inv_sq

end

end Problem1144
end Erdos
