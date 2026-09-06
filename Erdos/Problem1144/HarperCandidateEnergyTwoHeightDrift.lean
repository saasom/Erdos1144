import Erdos.Problem1144.HarperRankinTwoHeightCovariance
import Erdos.Problem1144.HarperTwoHeightDriftControl

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- Exact deterministic translation of the literal one-height-centered
Rankin increment under the two-height law. -/
theorem candidate_rankinTwoHeightCenteredPrimeDrift_eq_product
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    harperRankinTwoHeightCenteredPrimeDrift p a t s t =
      let A := harperRankinEulerNormalizer p a
      let qt := harperRankinTwoHeightPrimeCoefficient p a t
      let qs := harperRankinTwoHeightPrimeCoefficient p a s
      2 * qt * qs * (A ^ 2 - (2 * qt) ^ 2) /
        (A * harperRankinTwoHeightPrimeNormalizer p a t s) := by
  have hA := harperRankinEulerNormalizer_pos p a
  have hM := harperRankinTwoHeightPrimeNormalizer_pos hp ha t s
  have hMformula := harperRankinTwoHeightPrimeNormalizer_eq_correlation p a t s
  unfold harperRankinTwoHeightCenteredPrimeDrift
  rw [harperRankinTwoHeightTiltBias_eq hp ha]
  unfold harperRankinTiltBias harperRankinTwoHeightPrimeCoefficient
  field_simp [hA.ne', hM.ne']
  rw [hMformula]
  ring

/-- Uniform inverse-square error in the shifted two-height drift. The
leading term retains the literal radial weight, so no Rankin loss occurs. -/
theorem candidate_rankinTwoHeightCenteredPrimeDrift_sub_weightedCosine_le
    {p : ℕ} (hp : p.Prime) (hp16 : 16 ≤ p) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    |harperRankinTwoHeightCenteredPrimeDrift p a t s t -
      2 * Real.cos (t * Real.log (p : ℝ)) * Real.cos (s * Real.log (p : ℝ)) *
        harperRankinEulerRadius p a ^ 2| ≤ 64 * (p : ℝ)⁻¹ ^ 2 := by
  let x : Real := harperRankinEulerRadius p a ^ 2
  let A : Real := 1 + x
  let qt : Real := harperRankinTwoHeightPrimeCoefficient p a t
  let qs : Real := harperRankinTwoHeightPrimeCoefficient p a s
  let M : Real := harperRankinTwoHeightPrimeNormalizer p a t s
  have hpR : (0 : Real) < p := by exact_mod_cast hp.pos
  have hxPos : 0 < x := sq_pos_of_pos (harperRankinEulerRadius_pos hp.pos a)
  have hxInv : x ≤ (p : ℝ)⁻¹ := by
    dsimp only [x]
    rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg hp.pos a]
    exact mul_le_of_le_one_right (by positivity)
      (rpow_neg_le_one_of_one_le (by exact_mod_cast hp.one_le) ha)
  have hxSmall : x ≤ 1 / 16 := by
    apply hxInv.trans
    rw [show (1 / 16 : Real) = (16 : Real)⁻¹ by norm_num]
    rw [inv_le_inv₀ hpR (by norm_num : (0 : Real) < 16)]
    exact_mod_cast hp16
  have hAone : (1 : Real) ≤ A := by dsimp only [A]; linarith
  have hAleTwo : A ≤ 2 := by dsimp only [A]; linarith
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hAone
  have hprodFormula : qt * qs =
      Real.cos (t * Real.log (p : Real)) *
        Real.cos (s * Real.log (p : Real)) * x := by
    dsimp only [qt, qs, x, harperRankinTwoHeightPrimeCoefficient]
    ring
  have hprodAbs : |qt * qs| ≤ x := by
    rw [hprodFormula, abs_mul, abs_mul, abs_of_pos hxPos]
    calc
      |Real.cos (t * Real.log (p : Real))| *
            |Real.cos (s * Real.log (p : Real))| * x ≤
          1 * 1 * x := by
            gcongr <;> exact Real.abs_cos_le_one _
      _ = x := by ring
  have hqtSq : qt ^ (2 : Nat) ≤ x := by
    have hcosSq : Real.cos (t * Real.log (p : Real)) ^ (2 : Nat) ≤ 1 := by
      nlinarith [Real.neg_one_le_cos (t * Real.log (p : Real)),
        Real.cos_le_one (t * Real.log (p : Real))]
    have heq : qt ^ (2 : Nat) =
        Real.cos (t * Real.log (p : Real)) ^ (2 : Nat) * x := by
      dsimp only [qt, x, harperRankinTwoHeightPrimeCoefficient]
      ring
    rw [heq]
    simpa using mul_le_mul_of_nonneg_right hcosSq hxPos.le
  have hMformula : M = A ^ (2 : Nat) + 4 * qt * qs := by
    dsimp only [M]
    rw [harperRankinTwoHeightPrimeNormalizer_eq_correlation]
    dsimp only [A, x, qt, qs, harperRankinTwoHeightPrimeCoefficient,
      harperRankinEulerNormalizer]
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
  have hdrift := candidate_rankinTwoHeightCenteredPrimeDrift_eq_product hp ha t s
  have hlead :
      2 * Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * harperRankinEulerRadius p a ^ 2 =
        2 * qt * qs := by
    calc
      2 * Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * harperRankinEulerRadius p a ^ 2 =
        2 * (Real.cos (t * Real.log (p : Real)) *
          Real.cos (s * Real.log (p : Real)) * x) := by
            dsimp only [x]
            ring
      _ = 2 * (qt * qs) := by rw [← hprodFormula]
      _ = 2 * qt * qs := by ring
  have hreduce : 64 * x ^ 2 ≤ 64 * (p : ℝ)⁻¹ ^ 2 := by
    gcongr
  apply le_trans ?_ hreduce
  rw [hlead]
  change |harperRankinTwoHeightCenteredPrimeDrift p a t s t -
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
theorem candidate_rankinTwoHeightCenteredBlockDrift_sub_weightedCosineSum_le
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (h16 : ∀ p ∈ S, 16 ≤ p.1) {a : ℝ} (ha : 0 ≤ a) (t s : Real) :
    |harperRankinTwoHeightCenteredBlockDrift y S a t s t -
        2 * ∑ p ∈ S,
          Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) * harperRankinEulerRadius p.1 a ^ 2| ≤
      64 * ∑ p ∈ S, (p.1 : Real)⁻¹ ^ (2 : Nat) := by
  unfold harperRankinTwoHeightCenteredBlockDrift
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ p ∈ S,
        (harperRankinTwoHeightCenteredPrimeDrift p.1 a t s t -
          2 * (Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) * harperRankinEulerRadius p.1 a ^ 2))| ≤
      ∑ p ∈ S,
        |harperRankinTwoHeightCenteredPrimeDrift p.1 a t s t -
          2 * (Real.cos (t * Real.log (p.1 : Real)) *
            Real.cos (s * Real.log (p.1 : Real)) *
              harperRankinEulerRadius p.1 a ^ 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, 64 * (p.1 : Real)⁻¹ ^ (2 : Nat) := by
      apply Finset.sum_le_sum
      intro p hpS
      convert
        candidate_rankinTwoHeightCenteredPrimeDrift_sub_weightedCosine_le
          (Nat.prime_of_mem_primesBelow p.property) (h16 p hpS) ha t s using 1 <;>
        ring
    _ = 64 * ∑ p ∈ S, (p.1 : Real)⁻¹ ^ (2 : Nat) := by
      rw [Finset.mul_sum]

/-- The actual shifted scheduled drift is twice its own covariance,
with the same summable error as the critical-line estimate. -/
theorem candidate_rankinTwoHeightScheduledDrift_sub_two_covariance_le
    (y j : ℕ) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    |harperRankinTwoHeightCenteredBlockDrift y
        (Problem520.harperScheduledPrimeBlock y j) a t s t -
      2 * harperRankinTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) a ha t s t s| ≤
      576 * Problem520.harperScheduledSquareMass y j := by
  let S := Problem520.harperScheduledPrimeBlock y j
  let C := ∑ p ∈ S, Real.cos (t * Real.log (p.1 : ℝ)) *
    Real.cos (s * Real.log (p.1 : ℝ)) * harperRankinEulerRadius p.1 a ^ 2
  let E := Problem520.harperScheduledSquareMass y j
  have hdrift : |harperRankinTwoHeightCenteredBlockDrift y S a t s t - 2 * C| ≤
      64 * E := by
    exact candidate_rankinTwoHeightCenteredBlockDrift_sub_weightedCosineSum_le y S
      (fun p hp => Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp)
      ha t s
  have hcov : |harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s t s - C| ≤
      256 * E := by
    unfold harperRankinTwoHeightBlockCoordinateCovariance
    dsimp only [C, E, Problem520.harperScheduledSquareMass]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    have h := abs_harperRankinTwoHeightPrimeCoordinateCovariance_sub_weightedCosine_le
      (Nat.prime_of_mem_primesBelow p.property)
      (Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp) ha t s t s
    rw [harperRankinEulerRadius_sq_eq_inv_mul_rpow_neg
      (Nat.prime_of_mem_primesBelow p.property).pos a]
    simpa only [mul_assoc] using h
  have htriangle := abs_sub_le
    (harperRankinTwoHeightCenteredBlockDrift y S a t s t) (2 * C)
    (2 * harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s t s)
  have heq : |2 * C - 2 * harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s t s| =
      2 * |harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s t s - C| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
  rw [heq] at htriangle
  dsimp only [S, E] at *
  linarith

end Erdos.Problem1144
