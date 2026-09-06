import Erdos.Problem1144.HarperGaussianRegressionIdentification
import Erdos.Problem520.HarperScheduledRelativeInterval

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Erdos
namespace Problem1144

/-!
# Relative bivariate cells on the scheduled shell

This file starts the multiplicative two-height replacement needed by the
overlap-shell argument.  The first input is a uniform positive denominator:
after the natural shell coherence cutoff, every moderate rectangle of the
exact covariance-matched Gaussian has an explicit elementary lower bound.
-/

private theorem eventually_const_mul_pow_le_exp_quarter_nat_bivariate
    (A : Real) (d : Nat) :
    ∀ᶠ j : Nat in atTop,
      A * (j : Real) ^ d ≤ Real.exp ((j : Real) / 4) := by
  have ht : Tendsto
      (fun x : Real ↦ Real.exp ((1 / 4 : Real) * x) / x ^ (d : Real))
      atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop (d : Real) (1 / 4 : Real) (by norm_num)
  have htNat := ht.comp tendsto_natCast_atTop_atTop
  filter_upwards [htNat.eventually (eventually_ge_atTop A),
      eventually_ge_atTop (1 : Nat)] with j hj hjOne
  have hjPos : (0 : Real) < j := by positivity
  have hden : 0 < (j : Real) ^ d := by positivity
  change A ≤ Real.exp ((1 / 4 : Real) * (j : Real)) /
    (j : Real) ^ (d : Real) at hj
  rw [Real.rpow_natCast] at hj
  rw [le_div_iff₀ hden] at hj
  calc
    A * (j : Real) ^ d ≤ Real.exp ((1 / 4 : Real) * (j : Real)) := hj
    _ = Real.exp ((j : Real) / 4) := by
      congr 1
      ring

/-- On the moderate two-dimensional corridor, the Fejer tail from the
strong scheduled cutoff is smaller than one extra cell-width times the
elementary correlated-Gaussian cell lower bound. -/
theorem eventually_harperScheduledBivariateFejerTail_le_relativeGaussianMass :
    ∀ᶠ j : Nat in atTop, ∀ lambda a b : Real,
      |lambda| ≤ (3 / 8 : Real) →
        |a| + |b| + 3 ≤
            (1 / 16 : Real) * Real.sqrt (((2 ^ j : Nat) : Real)) →
          2 / Real.sqrt
              (Problem520.harperScheduledStrongComparisonFrequency j) ≤
            Problem520.harperScheduledRelativeIntervalWidth j *
              ((Problem520.harperScheduledRelativeIntervalWidth j ^
                    (2 : Nat) / 64) *
                Real.exp (-2 *
                  ((|a| + 1) ^ (2 : Nat) +
                    (|b - lambda * a +
                        Problem520.harperScheduledRelativeIntervalWidth j / 4| + 1) ^
                      (2 : Nat)))) := by
  have hpoly :=
    eventually_const_mul_pow_le_exp_quarter_nat_bivariate (8192 : Real) 6
  filter_upwards [hpoly, eventually_ge_atTop (1 : Nat)] with j hpolyJ hjOne
  intro lambda a b hlambda hmoderate
  let n : Real := ((2 ^ j : Nat) : Real)
  let D : Real := (((j + 1 : Nat) : Real) ^ 2)
  let delta : Real := Problem520.harperScheduledRelativeIntervalWidth j
  let q : Real := 2 *
    ((|a| + 1) ^ (2 : Nat) +
      (|b - lambda * a + delta / 4| + 1) ^ (2 : Nat))
  let T : Real := Problem520.harperScheduledStrongComparisonFrequency j
  have hn0 : 0 ≤ n := by dsimp [n]; positivity
  have hnPos : 0 < n := by dsimp [n]; positivity
  have hDPos : 0 < D := by dsimp [D]; positivity
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact Problem520.harperScheduledRelativeIntervalWidth_pos j
  have hdeltaOne : delta ≤ 1 := by
    dsimp only [delta]
    exact Problem520.harperScheduledRelativeIntervalWidth_le_one j
  have hTPos : 0 < T := by
    dsimp only [T]
    exact Problem520.harperScheduledStrongComparisonFrequency_pos j
  have hsecond :
      |b - lambda * a + delta / 4| + 1 ≤ |a| + |b| + 3 := by
    have habs :
        |b - lambda * a + delta / 4| ≤
          |b| + |lambda| * |a| + delta / 4 := by
      calc
        |b - lambda * a + delta / 4| ≤
            |b - lambda * a| + |delta / 4| := abs_add_le _ _
        _ ≤ (|b| + |lambda * a|) + |delta / 4| := by
          have hsub : |b - lambda * a| ≤ |b| + |lambda * a| := by
            rw [sub_eq_add_neg]
            simpa only [abs_neg] using (abs_add_le b (-(lambda * a)))
          linarith
        _ = |b| + |lambda| * |a| + delta / 4 := by
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ delta / 4)]
    calc
      |b - lambda * a + delta / 4| + 1 ≤
          |b| + |lambda| * |a| + delta / 4 + 1 := by linarith
      _ ≤ |b| + (3 / 8 : Real) * |a| + 1 / 4 + 1 := by
        gcongr
      _ ≤ |a| + |b| + 3 := by
        nlinarith [abs_nonneg a]
  have hfirst : |a| + 1 ≤ |a| + |b| + 3 := by
    nlinarith [abs_nonneg b]
  have hfirstMod :
      |a| + 1 ≤ (1 / 16 : Real) * Real.sqrt n :=
    hfirst.trans (by simpa only [n] using hmoderate)
  have hsecondMod :
      |b - lambda * a + delta / 4| + 1 ≤
        (1 / 16 : Real) * Real.sqrt n :=
    hsecond.trans (by simpa only [n] using hmoderate)
  have hsqrtSq : Real.sqrt n ^ (2 : Nat) = n := Real.sq_sqrt hn0
  have hfirst0 : 0 ≤ |a| + 1 := by positivity
  have hsecond0 : 0 ≤ |b - lambda * a + delta / 4| + 1 := by positivity
  have hright0 : 0 ≤ (1 / 16 : Real) * Real.sqrt n := by positivity
  have hfirstSq : (|a| + 1) ^ (2 : Nat) ≤ n / 256 := by
    have := (sq_le_sq₀ hfirst0 hright0).2 hfirstMod
    nlinarith
  have hsecondSq :
      (|b - lambda * a + delta / 4| + 1) ^ (2 : Nat) ≤ n / 256 := by
    have := (sq_le_sq₀ hsecond0 hright0).2 hsecondMod
    nlinarith
  have hq : q ≤ n / 64 := by
    dsimp only [q]
    linarith
  have hqExp : Real.exp q ≤ Real.exp (n / 64) :=
    Real.exp_le_exp.mpr hq
  have hjCast : ((j : Real) + 1) ≤ 2 * (j : Real) := by
    exact_mod_cast (show j + 1 ≤ 2 * j by omega)
  have hDcube : 128 * D ^ (3 : Nat) ≤ 8192 * (j : Real) ^ (6 : Nat) := by
    calc
      128 * D ^ (3 : Nat) = 128 * (((j : Real) + 1) ^ (6 : Nat)) := by
        dsimp only [D]
        push_cast
        ring
      _ ≤ 128 * (2 * (j : Real)) ^ (6 : Nat) := by gcongr
      _ = 8192 * (j : Real) ^ (6 : Nat) := by ring
  have hjNat : j ≤ 2 ^ j := (Nat.lt_two_pow_self (n := j)).le
  have hjn : (j : Real) ≤ n := by
    dsimp only [n]
    exact_mod_cast hjNat
  have hpolyN : 128 * D ^ (3 : Nat) ≤ Real.exp (n / 4) :=
    hDcube.trans (hpolyJ.trans (Real.exp_le_exp.mpr (by linarith)))
  have hcrossExp :
      128 * D ^ (3 : Nat) * Real.exp q ≤ Real.exp (17 * n / 64) := by
    calc
      128 * D ^ (3 : Nat) * Real.exp q ≤
          Real.exp (n / 4) * Real.exp (n / 64) := by gcongr
      _ = Real.exp (17 * n / 64) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hTexp : Real.exp (Real.log 2 * n) = T := by
    dsimp only [n, T, Problem520.harperScheduledStrongComparisonFrequency]
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hsqrtT : Real.sqrt T = Real.exp (Real.log 2 * n / 2) := by
    rw [← hTexp, ← Real.exp_half]
  have hrate : 17 * n / 64 ≤ Real.log 2 * n / 2 := by
    have hlog : (17 / 32 : Real) ≤ Real.log 2 := by
      exact le_of_lt ((by norm_num : (17 / 32 : Real) < 0.6931471803).trans
        Real.log_two_gt_d9)
    nlinarith
  have hcross : 128 * D ^ (3 : Nat) * Real.exp q ≤ Real.sqrt T := by
    rw [hsqrtT]
    exact hcrossExp.trans (Real.exp_le_exp.mpr hrate)
  have hsqrtTPos : 0 < Real.sqrt T := Real.sqrt_pos.2 hTPos
  have hdenPos : 0 < 64 * D ^ (3 : Nat) * Real.exp q := by positivity
  have hdiv :
      2 / Real.sqrt T ≤ 1 / (64 * D ^ (3 : Nat) * Real.exp q) := by
    rw [div_le_div_iff₀ hsqrtTPos hdenPos]
    nlinarith
  calc
    2 / Real.sqrt
        (Problem520.harperScheduledStrongComparisonFrequency j) =
        2 / Real.sqrt T := rfl
    _ ≤ 1 / (64 * D ^ (3 : Nat) * Real.exp q) := hdiv
    _ = delta * ((delta ^ (2 : Nat) / 64) * Real.exp (-q)) := by
      dsimp only [delta, D, Problem520.harperScheduledRelativeIntervalWidth]
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    _ = Problem520.harperScheduledRelativeIntervalWidth j *
        ((Problem520.harperScheduledRelativeIntervalWidth j ^ (2 : Nat) / 64) *
          Real.exp (-2 *
            ((|a| + 1) ^ (2 : Nat) +
              (|b - lambda * a +
                  Problem520.harperScheduledRelativeIntervalWidth j / 4| + 1) ^
                (2 : Nat)))) := by
      dsimp only [delta, q]
      rw [neg_mul]

/-- The scheduled strong frequency has eight full powers available before the
square root of the block endpoint.  The one-dimensional comparison only needs
five; the three spare powers pay for bivariate Fourier inversion. -/
theorem harperScheduledStrongComparisonFrequency_pow_eight_le_sqrt_endpoint
    (j : Nat) :
    Problem520.harperScheduledStrongComparisonFrequency j ^ (8 : Nat) ≤
      Real.sqrt (Problem520.harperBlockEndpoint j : Real) := by
  have hsq :
      (Problem520.harperScheduledStrongComparisonFrequency j ^ (8 : Nat)) ^
          (2 : Nat) ≤
        (Problem520.harperBlockEndpoint j : Real) := by
    have hexp : 2 ^ j * 8 * 2 = 16 * 2 ^ j := by omega
    simpa only [Problem520.harperScheduledStrongComparisonFrequency,
      Problem520.harperBlockEndpoint, Nat.cast_pow, Nat.cast_ofNat,
      ← pow_mul, hexp] using
        (le_refl ((2 : Real) ^ (16 * 2 ^ j)))
  exact Real.le_sqrt_of_sq_le hsq

private theorem bivariateFourierError_le_tail_of_large_frequency
    {F S delta : Real}
    (hF : 65536 ≤ F) (hFS : F ^ (8 : Nat) ≤ S)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (2 * Real.pi)⁻¹ ^ (2 : Nat) *
          |delta + 2 * (Real.sqrt F / (F / 2))| ^ (2 : Nat) * S⁻¹ *
            (512 * (F / 2) ^ (5 : Nat) +
              128 * (F / 2) ^ (6 : Nat)) ≤
        2 / Real.sqrt F := by
  have hFPos : 0 < F := lt_of_lt_of_le (by norm_num) hF
  have hFOne : 1 ≤ F := by linarith
  have hsqrtPos : 0 < Real.sqrt F := Real.sqrt_pos.2 hFPos
  have hsqrtSq : Real.sqrt F ^ (2 : Nat) = F := Real.sq_sqrt hFPos.le
  have htwoSqrt : (2 : Real) ≤ Real.sqrt F := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hsqrtLe : Real.sqrt F ≤ F := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hFPos.le
    · nlinarith [hFOne]
  have hratio : Real.sqrt F / (F / 2) = 2 / Real.sqrt F := by
    field_simp [hFPos.ne', hsqrtPos.ne']
    nlinarith
  have hwidth0 : 0 ≤ delta + 2 * (Real.sqrt F / (F / 2)) := by
    positivity
  have hwidth :
      |delta + 2 * (Real.sqrt F / (F / 2))| ≤ 3 := by
    rw [abs_of_nonneg hwidth0, hratio]
    have hdiv : 2 / Real.sqrt F ≤ 1 := by
      rw [div_le_one hsqrtPos]
      exact htwoSqrt
    nlinarith
  have htwoPiPos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have htwoPiOne : (1 : Real) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hpiInv : (2 * Real.pi)⁻¹ ≤ (1 : Real) :=
    (inv_le_one₀ htwoPiPos).2 htwoPiOne
  have hpiInv0 : 0 ≤ (2 * Real.pi)⁻¹ := inv_nonneg.2 htwoPiPos.le
  have hpiSq : (2 * Real.pi)⁻¹ ^ (2 : Nat) ≤ (1 : Real) :=
    pow_le_one₀ hpiInv0 hpiInv
  have hT0 : 0 ≤ F / 2 := by positivity
  have hTle : F / 2 ≤ F := by linarith
  have hT5 : (F / 2) ^ (5 : Nat) ≤ F ^ (6 : Nat) := by
    calc
      (F / 2) ^ (5 : Nat) ≤ F ^ (5 : Nat) := by gcongr
      _ ≤ F ^ (6 : Nat) := by
        exact pow_le_pow_right₀ hFOne (by norm_num)
  have hT6 : (F / 2) ^ (6 : Nat) ≤ F ^ (6 : Nat) := by gcongr
  have hpoly :
      512 * (F / 2) ^ (5 : Nat) + 128 * (F / 2) ^ (6 : Nat) ≤
        640 * F ^ (6 : Nat) := by
    nlinarith
  have hSPos : 0 < S := (pow_pos hFPos 8).trans_le hFS
  have hSinv : S⁻¹ ≤ (F ^ (8 : Nat))⁻¹ :=
    (inv_le_inv₀ hSPos (pow_pos hFPos 8)).2 hFS
  have hmain :
      (2 * Real.pi)⁻¹ ^ (2 : Nat) *
            |delta + 2 * (Real.sqrt F / (F / 2))| ^ (2 : Nat) * S⁻¹ *
              (512 * (F / 2) ^ (5 : Nat) +
                128 * (F / 2) ^ (6 : Nat)) ≤
          5760 / F ^ (2 : Nat) := by
    calc
      _ ≤ 1 * 3 ^ (2 : Nat) * (F ^ (8 : Nat))⁻¹ *
          (640 * F ^ (6 : Nat)) := by
        gcongr
      _ = 5760 / F ^ (2 : Nat) := by
        field_simp [hFPos.ne']
        ring
  have hlarge : 5760 / F ^ (2 : Nat) ≤ 2 / F := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hFPos) hFPos]
    nlinarith
  have hlast : 2 / F ≤ 2 / Real.sqrt F := by
    exact div_le_div_of_nonneg_left (by norm_num) hsqrtPos hsqrtLe
  exact hmain.trans (hlarge.trans hlast)

/-- With `T` equal to half the strong scheduled frequency and Fejer parameter
`sqrt(strong frequency)`, the explicit bivariate Fourier remainder is no
larger than the Fejer tail. -/
theorem eventually_harperScheduledBivariateFourierError_le_fejerTail :
    ∀ᶠ j : Nat in atTop,
      (2 * Real.pi)⁻¹ ^ (2 : Nat) *
          |Problem520.harperScheduledRelativeIntervalWidth j +
              2 * (Real.sqrt
                (Problem520.harperScheduledStrongComparisonFrequency j) /
                  (Problem520.harperScheduledStrongComparisonFrequency j / 2))| ^
            (2 : Nat) *
          (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
          (512 *
                (Problem520.harperScheduledStrongComparisonFrequency j / 2) ^
                  (5 : Nat) +
            128 *
                (Problem520.harperScheduledStrongComparisonFrequency j / 2) ^
                  (6 : Nat)) ≤
        2 / Real.sqrt
          (Problem520.harperScheduledStrongComparisonFrequency j) := by
  filter_upwards [eventually_ge_atTop (4 : Nat)] with j hj
  have hpow : (16 : Nat) ≤ 2 ^ j := by
    simpa only [show (16 : Nat) = 2 ^ 4 by norm_num] using
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hj
  have hF : (65536 : Real) ≤
      Problem520.harperScheduledStrongComparisonFrequency j := by
    calc
      (65536 : Real) = ((2 ^ 16 : Nat) : Real) := by norm_num
      _ ≤ ((2 ^ (2 ^ j) : Nat) : Real) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hpow
      _ = Problem520.harperScheduledStrongComparisonFrequency j := by
        simp only [Problem520.harperScheduledStrongComparisonFrequency,
          Nat.cast_pow, Nat.cast_ofNat]
  exact bivariateFourierError_le_tail_of_large_frequency hF
    (harperScheduledStrongComparisonFrequency_pow_eight_le_sqrt_endpoint j)
    (Problem520.harperScheduledRelativeIntervalWidth_pos j).le
    (Problem520.harperScheduledRelativeIntervalWidth_le_one j)

/-- After the natural dyadic coherence cutoff, the exact scheduled correlated
Gaussian assigns the elementary regression lower bound to every square cell.
No path-length-dependent decorrelation cutoff is used. -/
theorem exists_harperScheduledTwoHeightGaussianRectangleMass_lower :
    ∃ J : Nat, ∀ shell j y : Nat, J + (shell + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ a b delta : Real, 0 < delta → delta ≤ 1 →
                (delta ^ (2 : Nat) / 64) *
                    Real.exp (-2 *
                      ((|a| + 1) ^ (2 : Nat) +
                        (|b -
                            harperTwoHeightRegressionCoefficient y
                              (Problem520.harperScheduledPrimeBlock y j) t s * a +
                            delta / 4| + 1) ^ (2 : Nat))) ≤
                  (harperTwoHeightGaussianLaw y
                    (Problem520.harperScheduledPrimeBlock y j) t s).real
                      (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) := by
  obtain ⟨Jsmall, hsmall⟩ :=
    exists_eventually_harperTwoHeightScheduledCovariance_postCoherence_small
      (by norm_num : (0 : Real) < 1 / 8)
  obtain ⟨Jvar, hvar⟩ :=
    exists_eventually_harperTwoHeightScheduledCoordinateVariance_third_threeEighths
  refine ⟨max Jsmall Jvar, ?_⟩
  intro shell j y hj hy t ht s hs hsep a b delta hdelta0 hdelta1
  have hjSmall : Jsmall + (shell + 1) ≤ j := by
    omega
  have hjVar : Jvar ≤ j := by
    omega
  have hvarj := hvar j hjVar y hy t ht s hs
  have htt := hvarj t ht
  have hss := hvarj s hs
  have hq :
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
        (1 / 8 : Real) :=
    (hsmall shell j y hjSmall hy t ht s hs hsep).le
  have httPos : 0 < harperTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) t s t t := by
    linarith [htt.1]
  have hres := regressionResidualVariance_quarter_half
    htt.1.le htt.2.le hss.1.le hss.2.le hq
  have hlambda :
      |harperTwoHeightRegressionCoefficient y
          (Problem520.harperScheduledPrimeBlock y j) t s| ≤
        (3 / 8 : Real) := by
    unfold harperTwoHeightRegressionCoefficient
    have h := abs_regressionCoefficient_le_three_mul
      htt.1.le (by norm_num : (0 : Real) ≤ 1 / 8) hq
    norm_num at h ⊢
    exact h
  rw [harperTwoHeightGaussianLaw_eq_regression _ _ _ _ httPos]
  apply harperGaussianRegressionBlockLaw_rectangleMass_lower
  · simpa only [coe_harperTwoHeightCoordinateVarianceNNReal] using
      (show (1 / 4 : Real) ≤
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) t s t t by
        linarith [htt.1])
  · simpa only [coe_harperTwoHeightCoordinateVarianceNNReal] using
      (show harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) t s t t ≤
          (1 / 2 : Real) by
        linarith [htt.2])
  · simpa only [coe_harperTwoHeightRegressionResidualVarianceNNReal] using hres.1
  · simpa only [coe_harperTwoHeightRegressionResidualVarianceNNReal] using hres.2
  · exact hlambda
  · exact hdelta0
  · exact hdelta1

/-- One scheduled two-height Rademacher cell is bounded by the corresponding
slightly expanded correlated-Gaussian cell with a summable relative loss.
The comparison begins at the natural shell coherence index; there is no
`n⁻⁴⁰` covariance cutoff and no path-length-dependent delay. -/
theorem exists_harperScheduledTwoHeightRelativeRectangleProbability_le :
    ∃ J : Nat, ∀ shell j y : Nat, J + (shell + 1) ≤ j →
      Problem520.harperBlockEndpoint (j + 1) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ a b : Real,
                |a| + |b| + 3 ≤
                    (1 / 16 : Real) *
                      Real.sqrt (((2 ^ j : Nat) : Real)) →
                  (1 - 2 / Real.sqrt
                      (Problem520.harperScheduledStrongComparisonFrequency j)) ^
                        (2 : Nat) *
                      (harperTwoHeightPrimeBlockVectorLaw y
                        (Problem520.harperScheduledPrimeBlock y j) t s).real
                          (Ioc a
                              (a + Problem520.harperScheduledRelativeIntervalWidth j) ×ˢ
                            Ioc b
                              (b + Problem520.harperScheduledRelativeIntervalWidth j)) ≤
                    (1 + 2 * Problem520.harperScheduledRelativeIntervalWidth j) *
                      (harperTwoHeightGaussianLaw y
                        (Problem520.harperScheduledPrimeBlock y j) t s).real
                        (Ioc
                            (a - 2 *
                              (Real.sqrt
                                  (Problem520.harperScheduledStrongComparisonFrequency j) /
                                (Problem520.harperScheduledStrongComparisonFrequency j / 2)))
                            ((a + Problem520.harperScheduledRelativeIntervalWidth j) +
                              2 *
                                (Real.sqrt
                                    (Problem520.harperScheduledStrongComparisonFrequency j) /
                                  (Problem520.harperScheduledStrongComparisonFrequency j / 2))) ×ˢ
                          Ioc
                            (b - 2 *
                              (Real.sqrt
                                  (Problem520.harperScheduledStrongComparisonFrequency j) /
                                (Problem520.harperScheduledStrongComparisonFrequency j / 2)))
                            ((b + Problem520.harperScheduledRelativeIntervalWidth j) +
                              2 *
                                (Real.sqrt
                                    (Problem520.harperScheduledStrongComparisonFrequency j) /
                                  (Problem520.harperScheduledStrongComparisonFrequency j / 2)))) := by
  obtain ⟨Jtail, htail⟩ := Filter.eventually_atTop.1
    eventually_harperScheduledBivariateFejerTail_le_relativeGaussianMass
  obtain ⟨Jfourier, hfourier⟩ := Filter.eventually_atTop.1
    eventually_harperScheduledBivariateFourierError_le_fejerTail
  obtain ⟨Jgauss, hgauss⟩ :=
    exists_harperScheduledTwoHeightGaussianRectangleMass_lower
  obtain ⟨Jsmall, hsmall⟩ :=
    exists_eventually_harperTwoHeightScheduledCovariance_postCoherence_small
      (by norm_num : (0 : Real) < 1 / 8)
  obtain ⟨Jvar, hvar⟩ :=
    exists_eventually_harperTwoHeightScheduledCoordinateVariance_third_threeEighths
  let J := max 4 (max Jtail (max Jfourier (max Jgauss (max Jsmall Jvar))))
  refine ⟨J, ?_⟩
  intro shell j y hj hy t ht s hs hsep a b hmoderate
  have hjFour : 4 ≤ j := by
    dsimp only [J] at hj
    omega
  have hjTail : Jtail ≤ j := by
    dsimp only [J] at hj
    omega
  have hjFourier : Jfourier ≤ j := by
    dsimp only [J] at hj
    omega
  have hjGauss : Jgauss + (shell + 1) ≤ j := by
    dsimp only [J] at hj
    omega
  have hjSmall : Jsmall + (shell + 1) ≤ j := by
    dsimp only [J] at hj
    omega
  have hjVar : Jvar ≤ j := by
    dsimp only [J] at hj
    omega
  let F : Real := Problem520.harperScheduledStrongComparisonFrequency j
  let T : Real := F / 2
  let r : Real := Real.sqrt F
  let delta : Real := Problem520.harperScheduledRelativeIntervalWidth j
  let lambda : Real := harperTwoHeightRegressionCoefficient y
    (Problem520.harperScheduledPrimeBlock y j) t s
  let nu : Measure (Real × Real) := harperTwoHeightGaussianLaw y
    (Problem520.harperScheduledPrimeBlock y j) t s
  have hFPos : 0 < F := by
    dsimp only [F]
    exact Problem520.harperScheduledStrongComparisonFrequency_pos j
  have hTPos : 0 < T := by dsimp only [T]; positivity
  have hrPos : 0 < r := by dsimp only [r]; exact Real.sqrt_pos.2 hFPos
  have hdeltaPos : 0 < delta := by
    dsimp only [delta]
    exact Problem520.harperScheduledRelativeIntervalWidth_pos j
  have hdeltaOne : delta ≤ 1 := by
    dsimp only [delta]
    exact Problem520.harperScheduledRelativeIntervalWidth_le_one j
  have hpow : (16 : Nat) ≤ 2 ^ j := by
    simpa only [show (16 : Nat) = 2 ^ 4 by norm_num] using
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hjFour
  have hFlarge : (65536 : Real) ≤ F := by
    dsimp only [F]
    calc
      (65536 : Real) = ((2 ^ 16 : Nat) : Real) := by norm_num
      _ ≤ ((2 ^ (2 ^ j) : Nat) : Real) := by
        exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hpow
      _ = Problem520.harperScheduledStrongComparisonFrequency j := by
        simp only [Problem520.harperScheduledStrongComparisonFrequency,
          Nat.cast_pow, Nat.cast_ofNat]
  have hrTwo : 2 ≤ r := by
    dsimp only [r]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hfrequency :
      4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : Real) := by
    dsimp only [T, F]
    convert Problem520.harperScheduledStrongComparisonFrequency_condition j using 1 <;>
      ring
  have hvarj := hvar j hjVar y hy t ht s hs
  have htt := hvarj t ht
  have hq :
      |harperTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
        (1 / 8 : Real) :=
    (hsmall shell j y hjSmall hy t ht s hs hsep).le
  have hlambda : |lambda| ≤ (3 / 8 : Real) := by
    dsimp only [lambda, harperTwoHeightRegressionCoefficient]
    have h := abs_regressionCoefficient_le_three_mul
      htt.1.le (by norm_num : (0 : Real) ≤ 1 / 8) hq
    norm_num at h ⊢
    exact h
  have htailBudget := htail j hjTail lambda a b hlambda hmoderate
  have hgaussLower := hgauss shell j y hjGauss hy t ht s hs hsep
    a b delta hdeltaPos hdeltaOne
  have htailGauss :
      2 / r ≤ delta *
        nu.real (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) := by
    calc
      2 / r ≤ delta *
          ((delta ^ (2 : Nat) / 64) *
            Real.exp (-2 *
              ((|a| + 1) ^ (2 : Nat) +
                (|b - lambda * a + delta / 4| + 1) ^ (2 : Nat)))) := by
        simpa only [r, F, delta] using htailBudget
      _ ≤ delta * nu.real
          (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) := by
        gcongr
  have hfourierTail :
      (2 * Real.pi)⁻¹ ^ (2 : Nat) *
            |((a + delta) + r / T) - (a - r / T)| *
            |((b + delta) + r / T) - (b - r / T)| *
            (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
              (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) ≤
          2 / r := by
    have hf := hfourier j hjFourier
    simpa only [F, T, r, delta,
      show ((a + Problem520.harperScheduledRelativeIntervalWidth j) +
          Real.sqrt (Problem520.harperScheduledStrongComparisonFrequency j) /
            (Problem520.harperScheduledStrongComparisonFrequency j / 2)) -
          (a - Real.sqrt
            (Problem520.harperScheduledStrongComparisonFrequency j) /
              (Problem520.harperScheduledStrongComparisonFrequency j / 2)) =
        Problem520.harperScheduledRelativeIntervalWidth j +
          2 * (Real.sqrt
            (Problem520.harperScheduledStrongComparisonFrequency j) /
              (Problem520.harperScheduledStrongComparisonFrequency j / 2)) by ring,
      show ((b + Problem520.harperScheduledRelativeIntervalWidth j) +
          Real.sqrt (Problem520.harperScheduledStrongComparisonFrequency j) /
            (Problem520.harperScheduledStrongComparisonFrequency j / 2)) -
          (b - Real.sqrt
            (Problem520.harperScheduledStrongComparisonFrequency j) /
              (Problem520.harperScheduledStrongComparisonFrequency j / 2)) =
        Problem520.harperScheduledRelativeIntervalWidth j +
          2 * (Real.sqrt
            (Problem520.harperScheduledStrongComparisonFrequency j) /
              (Problem520.harperScheduledStrongComparisonFrequency j / 2)) by ring,
      pow_two, mul_assoc] using hf
  have hraw := harperScheduledTwoHeightRectangleMass_le_gaussianExpanded_explicit
    y j t s T r
      (a := a) (b := a + delta) (c := b) (d := b + delta)
      (by linarith) (by linarith) hTPos hrTwo hfrequency
  let expanded : Set (Real × Real) :=
    Ioc (a - 2 * (r / T)) ((a + delta) + 2 * (r / T)) ×ˢ
      Ioc (b - 2 * (r / T)) ((b + delta) + 2 * (r / T))
  have hsubset :
      Ioc a (a + delta) ×ˢ Ioc b (b + delta) ⊆ expanded := by
    intro z hz
    have hexpand : 0 ≤ 2 * (r / T) := by positivity
    constructor <;> constructor <;> dsimp only [expanded] <;>
      linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  have hmono :
      nu.real (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) ≤
        nu.real expanded := measureReal_mono hsubset
  have hfourierGauss :
      (2 * Real.pi)⁻¹ ^ (2 : Nat) *
            |((a + delta) + r / T) - (a - r / T)| *
            |((b + delta) + r / T) - (b - r / T)| *
            (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
              (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) ≤
          delta * nu.real (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) :=
    hfourierTail.trans htailGauss
  change (1 - 2 / r) ^ (2 : Nat) *
      (harperTwoHeightPrimeBlockVectorLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s).real
          (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) ≤
    (1 + 2 * delta) * nu.real expanded
  calc
    _ ≤ nu.real expanded + 2 / r +
        (2 * Real.pi)⁻¹ ^ (2 : Nat) *
          |((a + delta) + r / T) - (a - r / T)| *
          |((b + delta) + r / T) - (b - r / T)| *
          (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
            (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) := by
      simpa only [nu, expanded] using hraw
    _ ≤ nu.real expanded +
          delta * nu.real (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) +
          delta * nu.real (Ioc a (a + delta) ×ˢ Ioc b (b + delta)) := by
      gcongr
    _ ≤ (1 + 2 * delta) * nu.real expanded := by
      nlinarith [hmono, (measureReal_nonneg : 0 ≤ nu.real expanded),
        hdeltaPos.le]

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.eventually_harperScheduledBivariateFejerTail_le_relativeGaussianMass
#print axioms Erdos.Problem1144.harperScheduledStrongComparisonFrequency_pow_eight_le_sqrt_endpoint
#print axioms Erdos.Problem1144.eventually_harperScheduledBivariateFourierError_le_fejerTail
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightGaussianRectangleMass_lower
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightRelativeRectangleProbability_le
