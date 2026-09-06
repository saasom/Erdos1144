import Erdos.Problem1144.HarperCandidateEnergyTwoHeightScheduled
import Erdos.Problem1144.HarperBivariateFejerInversion

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

/-- Nonnegativity of a literal shifted marginal covariance. -/
theorem candidate_rankinTwoHeightCoordinateVariance_nonneg
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s u : ℝ) :
    0 ≤ harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s u u := by
  unfold harperRankinTwoHeightBlockCoordinateCovariance
  apply Finset.sum_nonneg
  intro p hp
  rw [mul_assoc, ← pow_two]
  apply mul_nonneg _ (sq_nonneg _)
  exact integral_nonneg fun b => sq_nonneg _

noncomputable def candidateRankinTwoHeightCoordinateVarianceNNReal
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s u : Real) : NNReal :=
  ⟨harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s u u,
    candidate_rankinTwoHeightCoordinateVariance_nonneg y S a ha t s u⟩

@[simp] theorem coe_candidateRankinTwoHeightCoordinateVarianceNNReal
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s u : Real) :
    (candidateRankinTwoHeightCoordinateVarianceNNReal y S a ha t s u : Real) =
      harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s u u := rfl

/-- Product of the two exact marginal Gaussian laws of one block. -/
noncomputable def candidateRankinTwoHeightIndependentGaussianBlockLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s : Real) : Measure (Real × Real) :=
  (gaussianReal 0
      (candidateRankinTwoHeightCoordinateVarianceNNReal y S a ha t s t)).prod
    (gaussianReal 0
      (candidateRankinTwoHeightCoordinateVarianceNNReal y S a ha t s s))

instance candidateRankinTwoHeightIndependentGaussianBlockLaw_isProbabilityMeasure
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s : Real) :
    IsProbabilityMeasure
      (candidateRankinTwoHeightIndependentGaussianBlockLaw y S a ha t s) := by
  unfold candidateRankinTwoHeightIndependentGaussianBlockLaw
  infer_instance

theorem candidate_rankinBivariateCharacteristic_independentGaussianBlockLaw
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : Real) :
    harperBivariateCharacteristic
        (candidateRankinTwoHeightIndependentGaussianBlockLaw y S a ha t s) (v, w) =
      Complex.exp
        (-(((v ^ (2 : Nat) *
              harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s t t +
            w ^ (2 : Nat) *
              harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s s s) / 2 :
                Real) : Complex)) := by
  rw [harperBivariateCharacteristic]
  unfold candidateRankinTwoHeightIndependentGaussianBlockLaw
  rw [charFunDual_prod]
  have hvcomp :
      (harperTwoHeightProjection v w).comp
          (ContinuousLinearMap.inl Real Real Real) =
        InnerProductSpace.toDualMap Real Real v := by
    ext
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      harperTwoHeightProjection_apply, mul_zero, add_zero,
      InnerProductSpace.toDualMap_apply_apply]
    rw [real_inner_eq_re_inner Real]
    simp [RCLike.inner_apply]
  have hwcomp :
      (harperTwoHeightProjection v w).comp
          (ContinuousLinearMap.inr Real Real Real) =
        InnerProductSpace.toDualMap Real Real w := by
    ext
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      harperTwoHeightProjection_apply, InnerProductSpace.toDualMap_apply_apply]
    rw [real_inner_eq_re_inner Real]
    simp [RCLike.inner_apply]
  rw [hvcomp, hwcomp, ← charFun_eq_charFunDual_toDualMap,
    ← charFun_eq_charFunDual_toDualMap]
  change
    charFun (gaussianReal 0
        (candidateRankinTwoHeightCoordinateVarianceNNReal y S a ha t s t)) v *
      charFun (gaussianReal 0
        (candidateRankinTwoHeightCoordinateVarianceNNReal y S a ha t s s)) w = _
  rw [charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add]
  simp only [coe_candidateRankinTwoHeightCoordinateVarianceNNReal]
  congr 1
  push_cast
  ring


/-- Dropping the actual off-diagonal covariance costs only its product
with the two Fourier frequencies. -/
theorem candidate_norm_rankinGaussianCharacteristic_sub_independent_le
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ) :
    ‖Complex.exp (-((harperRankinTwoHeightProjectedBlockVariance y S a ha t s v w / 2 : ℝ) : ℂ)) -
      harperBivariateCharacteristic
        (candidateRankinTwoHeightIndependentGaussianBlockLaw y S a ha t s) (v, w)‖ ≤
      |harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s t s| * |v| * |w| := by
  let U := harperRankinTwoHeightProjectedBlockVariance y S a ha t s v w / 2
  let D := (v ^ 2 * harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s t t +
    w ^ 2 * harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s s s) / 2
  have hU : 0 ≤ U := div_nonneg
    (harperRankinTwoHeightProjectedBlockVariance_nonneg y S a ha t s v w) (by norm_num)
  have hD : 0 ≤ D := div_nonneg
    (add_nonneg (mul_nonneg (sq_nonneg _) (candidate_rankinTwoHeightCoordinateVariance_nonneg y S a ha t s t))
      (mul_nonneg (sq_nonneg _) (candidate_rankinTwoHeightCoordinateVariance_nonneg y S a ha t s s)))
    (by norm_num)
  rw [candidate_rankinBivariateCharacteristic_independentGaussianBlockLaw]
  change ‖Complex.exp (-(U : ℂ)) - Complex.exp (-(D : ℂ))‖ ≤ _
  rw [← Complex.ofReal_neg, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_exp_neg_sub_exp_neg_le_abs_sub hU hD).trans_eq ?_
  have heq : U - D = v * w * harperRankinTwoHeightBlockCoordinateCovariance y S a ha t s t s := by
    dsimp only [U, D]
    rw [harperRankinTwoHeightProjectedBlockVariance_eq_coordinateCovariance]
    ring
  rw [heq, abs_mul, abs_mul]
  ring

/-- Direct characteristic comparison of the actual shifted pair law with
its independent marginal Gaussian, with every error explicit. -/
theorem candidate_rankinScheduledCharacteristic_sub_independent_le
    (y j : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ)
    (hfrequency : 2 * (|v| + |w|) ≤ Real.sqrt (Problem520.harperBlockEndpoint j : ℝ)) :
    ‖harperBivariateCharacteristic (harperRankinTwoHeightPrimeBlockVectorLaw y
      (Problem520.harperScheduledPrimeBlock y j) a ha t s) (v, w) -
      harperBivariateCharacteristic (candidateRankinTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y j) a ha t s) (v, w)‖ ≤
      (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
        (16 * (|v| + |w|) ^ 3 + 2 * (|v| + |w|) ^ 4) +
      |harperRankinTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) a ha t s t s| * |v| * |w| := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add
    (norm_charFunDual_harperRankinTwoHeightScheduledVectorLaw_sub_gaussian_le
      y j a ha t s v w hfrequency)
    (candidate_norm_rankinGaussianCharacteristic_sub_independent_le y
      (Problem520.harperScheduledPrimeBlock y j) a ha t s v w))

/-- Literal Fejer-smoothed rectangle comparison, directly to independent
marginals. Both the radial characteristic and covariance errors are retained. -/
theorem candidate_rankinScheduledSmoothRectangle_sub_independent_le
    (y j : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s T l r b d : ℝ) (hT : 0 < T)
    (hfrequency : 4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : ℝ)) :
    |harperBivariateSmoothRectangle (Problem520.harperFejerMeasureScaled T)
      (harperRankinTwoHeightPrimeBlockVectorLaw y (Problem520.harperScheduledPrimeBlock y j)
        a ha t s) l r b d -
      harperBivariateSmoothRectangle (Problem520.harperFejerMeasureScaled T)
        (candidateRankinTwoHeightIndependentGaussianBlockLaw y
          (Problem520.harperScheduledPrimeBlock y j) a ha t s) l r b d| ≤
      (2 * Real.pi)⁻¹ ^ 2 * |r - l| * |d - b| *
        (16 * |harperRankinTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) a ha t s t s| * T ^ 4 +
          (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ * (512 * T ^ 5 + 128 * T ^ 6)) := by
  let q := (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹
  let c := |harperRankinTwoHeightBlockCoordinateCovariance y
    (Problem520.harperScheduledPrimeBlock y j) a ha t s t s|
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hc : 0 ≤ c := abs_nonneg _
  have hbound := abs_harperBivariateSmoothRectangle_sub_le_of_identity_quadratic
    (harperRankinTwoHeightPrimeBlockVectorLaw y (Problem520.harperScheduledPrimeBlock y j) a ha t s)
    (candidateRankinTwoHeightIndependentGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y j) a ha t s)
    T (c + q * (32 * T + 8 * T ^ 2)) l r b d hT.le (by positivity)
    (harperBivariateFejerRectangleIdentity_of_pos _ _ hT) ?_
  · convert hbound using 1 <;> dsimp only [c, q] <;> ring
  · intro z hz
    have hz1 : |z.1| ≤ T := abs_le.mpr ⟨by linarith [hz.1.1], hz.1.2⟩
    have hz2 : |z.2| ≤ T := abs_le.mpr ⟨by linarith [hz.2.1], hz.2.2⟩
    have hf : 2 * (|z.1| + |z.2|) ≤ Real.sqrt (Problem520.harperBlockEndpoint j : ℝ) := by linarith
    have hbase := candidate_rankinScheduledCharacteristic_sub_independent_le y j a ha t s z.1 z.2 hf
    change _ ≤ q * (16 * (|z.1| + |z.2|) ^ 3 + 2 * (|z.1| + |z.2|) ^ 4) +
      c * |z.1| * |z.2| at hbase
    refine hbase.trans ?_
    let L := |z.1| + |z.2|
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hLT : L ≤ 2 * T := by dsimp [L]; linarith
    have hL3 : L ^ 3 ≤ (2 * T) * L ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hLT (sq_nonneg L)]
    have hL4 : L ^ 4 ≤ (4 * T ^ 2) * L ^ 2 := by
      have hL2 : L ^ 2 ≤ 4 * T ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hL2 (sq_nonneg L)]
    have hprod : |z.1| * |z.2| ≤ L ^ 2 := by
      dsimp [L]
      nlinarith [abs_nonneg z.1, abs_nonneg z.2, sq_nonneg (|z.1| - |z.2|)]
    have hpoly := add_le_add (mul_le_mul_of_nonneg_left hL3 (by norm_num : (0 : ℝ) ≤ 16))
      (mul_le_mul_of_nonneg_left hL4 (by norm_num : (0 : ℝ) ≤ 2))
    have h1 := mul_le_mul_of_nonneg_left hpoly hq
    have h2 := mul_le_mul_of_nonneg_left hprod hc
    change q * (16 * L ^ 3 + 2 * L ^ 4) + c * |z.1| * |z.2| ≤
      (c + q * (32 * T + 8 * T ^ 2)) * L ^ 2
    nlinarith

/-- Actual half-open rectangle comparison obtained by Fourier smoothing
and unsmoothing. The target is the independent Gaussian with exact marginals. -/
theorem candidate_rankinScheduledRectangleMass_le_independent_explicit
    (y j : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (t s T R : ℝ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hT : 0 < T) (hR : 2 ≤ R)
    (hfrequency : 4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : ℝ)) :
    (1 - 2 / R) ^ 2 * (harperRankinTwoHeightPrimeBlockVectorLaw y
      (Problem520.harperScheduledPrimeBlock y j) σ hσ t s).real (Ioc a b ×ˢ Ioc c d) ≤
      (candidateRankinTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y j) σ hσ t s).real
        (Ioc (a - 2 * (R / T)) (b + 2 * (R / T)) ×ˢ
          Ioc (c - 2 * (R / T)) (d + 2 * (R / T))) + 2 / R +
        (2 * Real.pi)⁻¹ ^ 2 * |(b + R / T) - (a - R / T)| *
          |(d + R / T) - (c - R / T)| *
          (16 * |harperRankinTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) σ hσ t s t s| * T ^ 4 +
            (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ * (512 * T ^ 5 + 128 * T ^ 6)) := by
  let P := harperRankinTwoHeightPrimeBlockVectorLaw y
    (Problem520.harperScheduledPrimeBlock y j) σ hσ t s
  let Q := candidateRankinTwoHeightIndependentGaussianBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) σ hσ t s
  let κ := Problem520.harperFejerMeasureScaled T
  have hδ : 0 ≤ R / T := div_nonneg (by linarith) hT.le
  have hα : 2 / R ≤ 1 := (div_le_one (by linarith)).mpr hR
  have htail := harperFejerMeasureScaled_tail_le_two_div hT hR
  have hlo := one_sub_sq_mul_rectangleMass_le_smoothExpanded κ P hab hcd hδ hα htail
  have hmid := candidate_rankinScheduledSmoothRectangle_sub_independent_le y j σ hσ t s T
    (a - R / T) (b + R / T) (c - R / T) (d + R / T) hT hfrequency
  have hup := smoothRectangle_le_expandedRectangleMass_add_tail κ Q
    (a := a - R / T) (b := b + R / T) (c := c - R / T) (d := d + R / T)
    (delta := R / T) (alpha := 2 / R)
    (by linarith) (by linarith) hδ (by positivity) htail
  have heq :
      (Ioc ((a - R / T) - R / T) ((b + R / T) + R / T) ×ˢ
        Ioc ((c - R / T) - R / T) ((d + R / T) + R / T)) =
      (Ioc (a - 2 * (R / T)) (b + 2 * (R / T)) ×ˢ
        Ioc (c - 2 * (R / T)) (d + 2 * (R / T))) := by ring_nf
  rw [heq] at hup
  have hmidOne := le_of_abs_le hmid
  change (1 - 2 / R) ^ 2 * P.real (Ioc a b ×ˢ Ioc c d) ≤ _
  dsimp only [P, Q, κ] at hlo hup ⊢
  linarith

end Erdos.Problem1144
