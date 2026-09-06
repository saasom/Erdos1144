import Erdos.Problem1144.HarperShiftedLatticeSuffix
import Erdos.Problem1144.HarperGaussianRegressionIdentification

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# A naturally coherent Gaussian suffix ballot

The translated suffix corridor has upper height `O(d)` after a common prefix
of length `d`.  Its elapsed-time lower guard controls every coordinate of the
first Gaussian path.  Geometrically decaying regression coefficients then
produce only an `O(d)` conditional drift.  Dropping the lower barriers after
this deterministic use reduces the correlated pair to a product of two
ordinary upper-ballot events and gives the required `O((d+1)^2/m)` cost.
-/

/-- The one-unit relaxed suffix guard bounds each increment at its elapsed
time scale. -/
theorem abs_coordinate_le_of_relaxed_suffix_partialSum_guard
    {d n : Nat} (omega : Fin n → Real)
    (hlower : ∀ k : Fin n,
      -64 * ((d + k.val + 1 : Nat) : Real) - 3 ≤
        Problem520.harperPathPartialSum omega k)
    (hupper : ∀ k : Fin n,
      Problem520.harperPathPartialSum omega k ≤ 64 * (d : Real) + 2)
    (i : Fin n) :
    |omega i| ≤ 128 * ((d + i.val + 1 : Nat) : Real) + 6 := by
  have habsSum (k : Fin n) :
      |Problem520.harperPathPartialSum omega k| ≤
        64 * ((d + k.val + 1 : Nat) : Real) + 3 := by
    rw [abs_le]
    constructor
    · linarith [hlower k]
    · have hdleNat : d ≤ d + k.val + 1 := by omega
      have hdle : (d : Real) ≤ ((d + k.val + 1 : Nat) : Real) := by
        exact_mod_cast hdleNat
      linarith [hupper k]
  by_cases hi : i.val = 0
  · have hset : Finset.Iic i = {i} := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_singleton]
      constructor
      · intro hji
        apply Fin.eq_of_val_eq
        have hj0 : j.val = 0 := by omega
        exact hj0.trans hi.symm
      · rintro rfl
        exact le_rfl
    have hiBound := habsSum i
    unfold Problem520.harperPathPartialSum at hiBound
    rw [hset, Finset.sum_singleton] at hiBound
    nlinarith
  · let p : Fin n := ⟨i.val - 1, by omega⟩
    have hset : Finset.Iic i = insert i (Finset.Iic p) := by
      ext j
      simp only [Finset.mem_Iic, Finset.mem_insert]
      constructor
      · intro hj
        by_cases hji : j = i
        · exact Or.inl hji
        · right
          change j.val ≤ p.val
          dsimp only [p]
          have hne : j.val ≠ i.val := by
            intro heq
            exact hji (Fin.eq_of_val_eq heq)
          omega
      · rintro (rfl | hj)
        · exact le_rfl
        · exact hj.trans (by
            change p.val ≤ i.val
            dsimp only [p]
            omega)
    have hinot : i ∉ Finset.Iic p := by
      simp only [Finset.mem_Iic]
      change ¬ i.val ≤ p.val
      dsimp only [p]
      omega
    have hsplit :
        Problem520.harperPathPartialSum omega i =
          omega i + Problem520.harperPathPartialSum omega p := by
      unfold Problem520.harperPathPartialSum
      rw [hset, Finset.sum_insert hinot]
    have hcoord : omega i =
        Problem520.harperPathPartialSum omega i -
          Problem520.harperPathPartialSum omega p := by
      linarith
    rw [hcoord]
    calc
      |Problem520.harperPathPartialSum omega i -
          Problem520.harperPathPartialSum omega p| ≤
          |Problem520.harperPathPartialSum omega i| +
            |Problem520.harperPathPartialSum omega p| := abs_sub _ _
      _ ≤ (64 * ((d + i.val + 1 : Nat) : Real) + 3) +
          (64 * ((d + p.val + 1 : Nat) : Real) + 3) := by
        exact add_le_add (habsSum i) (habsSum p)
      _ ≤ 128 * ((d + i.val + 1 : Nat) : Real) + 6 := by
        have hp : d + p.val + 1 ≤ d + i.val + 1 := by
          dsimp only [p]
          omega
        exact_mod_cast (show
          (64 * (d + i.val + 1) + 3) +
              (64 * (d + p.val + 1) + 3) ≤
            128 * (d + i.val + 1) + 6 by omega)

/-- The elapsed-time coordinate envelope and geometric regression decay give
an `O(d)` bound for every partial conditional drift. -/
theorem abs_partialSum_mul_le_of_relaxed_suffix_guard
    {d n : Nat} (lambda omega : Fin n → Real) (L : Real) (hL : 0 ≤ L)
    (hlambda : ∀ i : Fin n,
      |lambda i| ≤ L * (1 / 2 : Real) ^ i.val)
    (hlower : ∀ k : Fin n,
      -64 * ((d + k.val + 1 : Nat) : Real) - 3 ≤
        Problem520.harperPathPartialSum omega k)
    (hupper : ∀ k : Fin n,
      Problem520.harperPathPartialSum omega k ≤ 64 * (d : Real) + 2)
    (k : Fin n) :
    |Problem520.harperPathPartialSum (fun i ↦ lambda i * omega i) k| ≤
      536 * L * ((d + 1 : Nat) : Real) := by
  unfold Problem520.harperPathPartialSum
  calc
    |∑ i ∈ Finset.Iic k, lambda i * omega i| ≤
        ∑ i ∈ Finset.Iic k, |lambda i * omega i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Iic k,
        (134 * L * ((d + 1 : Nat) : Real)) *
          ((((i.val + 1 : Nat) : Real)) *
            (1 / 2 : Real) ^ i.val) := by
      gcongr with i hi
      rw [abs_mul]
      have homega := abs_coordinate_le_of_relaxed_suffix_partialSum_guard
        omega hlower hupper i
      have hpow : 0 ≤ (1 / 2 : Real) ^ i.val := by positivity
      have hdOne : (1 : Real) ≤ ((d + 1 : Nat) : Real) := by
        exact_mod_cast (show 1 ≤ d + 1 by omega)
      have hiOne : (1 : Real) ≤ ((i.val + 1 : Nat) : Real) := by
        exact_mod_cast (show 1 ≤ i.val + 1 by omega)
      have helapsed :
          ((d + i.val + 1 : Nat) : Real) ≤
            ((d + 1 : Nat) : Real) * ((i.val + 1 : Nat) : Real) := by
        exact_mod_cast (show d + i.val + 1 ≤ (d + 1) * (i.val + 1) by
          nlinarith)
      have hcoord :
          128 * ((d + i.val + 1 : Nat) : Real) + 6 ≤
            134 * ((d + 1 : Nat) : Real) *
              ((i.val + 1 : Nat) : Real) := by
        nlinarith
      calc
        |lambda i| * |omega i| ≤
            (L * (1 / 2 : Real) ^ i.val) *
              (128 * ((d + i.val + 1 : Nat) : Real) + 6) := by
          exact mul_le_mul (hlambda i) homega (abs_nonneg _)
            (mul_nonneg hL hpow)
        _ ≤ (L * (1 / 2 : Real) ^ i.val) *
              (134 * ((d + 1 : Nat) : Real) *
                ((i.val + 1 : Nat) : Real)) := by
          exact mul_le_mul_of_nonneg_left hcoord (mul_nonneg hL hpow)
        _ = (134 * L * ((d + 1 : Nat) : Real)) *
            (((i.val + 1 : Nat) : Real) *
              (1 / 2 : Real) ^ i.val) := by ring
    _ = (134 * L * ((d + 1 : Nat) : Real)) *
        (∑ i ∈ Finset.range (k.val + 1),
          (((i + 1 : Nat) : Real) * (1 / 2 : Real) ^ i)) := by
      rw [Finset.mul_sum]
      change Problem520.harperPathPartialSum
          (fun i : Fin n ↦
            (134 * L * ((d + 1 : Nat) : Real)) *
              ((((i.val + 1 : Nat) : Real)) *
                (1 / 2 : Real) ^ i.val)) k = _
      rw [Problem520.harperPathPartialSum_eq_sum_prefix]
      change (∑ i : Fin (k.val + 1),
        (134 * L * ((d + 1 : Nat) : Real)) *
          ((((i.val + 1 : Nat) : Real)) *
            (1 / 2 : Real) ^ i.val)) = _
      exact Fin.sum_univ_eq_sum_range
        (fun i : Nat ↦
          (134 * L * ((d + 1 : Nat) : Real)) *
            ((((i + 1 : Nat) : Real)) * (1 / 2 : Real) ^ i))
        (k.val + 1)
    _ ≤ (134 * L * ((d + 1 : Nat) : Real)) * 4 := by
      exact mul_le_mul_of_nonneg_left
        (sum_range_succ_mul_half_pow_le_four (k.val + 1))
        (mul_nonneg (mul_nonneg (by positivity) hL) (by positivity))
    _ = 536 * L * ((d + 1 : Nat) : Real) := by ring

/-- The relaxed scalar suffix corridor. -/
def harperRelaxedSuffixGuardPathEvent
    (d n : Nat) : Set (Fin n → Real) :=
  Problem520.harperPartialSumBarrierSet
    (fun k ↦ -64 * ((d + k.val + 1 : Nat) : Real) - 3)
    (fun _ ↦ 64 * (d : Real) + 2)

theorem measurableSet_harperRelaxedSuffixGuardPathEvent (d n : Nat) :
    MeasurableSet (harperRelaxedSuffixGuardPathEvent d n) := by
  exact Problem520.measurableSet_harperPartialSumBarrierSet _ _

/-- On the relaxed suffix guard, triangular regression is contained in two
independent upper-ballot events with heights `O(d)`. -/
theorem preimage_regression_relaxedSuffixGuard_subset_survival_product
    {d n : Nat} (lambda : Fin n → Real) (L : Real) (hL : 0 ≤ L)
    (hlambda : ∀ i : Fin n,
      |lambda i| ≤ L * (1 / 2 : Real) ^ i.val) :
    harperGaussianRegressionMap lambda ⁻¹'
        (harperRelaxedSuffixGuardPathEvent d n ×ˢ
          harperRelaxedSuffixGuardPathEvent d n) ⊆
      Problem520.gaussianWalkSurvivalSet n (64 * (d : Real) + 2) ×ˢ
        Problem520.gaussianWalkSurvivalSet n
          (64 * (d : Real) + 2 + 536 * L * ((d + 1 : Nat) : Real)) := by
  intro z hz
  have hx : z.1 ∈ harperRelaxedSuffixGuardPathEvent d n := hz.1
  have hy : (fun i ↦ lambda i * z.1 i + z.2 i) ∈
      harperRelaxedSuffixGuardPathEvent d n := hz.2
  constructor
  · change Problem520.gaussianWalkSurvives n (64 * (d : Real) + 2) z.1
    rw [gaussianWalkSurvives_iff_harperPathPartialSum_le]
    intro k
    exact (Problem520.mem_harperPartialSumBarrierSet.mp hx k).2
  · change Problem520.gaussianWalkSurvives n
      (64 * (d : Real) + 2 + 536 * L * ((d + 1 : Nat) : Real)) z.2
    rw [gaussianWalkSurvives_iff_harperPathPartialSum_le]
    intro k
    have hxlower : ∀ j : Fin n,
        -64 * ((d + j.val + 1 : Nat) : Real) - 3 ≤
          Problem520.harperPathPartialSum z.1 j := fun j ↦
      (Problem520.mem_harperPartialSumBarrierSet.mp hx j).1
    have hxupper : ∀ j : Fin n,
        Problem520.harperPathPartialSum z.1 j ≤ 64 * (d : Real) + 2 :=
      fun j ↦ (Problem520.mem_harperPartialSumBarrierSet.mp hx j).2
    have hyupper :=
      (Problem520.mem_harperPartialSumBarrierSet.mp hy k).2
    have hdrift := abs_partialSum_mul_le_of_relaxed_suffix_guard
      lambda z.1 L hL hlambda hxlower hxupper k
    have hsplit :
        Problem520.harperPathPartialSum
            (fun i ↦ lambda i * z.1 i + z.2 i) k =
          Problem520.harperPathPartialSum
              (fun i ↦ lambda i * z.1 i) k +
            Problem520.harperPathPartialSum z.2 k := by
      unfold Problem520.harperPathPartialSum
      rw [Finset.sum_add_distrib]
    rw [hsplit] at hyupper
    have hdriftLower :
        -(536 * L * ((d + 1 : Nat) : Real)) ≤
          Problem520.harperPathPartialSum
            (fun i ↦ lambda i * z.1 i) k := by
      rw [abs_le] at hdrift
      exact hdrift.1
    linarith

/-- A summably correlated Gaussian pair in the relaxed translated suffix
guard pays `O((d+1)^2/n)`, with an explicit constant. -/
theorem harperRegressedGaussianTwoWalk_relaxedSuffixGuard_probability_le
    {d n : Nat} (hn : 0 < n)
    (variance residualVariance : Fin n → NNReal)
    (lambda : Fin n → Real) (L : Real) (hL : 0 ≤ L)
    (hlambda : ∀ i : Fin n,
      |lambda i| ≤ L * (1 / 2 : Real) ^ i.val)
    (hvarianceLower : ∀ i, (1 / 4 : NNReal) ≤ variance i)
    (hvarianceUpper : ∀ i, variance i ≤ (1 / 2 : NNReal))
    (hresidualLower : ∀ i, (1 / 4 : NNReal) ≤ residualVariance i)
    (hresidualUpper : ∀ i, residualVariance i ≤ (1 / 2 : NNReal)) :
    (harperRegressedGaussianTwoWalkMeasure
        variance residualVariance lambda).real
      (harperRelaxedSuffixGuardPathEvent d n ×ˢ
        harperRelaxedSuffixGuardPathEvent d n) ≤
      (4096 * 68 * (536 * L + 68)) *
        (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (n : Real)⁻¹ := by
  let P := Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))
  let Q := Measure.pi
    (fun i : Fin n ↦ gaussianReal 0 (residualVariance i))
  let G := harperRelaxedSuffixGuardPathEvent d n
  let H₁ := Problem520.gaussianWalkSurvivalSet n (64 * (d : Real) + 2)
  let H₂ := Problem520.gaussianWalkSurvivalSet n
    (64 * (d : Real) + 2 + 536 * L * ((d + 1 : Nat) : Real))
  have hGmeas : MeasurableSet G :=
    measurableSet_harperRelaxedSuffixGuardPathEvent d n
  have hpairMeas : MeasurableSet (G ×ˢ G) := hGmeas.prod hGmeas
  have hmap :
      (harperRegressedGaussianTwoWalkMeasure
          variance residualVariance lambda).real (G ×ˢ G) =
        (P.prod Q).real
          (harperGaussianRegressionMap lambda ⁻¹' (G ×ˢ G)) := by
    unfold harperRegressedGaussianTwoWalkMeasure
      harperGaussianRegressionSource
    exact map_measureReal_apply
      (measurable_harperGaussianRegressionMap lambda) hpairMeas
  have hsubset :
      harperGaussianRegressionMap lambda ⁻¹' (G ×ˢ G) ⊆ H₁ ×ˢ H₂ := by
    simpa only [G, H₁, H₂] using
      preimage_regression_relaxedSuffixGuard_subset_survival_product
        (d := d) lambda L hL hlambda
  have hx₁ : 0 ≤ 64 * (d : Real) + 2 := by positivity
  have hx₂ :
      0 ≤ 64 * (d : Real) + 2 +
        536 * L * ((d + 1 : Nat) : Real) := by positivity
  have hfirst : P.real H₁ ≤
      (64 * 68 * ((d + 1 : Nat) : Real)) / Real.sqrt (n : Real) := by
    have hbase :=
      Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
        n hn variance hx₁ hvarianceLower hvarianceUpper
    have hd0 : 0 ≤ (d : Real) := by positivity
    dsimp only [P, H₁]
    calc
      (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
          (Problem520.gaussianWalkSurvivalSet n (64 * (d : Real) + 2)) ≤
        64 * (64 * (d : Real) + 2 + 2) /
          Real.sqrt (n : Real) := hbase
      _ ≤ (64 * 68 * ((d + 1 : Nat) : Real)) /
          Real.sqrt (n : Real) := by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith
  have hsecond : Q.real H₂ ≤
      (64 * (536 * L + 68) * ((d + 1 : Nat) : Real)) /
        Real.sqrt (n : Real) := by
    have hbase :=
      Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
        n hn residualVariance hx₂ hresidualLower hresidualUpper
    have hd0 : 0 ≤ (d : Real) := by positivity
    dsimp only [Q, H₂]
    calc
      (Measure.pi
          (fun i : Fin n ↦ gaussianReal 0 (residualVariance i))).real
          (Problem520.gaussianWalkSurvivalSet n
            (64 * (d : Real) + 2 +
              536 * L * ((d + 1 : Nat) : Real))) ≤
        64 *
            (64 * (d : Real) + 2 +
              536 * L * ((d + 1 : Nat) : Real) + 2) /
          Real.sqrt (n : Real) := hbase
      _ ≤ (64 * (536 * L + 68) * ((d + 1 : Nat) : Real)) /
          Real.sqrt (n : Real) := by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith
  have hproduct : (P.prod Q).real (H₁ ×ˢ H₂) =
      P.real H₁ * Q.real H₂ := by
    simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  change (harperRegressedGaussianTwoWalkMeasure
      variance residualVariance lambda).real (G ×ˢ G) ≤ _
  rw [hmap]
  calc
    (P.prod Q).real
        (harperGaussianRegressionMap lambda ⁻¹' (G ×ˢ G)) ≤
      (P.prod Q).real (H₁ ×ˢ H₂) := measureReal_mono hsubset
    _ = P.real H₁ * Q.real H₂ := hproduct
    _ ≤
        ((64 * 68 * ((d + 1 : Nat) : Real)) / Real.sqrt (n : Real)) *
          ((64 * (536 * L + 68) * ((d + 1 : Nat) : Real)) /
            Real.sqrt (n : Real)) :=
      mul_le_mul hfirst hsecond measureReal_nonneg (by positivity)
    _ = (4096 * 68 * (536 * L + 68)) *
        (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (n : Real)⁻¹ := by
      rw [div_mul_div_comm, ← pow_two (Real.sqrt (n : Real)),
        Real.sq_sqrt hnR.le]
      field_simp
      ring

/-- Paired-path form of the coarse relaxed translated suffix guard. -/
def harperPairedRelaxedSuffixGuardPathEvent
    (d n : Nat) : Set (Fin n → Real × Real) :=
  harperPairPathUnzipCLM n ⁻¹'
    (harperRelaxedSuffixGuardPathEvent d n ×ˢ
      harperRelaxedSuffixGuardPathEvent d n)

theorem measurableSet_harperPairedRelaxedSuffixGuardPathEvent (d n : Nat) :
    MeasurableSet (harperPairedRelaxedSuffixGuardPathEvent d n) := by
  exact ((measurableSet_harperRelaxedSuffixGuardPathEvent d n).prod
    (measurableSet_harperRelaxedSuffixGuardPathEvent d n)).preimage
      (harperPairPathUnzipCLM n).measurable

/-- Exact covariance-matched Gaussian version of the relaxed suffix ballot
upper bound. -/
theorem pi_harperTwoHeightGaussianLaw_relaxedSuffixGuard_probability_le
    {d n y : Nat} (hn : 0 < n)
    (S : Fin n → Finset (Problem520.HarperPrimeIndex y))
    (t s : Real)
    (ha : ∀ i,
      0 < harperTwoHeightBlockCoordinateCovariance y (S i) t s t t)
    (L : Real) (hL : 0 ≤ L)
    (hlambda : ∀ i : Fin n,
      |harperTwoHeightRegressionCoefficient y (S i) t s| ≤
        L * (1 / 2 : Real) ^ i.val)
    (hvarianceLower : ∀ i,
      (1 / 4 : NNReal) ≤
        harperTwoHeightCoordinateVarianceNNReal y (S i) t s t)
    (hvarianceUpper : ∀ i,
      harperTwoHeightCoordinateVarianceNNReal y (S i) t s t ≤
        (1 / 2 : NNReal))
    (hresidualLower : ∀ i,
      (1 / 4 : NNReal) ≤
        harperTwoHeightRegressionResidualVarianceNNReal
          y (S i) t s (ha i))
    (hresidualUpper : ∀ i,
      harperTwoHeightRegressionResidualVarianceNNReal
          y (S i) t s (ha i) ≤ (1 / 2 : NNReal)) :
    (Measure.pi (fun i ↦ harperTwoHeightGaussianLaw y (S i) t s)).real
        (harperPairedRelaxedSuffixGuardPathEvent d n) ≤
      (4096 * 68 * (536 * L + 68)) *
        (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (n : Real)⁻¹ := by
  rw [pi_harperTwoHeightGaussianLaw_eq_map_regressed S t s ha]
  rw [map_measureReal_apply (harperPairPathZipCLM n).measurable
    (measurableSet_harperPairedRelaxedSuffixGuardPathEvent d n)]
  have hpre :
      harperPairPathZipCLM n ⁻¹'
          harperPairedRelaxedSuffixGuardPathEvent d n =
        harperRelaxedSuffixGuardPathEvent d n ×ˢ
          harperRelaxedSuffixGuardPathEvent d n := by
    ext z
    simp [harperPairedRelaxedSuffixGuardPathEvent]
  rw [hpre]
  exact harperRegressedGaussianTwoWalk_relaxedSuffixGuard_probability_le
    hn
    (fun i ↦ harperTwoHeightCoordinateVarianceNNReal y (S i) t s t)
    (fun i ↦ harperTwoHeightRegressionResidualVarianceNNReal
      y (S i) t s (ha i))
    (fun i ↦ harperTwoHeightRegressionCoefficient y (S i) t s)
    L hL hlambda hvarianceLower hvarianceUpper
      hresidualLower hresidualUpper

/-- Relaxing an `O(d)` translated suffix corridor by one unit places it in
the coarse paired suffix guard used by the regression estimate. -/
theorem harperPairedRelaxedPartialSumBarrierSet_subset_suffixGuard
    {d n : Nat} (lower upper : Fin n → Real)
    (hlower : ∀ k,
      -64 * ((d + k.val + 1 : Nat) : Real) - 2 ≤ lower k)
    (hupper : ∀ k, upper k ≤ 64 * (d : Real) + 1) :
    harperPairedRelaxedPartialSumBarrierSet lower upper ⊆
      harperPairedRelaxedSuffixGuardPathEvent d n := by
  intro x hx
  have hxPair :
      (fun k ↦ (x k).1) ∈ Problem520.harperPartialSumBarrierSet
          (fun k ↦ lower k - 1) (fun k ↦ upper k + 1) ∧
        (fun k ↦ (x k).2) ∈ Problem520.harperPartialSumBarrierSet
          (fun k ↦ lower k - 1) (fun k ↦ upper k + 1) := hx
  change
    (fun k ↦ (x k).1) ∈ harperRelaxedSuffixGuardPathEvent d n ∧
      (fun k ↦ (x k).2) ∈ harperRelaxedSuffixGuardPathEvent d n
  constructor
  · unfold harperRelaxedSuffixGuardPathEvent
    rw [Problem520.mem_harperPartialSumBarrierSet]
    intro k
    have hk := Problem520.mem_harperPartialSumBarrierSet.mp hxPair.1 k
    exact ⟨by linarith [hlower k], by linarith [hupper k]⟩
  · unfold harperRelaxedSuffixGuardPathEvent
    rw [Problem520.mem_harperPartialSumBarrierSet]
    intro k
    have hk := Problem520.mem_harperPartialSumBarrierSet.mp hxPair.2 k
    exact ⟨by linarith [hlower k], by linarith [hupper k]⟩

/-! ## Scheduled natural-coherence consequence -/

/-- Beginning at any scheduled block beyond the shell's natural coherence
point, the exact covariance Gaussian obeys the relaxed suffix estimate. -/
theorem exists_harperScheduledCorrelatedGaussian_relaxedSuffixGuard_le :
    ∃ L > 0, ∃ J : Nat,
      ∀ shell start d m y : Nat, 0 < m →
        J + (shell + 1) ≤ start →
        Problem520.harperBlockEndpoint (start + m) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (shell + 1) < |t - s| →
                (Measure.pi (fun i : Fin m ↦
                  harperTwoHeightGaussianLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + i.val)) t s)).real
                    (harperPairedRelaxedSuffixGuardPathEvent d m) ≤
                  (4096 * 68 * (536 * L + 68)) *
                    (((d + 1 : Nat) : Real) ^ (2 : Nat)) *
                      (m : Real)⁻¹ := by
  obtain ⟨c, hc, C, hC, Jcov, hcov⟩ :=
    exists_harperTwoHeightScheduledCovariance_postCoherence_geometric
  obtain ⟨Jsmall, hsmall⟩ :=
    exists_eventually_harperTwoHeightScheduledCovariance_postCoherence_small
      (by norm_num : (0 : Real) < 1 / 8)
  obtain ⟨Jvar, hvar⟩ :=
    exists_eventually_harperTwoHeightScheduledCoordinateVariance_third_threeEighths
  obtain ⟨c', hc', C', hC', Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  obtain ⟨Jtheta, htheta⟩ := Filter.eventually_atTop.1
    (eventually_harperScheduledThetaEnvelope_le_geometric hc hC.le)
  let J := max Jsmall (max Jcov (max Jvar (max Jerr Jtheta)))
  let K : Real := 395 + 7 * C
  let L : Real := 3 * K
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  refine ⟨L, hL, J, ?_⟩
  intro shell start d m y hm hstart hy t ht s hs hsep
  let S : Fin m → Finset (Problem520.HarperPrimeIndex y) :=
    fun i ↦ Problem520.harperScheduledPrimeBlock y (start + i.val)
  have hblock (i : Fin m) :
      let j := start + i.val
      let a := harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s t t
      let b := harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s s s
      let q := harperTwoHeightBlockCoordinateCovariance y
        (Problem520.harperScheduledPrimeBlock y j) t s t s
      (1 / 3 : Real) < a ∧ a < 3 / 8 ∧
        (1 / 3 : Real) < b ∧ b < 3 / 8 ∧
          |q| ≤ K * (1 / 2 : Real) ^ i.val ∧
            |q| ≤ (1 / 8 : Real) := by
    dsimp only
    let j := start + i.val
    have hjEnd : j + 1 ≤ start + m := by
      dsimp only [j]
      omega
    have hyj : Problem520.harperBlockEndpoint (j + 1) ≤ y :=
      (Problem520.monotone_harperBlockEndpoint hjEnd).trans hy
    have hJcov : Jcov + (shell + 1) ≤ j := by
      dsimp only [j, J] at hstart ⊢
      have : Jcov ≤ max Jsmall (max Jcov (max Jvar (max Jerr Jtheta))) :=
        (le_max_left Jcov _).trans (le_max_right Jsmall _)
      omega
    have hJsmall : Jsmall + (shell + 1) ≤ j := by
      dsimp only [j, J] at hstart ⊢
      have : Jsmall ≤ max Jsmall (max Jcov (max Jvar (max Jerr Jtheta))) :=
        le_max_left _ _
      omega
    have hJvar : Jvar ≤ j := by
      dsimp only [j, J] at hstart ⊢
      have : Jvar ≤ max Jsmall (max Jcov (max Jvar (max Jerr Jtheta))) :=
        ((le_max_left Jvar _).trans (le_max_right Jcov _)).trans
          (le_max_right Jsmall _)
      omega
    have hJerr : Jerr ≤ j := by
      dsimp only [j, J] at hstart ⊢
      have : Jerr ≤ max Jsmall (max Jcov (max Jvar (max Jerr Jtheta))) :=
        (((le_max_left Jerr Jtheta).trans (le_max_right Jvar _)).trans
          (le_max_right Jcov _)).trans (le_max_right Jsmall _)
      omega
    have hJtheta : Jtheta ≤ j := by
      dsimp only [j, J] at hstart ⊢
      have : Jtheta ≤ max Jsmall (max Jcov (max Jvar (max Jerr Jtheta))) :=
        (((le_max_right Jerr Jtheta).trans (le_max_right Jvar _)).trans
          (le_max_right Jcov _)).trans (le_max_right Jsmall _)
      omega
    have hvarj := hvar j hJvar y hyj t ht s hs
    have htt := hvarj t ht
    have hss := hvarj s hs
    have hcovj := hcov shell j y hJcov hyj t ht s hs hsep
    have hsmallj := (hsmall shell j y hJsmall hyj t ht s hs hsep).le
    have hthetaJ := htheta j hJtheta
    have hsquareMass : Problem520.harperScheduledSquareMass y j ≤
        Problem520.harperScheduledSquareEnvelope j :=
      (herr j hJerr y hyj).2.2
    have hpDiff :
        (1 / 2 : Real) ^ (j - (shell + 1)) ≤
          (1 / 2 : Real) ^ i.val := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      dsimp only [j]
      omega
    have hpSum :
        (1 / 2 : Real) ^ (j - 1) ≤
          (1 / 2 : Real) ^ i.val := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      dsimp only [j]
      omega
    have hpJ :
        (1 / 2 : Real) ^ j ≤ (1 / 2 : Real) ^ i.val := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      dsimp only [j]
      omega
    have hthetaI : Problem520.harperScheduledThetaEnvelope c C j ≤
        (C + 1) * (1 / 2 : Real) ^ i.val := by
      exact hthetaJ.trans (mul_le_mul_of_nonneg_left hpJ (by linarith))
    have hsquareI : Problem520.harperScheduledSquareMass y j ≤
        (3 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
      calc
        Problem520.harperScheduledSquareMass y j ≤
            Problem520.harperScheduledSquareEnvelope j := hsquareMass
        _ ≤ (3 / 2 : Real) * (1 / 2 : Real) ^ j :=
          harperScheduledSquareEnvelope_le_threeHalves_geometric j
        _ ≤ (3 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
          gcongr
    have hq :
        |harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
          K * (1 / 2 : Real) ^ i.val := by
      calc
        |harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) t s t s| ≤
          2 * (1 / 2 : Real) ^ (j - (shell + 1)) +
            2 * (1 / 2 : Real) ^ (j - 1) +
            7 * Problem520.harperScheduledThetaEnvelope c C j +
            256 * Problem520.harperScheduledSquareMass y j := hcovj
        _ ≤ 2 * (1 / 2 : Real) ^ i.val +
            2 * (1 / 2 : Real) ^ i.val +
            7 * ((C + 1) * (1 / 2 : Real) ^ i.val) +
            256 * ((3 / 2 : Real) * (1 / 2 : Real) ^ i.val) := by
          gcongr
        _ = K * (1 / 2 : Real) ^ i.val := by
          dsimp only [K]
          ring
    exact ⟨htt.1, htt.2, hss.1, hss.2, hq, hsmallj⟩
  have ha : ∀ i,
      0 < harperTwoHeightBlockCoordinateCovariance y (S i) t s t t := by
    intro i
    exact lt_trans (by norm_num) (hblock i).1
  apply pi_harperTwoHeightGaussianLaw_relaxedSuffixGuard_probability_le
    (d := d) hm S t s ha L hL.le
  · intro i
    have hb := hblock i
    unfold harperTwoHeightRegressionCoefficient
    have hraw := abs_regressionCoefficient_le_three_mul
      hb.1.le (mul_nonneg hK.le (by positivity)) hb.2.2.2.2.1
    dsimp only [S] at hraw ⊢
    calc
      |harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y
              (start + i.val)) t s t s /
          harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y
              (start + i.val)) t s t t| ≤
        3 * (K * (1 / 2 : Real) ^ i.val) := hraw
      _ = L * (1 / 2 : Real) ^ i.val := by
        dsimp only [L]
        ring
  · intro i
    exact_mod_cast (show (1 / 4 : Real) ≤
      harperTwoHeightBlockCoordinateCovariance y (S i) t s t t by
        linarith [(hblock i).1])
  · intro i
    exact_mod_cast (show
      harperTwoHeightBlockCoordinateCovariance y (S i) t s t t ≤
        (1 / 2 : Real) by linarith [(hblock i).2.1])
  · intro i
    have hb := hblock i
    have hres := regressionResidualVariance_quarter_half
      hb.1.le hb.2.1.le hb.2.2.1.le hb.2.2.2.1.le
      hb.2.2.2.2.2
    exact_mod_cast hres.1
  · intro i
    have hb := hblock i
    have hres := regressionResidualVariance_quarter_half
      hb.1.le hb.2.1.le hb.2.2.1.le hb.2.2.2.1.le
      hb.2.2.2.2.2
    exact_mod_cast hres.2

/-- With a fixed initial scheduling delay, both literal ballot-centering
drifts decay geometrically from the natural coherence block.  In particular
their cumulative suffix drift is at most one, uniformly in the suffix
length. -/
theorem exists_harperScheduledRelativeDrift_geometric_half :
    ∃ J : Nat, ∀ shell baseStart d m y : Nat,
      J ≤ baseStart → shell + 1 ≤ d →
      Problem520.harperBlockEndpoint (baseStart + d + m) ≤ y →
        ∀ t ∈ harperLowerVerticalBand,
          ∀ s ∈ harperLowerVerticalBand,
            (1 / 2 : Real) ^ (shell + 1) < |t - s| →
              ∀ i : Fin m,
                |harperTwoHeightRelativeBlockDrift y
                    (Problem520.harperScheduledPrimeBlock y
                      (baseStart + d + i.val)) t s t t| ≤
                    (1 / 2 : Real) * (1 / 2 : Real) ^ i.val ∧
                  |harperTwoHeightRelativeBlockDrift y
                    (Problem520.harperScheduledPrimeBlock y
                      (baseStart + d + i.val)) t s s s| ≤
                    (1 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
  obtain ⟨c, hc, C, hC, Jcov, hcov⟩ :=
    exists_harperTwoHeightScheduledCovariance_postCoherence_geometric
  obtain ⟨c', hc', C', hC', Jerr, herr⟩ :=
    Problem520.exists_harperScheduledSummableBlockErrorBounds 1
  obtain ⟨Jtheta, htheta⟩ := Filter.eventually_atTop.1
    (eventually_harperScheduledThetaEnvelope_le_geometric hc hC.le)
  let K : Real := 395 + 7 * C
  let A : Real := 864 + 2 * K
  have hK : 0 < K := by
    dsimp only [K]
    nlinarith
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hhalfTendsto : Tendsto (fun j : Nat ↦ (1 / 2 : Real) ^ j)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaleTendsto : Tendsto
      (fun j : Nat ↦ A * (1 / 2 : Real) ^ j) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hhalfTendsto
  have hscaleEventually : ∀ᶠ j : Nat in atTop,
      A * (1 / 2 : Real) ^ j ≤ (1 / 2 : Real) := by
    filter_upwards
      [(tendsto_order.mp hscaleTendsto).2 (1 / 2 : Real) (by norm_num)]
      with j hj
    exact hj.le
  obtain ⟨Jscale, hscale⟩ := Filter.eventually_atTop.1 hscaleEventually
  let J := max Jcov (max Jerr (max Jtheta Jscale))
  refine ⟨J, ?_⟩
  intro shell baseStart d m y hstart hd hy t ht s hs hsep i
  let j := baseStart + d + i.val
  have hjEnd : j + 1 ≤ baseStart + d + m := by
    dsimp only [j]
    omega
  have hyj : Problem520.harperBlockEndpoint (j + 1) ≤ y :=
    (Problem520.monotone_harperBlockEndpoint hjEnd).trans hy
  have hJcov : Jcov + (shell + 1) ≤ j := by
    dsimp only [j, J] at hstart ⊢
    have : Jcov ≤ max Jcov (max Jerr (max Jtheta Jscale)) :=
      le_max_left _ _
    omega
  have hJerr : Jerr ≤ j := by
    dsimp only [j, J] at hstart ⊢
    have : Jerr ≤ max Jcov (max Jerr (max Jtheta Jscale)) :=
      (le_max_left Jerr _).trans (le_max_right Jcov _)
    omega
  have hJtheta : Jtheta ≤ j := by
    dsimp only [j, J] at hstart ⊢
    have : Jtheta ≤ max Jcov (max Jerr (max Jtheta Jscale)) :=
      ((le_max_left Jtheta Jscale).trans (le_max_right Jerr _)).trans
        (le_max_right Jcov _)
    omega
  have hJscale : Jscale ≤ baseStart := by
    dsimp only [J] at hstart
    have : Jscale ≤ max Jcov (max Jerr (max Jtheta Jscale)) :=
      ((le_max_right Jtheta Jscale).trans (le_max_right Jerr _)).trans
        (le_max_right Jcov _)
    exact this.trans hstart
  have hscaleBase := hscale baseStart hJscale
  have hthetaJ := htheta j hJtheta
  have hsquareMass : Problem520.harperScheduledSquareMass y j ≤
      Problem520.harperScheduledSquareEnvelope j :=
    (herr j hJerr y hyj).2.2
  have hpDiff :
      (1 / 2 : Real) ^ (j - (shell + 1)) ≤
        (1 / 2 : Real) ^ (baseStart + i.val) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp only [j]
    omega
  have hpSum :
      (1 / 2 : Real) ^ (j - 1) ≤
        (1 / 2 : Real) ^ (baseStart + i.val) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp only [j]
    omega
  have hpJ :
      (1 / 2 : Real) ^ j ≤
        (1 / 2 : Real) ^ (baseStart + i.val) := by
    apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
    dsimp only [j]
    omega
  have hthetaI : Problem520.harperScheduledThetaEnvelope c C j ≤
      (C + 1) * (1 / 2 : Real) ^ (baseStart + i.val) := by
    exact hthetaJ.trans (mul_le_mul_of_nonneg_left hpJ (by linarith))
  have hsquareI : Problem520.harperScheduledSquareMass y j ≤
      (3 / 2 : Real) * (1 / 2 : Real) ^ (baseStart + i.val) := by
    calc
      Problem520.harperScheduledSquareMass y j ≤
          Problem520.harperScheduledSquareEnvelope j := hsquareMass
      _ ≤ (3 / 2 : Real) * (1 / 2 : Real) ^ j :=
        harperScheduledSquareEnvelope_le_threeHalves_geometric j
      _ ≤ (3 / 2 : Real) *
          (1 / 2 : Real) ^ (baseStart + i.val) := by gcongr
  have hone (a b : Real) (haBand : a ∈ harperLowerVerticalBand)
      (hbBand : b ∈ harperLowerVerticalBand)
      (hsepAB : (1 / 2 : Real) ^ (shell + 1) < |a - b|) :
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y j) a b a a| ≤
        (1 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
    have hcovj := hcov shell j y hJcov hyj a haBand b hbBand hsepAB
    have hq :
        |harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) a b a b| ≤
          K * (1 / 2 : Real) ^ (baseStart + i.val) := by
      calc
        |harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) a b a b| ≤
          2 * (1 / 2 : Real) ^ (j - (shell + 1)) +
            2 * (1 / 2 : Real) ^ (j - 1) +
            7 * Problem520.harperScheduledThetaEnvelope c C j +
            256 * Problem520.harperScheduledSquareMass y j := hcovj
        _ ≤ 2 * (1 / 2 : Real) ^ (baseStart + i.val) +
            2 * (1 / 2 : Real) ^ (baseStart + i.val) +
            7 * ((C + 1) *
              (1 / 2 : Real) ^ (baseStart + i.val)) +
            256 * ((3 / 2 : Real) *
              (1 / 2 : Real) ^ (baseStart + i.val)) := by gcongr
        _ = K * (1 / 2 : Real) ^ (baseStart + i.val) := by
          dsimp only [K]
          ring
    have hcompare :=
      abs_harperTwoHeightScheduledCenteredBlockDrift_sub_two_covariance_le
        y j a b
    have htri :
        |harperTwoHeightCenteredBlockDrift y
            (Problem520.harperScheduledPrimeBlock y j) a b a| ≤
          576 * Problem520.harperScheduledSquareMass y j +
            2 * |harperTwoHeightBlockCoordinateCovariance y
              (Problem520.harperScheduledPrimeBlock y j) a b a b| := by
      calc
        |harperTwoHeightCenteredBlockDrift y
            (Problem520.harperScheduledPrimeBlock y j) a b a| =
          |(harperTwoHeightCenteredBlockDrift y
              (Problem520.harperScheduledPrimeBlock y j) a b a -
                2 * harperTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j) a b a b) +
              2 * harperTwoHeightBlockCoordinateCovariance y
                (Problem520.harperScheduledPrimeBlock y j) a b a b| := by
            congr 1
            ring
        _ ≤
          |harperTwoHeightCenteredBlockDrift y
              (Problem520.harperScheduledPrimeBlock y j) a b a -
                2 * harperTwoHeightBlockCoordinateCovariance y
                  (Problem520.harperScheduledPrimeBlock y j) a b a b| +
            |2 * harperTwoHeightBlockCoordinateCovariance y
              (Problem520.harperScheduledPrimeBlock y j) a b a b| :=
          abs_add_le _ _
        _ ≤ 576 * Problem520.harperScheduledSquareMass y j +
            2 * |harperTwoHeightBlockCoordinateCovariance y
              (Problem520.harperScheduledPrimeBlock y j) a b a b| := by
          gcongr
          rw [abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    rw [harperTwoHeightRelativeBlockDrift_first]
    calc
      |harperTwoHeightCenteredBlockDrift y
          (Problem520.harperScheduledPrimeBlock y j) a b a| ≤
        576 * Problem520.harperScheduledSquareMass y j +
          2 * |harperTwoHeightBlockCoordinateCovariance y
            (Problem520.harperScheduledPrimeBlock y j) a b a b| := htri
      _ ≤ A * (1 / 2 : Real) ^ (baseStart + i.val) := by
        calc
          576 * Problem520.harperScheduledSquareMass y j +
              2 * |harperTwoHeightBlockCoordinateCovariance y
                (Problem520.harperScheduledPrimeBlock y j) a b a b| ≤
            576 * ((3 / 2 : Real) *
                (1 / 2 : Real) ^ (baseStart + i.val)) +
              2 * (K *
                (1 / 2 : Real) ^ (baseStart + i.val)) := by gcongr
          _ = A * (1 / 2 : Real) ^ (baseStart + i.val) := by
            dsimp only [A]
            ring
      _ = (A * (1 / 2 : Real) ^ baseStart) *
          (1 / 2 : Real) ^ i.val := by rw [pow_add]; ring
      _ ≤ (1 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
        exact mul_le_mul_of_nonneg_right hscaleBase (by positivity)
  constructor
  · exact hone t s ht hs hsep
  · have hsepSwap :
        (1 / 2 : Real) ^ (shell + 1) < |s - t| := by
      simpa only [abs_sub_comm] using hsep
    have hraw := hone s t hs ht hsepSwap
    rw [harperTwoHeightRelativeBlockDrift_first] at hraw
    rw [harperTwoHeightRelativeBlockDrift_second]
    exact hraw

/-- Pointwise geometric drift decay gives a uniform one-unit bound for every
cumulative suffix drift. -/
theorem cumulative_harperScheduledRelativeDrift_le_one
    {baseStart d m y : Nat} {t s : Real}
    (hpoint : ∀ i : Fin m,
      |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) t s t t| ≤
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val ∧
        |harperTwoHeightRelativeBlockDrift y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) t s s s| ≤
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val) :
    ∀ k : Fin m,
      |∑ i ∈ Finset.Iic k,
        (harperTwoHeightBallotBlockDrift y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) t s).1| ≤ 1 ∧
      |∑ i ∈ Finset.Iic k,
        (harperTwoHeightBallotBlockDrift y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) t s).2| ≤ 1 := by
  intro k
  have hsum :
      (∑ i ∈ Finset.Iic k,
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val) ≤ 1 := by
    calc
      (∑ i ∈ Finset.Iic k,
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val) ≤
        ∑ i : Fin m, (1 / 2 : Real) * (1 / 2 : Real) ^ i.val :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (by intro i hi hnot; positivity)
      _ = (1 / 2 : Real) *
          ∑ i : Fin m, (1 / 2 : Real) ^ (0 + i.val) := by
        simp only [zero_add]
        rw [Finset.mul_sum]
      _ ≤ (1 / 2 : Real) * (2 * (1 / 2 : Real) ^ 0) := by
        exact mul_le_mul_of_nonneg_left
          (sum_fin_half_pow_shift_le 0 m) (by norm_num)
      _ = 1 := by norm_num
  constructor
  · calc
      |∑ i ∈ Finset.Iic k,
          (harperTwoHeightBallotBlockDrift y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) t s).1| ≤
        ∑ i ∈ Finset.Iic k,
          |(harperTwoHeightBallotBlockDrift y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) t s).1| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k,
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
        gcongr with i hi
        exact (hpoint i).1
      _ ≤ 1 := hsum
  · calc
      |∑ i ∈ Finset.Iic k,
          (harperTwoHeightBallotBlockDrift y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) t s).2| ≤
        ∑ i ∈ Finset.Iic k,
          |(harperTwoHeightBallotBlockDrift y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) t s).2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k,
          (1 / 2 : Real) * (1 / 2 : Real) ^ i.val := by
        gcongr with i hi
        exact (hpoint i).2
      _ ≤ 1 := hsum

/-- Removing a one-unit cumulative centering drift places a literal suffix
continuation in a one-unit relaxed centered corridor; paths in that corridor
still have the required elapsed-time coordinate envelope. -/
theorem abs_coordinates_le_of_mem_harperPairedRelaxedSuffix_logBallot
    {start d m : Nat} (hd : 0 < d)
    (u : Fin d → Real × Real) (v : Fin m → Real × Real)
    (hfull : Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (x : Fin m → Real × Real)
    (hx : x ∈ harperPairedRelaxedPartialSumBarrierSet
      (harperPairedSuffixLower
        (harper1144LogBallotLowerBarrier start (d + m)) u)
      (harperPairedSuffixUpper
        (harper1144LogBallotUpperBarrier (d + m)) u))
    (i : Fin m) :
    |(x i).1| ≤ 128 * ((d + i.val + 1 : Nat) : Real) + 6 ∧
      |(x i).2| ≤ 128 * ((d + i.val + 1 : Nat) : Real) + 6 := by
  let lower := harperPairedSuffixLower
    (harper1144LogBallotLowerBarrier start (d + m)) u
  let upper := harperPairedSuffixUpper
    (harper1144LogBallotUpperBarrier (d + m)) u
  have hxPair :
      (fun k ↦ (x k).1) ∈ Problem520.harperPartialSumBarrierSet
          (fun k ↦ lower k - 1) (fun k ↦ upper k + 1) ∧
        (fun k ↦ (x k).2) ∈ Problem520.harperPartialSumBarrierSet
          (fun k ↦ lower k - 1) (fun k ↦ upper k + 1) := hx
  have hlower (k : Fin m) :
      -64 * ((d + k.val + 1 : Nat) : Real) - 3 ≤ lower k - 1 := by
    linarith
      [neg_sixtyFour_mul_suffixElapsed_sub_one_le_harperPairedSuffixLower_logBallot
        hd u v hfull k]
  have hupper (k : Fin m) :
      upper k + 1 ≤ 64 * (d : Real) + 2 := by
    linarith [harperPairedSuffixUpper_logBallot_le hd u v hfull k]
  constructor
  · apply abs_coordinate_le_of_relaxed_suffix_partialSum_guard
      (fun k ↦ (x k).1)
    · intro k
      exact (hlower k).trans
        (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.1 k).1
    · intro k
      exact (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.1 k).2.trans
        (hupper k)
  · apply abs_coordinate_le_of_relaxed_suffix_partialSum_guard
      (fun k ↦ (x k).2)
    · intro k
      exact (hlower k).trans
        (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.2 k).1
    · intro k
      exact (Problem520.mem_harperPartialSumBarrierSet.mp hxPair.2 k).2.trans
        (hupper k)

private theorem scheduled_moderate_relaxed_suffix_nat_bound (i : Nat) :
    (4096 * (i + 1) + 272) ^ 2 ≤ 2 ^ (31 + i) := by
  by_cases hi : i < 2
  · interval_cases i <;> norm_num
  · have hi2 : 2 ≤ i := by omega
    induction i, hi2 using Nat.le_induction with
    | base => norm_num
    | succ i hi ih =>
        have hgrowth :
            (4096 * (i + 1 + 1) + 272) ^ 2 ≤
              2 * (4096 * (i + 1) + 272) ^ 2 := by
          nlinarith
        calc
          (4096 * (i + 1 + 1) + 272) ^ 2 ≤
              2 * (4096 * (i + 1) + 272) ^ 2 := hgrowth
          _ ≤ 2 * 2 ^ (31 + i) := Nat.mul_le_mul_left 2 (ih (by omega))
          _ = 2 ^ (31 + (i + 1)) := by
            rw [show 31 + (i + 1) = (31 + i) + 1 by omega, pow_succ]
            omega

theorem harperScheduled_relaxedSuffixEnvelope_le_moderateWindow
    {baseStart : Nat} (hstart : 31 ≤ baseStart) (i : Nat) :
    256 * (((i + 1 : Nat) : Real)) + 17 ≤
      (1 / 16 : Real) *
        Real.sqrt (((2 ^ (baseStart + i) : Nat) : Real)) := by
  have hnatBase := scheduled_moderate_relaxed_suffix_nat_bound i
  have hexponent : 31 + i ≤ baseStart + i := by omega
  have hnatPow : 2 ^ (31 + i) ≤ 2 ^ (baseStart + i) :=
    Nat.pow_le_pow_right (by norm_num) hexponent
  have hnat : (4096 * (i + 1) + 272) ^ 2 ≤ 2 ^ (baseStart + i) :=
    hnatBase.trans hnatPow
  have hreal :
      ((4096 * (i + 1) + 272 : Nat) : Real) ^ 2 ≤
        ((2 ^ (baseStart + i) : Nat) : Real) := by exact_mod_cast hnat
  have hsqrt :
      (16 : Real) * (256 * (((i + 1 : Nat) : Real)) + 17) ≤
        Real.sqrt (((2 ^ (baseStart + i) : Nat) : Real)) := by
    apply Real.le_sqrt_of_sq_le
    convert hreal using 1 <;> push_cast <;> ring
  nlinarith

/-- The literal centered two-height Rademacher suffix corridor has the same
natural-coherence `O((d+1)^2/m)` bound.  This composes the shifted-lattice
comparison with the Gaussian regression estimate. -/
theorem exists_harperScheduledTwoHeightCenteredLogBallotSuffix_probability_le :
    ∃ L > 0, ∃ J : Nat,
      ∀ shell baseStart d m y : Nat, 0 < m →
        J ≤ baseStart → shell + 1 ≤ d →
        Problem520.harperBlockEndpoint (baseStart + d + m) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (shell + 1) < |t - s| →
                ∀ u : Fin d → Real × Real,
                  ∀ v : Fin m → Real × Real,
                    Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
                      (harper1144LogBallotLowerBarrier baseStart (d + m))
                      (harper1144LogBallotUpperBarrier (d + m)) →
                    let lower := harperPairedSuffixLower
                      (harper1144LogBallotLowerBarrier baseStart (d + m)) u
                    let upper := harperPairedSuffixUpper
                      (harper1144LogBallotUpperBarrier (d + m)) u
                    (Measure.pi (fun i : Fin m ↦
                      harperTwoHeightPrimeBlockVectorLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (baseStart + d + i.val)) t s)).real
                        (harperPairedPartialSumBarrierSet lower upper) ≤
                      4 * Real.exp 4 *
                        ((4096 * 68 * (536 * L + 68)) *
                          (((d + 1 : Nat) : Real) ^ (2 : Nat)) *
                            (m : Real)⁻¹) := by
  obtain ⟨Jshift, hshift⟩ :=
    exists_harperScheduledTwoHeightCenteredLogBallotSuffix_le_gaussianRelaxed
  obtain ⟨L, hL, Jgauss, hgauss⟩ :=
    exists_harperScheduledCorrelatedGaussian_relaxedSuffixGuard_le
  let J := max Jshift Jgauss
  refine ⟨L, hL, J, ?_⟩
  intro shell baseStart d m y hm hstart hd hy t ht s hs hsep u v hfull
  dsimp only
  have hdPos : 0 < d := by omega
  have hshiftStart : Jshift ≤ baseStart :=
    (le_max_left Jshift Jgauss).trans hstart
  have hgaussStart : Jgauss + (shell + 1) ≤ baseStart + d := by
    have : Jgauss ≤ baseStart :=
      (le_max_right Jshift Jgauss).trans hstart
    omega
  let lower := harperPairedSuffixLower
    (harper1144LogBallotLowerBarrier baseStart (d + m)) u
  let upper := harperPairedSuffixUpper
    (harper1144LogBallotUpperBarrier (d + m)) u
  let G : Measure (Fin m → Real × Real) :=
    Measure.pi (fun i : Fin m ↦
      harperTwoHeightGaussianLaw y
        (Problem520.harperScheduledPrimeBlock y
          (baseStart + d + i.val)) t s)
  have hcompare := hshift shell baseStart d m y hshiftStart hd hy
    t ht s hs hsep u v hfull
  have hlower (k : Fin m) :
      -64 * ((d + k.val + 1 : Nat) : Real) - 2 ≤ lower k := by
    linarith
      [neg_sixtyFour_mul_suffixElapsed_sub_one_le_harperPairedSuffixLower_logBallot
        hdPos u v hfull k]
  have hupper (k : Fin m) : upper k ≤ 64 * (d : Real) + 1 := by
    linarith [harperPairedSuffixUpper_logBallot_le hdPos u v hfull k]
  have hsubset :
      harperPairedRelaxedPartialSumBarrierSet lower upper ⊆
        harperPairedRelaxedSuffixGuardPathEvent d m :=
    harperPairedRelaxedPartialSumBarrierSet_subset_suffixGuard
      lower upper hlower hupper
  have hmono :
      G.real (harperPairedRelaxedPartialSumBarrierSet lower upper) ≤
        G.real (harperPairedRelaxedSuffixGuardPathEvent d m) :=
    measureReal_mono hsubset
  have hgaussBound := hgauss shell (baseStart + d) d m y hm
    hgaussStart (by simpa only [add_assoc] using hy)
    t ht s hs hsep
  dsimp only [lower, upper, G] at hcompare hmono ⊢
  calc
    (Measure.pi (fun i : Fin m ↦
        harperTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet
          (harperPairedSuffixLower
            (harper1144LogBallotLowerBarrier baseStart (d + m)) u)
          (harperPairedSuffixUpper
            (harper1144LogBallotUpperBarrier (d + m)) u)) ≤
      4 * Real.exp 4 *
        (Measure.pi (fun i : Fin m ↦
          harperTwoHeightGaussianLaw y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) t s)).real
          (harperPairedRelaxedPartialSumBarrierSet
            (harperPairedSuffixLower
              (harper1144LogBallotLowerBarrier baseStart (d + m)) u)
            (harperPairedSuffixUpper
              (harper1144LogBallotUpperBarrier (d + m)) u)) := hcompare
    _ ≤ 4 * Real.exp 4 *
        (Measure.pi (fun i : Fin m ↦
          harperTwoHeightGaussianLaw y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) t s)).real
          (harperPairedRelaxedSuffixGuardPathEvent d m) := by
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ 4 * Real.exp 4 *
        ((4096 * 68 * (536 * L + 68)) *
          (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hgaussBound (by positivity)

/-- Natural-coherence suffix estimate for the literal two-height ballot
increments.  The deterministic joint-to-one-height centering drift is
removed with one unit of corridor room before the shifted-lattice and
Gaussian-regression comparisons. -/
theorem exists_harperScheduledTwoHeightLogBallotSuffix_natural_le :
    ∃ L > 0, ∃ J : Nat,
      ∀ shell baseStart d m y : Nat, 0 < m →
        J ≤ baseStart → shell + 1 ≤ d →
        Problem520.harperBlockEndpoint (baseStart + d + m) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (shell + 1) < |t - s| →
                ∀ u : Fin d → Real × Real,
                  ∀ v : Fin m → Real × Real,
                    Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
                      (harper1144LogBallotLowerBarrier baseStart (d + m))
                      (harper1144LogBallotUpperBarrier (d + m)) →
                    let lower := harperPairedSuffixLower
                      (harper1144LogBallotLowerBarrier baseStart (d + m)) u
                    let upper := harperPairedSuffixUpper
                      (harper1144LogBallotUpperBarrier (d + m)) u
                    (Measure.pi (fun i : Fin m ↦
                      harperTwoHeightBallotBlockLaw y
                        (Problem520.harperScheduledPrimeBlock y
                          (baseStart + d + i.val)) t s)).real
                        (harperPairedPartialSumBarrierSet lower upper) ≤
                      4 * Real.exp 4 *
                        ((4096 * 68 * (536 * L + 68)) *
                          (((d + 1 : Nat) : Real) ^ (2 : Nat)) *
                            (m : Real)⁻¹) := by
  obtain ⟨Jpath, hpath⟩ :=
    exists_harperScheduledTwoHeightPairedBarrier_le_gaussianRelaxed
  obtain ⟨L, hL, Jgauss, hgauss⟩ :=
    exists_harperScheduledCorrelatedGaussian_relaxedSuffixGuard_le
  obtain ⟨Jdrift, hdrift⟩ :=
    exists_harperScheduledRelativeDrift_geometric_half
  let J := max 31 (max Jpath (max Jgauss Jdrift))
  refine ⟨L, hL, J, ?_⟩
  intro shell baseStart d m y hm hstart hd hy t ht s hs hsep u v hfull
  dsimp only
  have hdPos : 0 < d := by omega
  have hbaseThirtyOne : 31 ≤ baseStart :=
    (le_max_left 31 (max Jpath (max Jgauss Jdrift))).trans hstart
  have hJpath : Jpath + (shell + 1) ≤ baseStart + d := by
    have : Jpath ≤ baseStart := by
      have hle : Jpath ≤ max 31 (max Jpath (max Jgauss Jdrift)) :=
        (le_max_left Jpath (max Jgauss Jdrift)).trans
          (le_max_right 31 _)
      exact hle.trans hstart
    omega
  have hJgauss : Jgauss + (shell + 1) ≤ baseStart + d := by
    have : Jgauss ≤ baseStart := by
      have hle : Jgauss ≤ max 31 (max Jpath (max Jgauss Jdrift)) :=
        ((le_max_left Jgauss Jdrift).trans (le_max_right Jpath _)).trans
          (le_max_right 31 _)
      exact hle.trans hstart
    omega
  have hJdrift : Jdrift ≤ baseStart := by
    have hle : Jdrift ≤ max 31 (max Jpath (max Jgauss Jdrift)) :=
      ((le_max_right Jgauss Jdrift).trans (le_max_right Jpath _)).trans
        (le_max_right 31 _)
    exact hle.trans hstart
  let lower := harperPairedSuffixLower
    (harper1144LogBallotLowerBarrier baseStart (d + m)) u
  let upper := harperPairedSuffixUpper
    (harper1144LogBallotUpperBarrier (d + m)) u
  let lower₁ : Fin m → Real := fun k ↦ lower k - 1
  let upper₁ : Fin m → Real := fun k ↦ upper k + 1
  let R : Fin m → Real := fun i ↦
    128 * ((d + i.val + 1 : Nat) : Real) + 6
  let G : Fin m → Measure (Real × Real) := fun i ↦
    harperTwoHeightPrimeBlockVectorLaw y
      (Problem520.harperScheduledPrimeBlock y
        (baseStart + d + i.val)) t s
  let drift : Fin m → Real × Real := fun i ↦
    harperTwoHeightBallotBlockDrift y
      (Problem520.harperScheduledPrimeBlock y
        (baseStart + d + i.val)) t s
  let Ggauss : Measure (Fin m → Real × Real) :=
    Measure.pi (fun i : Fin m ↦
      harperTwoHeightGaussianLaw y
        (Problem520.harperScheduledPrimeBlock y
          (baseStart + d + i.val)) t s)
  have hdriftPoint := hdrift shell baseStart d m y hJdrift hd hy
    t ht s hs hsep
  have hdriftPrefix := cumulative_harperScheduledRelativeDrift_le_one
    hdriftPoint
  have hremoveRaw := pi_translated_pairedBarrier_real_le_relaxed
    G drift lower upper 1
    (fun k ↦ (hdriftPrefix k).1) (fun k ↦ (hdriftPrefix k).2)
  have hlaw :
      (fun i : Fin m ↦
        harperTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) t s) =
      fun i : Fin m ↦
        Measure.map (harperPairTranslate (drift i)) (G i) := by
    funext i
    dsimp only [drift, G]
    exact harperTwoHeightBallotBlockLaw_eq_translate y
      (Problem520.harperScheduledPrimeBlock y
        (baseStart + d + i.val)) t s
  have hremove :
      (Measure.pi (fun i : Fin m ↦
        harperTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) t s)).real
          (harperPairedPartialSumBarrierSet lower upper) ≤
        (Measure.pi G).real
          (harperPairedPartialSumBarrierSet lower₁ upper₁) := by
    rw [hlaw]
    simpa only [lower₁, upper₁] using hremoveRaw
  have hcoordinate :
      ∀ x ∈ harperPairedPartialSumBarrierSet lower₁ upper₁,
        ∀ i, |(x i).1| ≤ R i ∧ |(x i).2| ≤ R i := by
    intro x hx i
    have hxRelaxed : x ∈
        harperPairedRelaxedPartialSumBarrierSet lower upper := by
      simpa only [harperPairedRelaxedPartialSumBarrierSet, lower₁, upper₁]
        using hx
    simpa only [lower, upper, R] using
      abs_coordinates_le_of_mem_harperPairedRelaxedSuffix_logBallot
        hdPos u v hfull x hxRelaxed i
  have hmoderate : ∀ i, 2 * R i + 5 ≤
      (1 / 16 : Real) *
        Real.sqrt (((2 ^ (baseStart + d + i.val) : Nat) : Real)) := by
    intro i
    have hmod := harperScheduled_relaxedSuffixEnvelope_le_moderateWindow
      hbaseThirtyOne (d + i.val)
    dsimp only [R]
    rw [show
      2 * (128 * ((d + i.val + 1 : Nat) : Real) + 6) + 5 =
        256 * ((d + i.val + 1 : Nat) : Real) + 17 by ring]
    simpa only [add_assoc] using hmod
  have hcenterCompare := hpath shell (baseStart + d) m y hJpath
    (by simpa only [add_assoc] using hy) t ht s hs hsep
    lower₁ upper₁ R hcoordinate hmoderate
  have hlower₁ (k : Fin m) :
      -64 * ((d + k.val + 1 : Nat) : Real) - 2 ≤ lower₁ k := by
    dsimp only [lower₁, lower]
    linarith
      [neg_sixtyFour_mul_suffixElapsed_sub_one_le_harperPairedSuffixLower_logBallot
        hdPos u v hfull k]
  have hupper₁ (k : Fin m) : upper₁ k ≤ 64 * (d : Real) + 1 := by
    dsimp only [upper₁, upper]
    linarith [harperPairedSuffixUpper_logBallot_le hdPos u v hfull k]
  have hsubset :
      harperPairedRelaxedPartialSumBarrierSet lower₁ upper₁ ⊆
        harperPairedRelaxedSuffixGuardPathEvent d m :=
    harperPairedRelaxedPartialSumBarrierSet_subset_suffixGuard
      lower₁ upper₁ hlower₁ hupper₁
  have hmono :
      Ggauss.real
          (harperPairedRelaxedPartialSumBarrierSet lower₁ upper₁) ≤
        Ggauss.real (harperPairedRelaxedSuffixGuardPathEvent d m) :=
    measureReal_mono hsubset
  have hgaussBound := hgauss shell (baseStart + d) d m y hm hJgauss
    (by simpa only [add_assoc] using hy) t ht s hs hsep
  dsimp only [G, Ggauss] at hremove hcenterCompare hmono ⊢
  calc
    (Measure.pi (fun i : Fin m ↦
        harperTwoHeightBallotBlockLaw y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet lower upper) ≤
      (Measure.pi (fun i : Fin m ↦
        harperTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y
            (baseStart + d + i.val)) t s)).real
        (harperPairedPartialSumBarrierSet lower₁ upper₁) := hremove
    _ ≤ 4 * Real.exp 4 *
        (Measure.pi (fun i : Fin m ↦
          harperTwoHeightGaussianLaw y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) t s)).real
          (harperPairedRelaxedPartialSumBarrierSet lower₁ upper₁) :=
      hcenterCompare
    _ ≤ 4 * Real.exp 4 *
        (Measure.pi (fun i : Fin m ↦
          harperTwoHeightGaussianLaw y
            (Problem520.harperScheduledPrimeBlock y
              (baseStart + d + i.val)) t s)).real
          (harperPairedRelaxedSuffixGuardPathEvent d m) := by
      exact mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ 4 * Real.exp 4 *
        ((4096 * 68 * (536 * L + 68)) *
          (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹) := by
      exact mul_le_mul_of_nonneg_left hgaussBound (by positivity)

/-- Fubini form of the natural-coherence suffix estimate: the full path mass
is at most the exposed-prefix mass times the uniform continuation cost. -/
theorem exists_harperScheduledTwoHeightLogBallotProduct_natural_le_prefix_mul :
    ∃ L > 0, ∃ J : Nat,
      ∀ shell start d m y : Nat, 0 < m →
        J ≤ start → shell + 1 ≤ d →
        Problem520.harperBlockEndpoint (start + d + m) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (shell + 1) < |t - s| →
                (Measure.pi (fun i : Fin (d + m) ↦
                  harperTwoHeightBallotBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + i.val)) t s)).real
                    (harperPairedPartialSumBarrierSet
                      (harper1144LogBallotLowerBarrier start (d + m))
                      (harper1144LogBallotUpperBarrier (d + m))) ≤
                  (Measure.pi (fun i : Fin d ↦
                    harperTwoHeightBallotBlockLaw y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + i.val)) t s)).real
                      (harperPairedLogBallotPrefixSet start d m) *
                    (4 * Real.exp 4 *
                      ((4096 * 68 * (536 * L + 68)) *
                        (((d + 1 : Nat) : Real) ^ (2 : Nat)) *
                          (m : Real)⁻¹)) := by
  obtain ⟨L, hL, J, hsuffix⟩ :=
    exists_harperScheduledTwoHeightLogBallotSuffix_natural_le
  refine ⟨L, hL, J, ?_⟩
  intro shell start d m y hm hstart hd hy t ht s hs hsep
  let M : Fin (d + m) → Measure (Real × Real) := fun i ↦
    harperTwoHeightBallotBlockLaw y
      (Problem520.harperScheduledPrimeBlock y (start + i.val)) t s
  let C : Real := 4 * Real.exp 4 *
    ((4096 * 68 * (536 * L + 68)) *
      (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹)
  apply pi_real_le_prefixEvent_mul_of_suffix_fiberwise M
    (harperPairedPartialSumBarrierSet
      (harper1144LogBallotLowerBarrier start (d + m))
      (harper1144LogBallotUpperBarrier (d + m)))
    (measurableSet_harperPairedPartialSumBarrierSet _ _)
    (harperPairedLogBallotPrefixSet start d m)
    (measurableSet_harperPairedLogBallotPrefixSet start d m) C
  · intro u v huv
    exact mem_harperPairedLogBallotPrefixSet_of_addCases_mem u v huv
  · intro u _hu
    by_cases hcont : ∃ v : Fin m → Real × Real,
        Fin.addCases u v ∈ harperPairedPartialSumBarrierSet
          (harper1144LogBallotLowerBarrier start (d + m))
          (harper1144LogBallotUpperBarrier (d + m))
    · obtain ⟨v, hv⟩ := hcont
      have hsubset :
          {w : Fin m → Real × Real | Fin.addCases u w ∈
            harperPairedPartialSumBarrierSet
              (harper1144LogBallotLowerBarrier start (d + m))
              (harper1144LogBallotUpperBarrier (d + m))} ⊆
            harperPairedPartialSumBarrierSet
              (harperPairedSuffixLower
                (harper1144LogBallotLowerBarrier start (d + m)) u)
              (harperPairedSuffixUpper
                (harper1144LogBallotUpperBarrier (d + m)) u) := by
        intro w hw
        exact mem_harperPairedSuffixBarrier_of_addCases_mem _ _ u w hw
      have hsuffixBound := hsuffix shell start d m y hm hstart hd hy
        t ht s hs hsep u v hv
      exact (measureReal_mono hsubset (measure_ne_top _ _)).trans (by
        simpa only [M, C, Fin.val_natAdd, add_assoc] using hsuffixBound)
    · have hempty :
          {w : Fin m → Real × Real | Fin.addCases u w ∈
            harperPairedPartialSumBarrierSet
              (harper1144LogBallotLowerBarrier start (d + m))
              (harper1144LogBallotUpperBarrier (d + m))} = ∅ := by
        ext w
        constructor
        · intro hw
          exact False.elim (hcont ⟨w, hw⟩)
        · intro hw
          exact False.elim hw
      rw [hempty, measureReal_empty]
      dsimp only [C]
      positivity

/-- Rooted-density form at the shell's common-history prefix.  The
fourth-power logarithmic pinch is now paired with the natural-coherence
literal suffix cost, with no additional decorrelation delay. -/
theorem exists_harper1144LogBallot_rooted_naturalSuffix_le :
    ∃ B > 0, ∃ L > 0, ∃ J : Nat,
      ∀ start q d m y : Nat, J ≤ start → q + 1 ≤ d → 0 < m →
        Problem520.harperBlockEndpoint (start + d + m) ≤ y →
          ∀ t ∈ harperLowerVerticalBand,
            ∀ s ∈ harperLowerVerticalBand,
              (1 / 2 : Real) ^ (q + 1) < |t - s| →
                let P := Problem520.harperScheduledPrimeRangeFrom y start (q + 1)
                harperTwoHeightCorrelation y t s *
                    (harperTwoHeightCubeLaw y t s).real
                      (harper1144LogBallotCubeEvent y start (d + m) t ∩
                        harper1144LogBallotCubeEvent y start (d + m) s) ≤
                  ((B * (2 : Real) ^ (q + 1) /
                      (((q + 1 : Nat) : Real) ^ (4 : Nat))) *
                    harperSubsetCorrelation y Pᶜ t s) *
                    (4 * Real.exp 4 *
                      ((4096 * 68 * (536 * L + 68)) *
                        (((d + 1 : Nat) : Real) ^ (2 : Nat)) *
                          (m : Real)⁻¹)) := by
  obtain ⟨B, hB, Jroot, hroot⟩ :=
    exists_harper1144LogBallot_correlation_probability_le_powTwo_div_fourth_compl
  obtain ⟨L, hL, Jsuffix, hsuffix⟩ :=
    exists_harperScheduledTwoHeightLogBallotProduct_natural_le_prefix_mul
  let J := max (Jroot + 1) Jsuffix
  refine ⟨B, hB, L, hL, J, ?_⟩
  intro start q d m y hstart hqd hm hy t ht s hs hsep
  dsimp only
  let C : Real := 4 * Real.exp 4 *
    ((4096 * 68 * (536 * L + 68)) *
      (((d + 1 : Nat) : Real) ^ (2 : Nat)) * (m : Real)⁻¹)
  let M : Real := B * (2 : Real) ^ (q + 1) /
    (((q + 1 : Nat) : Real) ^ (4 : Nat))
  have hstartRoot : Jroot + 1 ≤ start :=
    (le_max_left (Jroot + 1) Jsuffix).trans hstart
  have hstartSuffix : Jsuffix ≤ start :=
    (le_max_right (Jroot + 1) Jsuffix).trans hstart
  have hdPos : 0 < d := by omega
  have hprefixY : Problem520.harperBlockEndpoint (start + d) ≤ y := by
    apply (Problem520.strictMono_harperBlockEndpoint.monotone ?_).trans hy
    omega
  let commonLast : Fin d := ⟨q, by omega⟩
  have hcommonLastVal : commonLast.val + 1 = q + 1 := by
    rfl
  have hprefixRoot := hroot start d y hstartRoot hprefixY
    t ht s hs commonLast
  dsimp only at hprefixRoot
  rw [hcommonLastVal] at hprefixRoot
  have hprefixProduct := hsuffix q start d m y hm hstartSuffix hqd hy
    t ht s hs hsep
  have hfullEq :=
    harperTwoHeightCubeLaw_real_preimage_scheduledBallotBlockVectors_eq_pi
      y start (d + m) t s
      (harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m)))
      (measurableSet_harperPairedPartialSumBarrierSet
        (harper1144LogBallotLowerBarrier start (d + m))
        (harper1144LogBallotUpperBarrier (d + m)))
  rw [preimage_scheduledBallotBlockVectors_pairedLogBarrier_eq_inter] at hfullEq
  have hprefixEq :=
    harperTwoHeightCubeLaw_logBallotPrefixInter_eq_pi
      y start d m t s
  have hprob :
      (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start (d + m) t ∩
            harper1144LogBallotCubeEvent y start (d + m) s) ≤
        (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start d t ∩
            harper1144LogBallotCubeEvent y start d s) * C := by
    rw [hfullEq, hprefixEq]
    simpa only [C] using hprefixProduct
  have hcorrNonneg : 0 ≤ harperTwoHeightCorrelation y t s :=
    (harperTwoHeightCorrelation_pos y t s).le
  have hCnonneg : 0 ≤ C := by
    dsimp only [C]
    positivity
  calc
    harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start (d + m) t ∩
            harper1144LogBallotCubeEvent y start (d + m) s) ≤
      harperTwoHeightCorrelation y t s *
        ((harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start d t ∩
            harper1144LogBallotCubeEvent y start d s) * C) :=
        mul_le_mul_of_nonneg_left hprob hcorrNonneg
    _ = (harperTwoHeightCorrelation y t s *
        (harperTwoHeightCubeLaw y t s).real
          (harper1144LogBallotCubeEvent y start d t ∩
            harper1144LogBallotCubeEvent y start d s)) * C := by ring
    _ ≤ (M * harperSubsetCorrelation y
        (Problem520.harperScheduledPrimeRangeFrom y start (q + 1))ᶜ t s) * C :=
      mul_le_mul_of_nonneg_right (by simpa only [M] using hprefixRoot)
        hCnonneg
    _ = _ := by rfl

end

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.abs_coordinate_le_of_relaxed_suffix_partialSum_guard
#print axioms Erdos.Problem1144.abs_partialSum_mul_le_of_relaxed_suffix_guard
#print axioms Erdos.Problem1144.preimage_regression_relaxedSuffixGuard_subset_survival_product
#print axioms Erdos.Problem1144.harperRegressedGaussianTwoWalk_relaxedSuffixGuard_probability_le
#print axioms Erdos.Problem1144.pi_harperTwoHeightGaussianLaw_relaxedSuffixGuard_probability_le
#print axioms Erdos.Problem1144.harperPairedRelaxedPartialSumBarrierSet_subset_suffixGuard
#print axioms Erdos.Problem1144.exists_harperScheduledCorrelatedGaussian_relaxedSuffixGuard_le
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightCenteredLogBallotSuffix_probability_le
#print axioms Erdos.Problem1144.exists_harperScheduledRelativeDrift_geometric_half
#print axioms Erdos.Problem1144.cumulative_harperScheduledRelativeDrift_le_one
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightLogBallotSuffix_natural_le
#print axioms Erdos.Problem1144.exists_harperScheduledTwoHeightLogBallotProduct_natural_le_prefix_mul
#print axioms Erdos.Problem1144.exists_harper1144LogBallot_rooted_naturalSuffix_le
