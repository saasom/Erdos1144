import Erdos.Problem1144.HarperGaussianTwoWalkBallot

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# A summably correlated Gaussian two-walk ballot

After the height-coherence scale, a covariance-matched Gaussian pair can be
written conditionally as `Y_j = lambda_j X_j + W_j`, where the `W_j` are
independent of the first walk.  The coefficients `lambda_j` decay
geometrically.  The linear lower guard in the logarithmic-ballot event then
makes the induced partial-sum drift uniformly bounded.  This is the mechanism
which avoids the artificial `n^-40` covariance cutoff.

This file first isolates the deterministic heart of that argument.
-/

/-- The elementary weighted geometric sum used by the conditional drift
bound. -/
theorem sum_range_succ_mul_half_pow_eq (n : Nat) :
    (∑ i ∈ Finset.range n,
        (((i + 1 : Nat) : Real) * (1 / 2 : Real) ^ i)) =
      4 - (((2 * n + 4 : Nat) : Real) * (1 / 2 : Real) ^ n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      rw [pow_succ]
      ring

theorem sum_range_succ_mul_half_pow_le_four (n : Nat) :
    (∑ i ∈ Finset.range n,
        (((i + 1 : Nat) : Real) * (1 / 2 : Real) ^ i)) ≤ 4 := by
  rw [sum_range_succ_mul_half_pow_eq]
  have hnonneg : 0 ≤
      (((2 * n + 4 : Nat) : Real) * (1 / 2 : Real) ^ n) := by
    positivity
  linarith

/-- A path trapped between the logarithmic event's linear lower guard and
its flat upper envelope has increments of size at most `128(i+1)`. -/
theorem abs_coordinate_le_of_linear_partialSum_guard
    {n : Nat} (omega : Fin n → Real)
    (hlower : ∀ k : Fin n,
      -64 * (((k.val + 1 : Nat) : Real)) ≤
        Problem520.harperPathPartialSum omega k)
    (hupper : ∀ k : Fin n,
      Problem520.harperPathPartialSum omega k ≤ 1)
    (i : Fin n) :
    |omega i| ≤ 128 * (((i.val + 1 : Nat) : Real)) := by
  have habsSum (k : Fin n) :
      |Problem520.harperPathPartialSum omega k| ≤
        64 * (((k.val + 1 : Nat) : Real)) := by
    rw [abs_le]
    constructor
    · nlinarith [hlower k]
    · have hk : (1 : Real) ≤
          64 * (((k.val + 1 : Nat) : Real)) := by
        have : (1 : Real) ≤ ((k.val + 1 : Nat) : Real) := by
          exact_mod_cast (show 1 ≤ k.val + 1 by omega)
        nlinarith
      exact (hupper k).trans hk
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
    have hiCast : (((i.val + 1 : Nat) : Real)) = 1 := by
      rw [hi]
      norm_num
    rw [hiCast] at hiBound ⊢
    linarith
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
          have hval : j.val < i.val := by
            have hle : j.val ≤ i.val := hj
            have hne : j.val ≠ i.val := by
              intro heq
              exact hji (Fin.eq_of_val_eq heq)
            omega
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
      _ ≤ 64 * (((i.val + 1 : Nat) : Real)) +
          64 * (((p.val + 1 : Nat) : Real)) := by
        exact add_le_add (habsSum i) (habsSum p)
      _ ≤ 128 * (((i.val + 1 : Nat) : Real)) := by
        have hp : p.val + 1 ≤ i.val + 1 := by
          dsimp only [p]
          omega
        exact_mod_cast (show
          64 * (i.val + 1) + 64 * (p.val + 1) ≤
            128 * (i.val + 1) by omega)

/-- Geometrically decaying regression coefficients turn every path in the
linear corridor into an absolute-constant conditional drift. -/
theorem abs_partialSum_mul_le_of_geometric_coefficients
    {n : Nat} (lambda omega : Fin n → Real) (L : Real) (hL : 0 ≤ L)
    (hlambda : ∀ i : Fin n,
      |lambda i| ≤ L * (1 / 2 : Real) ^ i.val)
    (hlower : ∀ k : Fin n,
      -64 * (((k.val + 1 : Nat) : Real)) ≤
        Problem520.harperPathPartialSum omega k)
    (hupper : ∀ k : Fin n,
      Problem520.harperPathPartialSum omega k ≤ 1)
    (k : Fin n) :
    |Problem520.harperPathPartialSum (fun i ↦ lambda i * omega i) k| ≤
      512 * L := by
  unfold Problem520.harperPathPartialSum
  calc
    |∑ i ∈ Finset.Iic k, lambda i * omega i| ≤
        ∑ i ∈ Finset.Iic k, |lambda i * omega i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Iic k,
        (128 * L) *
          ((((i.val + 1 : Nat) : Real)) *
            (1 / 2 : Real) ^ i.val) := by
      gcongr with i hi
      rw [abs_mul]
      have homega := abs_coordinate_le_of_linear_partialSum_guard
        omega hlower hupper i
      have hpow : 0 ≤ (1 / 2 : Real) ^ i.val := by positivity
      calc
        |lambda i| * |omega i| ≤
            (L * (1 / 2 : Real) ^ i.val) *
              (128 * (((i.val + 1 : Nat) : Real))) := by
          exact mul_le_mul (hlambda i) homega (abs_nonneg _)
            (mul_nonneg hL hpow)
        _ = (128 * L) *
            ((((i.val + 1 : Nat) : Real)) *
              (1 / 2 : Real) ^ i.val) := by ring
    _ = (128 * L) *
        (∑ i ∈ Finset.range (k.val + 1),
          (((i + 1 : Nat) : Real) * (1 / 2 : Real) ^ i)) := by
      rw [Finset.mul_sum]
      change Problem520.harperPathPartialSum
          (fun i : Fin n ↦
            (128 * L) *
              ((((i.val + 1 : Nat) : Real)) *
                (1 / 2 : Real) ^ i.val)) k = _
      rw [Problem520.harperPathPartialSum_eq_sum_prefix]
      change (∑ i : Fin (k.val + 1),
        (128 * L) *
          ((((i.val + 1 : Nat) : Real)) *
            (1 / 2 : Real) ^ i.val)) = _
      exact Fin.sum_univ_eq_sum_range
        (fun i : Nat ↦
          (128 * L) *
            ((((i + 1 : Nat) : Real)) * (1 / 2 : Real) ^ i))
        (k.val + 1)
    _ ≤ (128 * L) * 4 := by
      exact mul_le_mul_of_nonneg_left
        (sum_range_succ_mul_half_pow_le_four (k.val + 1))
        (mul_nonneg (by norm_num) hL)
    _ = 512 * L := by ring

/-! ## The conditional Gaussian two-walk estimate -/

/-- The coarse corridor containing the pinched logarithmic event. -/
def harperLinearGuardPathEvent (n : Nat) : Set (Fin n → Real) :=
  Problem520.harperPartialSumBarrierSet
    (fun k ↦ -64 * (((k.val + 1 : Nat) : Real)))
    (fun _ ↦ 1)

theorem measurableSet_harperLinearGuardPathEvent (n : Nat) :
    MeasurableSet (harperLinearGuardPathEvent n) := by
  exact Problem520.measurableSet_harperPartialSumBarrierSet _ _

/-- The triangular regression map `(X,W) ↦ (X, lambda*X+W)`. -/
def harperGaussianRegressionMap {n : Nat} (lambda : Fin n → Real)
    (z : (Fin n → Real) × (Fin n → Real)) :
    (Fin n → Real) × (Fin n → Real) :=
  (z.1, fun i ↦ lambda i * z.1 i + z.2 i)

theorem measurable_harperGaussianRegressionMap
    {n : Nat} (lambda : Fin n → Real) :
    Measurable (harperGaussianRegressionMap lambda) := by
  unfold harperGaussianRegressionMap
  apply measurable_fst.prodMk
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact (measurable_const.mul
      ((measurable_pi_apply i).comp measurable_fst)).add
    ((measurable_pi_apply i).comp measurable_snd)

/-- The independent source law for a Gaussian regression representation. -/
noncomputable def harperGaussianRegressionSource
    {n : Nat} (variance residualVariance : Fin n → NNReal) :
    Measure ((Fin n → Real) × (Fin n → Real)) :=
  (Measure.pi (fun i ↦ gaussianReal 0 (variance i))).prod
    (Measure.pi (fun i ↦ gaussianReal 0 (residualVariance i)))

instance harperGaussianRegressionSource_isProbabilityMeasure
    {n : Nat} (variance residualVariance : Fin n → NNReal) :
    IsProbabilityMeasure
      (harperGaussianRegressionSource variance residualVariance) := by
  unfold harperGaussianRegressionSource
  infer_instance

/-- The corresponding correlated Gaussian path law. -/
noncomputable def harperRegressedGaussianTwoWalkMeasure
    {n : Nat} (variance residualVariance : Fin n → NNReal)
    (lambda : Fin n → Real) :
    Measure ((Fin n → Real) × (Fin n → Real)) :=
  Measure.map (harperGaussianRegressionMap lambda)
    (harperGaussianRegressionSource variance residualVariance)

instance harperRegressedGaussianTwoWalkMeasure_isProbabilityMeasure
    {n : Nat} (variance residualVariance : Fin n → NNReal)
    (lambda : Fin n → Real) :
    IsProbabilityMeasure
      (harperRegressedGaussianTwoWalkMeasure
        variance residualVariance lambda) := by
  unfold harperRegressedGaussianTwoWalkMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_harperGaussianRegressionMap lambda).aemeasurable

/-- On the linear guard, the triangular regression event is contained in a
literal product of two one-walk survival events. -/
theorem preimage_regression_pair_guard_subset_survival_product
    {n : Nat} (lambda : Fin n → Real) (L : Real) (hL : 0 ≤ L)
    (hlambda : ∀ i : Fin n,
      |lambda i| ≤ L * (1 / 2 : Real) ^ i.val) :
    harperGaussianRegressionMap lambda ⁻¹'
        (harperLinearGuardPathEvent n ×ˢ harperLinearGuardPathEvent n) ⊆
      harperLinearGuardPathEvent n ×ˢ
        Problem520.gaussianWalkSurvivalSet n (1 + 512 * L) := by
  intro z hz
  have hx : z.1 ∈ harperLinearGuardPathEvent n := hz.1
  have hy : (fun i ↦ lambda i * z.1 i + z.2 i) ∈
      harperLinearGuardPathEvent n := hz.2
  refine ⟨hx, ?_⟩
  change Problem520.gaussianWalkSurvives n (1 + 512 * L) z.2
  rw [gaussianWalkSurvives_iff_harperPathPartialSum_le]
  intro k
  have hxlower : ∀ j : Fin n,
      -64 * (((j.val + 1 : Nat) : Real)) ≤
        Problem520.harperPathPartialSum z.1 j := fun j ↦
    (Problem520.mem_harperPartialSumBarrierSet.mp hx j).1
  have hxupper : ∀ j : Fin n,
      Problem520.harperPathPartialSum z.1 j ≤ 1 := fun j ↦
    (Problem520.mem_harperPartialSumBarrierSet.mp hx j).2
  have hyupper :=
    (Problem520.mem_harperPartialSumBarrierSet.mp hy k).2
  have hdrift := abs_partialSum_mul_le_of_geometric_coefficients
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
      -512 * L ≤ Problem520.harperPathPartialSum
        (fun i ↦ lambda i * z.1 i) k := by
    rw [abs_le] at hdrift
    nlinarith [hdrift.1]
  linarith

/-- A summably correlated Gaussian pair pays the sharp squared-ballot cost.
No covariance cutoff depending on the path length occurs. -/
theorem harperRegressedGaussianTwoWalk_linearGuard_probability_le
    {n : Nat} (hn : 0 < n)
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
      (harperLinearGuardPathEvent n ×ˢ harperLinearGuardPathEvent n) ≤
        (12288 * (512 * L + 3)) * (n : Real)⁻¹ := by
  let P := Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))
  let Q := Measure.pi
    (fun i : Fin n ↦ gaussianReal 0 (residualVariance i))
  let G := harperLinearGuardPathEvent n
  let H := Problem520.gaussianWalkSurvivalSet n (1 + 512 * L)
  have hGmeas : MeasurableSet G :=
    measurableSet_harperLinearGuardPathEvent n
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
      harperGaussianRegressionMap lambda ⁻¹' (G ×ˢ G) ⊆ G ×ˢ H := by
    simpa only [G, H] using
      preimage_regression_pair_guard_subset_survival_product
        lambda L hL hlambda
  have hfirstSubset : G ⊆ Problem520.gaussianWalkSurvivalSet n 1 := by
    intro omega homega
    change Problem520.gaussianWalkSurvives n 1 omega
    rw [gaussianWalkSurvives_iff_harperPathPartialSum_le]
    intro k
    exact (Problem520.mem_harperPartialSumBarrierSet.mp homega k).2
  have hfirst : P.real G ≤ 192 / Real.sqrt (n : Real) := by
    calc
      P.real G ≤ P.real (Problem520.gaussianWalkSurvivalSet n 1) :=
        measureReal_mono hfirstSubset
      _ ≤ 64 * (1 + 2) / Real.sqrt (n : Real) := by
        simpa only [P] using
          Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
            n hn variance (by norm_num) hvarianceLower hvarianceUpper
      _ = 192 / Real.sqrt (n : Real) := by ring
  have hcapNonneg : 0 ≤ 1 + 512 * L := by positivity
  have hsecond : Q.real H ≤
      64 * (512 * L + 3) / Real.sqrt (n : Real) := by
    have hbase :=
      Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
        n hn residualVariance hcapNonneg hresidualLower hresidualUpper
    simpa only [Q, H, show 1 + 512 * L + 2 = 512 * L + 3 by ring]
      using hbase
  have hproduct : (P.prod Q).real (G ×ˢ H) = P.real G * Q.real H := by
    simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  change (harperRegressedGaussianTwoWalkMeasure
      variance residualVariance lambda).real (G ×ˢ G) ≤ _
  rw [hmap]
  calc
    (P.prod Q).real
        (harperGaussianRegressionMap lambda ⁻¹' (G ×ˢ G)) ≤
      (P.prod Q).real (G ×ˢ H) := measureReal_mono hsubset
    _ = P.real G * Q.real H := hproduct
    _ ≤ (192 / Real.sqrt (n : Real)) *
        (64 * (512 * L + 3) / Real.sqrt (n : Real)) :=
      mul_le_mul hfirst hsecond measureReal_nonneg (by positivity)
    _ = (12288 * (512 * L + 3)) * (n : Real)⁻¹ := by
      rw [div_mul_div_comm, ← pow_two (Real.sqrt (n : Real)),
        Real.sq_sqrt hnR.le]
      field_simp
      ring

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.sum_range_succ_mul_half_pow_eq
#print axioms Erdos.Problem1144.abs_coordinate_le_of_linear_partialSum_guard
#print axioms Erdos.Problem1144.abs_partialSum_mul_le_of_geometric_coefficients
#print axioms Erdos.Problem1144.preimage_regression_pair_guard_subset_survival_product
#print axioms Erdos.Problem1144.harperRegressedGaussianTwoWalk_linearGuard_probability_le
