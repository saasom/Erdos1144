import Erdos.Problem1144.HarperRankinTwoHeightCorrelation

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The normalized Rankin two-height product law

For a nonnegative Rankin shift, the product of the two shifted Euler
densities is normalized into an honest independent prime-coordinate law.
This gives the exact probability factor in the shifted second moment.
-/

/-- Probability weight of one Boolean sign under the shifted two-height
tilt. -/
noncomputable def harperRankinTwoHeightCoinWeight
    (p : ℕ) (a t s : ℝ) (b : Bool) : ℝ :=
  harperRankinCoordinateFactor p a t b *
      harperRankinCoordinateFactor p a s b /
    (2 * harperRankinTwoHeightPrimeNormalizer p a t s)

theorem harperRankinTwoHeightCoinWeight_nonneg
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a)
    (t s : ℝ) (b : Bool) :
    0 ≤ harperRankinTwoHeightCoinWeight p a t s b := by
  unfold harperRankinTwoHeightCoinWeight
  exact div_nonneg
    (mul_nonneg
      (harperRankinCoordinateFactor_pos hp ha t b).le
      (harperRankinCoordinateFactor_pos hp ha s b).le)
    (mul_nonneg (by norm_num)
      (harperRankinTwoHeightPrimeNormalizer_pos hp ha t s).le)

noncomputable def harperRankinTwoHeightCoinWeightNNReal
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s : ℝ) (b : Bool) : NNReal :=
  ⟨harperRankinTwoHeightCoinWeight p a t s b,
    harperRankinTwoHeightCoinWeight_nonneg hp ha t s b⟩

@[simp] theorem coe_harperRankinTwoHeightCoinWeightNNReal
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s : ℝ) (b : Bool) :
    (harperRankinTwoHeightCoinWeightNNReal p hp a ha t s b : ℝ) =
      harperRankinTwoHeightCoinWeight p a t s b := rfl

theorem harperRankinTwoHeightCoinWeight_false_add_true
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    harperRankinTwoHeightCoinWeight p a t s false +
      harperRankinTwoHeightCoinWeight p a t s true = 1 := by
  unfold harperRankinTwoHeightCoinWeight
  rw [← add_div, harperRankinTwoHeightPrimeNormalizer_eq]
  have hsum :
      0 < harperRankinCoordinateFactor p a t false *
            harperRankinCoordinateFactor p a s false +
          harperRankinCoordinateFactor p a t true *
            harperRankinCoordinateFactor p a s true :=
    add_pos
      (mul_pos (harperRankinCoordinateFactor_pos hp ha t false)
        (harperRankinCoordinateFactor_pos hp ha s false))
      (mul_pos (harperRankinCoordinateFactor_pos hp ha t true)
        (harperRankinCoordinateFactor_pos hp ha s true))
  field_simp [hsum.ne']

theorem harperRankinTwoHeightCoinWeightNNReal_false_add_true
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    harperRankinTwoHeightCoinWeightNNReal p hp a ha t s false +
      harperRankinTwoHeightCoinWeightNNReal p hp a ha t s true = 1 := by
  ext
  exact harperRankinTwoHeightCoinWeight_false_add_true hp ha t s

/-- One-coordinate shifted two-height tilted probability measure. -/
noncomputable def harperRankinTwoHeightCoin
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s : ℝ) : Measure Bool :=
  (harperRankinTwoHeightCoinWeightNNReal p hp a ha t s false : ENNReal) •
      Measure.dirac false +
    (harperRankinTwoHeightCoinWeightNNReal p hp a ha t s true : ENNReal) •
      Measure.dirac true

instance harperRankinTwoHeightCoin_isProbabilityMeasure
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ) :
    IsProbabilityMeasure (harperRankinTwoHeightCoin p hp a ha t s) where
  measure_univ := by
    simp [harperRankinTwoHeightCoin]
    rw [ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one]
    rw [← ENNReal.coe_add,
      harperRankinTwoHeightCoinWeightNNReal_false_add_true hp ha]
    simp

@[simp] theorem harperRankinTwoHeightCoin_apply_singleton
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s : ℝ) (b : Bool) :
    harperRankinTwoHeightCoin p hp a ha t s {b} =
      (harperRankinTwoHeightCoinWeightNNReal p hp a ha t s b : ENNReal) := by
  cases b <;> simp [harperRankinTwoHeightCoin] <;>
    rw [ENNReal.smul_def, smul_eq_mul, mul_one]

@[simp] theorem harperRankinTwoHeightCoin_real_singleton
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s : ℝ) (b : Bool) :
    (harperRankinTwoHeightCoin p hp a ha t s).real {b} =
      harperRankinTwoHeightCoinWeight p a t s b := by
  rw [Measure.real, harperRankinTwoHeightCoin_apply_singleton]
  simp

/-- Expectation under one shifted two-height coin is its explicit biased
two-point average. -/
theorem integral_harperRankinTwoHeightCoin
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a)
    (t s : ℝ) (g : Bool → ℝ) :
    (∫ b, g b ∂harperRankinTwoHeightCoin p hp a ha t s) =
      harperRankinTwoHeightCoinWeight p a t s false * g false +
        harperRankinTwoHeightCoinWeight p a t s true * g true := by
  rw [integral_fintype (Integrable.of_finite :
    Integrable g (harperRankinTwoHeightCoin p hp a ha t s))]
  simp only [harperRankinTwoHeightCoin_real_singleton, smul_eq_mul]
  rw [Fintype.sum_bool]
  ring

/-- Exact sign bias under the shifted two-height product tilt. -/
noncomputable def harperRankinTwoHeightTiltBias
    (p : ℕ) (a t s : ℝ) : ℝ :=
  harperRankinTwoHeightCoinWeight p a t s true -
    harperRankinTwoHeightCoinWeight p a t s false

theorem harperRankinTwoHeightTiltBias_eq
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    harperRankinTwoHeightTiltBias p a t s =
      harperRankinEulerNormalizer p a *
          (2 * harperRankinEulerRadius p a *
              Real.cos (t * Real.log (p : ℝ)) +
            2 * harperRankinEulerRadius p a *
              Real.cos (s * Real.log (p : ℝ))) /
        harperRankinTwoHeightPrimeNormalizer p a t s := by
  unfold harperRankinTwoHeightTiltBias harperRankinTwoHeightCoinWeight
  rw [harperRankinCoordinateFactor_true_eq_base_add,
    harperRankinCoordinateFactor_true_eq_base_add,
    harperRankinCoordinateFactor_false_eq_base_sub,
    harperRankinCoordinateFactor_false_eq_base_sub]
  field_simp [(harperRankinTwoHeightPrimeNormalizer_pos hp ha t s).ne']
  ring

theorem integral_cubeSign_harperRankinTwoHeightCoin
    (p : ℕ) (hp : p.Prime) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ) :
    (∫ b, Problem520.cubeSign b
        ∂harperRankinTwoHeightCoin p hp a ha t s) =
      harperRankinTwoHeightTiltBias p a t s := by
  rw [integral_harperRankinTwoHeightCoin]
  change harperRankinTwoHeightCoinWeight p a t s false * (-1) +
      harperRankinTwoHeightCoinWeight p a t s true * 1 = _
  unfold harperRankinTwoHeightTiltBias
  ring

/-- Product of the one-prime shifted two-height normalizers. -/
noncomputable def harperRankinTwoHeightNormalizer
    (y : ℕ) (a t s : ℝ) : ℝ :=
  ∏ p : Problem520.HarperPrimeIndex y,
    harperRankinTwoHeightPrimeNormalizer p.1 a t s

theorem harperRankinTwoHeightNormalizer_pos
    (y : ℕ) {a : ℝ} (ha : 0 ≤ a) (t s : ℝ) :
    0 < harperRankinTwoHeightNormalizer y a t s := by
  unfold harperRankinTwoHeightNormalizer
  exact Finset.prod_pos fun p _hp ↦
    harperRankinTwoHeightPrimeNormalizer_pos
      (Nat.prime_of_mem_primesBelow p.property) ha t s

/-- Exact split into the square of the shifted one-height normalizer and the
pure shifted correlation product. -/
theorem harperRankinTwoHeightNormalizer_eq_energy_sq_mul_correlation
    (y : ℕ) (a t s : ℝ) :
    harperRankinTwoHeightNormalizer y a t s =
      harperRankinPrimeEnergyNormalizer y a ^ (2 : ℕ) *
        harperRankinTwoHeightCorrelation y a t s := by
  unfold harperRankinTwoHeightNormalizer harperRankinTwoHeightCorrelation
    harperRankinPrimeEnergyNormalizer
  calc
    (∏ p : Problem520.HarperPrimeIndex y,
        harperRankinTwoHeightPrimeNormalizer p.1 a t s) =
      ∏ p : Problem520.HarperPrimeIndex y,
        (harperRankinEulerNormalizer p.1 a ^ (2 : ℕ) *
          harperRankinTwoHeightPrimeCorrelation p.1 a t s) := by
      apply Finset.prod_congr rfl
      intro p _hp
      unfold harperRankinTwoHeightPrimeCorrelation
      have hden : harperRankinEulerNormalizer p.1 a ^ (2 : ℕ) ≠ 0 :=
        pow_ne_zero _ (harperRankinEulerNormalizer_pos p.1 a).ne'
      field_simp [hden, (harperRankinEulerNormalizer_pos p.1 a).ne']
      <;> ring
    _ = (∏ p : Problem520.HarperPrimeIndex y,
          harperRankinEulerNormalizer p.1 a ^ (2 : ℕ)) *
        ∏ p : Problem520.HarperPrimeIndex y,
          harperRankinTwoHeightPrimeCorrelation p.1 a t s := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ p : Problem520.HarperPrimeIndex y,
          harperRankinEulerNormalizer p.1 a) ^ (2 : ℕ) *
        ∏ p : Problem520.HarperPrimeIndex y,
          harperRankinTwoHeightPrimeCorrelation p.1 a t s := by
      rw [Finset.prod_pow]
    _ = (∏ p ∈ (y + 1).primesBelow,
          harperRankinEulerNormalizer p a) ^ (2 : ℕ) *
        ∏ p : Problem520.HarperPrimeIndex y,
          harperRankinTwoHeightPrimeCorrelation p.1 a t s := by
      exact congrArg
        (fun z : ℝ ↦ z ^ (2 : ℕ) *
          ∏ p : Problem520.HarperPrimeIndex y,
            harperRankinTwoHeightPrimeCorrelation p.1 a t s)
        (Finset.prod_coe_sort ((y + 1).primesBelow)
          (fun p ↦ harperRankinEulerNormalizer p a))

/-- The independent shifted two-height law on the finite prime cube. -/
noncomputable def harperRankinTwoHeightCubeLaw
    (y : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ) :
    Measure (Problem520.HarperPrimeCube y) :=
  Measure.pi fun p : Problem520.HarperPrimeIndex y ↦
    harperRankinTwoHeightCoin p.1
      (Nat.prime_of_mem_primesBelow p.property) a ha t s

instance harperRankinTwoHeightCubeLaw_isProbabilityMeasure
    (y : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ) :
    IsProbabilityMeasure (harperRankinTwoHeightCubeLaw y a ha t s) := by
  unfold harperRankinTwoHeightCubeLaw
  infer_instance

/-- Coordinates remain independent under the shifted two-height product
law. -/
theorem iIndepFun_harperRankinTwoHeightCube_coordinates
    (y : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ) :
    iIndepFun
      (fun p : Problem520.HarperPrimeIndex y ↦
        fun eta : Problem520.HarperPrimeCube y ↦ eta p)
      (harperRankinTwoHeightCubeLaw y a ha t s) := by
  unfold harperRankinTwoHeightCubeLaw
  exact iIndepFun_pi
    (X := fun _ : Problem520.HarperPrimeIndex y ↦ id)
    (fun _ ↦ aemeasurable_id)

/-- Every coordinate has the corresponding shifted two-height coin as its
marginal law. -/
theorem measurePreserving_harperRankinTwoHeightCube_eval
    (y : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ)
    (p : Problem520.HarperPrimeIndex y) :
    MeasurePreserving
      (fun eta : Problem520.HarperPrimeCube y ↦ eta p)
      (harperRankinTwoHeightCubeLaw y a ha t s)
      (harperRankinTwoHeightCoin p.1
        (Nat.prime_of_mem_primesBelow p.property) a ha t s) := by
  unfold harperRankinTwoHeightCubeLaw
  exact measurePreserving_eval
    (fun q : Problem520.HarperPrimeIndex y ↦
      harperRankinTwoHeightCoin q.1
        (Nat.prime_of_mem_primesBelow q.property) a ha t s) p

/-- Integration of a one-coordinate observable reduces to its shifted
two-point marginal. -/
theorem integral_harperRankinTwoHeightCube_eval
    (y : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ)
    (p : Problem520.HarperPrimeIndex y) (g : Bool → ℝ) :
    (∫ eta, g (eta p) ∂harperRankinTwoHeightCubeLaw y a ha t s) =
      ∫ b, g b ∂harperRankinTwoHeightCoin p.1
        (Nat.prime_of_mem_primesBelow p.property) a ha t s := by
  have hmp := measurePreserving_harperRankinTwoHeightCube_eval
    y a ha t s p
  calc
    (∫ eta, g (eta p) ∂harperRankinTwoHeightCubeLaw y a ha t s) =
        ∫ b, g b ∂Measure.map
          (fun eta : Problem520.HarperPrimeCube y ↦ eta p)
          (harperRankinTwoHeightCubeLaw y a ha t s) := by
      symm
      exact integral_map hmp.measurable.aemeasurable
        (measurable_of_finite g).aestronglyMeasurable
    _ = _ := by rw [hmp.map_eq]

@[simp] theorem harperRankinTwoHeightCubeLaw_real_singleton
    (y : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ)
    (eta : Problem520.HarperPrimeCube y) :
    (harperRankinTwoHeightCubeLaw y a ha t s).real {eta} =
      ∏ p : Problem520.HarperPrimeIndex y,
        harperRankinTwoHeightCoinWeight p.1 a t s (eta p) := by
  rw [Measure.real, harperRankinTwoHeightCubeLaw, Measure.pi_singleton,
    ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [← Measure.real, harperRankinTwoHeightCoin_real_singleton]

theorem harperRankinTwoHeightPrimeNormalizer_mul_weight
    {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : 0 ≤ a)
    (t s : ℝ) (b : Bool) :
    harperRankinTwoHeightPrimeNormalizer p a t s *
        harperRankinTwoHeightCoinWeight p a t s b =
      harperRankinCoordinateFactor p a t b *
        harperRankinCoordinateFactor p a s b * (1 / 2 : ℝ) := by
  unfold harperRankinTwoHeightCoinWeight
  field_simp [(harperRankinTwoHeightPrimeNormalizer_pos hp ha t s).ne']

/-- Pointwise Radon--Nikodym identity for the shifted two-height law. -/
theorem harperRankinTwoHeightNormalizer_mul_cubeLaw_singleton
    (y : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ)
    (eta : Problem520.HarperPrimeCube y) :
    harperRankinTwoHeightNormalizer y a t s *
        (harperRankinTwoHeightCubeLaw y a ha t s).real {eta} =
      harperRankinCubeDensity y a t eta *
        harperRankinCubeDensity y a s eta *
        (Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦
          Problem520.coin)).real {eta} := by
  rw [harperRankinTwoHeightCubeLaw_real_singleton,
    Problem520.fairHarperCubeLaw_real_singleton]
  unfold harperRankinTwoHeightNormalizer harperRankinCubeDensity
  calc
    (∏ p : Problem520.HarperPrimeIndex y,
        harperRankinTwoHeightPrimeNormalizer p.1 a t s) *
        ∏ p : Problem520.HarperPrimeIndex y,
          harperRankinTwoHeightCoinWeight p.1 a t s (eta p) =
      ∏ p : Problem520.HarperPrimeIndex y,
        (harperRankinTwoHeightPrimeNormalizer p.1 a t s *
          harperRankinTwoHeightCoinWeight p.1 a t s (eta p)) := by
      rw [Finset.prod_mul_distrib]
    _ = ∏ p : Problem520.HarperPrimeIndex y,
        (harperRankinCoordinateFactor p.1 a t (eta p) *
          harperRankinCoordinateFactor p.1 a s (eta p) *
          (1 / 2 : ℝ)) := by
      apply Finset.prod_congr rfl
      intro p _hp
      exact harperRankinTwoHeightPrimeNormalizer_mul_weight
        (Nat.prime_of_mem_primesBelow p.property) ha t s (eta p)
    _ = (∏ p : Problem520.HarperPrimeIndex y,
          harperRankinCoordinateFactor p.1 a t (eta p)) *
        (∏ p : Problem520.HarperPrimeIndex y,
          harperRankinCoordinateFactor p.1 a s (eta p)) *
        ∏ _p : Problem520.HarperPrimeIndex y, (1 / 2 : ℝ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

/-- Exact two-height change of measure for any finite-cube observable. -/
theorem harperRankinTwoHeightNormalizer_mul_integral_cubeLaw_eq
    (y : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ)
    (g : Problem520.HarperPrimeCube y → ℝ) :
    harperRankinTwoHeightNormalizer y a t s *
        (∫ eta, g eta ∂harperRankinTwoHeightCubeLaw y a ha t s) =
      ∫ eta,
        (harperRankinCubeDensity y a t eta *
          harperRankinCubeDensity y a s eta) * g eta
        ∂Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦
          Problem520.coin) := by
  rw [integral_fintype (Integrable.of_finite :
      Integrable g (harperRankinTwoHeightCubeLaw y a ha t s)),
    integral_fintype (Integrable.of_finite :
      Integrable (fun eta ↦
        (harperRankinCubeDensity y a t eta *
          harperRankinCubeDensity y a s eta) * g eta)
        (Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦
          Problem520.coin))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _heta
  calc
    harperRankinTwoHeightNormalizer y a t s *
        ((harperRankinTwoHeightCubeLaw y a ha t s).real {eta} • g eta) =
      (harperRankinTwoHeightNormalizer y a t s *
          (harperRankinTwoHeightCubeLaw y a ha t s).real {eta}) * g eta := by
      simp only [smul_eq_mul]
      ring
    _ = (harperRankinCubeDensity y a t eta *
          harperRankinCubeDensity y a s eta *
          (Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦
            Problem520.coin)).real {eta}) * g eta := by
      rw [harperRankinTwoHeightNormalizer_mul_cubeLaw_singleton]
    _ = (Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦
          Problem520.coin)).real {eta} •
        ((harperRankinCubeDensity y a t eta *
          harperRankinCubeDensity y a s eta) * g eta) := by
      simp only [smul_eq_mul]
      ring

/-- Event form of the exact shifted two-height change of measure. -/
theorem harperRankinTwoHeightCubeMass_eq_normalizer_mul_probability
    (y : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ)
    (A : Set (Problem520.HarperPrimeCube y)) :
    harperRankinTwoHeightCubeMass y a t s A =
      harperRankinTwoHeightNormalizer y a t s *
        (harperRankinTwoHeightCubeLaw y a ha t s).real A := by
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  rw [← integral_indicator_one
    (μ := harperRankinTwoHeightCubeLaw y a ha t s) hA,
    harperRankinTwoHeightNormalizer_mul_integral_cubeLaw_eq]
  unfold harperRankinTwoHeightCubeMass
  rw [← integral_indicator hA]
  apply integral_congr_ae
  exact ae_of_all _ fun eta ↦ by
    by_cases heta : eta ∈ A
    · simp [Set.indicator_of_mem heta]
    · simp [Set.indicator_of_notMem heta]

#print axioms Erdos.Problem1144.harperRankinTwoHeightNormalizer_eq_energy_sq_mul_correlation
#print axioms Erdos.Problem1144.harperRankinTwoHeightTiltBias_eq
#print axioms Erdos.Problem1144.iIndepFun_harperRankinTwoHeightCube_coordinates
#print axioms Erdos.Problem1144.integral_harperRankinTwoHeightCube_eval
#print axioms Erdos.Problem1144.harperRankinTwoHeightNormalizer_mul_integral_cubeLaw_eq
#print axioms Erdos.Problem1144.harperRankinTwoHeightCubeMass_eq_normalizer_mul_probability

end


end Problem1144
end Erdos
