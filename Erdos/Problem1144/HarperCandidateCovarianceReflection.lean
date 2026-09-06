import Erdos.Problem1144.HarperCandidateCovarianceRowContractionEuler
import Erdos.Problem1144.HarperCandidateCovarianceScreen

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The actual squarefree Euler density is even in angular height. -/
theorem candidate_eulerDensity_neg (Y : ℕ) (ω : Omega) (t : ℝ) :
    Problem520.harperEulerDensity Y ω (-t) = Problem520.harperEulerDensity Y ω t := by
  rw [← candidate_critical_rankinDensity_eq, candidate_shifted_euler_density_neg,
    candidate_critical_rankinDensity_eq]

/-- The Cauchy denominator preserves the reflection symmetry. -/
theorem candidate_eulerBandSquaredWeight_neg (Y : ℕ) (ω : Omega) (t : ℝ) :
    candidateEulerBandSquaredWeight Y ω (-t) = candidateEulerBandSquaredWeight Y ω t := by
  simp only [candidateEulerBandSquaredWeight, candidate_eulerDensity_neg, neg_sq]

/-- Every literal D-star prefix condition is unchanged by reflection. -/
theorem candidate_covarianceDStar_neg (start N : ℕ) (t W : ℝ) :
    candidateCovarianceDStarEvent start N (-t) W = candidateCovarianceDStarEvent start N t W := by
  simp only [candidateCovarianceDStarEvent, candidate_eulerDensity_neg]

/-- Every selected strong-prefix condition is unchanged by reflection. -/
theorem candidate_covarianceStrongScreen_neg (start : ℕ) (t W : ℝ) (s : Finset ℕ) :
    candidateCovarianceStrongScreenEvent start (-t) W s =
      candidateCovarianceStrongScreenEvent start t W s := by
  simp only [candidateCovarianceStrongScreenEvent, candidate_eulerDensity_neg]

/-- Literal finite-frequency, D-star and strong-screen restriction for the
remaining squared-density integral. -/
def candidateCovarianceScreenedHeightSet (start N : ℕ) (W H : ℝ)
    (s : Finset ℕ) (ω : Omega) : Set ℝ :=
  {t | |t| ≤ H ∧ ω ∈ candidateCovarianceDStarEvent start N t W ∧
    ω ∈ candidateCovarianceStrongScreenEvent start t W s}

/-- The actual retained frequency set is measurable. -/
theorem candidate_measurableSet_screenedHeightSet (start N : ℕ) (W H : ℝ)
    (s : Finset ℕ) (ω : Omega) :
    MeasurableSet (candidateCovarianceScreenedHeightSet start N W H s ω) := by
  have hd := (candidate_measurableSet_covarianceDStar_joint start N W).preimage
    (measurable_id.prodMk measurable_const : Measurable (fun t : ℝ => (t, ω)))
  have hs := (candidate_measurableSet_covarianceStrongScreen_joint start W s).preimage
    (measurable_id.prodMk measurable_const : Measurable (fun t : ℝ => (t, ω)))
  exact (measurableSet_le measurable_id.abs measurable_const).inter (hd.inter hs)

/-- Reflection preserves the literal screened frequency set. -/
theorem candidate_mem_screenedHeightSet_neg (start N : ℕ) (W H : ℝ)
    (s : Finset ℕ) (ω : Omega) (t : ℝ) :
    -t ∈ candidateCovarianceScreenedHeightSet start N W H s ω ↔
      t ∈ candidateCovarianceScreenedHeightSet start N W H s ω := by
  simp only [candidateCovarianceScreenedHeightSet, mem_setOf_eq, abs_neg,
    candidate_covarianceDStar_neg, candidate_covarianceStrongScreen_neg]

/-- Coordinatewise reflection; `true` reflects the corresponding height. -/
def candidateCovarianceReflect (n : ℕ) (b : Fin n → Bool) : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) where
  toFun x i := if b i then -x i else x i
  invFun x i := if b i then -x i else x i
  left_inv x := by funext i; cases hb : b i <;> simp [hb]
  right_inv x := by funext i; cases hb : b i <;> simp [hb]
  measurable_toFun := measurable_pi_lambda _ fun i => by cases hb : b i <;> simp [hb] <;> fun_prop
  measurable_invFun := measurable_pi_lambda _ fun i => by cases hb : b i <;> simp [hb] <;> fun_prop

/-- The finite reflection has Jacobian of absolute value one. -/
theorem candidate_measurePreserving_covarianceReflect (n : ℕ) (b : Fin n → Bool) :
    MeasurePreserving (candidateCovarianceReflect n b) volume volume := by
  change MeasurePreserving (fun x : Fin n → ℝ => fun i => if b i then -x i else x i)
    (Measure.pi fun _ => volume) (Measure.pi fun _ => volume)
  refine measurePreserving_pi (fun _ : Fin n => volume) (fun _ : Fin n => volume)
    (f := fun i t => if b i then -t else t) ?_
  intro i
  cases hb : b i
  · simpa [hb] using MeasurePreserving.id (volume : Measure ℝ)
  · simpa [hb] using Measure.measurePreserving_neg (volume : Measure ℝ)

/-- Signs after reflecting heights. In particular their sum need not vanish. -/
def candidateCovarianceReflectedSigns {n : ℕ} (ε : Fin n → ℤ) (b : Fin n → Bool) : Fin n → ℤ :=
  fun i => if b i then -ε i else ε i

/-- Reflection preserves the fact that every coefficient is a sign. -/
theorem candidate_covarianceReflectedSigns_unit {n : ℕ} (ε : Fin n → ℤ) (b : Fin n → Bool)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i : Fin n) :
    candidateCovarianceReflectedSigns ε b i = 1 ∨ candidateCovarianceReflectedSigns ε b i = -1 := by
  rcases hε i with h | h <;> cases hb : b i <;> simp [candidateCovarianceReflectedSigns, hb, h]

/-- The signed resonance sum transforms exactly, without balance assumptions. -/
theorem candidate_covariance_signed_sum_reflect {n : ℕ} (ε : Fin n → ℤ)
    (b : Fin n → Bool) (x : Fin n → ℝ) :
    (∑ i, (ε i : ℝ) * candidateCovarianceReflect n b x i) =
      ∑ i, (candidateCovarianceReflectedSigns ε b i : ℝ) * x i := by
  apply Finset.sum_congr rfl
  intro i hi
  cases hb : b i <;> simp [candidateCovarianceReflect, candidateCovarianceReflectedSigns, hb]

/-- A literal signed resonance cell with all actual screens retained. -/
def candidateCovarianceHeightCell {n : ℕ} (start N : ℕ) (W H : ℝ)
    (s : Finset ℕ) (ω : Omega) (ε : Fin n → ℤ) (z δ : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, x i ∈ candidateCovarianceScreenedHeightSet start N W H s ω) ∧
    |(∑ i, (ε i : ℝ) * x i) - z| ≤ δ}

/-- The screened resonance cell is measurable. -/
theorem candidate_measurableSet_covarianceHeightCell {n : ℕ} (start N : ℕ) (W H : ℝ)
    (s : Finset ℕ) (ω : Omega) (ε : Fin n → ℤ) (z δ : ℝ) :
    MeasurableSet (candidateCovarianceHeightCell start N W H s ω ε z δ) := by
  change MeasurableSet ({x : Fin n → ℝ | ∀ i, x i ∈ candidateCovarianceScreenedHeightSet start N W H s ω} ∩
    {x : Fin n → ℝ | |(∑ i, (ε i : ℝ) * x i) - z| ≤ δ})
  apply MeasurableSet.inter
  · rw [setOf_forall]
    exact MeasurableSet.iInter fun i : Fin n =>
      (candidate_measurableSet_screenedHeightSet start N W H s ω).preimage (measurable_pi_apply i)
  · exact measurableSet_le (by fun_prop) measurable_const

/-- Exact pullback of the literal cell under coordinate reflection. -/
theorem candidate_covarianceHeightCell_preimage_reflect {n : ℕ} (start N : ℕ) (W H : ℝ)
    (s : Finset ℕ) (ω : Omega) (ε : Fin n → ℤ) (z δ : ℝ) (b : Fin n → Bool) :
    candidateCovarianceReflect n b ⁻¹' candidateCovarianceHeightCell start N W H s ω ε z δ =
      candidateCovarianceHeightCell start N W H s ω (candidateCovarianceReflectedSigns ε b) z δ := by
  ext x
  change ((∀ i, candidateCovarianceReflect n b x i ∈ _) ∧ _) ↔ _
  rw [candidate_covariance_signed_sum_reflect]
  change ((∀ i, candidateCovarianceReflect n b x i ∈ _) ∧ _) ↔ ((∀ i, x i ∈ _) ∧ _)
  apply and_congr_left'
  apply forall_congr'
  intro i
  cases hb : b i
  · simp [candidateCovarianceReflect, hb]
  · simpa [candidateCovarianceReflect, hb] using candidate_mem_screenedHeightSet_neg start N W H s ω (x i)

/-- Reflection removes every sign from the squared-density amplitude. -/
theorem candidate_covariance_euler_product_reflect (Y : ℕ) (ω : Omega) {n : ℕ}
    (b : Fin n → Bool) (x : Fin n → ℝ) :
    (∏ i, candidateEulerBandSquaredWeight Y ω (candidateCovarianceReflect n b x i)) =
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i) := by
  apply Finset.prod_congr rfl
  intro i hi
  cases hb : b i
  · simp [candidateCovarianceReflect, hb]
  · simpa [candidateCovarianceReflect, hb] using candidate_eulerBandSquaredWeight_neg Y ω (x i)

/-- Actual reflected-cell change of variables. Taking `E` to be the
nonnegative orthant turns each original orthant into positive heights,
with exactly the reflected signs in its resonance sum. -/
theorem candidate_integral_screened_euler_reflect (Y : ℕ) (ω : Omega) {n : ℕ}
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (ε : Fin n → ℤ) (z δ : ℝ)
    (b : Fin n → Bool) {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) :
    (∫ x in candidateCovarianceHeightCell start N W H s ω ε z δ ∩
        candidateCovarianceReflect n b ⁻¹' E,
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i)) =
    ∫ x in candidateCovarianceHeightCell start N W H s ω (candidateCovarianceReflectedSigns ε b) z δ ∩ E,
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i) := by
  let A := candidateCovarianceHeightCell start N W H s ω ε z δ ∩ candidateCovarianceReflect n b ⁻¹' E
  have hA : MeasurableSet A :=
    (candidate_measurableSet_covarianceHeightCell start N W H s ω ε z δ).inter
      (hE.preimage (candidateCovarianceReflect n b).measurable)
  have hp : candidateCovarianceReflect n b ⁻¹' A =
      candidateCovarianceHeightCell start N W H s ω (candidateCovarianceReflectedSigns ε b) z δ ∩ E := by
    dsimp only [A]
    rw [Set.preimage_inter, candidate_covarianceHeightCell_preimage_reflect]
    congr 1
    ext x
    change candidateCovarianceReflect n b (candidateCovarianceReflect n b x) ∈ E ↔ x ∈ E
    have hx : candidateCovarianceReflect n b (candidateCovarianceReflect n b x) = x :=
      (candidateCovarianceReflect n b).left_inv x
    rw [hx]
  have h := (candidate_measurePreserving_covarianceReflect n b).restrict_preimage hA
  have hi := h.integral_comp' (fun x : Fin n → ℝ => ∏ i, candidateEulerBandSquaredWeight Y ω (x i))
  rw [hp] at hi
  simpa only [candidate_covariance_euler_product_reflect] using hi.symm

end
end Erdos.Problem1144
