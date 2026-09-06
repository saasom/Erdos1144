import Erdos.Problem1144.HarperCandidateCovarianceReflection

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Relabel the remaining scalar heights by a permutation. -/
def candidateCovariancePermute {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) p.symm

/-- Permutations preserve the literal frequency volume. -/
theorem candidate_measurePreserving_covariancePermute {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurePreserving (candidateCovariancePermute p) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) p.symm

/-- Resonance signs are relabelled by the inverse permutation. -/
theorem candidate_covariance_signed_sum_permute {n : ℕ} (ε : Fin n → ℤ)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    (∑ i, (ε i : ℝ) * candidateCovariancePermute p x i) =
      ∑ i, (ε (p.symm i) : ℝ) * x i := by
  simpa [candidateCovariancePermute, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply] using
    Equiv.sum_comp p (fun i => (ε (p.symm i) : ℝ) * x i)

/-- Every literal screen survives arbitrary coordinate relabelling. -/
theorem candidate_covarianceHeightCell_preimage_permute {n : ℕ} (start N : ℕ) (W H : ℝ)
    (s : Finset ℕ) (ω : Omega) (ε : Fin n → ℤ) (z δ : ℝ) (p : Equiv.Perm (Fin n)) :
    candidateCovariancePermute p ⁻¹' candidateCovarianceHeightCell start N W H s ω ε z δ =
      candidateCovarianceHeightCell start N W H s ω (fun i => ε (p.symm i)) z δ := by
  ext x
  change ((∀ i, candidateCovariancePermute p x i ∈ _) ∧ _) ↔ ((∀ i, x i ∈ _) ∧ _)
  rw [candidate_covariance_signed_sum_permute]
  apply and_congr_left'
  constructor
  · intro hx i
    simpa [candidateCovariancePermute, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply] using hx (p.symm i)
  · intro hx i
    simpa [candidateCovariancePermute, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply] using hx (p i)

/-- The squared-Euler amplitude is symmetric in all retained heights. -/
theorem candidate_covariance_euler_product_permute (Y : ℕ) (ω : Omega) {n : ℕ}
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    (∏ i, candidateEulerBandSquaredWeight Y ω (candidateCovariancePermute p x i)) =
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i) := by
  simpa [candidateCovariancePermute, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply] using
    Equiv.prod_comp p (fun i => candidateEulerBandSquaredWeight Y ω (x i))

/-- Actual permutation change of variables on any measurable frequency
region, including an ordered cell. No balance or separation assumption is used. -/
theorem candidate_integral_screened_euler_permute (Y : ℕ) (ω : Omega) {n : ℕ}
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (ε : Fin n → ℤ) (z δ : ℝ)
    (p : Equiv.Perm (Fin n)) {E : Set (Fin n → ℝ)} (hE : MeasurableSet E) :
    (∫ x in candidateCovarianceHeightCell start N W H s ω ε z δ ∩ E,
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i)) =
    ∫ x in candidateCovarianceHeightCell start N W H s ω (fun i => ε (p.symm i)) z δ ∩
        candidateCovariancePermute p ⁻¹' E,
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i) := by
  have hA := (candidate_measurableSet_covarianceHeightCell start N W H s ω ε z δ).inter hE
  have h := (candidate_measurePreserving_covariancePermute p).restrict_preimage hA
  have hi := h.integral_comp' (fun x : Fin n → ℝ => ∏ i, candidateEulerBandSquaredWeight Y ω (x i))
  rw [Set.preimage_inter, candidate_covarianceHeightCell_preimage_permute] at hi
  simpa only [candidate_covariance_euler_product_permute] using hi.symm

/-- Flatten the two original `k`-tuples into the actual `2k` scalar heights. -/
def candidateCovarianceFlatten (k : ℕ) :
    ((Fin k → ℝ) × (Fin k → ℝ)) ≃ᵐ (Fin (k + k) → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin k => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (k + k) => ℝ) finSumFinEquiv)

/-- Flattening preserves the exact restricted product measures from the
partner-contraction endpoint. -/
theorem candidate_measurePreserving_covarianceFlatten (k : ℕ) (μ : Measure ℝ) [SigmaFinite μ] :
    MeasurePreserving (candidateCovarianceFlatten k) (candidateRowPowerMeasure μ k)
      (Measure.pi fun _ : Fin (k + k) => μ) :=
  (measurePreserving_piCongrLeft (fun _ : Fin (k + k) => μ) finSumFinEquiv).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin k ⊕ Fin k => μ))

private theorem flatten_left (k : ℕ) (x : (Fin k → ℝ) × (Fin k → ℝ)) (i : Fin k) :
    candidateCovarianceFlatten k x (Fin.castAdd k i) = x.1 i := by
  simp only [candidateCovarianceFlatten, MeasurableEquiv.trans_apply,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
    finSumFinEquiv_symm_apply_castAdd, eq_rec_constant]
  rfl

private theorem flatten_right (k : ℕ) (x : (Fin k → ℝ) × (Fin k → ℝ)) (i : Fin k) :
    candidateCovarianceFlatten k x (Fin.natAdd k i) = x.2 i := by
  simp only [candidateCovarianceFlatten, MeasurableEquiv.trans_apply,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
    finSumFinEquiv_symm_apply_natAdd, eq_rec_constant]
  rfl

/-- Original row signs before any reflections or permutations. -/
def candidateCovarianceInitialSigns (k : ℕ) : Fin (k + k) → ℤ :=
  Fin.addCases (fun _ : Fin k => 1) (fun _ : Fin k => -1)

/-- The original row coefficients are literal unit signs. -/
theorem candidate_covarianceInitialSigns_unit (k : ℕ) (i : Fin (k + k)) :
    candidateCovarianceInitialSigns k i = 1 ∨ candidateCovarianceInitialSigns k i = -1 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [candidateCovarianceInitialSigns, Fin.addCases_left, Fin.addCases_right, or_true, true_or]

/-- The flattened signed sum is exactly the original row frequency. -/
theorem candidate_covariance_flatten_signed_sum (k : ℕ) (x : (Fin k → ℝ) × (Fin k → ℝ)) :
    (∑ i, (candidateCovarianceInitialSigns k i : ℝ) * candidateCovarianceFlatten k x i) =
      candidateRowPowerFrequency id x := by
  rw [Fin.sum_univ_add]
  simp only [candidateCovarianceInitialSigns, Fin.addCases_left, Fin.addCases_right,
    flatten_left, flatten_right, Int.cast_one, Int.cast_neg, one_mul, neg_one_mul,
    Finset.sum_neg_distrib, candidateRowPowerFrequency, id_eq, sub_eq_add_neg]

/-- Flattening preserves the genuine squared-density amplitude. -/
theorem candidate_covariance_flatten_euler_product (Y : ℕ) (ω : Omega) (k : ℕ)
    (x : (Fin k → ℝ) × (Fin k → ℝ)) :
    (∏ i, candidateEulerBandSquaredWeight Y ω (candidateCovarianceFlatten k x i)) =
      candidateRowProduct (candidateEulerBandSquaredWeight Y ω) x := by
  rw [Fin.prod_univ_add]
  simp only [flatten_left, flatten_right, candidateRowProduct]

/-- The exact `2k`-height contraction output in a single finite-coordinate
integral, ready for reflection and ordered-coordinate changes of variables. -/
theorem candidate_integral_row_squaredDensity_eq_flattened (Y : ℕ) (ω : Omega) (k : ℕ)
    (μ : Measure ℝ) [SigmaFinite μ] (z δ : ℝ) :
    (∫ x in {x | |candidateRowPowerFrequency id x - z| ≤ δ},
      candidateRowProduct (candidateEulerBandSquaredWeight Y ω) x
      ∂candidateRowPowerMeasure μ k) =
    ∫ x in {x | |(∑ i, (candidateCovarianceInitialSigns k i : ℝ) * x i) - z| ≤ δ},
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i) ∂Measure.pi (fun _ : Fin (k + k) => μ) := by
  have hA : MeasurableSet {x : Fin (k + k) → ℝ |
      |(∑ i, (candidateCovarianceInitialSigns k i : ℝ) * x i) - z| ≤ δ} :=
    measurableSet_le (by fun_prop) measurable_const
  have h := (candidate_measurePreserving_covarianceFlatten k μ).restrict_preimage hA
  have hi := h.integral_comp' (fun x : Fin (k + k) → ℝ =>
    ∏ i, candidateEulerBandSquaredWeight Y ω (x i))
  have hp : candidateCovarianceFlatten k ⁻¹'
      {x | |(∑ i, (candidateCovarianceInitialSigns k i : ℝ) * x i) - z| ≤ δ} =
      {x | |candidateRowPowerFrequency id x - z| ≤ δ} := by
    ext x
    simp only [Set.mem_preimage, mem_setOf_eq, candidate_covariance_flatten_signed_sum]
  rw [hp] at hi
  simpa only [candidate_covariance_flatten_euler_product] using hi

/-- The contracted row integral with the literal screens is exactly the
single-coordinate screened cell used by reflection and permutation. -/
theorem candidate_integral_row_screenedSquaredDensity_eq_cell (Y : ℕ) (ω : Omega) (k : ℕ)
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (z δ : ℝ) :
    (∫ x in {x | |candidateRowPowerFrequency id x - z| ≤ δ},
      candidateRowProduct (candidateEulerBandSquaredWeight Y ω) x
      ∂candidateRowPowerMeasure (volume.restrict
        (candidateCovarianceScreenedHeightSet start N W H s ω)) k) =
    ∫ x in candidateCovarianceHeightCell start N W H s ω (candidateCovarianceInitialSigns k) z δ,
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i) := by
  rw [candidate_integral_row_squaredDensity_eq_flattened, ← Measure.restrict_pi_pi]
  have hA : MeasurableSet {x : Fin (k + k) → ℝ |
      |(∑ i, (candidateCovarianceInitialSigns k i : ℝ) * x i) - z| ≤ δ} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.restrict_restrict hA]
  have hset : {x : Fin (k + k) → ℝ | |(∑ i, (candidateCovarianceInitialSigns k i : ℝ) * x i) - z| ≤ δ} ∩
      univ.pi (fun _ => candidateCovarianceScreenedHeightSet start N W H s ω) =
      candidateCovarianceHeightCell start N W H s ω (candidateCovarianceInitialSigns k) z δ := by
    ext x
    simp [candidateCovarianceHeightCell, and_comm]
  rw [hset]
  rfl

end
end Erdos.Problem1144
