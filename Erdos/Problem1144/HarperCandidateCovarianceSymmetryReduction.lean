import Erdos.Problem1144.HarperCandidateCovarianceSymmetry
import Mathlib.Data.Fin.Tuple.Sort

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

private theorem density_product_nonneg (Y : ℕ) (ω : Omega) {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ ∏ i, candidateEulerBandSquaredWeight Y ω (x i) := by
  apply Finset.prod_nonneg
  intro i hi
  rw [candidate_eulerBandSquaredWeight_eq_norm_sq]
  positivity

/-- Integrability of the literal squared-density product on its screened
cell, with any further frequency restriction. -/
theorem candidate_integrableOn_screened_euler_product (Y : ℕ) (ω : Omega) {n : ℕ}
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (ε : Fin n → ℤ) (z δ : ℝ) :
    IntegrableOn (fun x : Fin n → ℝ => ∏ i, candidateEulerBandSquaredWeight Y ω (x i))
      (candidateCovarianceHeightCell start N W H s ω ε z δ) := by
  have hi : Integrable (candidateEulerBandSquaredWeight Y ω) (volume.restrict (Icc (-H) H)) := by
    rw [show candidateEulerBandSquaredWeight Y ω = (fun t => ‖candidateEulerAngularApprox Y 0 ω t‖ ^ 2)
      from funext (candidate_eulerBandSquaredWeight_eq_norm_sq Y ω)]
    exact ((candidate_continuous_criticalEulerAngularApprox Y ω).norm.pow 2).integrableOn_Icc
  have hp := Integrable.fintype_prod (fun _ : Fin n => hi)
  rw [← Measure.restrict_pi_pi] at hp
  have hp' : IntegrableOn (fun x : Fin n → ℝ => ∏ i, candidateEulerBandSquaredWeight Y ω (x i))
      (univ.pi fun _ => Icc (-H) H) := hp
  apply hp'.mono_set
  intro x hx i hi
  exact abs_le.mp (hx.1 i).1

private theorem finite_cover_integral_le {X I : Type*} [MeasurableSpace X] [Fintype I]
    {μ : Measure X} {f : X → ℝ} {A : Set X} (hA : MeasurableSet A)
    (hi : IntegrableOn f A μ) (hf : ∀ x, 0 ≤ f x)
    (E : I → Set X) (hE : ∀ i, MeasurableSet (E i)) (hc : ∀ x ∈ A, ∃ i, x ∈ E i) :
    (∫ x in A, f x ∂μ) ≤ ∑ i, ∫ x in A ∩ E i, f x ∂μ := by
  classical
  have hiE (i : I) : Integrable ((A ∩ E i).indicator f) μ :=
    (hi.mono_set inter_subset_left).integrable_indicator (hA.inter (hE i))
  have h := integral_mono_ae (hi.integrable_indicator hA)
    (integrable_finset_sum Finset.univ fun i _ => hiE i) (ae_of_all _ fun x => ?_)
  · rw [integral_indicator hA, integral_finset_sum Finset.univ fun i _ => hiE i] at h
    simpa only [integral_indicator (hA.inter (hE _))] using h
  · by_cases hx : x ∈ A
    · obtain ⟨i, hix⟩ := hc x hx
      rw [indicator_of_mem hx]
      calc
        f x = (A ∩ E i).indicator f x := (indicator_of_mem (show x ∈ A ∩ E i from ⟨hx, hix⟩) f).symm
        _ ≤ ∑ j, (A ∩ E j).indicator f x :=
          Finset.single_le_sum (fun j _ => show 0 ≤ (A ∩ E j).indicator f x from
            indicator_nonneg (fun y _ => hf y) x) (mem_univ i)
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg fun i _ => indicator_nonneg (fun _ _ => hf _) x

/-- Nonnegative heights for reflection into the first orthant. -/
def candidateCovariancePositiveHeights (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, 0 ≤ x i}

/-- Ordered nonnegative heights for the actual mixed-Euler estimate. -/
def candidateCovarianceOrderedPositiveHeights (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ Monotone x}

private theorem measurable_positive (n : ℕ) : MeasurableSet (candidateCovariancePositiveHeights n) := by
  unfold candidateCovariancePositiveHeights
  rw [setOf_forall]
  exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)

private theorem measurable_ordered (n : ℕ) : MeasurableSet (candidateCovarianceOrderedPositiveHeights n) := by
  change MeasurableSet ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x : Fin n → ℝ | Monotone x})
  refine (measurable_positive n).inter ?_
  change MeasurableSet {x : Fin n → ℝ | ∀ i j, i ≤ j → x i ≤ x j}
  simp_rw [setOf_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun hij => measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j)

/-- Cover the actual screened integral by reflected positive orthants.
The sum is over all sign patterns; boundary multiplicity is harmless
because the genuine squared-density integrand is nonnegative. -/
theorem candidate_integral_screened_euler_le_reflected_positive (Y : ℕ) (ω : Omega) {n : ℕ}
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (ε : Fin n → ℤ) (z δ : ℝ) :
    (∫ x in candidateCovarianceHeightCell start N W H s ω ε z δ,
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i)) ≤
    ∑ b : Fin n → Bool,
      ∫ x in candidateCovarianceHeightCell start N W H s ω (candidateCovarianceReflectedSigns ε b) z δ ∩
          candidateCovariancePositiveHeights n,
        ∏ i, candidateEulerBandSquaredWeight Y ω (x i) := by
  classical
  have hc : ∀ x : Fin n → ℝ, ∃ b : Fin n → Bool,
      x ∈ candidateCovarianceReflect n b ⁻¹' candidateCovariancePositiveHeights n := by
    intro x
    refine ⟨fun i => decide (x i < 0), ?_⟩
    intro i
    by_cases hi : x i < 0
    · simpa [candidateCovarianceReflect, hi] using (neg_nonneg.mpr hi.le)
    · simpa [candidateCovarianceReflect, hi] using (le_of_not_gt hi)
  have h := finite_cover_integral_le
    (candidate_measurableSet_covarianceHeightCell start N W H s ω ε z δ)
    (candidate_integrableOn_screened_euler_product Y ω start N W H s ε z δ)
    (density_product_nonneg Y ω)
    (fun b : Fin n → Bool => candidateCovarianceReflect n b ⁻¹' candidateCovariancePositiveHeights n)
    (fun b => (measurable_positive n).preimage (candidateCovarianceReflect n b).measurable)
    (fun x hx => hc x)
  convert h using 1
  apply Finset.sum_congr rfl
  intro b hb
  exact (candidate_integral_screened_euler_reflect Y ω start N W H s ε z δ b (measurable_positive n)).symm

private theorem permute_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    candidateCovariancePermute p x i = x (p i) := by
  simp [candidateCovariancePermute, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

/-- Sorting the positive-height integral only permutes its effective
unit-sign coefficients; their total sum is not constrained. -/
theorem candidate_integral_positive_euler_le_ordered (Y : ℕ) (ω : Omega) {n : ℕ}
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (ε : Fin n → ℤ) (z δ : ℝ) :
    (∫ x in candidateCovarianceHeightCell start N W H s ω ε z δ ∩
        candidateCovariancePositiveHeights n,
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i)) ≤
    ∑ p : Equiv.Perm (Fin n),
      ∫ x in candidateCovarianceHeightCell start N W H s ω (fun i => ε (p i)) z δ ∩
          candidateCovarianceOrderedPositiveHeights n,
        ∏ i, candidateEulerBandSquaredWeight Y ω (x i) := by
  classical
  let O := candidateCovarianceOrderedPositiveHeights n
  have hO : MeasurableSet O := measurable_ordered n
  have hc : ∀ x ∈ candidateCovarianceHeightCell start N W H s ω ε z δ ∩
      candidateCovariancePositiveHeights n, ∃ p : Equiv.Perm (Fin n),
      x ∈ candidateCovariancePermute p ⁻¹' O := by
    intro x hx
    refine ⟨Tuple.sort x, ?_, ?_⟩
    · intro i
      rw [permute_apply]
      exact hx.2 _
    · intro i j hij
      simp only [permute_apply]
      exact Tuple.monotone_sort x hij
  have h := finite_cover_integral_le
    ((candidate_measurableSet_covarianceHeightCell start N W H s ω ε z δ).inter (measurable_positive n))
    ((candidate_integrableOn_screened_euler_product Y ω start N W H s ε z δ).mono_set inter_subset_left)
    (density_product_nonneg Y ω)
    (fun p : Equiv.Perm (Fin n) => candidateCovariancePermute p ⁻¹' O)
    (fun p => hO.preimage (candidateCovariancePermute p).measurable) hc
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro p hp
  have he := candidate_integral_screened_euler_permute Y ω start N W H s ε z δ p.symm
    ((measurable_positive n).inter (hO.preimage (candidateCovariancePermute p).measurable))
  have hpre : candidateCovariancePermute p.symm ⁻¹'
      (candidateCovariancePositiveHeights n ∩ candidateCovariancePermute p ⁻¹' O) = O := by
    ext x
    change ((∀ i, candidateCovariancePermute p.symm x i ≥ 0) ∧
      candidateCovariancePermute p (candidateCovariancePermute p.symm x) ∈ O) ↔ x ∈ O
    have hinv : candidateCovariancePermute p (candidateCovariancePermute p.symm x) = x := by
      funext i
      simp only [permute_apply, Equiv.symm_apply_apply]
    rw [hinv]
    constructor
    · exact fun hx => hx.2
    · intro hx
      refine ⟨?_, hx⟩
      intro i
      rw [permute_apply]
      exact hx.1 _
  rw [hpre] at he
  simpa only [Set.inter_assoc, Equiv.symm_symm] using he

/-- Full deterministic reflection and permutation reduction of the
remaining actual screened squared-Euler-density integral. -/
theorem candidate_integral_screened_euler_le_reflected_ordered (Y : ℕ) (ω : Omega) {n : ℕ}
    (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (ε : Fin n → ℤ) (z δ : ℝ) :
    (∫ x in candidateCovarianceHeightCell start N W H s ω ε z δ,
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i)) ≤
    ∑ b : Fin n → Bool, ∑ p : Equiv.Perm (Fin n),
      ∫ x in candidateCovarianceHeightCell start N W H s ω
          (fun i => candidateCovarianceReflectedSigns ε b (p i)) z δ ∩
          candidateCovarianceOrderedPositiveHeights n,
        ∏ i, candidateEulerBandSquaredWeight Y ω (x i) := by
  apply (candidate_integral_screened_euler_le_reflected_positive Y ω start N W H s ε z δ).trans
  exact Finset.sum_le_sum fun b hb =>
    candidate_integral_positive_euler_le_ordered Y ω start N W H s (candidateCovarianceReflectedSigns ε b) z δ

/-- Every effective coefficient in the reflected and ordered row integral
is a unit sign, even though the total may no longer be zero. -/
theorem candidate_covariance_effectiveRowSigns_unit (k : ℕ) (b : Fin (k + k) → Bool)
    (p : Equiv.Perm (Fin (k + k))) (i : Fin (k + k)) :
    candidateCovarianceReflectedSigns (candidateCovarianceInitialSigns k) b (p i) = 1 ∨
      candidateCovarianceReflectedSigns (candidateCovarianceInitialSigns k) b (p i) = -1 :=
  candidate_covarianceReflectedSigns_unit (candidateCovarianceInitialSigns k) b
    (candidate_covarianceInitialSigns_unit k) (p i)

/-- The explicit finite window in the original contraction measure is
already part of the literal screened frequency set. -/
theorem candidate_restrict_window_screenedHeightSet (start N : ℕ) (W H : ℝ)
    (s : Finset ℕ) (ω : Omega) :
    (volume.restrict (Icc (-H) H)).restrict (candidateCovarianceScreenedHeightSet start N W H s ω) =
      volume.restrict (candidateCovarianceScreenedHeightSet start N W H s ω) := by
  rw [Measure.restrict_restrict (candidate_measurableSet_screenedHeightSet start N W H s ω)]
  congr 1
  exact inter_eq_left.mpr fun t ht => abs_le.mp ht.1

/-- Direct reflection and permutation reduction of the actual `2k`-height
output of partner contraction, with all screens and resonance width intact. -/
theorem candidate_integral_row_screenedSquaredDensity_le_reflected_ordered
    (Y : ℕ) (ω : Omega) (k : ℕ) (start N : ℕ) (W H : ℝ) (s : Finset ℕ) (z δ : ℝ) :
    (∫ x in {x | |candidateRowPowerFrequency id x - z| ≤ δ},
      candidateRowProduct (candidateEulerBandSquaredWeight Y ω) x
      ∂candidateRowPowerMeasure ((volume.restrict (Icc (-H) H)).restrict
        (candidateCovarianceScreenedHeightSet start N W H s ω)) k) ≤
    ∑ b : Fin (k + k) → Bool, ∑ p : Equiv.Perm (Fin (k + k)),
      ∫ x in candidateCovarianceHeightCell start N W H s ω
          (fun i => candidateCovarianceReflectedSigns (candidateCovarianceInitialSigns k) b (p i)) z δ ∩
          candidateCovarianceOrderedPositiveHeights (k + k),
        ∏ i, candidateEulerBandSquaredWeight Y ω (x i) := by
  rw [candidate_restrict_window_screenedHeightSet, candidate_integral_row_screenedSquaredDensity_eq_cell]
  exact candidate_integral_screened_euler_le_reflected_ordered Y ω start N W H s
    (candidateCovarianceInitialSigns k) z δ

end
end Erdos.Problem1144
