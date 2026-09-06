import Erdos.Problem1144.HarperCandidateEnergyFlip
import Erdos.Problem1144.HarperCandidateEnvelope

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem1144

/-- The coordinates on which two assignments to one cylinder disagree. -/
def candidateAssignmentFlip (s : Finset ℕ) (ξ η : s → Bool) : Finset ℕ :=
  s.filter fun p => ∃ hp : p ∈ s, ξ ⟨p, hp⟩ ≠ η ⟨p, hp⟩

theorem candidateAssignmentFlip_subset (s : Finset ℕ) (ξ η : s → Bool) :
    candidateAssignmentFlip s ξ η ⊆ s := Finset.filter_subset _ _

/-- The explicit finite flip sends every source-cylinder world into the
specified target cylinder. -/
theorem candidateAssignmentFlip_mem_cylinder
    (s : Finset ℕ) (ξ η : s → Bool) {ω : Omega}
    (hω : ω ∈ candidateCylinder s ξ) :
    freshSignFlip (candidateAssignmentFlip s ξ η) ω ∈ candidateCylinder s η := by
  change s.restrict ω = ξ at hω
  change s.restrict (freshSignFlip (candidateAssignmentFlip s ξ η) ω) = η
  funext p
  have hp : (p : ℕ) ∈ candidateAssignmentFlip s ξ η ↔ ξ p ≠ η p := by
    simp [candidateAssignmentFlip, p.property]
  have hval : ω p = ξ p := congrFun hω p
  change (if (p : ℕ) ∈ candidateAssignmentFlip s ξ η then !(ω p) else ω p) = η p
  simp only [hp, hval]
  cases hξ : ξ p <;> cases hη : η p <;> simp

/-- Summing over all assignments recovers the original probability mass. -/
theorem candidate_sum_cylinder_inter_measureReal
    (s : Finset ℕ) (E : Set Omega) :
    (∑ ξ : s → Bool, mu.real (candidateCylinder s ξ ∩ E)) = mu.real E := by
  have h := sum_measureReal_preimage_singleton (μ := mu.restrict E)
    (Finset.univ : Finset (s → Bool)) (f := s.restrict)
    (fun ξ _ => measurableSet_candidateCylinder s ξ)
  simp only [Finset.coe_univ, preimage_univ] at h
  change (∑ ξ : s → Bool, (mu.restrict E).real (candidateCylinder s ξ)) =
    (mu.restrict E).real univ at h
  simpa only [measureReal_restrict_apply (measurableSet_candidateCylinder s _),
    measureReal_restrict_apply MeasurableSet.univ, univ_inter] using h

/-- A positive-probability lower bound for the actual prefix energy survives
every fixed cylinder with the same probability. Only the deterministic floor
is reduced, by the explicit finite-coordinate factor `49^|s|`. -/
theorem candidate_squarefree_prefix_energy_cylinder_probability_ge
    (s : Finset ℕ) (η : s → Bool) {y : ℕ} (hy : 1 ≤ y) (A : ℝ) :
    mu.real {ω | A ≤ harperSquarefreeCoefficientPrefixEnergy y ω} ≤
      (candidateCylinderLaw s η).real
        {ω | A / (49 : ℝ) ^ s.card ≤ harperSquarefreeCoefficientPrefixEnergy y ω} := by
  classical
  let E : Set Omega := {ω | A ≤ harperSquarefreeCoefficientPrefixEnergy y ω}
  let F : Set Omega :=
    {ω | A / (49 : ℝ) ^ s.card ≤ harperSquarefreeCoefficientPrefixEnergy y ω}
  have hF : MeasurableSet F :=
    measurableSet_le measurable_const (measurable_harperSquarefreeCoefficientPrefixEnergy y)
  have hmass (ξ : s → Bool) : mu.real (candidateCylinder s ξ ∩ E) ≤
      mu.real (candidateCylinder s η ∩ F) := by
    let d := candidateAssignmentFlip s ξ η
    have hsub : candidateCylinder s ξ ∩ E ⊆
        freshSignFlip d ⁻¹' (candidateCylinder s η ∩ F) := by
      intro ω hω
      refine ⟨candidateAssignmentFlip_mem_cylinder s ξ η hω.1, ?_⟩
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (49 : ℝ) ^ s.card)).mpr
      have henergy := candidate_squarefree_prefix_energy_le_flip d ω hy
      have hcard : d.card ≤ s.card := Finset.card_le_card (candidateAssignmentFlip_subset s ξ η)
      have hpow : (49 : ℝ) ^ d.card ≤ (49 : ℝ) ^ s.card :=
        pow_le_pow_right₀ (by norm_num) hcard
      exact hω.2.trans (henergy.trans (by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hpow
          (harperSquarefreeCoefficientPrefixEnergy_nonneg y (freshSignFlip d ω))))
    apply (measureReal_mono hsub).trans_eq
    simp only [measureReal_def]
    rw [(measurePreserving_freshSignFlip d).measure_preimage
      ((measurableSet_candidateCylinder s η).inter hF).nullMeasurableSet]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (s → Bool)))
    (fun ξ _ => hmass ξ)
  rw [candidate_sum_cylinder_inter_measureReal] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  rw [candidateCylinderLaw_real]
  change mu.real E ≤ mu.real (candidateCylinder s η ∩ F) / mu.real (candidateCylinder s η)
  have hnormalizer : (Fintype.card (s → Bool) : ℝ) =
      (mu.real (candidateCylinder s η))⁻¹ := by
    simp [measureReal_def, mu_candidateCylinder, Fintype.card_pi, Fintype.card_coe]
  rw [hnormalizer] at hsum
  simpa only [div_eq_mul_inv, mul_comm] using hsum

end Erdos.Problem1144
