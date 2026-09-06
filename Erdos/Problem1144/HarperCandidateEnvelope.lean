import Erdos.Problem1144.Targets
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.ConditionalProbability

open MeasureTheory Set Filter
open scoped ENNReal symmDiff BigOperators

namespace Erdos.Problem1144

/-!
# Finite-cylinder concentration for the upper-envelope argument

The stationary candidate uses concentration under a fixed finite assignment,
rather than a stagewise lower conditional probability. This file proves that
probability reduction directly from finite-cylinder approximation.
-/

theorem candidate_measurableCylinders_measureDense
    (ν : Measure Omega) [IsFiniteMeasure ν] :
    ν.MeasureDense (measurableCylinders (fun _ : ℕ => Bool)) := by
  apply Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite ν
  · exact ⟨empty_mem_measurableCylinders _,
      fun _ h => compl_mem_measurableCylinders h,
      fun _ _ hs ht => union_mem_measurableCylinders hs ht⟩
  · exact generateFrom_measurableCylinders.symm

/-- Every positive-measure event has arbitrarily high relative density in a
finite-coordinate cylinder. The approximation tolerance splits the event's
mass in half; it is chosen from the requested density, not fixed in advance. -/
theorem exists_candidate_measurableCylinder_concentration
    (ν : Measure Omega) [IsFiniteMeasure ν] {E : Set Omega}
    (hE : MeasurableSet E) (hpos : 0 < ν.real E)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ C ∈ measurableCylinders (fun _ : ℕ => Bool),
      0 < ν.real C ∧ (1 - δ) * ν.real C < ν.real (C ∩ E) := by
  have heps : 0 < δ * ν.real E / 2 := by positivity
  obtain ⟨C, hC, herr⟩ := (candidate_measurableCylinders_measureDense ν).approx
    E hE (measure_ne_top _ _) (δ * ν.real E / 2) heps
  have herrR : ν.real (E ∆ C) < δ * ν.real E / 2 := by
    exact (ENNReal.toReal_lt_of_lt_ofReal herr)
  have hEC : ν.real E - ν.real C ≤ ν.real (E ∆ C) :=
    (le_measureReal_diff (μ := ν) (s₁ := E) (s₂ := C)).trans
      (measureReal_mono (by intro x hx; exact Or.inl hx))
  have hCE : ν.real (C \ E) ≤ ν.real (E ∆ C) :=
    measureReal_mono (by intro x hx; exact Or.inr hx)
  have hChalf : ν.real E / 2 < ν.real C := by nlinarith
  have hClarge : 0 < ν.real C := by linarith
  have hdiff : ν.real (C \ E) < δ * ν.real C := by nlinarith
  have hsplit := measureReal_inter_add_diff (μ := ν) (s := C) hE
  exact ⟨C, hC, hClarge, by nlinarith⟩

/-- A single finite assignment, including harmless non-prime coordinates. -/
def candidateCylinder (s : Finset ℕ) (η : s → Bool) : Set Omega :=
  cylinder s {η}

theorem measurableSet_candidateCylinder (s : Finset ℕ) (η : s → Bool) :
    MeasurableSet (candidateCylinder s η) :=
  (measurableSet_singleton η).cylinder s

theorem mu_candidateCylinder (s : Finset ℕ) (η : s → Bool) :
    mu (candidateCylinder s η) = (1 / 2 : ℝ≥0∞) ^ s.card := by
  classical
  unfold candidateCylinder mu
  rw [Measure.infinitePi_cylinder _ (measurableSet_singleton η), Measure.pi_singleton]
  have hcoin : ∀ b : Bool, coin {b} = (1 / 2 : ℝ≥0∞) := by
    intro b
    cases b <;> simp [coin]
  simp [hcoin]

theorem mu_candidateCylinder_ne_zero (s : Finset ℕ) (η : s → Bool) :
    mu (candidateCylinder s η) ≠ 0 := by
  rw [mu_candidateCylinder]
  exact pow_ne_zero _ (by norm_num)

noncomputable def candidateCylinderLaw (s : Finset ℕ) (η : s → Bool) : Measure Omega :=
  ProbabilityTheory.cond mu (candidateCylinder s η)

instance candidateCylinderLaw_isProbabilityMeasure (s : Finset ℕ) (η : s → Bool) :
    IsProbabilityMeasure (candidateCylinderLaw s η) :=
  ProbabilityTheory.cond_isProbabilityMeasure (mu_candidateCylinder_ne_zero s η)

theorem candidateCylinderLaw_real (s : Finset ℕ) (η : s → Bool) (E : Set Omega) :
    (candidateCylinderLaw s η).real E =
      mu.real (candidateCylinder s η ∩ E) / mu.real (candidateCylinder s η) := by
  simp only [measureReal_def]
  unfold candidateCylinderLaw
  rw [ProbabilityTheory.cond_apply (measurableSet_candidateCylinder s η),
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring

/-- Cylinder concentration can be attained on one assignment, rather than a
union of assignments. The proof is finite weighted averaging. -/
theorem exists_candidateCylinder_concentration
    (ν : Measure Omega) [IsFiniteMeasure ν] {E : Set Omega}
    (hE : MeasurableSet E) (hpos : 0 < ν.real E)
    {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    ∃ (s : Finset ℕ) (η : s → Bool), 0 < ν.real (candidateCylinder s η) ∧
      (1 - δ) * ν.real (candidateCylinder s η) <
        ν.real (candidateCylinder s η ∩ E) := by
  classical
  obtain ⟨C, hC, _, hconc⟩ :=
    exists_candidate_measurableCylinder_concentration ν hE hpos hδ hδone
  obtain ⟨s, B, hB, rfl⟩ := (mem_measurableCylinders C).mp hC
  have hCmeas : MeasurableSet (cylinder s B : Set Omega) :=
    MeasurableSet.of_mem_measurableCylinders hC
  have hsum (ξ : Measure Omega) [IsFiniteMeasure ξ] :
      (∑ η ∈ B.toFinset, ξ.real (candidateCylinder s η)) =
        ξ.real (cylinder s B) := by
    simpa only [candidateCylinder, cylinder, Set.coe_toFinset] using
      (sum_measureReal_preimage_singleton (μ := ξ) B.toFinset
        (f := s.restrict) (fun η _ => measurableSet_candidateCylinder s η))
  have hsumE : (∑ η ∈ B.toFinset, ν.real (candidateCylinder s η ∩ E)) =
      ν.real (cylinder s B ∩ E) := by
    have h := hsum (ν.restrict E)
    simpa only [measureReal_restrict_apply (measurableSet_candidateCylinder s _),
      measureReal_restrict_apply hCmeas] using h
  obtain ⟨η, hη⟩ : ∃ η : s → Bool,
      (1 - δ) * ν.real (candidateCylinder s η) <
        ν.real (candidateCylinder s η ∩ E) := by
    by_contra! hn
    have h := Finset.sum_le_sum (s := B.toFinset) (fun η _ => hn η)
    rw [← Finset.mul_sum] at h
    rw [hsumE, hsum ν] at h
    linarith
  refine ⟨s, η, ?_, hη⟩
  have hmono : ν.real (candidateCylinder s η ∩ E) ≤
      ν.real (candidateCylinder s η) := measureReal_mono inter_subset_left
  have hnonneg := measureReal_nonneg (μ := ν) (s := candidateCylinder s η)
  by_contra! hn
  have hz : ν.real (candidateCylinder s η) = 0 := le_antisymm hn hnonneg
  simp only [hz, mul_zero] at hη hmono
  linarith

/-- A global upper envelope, with no absolute-value assumption. -/
def candidateUpperEnvelope (M : ℝ) : Set Omega :=
  {omega | ∀ N : ℕ, normSum omega N ≤ M}

theorem measurableSet_candidateUpperEnvelope (M : ℝ) :
    MeasurableSet (candidateUpperEnvelope M) := by
  simpa only [candidateUpperEnvelope, setOf_forall] using
    (MeasurableSet.iInter fun N =>
      measurableSet_le (measurable_normSum N) (measurable_const (a := M)))

/-- Absence of every integer upper envelope gives arbitrarily late positive
excursions. The deterministic square-root bound controls each finite prefix. -/
theorem candidate_positive_frequently_of_no_upperEnvelope (omega : Omega)
    (h : ∀ M : ℕ, omega ∉ candidateUpperEnvelope (M : ℝ)) :
    ∀ A : ℝ, ∃ᶠ N : ℕ in atTop, A ≤ normSum omega N := by
  intro A
  rw [frequently_atTop]
  intro N₀
  obtain ⟨M, hM⟩ := exists_nat_gt (max A (Real.sqrt (N₀ + 1 : ℕ)))
  have hnot := h M
  simp only [candidateUpperEnvelope, mem_setOf_eq, not_forall, not_le] at hnot
  obtain ⟨N, hN⟩ := hnot
  refine ⟨N, ?_, (le_max_left _ _).trans (hM.le.trans hN.le)⟩
  by_contra! hsmall
  have hbound := (le_abs_self (normSum omega N)).trans (abs_normSum_le_sqrt omega N)
  have hsqrt : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ Real.sqrt ((N₀ + 1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.succ_le_succ hsmall.le)
  have := le_max_right A (Real.sqrt (N₀ + 1 : ℕ))
  linarith

/-- A fixed loss of upper-envelope mass in every finite assignment forces
that envelope to be null. No tail-event or independence assertion is used. -/
theorem candidate_upperEnvelope_null_of_cylinder_gap
    (M : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1)
    (hgap : ∀ (s : Finset ℕ) (η : s → Bool),
      mu.real (candidateCylinder s η ∩ candidateUpperEnvelope M) ≤
        (1 - δ) * mu.real (candidateCylinder s η)) :
    mu (candidateUpperEnvelope M) = 0 := by
  apply (measureReal_eq_zero_iff).mp
  apply le_antisymm _ measureReal_nonneg
  by_contra! hpos
  obtain ⟨s, η, _, hconc⟩ := exists_candidateCylinder_concentration mu
    (measurableSet_candidateUpperEnvelope M) hpos hδ hδone
  exact (not_lt_of_ge (hgap s η)) hconc

/-- Faithful final probability endpoint for the stationary candidate. A
uniform cylinder gap may depend on the fixed envelope height; a growing-past
conditional block certificate is not required. -/
theorem erdos1144_of_candidateCylinderEnvelopeGap
    (hgap : ∀ M : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (s : Finset ℕ) (η : s → Bool),
        mu.real (candidateCylinder s η ∩ candidateUpperEnvelope M) ≤
          (1 - δ) * mu.real (candidateCylinder s η)) : Erdos1144 := by
  have hnull : ∀ M : ℕ, mu (candidateUpperEnvelope M) = 0 := by
    intro M
    obtain ⟨δ, hδ, hδone, hbound⟩ := hgap M
    exact candidate_upperEnvelope_null_of_cylinder_gap M hδ hδone hbound
  have hae : ∀ᵐ omega ∂mu, ∀ M : ℕ, omega ∉ candidateUpperEnvelope M :=
    ae_all_iff.mpr (fun M => by simpa only [ae_iff, not_not, setOf_mem_eq] using hnull M)
  exact hae.mono fun omega h => candidate_positive_frequently_of_no_upperEnvelope omega h

/-- Normalized fixed-cylinder version of the final endpoint. -/
theorem erdos1144_of_candidateConditionalEnvelopeGap
    (hgap : ∀ M : ℕ, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (s : Finset ℕ) (η : s → Bool),
        (candidateCylinderLaw s η).real (candidateUpperEnvelope M) ≤ 1 - δ) :
    Erdos1144 := by
  apply erdos1144_of_candidateCylinderEnvelopeGap
  intro M
  obtain ⟨δ, hδ, hδone, hbound⟩ := hgap M
  refine ⟨δ, hδ, hδone, fun s η => ?_⟩
  have h := hbound s η
  rw [candidateCylinderLaw_real] at h
  have hpos : 0 < mu.real (candidateCylinder s η) :=
    ENNReal.toReal_pos (mu_candidateCylinder_ne_zero s η) (measure_ne_top _ _)
  exact (div_le_iff₀ hpos).mp h

end Erdos.Problem1144
