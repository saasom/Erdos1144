import Erdos.Problem1144.HarperFreshCoefficientScreen

open MeasureTheory
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Reflection for the stationary-field candidate

The two reflection steps in equations (31) and (36) are finite-measure
statements. A common measure-preserving map fixes the old data and negates
every fresh coordinate. It therefore works after restricting the law to any
measurable invariant cylinder. No independence or analytic estimate is hidden
in the statements below.
-/

section FiniteMeasure

variable {α ι : Type*} [MeasurableSpace α]
variable {ν : Measure α}

/-- A measure-preserving map also preserves the restriction to a measurable
invariant event. This is the form needed for a fixed finite-prefix cylinder. -/
theorem candidate_measurePreserving_restrict_of_invariant
    {τ : α → α} (hτ : MeasurePreserving τ ν ν)
    {C : Set α} (hC : MeasurableSet C) (hCI : τ ⁻¹' C = C) :
    MeasurePreserving τ (ν.restrict C) (ν.restrict C) := by
  simpa only [hCI] using hτ.restrict_preimage hC

variable [IsFiniteMeasure ν]

/-- A two-point covering by an event and its reflected preimage loses at most
a factor of two. Measurability of the covered events is unnecessary. -/
theorem candidate_measureReal_le_two_of_reflection_cover
    {τ : α → α} (hτ : MeasurePreserving τ ν ν)
    {E P : Set α} (hcover : E ⊆ P ∪ τ ⁻¹' P) :
    ν.real E ≤ 2 * ν.real P := by
  have hpre : ν.real (τ ⁻¹' P) ≤ ν.real P :=
    ENNReal.toReal_mono (measure_ne_top ν P) (hτ.measure_preimage_le P)
  calc
    ν.real E ≤ ν.real (P ∪ τ ⁻¹' P) := measureReal_mono hcover
    _ ≤ ν.real P + ν.real (τ ⁻¹' P) := measureReal_union_le _ _
    _ ≤ 2 * ν.real P := by linarith

/-- Candidate equation (36): an old negative tail is at most twice the
corresponding negative tail of the full old-plus-fresh sum. -/
theorem candidate_measureReal_old_negative_le_twice_full
    {τ : α → α} (hτ : MeasurePreserving τ ν ν)
    (A Z : α → ℝ) (b : ℝ)
    (hA : ∀ ω, A (τ ω) = A ω)
    (hZ : ∀ ω, Z (τ ω) = -Z ω) :
    ν.real {ω | A ω < -b} ≤ 2 * ν.real {ω | A ω + Z ω < -b} := by
  apply candidate_measureReal_le_two_of_reflection_cover hτ
  intro ω hω
  change A ω < -b at hω
  by_cases hz : Z ω ≤ 0
  · exact Or.inl (by change A ω + Z ω < -b; linarith)
  · right
    change A (τ ω) + Z (τ ω) < -b
    rw [hA, hZ]
    linarith

/-- Candidate equation (31), before taking limits: on a randomly retained
index set fixed by reflection, a positive fresh maximum has at least half
the measure of the absolute fresh maximum. The result holds for any index
type; a finite grid is a direct specialization. -/
theorem candidate_measureReal_selected_positive_ge_half_absolute
    {τ : α → α} (hτ : MeasurePreserving τ ν ν)
    (Z : α → ι → ℝ) (R : α → ι → Prop) (K : ℝ)
    (hR : ∀ ω i, R (τ ω) i ↔ R ω i)
    (hZ : ∀ ω i, Z (τ ω) i = -Z ω i) :
    ν.real {ω | ∃ i, R ω i ∧ K < |Z ω i|} / 2 ≤
      ν.real {ω | ∃ i, R ω i ∧ K < Z ω i} := by
  have htwice :
      ν.real {ω | ∃ i, R ω i ∧ K < |Z ω i|} ≤
        2 * ν.real {ω | ∃ i, R ω i ∧ K < Z ω i} := by
    apply candidate_measureReal_le_two_of_reflection_cover hτ
    rintro ω ⟨i, hi, hzi⟩
    rcases lt_abs.mp hzi with hp | hn
    · exact Or.inl ⟨i, hi, hp⟩
    · right
      refine ⟨i, (hR ω i).mpr hi, ?_⟩
      rw [hZ]
      linarith
  linarith

end FiniteMeasure

/-- A common fresh flip fixes the complete smooth contribution, regardless
of the endpoint. -/
theorem smoothProcess_freshSignFlip_eq_of_above
    (s : Finset ℕ) (ω : Omega) (X N : ℕ)
    (hs : ∀ p ∈ s, X < p) :
    smoothProcess (freshSignFlip s ω) X N = smoothProcess ω X N := by
  unfold smoothProcess
  rw [smoothSum_freshSignFlip_eq_of_above s ω X N hs]

/-- Flipping any common set containing all endpoint-visible fresh primes
negates the complete large-prime process in the exact linear range. -/
theorem largePrimeProcess_freshSignFlip_superset_eq_neg
    (s : Finset ℕ) (ω : Omega) {X N : ℕ}
    (hN : N < X ^ 2) (hs : ∀ p ∈ s, X < p)
    (hcover : largePrimeInterval X N ⊆ s) :
    largePrimeProcess (freshSignFlip s ω) X N = -largePrimeProcess ω X N := by
  classical
  rw [largePrimeProcess_eq_sum_coeff, largePrimeProcess_eq_sum_coeff, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [eps_freshSignFlip_of_mem s ω (hcover hp),
    largePrimeCoeff_freshSignFlip_eq_of_above s ω
      (by simpa [pow_two] using hN) hp hs]
  ring

/-- One finite fresh-prime set for all endpoints in a finite grid. -/
noncomputable def candidateGridFreshPrimes
    {ι : Type*} [Fintype ι] (X : ℕ) (N : ι → ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun i => largePrimeInterval X (N i)

theorem candidateGridFreshPrimes_above {ι : Type*} [Fintype ι]
    (X : ℕ) (N : ι → ℕ) :
    ∀ p ∈ candidateGridFreshPrimes X N, X < p := by
  classical
  intro p hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  exact (mem_largePrimeInterval.mp hi).2.1

theorem largePrimeInterval_subset_candidateGridFreshPrimes
    {ι : Type*} [Fintype ι] (X : ℕ) (N : ι → ℕ) (i : ι) :
    largePrimeInterval X (N i) ⊆ candidateGridFreshPrimes X N := by
  classical
  intro p hp
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩

/-- Simultaneous complete-process reflection across the whole finite grid. -/
theorem largePrimeProcess_candidateGridFreshFlip_eq_neg
    {ι : Type*} [Fintype ι] (X : ℕ) (N : ι → ℕ)
    (hN : ∀ i, N i < X ^ 2) (ω : Omega) (i : ι) :
    largePrimeProcess (freshSignFlip (candidateGridFreshPrimes X N) ω) X (N i) =
      -largePrimeProcess ω X (N i) :=
  largePrimeProcess_freshSignFlip_superset_eq_neg _ ω (hN i)
    (candidateGridFreshPrimes_above X N)
    (largePrimeInterval_subset_candidateGridFreshPrimes X N i)

/-- Complete-model equation (36) for any finite law preserved by the common
fresh flip, including restrictions to invariant finite-prefix cylinders. -/
theorem candidate_measureReal_smooth_negative_le_twice_cutoff
    {ν : Measure Omega} [IsFiniteMeasure ν]
    (s : Finset ℕ) (hν : MeasurePreserving (freshSignFlip s) ν ν)
    {X N : ℕ} (hN : N < X ^ 2)
    (hs : ∀ p ∈ s, X < p) (hcover : largePrimeInterval X N ⊆ s) (b : ℝ) :
    ν.real {ω | smoothProcess ω X N < -b} ≤
      2 * ν.real {ω | cutoffNormSum ω N < -b} := by
  have h := candidate_measureReal_old_negative_le_twice_full hν
    (fun ω => smoothProcess ω X N) (fun ω => largePrimeProcess ω X N) b
    (fun ω => smoothProcess_freshSignFlip_eq_of_above s ω X N hs)
    (fun ω => largePrimeProcess_freshSignFlip_superset_eq_neg s ω hN hs hcover)
  simpa only [cutoffNormSum_eq_smoothProcess_add_largePrimeProcess _ hN] using h

/-- Complete-model equation (31) on a finite grid and an old-invariant random
retained subset. The law may already be restricted to a fixed cylinder. -/
theorem candidate_measureReal_largePrime_selected_positive_ge_half_absolute
    {ι : Type*} [Fintype ι] {ν : Measure Omega} [IsFiniteMeasure ν]
    (X : ℕ) (N : ι → ℕ) (hN : ∀ i, N i < X ^ 2)
    (hν : MeasurePreserving (freshSignFlip (candidateGridFreshPrimes X N)) ν ν)
    (R : Omega → ι → Prop) (K : ℝ)
    (hR : ∀ ω i, R (freshSignFlip (candidateGridFreshPrimes X N) ω) i ↔ R ω i) :
    ν.real {ω | ∃ i, R ω i ∧ K < |largePrimeProcess ω X (N i)|} / 2 ≤
      ν.real {ω | ∃ i, R ω i ∧ K < largePrimeProcess ω X (N i)} :=
  candidate_measureReal_selected_positive_ge_half_absolute hν
    (fun ω i => largePrimeProcess ω X (N i)) R K hR
    (largePrimeProcess_candidateGridFreshFlip_eq_neg X N hN)

end Erdos.Problem1144

#print axioms Erdos.Problem1144.candidate_measurePreserving_restrict_of_invariant
#print axioms Erdos.Problem1144.candidate_measureReal_old_negative_le_twice_full
#print axioms Erdos.Problem1144.candidate_measureReal_selected_positive_ge_half_absolute
#print axioms Erdos.Problem1144.largePrimeProcess_candidateGridFreshFlip_eq_neg
#print axioms Erdos.Problem1144.candidate_measureReal_smooth_negative_le_twice_cutoff
#print axioms Erdos.Problem1144.candidate_measureReal_largePrime_selected_positive_ge_half_absolute
