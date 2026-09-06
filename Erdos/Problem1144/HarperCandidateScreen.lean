import Erdos.Problem1144.HarperCandidateReflection
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# The retained-grid upper-envelope screen

This is the finite-scale argument behind candidate equations (37)--(39).
The old negative-tail budget controls the probability of a sparse good set.
On its complement, reflection turns an absolute fresh crossing into a positive
crossing on a good old coordinate, contradicting an upper envelope.
-/

section Screen

variable {α ι : Type*} [Fintype ι]

/-- Grid coordinates with old contribution at least `-b`. -/
noncomputable def candidateGoodIndices (A : α → ι → ℝ) (b : ℝ) (ω : α) : Finset ι :=
  Finset.univ.filter fun i => -b ≤ A ω i

/-- The old-measurable selector: retain the good coordinates if sufficiently
numerous, and otherwise retain the full grid. -/
noncomputable def candidateRetainedIndices
    (A : α → ι → ℝ) (b ρ : ℝ) (ω : α) : Finset ι :=
  if ρ * Fintype.card ι ≤ (candidateGoodIndices A b ω).card then
    candidateGoodIndices A b ω else Finset.univ

/-- Number of old-negative coordinates, written as a real-valued indicator sum. -/
noncomputable def candidateOldBadCount (A : α → ι → ℝ) (b : ℝ) (ω : α) : ℝ :=
  ∑ i, if A ω i < -b then 1 else 0

@[simp] theorem mem_candidateGoodIndices (A : α → ι → ℝ) (b : ℝ) (ω : α) (i : ι) :
    i ∈ candidateGoodIndices A b ω ↔ -b ≤ A ω i := by
  classical
  simp [candidateGoodIndices]

theorem candidateGoodIndices_card_add_badCount (A : α → ι → ℝ) (b : ℝ) (ω : α) :
    ((candidateGoodIndices A b ω).card : ℝ) + candidateOldBadCount A b ω =
      Fintype.card ι := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : ι => -b ≤ A ω i)
  have hc := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa [candidateGoodIndices, candidateOldBadCount, not_le] using hc

theorem candidateGoodIndices_dense_iff_badCount
    (A : α → ι → ℝ) (b ρ : ℝ) (ω : α) :
    ρ * Fintype.card ι ≤ (candidateGoodIndices A b ω).card ↔
      candidateOldBadCount A b ω ≤ (1 - ρ) * Fintype.card ι := by
  have h := candidateGoodIndices_card_add_badCount A b ω
  constructor <;> intro hd <;> nlinarith

theorem candidateRetainedIndices_card_lower
    (A : α → ι → ℝ) (b ρ : ℝ) (hρ : ρ ≤ 1) (ω : α) :
    ρ * Fintype.card ι ≤ (candidateRetainedIndices A b ρ ω).card := by
  classical
  unfold candidateRetainedIndices
  split_ifs with h
  · exact h
  · simpa using mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg (Fintype.card ι) :
      (0 : ℝ) ≤ Fintype.card ι)

theorem candidateRetainedIndices_invariant
    (A : α → ι → ℝ) (b ρ : ℝ) (τ : α → α)
    (hA : ∀ ω i, A (τ ω) i = A ω i) (ω : α) :
    candidateRetainedIndices A b ρ (τ ω) = candidateRetainedIndices A b ρ ω := by
  classical
  have hg : candidateGoodIndices A b (τ ω) = candidateGoodIndices A b ω := by
    ext i
    simp [hA]
  simp only [candidateRetainedIndices, hg]

variable [MeasurableSpace α]

theorem measurable_candidateOldBadCount
    (A : α → ι → ℝ) (hA : ∀ i, Measurable fun ω => A ω i) (b : ℝ) :
    Measurable (candidateOldBadCount A b) := by
  classical
  unfold candidateOldBadCount
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.ite (measurableSet_lt (hA i) measurable_const) measurable_const

theorem measurableSet_mem_candidateRetainedIndices
    (A : α → ι → ℝ) (hA : ∀ i, Measurable fun ω => A ω i)
    (b ρ : ℝ) (i : ι) :
    MeasurableSet {ω | i ∈ candidateRetainedIndices A b ρ ω} := by
  classical
  have hd : MeasurableSet {ω | ρ * Fintype.card ι ≤
      (candidateGoodIndices A b ω).card} := by
    simp_rw [candidateGoodIndices_dense_iff_badCount]
    exact measurableSet_le (measurable_candidateOldBadCount A hA b) measurable_const
  have hgood : MeasurableSet {ω | -b ≤ A ω i} :=
    measurableSet_le measurable_const (hA i)
  have heq : {ω | i ∈ candidateRetainedIndices A b ρ ω} =
      ({ω | ρ * Fintype.card ι ≤ (candidateGoodIndices A b ω).card} ∩
        {ω | -b ≤ A ω i}) ∪
      {ω | ρ * Fintype.card ι ≤ (candidateGoodIndices A b ω).card}ᶜ := by
    ext ω
    simp only [candidateRetainedIndices, Set.mem_setOf_eq, Set.mem_union,
      Set.mem_inter_iff, Set.mem_compl_iff]
    split_ifs <;> simp_all
  rw [heq]
  exact (hd.inter hgood).union hd.compl

variable {ν : Measure α} [IsFiniteMeasure ν]

theorem integrable_candidateOldBadCount
    (A : α → ι → ℝ) (hA : ∀ i, Measurable fun ω => A ω i) (b : ℝ) :
    Integrable (candidateOldBadCount A b) ν := by
  classical
  unfold candidateOldBadCount
  apply integrable_finset_sum
  intro i _
  simpa only [Set.indicator, Set.mem_setOf_eq] using
    (integrable_const (1 : ℝ)).indicator (measurableSet_lt (hA i) measurable_const)

/-- Expected old-negative count is the sum of the individual tail probabilities. -/
theorem integral_candidateOldBadCount
    (A : α → ι → ℝ) (hA : ∀ i, Measurable fun ω => A ω i) (b : ℝ) :
    (∫ ω, candidateOldBadCount A b ω ∂ν) =
      ∑ i, ν.real {ω | A ω i < -b} := by
  classical
  unfold candidateOldBadCount
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      integral_indicator_one (μ := ν) (measurableSet_lt (hA i) measurable_const)
  · intro i _
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      (integrable_const (1 : ℝ)).indicator (measurableSet_lt (hA i) measurable_const)

/-- Markov's inequality for failure of the retained good-set density. -/
theorem candidate_measureReal_sparse_good_le
    [Nonempty ι] (A : α → ι → ℝ) (hA : ∀ i, Measurable fun ω => A ω i)
    (b ρ B : ℝ) (hρ : ρ < 1)
    (hbudget : (∑ i, ν.real {ω | A ω i < -b}) ≤ B * Fintype.card ι) :
    ν.real {ω | ((candidateGoodIndices A b ω).card : ℝ) < ρ * Fintype.card ι} ≤
      B / (1 - ρ) := by
  classical
  let d : ℝ := (1 - ρ) * Fintype.card ι
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hd : 0 < d := mul_pos (sub_pos.mpr hρ) hn
  have hnonneg : ∀ ω, 0 ≤ candidateOldBadCount A b ω := by
    intro ω
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
  have hint := (integrable_candidateOldBadCount (ν := ν) A hA b).div_const d
  have hmark := hint.measure_le_integral (ae_of_all _ fun ω => div_nonneg (hnonneg ω) hd.le)
    (s := {ω | ((candidateGoodIndices A b ω).card : ℝ) < ρ * Fintype.card ι})
    (by
      intro ω hω
      apply (one_le_div hd).mpr
      have hcard := candidateGoodIndices_card_add_badCount A b ω
      change ((candidateGoodIndices A b ω).card : ℝ) < ρ * Fintype.card ι at hω
      dsimp [d]
      nlinarith)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmark
  rw [ENNReal.toReal_ofReal (integral_nonneg fun ω => div_nonneg (hnonneg ω) hd.le),
    integral_div, integral_candidateOldBadCount A hA b] at hreal
  refine hreal.trans ?_
  calc
    (∑ i, ν.real {ω | A ω i < -b}) / d ≤ (B * Fintype.card ι) / d :=
      div_le_div_of_nonneg_right hbudget hd.le
    _ = B / (1 - ρ) := by dsimp [d]; field_simp

omit [IsFiniteMeasure ν] in
/-- Finite-scale candidate upper-envelope exclusion. The selector, its
reflection invariance, and the Markov loss are all derived here. -/
theorem candidate_measureReal_envelope_le_of_absolute_crossing
    [Nonempty ι] [IsProbabilityMeasure ν]
    (A Z : α → ι → ℝ) (hAmeas : ∀ i, Measurable fun ω => A ω i)
    (τ : α → α) (hτ : MeasurePreserving τ ν ν)
    (hA : ∀ ω i, A (τ ω) i = A ω i)
    (hZ : ∀ ω i, Z (τ ω) i = -Z ω i)
    (M b ρ p B : ℝ) (hρ : ρ < 1)
    (hbudget : (∑ i, ν.real {ω | A ω i < -b}) ≤ B * Fintype.card ι)
    (hcross : p ≤ ν.real {ω | ∃ i ∈ candidateRetainedIndices A b ρ ω,
      M + b < |Z ω i|})
    {E : Set α} (hE : MeasurableSet E)
    (hcap : ∀ ω ∈ E, ∀ i, A ω i + Z ω i ≤ M) :
    ν.real E ≤ 1 - p / 2 + B / (1 - ρ) := by
  classical
  let P : Set α := {ω | ∃ i ∈ candidateRetainedIndices A b ρ ω, M + b < Z ω i}
  let F : Set α :=
    {ω | ((candidateGoodIndices A b ω).card : ℝ) < ρ * Fintype.card ι}
  have hpositive := candidate_measureReal_selected_positive_ge_half_absolute hτ Z
    (fun ω i => i ∈ candidateRetainedIndices A b ρ ω) (M + b)
    (fun ω i => by
      dsimp only
      rw [candidateRetainedIndices_invariant A b ρ τ hA]) hZ
  have hcover : P ⊆ Eᶜ ∪ F := by
    rintro ω ⟨i, hi, hz⟩
    by_cases he : ω ∈ E
    · right
      change ((candidateGoodIndices A b ω).card : ℝ) < ρ * Fintype.card ι
      by_contra hd
      have hd' : ρ * Fintype.card ι ≤ (candidateGoodIndices A b ω).card := le_of_not_gt hd
      have hgood : -b ≤ A ω i := by
        simpa only [candidateRetainedIndices, if_pos hd', mem_candidateGoodIndices] using hi
      have hfull := hcap ω he i
      linarith
    · exact Or.inl he
  have hupper : ν.real P ≤ 1 - ν.real E + B / (1 - ρ) := by
    calc
      ν.real P ≤ ν.real (Eᶜ ∪ F) := measureReal_mono hcover
      _ ≤ ν.real Eᶜ + ν.real F := measureReal_union_le _ _
      _ ≤ (1 - ν.real E) + B / (1 - ρ) := by
        rw [probReal_compl_eq_one_sub hE]
        exact add_le_add_right (candidate_measureReal_sparse_good_le A hAmeas b ρ B hρ hbudget) _
  change _ ≤ ν.real P at hpositive
  linarith

end Screen

/-- The finite-grid screen for the literal complete arithmetic decomposition.
Only the old-negative budget and selected absolute fresh crossing remain
probabilistic inputs. -/
theorem candidate_measureReal_complete_envelope_le_of_absolute_crossing
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {ν : Measure Omega} [IsProbabilityMeasure ν]
    (X : ℕ) (N : ι → ℕ) (hN : ∀ i, N i < X ^ 2)
    (hν : MeasurePreserving (freshSignFlip (candidateGridFreshPrimes X N)) ν ν)
    (M b ρ p B : ℝ) (hρ : ρ < 1)
    (hbudget : (∑ i, ν.real {ω | smoothProcess ω X (N i) < -b}) ≤
      B * Fintype.card ι)
    (hcross : p ≤ ν.real {ω | ∃ i ∈ candidateRetainedIndices
      (fun ω i => smoothProcess ω X (N i)) b ρ ω,
      M + b < |largePrimeProcess ω X (N i)|})
    {E : Set Omega} (hE : MeasurableSet E)
    (hcap : ∀ ω ∈ E, ∀ i, cutoffNormSum ω (N i) ≤ M) :
    ν.real E ≤ 1 - p / 2 + B / (1 - ρ) := by
  apply candidate_measureReal_envelope_le_of_absolute_crossing
    (fun ω i => smoothProcess ω X (N i))
    (fun ω i => largePrimeProcess ω X (N i))
    (fun i => measurable_smoothProcess X (N i))
    (freshSignFlip (candidateGridFreshPrimes X N)) hν
    (fun ω i => smoothProcess_freshSignFlip_eq_of_above _ ω X (N i)
      (candidateGridFreshPrimes_above X N))
    (largePrimeProcess_candidateGridFreshFlip_eq_neg X N hN)
    M b ρ p B hρ hbudget hcross hE
  intro ω hω i
  simpa only [cutoffNormSum_eq_smoothProcess_add_largePrimeProcess ω (hN i)]
    using hcap ω hω i

end Erdos.Problem1144

#print axioms Erdos.Problem1144.candidateRetainedIndices_card_lower
#print axioms Erdos.Problem1144.measurableSet_mem_candidateRetainedIndices
#print axioms Erdos.Problem1144.integral_candidateOldBadCount
#print axioms Erdos.Problem1144.candidate_measureReal_sparse_good_le
#print axioms Erdos.Problem1144.candidate_measureReal_envelope_le_of_absolute_crossing
#print axioms Erdos.Problem1144.candidate_measureReal_complete_envelope_le_of_absolute_crossing
