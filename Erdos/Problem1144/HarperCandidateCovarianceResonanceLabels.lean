import Erdos.Problem1144.HarperCandidateCovarianceRowResonance

open Finset Set MeasureTheory
open scoped BigOperators Classical

namespace Erdos.Problem1144
noncomputable section

/-- Labels for resonance cells meeting the original `n`-coordinate height
window. This range is chosen before any enlargement in gap coordinates. -/
def candidateCovarianceResonanceLabels (n : ℕ) (M e : ℝ) : Finset ℤ :=
  Finset.Icc ⌈-((n : ℝ) * M + e)⌉ ⌊(n : ℝ) * M + e⌋

/-- A signed sum on the original height window has a bound linear in the
number of coordinates. Coefficients of absolute value at most one suffice. -/
theorem candidate_signed_height_sum_abs_le {ι : Type*} [Fintype ι]
    (ε t : ι → ℝ) (M : ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (ht : ∀ i, |t i| ≤ M) :
    |∑ i, ε i * t i| ≤ (Fintype.card ι : ℝ) * M := by
  calc
    _ ≤ ∑ i, |ε i * t i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, M := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hε i) (abs_nonneg _)).trans (by simpa using ht i)
    _ = _ := by simp

/-- A cell which meets the original height window has a bounded integer
label, even if a later change of variables enlarges that window. -/
theorem candidate_resonance_label_abs_le {ι : Type*} [Fintype ι]
    (ε t : ι → ℝ) (M e : ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (ht : ∀ i, |t i| ≤ M) (m : ℤ)
    (hm : |(∑ i, ε i * t i) - (m : ℝ)| ≤ e) :
    |(m : ℝ)| ≤ (Fintype.card ι : ℝ) * M + e := by
  calc
    _ = |(∑ i, ε i * t i) - ((∑ i, ε i * t i) - (m : ℝ))| := by ring_nf
    _ ≤ |∑ i, ε i * t i| + |(∑ i, ε i * t i) - (m : ℝ)| := abs_sub _ _
    _ ≤ _ := add_le_add (candidate_signed_height_sum_abs_le ε t M hε ht) hm

theorem candidate_mem_resonanceLabels_iff (n : ℕ) (M e : ℝ) (m : ℤ) :
    m ∈ candidateCovarianceResonanceLabels n M e ↔
      |(m : ℝ)| ≤ (n : ℝ) * M + e := by
  simp only [candidateCovarianceResonanceLabels, Finset.mem_Icc,
    Int.ceil_le, Int.le_floor, abs_le]

theorem candidate_resonance_label_mem {ι : Type*} [Fintype ι]
    (ε t : ι → ℝ) (M e : ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (ht : ∀ i, |t i| ≤ M) (m : ℤ)
    (hm : |(∑ i, ε i * t i) - (m : ℝ)| ≤ e) :
    m ∈ candidateCovarianceResonanceLabels (Fintype.card ι) M e := by
  rw [candidate_mem_resonanceLabels_iff]
  exact candidate_resonance_label_abs_le ε t M e hε ht m hm

/-- Exact finite-label count. -/
theorem candidate_card_resonanceLabels (n : ℕ) (M e : ℝ)
    (hM : 0 ≤ M) (he : 0 ≤ e) :
    (candidateCovarianceResonanceLabels n M e).card =
      2 * ⌊(n : ℝ) * M + e⌋.toNat + 1 := by
  have hR : 0 ≤ (n : ℝ) * M + e := by positivity
  have hf : 0 ≤ ⌊(n : ℝ) * M + e⌋ := Int.floor_nonneg.mpr hR
  rw [candidateCovarianceResonanceLabels, Int.ceil_neg, Int.card_Icc]
  omega

/-- The total number of possible cells is at most `2(nM+e)+1`, with no
quadratic loss in the number of original heights. -/
theorem candidate_card_resonanceLabels_le (n : ℕ) (M e : ℝ)
    (hM : 0 ≤ M) (he : 0 ≤ e) :
    ((candidateCovarianceResonanceLabels n M e).card : ℝ) ≤
      2 * ((n : ℝ) * M + e) + 1 := by
  have hf : 0 ≤ ⌊(n : ℝ) * M + e⌋ := Int.floor_nonneg.mpr (by positivity)
  have hcast : (⌊(n : ℝ) * M + e⌋.toNat : ℝ) = (⌊(n : ℝ) * M + e⌋ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hf
  rw [candidate_card_resonanceLabels n M e hM he]
  push_cast
  rw [hcast]
  linarith [Int.floor_le ((n : ℝ) * M + e)]

/-- On the original height domain, the near-integer set is an explicitly
finite union of cells. The domain is retained on both sides of the identity. -/
theorem candidate_heightWindow_resonance_eq_finite_union
    {Ω ι : Type*} [Fintype ι] (S : Set Ω) (X : ι → Ω → ℝ)
    (ε : ι → ℝ) (M e : ℝ) (hε : ∀ i, |ε i| ≤ 1)
    (hX : ∀ ω ∈ S, ∀ i, |X i ω| ≤ M) :
    S ∩ {ω | candidateIntegerDistance (∑ i, ε i * X i ω) ≤ e} =
      ⋃ m ∈ candidateCovarianceResonanceLabels (Fintype.card ι) M e,
        S ∩ {ω | |(∑ i, ε i * X i ω) - (m : ℝ)| ≤ e} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hS, hω⟩
    obtain ⟨m, hm⟩ := (candidateIntegerDistance_le_iff _ _).mp hω
    exact ⟨m, candidate_resonance_label_mem ε (fun i => X i ω) M e hε
      (hX ω hS) m hm, hS, hm⟩
  · rintro ⟨m, _, hS, hm⟩
    exact ⟨hS, (candidateIntegerDistance_le_abs_sub_int _ m).trans hm⟩

/-- A nonnegative integral over the actual near-integer set is bounded by
the finite sum of cell integrals, with labels fixed by the original window.
Cells may overlap; no disjointness or small-width assumption is required. -/
theorem candidate_integral_heightWindow_resonance_le_sum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω)
    (S : Set Ω) (hS : MeasurableSet S) (X : ι → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (ε : ι → ℝ) (M e : ℝ)
    (hε : ∀ i, |ε i| ≤ 1) (hX : ∀ ω ∈ S, ∀ i, |X i ω| ≤ M)
    (f : Ω → ℝ) (hf : Integrable f μ) (hf0 : ∀ ω, 0 ≤ f ω) :
    (∫ ω in S ∩ {ω | candidateIntegerDistance (∑ i, ε i * X i ω) ≤ e},
      f ω ∂μ) ≤
      ∑ m ∈ candidateCovarianceResonanceLabels (Fintype.card ι) M e,
        ∫ ω in S ∩ {ω | |(∑ i, ε i * X i ω) - (m : ℝ)| ≤ e}, f ω ∂μ := by
  let A : Ω → ℝ := fun ω => ∑ i, ε i * X i ω
  let E : Set Ω := S ∩ {ω | candidateIntegerDistance (A ω) ≤ e}
  let C : ℤ → Set Ω := fun m => S ∩ {ω | |A ω - (m : ℝ)| ≤ e}
  let L := candidateCovarianceResonanceLabels (Fintype.card ι) M e
  have hAm : Measurable A := by
    apply Finset.measurable_sum
    intro i hi
    exact (hXm i).const_mul (ε i)
  have hEm : MeasurableSet E := hS.inter (measurableSet_le
    (candidateIntegerDistance_lipschitz.continuous.measurable.comp hAm) measurable_const)
  have hCm (m : ℤ) : MeasurableSet (C m) :=
    hS.inter (measurableSet_le (hAm.sub_const _).abs measurable_const)
  have hCi (m : ℤ) : Integrable ((C m).indicator f) μ := hf.indicator (hCm m)
  have hC0 (m : ℤ) (ω : Ω) : 0 ≤ (C m).indicator f ω :=
    Set.indicator_nonneg (fun x _ => hf0 x) ω
  have hpoint (ω : Ω) : E.indicator f ω ≤ ∑ m ∈ L, (C m).indicator f ω := by
    by_cases hω : ω ∈ E
    · obtain ⟨m, hm⟩ := (candidateIntegerDistance_le_iff (A ω) e).mp hω.2
      have hmL : m ∈ L := candidate_resonance_label_mem ε (fun i => X i ω)
        M e hε (hX ω hω.1) m hm
      have hmC : ω ∈ C m := ⟨hω.1, hm⟩
      rw [Set.indicator_of_mem hω]
      calc
        f ω = (C m).indicator f ω := (Set.indicator_of_mem hmC f).symm
        _ ≤ ∑ j ∈ L, (C j).indicator f ω :=
          Finset.single_le_sum (fun j hj => hC0 j ω) hmL
    · rw [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg fun m hm => hC0 m ω
  change (∫ ω in E, f ω ∂μ) ≤ ∑ m ∈ L, ∫ ω in C m, f ω ∂μ
  rw [← integral_indicator hEm]
  calc
    (∫ ω, E.indicator f ω ∂μ) ≤ ∫ ω, ∑ m ∈ L, (C m).indicator f ω ∂μ :=
      integral_mono (hf.indicator hEm) (integrable_finset_sum L (fun m _ => hCi m)) hpoint
    _ = ∑ m ∈ L, ∫ ω, (C m).indicator f ω ∂μ :=
      integral_finset_sum L (fun m _ => hCi m)
    _ = _ := Finset.sum_congr rfl fun m hm => integral_indicator (hCm m)

end
end Erdos.Problem1144
