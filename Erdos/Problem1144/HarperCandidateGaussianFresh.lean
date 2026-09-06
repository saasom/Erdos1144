import Erdos.Problem1144.HarperCandidateGaussianSmoothing

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem1144

/-- The actual fresh-coefficient replacement, uniformly over every retained
set. The number of fresh signs does not enter the error bound. -/
theorem candidate_selected_fresh_max_rademacher_comparison
    {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (omega : Omega) (u : Fin m → ℝ)
      (q : Fin n → ℕ) (hq : Function.Injective q) (J : Finset (Fin m))
      (T β : ℝ), Real.log 2 ≤ T →
      (∀ p, ⌊Real.exp T⌋₊ < q p) → (∀ i, u i ≤ β * T) →
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
          {v | ∃ i ∈ J, K + δ ≤ |∑ p,
            (S omega (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2)) * v p|} ≤
        (Measure.pi (fun _ : Fin n => candidateRademacherLaw)).real
          {v | ∃ i ∈ J, K < |∑ p,
            (S omega (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2)) * v p|} +
        C * (m : ℝ) ^ 3 * Real.exp ((3 * β / 2 - 2) * T) := by
  classical
  obtain ⟨C, hC, hcomp⟩ := candidate_selected_linear_max_rademacher_comparison hK hδ
  refine ⟨4 * C, by positivity, ?_⟩
  intro n m omega u q hq J T β hT hqT hu
  let P := Finset.univ.image q
  have hP : P ⊆ Finset.Icc (⌊Real.exp T⌋₊ + 1) (Finset.univ.sup q) := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_Icc.mpr ⟨hqT j, Finset.le_sup (f := q) (Finset.mem_univ j)⟩
  let a : Fin n → Fin m → ℝ := fun p i =>
    S omega (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2)
  have hbudget : (∑ p, (∑ i ∈ J, |a p i|) ^ 3) ≤
      4 * (m : ℝ) ^ 3 * Real.exp ((3 * β / 2 - 2) * T) := by
    calc
      _ ≤ ∑ p, (∑ i, |a p i|) ^ 3 := by
        apply Finset.sum_le_sum
        intro p _
        apply pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
          (fun _ _ _ => abs_nonneg _)
      _ = ∑ p ∈ P, (∑ i, |S omega (⌊Real.exp (u i)⌋₊ / p) /
          Real.exp (u i / 2)|) ^ 3 := by
        symm
        apply Finset.sum_image
        exact fun _ _ _ _ h => hq h
      _ ≤ _ := by
        simpa only [Fintype.card_fin] using
          candidate_log_fresh_cubic_coefficient_budget_exp omega u hT P hP hu
  have h := hcomp n m J a
  have he : C * ∑ p, (∑ i ∈ J, |a p i|) ^ 3 ≤
      (4 * C) * (m : ℝ) ^ 3 * Real.exp ((3 * β / 2 - 2) * T) := by
    calc
      _ ≤ C * (4 * (m : ℝ) ^ 3 * Real.exp ((3 * β / 2 - 2) * T)) :=
        mul_le_mul_of_nonneg_left hbudget hC.le
      _ = _ := by ring
  exact h.trans (add_le_add_right he _)

end Erdos.Problem1144
