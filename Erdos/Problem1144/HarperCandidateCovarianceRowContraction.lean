import Erdos.Problem1144.HarperCandidateCovarianceRowPairing
import Erdos.Problem1144.HarperCandidateCovarianceKernelMass

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Reorder the literal `2k` pairs into the `2k` retained heights and their
`2k` partner heights. No coordinates are discarded by this equivalence. -/
def candidateRowRearrange (k : ℕ) :
    ((Fin k → ℝ × ℝ) × (Fin k → ℝ × ℝ)) ≃ᵐ
      (((Fin k → ℝ) × (Fin k → ℝ)) × ((Fin k → ℝ) × (Fin k → ℝ))) where
  toFun z := ((fun i => (z.1 i).1, fun i => (z.2 i).1),
    (fun i => (z.1 i).2, fun i => (z.2 i).2))
  invFun z := (fun i => (z.1.1 i, z.2.1 i), fun i => (z.1.2 i, z.2.2 i))
  left_inv z := by ext <;> rfl
  right_inv z := by ext <;> rfl
  measurable_toFun := by dsimp; fun_prop
  measurable_invFun := by dsimp; fun_prop

private theorem preserving_interchange {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (σ : Measure D)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] [SigmaFinite σ] :
    MeasurePreserving (fun z : (A × B) × (C × D) => ((z.1.1, z.2.1), (z.1.2, z.2.2)))
      ((μ.prod ν).prod (ρ.prod σ)) ((μ.prod ρ).prod (ν.prod σ)) := by
  have h₁ := measurePreserving_prodAssoc μ ν (ρ.prod σ)
  have h₂ := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν ρ σ).symm
  have h₃ := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := ρ)).prod (MeasurePreserving.id σ))
  have h₄ := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ρ ν σ)
  have h₅ := (measurePreserving_prodAssoc μ ρ (ν.prod σ)).symm
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

/-- The rearrangement preserves the exact finite product measures. -/
theorem candidate_measurePreserving_rowRearrange (μ ν : Measure ℝ)
    [SigmaFinite μ] [SigmaFinite ν] (k : ℕ) :
    MeasurePreserving (candidateRowRearrange k)
      (candidateRowPowerMeasure (μ.prod ν) k)
      ((candidateRowPowerMeasure μ k).prod (candidateRowPowerMeasure ν k)) := by
  have h := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin k) (fun _ => μ) (fun _ => ν)
  exact (preserving_interchange (Measure.pi fun _ : Fin k => μ) (Measure.pi fun _ : Fin k => ν)
    (Measure.pi fun _ : Fin k => μ) (Measure.pi fun _ : Fin k => ν)).comp (h.prod h)

/-- Product restrictions in the row expansion are one literal restriction
of the original finite product measure. -/
theorem candidate_rowPowerMeasure_restrict (ν : Measure (ℝ × ℝ)) [SigmaFinite ν]
    (E : Set (ℝ × ℝ)) (k : ℕ) :
    candidateRowPowerMeasure (ν.restrict E) k =
      (candidateRowPowerMeasure ν k).restrict
        ((univ.pi fun _ : Fin k => E) ×ˢ (univ.pi fun _ : Fin k => E)) := by
  unfold candidateRowPowerMeasure
  rw [← Measure.restrict_pi_pi, Measure.prod_restrict]

private theorem rowProduct_nonneg {X : Type*} {k : ℕ} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (z : (Fin k → X) × (Fin k → X)) : 0 ≤ candidateRowProduct f z :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => hf _) (Finset.prod_nonneg fun _ _ => hf _)

/-- Finite-dimensional Fubini contracts all partner heights simultaneously.
The only kernel inputs are nonnegativity, a bounded measurable kernel, and
its one-coordinate row integral; the actual kernel discharges these below. -/
theorem candidate_integral_row_kernel_contraction (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (k : ℕ)
    {F : ((Fin k → ℝ) × (Fin k → ℝ)) → ℝ}
    (hFm : Measurable F) (hFi : Integrable F (candidateRowPowerMeasure μ k))
    (hF : ∀ x, 0 ≤ F x) {w : ℝ × ℝ → ℝ} (hwm : Measurable w)
    (hw : ∀ z, 0 ≤ w z) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hwC : ∀ z, w z ≤ C) (hrow : ∀ x, (∫ y, w (x, y) ∂ν) ≤ M) :
    Integrable (fun z => F ((candidateRowRearrange k z).1) * candidateRowProduct w z)
      (candidateRowPowerMeasure (μ.prod ν) k) ∧
    (∫ z, F ((candidateRowRearrange k z).1) * candidateRowProduct w z
      ∂candidateRowPowerMeasure (μ.prod ν) k) ≤
      M ^ (2 * k) * ∫ x, F x ∂candidateRowPowerMeasure μ k := by
  letI : IsFiniteMeasure (candidateRowPowerMeasure μ k) := by
    unfold candidateRowPowerMeasure
    infer_instance
  letI : IsFiniteMeasure (candidateRowPowerMeasure ν k) := by
    unfold candidateRowPowerMeasure
    infer_instance
  let G := fun z : (((Fin k → ℝ) × (Fin k → ℝ)) × ((Fin k → ℝ) × (Fin k → ℝ))) =>
    F z.1 * ((∏ i, w (z.1.1 i, z.2.1 i)) * ∏ i, w (z.1.2 i, z.2.2 i))
  have hbound (z : (((Fin k → ℝ) × (Fin k → ℝ)) × ((Fin k → ℝ) × (Fin k → ℝ)))) :
      ‖((∏ i, w (z.1.1 i, z.2.1 i)) * ∏ i, w (z.1.2 i, z.2.2 i))‖ ≤ C ^ (2 * k) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Finset.prod_nonneg fun _ _ => hw _) (Finset.prod_nonneg fun _ _ => hw _))]
    calc
      _ ≤ (∏ _ : Fin k, C) * ∏ _ : Fin k, C := mul_le_mul
        (Finset.prod_le_prod (fun _ _ => hw _) (fun _ _ => hwC _))
        (Finset.prod_le_prod (fun _ _ => hw _) (fun _ _ => hwC _))
        (Finset.prod_nonneg fun _ _ => hw _) (Finset.prod_nonneg fun _ _ => hC)
      _ = _ := by simp [← pow_add]; congr 1; omega
  have hGi : Integrable G ((candidateRowPowerMeasure μ k).prod (candidateRowPowerMeasure ν k)) := by
    have hi := hFi.mul_prod (integrable_const (1 : ℝ) (μ := candidateRowPowerMeasure ν k))
    simp only [mul_one] at hi
    exact hi.mul_bdd (by apply Measurable.aestronglyMeasurable; fun_prop) (ae_of_all _ hbound)
  have hinner (x : (Fin k → ℝ) × (Fin k → ℝ)) :
      (∫ y, ((∏ i, w (x.1 i, y.1 i)) * ∏ i, w (x.2 i, y.2 i))
        ∂candidateRowPowerMeasure ν k) ≤ M ^ (2 * k) := by
    calc
      _ = (∫ y : Fin k → ℝ, ∏ i, w (x.1 i, y i) ∂Measure.pi (fun _ => ν)) *
          (∫ y : Fin k → ℝ, ∏ i, w (x.2 i, y i) ∂Measure.pi (fun _ => ν)) :=
        integral_prod_mul _ _
      _ = (∏ i, ∫ y, w (x.1 i, y) ∂ν) * ∏ i, ∫ y, w (x.2 i, y) ∂ν := by
        exact congrArg₂ (fun a b : ℝ => a * b)
          (integral_fintype_prod_eq_prod (μ := fun _ => ν) (fun i y => w (x.1 i, y)))
          (integral_fintype_prod_eq_prod (μ := fun _ => ν) (fun i y => w (x.2 i, y)))
      _ ≤ (∏ _ : Fin k, M) * ∏ _ : Fin k, M := mul_le_mul
        (Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => hw _) (fun _ _ => hrow _))
        (Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => hw _) (fun _ _ => hrow _))
        (Finset.prod_nonneg fun _ _ => integral_nonneg fun _ => hw _)
        (Finset.prod_nonneg fun _ _ => hM)
      _ = _ := by simp [← pow_add]; congr 1; omega
  refine ⟨?_, ?_⟩
  · exact ((candidate_measurePreserving_rowRearrange μ ν k).integrable_comp_emb
      (candidateRowRearrange k).measurableEmbedding).mpr hGi
  calc
    _ = ∫ z, G z ∂(candidateRowPowerMeasure μ k).prod (candidateRowPowerMeasure ν k) := by
      exact (candidate_measurePreserving_rowRearrange μ ν k).integral_comp' G
    _ = ∫ x, ∫ y, G (x, y) ∂candidateRowPowerMeasure ν k ∂candidateRowPowerMeasure μ k :=
      integral_prod _ hGi
    _ ≤ ∫ x, F x * M ^ (2 * k) ∂candidateRowPowerMeasure μ k := by
      apply integral_mono hGi.integral_prod_left (hFi.mul_const _)
      intro x
      dsimp only [G]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hinner x) (hF x)
    _ = _ := by rw [integral_mul_const]; ring

end
end Erdos.Problem1144
