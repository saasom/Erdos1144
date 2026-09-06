import Erdos.Problem1144.HarperCandidateCovarianceResonanceSliceProduct
import Mathlib.Algebra.BigOperators.Fin

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem1144

/-- Slice at any chosen gap coordinate of the literal finite product box.
The remaining coordinates, including a retained endpoint coordinate, keep
their individual weighted integrals. -/
theorem candidate_integral_coordinate_resonanceSlice_le
    {n : ℕ} (j : Fin (n + 1)) {a ε K : ℝ}
    (ha : a ≠ 0) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (b : (Fin n → ℝ) → ℝ) (hb : Measurable b) (m : ℤ)
    (lower upper : Fin (n + 1) → ℝ) (w : Fin (n + 1) → ℝ → ℝ)
    (hw : Measurable (w j))
    (hwi : ∀ i, IntegrableOn (w i) (Icc (lower i) (upper i)))
    (hwn : ∀ i x, x ∈ Icc (lower i) (upper i) → 0 ≤ w i x)
    (hwb : ∀ x ∈ Icc (lower j) (upper j), w j x ≤ K) :
    (∫ x, {x : Fin (n + 1) → ℝ | |a * x j + b (j.removeNth x) - (m : ℝ)| ≤ ε}.indicator
      (fun x => ∏ i, w i (x i)) x
        ∂Measure.pi (fun i => volume.restrict (Icc (lower i) (upper i)))) ≤
      ((2 * ε / |a|) * K) *
        ∏ i : Fin n, ∫ x in Icc (lower (j.succAbove i)) (upper (j.succAbove i)),
          w (j.succAbove i) x := by
  classical
  let μ : Fin (n + 1) → Measure ℝ := fun i => volume.restrict (Icc (lower i) (upper i))
  let ν : Measure (Fin n → ℝ) := Measure.pi fun i => μ (j.succAbove i)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  let F : (Fin (n + 1) → ℝ) → ℝ :=
    {x | |a * x j + b (j.removeNth x) - (m : ℝ)| ≤ ε}.indicator (fun x => ∏ i, w i (x i))
  have hp : MeasurePreserving e (Measure.pi μ) ((μ j).prod ν) :=
    measurePreserving_piFinSuccAbove μ j
  have heq : (fun z => F (e.symm z)) =
      (candidateAffineResonanceGraph a b m ε).indicator
        (fun z => w j z.1 * ∏ i : Fin n, w (j.succAbove i) (z.2 i)) := by
    funext z
    have hins : e.symm z = j.insertNth z.1 z.2 := rfl
    have hprod : (∏ i, w i (e.symm z i)) =
        w j z.1 * ∏ i : Fin n, w (j.succAbove i) (z.2 i) := by
      rw [Fin.prod_univ_succAbove _ j]
      simp [hins]
    by_cases hz : |a * z.1 + b z.2 - (m : ℝ)| ≤ ε
    · have hleft : e.symm z ∈ {x : Fin (n + 1) → ℝ |
          |a * x j + b (j.removeNth x) - (m : ℝ)| ≤ ε} := by simpa [hins] using hz
      have hright : z ∈ candidateAffineResonanceGraph a b m ε := hz
      change _ = (candidateAffineResonanceGraph a b m ε).indicator _ z
      rw [Set.indicator_of_mem hright]
      exact (Set.indicator_of_mem hleft _).trans hprod
    · have hleft : e.symm z ∉ {x : Fin (n + 1) → ℝ |
          |a * x j + b (j.removeNth x) - (m : ℝ)| ≤ ε} := by simpa [hins] using hz
      have hright : z ∉ candidateAffineResonanceGraph a b m ε := hz
      change _ = (candidateAffineResonanceGraph a b m ε).indicator _ z
      rw [Set.indicator_of_notMem hright]
      exact Set.indicator_of_notMem hleft _
  let V : (Fin n → ℝ) → ℝ := fun z => ∏ i, w (j.succAbove i) (z i)
  have hiV : Integrable V ν := Integrable.fintype_prod (fun i => hwi (j.succAbove i))
  have hnV : ∀ᵐ z ∂ν, 0 ≤ V z := by
    have hall : ∀ᵐ z ∂ν, ∀ i : Fin n,
        z i ∈ Icc (lower (j.succAbove i)) (upper (j.succAbove i)) := by
      apply (ae_all_iff).mpr
      intro i
      exact (Measure.tendsto_eval_ae_ae (μ := fun i : Fin n => μ (j.succAbove i))).eventually
        (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hall] with z hz
    exact Finset.prod_nonneg (fun i _ => hwn (j.succAbove i) (z i) (hz i))
  have h := candidate_integral_product_resonanceSlice_le ν ha hε hK b hb m (w j) hw
    (hwn j) hwb V hiV hnV
  change (∫ x, F x ∂Measure.pi μ) ≤ _
  rw [← hp.symm.integral_comp' F, heq]
  convert h using 1
  unfold V ν
  rw [integral_fintype_prod_eq_prod]

end Erdos.Problem1144
