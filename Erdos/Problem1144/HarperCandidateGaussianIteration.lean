import Erdos.Problem1144.HarperCandidateGaussianReplacement
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem1144

/-- The fair real sign law used for the fresh scalar coordinates. -/
noncomputable def candidateRademacherLaw : Measure ℝ :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac 1 + (1 / 2 : ℝ≥0∞) • Measure.dirac (-1)

instance candidateRademacherLaw_isProbabilityMeasure : IsProbabilityMeasure candidateRademacherLaw where
  measure_univ := by simp [candidateRademacherLaw, ENNReal.inv_two_add_inv_two]

theorem candidate_integral_rademacher (f : ℝ → ℝ) :
    (∫ x, f x ∂candidateRademacherLaw) = (f 1 + f (-1)) / 2 := by
  have hi (x : ℝ) : Integrable f ((1 / 2 : ℝ≥0∞) • Measure.dirac x) :=
    (integrable_dirac (f := f) (by simp)).smul_measure (by norm_num)
  rw [candidateRademacherLaw, integral_add_measure (hi 1) (hi (-1)),
    integral_smul_measure, integral_smul_measure]
  simp
  ring

private def candidatePiSplit {n : ℕ} (i : Fin (n + 1)) :
    (Fin (n + 1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).trans
    MeasurableEquiv.prodComm

private theorem candidate_pi_integral_split {n : ℕ}
    (M : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (M i)]
    (i : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℝ)
    (hF : Measurable F) {D : ℝ} (hD : ∀ x, |F x| ≤ D) :
    (∫ x, F x ∂Measure.pi M) =
      ∫ w, ∫ t, F (i.insertNth t w) ∂M i
        ∂Measure.pi (fun j : Fin n => M (i.succAbove j)) := by
  let e := candidatePiSplit i
  have hp : MeasurePreserving e (Measure.pi M)
      ((Measure.pi fun j : Fin n => M (i.succAbove j)).prod (M i)) :=
    (measurePreserving_piFinSuccAbove M i).trans Measure.measurePreserving_swap
  have hm : Measurable (fun z => F (e.symm z)) := hF.comp e.symm.measurable
  have hi : Integrable (fun z => F (e.symm z))
      ((Measure.pi fun j : Fin n => M (i.succAbove j)).prod (M i)) :=
    Integrable.of_bound hm.aestronglyMeasurable D
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hD (e.symm z))
  calc
    _ = ∫ z, F (e.symm z) ∂((Measure.pi fun j : Fin n => M (i.succAbove j)).prod (M i)) := by
      simpa only [e.symm_apply_apply] using hp.integral_comp' (fun z => F (e.symm z))
    _ = _ := integral_prod _ hi

/-- One coordinate of an actual finite product is replaced using the proved
scalar Taylor estimate, and all other independent coordinates are integrated
out. The only test hypotheses are measurability, boundedness and C³ sections. -/
theorem candidate_pi_coordinate_smooth_replacement {n : ℕ}
    (M : Fin (n + 1) → Measure ℝ) [∀ i, IsProbabilityMeasure (M i)]
    (i : Fin (n + 1)) (hMi : M i = candidateRademacherLaw)
    (F : (Fin (n + 1) → ℝ) → ℝ) (hF : Measurable F) {C D : ℝ}
    (hD : ∀ x, |F x| ≤ D)
    (hC3 : ∀ v, ContDiff ℝ 3 (fun t => F (Function.update v i t)))
    (hC : ∀ v t, |iteratedDeriv 3 (fun s => F (Function.update v i s)) t| ≤ C) :
    |(∫ x, F x ∂Measure.pi M) -
      ∫ x, F x ∂Measure.pi (Function.update M i (gaussianReal 0 1))| ≤
      (C / 6) * (1 + ∫ t : ℝ, |t| ^ 3 ∂gaussianReal 0 1) := by
  classical
  let M' := Function.update M i (gaussianReal 0 1)
  let R : Measure (Fin n → ℝ) := Measure.pi fun j : Fin n => M (i.succAbove j)
  let e := candidatePiSplit i
  haveI : ∀ j, IsProbabilityMeasure (M' j) := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [M', Function.update_self] using
        (inferInstance : IsProbabilityMeasure (gaussianReal 0 1))
    · simpa [M', hj] using (inferInstance : IsProbabilityMeasure (M j))
  have hrest : Measure.pi (fun j : Fin n => M' (i.succAbove j)) = R := by
    congr 1
    funext j
    simp [M', i.succAbove_ne j]
  have hsource := candidate_pi_integral_split M i F hF hD
  have htarget := candidate_pi_integral_split M' i F hF hD
  rw [hrest] at htarget
  simp only [M', Function.update_self] at htarget
  rw [hMi] at hsource
  have hi (ν : Measure ℝ) [IsProbabilityMeasure ν] :
      Integrable (fun z : (Fin n → ℝ) × ℝ => F (e.symm z)) (R.prod ν) :=
    Integrable.of_bound (hF.comp e.symm.measurable).aestronglyMeasurable D
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hD (e.symm z))
  have hiR : Integrable (fun w => ∫ t, F (i.insertNth t w) ∂candidateRademacherLaw) R :=
    (hi candidateRademacherLaw).integral_prod_left
  have hiG : Integrable (fun w => ∫ t, F (i.insertNth t w) ∂gaussianReal 0 1) R :=
    (hi (gaussianReal 0 1)).integral_prod_left
  have hpoint (w : Fin n → ℝ) :
      |(∫ t, F (i.insertNth t w) ∂candidateRademacherLaw) -
        ∫ t, F (i.insertNth t w) ∂gaussianReal 0 1| ≤
      (C / 6) * (1 + ∫ t : ℝ, |t| ^ 3 ∂gaussianReal 0 1) := by
    rw [candidate_integral_rademacher]
    have heq : (fun t => F (Function.update (i.insertNth 0 w) i t)) =
        (fun t => F (i.insertNth t w)) := by simp only [Fin.update_insertNth]
    apply candidate_rademacher_gaussian_smooth_replacement
      (f := fun t => F (i.insertNth t w)) (C := C) (D := D)
    · simpa only [heq] using hC3 (i.insertNth 0 w)
    · intro t
      simpa only [heq] using hC (i.insertNth 0 w) t
    · exact fun t => hD _
  rw [hsource, htarget]
  change |(∫ w, _ ∂R) - ∫ w, _ ∂R| ≤ _
  rw [← integral_sub hiR hiG]
  calc
    _ ≤ ∫ w, |(∫ t, F (i.insertNth t w) ∂candidateRademacherLaw) -
        ∫ t, F (i.insertNth t w) ∂gaussianReal 0 1| ∂R := abs_integral_le_integral_abs
    _ ≤ ∫ _w, (C / 6) * (1 + ∫ t : ℝ, |t| ^ 3 ∂gaussianReal 0 1) ∂R :=
      integral_mono (hiR.sub hiG).abs (integrable_const _) hpoint
    _ = _ := by simp

/-- Full finite-product Lindeberg replacement with the sum of the actual
coordinate third-derivative bounds. No Gaussian comparison or event estimate
is hidden in the hypotheses. -/
theorem candidate_pi_rademacher_gaussian_smooth_replacement {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) (C : Fin n → ℝ) {D : ℝ}
    (hD : ∀ x, |F x| ≤ D)
    (hC3 : ∀ i v, ContDiff ℝ 3 (fun t => F (Function.update v i t)))
    (hC : ∀ i v t, |iteratedDeriv 3 (fun s => F (Function.update v i s)) t| ≤ C i) :
    |(∫ x, F x ∂Measure.pi (fun _ : Fin n => candidateRademacherLaw)) -
      ∫ x, F x ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)| ≤
      ((∑ i, C i) / 6) * (1 + ∫ t : ℝ, |t| ^ 3 ∂gaussianReal 0 1) := by
  classical
  cases n with
  | zero =>
      have hmeas : (fun _ : Fin 0 => candidateRademacherLaw) =
          (fun _ : Fin 0 => gaussianReal 0 1) := funext fun i => Fin.elim0 i
      rw [hmeas]
      simp
  | succ n =>
      let M : ℕ → Fin (n + 1) → Measure ℝ := fun k i =>
        if (i : ℕ) < k then gaussianReal 0 1 else candidateRademacherLaw
      haveI hM (k : ℕ) : ∀ i, IsProbabilityMeasure (M k i) := by
        intro i
        dsimp [M]
        split <;> infer_instance
      let E : ℕ → ℝ := fun k => ∫ x, F x ∂Measure.pi (M k)
      let c : ℕ → ℝ := fun k => if hk : k < n + 1 then C ⟨k, hk⟩ else 0
      have hzero : M 0 = fun _ => candidateRademacherLaw := by funext i; simp [M]
      have hlast : M (n + 1) = fun _ => gaussianReal 0 1 := by
        funext i
        simp [M, i.isLt]
      have hstep (k : ℕ) (hk : k < n + 1) :
          |E k - E (k + 1)| ≤ (c k / 6) *
            (1 + ∫ t : ℝ, |t| ^ 3 ∂gaussianReal 0 1) := by
        let i : Fin (n + 1) := ⟨k, hk⟩
        have hki : M k i = candidateRademacherLaw := by simp [M, i]
        have hupdate : M (k + 1) = Function.update (M k) i (gaussianReal 0 1) := by
          funext j
          by_cases hj : j = i
          · subst j
            simp [M, i]
          · have hjk : (j : ℕ) ≠ k := by
              intro h
              exact hj (Fin.ext h)
            simp [M, hj, show ((j : ℕ) < k + 1) ↔ (j : ℕ) < k by omega]
        have h := candidate_pi_coordinate_smooth_replacement (M k) i hki F hF hD
          (hC3 i) (hC i)
        simpa only [E, hupdate, c, dif_pos hk, i] using h
      have hsum : (∑ k ∈ Finset.range (n + 1), c k) = ∑ i, C i := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [c]
        rw [dif_pos i.isLt]
      rw [← hzero, ← hlast]
      change |E 0 - E (n + 1)| ≤ _
      · rw [← Finset.sum_range_sub' E (n + 1)]
        calc
          _ ≤ ∑ k ∈ Finset.range (n + 1), |E k - E (k + 1)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range (n + 1), (c k / 6) *
              (1 + ∫ t : ℝ, |t| ^ 3 ∂gaussianReal 0 1) := by
            apply Finset.sum_le_sum
            intro k hk
            exact hstep k (Finset.mem_range.mp hk)
          _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_div, hsum]

end Erdos.Problem1144
