import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

open MeasureTheory Set Finset
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- Consecutive gaps together with the right endpoint. The last coordinate
is retained, so the map has the same dimension and loses no translation
variable. In dimension zero this is the unique map. -/
def candidateGapCoordinates (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun t i := if h : i.val + 1 < n then t ⟨i.val + 1, h⟩ - t i else t i
  map_add' x y := by
    funext i
    dsimp
    split_ifs <;> ring
  map_smul' c x := by
    funext i
    dsimp
    split_ifs <;> ring

theorem candidateGapCoordinates_apply_gap (n : ℕ) (t : Fin (n + 1) → ℝ) (i : Fin n) :
    candidateGapCoordinates (n + 1) t i.castSucc = t i.succ - t i.castSucc := by
  change (if h : i.val + 1 < n + 1 then t ⟨i.val + 1, h⟩ - t i.castSucc
    else t i.castSucc) = _
  rw [dif_pos (by omega : i.val + 1 < n + 1)]
  rfl

theorem candidateGapCoordinates_apply_last (n : ℕ) (t : Fin (n + 1) → ℝ) :
    candidateGapCoordinates (n + 1) t (Fin.last n) = t (Fin.last n) := by
  simp [candidateGapCoordinates]

private theorem gapCoordinates_abs_det (n : ℕ) :
    |LinearMap.det (candidateGapCoordinates n)| = 1 := by
  let A := LinearMap.toMatrix' (candidateGapCoordinates n)
  have htri : A.BlockTriangular id := by
    intro i j hij
    change j < i at hij
    change candidateGapCoordinates n (Pi.single j 1) i = 0
    dsimp [candidateGapCoordinates]
    split_ifs with h
    · have hji : j ≠ i := ne_of_lt hij
      have hjn : j ≠ (⟨i.val + 1, h⟩ : Fin n) := by
        intro he
        have he' : j.val = i.val + 1 := congrArg Fin.val he
        have hj' : j.val < i.val := hij
        omega
      simp [Ne.symm hji, Ne.symm hjn]
    · simp [ne_of_gt hij]
  have hdiag (i : Fin n) : |A i i| = 1 := by
    change |candidateGapCoordinates n (Pi.single i 1) i| = 1
    dsimp [candidateGapCoordinates]
    split_ifs with h
    · have hne : i ≠ (⟨i.val + 1, h⟩ : Fin n) := by
        intro he
        have he' : i.val = i.val + 1 := congrArg Fin.val he
        omega
      simp [Ne.symm hne]
    · simp
  rw [← LinearMap.det_toMatrix', Matrix.det_of_upperTriangular htri, Finset.abs_prod]
  simp_rw [hdiag]
  simp

private theorem gapCoordinates_continuous (n : ℕ) :
    Continuous (candidateGapCoordinates n) := LinearMap.continuous_on_pi _

private theorem gapCoordinates_det_ne_zero (n : ℕ) :
    LinearMap.det (candidateGapCoordinates n) ≠ 0 := by
  intro h
  have ha := gapCoordinates_abs_det n
  rw [h, abs_zero] at ha
  norm_num at ha

/-- The consecutive-gap transformation preserves the actual finite product
Lebesgue measure. Its triangular determinant has absolute value one. -/
theorem candidate_measurePreserving_gapCoordinates (n : ℕ) :
    MeasurePreserving (candidateGapCoordinates n) volume volume := by
  refine ⟨(gapCoordinates_continuous n).measurable, ?_⟩
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi (gapCoordinates_det_ne_zero n),
    abs_inv, gapCoordinates_abs_det, inv_one, ENNReal.ofReal_one, one_smul]

theorem candidate_measurableEmbedding_gapCoordinates (n : ℕ) :
    MeasurableEmbedding (candidateGapCoordinates n) := by
  apply (gapCoordinates_continuous n).measurableEmbedding
  apply LinearMap.ker_eq_bot.mp
  by_contra h
  exact gapCoordinates_det_ne_zero n (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)

/-- Exact change of variables, including the right endpoint coordinate. -/
theorem candidate_integral_gapCoordinates (n : ℕ) (F : (Fin n → ℝ) → ℝ) :
    (∫ t, F (candidateGapCoordinates n t)) = ∫ g, F g :=
  (candidate_measurePreserving_gapCoordinates n).integral_comp
    (candidate_measurableEmbedding_gapCoordinates n) F

/-- Nonnegative ordered heights in the original window give nonnegative
gaps and a right endpoint in the same window. Dropping the additional sum
constraint therefore only enlarges the gap integration domain. -/
theorem candidateGapCoordinates_mem_box (n : ℕ) {M : ℝ} (t : Fin n → ℝ)
    (ht : Monotone t) (hM : ∀ i, t i ∈ Icc (0 : ℝ) M) :
    candidateGapCoordinates n t ∈ Set.univ.pi (fun _ => Icc (0 : ℝ) M) := by
  intro i _
  dsimp [candidateGapCoordinates]
  split_ifs with h
  · have hij : i ≤ (⟨i.val + 1, h⟩ : Fin n) := by
      apply Fin.le_iff_val_le_val.mpr
      simp
    have hm := ht hij
    have hi := hM i
    have hj := hM ⟨i.val + 1, h⟩
    exact ⟨by linarith, by linarith [hi.1, hj.2]⟩
  · exact hM i

/-- The positive ordered chamber in the actual finite height window. -/
def candidateOrderedHeightBox (n : ℕ) (M : ℝ) : Set (Fin n → ℝ) :=
  {t | Monotone t ∧ ∀ i, t i ∈ Icc (0 : ℝ) M}

theorem candidate_measurableSet_orderedHeightBox (n : ℕ) (M : ℝ) :
    MeasurableSet (candidateOrderedHeightBox n M) := by
  have hm (i j : Fin n) :
      MeasurableSet {t : Fin n → ℝ | i ≤ j → t i ≤ t j} := by
    by_cases h : i ≤ j
    · simpa only [h, true_implies] using
        (measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j))
    · simp [h]
  have hb (i : Fin n) : MeasurableSet {t : Fin n → ℝ | t i ∈ Icc (0 : ℝ) M} :=
    measurableSet_Icc.preimage (measurable_pi_apply i)
  simpa only [candidateOrderedHeightBox, Monotone, setOf_and, setOf_forall] using
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => hm i j).inter
      (MeasurableSet.iInter hb)

/-- A genuine bound for the original ordered integral from an integrable
gap envelope. The proof performs the volume-preserving substitution before
discarding the ordered chamber's additional cumulative-gap constraint. -/
theorem candidate_integral_orderedHeightBox_le_gap_box (n : ℕ) (M : ℝ)
    (f F : (Fin n → ℝ) → ℝ)
    (hfi : IntegrableOn f (candidateOrderedHeightBox n M))
    (hFi : IntegrableOn F (Set.univ.pi (fun _ => Icc (0 : ℝ) M)))
    (hF : ∀ g ∈ Set.univ.pi (fun _ => Icc (0 : ℝ) M), 0 ≤ F g)
    (hbound : ∀ t ∈ candidateOrderedHeightBox n M, f t ≤ F (candidateGapCoordinates n t)) :
    (∫ t in candidateOrderedHeightBox n M, f t) ≤
      ∫ g in Set.univ.pi (fun _ => Icc (0 : ℝ) M), F g := by
  let Q : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Icc (0 : ℝ) M)
  have hD := candidate_measurableSet_orderedHeightBox n M
  have hQ : MeasurableSet Q := MeasurableSet.pi countable_univ fun _ _ => measurableSet_Icc
  have hQi : Integrable (Q.indicator F) := (integrable_indicator_iff hQ).mpr hFi
  have hcomp := (candidate_measurePreserving_gapCoordinates n).integrable_comp_of_integrable hQi
  change (∫ t in candidateOrderedHeightBox n M, f t) ≤ ∫ g in Q, F g
  rw [← integral_indicator hD, ← integral_indicator hQ,
    ← candidate_integral_gapCoordinates n (Q.indicator F)]
  apply integral_mono ((integrable_indicator_iff hD).mpr hfi) hcomp
  intro t
  by_cases ht : t ∈ candidateOrderedHeightBox n M
  · have hg : candidateGapCoordinates n t ∈ Q := candidateGapCoordinates_mem_box n t ht.1 ht.2
    simpa only [Function.comp_apply, indicator_of_mem ht, indicator_of_mem hg] using hbound t ht
  · rw [indicator_of_notMem ht]
    exact indicator_nonneg (fun g hg => hF g hg) _

end
end Erdos.Problem1144
