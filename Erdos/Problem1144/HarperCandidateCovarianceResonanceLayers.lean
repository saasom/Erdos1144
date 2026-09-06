import Erdos.Problem1144.HarperCandidateCovarianceRowResonance
import Mathlib.NumberTheory.Harmonic.Bounds

open Finset Set MeasureTheory
open scoped BigOperators Classical

namespace Erdos.Problem1144
noncomputable section

private theorem le_one_add_threshold_count (N : ℕ) (z : ℝ) (hz : z ≤ N) :
    z ≤ 1 + ∑ j ∈ Finset.range N, if ((j + 1 : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0 := by
  induction N with
  | zero =>
    simp only [Nat.cast_zero] at hz
    simpa using (show z ≤ 1 by linarith)
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hsmall : z ≤ (N : ℝ)
    · have hb := ih hsmall
      split_ifs <;> linarith
    · have hNz : (N : ℝ) < z := lt_of_not_ge hsmall
      have hsum : (∑ j ∈ Finset.range N,
          if ((j + 1 : ℕ) : ℝ) ≤ z then (1 : ℝ) else 0) = N := by
        have hterm (j : ℕ) (hj : j ∈ Finset.range N) : ((j + 1 : ℕ) : ℝ) ≤ z := by
          have hjN : j + 1 ≤ N := by simpa only [Finset.mem_range] using hj
          exact (by exact_mod_cast hjN : ((j + 1 : ℕ) : ℝ) ≤ N).trans hNz.le
        simp only [Finset.sum_congr rfl (fun j hj => if_pos (hterm j hj)),
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [hsum]
      push_cast at hz ⊢
      split_ifs <;> linarith

theorem candidateIntegerDistance_le_half (x : ℝ) :
    candidateIntegerDistance x ≤ 1 / 2 := abs_sub_round x

/-- A finite layer bound with exactly the actual row length as its number
of layers. This includes integer frequencies and the empty row. -/
theorem candidate_rowFourierSum_norm_le_resonance_layers (N : ℕ) (x : ℝ) :
    ‖candidateRowFourierSum N (-(2 * Real.pi)) x‖ ≤
      1 + ∑ j ∈ Finset.range N,
        if candidateIntegerDistance x ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ)) then (1 : ℝ) else 0 := by
  let z := ‖candidateRowFourierSum N (-(2 * Real.pi)) x‖
  have hz : z ≤ N := candidate_rowFourierSum_norm_le_card N _ x
  have hcount := le_one_add_threshold_count N z hz
  apply hcount.trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j hj
  by_cases hzj : ((j + 1 : ℕ) : ℝ) ≤ z
  · have hcell : candidateIntegerDistance x ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ)) := by
      by_cases hd : candidateIntegerDistance x = 0
      · rw [hd]
        positivity
      · have hd0 : 0 < candidateIntegerDistance x :=
          lt_of_le_of_ne (candidateIntegerDistance_nonneg x) (Ne.symm hd)
        have hrecip := (candidate_rowFourierSum_norm_le_neg_integerDistance N x hd0).trans
          (min_le_right _ _)
        have hmul := (le_div_iff₀ (by positivity : 0 < 2 * candidateIntegerDistance x)).mp
          (hzj.trans hrecip)
        apply (le_div_iff₀ (by positivity : 0 < 2 * ((j + 1 : ℕ) : ℝ))).mpr
        nlinarith
    simp only [hzj, hcell, if_true]
    exact le_rfl
  · simp only [hzj, if_false]
    split_ifs <;> norm_num

theorem candidate_integrable_mul_rowFourierSum_norm
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ)
    (X : Ω → ℝ) (hX : Measurable X) (f : Ω → ℝ) (hf : Integrable f μ) :
    Integrable (fun ω => f ω * ‖candidateRowFourierSum N (-(2 * Real.pi)) (X ω)‖) μ := by
  have hm : Measurable (fun ω => ‖candidateRowFourierSum N (-(2 * Real.pi)) (X ω)‖) := by
    unfold candidateRowFourierSum candidateCovariancePhase
    fun_prop
  apply hf.mul_bdd (c := (N : ℝ)) hm.aestronglyMeasurable
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs, abs_norm] using
    candidate_rowFourierSum_norm_le_card N (-(2 * Real.pi)) (X ω)

/-- The literal geometric-sum integral is bounded by the sum of its
finite resonance sublevel integrals. No sublevel estimate is assumed here. -/
theorem candidate_integral_rowFourierSum_le_resonance_layers
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ)
    (X : Ω → ℝ) (hX : Measurable X) (f : Ω → ℝ) (hf : Integrable f μ)
    (hf0 : ∀ ω, 0 ≤ f ω) :
    (∫ ω, f ω * ‖candidateRowFourierSum N (-(2 * Real.pi)) (X ω)‖ ∂μ) ≤
      (∫ ω, f ω ∂μ) + ∑ j ∈ Finset.range N,
        ∫ ω in {ω | candidateIntegerDistance (X ω) ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ))},
          f ω ∂μ := by
  let S : ℕ → Set Ω := fun j =>
    {ω | candidateIntegerDistance (X ω) ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ))}
  have hS (j : ℕ) : MeasurableSet (S j) := measurableSet_le
    (candidateIntegerDistance_lipschitz.continuous.measurable.comp hX) measurable_const
  have hI (j : ℕ) : Integrable ((S j).indicator f) μ := hf.indicator (hS j)
  have hp (ω : Ω) :
      f ω * ‖candidateRowFourierSum N (-(2 * Real.pi)) (X ω)‖ ≤
        f ω + ∑ j ∈ Finset.range N, (S j).indicator f ω := by
    have h := mul_le_mul_of_nonneg_left
      (candidate_rowFourierSum_norm_le_resonance_layers N (X ω)) (hf0 ω)
    apply h.trans_eq
    rw [mul_add, mul_one, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hω : ω ∈ S j
    · rw [Set.indicator_of_mem hω]
      have hmem : candidateIntegerDistance (X ω) ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ)) := hω
      rw [if_pos hmem, mul_one]
    · rw [Set.indicator_of_notMem hω]
      have hmem : ¬candidateIntegerDistance (X ω) ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ)) := hω
      rw [if_neg hmem, mul_zero]
  calc
    _ ≤ ∫ ω, f ω + ∑ j ∈ Finset.range N, (S j).indicator f ω ∂μ :=
      integral_mono (candidate_integrable_mul_rowFourierSum_norm μ N X hX f hf)
        (hf.add (integrable_finset_sum _ (fun j _ => hI j))) hp
    _ = _ := by
      rw [integral_add hf (integrable_finset_sum _ (fun j _ => hI j)),
        integral_finset_sum _ (fun j _ => hI j)]
      congr 1
      exact Finset.sum_congr rfl fun j hj => integral_indicator (hS j)

/-- An affine sublevel-mass estimate pays for all layers. The full mass
is supplied by the radius-one-half sublevel, which is the whole space. -/
theorem candidate_integral_rowFourierSum_le_affine_resonance_mass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ)
    (X : Ω → ℝ) (hX : Measurable X) (f : Ω → ℝ) (hf : Integrable f μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (a b : ℝ)
    (hmass : ∀ e : ℝ, 0 ≤ e → e ≤ 1 / 2 →
      (∫ ω in {ω | candidateIntegerDistance (X ω) ≤ e}, f ω ∂μ) ≤ a + b * e) :
    (∫ ω, f ω * ‖candidateRowFourierSum N (-(2 * Real.pi)) (X ω)‖ ∂μ) ≤
      ((N : ℝ) + 1) * a + (b / 2) * (1 + (harmonic N : ℝ)) := by
  have hfull : (∫ ω, f ω ∂μ) ≤ a + b * (1 / 2) := by
    have hu : {ω | candidateIntegerDistance (X ω) ≤ 1 / 2} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact candidateIntegerDistance_le_half (X ω)
    simpa only [hu, Measure.restrict_univ] using hmass (1 / 2) (by norm_num) le_rfl
  have hwidth (j : ℕ) : 0 ≤ 1 / (2 * ((j + 1 : ℕ) : ℝ)) ∧
      1 / (2 * ((j + 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
    constructor
    · positivity
    · apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
      linarith
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun j _ =>
    hmass (1 / (2 * ((j + 1 : ℕ) : ℝ))) (hwidth j).1 (hwidth j).2)
  have heq : a + b * (1 / 2) + (∑ j ∈ Finset.range N,
      (a + b * (1 / (2 * ((j + 1 : ℕ) : ℝ))))) =
      ((N : ℝ) + 1) * a + (b / 2) * (1 + (harmonic N : ℝ)) := by
    have hterm (j : ℕ) : b * (1 / (2 * ((j + 1 : ℕ) : ℝ))) =
        (b / 2) * (((j + 1 : ℕ) : ℝ)⁻¹) := by ring
    simp only [Finset.sum_add_distrib, hterm, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, harmonic,
      Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    ring
  exact (candidate_integral_rowFourierSum_le_resonance_layers μ N X hX f hf hf0).trans
    ((add_le_add hfull hsum).trans_eq heq)

/-- The same genuine sublevel hypotheses give a logarithmic cost in the
row length for the slope term; the intercept retains its necessary `N` factor. -/
theorem candidate_integral_rowFourierSum_le_affine_resonance_mass_log
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ)
    (X : Ω → ℝ) (hX : Measurable X) (f : Ω → ℝ) (hf : Integrable f μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (a b : ℝ) (hb : 0 ≤ b)
    (hmass : ∀ e : ℝ, 0 ≤ e → e ≤ 1 / 2 →
      (∫ ω in {ω | candidateIntegerDistance (X ω) ≤ e}, f ω ∂μ) ≤ a + b * e) :
    (∫ ω, f ω * ‖candidateRowFourierSum N (-(2 * Real.pi)) (X ω)‖ ∂μ) ≤
      ((N : ℝ) + 1) * a + (b / 2) * (2 + Real.log N) := by
  apply (candidate_integral_rowFourierSum_le_affine_resonance_mass
    μ N X hX f hf hf0 a b hmass).trans
  have hh := harmonic_le_one_add_log N
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (show 1 + (harmonic N : ℝ) ≤ 2 + Real.log N by linarith) (by positivity))

end
end Erdos.Problem1144
