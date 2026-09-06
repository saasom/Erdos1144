import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set

namespace Erdos.Problem1144

/-!
# The candidate's averaged negative-tail argument

A nonnegative weighted integral and an upper envelope bound the weighted
negative part.  Fubini then turns this pathwise bound on a high-probability
event into an averaged negative-tail estimate.  The ambient time measure may
be infinite; only the observation window has finite measure.
-/

theorem candidate_integrable_weighted_negativePart
    {τ : Type*} [MeasurableSpace τ] {μ : Measure τ}
    {a w : τ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hwa : Integrable (fun t ↦ w t * a t) μ) :
    Integrable (fun t ↦ w t * max (-a t) 0) μ := by
  convert hwa.neg.real_toNNReal using 1
  ext t
  simp only [Real.coe_toNNReal', Pi.neg_apply]
  by_cases ha : 0 ≤ a t
  · rw [max_eq_right (neg_nonpos.mpr ha), mul_zero,
      max_eq_right (neg_nonpos.mpr (mul_nonneg (hw t) ha))]
  · rw [max_eq_left (by linarith : 0 ≤ -a t),
      max_eq_left (by nlinarith [hw t] : 0 ≤ -(w t * a t))]
    ring

/-- A positive weighted transform and an upper envelope bound the weighted
negative part by the upper envelope times the total weight. -/
theorem candidate_weighted_negativePart_le
    {τ : Type*} [MeasurableSpace τ] {μ : Measure τ}
    {a w : τ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ t, 0 ≤ w t) (hwi : Integrable w μ)
    (hwa : Integrable (fun t ↦ w t * a t) μ)
    (ha : ∀ᵐ t ∂μ, a t ≤ M)
    (htransform : 0 ≤ ∫ t, w t * a t ∂μ) :
    (∫ t, w t * max (-a t) 0 ∂μ) ≤ M * ∫ t, w t ∂μ := by
  have hn := candidate_integrable_weighted_negativePart hw hwa
  have hp := hwa.real_toNNReal
  have hdecomp := integral_eq_integral_pos_part_sub_integral_neg_part hwa
  have hneg : (∫ t, (Real.toNNReal (-(w t * a t)) : ℝ) ∂μ) =
      ∫ t, w t * max (-a t) 0 ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [Real.coe_toNNReal']
    by_cases ha : 0 ≤ a t
    · rw [max_eq_right (neg_nonpos.mpr (mul_nonneg (hw t) ha)),
        max_eq_right (neg_nonpos.mpr ha), mul_zero]
    · rw [max_eq_left (by nlinarith [hw t] : 0 ≤ -(w t * a t)),
        max_eq_left (by linarith : 0 ≤ -a t)]
      ring
  have hpos : (∫ t, (Real.toNNReal (w t * a t) : ℝ) ∂μ) ≤
      M * ∫ t, w t ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono_ae hp (hwi.const_mul M) ?_
    filter_upwards [ha] with t ht
    simp only [Real.coe_toNNReal']
    exact max_le (by nlinarith [hw t]) (mul_nonneg hM (hw t))
  rw [hneg] at hdecomp
  linarith

/-- The weighted negative-part budget controls time spent below `-b` in any
finite window on which the weight is at least `c > 0`. -/
theorem candidate_negativeTail_measure_le_of_weighted_budget
    {τ : Type*} [MeasurableSpace τ] {μ ν : Measure τ} [IsFiniteMeasure ν]
    {a w : τ → ℝ} {b c B : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hw : ∀ t, 0 ≤ w t)
    (hwa : Integrable (fun t ↦ w t * a t) μ)
    (hν : ν ≤ μ) (hwindow : ∀ᵐ t ∂ν, c ≤ w t)
    (hbudget : (∫ t, w t * max (-a t) 0 ∂μ) ≤ B) :
    ν.real {t | a t < -b} ≤ B / (b * c) := by
  have hneg := candidate_integrable_weighted_negativePart hw hwa
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := ν)
    (f := fun t ↦ w t * max (-a t) 0)
    (ae_of_all _ fun t ↦ mul_nonneg (hw t) (le_max_right _ _))
    (hneg.mono_measure hν) (b * c)
  have hsub : ∀ᵐ t ∂ν, t ∈ {t | a t < -b} →
      t ∈ {t | b * c ≤ w t * max (-a t) 0} := by
    filter_upwards [hwindow] with t hwt ht
    change a t < -b at ht
    have hm : b ≤ max (-a t) 0 := le_trans (by linarith) (le_max_left _ _)
    calc
      b * c ≤ max (-a t) 0 * w t := mul_le_mul hm hwt hc.le
        (le_max_right _ _)
      _ = w t * max (-a t) 0 := mul_comm _ _
  have hint : (∫ t, w t * max (-a t) 0 ∂ν) ≤ B :=
    (integral_mono_measure hν
      (ae_of_all _ fun t ↦ mul_nonneg (hw t) (le_max_right _ _)) hneg).trans hbudget
  apply (le_div_iff₀ (mul_pos hb hc)).mpr
  calc
    ν.real {t | a t < -b} * (b * c) ≤
        (b * c) * ν.real {t | b * c ≤ w t * max (-a t) 0} := by
      have hm : ν.real {t | a t < -b} ≤
          ν.real {t | b * c ≤ w t * max (-a t) 0} :=
        ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono_ae hsub)
      nlinarith [mul_pos hb hc]
    _ ≤ B := hmarkov.trans hint

private theorem candidate_integral_tail_indicator
    {τ : Type*} [MeasurableSpace τ] {ν : Measure τ}
    {a : τ → ℝ} {b : ℝ} (ha : Measurable a) :
    (∫ t, (if a t < -b then (1 : ℝ) else 0) ∂ν) =
      ν.real {t | a t < -b} := by
  simpa only [Set.indicator, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
    (integral_indicator_const (μ := ν) (1 : ℝ)
      (measurableSet_lt ha measurable_const))

/-- Fubini identifies the average pointwise negative-tail probability with
the expected time spent below the threshold. -/
theorem candidate_integral_negativeTail_eq_occupation
    {Ω τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {Q : Measure Ω} {ν : Measure τ} [IsFiniteMeasure Q] [IsFiniteMeasure ν]
    {a : Ω × τ → ℝ} {b : ℝ} (ha : Measurable a) :
    (∫ t, Q.real {ω | a (ω, t) < -b} ∂ν) =
      ∫ ω, ν.real {t | a (ω, t) < -b} ∂Q := by
  have hi : Integrable (fun z : Ω × τ ↦ if a z < -b then (1 : ℝ) else 0)
      (Q.prod ν) := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      (integrable_const (1 : ℝ)).indicator (measurableSet_lt ha measurable_const)
  have hf := integral_integral_swap (f := fun ω t ↦
    if a (ω, t) < -b then (1 : ℝ) else 0) hi
  have hl : ∀ ω, (∫ t, (if a (ω, t) < -b then (1 : ℝ) else 0) ∂ν) =
      ν.real {t | a (ω, t) < -b} := fun ω ↦
    candidate_integral_tail_indicator (ha.comp measurable_prodMk_left)
  have hr : ∀ t, (∫ ω, (if a (ω, t) < -b then (1 : ℝ) else 0) ∂Q) =
      Q.real {ω | a (ω, t) < -b} := fun t ↦
    candidate_integral_tail_indicator (ha.comp measurable_prodMk_right)
  simp_rw [hl, hr] at hf
  exact hf.symm

theorem candidate_integrable_negativeTail_occupation
    {Ω τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {Q : Measure Ω} {ν : Measure τ} [IsFiniteMeasure Q] [IsFiniteMeasure ν]
    {a : Ω × τ → ℝ} {b : ℝ} (ha : Measurable a) :
    Integrable (fun ω ↦ ν.real {t | a (ω, t) < -b}) Q := by
  have hi : Integrable (fun z : Ω × τ ↦ if a z < -b then (1 : ℝ) else 0)
      (Q.prod ν) := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      (integrable_const (1 : ℝ)).indicator (measurableSet_lt ha measurable_const)
  have hl : ∀ ω, (∫ t, (if a (ω, t) < -b then (1 : ℝ) else 0) ∂ν) =
      ν.real {t | a (ω, t) < -b} := fun ω ↦
    candidate_integral_tail_indicator (ha.comp measurable_prodMk_left)
  have h := hi.integral_prod_left
  simp_rw [hl] at h
  exact h

/-- On a finite observation window the pointwise tail probabilities are
integrable, independently of any moment assumptions on the process. -/
theorem candidate_integrable_negativeTail_probability
    {Ω τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {Q : Measure Ω} {ν : Measure τ} [IsFiniteMeasure Q] [IsFiniteMeasure ν]
    {a : Ω × τ → ℝ} {b : ℝ} (ha : Measurable a) :
    Integrable (fun t ↦ Q.real {ω | a (ω, t) < -b}) ν := by
  have hi : Integrable (fun z : Ω × τ ↦ if a z < -b then (1 : ℝ) else 0)
      (Q.prod ν) := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using
      (integrable_const (1 : ℝ)).indicator (measurableSet_lt ha measurable_const)
  have hr : ∀ t, (∫ ω, (if a (ω, t) < -b then (1 : ℝ) else 0) ∂Q) =
      Q.real {ω | a (ω, t) < -b} := fun t ↦
    candidate_integral_tail_indicator (ha.comp measurable_prodMk_right)
  have h := hi.integral_prod_right
  simp_rw [hr] at h
  exact h

/-- An almost-everywhere occupation bound on `E` gives an averaged probability
bound. Null exceptional worlds contribute no error, so the exceptional term
remains exactly the probability of `Eᶜ`. -/
theorem candidate_integral_negativeTail_le_of_ae_occupation
    {Ω τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {Q : Measure Ω} {ν : Measure τ} [IsProbabilityMeasure Q] [IsFiniteMeasure ν]
    {a : Ω × τ → ℝ} {b B : ℝ} {E : Set Ω}
    (ha : Measurable a) (hE : MeasurableSet E) (hB : 0 ≤ B)
    (hbudget : ∀ᵐ ω ∂Q, ω ∈ E → ν.real {t | a (ω, t) < -b} ≤ B) :
    (∫ t, Q.real {ω | a (ω, t) < -b} ∂ν) ≤
      Q.real Eᶜ * ν.real Set.univ + B := by
  rw [candidate_integral_negativeTail_eq_occupation ha]
  have hdom : ∀ᵐ ω ∂Q, ν.real {t | a (ω, t) < -b} ≤
      Eᶜ.indicator (fun _ ↦ ν.real Set.univ) ω + B := by
    filter_upwards [hbudget] with ω hωbudget
    by_cases hω : ω ∈ E
    · simpa [hω] using hωbudget hω
    · have hmass : ν.real {t | a (ω, t) < -b} ≤ ν.real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      simpa [hω] using hmass.trans (le_add_of_nonneg_right hB)
  have hbound := integral_mono_ae
    (candidate_integrable_negativeTail_occupation (Q := Q) (ν := ν) (b := b) ha)
    (((integrable_const (μ := Q) (ν.real Set.univ)).indicator hE.compl).add
      (integrable_const (μ := Q) B)) hdom
  simpa only [Pi.add_apply,
    integral_add ((integrable_const (μ := Q) (ν.real Set.univ)).indicator hE.compl)
      (integrable_const (μ := Q) B), integral_indicator_const _ hE.compl,
    integral_const, probReal_univ, smul_eq_mul, one_mul] using hbound

/-- A pathwise occupation bound on `E` gives an averaged probability bound,
with only the window's full mass charged on `Eᶜ`. -/
theorem candidate_integral_negativeTail_le_of_occupation
    {Ω τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {Q : Measure Ω} {ν : Measure τ} [IsProbabilityMeasure Q] [IsFiniteMeasure ν]
    {a : Ω × τ → ℝ} {b B : ℝ} {E : Set Ω}
    (ha : Measurable a) (hE : MeasurableSet E) (hB : 0 ≤ B)
    (hbudget : ∀ ω ∈ E, ν.real {t | a (ω, t) < -b} ≤ B) :
    (∫ t, Q.real {ω | a (ω, t) < -b} ∂ν) ≤
      Q.real Eᶜ * ν.real Set.univ + B := by
  exact candidate_integral_negativeTail_le_of_ae_occupation ha hE hB
    (ae_of_all _ hbudget)

/-- The candidate's averaged negative-tail bound, for an arbitrary ambient
time measure and finite observation window.  The positivity and
integrability assumptions are only required on the upper-envelope event. -/
theorem candidate_integral_negativeTail_le_of_ae_positive_weighted_transform
    {Ω τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {Q : Measure Ω} {μ ν : Measure τ} [IsProbabilityMeasure Q] [IsFiniteMeasure ν]
    {a : Ω × τ → ℝ} {w : τ → ℝ} {M b c : ℝ} {E : Set Ω}
    (ha : Measurable a) (hE : MeasurableSet E)
    (hM : 0 ≤ M) (hb : 0 < b) (hc : 0 < c)
    (hw : ∀ t, 0 ≤ w t) (hwi : Integrable w μ)
    (hν : ν ≤ μ) (hwindow : ∀ᵐ t ∂ν, c ≤ w t)
    (hpaths : ∀ᵐ ω ∂Q, ω ∈ E →
      Integrable (fun t ↦ w t * a (ω, t)) μ ∧
      (∀ᵐ t ∂μ, a (ω, t) ≤ M) ∧
      0 ≤ ∫ t, w t * a (ω, t) ∂μ) :
    (∫ t, Q.real {ω | a (ω, t) < -b} ∂ν) ≤
      Q.real Eᶜ * ν.real Set.univ + (M * ∫ t, w t ∂μ) / (b * c) := by
  apply candidate_integral_negativeTail_le_of_ae_occupation ha hE
    (div_nonneg (mul_nonneg hM (integral_nonneg hw)) (mul_pos hb hc).le)
  filter_upwards [hpaths] with ω hωpaths
  intro hω
  obtain ⟨hweighted, hupper, hpositive⟩ := hωpaths hω
  exact candidate_negativeTail_measure_le_of_weighted_budget hb hc hw
    hweighted hν hwindow
    (candidate_weighted_negativePart_le hM hw hwi hweighted
      hupper hpositive)

/-- The candidate's averaged negative-tail bound, for an arbitrary ambient
time measure and finite observation window.  The positivity and
integrability assumptions are only required on the upper-envelope event. -/
theorem candidate_integral_negativeTail_le_of_positive_weighted_transform
    {Ω τ : Type*} [MeasurableSpace Ω] [MeasurableSpace τ]
    {Q : Measure Ω} {μ ν : Measure τ} [IsProbabilityMeasure Q] [IsFiniteMeasure ν]
    {a : Ω × τ → ℝ} {w : τ → ℝ} {M b c : ℝ} {E : Set Ω}
    (ha : Measurable a) (hE : MeasurableSet E)
    (hM : 0 ≤ M) (hb : 0 < b) (hc : 0 < c)
    (hw : ∀ t, 0 ≤ w t) (hwi : Integrable w μ)
    (hν : ν ≤ μ) (hwindow : ∀ᵐ t ∂ν, c ≤ w t)
    (hweighted : ∀ ω ∈ E, Integrable (fun t ↦ w t * a (ω, t)) μ)
    (hupper : ∀ ω ∈ E, ∀ᵐ t ∂μ, a (ω, t) ≤ M)
    (hpositive : ∀ ω ∈ E, 0 ≤ ∫ t, w t * a (ω, t) ∂μ) :
    (∫ t, Q.real {ω | a (ω, t) < -b} ∂ν) ≤
      Q.real Eᶜ * ν.real Set.univ + (M * ∫ t, w t ∂μ) / (b * c) := by
  apply candidate_integral_negativeTail_le_of_ae_positive_weighted_transform
    ha hE hM hb hc hw hwi hν hwindow
  exact ae_of_all _ fun ω hω ↦ ⟨hweighted ω hω, hupper ω hω, hpositive ω hω⟩

/-- The exponential weight in the candidate has total mass exactly `T`. -/
theorem candidate_integral_exp_weight {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-t / T)) = T := by
  have h := integral_exp_mul_Ioi (a := -T⁻¹) (neg_lt_zero.mpr (inv_pos.mpr hT)) 0
  simpa [div_eq_mul_inv, mul_comm] using h

/-- Equation (34) of the candidate, with the exact exceptional probability.
No integrability in the random world variable is assumed: the bounded
occupation indicator is the function to which Fubini is applied. The pathwise
Laplace assumptions need hold only almost surely on the envelope event. -/
theorem candidate_integral_negativeTail_exp_window_le_of_ae
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {a : Ω × ℝ → ℝ} {E : Set Ω} {M b T α β : ℝ}
    (ha : Measurable a) (hE : MeasurableSet E)
    (hM : 0 ≤ M) (hb : 0 < b) (hT : 0 < T) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hpaths : ∀ᵐ ω ∂Q, ω ∈ E →
      IntegrableOn (fun t ↦ Real.exp (-t / T) * a (ω, t)) (Set.Ioi 0) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioi 0), a (ω, t) ≤ M) ∧
      0 ≤ ∫ t in Set.Ioi 0, Real.exp (-t / T) * a (ω, t)) :
    (∫ t in Set.Ioc (α * T) (β * T), Q.real {ω | a (ω, t) < -b}) ≤
      Q.real Eᶜ * (β - α) * T + Real.exp β * M * T / b := by
  have hwi : IntegrableOn (fun t : ℝ ↦ Real.exp (-t / T)) (Set.Ioi 0) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (integrableOn_exp_mul_Ioi (a := -T⁻¹) (neg_lt_zero.mpr (inv_pos.mpr hT)) 0)
  have hν : volume.restrict (Set.Ioc (α * T) (β * T)) ≤
      volume.restrict (Set.Ioi (0 : ℝ)) := by
    apply Measure.restrict_mono _ le_rfl
    intro t ht
    exact lt_of_le_of_lt (mul_nonneg hα hT.le) ht.1
  have hwindow : ∀ᵐ t ∂volume.restrict (Set.Ioc (α * T) (β * T)),
      Real.exp (-β) ≤ Real.exp (-t / T) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    apply Real.exp_le_exp.mpr
    exact (le_div_iff₀ hT).mpr (by nlinarith [ht.2])
  have h := candidate_integral_negativeTail_le_of_ae_positive_weighted_transform (Q := Q) (b := b)
    (μ := volume.restrict (Set.Ioi 0))
    (ν := volume.restrict (Set.Ioc (α * T) (β * T)))
    ha hE hM hb (Real.exp_pos (-β)) (fun t ↦ (Real.exp_pos _).le)
    hwi hν hwindow hpaths
  rw [candidate_integral_exp_weight hT, measureReal_restrict_apply_univ,
    Real.volume_real_Ioc_of_le (mul_le_mul_of_nonneg_right hαβ hT.le)] at h
  convert h using 1
  rw [Real.exp_neg]
  field_simp

/-- Equation (34) of the candidate, with the exact exceptional probability.
No integrability in the random world variable is assumed: the bounded
occupation indicator is the function to which Fubini is applied. -/
theorem candidate_integral_negativeTail_exp_window_le
    {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
    {a : Ω × ℝ → ℝ} {E : Set Ω} {M b T α β : ℝ}
    (ha : Measurable a) (hE : MeasurableSet E)
    (hM : 0 ≤ M) (hb : 0 < b) (hT : 0 < T) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hweighted : ∀ ω ∈ E, IntegrableOn (fun t ↦ Real.exp (-t / T) * a (ω, t))
      (Set.Ioi 0))
    (hupper : ∀ ω ∈ E, ∀ᵐ t ∂volume.restrict (Set.Ioi 0), a (ω, t) ≤ M)
    (hpositive : ∀ ω ∈ E, 0 ≤ ∫ t in Set.Ioi 0, Real.exp (-t / T) * a (ω, t)) :
    (∫ t in Set.Ioc (α * T) (β * T), Q.real {ω | a (ω, t) < -b}) ≤
      Q.real Eᶜ * (β - α) * T + Real.exp β * M * T / b := by
  apply candidate_integral_negativeTail_exp_window_le_of_ae ha hE hM hb hT hα hαβ
  exact ae_of_all _ fun ω hω ↦ ⟨hweighted ω hω, hupper ω hω, hpositive ω hω⟩

end Erdos.Problem1144
