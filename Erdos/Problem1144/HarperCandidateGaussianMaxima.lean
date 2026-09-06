import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace Erdos.Problem1144

/-!
# Gaussian maximum error bounds

The candidate's high-frequency and stationary-extension errors have Gaussian
coordinates conditional on the multiplicative signs. Independence between
coordinates is not needed: Gaussian tails and a union bound control the whole
maximum, and a common random variance bound is handled by Markov and Fubini.
-/

/-- A centered Gaussian marginal is subgaussian with every larger variance
parameter. No joint independence is involved. -/
theorem candidate_hasSubgaussianMGF_of_gaussianReal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {σ v : ℝ≥0}
    (hX : P.map X = gaussianReal 0 σ) (hσ : σ ≤ v) :
    HasSubgaussianMGF X v P where
  integrable_exp_mul t := by
    rw [← mgf_pos_iff, mgf_gaussianReal hX t]
    exact Real.exp_pos _
  mgf_le t := by
    rw [mgf_gaussianReal hX t, zero_mul, zero_add]
    apply Real.exp_le_exp.mpr
    gcongr

/-- Absolute Gaussian tail with a common variance parameter. -/
theorem candidate_gaussian_absolute_tail_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} {σ v : ℝ≥0} {r : ℝ}
    (hX : P.map X = gaussianReal 0 σ) (hσ : σ ≤ v) (hr : 0 ≤ r) :
    P.real {ω | r ≤ |X ω|} ≤ 2 * Real.exp (-r ^ 2 / (2 * v)) := by
  have h := candidate_hasSubgaussianMGF_of_gaussianReal hX hσ
  have heq : {ω | r ≤ |X ω|} = {ω | r ≤ X ω} ∪ {ω | r ≤ -X ω} := by
    ext ω
    simp only [mem_setOf_eq, mem_union]
    exact le_abs
  rw [heq]
  calc
    _ ≤ P.real {ω | r ≤ X ω} + P.real {ω | r ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-r ^ 2 / (2 * v)) + Real.exp (-r ^ 2 / (2 * v)) :=
      add_le_add (h.measure_ge_le hr) (h.neg.measure_ge_le hr)
    _ = 2 * Real.exp (-r ^ 2 / (2 * v)) := by ring

/-- A finite correlated Gaussian family has the same union-bound maximum
estimate as independent Gaussian coordinates. -/
theorem candidate_gaussian_maximum_tail_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ι → Ω → ℝ} {σ : ι → ℝ≥0} {v : ℝ≥0} {r : ℝ}
    (hX : ∀ i, P.map (X i) = gaussianReal 0 (σ i))
    (hσ : ∀ i, σ i ≤ v) (hr : 0 ≤ r) :
    P.real {ω | ∃ i, r ≤ |X i ω|} ≤
      2 * Fintype.card ι * Real.exp (-r ^ 2 / (2 * v)) := by
  classical
  rw [show {ω | ∃ i, r ≤ |X i ω|} = ⋃ i, {ω | r ≤ |X i ω|} by ext; simp]
  calc
    _ ≤ ∑ i, P.real {ω | r ≤ |X i ω|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, 2 * Real.exp (-r ^ 2 / (2 * v)) :=
      Finset.sum_le_sum fun i _ ↦ candidate_gaussian_absolute_tail_le (hX i) (hσ i) hr
    _ = 2 * Fintype.card ι * Real.exp (-r ^ 2 / (2 * v)) := by simp; ring

private theorem candidate_product_event_real_eq_integral
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {Q : Measure Ω} {P : Measure Ξ} [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    {E : Set (Ω × Ξ)} (hE : MeasurableSet E) :
    (Q.prod P).real E = ∫ ω, P.real {ξ | (ω, ξ) ∈ E} ∂Q := by
  have hi : Integrable (E.indicator (fun _ ↦ (1 : ℝ))) (Q.prod P) :=
    (integrable_const _).indicator hE
  calc
    _ = ∫ z, E.indicator (fun _ ↦ (1 : ℝ)) z ∂Q.prod P := by
      simpa using (integral_indicator_const (μ := Q.prod P) (1 : ℝ) hE).symm
    _ = ∫ ω, ∫ ξ, E.indicator (fun _ ↦ (1 : ℝ)) (ω, ξ) ∂P ∂Q := integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simpa [Set.indicator] using integral_indicator_const (μ := P) (1 : ℝ)
        (hE.preimage (show Measurable (fun ξ : Ξ ↦ (ω, ξ)) from
          measurable_const.prodMk measurable_id))

/-- A random common variance bound suffices to control a conditional Gaussian
maximum. This is the precise error estimate used when averaging over the
multiplicative signs; the Gaussian coordinates need not be independent. -/
theorem candidate_gaussian_maximum_tail_le_random_variance
    {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [Fintype ι]
    {Q : Measure Ω} {P : Measure Ξ} [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    {X : ι → Ω × Ξ → ℝ} {σ : Ω → ι → ℝ≥0} {V : Ω → ℝ≥0}
    {v : ℝ≥0} {r : ℝ}
    (hXmeas : ∀ i, Measurable (X i)) (hVmeas : Measurable V)
    (hX : ∀ ω i, P.map (fun ξ ↦ X i (ω, ξ)) = gaussianReal 0 (σ ω i))
    (hσ : ∀ ω i, σ ω i ≤ V ω)
    (hVi : Integrable (fun ω ↦ (V ω : ℝ)) Q) (hv : 0 < v) (hr : 0 ≤ r) :
    (Q.prod P).real {z | ∃ i, r ≤ |X i z|} ≤
      (∫ ω, (V ω : ℝ) ∂Q) / v +
        2 * Fintype.card ι * Real.exp (-r ^ 2 / (2 * v)) := by
  classical
  let E : Set (Ω × Ξ) := {z | ∃ i, r ≤ |X i z|}
  let B : Set Ω := {ω | v < V ω}
  let c : ℝ := 2 * Fintype.card ι * Real.exp (-r ^ 2 / (2 * v))
  have hE : MeasurableSet E := by
    change MeasurableSet {z | ∃ i, r ≤ |X i z|}
    simp only [setOf_exists]
    exact MeasurableSet.iUnion fun i ↦ measurableSet_le measurable_const (hXmeas i).abs
  have hB : MeasurableSet B := measurableSet_lt measurable_const hVmeas
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hi : Integrable (E.indicator (fun _ ↦ (1 : ℝ))) (Q.prod P) :=
    (integrable_const _).indicator hE
  have hfiber : ∀ ω, (∫ ξ, E.indicator (fun _ ↦ (1 : ℝ)) (ω, ξ) ∂P) =
      P.real {ξ | ∃ i, r ≤ |X i (ω, ξ)|} := by
    intro ω
    simpa [Set.indicator, E] using integral_indicator_const (μ := P) (1 : ℝ)
      (hE.preimage (show Measurable (fun ξ : Ξ ↦ (ω, ξ)) from
        measurable_const.prodMk measurable_id))
  have hfint : Integrable (fun ω ↦ P.real {ξ | ∃ i, r ≤ |X i (ω, ξ)|}) Q := by
    simpa only [hfiber] using hi.integral_prod_left
  have hfbound : ∀ ω, P.real {ξ | ∃ i, r ≤ |X i (ω, ξ)|} ≤
      B.indicator (fun _ ↦ (1 : ℝ)) ω + c := by
    intro ω
    by_cases hω : ω ∈ B
    · simpa only [Set.indicator_of_mem hω] using
        (measureReal_le_one (μ := P) (s := {ξ | ∃ i, r ≤ |X i (ω, ξ)|})).trans
          (le_add_of_nonneg_right hc)
    · have hV : V ω ≤ v := le_of_not_gt hω
      simpa only [Set.indicator_of_notMem hω, zero_add] using
        candidate_gaussian_maximum_tail_le (hX ω) (fun i ↦ (hσ ω i).trans hV) hr
  have hint := integral_mono hfint
    (((integrable_const (μ := Q) (1 : ℝ)).indicator hB).add (integrable_const c)) hfbound
  simp only [Pi.add_apply] at hint
  rw [integral_add ((integrable_const (μ := Q) (1 : ℝ)).indicator hB)
    (integrable_const c), integral_indicator_const _ hB, integral_const,
    probReal_univ, one_smul] at hint
  simp only [smul_eq_mul, mul_one] at hint
  have hvR : 0 < (v : ℝ) := hv
  have hmark := (hVi.div_const (v : ℝ)).measure_le_integral
    (ae_of_all _ fun ω ↦ div_nonneg (V ω).coe_nonneg hvR.le)
    (s := B) (fun ω hω ↦ (one_le_div hvR).mpr (le_of_lt hω))
  have hmarkR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmark
  rw [ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ div_nonneg (V ω).coe_nonneg hvR.le),
    integral_div] at hmarkR
  rw [candidate_product_event_real_eq_integral hE]
  exact hint.trans (add_le_add hmarkR (le_refl c))

/-- Optimizing the variance cutoff gives the logarithmic cost used in the
candidate. In particular, `log(card) * E[V] → 0` makes every fixed positive
maximum-error threshold negligible as the grid size tends to infinity. -/
theorem candidate_gaussian_maximum_tail_le_log_variance
    {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [Fintype ι] [Nonempty ι]
    {Q : Measure Ω} {P : Measure Ξ} [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    {X : ι → Ω × Ξ → ℝ} {σ : Ω → ι → ℝ≥0} {V : Ω → ℝ≥0} {r : ℝ}
    (hXmeas : ∀ i, Measurable (X i)) (hVmeas : Measurable V)
    (hX : ∀ ω i, P.map (fun ξ ↦ X i (ω, ξ)) = gaussianReal 0 (σ ω i))
    (hσ : ∀ ω i, σ ω i ≤ V ω)
    (hVi : Integrable (fun ω ↦ (V ω : ℝ)) Q) (hr : 0 < r) :
    (Q.prod P).real {z | ∃ i, r ≤ |X i z|} ≤
      4 * Real.log (2 * Fintype.card ι) * (∫ ω, (V ω : ℝ) ∂Q) / r ^ 2 +
        1 / (2 * Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hl : 0 < Real.log (2 * Fintype.card ι) := Real.log_pos (by linarith)
  let v : ℝ≥0 := ⟨r ^ 2 / (4 * Real.log (2 * Fintype.card ι)), by positivity⟩
  have hv : 0 < v := by change (0 : ℝ) < r ^ 2 / (4 * Real.log (2 * Fintype.card ι)); positivity
  have hvval : (v : ℝ) = r ^ 2 / (4 * Real.log (2 * Fintype.card ι)) := rfl
  have h := candidate_gaussian_maximum_tail_le_random_variance
    hXmeas hVmeas hX hσ hVi hv hr.le
  have he : -r ^ 2 / (2 * (v : ℝ)) = -(2 * Real.log (2 * Fintype.card ι)) := by
    rw [hvval]
    field_simp [hr.ne', hl.ne']
    ring
  rw [he, Real.exp_neg,
    show 2 * Real.log (2 * Fintype.card ι) =
      Real.log (2 * Fintype.card ι) + Real.log (2 * Fintype.card ι) by ring,
    Real.exp_add, Real.exp_log (by positivity)] at h
  convert h using 1
  rw [hvval]
  field_simp [hr.ne', hl.ne', hn.ne']

/-- Conditional Gaussian error fields vanish uniformly in probability when
the expected common variance times the logarithm of the grid size vanishes. -/
theorem candidate_gaussian_maximum_tendsto_zero_of_log_variance
    {Ω Ξ : Type*} {ι : ℕ → Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)]
    {Q : Measure Ω} {P : Measure Ξ} [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    {X : (n : ℕ) → ι n → Ω × Ξ → ℝ}
    {σ : (n : ℕ) → Ω → ι n → ℝ≥0} {V : ℕ → Ω → ℝ≥0} {r : ℝ}
    (hXmeas : ∀ n i, Measurable (X n i)) (hVmeas : ∀ n, Measurable (V n))
    (hX : ∀ n ω i, P.map (fun ξ ↦ X n i (ω, ξ)) = gaussianReal 0 (σ n ω i))
    (hσ : ∀ n ω i, σ n ω i ≤ V n ω)
    (hVi : ∀ n, Integrable (fun ω ↦ (V n ω : ℝ)) Q) (hr : 0 < r)
    (hcard : Filter.Tendsto (fun n ↦ (Fintype.card (ι n) : ℝ)) Filter.atTop Filter.atTop)
    (hvar : Filter.Tendsto
      (fun n ↦ Real.log (2 * Fintype.card (ι n)) * ∫ ω, (V n ω : ℝ) ∂Q)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ (Q.prod P).real {z | ∃ i, r ≤ |X n i z|})
      Filter.atTop (nhds 0) := by
  have hmain := (hvar.const_mul 4).div_const (r ^ 2)
  have htail : Filter.Tendsto (fun n ↦ 1 / (2 * (Fintype.card (ι n) : ℝ)))
      Filter.atTop (nhds 0) := by
    exact Filter.Tendsto.const_div_atTop (hcard.const_mul_atTop (by norm_num)) 1
  have htotal := hmain.add htail
  simp only [mul_zero, zero_div, zero_add] at htotal
  apply Filter.Tendsto.squeeze (g := fun _ ↦ (0 : ℝ)) tendsto_const_nhds htotal
  · exact fun _ ↦ measureReal_nonneg
  · intro n
    simpa only [mul_assoc] using candidate_gaussian_maximum_tail_le_log_variance
      (hXmeas n) (hVmeas n) (hX n) (hσ n) (hVi n) hr

end Erdos.Problem1144
