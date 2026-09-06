import Erdos.Problem1144.HarperCandidateStationaryTailVariance
import Erdos.Problem1144.HarperCandidateSchedule

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology

namespace Erdos.Problem1144

/-- Gaussian maxima on a measurable old-sign event are controlled by an
almost-sure variance bound on that event. Exceptional null paths and
dependence among the Gaussian coordinates are both allowed. -/
theorem candidate_gaussian_maximum_on_event_le
    {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    [Fintype ι] [Nonempty ι]
    {Q : Measure Ω} {P : Measure Ξ} [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    {E : Set Ω} (hE : MeasurableSet E) {X : ι → Ω × Ξ → ℝ}
    {σ : Ω → ι → ℝ≥0} {V : Ω → ℝ} {A r : ℝ}
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ ω i, P.map (fun ξ => X i (ω, ξ)) = gaussianReal 0 (σ ω i))
    (hA : 0 ≤ A) (hV : ∀ ω, 0 ≤ V ω) (hVi : Integrable V Q)
    (hσ : ∀ᵐ ω ∂Q, ω ∈ E → ∀ i, (σ ω i : ℝ) ≤ A + V ω) (hr : 0 < r) :
    (Q.prod P).real {z | z.1 ∈ E ∧ ∃ i, r ≤ |X i z|} ≤
      4 * Real.log (2 * Fintype.card ι) * (A + ∫ ω, V ω ∂Q) / r ^ 2 +
        1 / (2 * Fintype.card ι) := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hl : 0 < Real.log (2 * Fintype.card ι) := Real.log_pos (by linarith)
  let v : ℝ≥0 := ⟨r ^ 2 / (4 * Real.log (2 * Fintype.card ι)), by positivity⟩
  have hvval : (v : ℝ) = r ^ 2 / (4 * Real.log (2 * Fintype.card ι)) := rfl
  have hv : 0 < (v : ℝ) := div_pos (sq_pos_of_pos hr) (mul_pos (by norm_num) hl)
  let b : ℝ := 2 * Fintype.card ι * Real.exp (-r ^ 2 / (2 * v))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  let F : Set (Ω × Ξ) := {z | z.1 ∈ E ∧ ∃ i, r ≤ |X i z|}
  have hF : MeasurableSet F := by
    apply (hE.preimage measurable_fst).inter
    change MeasurableSet {z | ∃ i, r ≤ |X i z|}
    simp only [setOf_exists]
    exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (hXm i).abs
  have hi : Integrable (F.indicator (fun _ => (1 : ℝ))) (Q.prod P) :=
    (integrable_const _).indicator hF
  have hfiber (ω : Ω) : (∫ ξ, F.indicator (fun _ => (1 : ℝ)) (ω, ξ) ∂P) =
      P.real {ξ | (ω, ξ) ∈ F} := by
    simpa [indicator] using integral_indicator_const (μ := P) (1 : ℝ)
      (hF.preimage (measurable_const.prodMk measurable_id))
  have hpoint : ∀ᵐ ω ∂Q,
      (∫ ξ, F.indicator (fun _ => (1 : ℝ)) (ω, ξ) ∂P) ≤ (A + V ω) / v + b := by
    filter_upwards [hσ] with ω hω
    rw [hfiber]
    by_cases hωE : ω ∈ E
    · have hf : {ξ | (ω, ξ) ∈ F} = {ξ | ∃ i, r ≤ |X i (ω, ξ)|} := by
        ext ξ
        simp [F, hωE]
      rw [hf]
      by_cases hs : A + V ω ≤ v
      · exact (candidate_gaussian_maximum_tail_le (hX ω)
          (fun i => show σ ω i ≤ v from (hω hωE i).trans hs) hr.le).trans
            (le_add_of_nonneg_left (div_nonneg (add_nonneg hA (hV ω)) hv.le))
      · exact (measureReal_le_one (μ := P)).trans
          ((one_le_div hv).mpr (le_of_not_ge hs) |>.trans (le_add_of_nonneg_right hb))
    · have hempty : {ξ | (ω, ξ) ∈ F} = ∅ := by ext ξ; simp [F, hωE]
      rw [hempty, measureReal_empty]
      exact add_nonneg (div_nonneg (add_nonneg hA (hV ω)) hv.le) hb
  have hint := integral_mono_ae hi.integral_prod_left
    (((integrable_const A).add hVi).div_const (v : ℝ) |>.add (integrable_const b)) hpoint
  have hprob : (Q.prod P).real F = ∫ ω, ∫ ξ,
      F.indicator (fun _ => (1 : ℝ)) (ω, ξ) ∂P ∂Q := by
    rw [← integral_prod _ hi]
    simpa using (integral_indicator_const (μ := Q.prod P) (1 : ℝ) hF).symm
  rw [← hprob] at hint
  simp only [Pi.add_apply] at hint
  have hAi : Integrable (fun ω => A + V ω) Q := (integrable_const A).add hVi
  rw [integral_add (hAi.div_const (v : ℝ)) (integrable_const b), integral_div] at hint
  have hsum : (∫ ω, A + V ω ∂Q) = A + ∫ ω, V ω ∂Q := by
    calc
      _ = (∫ _ω, A ∂Q) + ∫ ω, V ω ∂Q := integral_add (integrable_const A) hVi
      _ = _ := by simp
  rw [hsum] at hint
  simp only [integral_const, probReal_univ, one_smul] at hint
  have he : -r ^ 2 / (2 * (v : ℝ)) = -(2 * Real.log (2 * Fintype.card ι)) := by
    rw [hvval]
    field_simp
    ring
  dsimp [b] at hint
  rw [he, Real.exp_neg,
    show 2 * Real.log (2 * Fintype.card ι) =
      Real.log (2 * Fintype.card ι) + Real.log (2 * Fintype.card ι) by ring,
    Real.exp_add, Real.exp_log (by positivity)] at hint
  convert hint using 1
  rw [hvval]
  field_simp

/-- Equation (24) gives a quantitative Gaussian maximum bound on any fixed
weighted-bound event under any fixed cylinder. -/
theorem candidate_stationary_gaussian_maximum_on_weighted_event_le
    {Ξ ι : Type*} [MeasurableSpace Ξ] [Fintype ι] [Nonempty ι]
    {P : Measure Ξ} [IsProbabilityMeasure P]
    (s : Finset ℕ) (η : s → Bool) {E : Set Omega} (hE : MeasurableSet E)
    {X : ι → Omega × Ξ → ℝ} {σ : Omega → ι → ℝ≥0}
    {c T W K r : ℝ} (hc : 0 ≤ c) (hT : 1 ≤ T) (hj : 1 ≤ Real.log T)
    (hW : 1 ≤ W) (hK : 0 ≤ K) (hr : 0 < r)
    (hR : ∀ᵐ ω ∂candidateCylinderLaw s η, ω ∈ E → CandidateWeightedLogBound ω K)
    (hXm : ∀ i, Measurable (X i))
    (hX : ∀ ω i, P.map (fun ξ => X i (ω, ξ)) = gaussianReal 0 (σ ω i))
    (hσ : ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ i,
      (σ ω i : ℝ) ≤ candidateCompleteStationaryTailVariance ω c T W) :
    ((candidateCylinderLaw s η).prod P).real {z | z.1 ∈ E ∧ ∃ i, r ≤ |X i z|} ≤
      4 * Real.log (2 * Fintype.card ι) *
        (2 * K ^ 2 * candidateStationaryTailConstant c * Real.log T ^ 2 *
          Real.exp (-2 * c * W) / W +
          Real.exp (-2 * c * W) / (W * mu.real (candidateCylinder s η))) / r ^ 2 +
        1 / (2 * Fintype.card ι) := by
  have hTpos : 0 < T := by linarith
  have hWpos : 0 < W := by linarith
  have he := candidateCylinderLaw_integral_stationarySquareErrorVariance_le s η c hTpos hWpos
  have h := candidate_gaussian_maximum_on_event_le hE hXm hX
    (A := 2 * K ^ 2 * candidateStationaryTailConstant c * Real.log T ^ 2 *
      Real.exp (-2 * c * W) / W)
    (V := fun ω => candidateStationarySquareErrorVariance ω c T W)
    (by unfold candidateStationaryTailConstant; positivity)
    (fun ω => candidateStationarySquareErrorVariance_nonneg ω c W hTpos.le) he.1
    (by filter_upwards [hR, hσ,
          candidateCylinderLaw_ae_stationaryTailVariance_le_of_weighted_bound
            s η hc hT hj hW hK] with ω hωR hωσ hωtail
        intro hωE i
        exact (hωσ i).trans (hωtail (hωR hωE))) hr
  apply h.trans
  have hl : 0 ≤ Real.log (2 * Fintype.card ι) := Real.log_nonneg (by
    have hn : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast (by omega : 1 ≤ 2 * Fintype.card ι))
  gcongr
  exact he.2

end Erdos.Problem1144
