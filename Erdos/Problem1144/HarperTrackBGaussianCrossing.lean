import Mathlib.Probability.Distributions.Gaussian.Real
import Erdos.Problem1144.HarperTrackBFiniteBlock

open MeasureTheory
open scoped ENNReal NNReal

namespace Erdos
namespace Problem1144

/-!
# Track B Gaussian crossing layer

This file isolates the pure-probability crossing step used by the finite
Track B spine.

The rough-core martingale CLT gives lower-orthant approximation for the
prefix vector.  The Gaussian crossing estimate itself is a bound on the
matching Gaussian lower orthant.  The deterministic content proved here is the
conversion from those two inputs to the event-level
`TrackBGaussianCrossingCertificate` consumed by `HarperTrackBFiniteBlock`.

The reflection-principle/Brownian-bridge estimate should eventually provide
the `gaussian_toReal` field below with the advertised
`C_K Λ^K (η + mesh^{-1/2})` budget.  This file keeps that estimate in the
correct finite lower-orthant form instead of hiding it in an opaque event.
-/

/-- If a finite measure is a probability measure, every set has finite
measure. -/
theorem measure_ne_top_of_isProbabilityMeasure
    {Ω' : Type*} [MeasurableSpace Ω'] (μ' : Measure Ω')
    [IsProbabilityMeasure μ'] (s : Set Ω') :
    μ' s ≠ ∞ := by
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ s)).trans (by simp))

/-- The prefix-vector map is measurable on finite real vectors. -/
theorem measurable_prefixVec {M : ℕ} :
    Measurable (prefixVec (M := M)) := by
  unfold prefixVec prefixSum
  refine measurable_pi_lambda _ fun m => ?_
  exact Finset.measurable_sum _ fun r _ => by
    by_cases hrm : (r : ℕ) ≤ (m : ℕ)
    · simpa [hrm] using measurable_pi_apply r
    · simp [hrm]

/-- Lower orthants in finite real vector spaces are measurable. -/
theorem measurableSet_lowerOrthant {M : ℕ} (b : Fin M → ℝ) :
    MeasurableSet (lowerOrthant b) := by
  classical
  rw [show lowerOrthant b =
      ⋂ m : Fin M, {s : Fin M → ℝ | s m < b m} by
        ext s
        simp [lowerOrthant]]
  exact MeasurableSet.iInter fun m =>
    measurableSet_lt (by fun_prop) measurable_const

/-- The running-maximum crossing set is measurable. -/
theorem measurableSet_crossingSet {M : ℕ} (a : ℝ) :
    MeasurableSet (crossingSet (M := M) a) := by
  change MeasurableSet
    {x : Fin M → ℝ | prefixVec x ∈ lowerOrthant (fun _ : Fin M => a)}
  exact
    (measurableSet_lowerOrthant (fun _ : Fin M => a)).preimage
      measurable_prefixVec

/-- Independent centered Gaussian increment law with prescribed coordinate
variances. -/
noncomputable def gaussianWalkIncrementMeasure {M : ℕ}
    (variance : Fin M → ℝ≥0) : Measure (Fin M → ℝ) :=
  Measure.pi fun r => ProbabilityTheory.gaussianReal 0 (variance r)

/-- Law of the Gaussian prefix vector obtained from independent increments. -/
noncomputable def gaussianWalkPrefixMeasure {M : ℕ}
    (variance : Fin M → ℝ≥0) : Measure (Fin M → ℝ) :=
  (gaussianWalkIncrementMeasure variance).map prefixVec

instance gaussianWalkIncrementMeasure_isProbabilityMeasure {M : ℕ}
    (variance : Fin M → ℝ≥0) :
    IsProbabilityMeasure (gaussianWalkIncrementMeasure variance) := by
  unfold gaussianWalkIncrementMeasure
  infer_instance

instance gaussianWalkPrefixMeasure_isProbabilityMeasure {M : ℕ}
    (variance : Fin M → ℝ≥0) :
    IsProbabilityMeasure (gaussianWalkPrefixMeasure variance) := by
  refine ⟨?_⟩
  rw [gaussianWalkPrefixMeasure,
    Measure.map_apply measurable_prefixVec MeasurableSet.univ]
  simp

/-- Applying the Gaussian prefix law to a lower orthant is the same as applying
the independent-increment law to the corresponding prefix preimage. -/
theorem gaussianWalkPrefixMeasure_apply_lowerOrthant {M : ℕ}
    (variance : Fin M → ℝ≥0) (b : Fin M → ℝ) :
    gaussianWalkPrefixMeasure variance (lowerOrthant b) =
      gaussianWalkIncrementMeasure variance
        {x : Fin M → ℝ | prefixVec x ∈ lowerOrthant b} := by
  rw [gaussianWalkPrefixMeasure]
  exact Measure.map_apply measurable_prefixVec (measurableSet_lowerOrthant b)

/-- The constant lower-orthant event for the Gaussian prefix law is exactly the
running-maximum crossing event for the independent Gaussian increments. -/
theorem gaussianWalkPrefixMeasure_apply_const_lowerOrthant {M : ℕ}
    (variance : Fin M → ℝ≥0) (a : ℝ) :
    gaussianWalkPrefixMeasure variance
        (lowerOrthant (fun _ : Fin M => a)) =
      gaussianWalkIncrementMeasure variance (crossingSet a) := by
  rw [gaussianWalkPrefixMeasure_apply_lowerOrthant]
  rfl

/-- Variance-window assumptions for the finite independent Gaussian walk.

`varianceRatio` is intended to be a polynomial loss such as `C Λ^(2K)`.
-/
structure GaussianWalkVarianceWindow {M : ℕ}
    (variance : Fin M → ℝ≥0) (V varianceRatio : ℝ) : Prop where
  lower : ∀ r, V ≤ (variance r : ℝ)
  upper : ∀ r, (variance r : ℝ) ≤ varianceRatio * V

/-- The variance-window upper ratio can be relaxed, provided the variance
floor is nonnegative. -/
theorem GaussianWalkVarianceWindow.mono_ratio
    {M : ℕ} {variance : Fin M → ℝ≥0} {V ratio ratio' : ℝ}
    (h : GaussianWalkVarianceWindow variance V ratio)
    (hV : 0 ≤ V) (hratio : ratio ≤ ratio') :
    GaussianWalkVarianceWindow variance V ratio' where
  lower := h.lower
  upper := fun r => (h.upper r).trans (mul_le_mul_of_nonneg_right hratio hV)

/-- Lean-facing form of the reflection-principle/Brownian-bridge estimate for
an independent Gaussian walk.  This is the remaining analytic probability
bound inside T1: once proved, it supplies the `gaussian_toReal` field of
`TrackBGaussianLowerOrthantCrossingInput` for
`gamma = gaussianWalkPrefixMeasure variance`.
-/
structure IndependentGaussianWalkCrossingEstimate
    {M : ℕ} (variance : Fin M → ℝ≥0) (level bound : ℝ) : Prop where
  crossing_toReal :
    (gaussianWalkIncrementMeasure variance (crossingSet level)).toReal ≤
      bound

/-- Crossing estimates are monotone in the real bound. -/
theorem IndependentGaussianWalkCrossingEstimate.mono_bound
    {M : ℕ} {variance : Fin M → ℝ≥0} {level bound bound' : ℝ}
    (h : IndependentGaussianWalkCrossingEstimate variance level bound)
    (hbound : bound ≤ bound') :
    IndependentGaussianWalkCrossingEstimate variance level bound' where
  crossing_toReal := h.crossing_toReal.trans hbound

/-- Trivial baseline Gaussian crossing estimate from the fact that the
independent Gaussian walk law is a probability measure.  The sharp Track B
schedule needs the reflection-principle estimate, but this constructor is
useful for degenerate and sanity-check applications of the interface. -/
theorem IndependentGaussianWalkCrossingEstimate.of_one_le_bound
    {M : ℕ} {variance : Fin M → ℝ≥0} {level bound : ℝ}
    (hbound : 1 ≤ bound) :
    IndependentGaussianWalkCrossingEstimate variance level bound where
  crossing_toReal := by
    have hprob :
        gaussianWalkIncrementMeasure variance (crossingSet level) ≤ 1 := by
      simpa using
        (measure_mono
          (Set.subset_univ (crossingSet (M := M) level))).trans
          (by simp)
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hprob).trans hbound

/-- Variance-window version of the independent Gaussian crossing estimate.

This is the exact target for the future reflection-principle proof: under a
variance window, prove a small crossing bound.  Keeping the window together
with the resulting estimate prevents later stages from losing track of the
variance-ratio hypotheses used to derive the bound. -/
structure IndependentGaussianWalkVarianceCrossingEstimate
    {M : ℕ} (variance : Fin M → ℝ≥0)
    (V varianceRatio level bound : ℝ) : Prop where
  window : GaussianWalkVarianceWindow variance V varianceRatio
  crossing : IndependentGaussianWalkCrossingEstimate variance level bound

/-- Forget the variance-window bookkeeping after the crossing bound is
proved. -/
theorem IndependentGaussianWalkVarianceCrossingEstimate.toCrossingEstimate
    {M : ℕ} {variance : Fin M → ℝ≥0}
    {V varianceRatio level bound : ℝ}
    (h :
      IndependentGaussianWalkVarianceCrossingEstimate variance V
        varianceRatio level bound) :
    IndependentGaussianWalkCrossingEstimate variance level bound :=
  h.crossing

/-- Degenerate variance-window crossing estimate obtained from the trivial
probability bound.  This does not supply the Track B asymptotic schedule, but
it is useful for testing the complete variance-window plumbing before the
reflection-principle estimate is installed. -/
theorem IndependentGaussianWalkVarianceCrossingEstimate.of_one_le_bound
    {M : ℕ} {variance : Fin M → ℝ≥0}
    {V varianceRatio level bound : ℝ}
    (hwindow : GaussianWalkVarianceWindow variance V varianceRatio)
    (hbound : 1 ≤ bound) :
    IndependentGaussianWalkVarianceCrossingEstimate variance V
      varianceRatio level bound where
  window := hwindow
  crossing := IndependentGaussianWalkCrossingEstimate.of_one_le_bound hbound

/-- Independent-walk crossing estimates produce lower-orthant bounds for the
matching Gaussian prefix law. -/
theorem IndependentGaussianWalkCrossingEstimate.prefix_toReal
    {M : ℕ} {variance : Fin M → ℝ≥0} {level bound : ℝ}
    (h : IndependentGaussianWalkCrossingEstimate variance level bound) :
    (gaussianWalkPrefixMeasure variance
      (lowerOrthant (fun _ : Fin M => level))).toReal ≤ bound := by
  rw [gaussianWalkPrefixMeasure_apply_const_lowerOrthant]
  exact h.crossing_toReal

/-- Convert a real bound on the `toReal` of a finite `ENNReal` into an
`ENNReal.ofReal` bound. -/
theorem ennreal_le_of_toReal_le
    {x : ℝ≥0∞} {a : ℝ} (hx : x ≠ ∞)
    (hxa : x.toReal ≤ a) :
    x ≤ ENNReal.ofReal a := by
  rw [← ENNReal.ofReal_toReal hx]
  exact ENNReal.ofReal_le_ofReal hxa

/-- Lower-orthant approximation and a Gaussian lower-orthant real bound give
a real bound for the original crossing event. -/
theorem crossing_measure_toReal_le_of_lowerOrthantApprox
    {Ω' : Type*} [MeasurableSpace Ω'] {M : ℕ}
    {μ' : Measure Ω'} {Y : Ω' → Fin M → ℝ}
    {γ : Measure (Fin M → ℝ)} {a ε gaussianBound : ℝ}
    (hApprox :
      LowerOrthantApprox μ' (fun omega => prefixVec (Y omega)) γ ε)
    (hGaussian :
      (γ (lowerOrthant (fun _ : Fin M => a))).toReal ≤ gaussianBound) :
    (μ' {omega | Y omega ∈ crossingSet a}).toReal ≤
      gaussianBound + ε := by
  have hdiff :
      ((μ' {omega | Y omega ∈ crossingSet a}).toReal -
        (γ (lowerOrthant (fun _ : Fin M => a))).toReal) ≤ ε := by
    exact (le_abs_self _).trans
      (crossing_of_lowerOrthantApprox μ' Y γ a ε hApprox)
  linarith

/-- Lower-orthant approximation and a Gaussian lower-orthant real bound give
an `ENNReal` bound for the original crossing event. -/
theorem crossing_measure_le_of_lowerOrthantApprox
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {M : ℕ} {Y : Ω' → Fin M → ℝ}
    {γ : Measure (Fin M → ℝ)} {a ε gaussianBound : ℝ}
    (hApprox :
      LowerOrthantApprox μ' (fun omega => prefixVec (Y omega)) γ ε)
    (hGaussian :
      (γ (lowerOrthant (fun _ : Fin M => a))).toReal ≤ gaussianBound) :
    μ' {omega | Y omega ∈ crossingSet a} ≤
      ENNReal.ofReal (gaussianBound + ε) := by
  exact
    ennreal_le_of_toReal_le
      (measure_ne_top_of_isProbabilityMeasure μ'
        {omega | Y omega ∈ crossingSet a})
      (crossing_measure_toReal_le_of_lowerOrthantApprox hApprox hGaussian)

/-- Convert a real three-term bound into the existing ENNReal Gaussian
crossing budget. -/
theorem ofReal_le_trackBGaussianCrossingBudget_of_le_three
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    {j : ℕ} {x eta mesh variance : ℝ}
    (hx : x ≤ eta + mesh + variance)
    (heta : ENNReal.ofReal eta ≤ etaTerm j)
    (hmesh : ENNReal.ofReal mesh ≤ meshTerm j)
    (hvar : ENNReal.ofReal variance ≤ varianceTerm j) :
    ENNReal.ofReal x ≤
      trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j := by
  calc
    ENNReal.ofReal x ≤ ENNReal.ofReal (eta + mesh + variance) :=
      ENNReal.ofReal_le_ofReal hx
    _ = ENNReal.ofReal ((eta + mesh) + variance) := by ring_nf
    _ ≤ ENNReal.ofReal (eta + mesh) + ENNReal.ofReal variance :=
      ENNReal.ofReal_add_le
    _ ≤ (ENNReal.ofReal eta + ENNReal.ofReal mesh) +
        ENNReal.ofReal variance := by
      simpa [add_assoc, add_comm, add_left_comm] using
        add_le_add_right
          (ENNReal.ofReal_add_le (p := eta) (q := mesh))
          (ENNReal.ofReal variance)
    _ ≤ (etaTerm j + meshTerm j) + varianceTerm j :=
      add_le_add (add_le_add heta hmesh) hvar
    _ = trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j := by
      simp [trackBGaussianCrossingBudget]

/-- Real-valued decomposition of the Gaussian crossing budget into
small-height, mesh, and variance/replacement terms.  This is the shape the
future reflection-principle estimate naturally produces before conversion to
the ENNReal budget used by the finite Track B union bound. -/
structure TrackBGaussianRealBudgetInput
    (etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞)
    (gaussianBound replacementError : ℕ → ℝ) where
  etaReal : ℕ → ℝ
  meshReal : ℕ → ℝ
  varianceReal : ℕ → ℝ
  real_bound :
    ∀ j,
      gaussianBound j + replacementError j ≤
        etaReal j + meshReal j + varianceReal j
  eta_budget : ∀ j, ENNReal.ofReal (etaReal j) ≤ etaTerm j
  mesh_budget : ∀ j, ENNReal.ofReal (meshReal j) ≤ meshTerm j
  variance_budget : ∀ j, ENNReal.ofReal (varianceReal j) ≤ varianceTerm j

/-- A real three-term Gaussian budget supplies the ENNReal budget inequality
required by the Track B crossing inputs. -/
theorem TrackBGaussianRealBudgetInput.budget_le
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    {gaussianBound replacementError : ℕ → ℝ}
    (h :
      TrackBGaussianRealBudgetInput etaTerm meshTerm varianceTerm
        gaussianBound replacementError) :
    ∀ j,
      ENNReal.ofReal (gaussianBound j + replacementError j) ≤
        trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j := by
  intro j
  exact
    ofReal_le_trackBGaussianCrossingBudget_of_le_three
      (j := j) (h.real_bound j) (h.eta_budget j) (h.mesh_budget j)
      (h.variance_budget j)

/-- Lean-facing lower-orthant version of the Track B Gaussian crossing input.

For each stage `j`, `eval j` is the rough-core increment vector on the
original probability space, `gamma j` is the matching Gaussian law for the
prefix vector, and `level j` is the crossing threshold.  The fields require:

* lower-orthant approximation of the prefix vector;
* a real-valued Gaussian crossing bound;
* conversion of that real bound plus replacement error into the three-term
  Track B Gaussian budget.
-/
structure TrackBGaussianLowerOrthantCrossingInput
    (etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞) where
  M : ℕ → ℕ
  level : ℕ → ℝ
  eval : (j : ℕ) → Omega → Fin (M j) → ℝ
  gamma : (j : ℕ) → Measure (Fin (M j) → ℝ)
  replacementError : ℕ → ℝ
  gaussianBound : ℕ → ℝ
  lower_orthant :
    ∀ j,
      LowerOrthantApprox mu
        (fun omega => prefixVec (eval j omega))
        (gamma j) (replacementError j)
  gaussian_toReal :
    ∀ j,
      ((gamma j)
        (lowerOrthant (fun _ : Fin (M j) => level j))).toReal ≤
        gaussianBound j
  budget_le :
    ∀ j,
      ENNReal.ofReal (gaussianBound j + replacementError j) ≤
        trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j

/-- Version of the Gaussian crossing input where the Gaussian law is supplied
by independent increments with explicit variances.  This is the form expected
from the reflection-principle/Brownian-bridge estimate. -/
structure TrackBIndependentGaussianWalkCrossingInput
    (etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞) where
  M : ℕ → ℕ
  level : ℕ → ℝ
  eval : (j : ℕ) → Omega → Fin (M j) → ℝ
  variance : (j : ℕ) → Fin (M j) → ℝ≥0
  replacementError : ℕ → ℝ
  gaussianBound : ℕ → ℝ
  lower_orthant :
    ∀ j,
      LowerOrthantApprox mu
        (fun omega => prefixVec (eval j omega))
        (gaussianWalkPrefixMeasure (variance j)) (replacementError j)
  independent_crossing :
    ∀ j,
      IndependentGaussianWalkCrossingEstimate (variance j) (level j)
        (gaussianBound j)
  budget_le :
    ∀ j,
      ENNReal.ofReal (gaussianBound j + replacementError j) ≤
        trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j

/-- Stagewise independent Gaussian crossing input with explicit variance
windows.  This is the final T1-facing interface: the future
reflection-principle theorem should construct `variance_crossing`. -/
structure TrackBIndependentGaussianWalkVarianceInput
    (etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞) where
  M : ℕ → ℕ
  level : ℕ → ℝ
  eval : (j : ℕ) → Omega → Fin (M j) → ℝ
  variance : (j : ℕ) → Fin (M j) → ℝ≥0
  V : ℕ → ℝ
  varianceRatio : ℕ → ℝ
  replacementError : ℕ → ℝ
  gaussianBound : ℕ → ℝ
  lower_orthant :
    ∀ j,
      LowerOrthantApprox mu
        (fun omega => prefixVec (eval j omega))
        (gaussianWalkPrefixMeasure (variance j)) (replacementError j)
  variance_crossing :
    ∀ j,
      IndependentGaussianWalkVarianceCrossingEstimate (variance j) (V j)
        (varianceRatio j) (level j) (gaussianBound j)
  budget_le :
    ∀ j,
      ENNReal.ofReal (gaussianBound j + replacementError j) ≤
        trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j

/-- Forget the explicit variance-window bookkeeping once the independent
Gaussian crossing estimate is available. -/
noncomputable def TrackBIndependentGaussianWalkVarianceInput.toIndependentInput
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    (h :
      TrackBIndependentGaussianWalkVarianceInput etaTerm meshTerm
        varianceTerm) :
    TrackBIndependentGaussianWalkCrossingInput etaTerm meshTerm varianceTerm where
  M := h.M
  level := h.level
  eval := h.eval
  variance := h.variance
  replacementError := h.replacementError
  gaussianBound := h.gaussianBound
  lower_orthant := h.lower_orthant
  independent_crossing := fun j =>
    (h.variance_crossing j).toCrossingEstimate
  budget_le := h.budget_le

/-- Independent-increment Gaussian crossing inputs are lower-orthant Gaussian
crossing inputs after pushing the independent walk through `prefixVec`. -/
noncomputable def TrackBIndependentGaussianWalkCrossingInput.toLowerOrthantInput
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    (h :
      TrackBIndependentGaussianWalkCrossingInput etaTerm meshTerm varianceTerm) :
    TrackBGaussianLowerOrthantCrossingInput etaTerm meshTerm varianceTerm where
  M := h.M
  level := h.level
  eval := h.eval
  gamma := fun j => gaussianWalkPrefixMeasure (h.variance j)
  replacementError := h.replacementError
  gaussianBound := h.gaussianBound
  lower_orthant := h.lower_orthant
  gaussian_toReal := fun j =>
    (h.independent_crossing j).prefix_toReal
  budget_le := h.budget_le

/-- The lower-orthant Gaussian crossing input supplies the event-level Track B
Gaussian crossing certificate. -/
noncomputable def TrackBGaussianLowerOrthantCrossingInput.toCertificate
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    (h :
      TrackBGaussianLowerOrthantCrossingInput etaTerm meshTerm varianceTerm) :
    TrackBGaussianCrossingCertificate etaTerm meshTerm varianceTerm where
  bad := fun j => {omega | h.eval j omega ∈ crossingSet (h.level j)}
  prob := by
    intro j
    exact
      (crossing_measure_le_of_lowerOrthantApprox
        (μ' := mu) (Y := h.eval j) (γ := h.gamma j)
        (a := h.level j) (ε := h.replacementError j)
        (gaussianBound := h.gaussianBound j)
        (h.lower_orthant j) (h.gaussian_toReal j)).trans
        (h.budget_le j)

/-- Independent-increment Gaussian crossing inputs directly supply the
event-level Track B Gaussian crossing certificate. -/
noncomputable def TrackBIndependentGaussianWalkCrossingInput.toCertificate
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    (h :
      TrackBIndependentGaussianWalkCrossingInput etaTerm meshTerm varianceTerm) :
    TrackBGaussianCrossingCertificate etaTerm meshTerm varianceTerm :=
  h.toLowerOrthantInput.toCertificate

/-- Variance-window Gaussian crossing inputs directly supply the event-level
Track B Gaussian crossing certificate. -/
noncomputable def TrackBIndependentGaussianWalkVarianceInput.toCertificate
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    (h :
      TrackBIndependentGaussianWalkVarianceInput etaTerm meshTerm
        varianceTerm) :
    TrackBGaussianCrossingCertificate etaTerm meshTerm varianceTerm :=
  h.toIndependentInput.toCertificate

/-- Variant with a larger ambient Gaussian error budget. -/
noncomputable def TrackBGaussianLowerOrthantCrossingInput.toDirectProbabilityInputLe
    {etaTerm meshTerm varianceTerm errGaussian : ℕ → ℝ≥0∞}
    (h :
      TrackBGaussianLowerOrthantCrossingInput etaTerm meshTerm varianceTerm)
    (hle :
      ∀ j,
        trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j ≤
          errGaussian j) :
    TrackBDirectProbabilityInput errGaussian :=
  h.toCertificate.toDirectProbabilityInputLe hle

end Problem1144
end Erdos
