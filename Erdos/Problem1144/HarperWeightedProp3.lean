import Erdos.Problem1144.HarperIncrement
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-!
# Weighted Harper Proposition 3 interface

This file isolates the deterministic part of the weighted Proposition 3
detour.  The actual Harper high-moment estimate remains an explicit analytic
input, but it is now routed through concrete interfaces: admissible weights,
weighted volume bounds, and a row-moment-to-bad-degree counting lemma.
-/

/-- A harmless stand-in for `log log X` in parameter hypotheses. -/
noncomputable def loglogNat (X : ℕ) : ℝ :=
  Real.log (Real.log (X : ℝ))

/-- A harmless stand-in for `log log log X` in parameter hypotheses. -/
noncomputable def logloglogNat (X : ℕ) : ℝ :=
  Real.log (loglogNat X)

/-- Length of a real interval, truncated at zero. -/
noncomputable def intervalLength (a b : ℝ) : ℝ :=
  max 0 (b - a)

theorem intervalLength_nonneg (a b : ℝ) :
    0 ≤ intervalLength a b := by
  unfold intervalLength
  exact le_max_left _ _

/-- Weighted mass of an interval for a deterministic complex weight. -/
noncomputable def weightedIntervalMass (H : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ t in Set.Icc a b, (‖H t‖) ^ 2

/-- Admissible deterministic weights for the weighted Harper covariance
integral.

The local-mass field is the important addition over a bare `L∞`/`L²`
condition: it prevents the deterministic weight from concentrating all of its
mass on tiny resonant intervals. -/
structure HarperWeight
    (X : ℕ) (B ell M : ℝ) (H : ℝ → ℂ) where
  a0 : ℝ
  a1 : ℝ
  Cmu : ℝ
  a0_pos : 0 < a0
  a1_nonneg : 0 ≤ a1
  Cmu_nonneg : 0 ≤ Cmu
  ell_nonneg : 0 ≤ ell
  M_nonneg : 0 ≤ M
  interval_mass_nonneg :
    ∀ a b : ℝ, 0 ≤ weightedIntervalMass H a b
  mass_lower : a0 * ell ≤ M
  mass_upper : M ≤ a1 * ell
  local_mass :
    ∀ a b : ℝ,
      weightedIntervalMass H a b ≤
        Cmu * M * min 1 (ell * intervalLength a b)
  ell_polylog : ell ≤ (loglogNat X) ^ B

/-- Backwards-compatible name for the first weighted layer. -/
abbrev HarperWeightAdmissible := HarperWeight

/-- Extra regularity needed only when deriving the weighted covariance
integral from a Perron/truncation formula.  Weighted Proposition 3 itself uses
only `HarperWeight`. -/
structure PerronHarperWeight
    (X : ℕ) (B ell M : ℝ) (H : ℝ → ℂ)
    extends HarperWeight X B ell M H where
  supported_on_harper_range :
    ∀ t : ℝ, H t ≠ 0 →
      (loglogNat X) ^ (-(2 : ℝ)) ≤ |t| ∧ |t| ≤ (loglogNat X) ^ 2
  continuous_on_range :
    ContinuousOn H {t : ℝ | |t| ≤ (loglogNat X) ^ 2}
  c1_bound_on_range :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t : ℝ, |t| ≤ (loglogNat X) ^ 2 → ‖deriv H t‖ ≤ K

/-- A local-mass consequence with an externally supplied interval-length
upper bound. -/
theorem weighted_interval_mass_le_of_length_le
    {X : ℕ} {B ell M : ℝ} {H : ℝ → ℂ}
    (hH : HarperWeightAdmissible X B ell M H)
    {a b delta : ℝ}
    (hlen : intervalLength a b ≤ delta)
    (_hdelta : 0 ≤ delta) :
    weightedIntervalMass H a b ≤
      hH.Cmu * M * min 1 (ell * delta) := by
  have hmin :
      min 1 (ell * intervalLength a b) ≤ min 1 (ell * delta) := by
    exact min_le_min_left _ (mul_le_mul_of_nonneg_left hlen hH.ell_nonneg)
  exact (hH.local_mass a b).trans
    (mul_le_mul_of_nonneg_left hmin (mul_nonneg hH.Cmu_nonneg hH.M_nonneg))

section Volume

variable {ι : Type*}

/-- Product-form weighted gap-cell bound.  This is the deterministic piece
used after ordering variables and partitioning by gap sizes. -/
theorem weighted_gap_volume_bound
    {X : ℕ} {B ell M : ℝ} {H : ℝ → ℂ}
    (hH : HarperWeightAdmissible X B ell M H)
    (gaps : Finset ι) (left right gapLength : ι → ℝ)
    (hlen :
      ∀ i ∈ gaps, intervalLength (left i) (right i) ≤ gapLength i)
    (hgap_nonneg : ∀ i ∈ gaps, 0 ≤ gapLength i) :
    (∏ i ∈ gaps, weightedIntervalMass H (left i) (right i)) ≤
      ∏ i ∈ gaps,
        hH.Cmu * M * min 1 (ell * gapLength i) := by
  exact Finset.prod_le_prod
    (fun i _hi => hH.interval_mass_nonneg (left i) (right i))
    (fun i hi =>
      weighted_interval_mass_le_of_length_le hH
        (hlen i hi) (hgap_nonneg i hi))

private theorem weighted_local_upper_nonneg
    {X : ℕ} {B ell M : ℝ} {H : ℝ → ℂ}
    (hH : HarperWeightAdmissible X B ell M H)
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    0 ≤ hH.Cmu * M * min 1 (ell * delta) := by
  have hmin : 0 ≤ min 1 (ell * delta) := by
    exact le_min (by norm_num) (mul_nonneg hH.ell_nonneg hdelta)
  exact mul_nonneg (mul_nonneg hH.Cmu_nonneg hH.M_nonneg) hmin

/-- Hyperplane-improved resonant volume bound.  The distinguished interval
models the extra restriction forced by the resonant signed-sum condition; the
remaining factors are ordinary gap-cell local-mass bounds. -/
theorem weighted_gap_volume_resonant_bound
    {X : ℕ} {B ell M : ℝ} {H : ℝ → ℂ}
    (hH : HarperWeightAdmissible X B ell M H)
    (gaps : Finset ι) (left right gapLength : ι → ℝ)
    (hyperLeft hyperRight hyperWidth : ℝ)
    (hlen :
      ∀ i ∈ gaps, intervalLength (left i) (right i) ≤ gapLength i)
    (hgap_nonneg : ∀ i ∈ gaps, 0 ≤ gapLength i)
    (hhyper_len : intervalLength hyperLeft hyperRight ≤ hyperWidth)
    (hhyper_nonneg : 0 ≤ hyperWidth) :
    weightedIntervalMass H hyperLeft hyperRight *
      (∏ i ∈ gaps, weightedIntervalMass H (left i) (right i)) ≤
      (hH.Cmu * M * min 1 (ell * hyperWidth)) *
        ∏ i ∈ gaps,
          hH.Cmu * M * min 1 (ell * gapLength i) := by
  have hfirst :=
    weighted_interval_mass_le_of_length_le hH hhyper_len hhyper_nonneg
  have hprod :=
    weighted_gap_volume_bound hH gaps left right gapLength hlen hgap_nonneg
  have hprod_nonneg :
      0 ≤ ∏ i ∈ gaps, weightedIntervalMass H (left i) (right i) := by
    exact Finset.prod_nonneg fun i _hi =>
      hH.interval_mass_nonneg (left i) (right i)
  have hfirst_upper_nonneg :
      0 ≤ hH.Cmu * M * min 1 (ell * hyperWidth) :=
    weighted_local_upper_nonneg hH hhyper_nonneg
  exact mul_le_mul hfirst hprod hprod_nonneg hfirst_upper_nonneg

/-- Concrete ordered weighted gap cell.  The fields `length_le` and
`length_nonneg` are the deterministic geometry hypotheses used by the local
mass bound. -/
structure WeightedGapCell (ι : Type*) where
  gaps : Finset ι
  left : ι → ℝ
  right : ι → ℝ
  gapLength : ι → ℝ
  length_le :
    ∀ i ∈ gaps, intervalLength (left i) (right i) ≤ gapLength i
  length_nonneg : ∀ i ∈ gaps, 0 ≤ gapLength i

/-- Weighted volume of an ordered gap cell. -/
noncomputable def weightedOrderedGapCellVolume
    {ι : Type*} (H : ℝ → ℂ) (cell : WeightedGapCell ι) : ℝ :=
  ∏ i ∈ cell.gaps, weightedIntervalMass H (cell.left i) (cell.right i)

/-- Product upper bound supplied by local mass for an ordered gap cell. -/
noncomputable def weightedOrderedGapCellUpper
    {ι : Type*} {X : ℕ} {B ell M : ℝ} {H : ℝ → ℂ}
    (hH : HarperWeightAdmissible X B ell M H)
    (cell : WeightedGapCell ι) : ℝ :=
  ∏ i ∈ cell.gaps,
    hH.Cmu * M * min 1 (ell * cell.gapLength i)

/-- Named ordered gap-cell volume bound. -/
theorem weightedOrderedGapCellVolume_le
    {ι : Type*} {X : ℕ} {B ell M : ℝ} {H : ℝ → ℂ}
    (hH : HarperWeightAdmissible X B ell M H)
    (cell : WeightedGapCell ι) :
    weightedOrderedGapCellVolume H cell ≤
      weightedOrderedGapCellUpper hH cell := by
  exact
    weighted_gap_volume_bound hH cell.gaps cell.left cell.right cell.gapLength
      cell.length_le cell.length_nonneg

/-- Ordered gap cell with one additional resonant hyperplane restriction. -/
structure WeightedResonantGapCell (ι : Type*) where
  cell : WeightedGapCell ι
  hyperLeft : ℝ
  hyperRight : ℝ
  hyperWidth : ℝ
  hyper_length_le : intervalLength hyperLeft hyperRight ≤ hyperWidth
  hyper_nonneg : 0 ≤ hyperWidth

/-- Weighted volume of an ordered gap cell with a resonant hyperplane
restriction. -/
noncomputable def weightedResonantHyperplaneVolume
    {ι : Type*} (H : ℝ → ℂ) (cell : WeightedResonantGapCell ι) : ℝ :=
  weightedIntervalMass H cell.hyperLeft cell.hyperRight *
    weightedOrderedGapCellVolume H cell.cell

/-- Product upper bound for an ordered gap cell with a hyperplane restriction. -/
noncomputable def weightedResonantHyperplaneUpper
    {ι : Type*} {X : ℕ} {B ell M : ℝ} {H : ℝ → ℂ}
    (hH : HarperWeightAdmissible X B ell M H)
    (cell : WeightedResonantGapCell ι) : ℝ :=
  (hH.Cmu * M * min 1 (ell * cell.hyperWidth)) *
    weightedOrderedGapCellUpper hH cell.cell

/-- Named hyperplane-improved resonant gap-cell volume bound. -/
theorem weightedResonantHyperplaneVolume_le
    {ι : Type*} {X : ℕ} {B ell M : ℝ} {H : ℝ → ℂ}
    (hH : HarperWeightAdmissible X B ell M H)
    (cell : WeightedResonantGapCell ι) :
    weightedResonantHyperplaneVolume H cell ≤
      weightedResonantHyperplaneUpper hH cell := by
  exact
    weighted_gap_volume_resonant_bound hH
      cell.cell.gaps cell.cell.left cell.cell.right cell.cell.gapLength
      cell.hyperLeft cell.hyperRight cell.hyperWidth
      cell.cell.length_le cell.cell.length_nonneg
      cell.hyper_length_le cell.hyper_nonneg

end Volume

/-- Placeholder for the truncated pole factor `ζ_X(1+2it)`.  The upper and
lower pole estimates needed for admissibility are intentionally kept as fields
of `CompleteIncrementWeightAdmissibleInput`, not hidden in this definition. -/
opaque truncatedZetaPoleFactor (_X : ℕ) (_t : ℝ) : ℂ :=
  1

/-- Complete-model increment weight
`(exp(i t ell)-1) ζ_X(1+2it)`, with the finite zeta factor represented by the
named placeholder above. -/
noncomputable def completeIncrementWeight (X : ℕ) (ell : ℝ) : ℝ → ℂ :=
  fun t =>
    (Complex.exp (Complex.I * ((ell * t : ℝ) : ℂ)) - 1) *
      truncatedZetaPoleFactor X t

/-- Explicit analytic inputs proving that the complete-model increment
weight is admissible.  These fields are where the truncated-zeta upper/lower
pole estimates and local-mass estimates belong. -/
structure CompleteIncrementWeightAdmissibleInput
    (X : ℕ) (B ell M : ℝ) where
  a0 : ℝ
  a1 : ℝ
  Cmu : ℝ
  a0_pos : 0 < a0
  a1_nonneg : 0 ≤ a1
  Cmu_nonneg : 0 ≤ Cmu
  ell_nonneg : 0 ≤ ell
  M_nonneg : 0 ≤ M
  interval_mass_nonneg :
    ∀ a b : ℝ,
      0 ≤ weightedIntervalMass (completeIncrementWeight X ell) a b
  mass_lower : a0 * ell ≤ M
  mass_upper : M ≤ a1 * ell
  local_mass :
    ∀ a b : ℝ,
      weightedIntervalMass (completeIncrementWeight X ell) a b ≤
        Cmu * M * min 1 (ell * intervalLength a b)
  ell_polylog : ell ≤ (loglogNat X) ^ B

/-- A more granular admissibility input for the complete increment weight.
The local-mass bound is derived from a global mass upper bound and an `L∞`
bound, which is the deterministic argument used for
`B_ell(t) = (e^{it ell}-1) zeta_X(1+2it)`. -/
structure CompleteIncrementWeightBasicInput
    (X : ℕ) (B ell M : ℝ) where
  a0 : ℝ
  a1 : ℝ
  Kinf : ℝ
  Cmu : ℝ
  a0_pos : 0 < a0
  a1_nonneg : 0 ≤ a1
  Kinf_nonneg : 0 ≤ Kinf
  Cmu_nonneg : 0 ≤ Cmu
  ell_nonneg : 0 ≤ ell
  M_nonneg : 0 ≤ M
  interval_mass_nonneg :
    ∀ a b : ℝ,
      0 ≤ weightedIntervalMass (completeIncrementWeight X ell) a b
  mass_lower : a0 * ell ≤ M
  mass_upper : M ≤ a1 * ell
  interval_mass_le_mass :
    ∀ a b : ℝ,
      weightedIntervalMass (completeIncrementWeight X ell) a b ≤ M
  linfty_interval_mass :
    ∀ a b : ℝ,
      weightedIntervalMass (completeIncrementWeight X ell) a b ≤
        Kinf ^ 2 * ell ^ 2 * intervalLength a b
  Cmu_large : 1 ≤ Cmu
  Cmu_linf_large : Kinf ^ 2 ≤ Cmu * a0
  ell_polylog : ell ≤ (loglogNat X) ^ B

/-- The basic complete-increment input derives the local-mass estimate used by
`HarperWeight`: use the global mass bound for the `min = 1` side and the
`L∞` interval bound plus `a0 * ell <= M` for the small-interval side. -/
def completeIncrementWeightAdmissibleInput_of_basic
    {X : ℕ} {B ell M : ℝ}
    (h : CompleteIncrementWeightBasicInput X B ell M) :
    CompleteIncrementWeightAdmissibleInput X B ell M where
  a0 := h.a0
  a1 := h.a1
  Cmu := h.Cmu
  a0_pos := h.a0_pos
  a1_nonneg := h.a1_nonneg
  Cmu_nonneg := h.Cmu_nonneg
  ell_nonneg := h.ell_nonneg
  M_nonneg := h.M_nonneg
  interval_mass_nonneg := h.interval_mass_nonneg
  mass_lower := h.mass_lower
  mass_upper := h.mass_upper
  local_mass := by
    intro a b
    let len := intervalLength a b
    have hglobal :
        weightedIntervalMass (completeIncrementWeight X ell) a b ≤ h.Cmu * M := by
      exact (h.interval_mass_le_mass a b).trans
        (by
          calc
            M = 1 * M := by ring
            _ ≤ h.Cmu * M :=
              mul_le_mul_of_nonneg_right h.Cmu_large h.M_nonneg)
    have hlen_nonneg : 0 ≤ len := intervalLength_nonneg a b
    have hell_len_nonneg : 0 ≤ ell * len :=
      mul_nonneg h.ell_nonneg hlen_nonneg
    have hlinf_coeff : h.Kinf ^ 2 * ell ≤ h.Cmu * M := by
      calc
        h.Kinf ^ 2 * ell ≤ (h.Cmu * h.a0) * ell :=
          mul_le_mul_of_nonneg_right h.Cmu_linf_large h.ell_nonneg
        _ = h.Cmu * (h.a0 * ell) := by ring
        _ ≤ h.Cmu * M :=
          mul_le_mul_of_nonneg_left h.mass_lower h.Cmu_nonneg
    have hsmall :
        weightedIntervalMass (completeIncrementWeight X ell) a b ≤
          h.Cmu * M * (ell * intervalLength a b) := by
      have hlinf := h.linfty_interval_mass a b
      have hcoeff :
          h.Kinf ^ 2 * ell ^ 2 * len ≤ h.Cmu * M * (ell * len) := by
        calc
          h.Kinf ^ 2 * ell ^ 2 * len =
              (h.Kinf ^ 2 * ell) * (ell * len) := by ring
          _ ≤ (h.Cmu * M) * (ell * len) :=
              mul_le_mul_of_nonneg_right hlinf_coeff hell_len_nonneg
          _ = h.Cmu * M * (ell * len) := by ring
      exact hlinf.trans hcoeff
    by_cases hcase : ell * intervalLength a b ≤ 1
    · have hmin : min 1 (ell * intervalLength a b) =
          ell * intervalLength a b := min_eq_right hcase
      simpa [hmin] using hsmall
    · have hmin : min 1 (ell * intervalLength a b) = 1 := by
        exact min_eq_left (le_of_lt (lt_of_not_ge hcase))
      simpa [hmin] using hglobal
  ell_polylog := h.ell_polylog

/-- The complete increment weight is admissible once the explicit pole/mass
inputs have been supplied. -/
def completeIncrementWeight_admissible
    {X : ℕ} {B ell M : ℝ}
    (h : CompleteIncrementWeightAdmissibleInput X B ell M) :
    HarperWeightAdmissible X B ell M (completeIncrementWeight X ell) where
  a0 := h.a0
  a1 := h.a1
  Cmu := h.Cmu
  a0_pos := h.a0_pos
  a1_nonneg := h.a1_nonneg
  Cmu_nonneg := h.Cmu_nonneg
  ell_nonneg := h.ell_nonneg
  M_nonneg := h.M_nonneg
  interval_mass_nonneg := h.interval_mass_nonneg
  mass_lower := h.mass_lower
  mass_upper := h.mass_upper
  local_mass := h.local_mass
  ell_polylog := h.ell_polylog

/-- Abstract weighted covariance integral.  Its future Perron/Euler-product
identity should replace this placeholder body without changing downstream
interfaces. -/
opaque weightedCovarianceIntegral
    (_X _R : ℕ) (_H : ℝ → ℂ) (_alpha : ℕ → ℝ)
    (_omega : Omega) (_r _u : ℕ) : ℂ :=
  0

/-- Row high moment appearing in weighted Proposition 3. -/
noncomputable def weightedRowMoment
    (X R k : ℕ) (H : ℝ → ℂ) (alpha : ℕ → ℝ)
    (omega : Omega) (r : ℕ) : ℝ :=
  ∑ u ∈ Finset.range R,
    (‖weightedCovarianceIntegral X R H alpha omega r u‖) ^ (2 * k)

/-- The residual exponent in the weighted barrier-saving term.  The explicit
bookkeeping gives `Q - B - 15`; choosing `Q ≥ B + 115` recovers a residual
power of at least `100`. -/
noncomputable def weightedBarrierResidualExponent (B Q : ℝ) : ℝ :=
  Q - B - 15

theorem weightedBarrierResidualExponent_ge_100
    {B Q : ℝ} (hQ : B + 115 ≤ Q) :
    100 ≤ weightedBarrierResidualExponent B Q := by
  unfold weightedBarrierResidualExponent
  linarith

/-- Scalar gap cost after replacing ordinary volume by weighted local mass.
This is the formal version of
`(L / exp htilde) * min(1, ell exp h / L)`. -/
noncomputable def weightedGapCost (X : ℕ) (ell h htilde : ℝ) : ℝ :=
  (Real.log (X : ℝ) / Real.exp htilde) *
    min 1 (ell * Real.exp h / Real.log (X : ℝ))

/-- Deterministic GAP bookkeeping: if `ell <= P` and
`exp h / exp htilde <= E`, then the weighted gap cost is at most `P * E`.

In the paper audit, `P = (loglog X)^B` and
`E = exp 1 * (loglog X)^2`, giving a harmless polylogarithmic cost per gap. -/
theorem weightedGapCost_le_mul
    {X : ℕ} {ell h htilde P E : ℝ}
    (hlog_pos : 0 < Real.log (X : ℝ))
    (hell_nonneg : 0 ≤ ell)
    (hell_le : ell ≤ P)
    (hexp_ratio : Real.exp h / Real.exp htilde ≤ E) :
    weightedGapCost X ell h htilde ≤ P * E := by
  have hden_pos : 0 < Real.exp htilde := Real.exp_pos _
  have hnum_pos : 0 < Real.exp h := Real.exp_pos _
  have hfac_nonneg : 0 ≤ Real.log (X : ℝ) / Real.exp htilde :=
    div_nonneg hlog_pos.le hden_pos.le
  have hratio_nonneg : 0 ≤ Real.exp h / Real.exp htilde :=
    div_nonneg hnum_pos.le hden_pos.le
  have hP_nonneg : 0 ≤ P := hell_nonneg.trans hell_le
  have hcost_le :
      weightedGapCost X ell h htilde ≤
        ell * (Real.exp h / Real.exp htilde) := by
    unfold weightedGapCost
    have hmin :
        min 1 (ell * Real.exp h / Real.log (X : ℝ)) ≤
          ell * Real.exp h / Real.log (X : ℝ) :=
      min_le_right _ _
    calc
      (Real.log (X : ℝ) / Real.exp htilde) *
          min 1 (ell * Real.exp h / Real.log (X : ℝ))
          ≤
        (Real.log (X : ℝ) / Real.exp htilde) *
          (ell * Real.exp h / Real.log (X : ℝ)) :=
            mul_le_mul_of_nonneg_left hmin hfac_nonneg
      _ = ell * (Real.exp h / Real.exp htilde) := by
            field_simp [ne_of_gt hlog_pos, ne_of_gt hden_pos]
  exact hcost_le.trans
    (mul_le_mul hell_le hexp_ratio hratio_nonneg hP_nonneg)

/-- Scalar resonant hyperplane cost per resonant index.  In Harper's notation
this represents the factor `ell / (G * L^(2/3))` after the hyperplane-improved
volume estimate. -/
noncomputable def weightedResonantIndexCost
    (ell G Lpow : ℝ) : ℝ :=
  ell / (G * Lpow)

/-- Resonant index summation: if the number of resonant indices is at most
`C * k * G`, then summing the hyperplane-improved factor cancels the spacing
`G` and costs only `C * k * ell / Lpow`.

This is the formal scalar version of
`sum_{|m| <= C k G} ell / (G L^(2/3)) <= C k ell / L^(2/3)`. -/
theorem weightedResonantIndexSum_le
    {ι : Type*} (indices : Finset ι)
    {ell G Lpow C k : ℝ}
    (hell_nonneg : 0 ≤ ell)
    (hG_pos : 0 < G)
    (hLpow_pos : 0 < Lpow)
    (hcard : (indices.card : ℝ) ≤ C * k * G) :
    (∑ _m ∈ indices, weightedResonantIndexCost ell G Lpow) ≤
      C * k * ell / Lpow := by
  have hcost_nonneg : 0 ≤ weightedResonantIndexCost ell G Lpow := by
    unfold weightedResonantIndexCost
    exact div_nonneg hell_nonneg (mul_pos hG_pos hLpow_pos).le
  have hsum :
      (∑ _m ∈ indices, weightedResonantIndexCost ell G Lpow) =
        (indices.card : ℝ) * weightedResonantIndexCost ell G Lpow := by
    simp
  rw [hsum]
  have hmul :
      (indices.card : ℝ) * weightedResonantIndexCost ell G Lpow ≤
        (C * k * G) * weightedResonantIndexCost ell G Lpow :=
    mul_le_mul_of_nonneg_right hcard hcost_nonneg
  calc
    (indices.card : ℝ) * weightedResonantIndexCost ell G Lpow
        ≤ (C * k * G) * weightedResonantIndexCost ell G Lpow := hmul
    _ = C * k * ell / Lpow := by
      unfold weightedResonantIndexCost
      field_simp [ne_of_gt hG_pos, ne_of_gt hLpow_pos]

/-- Non-resonant part of the weighted Proposition 3 row bound. -/
noncomputable def weightedProp3NonresonantBound
    (X R k : ℕ) (M C_B Cmu : ℝ) : ℝ :=
  (R : ℝ) * M ^ (2 * k) *
    ((Real.log (X : ℝ)) ^ ((2 : ℝ) / 3) / (R : ℝ) *
      (C_B * Cmu * (loglogNat X) ^ C_B) ^ (2 * k))

/-- Resonant `L^{-1/3}` part of the weighted Proposition 3 row bound after
the explicit `k ell / L^(2/3)` weighted loss and Markov multiplier have been
absorbed into the high-moment base. -/
noncomputable def weightedProp3ResonantBound
    (X R k : ℕ) (M C_B Cmu : ℝ) : ℝ :=
  (R : ℝ) * M ^ (2 * k) *
    ((Real.log (X : ℝ)) ^ (-(1 : ℝ) / 3) *
      (C_B * Cmu * (k : ℝ) ^ 29 * (loglogNat X) ^ C_B) ^ (2 * k))

/-- Barrier-saving part of the weighted Proposition 3 row bound with the
honest residual exponent `Q - B - 15`. -/
noncomputable def weightedProp3BarrierBound
    (X R k : ℕ) (B Q M C_B Cmu : ℝ) : ℝ :=
  (R : ℝ) * M ^ (2 * k) *
    ((C_B * Cmu * (k : ℝ) ^ 29 /
        (loglogNat X) ^ (weightedBarrierResidualExponent B Q)) ^ (2 * k))

/-- Explicit weighted Proposition 3 row bound. -/
noncomputable def weightedProp3ExplicitRowBound
    (X R k : ℕ) (B Q M C_B Cmu : ℝ) : ℝ :=
  weightedProp3NonresonantBound X R k M C_B Cmu +
    weightedProp3ResonantBound X R k M C_B Cmu +
      weightedProp3BarrierBound X R k B Q M C_B Cmu

/-- Shell energy appearing in the non-resonant part of Harper's proof.
Future work should replace this placeholder by the integral
`∫_{N <= |t| <= N+1} |F_X^square(1/2+it)|^2 |H(t)|^2 dt`. -/
opaque weightedEnergyShellIntegral
    (_X : ℕ) (_H : ℝ → ℂ) (_omega : Omega) (_N : ℕ) : ℝ :=
  0

/-- Weighted non-resonant shell-energy term before collapsing the shell
energies to the explicit row bound.  This models the first term in Harper's
Proposition 3 after the prime-kernel estimate and shell split. -/
noncomputable def weightedNonresonantEnergyTerm
    (X k : ℕ) (H : ℝ → ℂ) (shells : Finset ℕ)
    (omega : Omega) : ℝ :=
  (Real.log (X : ℝ)) ^ ((2 : ℝ) / 3) *
    ∑ N ∈ shells,
      (1 / (((N : ℝ) ^ 2) + 1)) *
        (((logloglogNat X) / Real.log (X : ℝ) *
            weightedEnergyShellIntegral X H omega N) ^ (2 * k))

/-- Non-resonant energy certificate.  This is the first Harper proof subgoal:
the shell energy event collapses the non-resonant shell term to the explicit
weighted Proposition 3 non-resonant bound. -/
structure WeightedNonresonantEnergyCertificate where
  X : ℕ
  R : ℕ
  k : ℕ
  B : ℝ
  ell : ℝ
  M : ℝ
  C_B : ℝ
  H : ℝ → ℂ
  shells : Finset ℕ
  energyGood : Set Omega
  failEnergy : ℝ≥0∞
  weight : HarperWeight X B ell M H
  energy_bound :
    ∀ omega ∈ energyGood,
      weightedNonresonantEnergyTerm X k H shells omega ≤
        weightedProp3NonresonantBound X R k M C_B weight.Cmu
  prob_energy_compl : mu energyGoodᶜ ≤ failEnergy

/-- The non-resonant energy certificate supplies the corresponding row
contribution bound when that contribution is taken to be the shell-energy
term. -/
theorem weightedNonresonant_bound_of_energyCertificate
    (h : WeightedNonresonantEnergyCertificate) :
    ∀ omega ∈ h.energyGood, ∀ _r : ℕ, _r < h.R →
      weightedNonresonantEnergyTerm h.X h.k h.H h.shells omega ≤
        weightedProp3NonresonantBound h.X h.R h.k h.M h.C_B h.weight.Cmu := by
  intro omega homega _r _hr
  exact h.energy_bound omega homega

/-- Abstract weighted resonant ordered-gap contribution.  This names the
quantity obtained after Harper's resonant reduction to ordered gap cells and
the Euler-product/barrier calculation. -/
opaque weightedResonantGapContribution
    (_X _R _k : ℕ) (_B _Q _ell _M _G : ℝ)
    (_H : ℝ → ℂ) (_alpha : ℕ → ℝ)
    (_omega : Omega) (_r : ℕ) : ℝ :=
  0

/-- Abstract weighted low-barrier contribution.  This is the part of the
ordered-gap sum where Harper's barrier gives the strong negative power of
`log log X`. -/
opaque weightedBarrierGapContribution
    (_X _R _k : ℕ) (_B _Q _ell _M _G : ℝ)
    (_H : ℝ → ℂ) (_alpha : ℕ → ℝ)
    (_omega : Omega) (_r : ℕ) : ℝ :=
  0

/-- Resonant ordered-gap certificate.  This is the formal target for the
weighted version of Harper's resonant argument: the weighted volume estimates,
Euler-product moment calculation, large-pair dichotomy, and low-barrier
saving must prove the two displayed contribution bounds. -/
structure WeightedResonantGapCertificate where
  X : ℕ
  R : ℕ
  k : ℕ
  B : ℝ
  Q : ℝ
  ell : ℝ
  M : ℝ
  G : ℝ
  C_B : ℝ
  H : ℝ → ℂ
  alpha : ℕ → ℝ
  resonantGood : Set Omega
  failResonant : ℝ≥0∞
  weight : HarperWeight X B ell M H
  grid_spacing : ∀ r : ℕ, alpha r = alpha 0 + (r : ℝ) * G
  barrier_large : B + 115 ≤ Q
  large_pair_bound :
    ∀ omega ∈ resonantGood, ∀ r : ℕ, r < R →
      weightedResonantGapContribution X R k B Q ell M G H alpha omega r ≤
        weightedProp3ResonantBound X R k M C_B weight.Cmu
  low_barrier_bound :
    ∀ omega ∈ resonantGood, ∀ r : ℕ, r < R →
      weightedBarrierGapContribution X R k B Q ell M G H alpha omega r ≤
        weightedProp3BarrierBound X R k B Q M C_B weight.Cmu
  prob_resonant_compl : mu resonantGoodᶜ ≤ failResonant

/-- The resonant gap certificate supplies the `L^{-1/3}` resonant contribution
bound needed by the proof-step certificate. -/
theorem weightedResonant_bound_of_gapCertificate
    (h : WeightedResonantGapCertificate) :
    ∀ omega ∈ h.resonantGood, ∀ r : ℕ, r < h.R →
      weightedResonantGapContribution
        h.X h.R h.k h.B h.Q h.ell h.M h.G h.H h.alpha omega r ≤
        weightedProp3ResonantBound h.X h.R h.k h.M h.C_B h.weight.Cmu := by
  intro omega homega r hr
  exact h.large_pair_bound omega homega r hr

/-- The resonant gap certificate supplies the strong barrier-saving
contribution bound needed by the proof-step certificate. -/
theorem weightedBarrier_bound_of_gapCertificate
    (h : WeightedResonantGapCertificate) :
    ∀ omega ∈ h.resonantGood, ∀ r : ℕ, r < h.R →
      weightedBarrierGapContribution
        h.X h.R h.k h.B h.Q h.ell h.M h.G h.H h.alpha omega r ≤
        weightedProp3BarrierBound h.X h.R h.k h.B h.Q h.M h.C_B h.weight.Cmu := by
  intro omega homega r hr
  exact h.low_barrier_bound omega homega r hr

/-- Bad neighbours at threshold `rho * M`. -/
noncomputable def weightedBadNeighborSet
    (X R : ℕ) (H : ℝ → ℂ) (alpha : ℕ → ℝ)
    (rho M : ℝ) (omega : Omega) (r : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range R).filter fun u =>
      rho * M < ‖weightedCovarianceIntegral X R H alpha omega r u‖

/-- Real-valued bad degree. -/
noncomputable def weightedBadDegreeReal
    (X R : ℕ) (H : ℝ → ℂ) (alpha : ℕ → ℝ)
    (rho M : ℝ) (omega : Omega) (r : ℕ) : ℝ :=
  ((weightedBadNeighborSet X R H alpha rho M omega r).card : ℝ)

/-- Actual increment-covariance bad neighbours for a row of increment
intervals.  This is the downstream object that the Perron/Euler-product
identity must control using `weightedCovarianceIntegral`. -/
noncomputable def incrementCovarianceBadNeighborSet
    (X R : ℕ) (leftEnd rightEnd : ℕ → ℕ)
    (rho V : ℝ) (omega : Omega) (r : ℕ) : Finset ℕ := by
  classical
  exact
    (Finset.range R).filter fun u =>
      rho * V <
        |largePrimeIncrementCovariance omega X
          (leftEnd r) (rightEnd r) (leftEnd u) (rightEnd u)|

/-- Increment covariance is symmetric in the two increment intervals. -/
theorem largePrimeIncrementCovariance_comm
    (omega : Omega) (X M N P Q : ℕ) :
    largePrimeIncrementCovariance omega X M N P Q =
      largePrimeIncrementCovariance omega X P Q M N := by
  classical
  unfold largePrimeIncrementCovariance largePrimeIncrementPairSupport
  rw [Finset.union_comm]
  refine Finset.sum_congr rfl fun r _hr => ?_
  ring

/-- Actual increment-covariance bad-neighbour membership is symmetric once
both endpoints are inside the finite row range. -/
theorem incrementCovarianceBadNeighborSet_symm_mem
    {X R : ℕ} {leftEnd rightEnd : ℕ → ℕ}
    {rho V : ℝ} {omega : Omega} {r u : ℕ}
    (hr : r < R)
    (hu : u ∈ incrementCovarianceBadNeighborSet
      X R leftEnd rightEnd rho V omega r) :
    r ∈ incrementCovarianceBadNeighborSet
      X R leftEnd rightEnd rho V omega u := by
  classical
  have hbad :
      rho * V <
        |largePrimeIncrementCovariance omega X
          (leftEnd r) (rightEnd r) (leftEnd u) (rightEnd u)| :=
    (Finset.mem_filter.mp hu).2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr hr, by
      simpa [largePrimeIncrementCovariance_comm] using hbad⟩

/-- Real-valued actual increment-covariance bad degree. -/
noncomputable def incrementCovarianceBadDegreeReal
    (X R : ℕ) (leftEnd rightEnd : ℕ → ℕ)
    (rho V : ℝ) (omega : Omega) (r : ℕ) : ℝ :=
  ((incrementCovarianceBadNeighborSet X R leftEnd rightEnd rho V omega r).card : ℝ)

/-- Event that actual increment covariance bad degrees are controlled on all
rows by a real-valued threshold. -/
def incrementCovarianceBadDegreeEvent
    (X R : ℕ) (leftEnd rightEnd : ℕ → ℕ)
    (rho V degreeBound : ℝ) : Set Omega :=
  {omega |
    ∀ r : ℕ, r < R →
      incrementCovarianceBadDegreeReal X R leftEnd rightEnd rho V omega r ≤
        degreeBound}

/-- Natural-valued bad-degree event for finite graph pruning. -/
def incrementCovarianceBadDegreeNatEvent
    (X R : ℕ) (leftEnd rightEnd : ℕ → ℕ)
    (rho V : ℝ) (D : ℕ) : Set Omega :=
  {omega |
    ∀ r : ℕ, r < R →
      (incrementCovarianceBadNeighborSet X R leftEnd rightEnd rho V omega r).card ≤ D}

/-- A real-valued bad-degree bound implies a natural-valued one after choosing
a natural ceiling bound. -/
theorem incrementCovarianceBadDegreeNatEvent_of_real
    {X R D : ℕ} {leftEnd rightEnd : ℕ → ℕ}
    {rho V degreeBound : ℝ} {omega : Omega}
    (hceil : degreeBound ≤ (D : ℝ))
    (hreal : omega ∈ incrementCovarianceBadDegreeEvent
      X R leftEnd rightEnd rho V degreeBound) :
    omega ∈ incrementCovarianceBadDegreeNatEvent
      X R leftEnd rightEnd rho V D := by
  intro r hr
  have hrow := hreal r hr
  have hcast :
      ((incrementCovarianceBadNeighborSet
        X R leftEnd rightEnd rho V omega r).card : ℝ) ≤ (D : ℝ) :=
    hrow.trans hceil
  exact_mod_cast hcast

private def pairwiseNoBadOn
    (base : Finset ℕ) (bad : ℕ → ℕ → Prop) (s : Finset ℕ) : Prop :=
  s ⊆ base ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ bad a b

private theorem exists_large_pairwiseNoBadOn_of_bounded_degree
    {base : Finset ℕ} {bad : ℕ → ℕ → Prop} [DecidableRel bad]
    {D : ℕ}
    (hsymm : ∀ a ∈ base, ∀ b ∈ base, bad a b → bad b a)
    (hdeg : ∀ a ∈ base, ((base.filter fun b => bad a b).card ≤ D)) :
    ∃ s : Finset ℕ,
      pairwiseNoBadOn base bad s ∧ base.card ≤ (D + 1) * s.card := by
  classical
  let candidates := base.powerset.filter fun s => pairwiseNoBadOn base bad s
  have hcandidates_nonempty : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, pairwiseNoBadOn]
  obtain ⟨s, hs_cand, hs_max⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates_nonempty
  have hs_good : pairwiseNoBadOn base bad s :=
    (Finset.mem_filter.mp hs_cand).2
  have hs_subset : s ⊆ base := hs_good.1
  have hs_nobad : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ bad a b := hs_good.2
  let neighborUnion := s.biUnion fun a => base.filter fun b => bad a b
  have hcover : base ⊆ s ∪ neighborUnion := by
    intro v hv
    by_cases hv_s : v ∈ s
    · exact Finset.mem_union.mpr (Or.inl hv_s)
    · by_contra hv_not
      have hnot_neighbor : ∀ a ∈ s, ¬ bad a v := by
        intro a ha hab
        exact hv_not (Finset.mem_union.mpr (Or.inr
          (Finset.mem_biUnion.mpr
            ⟨a, ha, Finset.mem_filter.mpr ⟨hv, hab⟩⟩)))
      have hnot_v_neighbor : ∀ a ∈ s, ¬ bad v a := by
        intro a ha hva
        exact hnot_neighbor a ha (hsymm v hv a (hs_subset ha) hva)
      have hinsert_good : pairwiseNoBadOn base bad (insert v s) := by
        constructor
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx_s
          · exact hv
          · exact hs_subset hx_s
        · intro a ha b hb hne hab
          rcases Finset.mem_insert.mp ha with rfl | ha_s
          · rcases Finset.mem_insert.mp hb with rfl | hb_s
            · exact hne rfl
            · exact hnot_v_neighbor b hb_s hab
          · rcases Finset.mem_insert.mp hb with rfl | hb_s
            · exact hnot_neighbor a ha_s hab
            · exact hs_nobad a ha_s b hb_s hne hab
      have hinsert_cand : insert v s ∈ candidates := by
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr hinsert_good.1, hinsert_good⟩
      have hle := hs_max (insert v s) hinsert_cand
      have hcard_insert : (insert v s).card = s.card + 1 :=
        Finset.card_insert_of_notMem hv_s
      omega
  have hcard_cover : base.card ≤ (s ∪ neighborUnion).card :=
    Finset.card_le_card hcover
  have hcard_union :
      (s ∪ neighborUnion).card ≤ s.card + neighborUnion.card :=
    Finset.card_union_le _ _
  have hneighbor_card : neighborUnion.card ≤ s.card * D := by
    exact Finset.card_biUnion_le_card_mul s
      (fun a => base.filter fun b => bad a b) D
      (by
        intro a ha
        exact hdeg a (hs_subset ha))
  refine ⟨s, hs_good, ?_⟩
  calc
    base.card ≤ (s ∪ neighborUnion).card := hcard_cover
    _ ≤ s.card + neighborUnion.card := hcard_union
    _ ≤ s.card + s.card * D := Nat.add_le_add_left hneighbor_card s.card
    _ = D * s.card + s.card := by rw [Nat.mul_comm s.card D, Nat.add_comm]
    _ = (D + 1) * s.card := by rw [Nat.add_mul, Nat.one_mul]

/-- Counting step from a row high-moment bound to a bad-degree bound. -/
theorem weighted_badDegreeReal_le_of_rowMoment
    {X R k : ℕ} {H : ℝ → ℂ} {alpha : ℕ → ℝ}
    {rho M rowBound : ℝ} {omega : Omega} {r : ℕ}
    (hrhoM : 0 < rho * M)
    (hrow :
      weightedRowMoment X R k H alpha omega r ≤ rowBound) :
    weightedBadDegreeReal X R H alpha rho M omega r ≤
      rowBound / (rho * M) ^ (2 * k) := by
  classical
  let bad := weightedBadNeighborSet X R H alpha rho M omega r
  let moment : ℕ → ℝ := fun u =>
    (‖weightedCovarianceIntegral X R H alpha omega r u‖) ^ (2 * k)
  have hbad_subset : bad ⊆ Finset.range R := by
    intro u hu
    exact (Finset.mem_filter.mp hu).1
  have h_each :
      ∀ u ∈ bad, (rho * M) ^ (2 * k) ≤ moment u := by
    intro u hu
    have hlt :
        rho * M <
          ‖weightedCovarianceIntegral X R H alpha omega r u‖ :=
      (Finset.mem_filter.mp hu).2
    exact pow_le_pow_left₀ hrhoM.le (le_of_lt hlt) (2 * k)
  have hsum_bad :
      (bad.card : ℝ) * (rho * M) ^ (2 * k) ≤
        ∑ u ∈ bad, moment u := by
    calc
      (bad.card : ℝ) * (rho * M) ^ (2 * k)
          = ∑ _u ∈ bad, (rho * M) ^ (2 * k) := by
            simp
      _ ≤ ∑ u ∈ bad, moment u :=
            Finset.sum_le_sum h_each
  have hsum_subset :
      ∑ u ∈ bad, moment u ≤ ∑ u ∈ Finset.range R, moment u :=
    Finset.sum_le_sum_of_subset_of_nonneg hbad_subset (by
      intro u _hu _hnot
      exact pow_nonneg (norm_nonneg _) _)
  have htotal :
      (bad.card : ℝ) * (rho * M) ^ (2 * k) ≤ rowBound := by
    exact (hsum_bad.trans hsum_subset).trans hrow
  have hden_pos : 0 < (rho * M) ^ (2 * k) :=
    pow_pos hrhoM _
  rw [weightedBadDegreeReal]
  change (bad.card : ℝ) ≤ rowBound / (rho * M) ^ (2 * k)
  rw [le_div_iff₀ hden_pos]
  exact htotal

/-- If the Perron/Euler-product reduction bounds actual increment covariance
by the weighted covariance integral plus an error, and the weighted threshold
has that much slack, then actual bad neighbours are a subset of weighted bad
neighbours. -/
theorem incrementCovarianceBadNeighborSet_subset_weighted
    {X R : ℕ} {H : ℝ → ℂ} {alpha : ℕ → ℝ}
    {leftEnd rightEnd : ℕ → ℕ}
    {rhoActual V rhoWeighted M err : ℝ}
    {omega : Omega} {r : ℕ}
    (hslack : rhoWeighted * M + err ≤ rhoActual * V)
    (hperron :
      ∀ u : ℕ, u < R →
        |largePrimeIncrementCovariance omega X
          (leftEnd r) (rightEnd r) (leftEnd u) (rightEnd u)| ≤
          ‖weightedCovarianceIntegral X R H alpha omega r u‖ + err) :
    incrementCovarianceBadNeighborSet X R leftEnd rightEnd rhoActual V omega r ⊆
      weightedBadNeighborSet X R H alpha rhoWeighted M omega r := by
  classical
  intro u hu
  have hu_range : u ∈ Finset.range R := (Finset.mem_filter.mp hu).1
  have hu_lt : u < R := Finset.mem_range.mp hu_range
  have hbad :
      rhoActual * V <
        |largePrimeIncrementCovariance omega X
          (leftEnd r) (rightEnd r) (leftEnd u) (rightEnd u)| :=
    (Finset.mem_filter.mp hu).2
  have hbound := hperron u hu_lt
  have hweighted_lt :
      rhoWeighted * M <
        ‖weightedCovarianceIntegral X R H alpha omega r u‖ := by
    have hchain :
        rhoWeighted * M + err <
          ‖weightedCovarianceIntegral X R H alpha omega r u‖ + err :=
      lt_of_le_of_lt hslack (lt_of_lt_of_le hbad hbound)
    linarith
  exact Finset.mem_filter.mpr ⟨hu_range, hweighted_lt⟩

/-- Bad-degree transfer from weighted covariance integrals to actual increment
covariances under a Perron reduction with threshold slack. -/
theorem incrementCovarianceBadDegree_le_weightedBadDegree
    {X R : ℕ} {H : ℝ → ℂ} {alpha : ℕ → ℝ}
    {leftEnd rightEnd : ℕ → ℕ}
    {rhoActual V rhoWeighted M err : ℝ}
    {omega : Omega} {r : ℕ}
    (hslack : rhoWeighted * M + err ≤ rhoActual * V)
    (hperron :
      ∀ u : ℕ, u < R →
        |largePrimeIncrementCovariance omega X
          (leftEnd r) (rightEnd r) (leftEnd u) (rightEnd u)| ≤
          ‖weightedCovarianceIntegral X R H alpha omega r u‖ + err) :
    incrementCovarianceBadDegreeReal X R leftEnd rightEnd rhoActual V omega r ≤
      weightedBadDegreeReal X R H alpha rhoWeighted M omega r := by
  unfold incrementCovarianceBadDegreeReal weightedBadDegreeReal
  exact_mod_cast
    Finset.card_le_card
      (incrementCovarianceBadNeighborSet_subset_weighted
        (X := X) (R := R) (H := H) (alpha := alpha)
        (leftEnd := leftEnd) (rightEnd := rightEnd)
        (rhoActual := rhoActual) (V := V)
        (rhoWeighted := rhoWeighted) (M := M) (err := err)
        (omega := omega) (r := r) hslack hperron)

/-- Weighted Proposition 3 certificate.  The load-bearing analytic input is
`moment_row_bound`; all later bad-degree consequences are deterministic. -/
structure WeightedHarperProp3Certificate where
  X : ℕ
  R : ℕ
  k : ℕ
  B : ℝ
  ell : ℝ
  M : ℝ
  G : ℝ
  rho : ℝ
  H : ℝ → ℂ
  alpha : ℕ → ℝ
  good : Set Omega
  fail : ℝ≥0∞
  rowBound : ℝ
  degreeBound : ℝ
  weight_admissible : HarperWeightAdmissible X B ell M H
  grid_spacing : ∀ r : ℕ, alpha r = alpha 0 + (r : ℝ) * G
  rhoM_pos : 0 < rho * M
  moment_row_bound :
    ∀ omega ∈ good, ∀ r : ℕ, r < R →
      weightedRowMoment X R k H alpha omega r ≤ rowBound
  rowBound_degree :
    rowBound / (rho * M) ^ (2 * k) ≤ degreeBound
  prob_good_compl : mu goodᶜ ≤ fail

/-- Pairwise-good covariance event for a concrete pruned submesh. -/
def incrementCovariancePairwiseGoodEvent
    (X : ℕ) (leftEnd rightEnd : ℕ → ℕ)
    (rho V : ℝ) (indexSet : Finset ℕ) : Set Omega :=
  {omega |
    ∀ r ∈ indexSet, ∀ u ∈ indexSet, r ≠ u →
      |largePrimeIncrementCovariance omega X
        (leftEnd r) (rightEnd r) (leftEnd u) (rightEnd u)| ≤ rho * V}

/-- A pruned set has pairwise-good covariance if it contains no actual
bad-neighbour edge. -/
theorem incrementCovariancePairwiseGood_of_no_bad_pairs
    {X R : ℕ} {leftEnd rightEnd : ℕ → ℕ}
    {rho V : ℝ} {indexSet : Finset ℕ} {omega : Omega}
    (hsub : indexSet ⊆ Finset.range R)
    (hno_bad :
      ∀ r ∈ indexSet, ∀ u ∈ indexSet, r ≠ u →
        u ∉ incrementCovarianceBadNeighborSet
          X R leftEnd rightEnd rho V omega r) :
    omega ∈ incrementCovariancePairwiseGoodEvent
      X leftEnd rightEnd rho V indexSet := by
  intro r hr u hu hne
  have hu_range : u ∈ Finset.range R := hsub hu
  have hnot := hno_bad r hr u hu hne
  have hle :
      ¬ rho * V <
        |largePrimeIncrementCovariance omega X
          (leftEnd r) (rightEnd r) (leftEnd u) (rightEnd u)| := by
    intro hlt
    exact hnot (Finset.mem_filter.mpr ⟨hu_range, hlt⟩)
  exact le_of_not_gt hle

/-- Existence event for a pruned submesh with controlled pairwise increment
covariances.  The submesh may depend on the small-prime environment; this is
the right finite target after a bad-degree/pruning argument. -/
def incrementCovariancePrunedPairwiseEvent
    (X R : ℕ) (leftEnd rightEnd : ℕ → ℕ)
    (rho V : ℝ) (K : ℕ) : Set Omega :=
  {omega |
    ∃ indexSet : Finset ℕ,
      indexSet ⊆ Finset.range R ∧
        K ≤ indexSet.card ∧
          omega ∈ incrementCovariancePairwiseGoodEvent
            X leftEnd rightEnd rho V indexSet}

/-- A concrete no-bad-pair submesh witnesses the pruned pairwise-good event. -/
theorem incrementCovariancePrunedPairwiseEvent_of_no_bad_pairs
    {X R K : ℕ} {leftEnd rightEnd : ℕ → ℕ}
    {rho V : ℝ} {indexSet : Finset ℕ} {omega : Omega}
    (hsub : indexSet ⊆ Finset.range R)
    (hcard : K ≤ indexSet.card)
    (hno_bad :
      ∀ r ∈ indexSet, ∀ u ∈ indexSet, r ≠ u →
        u ∉ incrementCovarianceBadNeighborSet
          X R leftEnd rightEnd rho V omega r) :
    omega ∈ incrementCovariancePrunedPairwiseEvent
      X R leftEnd rightEnd rho V K := by
  refine ⟨indexSet, hsub, hcard, ?_⟩
  exact incrementCovariancePairwiseGood_of_no_bad_pairs
    (X := X) (R := R) (leftEnd := leftEnd) (rightEnd := rightEnd)
    (rho := rho) (V := V) (indexSet := indexSet) (omega := omega)
    hsub hno_bad

/-- Bounded symmetric bad degree on `range R` gives a large pruned submesh.

This is the finite greedy-pruning step specialized to actual increment
covariance bad neighbours.  The size hypothesis is intentionally arithmetic:
if `(D + 1) * K <= R`, the retained submesh has at least `K` points. -/
theorem incrementCovariancePrunedPairwiseEvent_of_badDegreeNatEvent
    {X R K D : ℕ} {leftEnd rightEnd : ℕ → ℕ}
    {rho V : ℝ} {omega : Omega}
    (hsize : (D + 1) * K ≤ R)
    (hdeg : omega ∈ incrementCovarianceBadDegreeNatEvent
      X R leftEnd rightEnd rho V D) :
    omega ∈ incrementCovariancePrunedPairwiseEvent
      X R leftEnd rightEnd rho V K := by
  classical
  let base : Finset ℕ := Finset.range R
  let bad : ℕ → ℕ → Prop := fun r u =>
    u ∈ incrementCovarianceBadNeighborSet
      X R leftEnd rightEnd rho V omega r
  have hsymm : ∀ a ∈ base, ∀ b ∈ base, bad a b → bad b a := by
    intro a ha b _hb hab
    exact incrementCovarianceBadNeighborSet_symm_mem
      (X := X) (R := R) (leftEnd := leftEnd) (rightEnd := rightEnd)
      (rho := rho) (V := V) (omega := omega)
      (r := a) (u := b) (Finset.mem_range.mp ha) hab
  have hdegree : ∀ a ∈ base, ((base.filter fun b => bad a b).card ≤ D) := by
    intro a ha
    have hrow := hdeg a (Finset.mem_range.mp ha)
    have hfilter_eq :
        (base.filter fun b => bad a b) =
          incrementCovarianceBadNeighborSet
            X R leftEnd rightEnd rho V omega a := by
      ext b
      simp [base, bad, incrementCovarianceBadNeighborSet]
    rw [hfilter_eq]
    exact hrow
  obtain ⟨s, hs_good, hlarge⟩ :=
    exists_large_pairwiseNoBadOn_of_bounded_degree
      (base := base) (bad := bad) (D := D) hsymm hdegree
  have hcard : K ≤ s.card := by
    have hmul : (D + 1) * K ≤ (D + 1) * s.card := by
      exact hsize.trans (by simpa [base] using hlarge)
    exact Nat.le_of_mul_le_mul_left hmul (Nat.succ_pos D)
  exact incrementCovariancePrunedPairwiseEvent_of_no_bad_pairs
    (X := X) (R := R) (K := K)
    (leftEnd := leftEnd) (rightEnd := rightEnd)
    (rho := rho) (V := V) (indexSet := s) (omega := omega)
    (by simpa [base] using hs_good.1)
    hcard
    (by
      intro r hr u hu hne hubad
      exact hs_good.2 r hr u hu hne hubad)

/-- Probability version of the finite pruning step. -/
theorem prob_incrementCovariancePrunedPairwiseEvent_compl_le_of_badDegreeNat
    {X R K D : ℕ} {leftEnd rightEnd : ℕ → ℕ}
    {rho V : ℝ} {fail : ℝ≥0∞}
    (hsize : (D + 1) * K ≤ R)
    (hprob :
      mu (incrementCovarianceBadDegreeNatEvent
        X R leftEnd rightEnd rho V D)ᶜ ≤ fail) :
    mu (incrementCovariancePrunedPairwiseEvent
        X R leftEnd rightEnd rho V K)ᶜ ≤ fail := by
  have hsub :
      (incrementCovariancePrunedPairwiseEvent
        X R leftEnd rightEnd rho V K)ᶜ ⊆
          (incrementCovarianceBadDegreeNatEvent
            X R leftEnd rightEnd rho V D)ᶜ := by
    intro omega hnot hdeg
    exact hnot
      (incrementCovariancePrunedPairwiseEvent_of_badDegreeNatEvent
        (X := X) (R := R) (K := K) (D := D)
        (leftEnd := leftEnd) (rightEnd := rightEnd)
        (rho := rho) (V := V) (omega := omega)
        hsize hdeg)
  exact (measure_mono hsub).trans hprob

/-- Probability version using the existing real-valued bad-degree event. -/
theorem prob_incrementCovariancePrunedPairwiseEvent_compl_le_of_badDegreeReal
    {X R K D : ℕ} {leftEnd rightEnd : ℕ → ℕ}
    {rho V degreeBound : ℝ} {fail : ℝ≥0∞}
    (hsize : (D + 1) * K ≤ R)
    (hceil : degreeBound ≤ (D : ℝ))
    (hprob :
      mu (incrementCovarianceBadDegreeEvent
        X R leftEnd rightEnd rho V degreeBound)ᶜ ≤ fail) :
    mu (incrementCovariancePrunedPairwiseEvent
        X R leftEnd rightEnd rho V K)ᶜ ≤ fail := by
  have hsub :
      (incrementCovariancePrunedPairwiseEvent
        X R leftEnd rightEnd rho V K)ᶜ ⊆
          (incrementCovarianceBadDegreeEvent
            X R leftEnd rightEnd rho V degreeBound)ᶜ := by
    intro omega hnot hreal
    exact hnot
      (incrementCovariancePrunedPairwiseEvent_of_badDegreeNatEvent
        (X := X) (R := R) (K := K) (D := D)
        (leftEnd := leftEnd) (rightEnd := rightEnd)
        (rho := rho) (V := V) (omega := omega)
        hsize
        (incrementCovarianceBadDegreeNatEvent_of_real
          (X := X) (R := R) (D := D)
          (leftEnd := leftEnd) (rightEnd := rightEnd)
          (rho := rho) (V := V) (degreeBound := degreeBound)
          (omega := omega) hceil hreal))
  exact (measure_mono hsub).trans hprob

/-- Finite pruning certificate for the increment covariance graph.

This deliberately isolates the graph-theoretic selection step.  Later work
can prove `select_*` from a bounded bad-degree event by greedy pruning, while
the downstream probabilistic consequence below is already deterministic. -/
structure IncrementCovariancePrunedSubmeshCertificate where
  X : ℕ
  R : ℕ
  K : ℕ
  leftEnd : ℕ → ℕ
  rightEnd : ℕ → ℕ
  rho : ℝ
  V : ℝ
  good : Set Omega
  fail : ℝ≥0∞
  select : Omega → Finset ℕ
  select_subset_range :
    ∀ omega ∈ good, select omega ⊆ Finset.range R
  select_card_lower :
    ∀ omega ∈ good, K ≤ (select omega).card
  select_no_bad_pairs :
    ∀ omega ∈ good,
      ∀ r ∈ select omega, ∀ u ∈ select omega, r ≠ u →
        u ∉ incrementCovarianceBadNeighborSet
          X R leftEnd rightEnd rho V omega r
  prob_good_compl : mu goodᶜ ≤ fail

/-- The finite pruning certificate produces a pruned pairwise-good covariance
event on its good set. -/
theorem incrementCovariancePrunedPairwiseEvent_of_pruningCertificate
    (h : IncrementCovariancePrunedSubmeshCertificate) :
    h.good ⊆
      incrementCovariancePrunedPairwiseEvent
        h.X h.R h.leftEnd h.rightEnd h.rho h.V h.K := by
  intro omega hgood
  exact incrementCovariancePrunedPairwiseEvent_of_no_bad_pairs
    (X := h.X) (R := h.R) (K := h.K)
    (leftEnd := h.leftEnd) (rightEnd := h.rightEnd)
    (rho := h.rho) (V := h.V)
    (indexSet := h.select omega) (omega := omega)
    (h.select_subset_range omega hgood)
    (h.select_card_lower omega hgood)
    (h.select_no_bad_pairs omega hgood)

/-- Probability consequence of the finite pruning certificate. -/
theorem prob_incrementCovariancePrunedPairwiseEvent_compl_le
    (h : IncrementCovariancePrunedSubmeshCertificate) :
    mu (incrementCovariancePrunedPairwiseEvent
        h.X h.R h.leftEnd h.rightEnd h.rho h.V h.K)ᶜ ≤ h.fail := by
  have hsub :
      (incrementCovariancePrunedPairwiseEvent
        h.X h.R h.leftEnd h.rightEnd h.rho h.V h.K)ᶜ ⊆ h.goodᶜ := by
    intro omega hnot hgood
    exact hnot
      (incrementCovariancePrunedPairwiseEvent_of_pruningCertificate h hgood)
  exact (measure_mono hsub).trans h.prob_good_compl

/-- Perron/Euler-product reduction certificate connecting the weighted
covariance integral to actual complete-model increment covariance. -/
structure WeightedPerronReductionCertificate where
  prop3 : WeightedHarperProp3Certificate
  leftEnd : ℕ → ℕ
  rightEnd : ℕ → ℕ
  rhoActual : ℝ
  V : ℝ
  err : ℝ
  perronGood : Set Omega
  failPerron : ℝ≥0∞
  threshold_slack : prop3.rho * prop3.M + err ≤ rhoActual * V
  perron_error :
    ∀ omega ∈ perronGood, ∀ r : ℕ, r < prop3.R →
      ∀ u : ℕ, u < prop3.R →
        |largePrimeIncrementCovariance omega prop3.X
          (leftEnd r) (rightEnd r) (leftEnd u) (rightEnd u)| ≤
          ‖weightedCovarianceIntegral prop3.X prop3.R
            prop3.H prop3.alpha omega r u‖ + err
  prob_perron_compl : mu perronGoodᶜ ≤ failPerron

/-- Explicit weighted Proposition 3 certificate with the bookkeeping exposed:
`Cmu`, the barrier exponent `Q`, the padded residual `Q - B - 15`, and the
`C'_B` restriction on the high-moment range. -/
structure WeightedHarperProp3ExplicitCertificate where
  X : ℕ
  R : ℕ
  k : ℕ
  B : ℝ
  Q : ℝ
  ell : ℝ
  M : ℝ
  G : ℝ
  rho : ℝ
  C_B : ℝ
  Cprime_B : ℝ
  H : ℝ → ℂ
  alpha : ℕ → ℝ
  good : Set Omega
  fail : ℝ≥0∞
  degreeBound : ℝ
  weight : HarperWeight X B ell M H
  grid_spacing : ∀ r : ℕ, alpha r = alpha 0 + (r : ℝ) * G
  barrier_large : B + 115 ≤ Q
  moment_range :
    (k : ℝ) ≤ loglogNat X / (Cprime_B * logloglogNat X)
  Cprime_large :
    12 * (29 + C_B) ≤ Cprime_B
  rhoM_pos : 0 < rho * M
  moment_row_bound :
    ∀ omega ∈ good, ∀ r : ℕ, r < R →
      weightedRowMoment X R k H alpha omega r ≤
        weightedProp3ExplicitRowBound X R k B Q M C_B weight.Cmu
  rowBound_degree :
    weightedProp3ExplicitRowBound X R k B Q M C_B weight.Cmu /
      (rho * M) ^ (2 * k) ≤ degreeBound
  prob_good_compl : mu goodᶜ ≤ fail

/-- Harper's proof-level decomposition of the weighted Proposition 3 row
bound.

This is the layer closest to the paper proof.  The row moment is split into
the non-resonant contribution, the resonant `L^{-1/3}` contribution, and the
barrier-saving contribution.  The analytic work is now concentrated in the
three contribution bounds and the two good-event probability bounds; the
assembly into the explicit Proposition 3 certificate is deterministic. -/
structure WeightedHarperProp3ProofStepCertificate where
  X : ℕ
  R : ℕ
  k : ℕ
  B : ℝ
  Q : ℝ
  ell : ℝ
  M : ℝ
  G : ℝ
  rho : ℝ
  C_B : ℝ
  Cprime_B : ℝ
  H : ℝ → ℂ
  alpha : ℕ → ℝ
  energyGood : Set Omega
  resonantGood : Set Omega
  failEnergy : ℝ≥0∞
  failResonant : ℝ≥0∞
  degreeBound : ℝ
  nonresonantContribution : Omega → ℕ → ℝ
  resonantContribution : Omega → ℕ → ℝ
  barrierContribution : Omega → ℕ → ℝ
  weight : HarperWeight X B ell M H
  grid_spacing : ∀ r : ℕ, alpha r = alpha 0 + (r : ℝ) * G
  barrier_large : B + 115 ≤ Q
  moment_range :
    (k : ℝ) ≤ loglogNat X / (Cprime_B * logloglogNat X)
  Cprime_large :
    12 * (29 + C_B) ≤ Cprime_B
  rhoM_pos : 0 < rho * M
  row_decomposition :
    ∀ omega ∈ energyGood ∩ resonantGood, ∀ r : ℕ, r < R →
      weightedRowMoment X R k H alpha omega r ≤
        nonresonantContribution omega r +
          resonantContribution omega r +
            barrierContribution omega r
  nonresonant_bound :
    ∀ omega ∈ energyGood, ∀ r : ℕ, r < R →
      nonresonantContribution omega r ≤
        weightedProp3NonresonantBound X R k M C_B weight.Cmu
  resonant_bound :
    ∀ omega ∈ resonantGood, ∀ r : ℕ, r < R →
      resonantContribution omega r ≤
        weightedProp3ResonantBound X R k M C_B weight.Cmu
  barrier_bound :
    ∀ omega ∈ resonantGood, ∀ r : ℕ, r < R →
      barrierContribution omega r ≤
        weightedProp3BarrierBound X R k B Q M C_B weight.Cmu
  rowBound_degree :
    weightedProp3ExplicitRowBound X R k B Q M C_B weight.Cmu /
      (rho * M) ^ (2 * k) ≤ degreeBound
  prob_energy_compl : mu energyGoodᶜ ≤ failEnergy
  prob_resonant_compl : mu resonantGoodᶜ ≤ failResonant

/-- Structured proof certificate using the named Harper objects: the
non-resonant shell-energy term and the two resonant ordered-gap terms.  This
is the preferred interface for filling in the analytic proof of weighted
Proposition 3. -/
structure WeightedHarperProp3StructuredCertificate where
  X : ℕ
  R : ℕ
  k : ℕ
  B : ℝ
  Q : ℝ
  ell : ℝ
  M : ℝ
  G : ℝ
  rho : ℝ
  C_B : ℝ
  Cprime_B : ℝ
  H : ℝ → ℂ
  alpha : ℕ → ℝ
  shells : Finset ℕ
  energyGood : Set Omega
  resonantGood : Set Omega
  failEnergy : ℝ≥0∞
  failResonant : ℝ≥0∞
  degreeBound : ℝ
  weight : HarperWeight X B ell M H
  grid_spacing : ∀ r : ℕ, alpha r = alpha 0 + (r : ℝ) * G
  barrier_large : B + 115 ≤ Q
  moment_range :
    (k : ℝ) ≤ loglogNat X / (Cprime_B * logloglogNat X)
  Cprime_large :
    12 * (29 + C_B) ≤ Cprime_B
  rhoM_pos : 0 < rho * M
  row_decomposition :
    ∀ omega ∈ energyGood ∩ resonantGood, ∀ r : ℕ, r < R →
      weightedRowMoment X R k H alpha omega r ≤
        weightedNonresonantEnergyTerm X k H shells omega +
          weightedResonantGapContribution X R k B Q ell M G H alpha omega r +
            weightedBarrierGapContribution X R k B Q ell M G H alpha omega r
  energy_bound :
    ∀ omega ∈ energyGood,
      weightedNonresonantEnergyTerm X k H shells omega ≤
        weightedProp3NonresonantBound X R k M C_B weight.Cmu
  large_pair_bound :
    ∀ omega ∈ resonantGood, ∀ r : ℕ, r < R →
      weightedResonantGapContribution X R k B Q ell M G H alpha omega r ≤
        weightedProp3ResonantBound X R k M C_B weight.Cmu
  low_barrier_bound :
    ∀ omega ∈ resonantGood, ∀ r : ℕ, r < R →
      weightedBarrierGapContribution X R k B Q ell M G H alpha omega r ≤
        weightedProp3BarrierBound X R k B Q M C_B weight.Cmu
  rowBound_degree :
    weightedProp3ExplicitRowBound X R k B Q M C_B weight.Cmu /
      (rho * M) ^ (2 * k) ≤ degreeBound
  prob_energy_compl : mu energyGoodᶜ ≤ failEnergy
  prob_resonant_compl : mu resonantGoodᶜ ≤ failResonant

/-- View the structured Harper proof certificate as the proof-step
certificate. -/
noncomputable def weightedHarperProp3ProofSteps_of_structured
    (h : WeightedHarperProp3StructuredCertificate) :
    WeightedHarperProp3ProofStepCertificate where
  X := h.X
  R := h.R
  k := h.k
  B := h.B
  Q := h.Q
  ell := h.ell
  M := h.M
  G := h.G
  rho := h.rho
  C_B := h.C_B
  Cprime_B := h.Cprime_B
  H := h.H
  alpha := h.alpha
  energyGood := h.energyGood
  resonantGood := h.resonantGood
  failEnergy := h.failEnergy
  failResonant := h.failResonant
  degreeBound := h.degreeBound
  nonresonantContribution :=
    fun omega _r => weightedNonresonantEnergyTerm h.X h.k h.H h.shells omega
  resonantContribution :=
    fun omega r =>
      weightedResonantGapContribution
        h.X h.R h.k h.B h.Q h.ell h.M h.G h.H h.alpha omega r
  barrierContribution :=
    fun omega r =>
      weightedBarrierGapContribution
        h.X h.R h.k h.B h.Q h.ell h.M h.G h.H h.alpha omega r
  weight := h.weight
  grid_spacing := h.grid_spacing
  barrier_large := h.barrier_large
  moment_range := h.moment_range
  Cprime_large := h.Cprime_large
  rhoM_pos := h.rhoM_pos
  row_decomposition := h.row_decomposition
  nonresonant_bound := by
    intro omega homega _r _hr
    exact h.energy_bound omega homega
  resonant_bound := h.large_pair_bound
  barrier_bound := h.low_barrier_bound
  rowBound_degree := h.rowBound_degree
  prob_energy_compl := h.prob_energy_compl
  prob_resonant_compl := h.prob_resonant_compl

/-- The combined good event for the proof-step version of weighted
Proposition 3. -/
def weightedProp3ProofStepGood
    (h : WeightedHarperProp3ProofStepCertificate) : Set Omega :=
  h.energyGood ∩ h.resonantGood

/-- The combined failure budget for the proof-step version of weighted
Proposition 3. -/
def weightedProp3ProofStepFail
    (h : WeightedHarperProp3ProofStepCertificate) : ℝ≥0∞ :=
  h.failEnergy + h.failResonant

/-- The two Harper proof good events imply the combined good event except
with the sum of their failure budgets. -/
theorem prob_weightedProp3ProofStepGood_compl_le
    (h : WeightedHarperProp3ProofStepCertificate) :
    mu (weightedProp3ProofStepGood h)ᶜ ≤ weightedProp3ProofStepFail h := by
  have hsub :
      (weightedProp3ProofStepGood h)ᶜ ⊆ h.energyGoodᶜ ∪ h.resonantGoodᶜ := by
    intro omega hnot
    by_cases henergy : omega ∈ h.energyGood
    · right
      intro hres
      exact hnot ⟨henergy, hres⟩
    · left
      exact henergy
  calc
    mu (weightedProp3ProofStepGood h)ᶜ
        ≤ mu (h.energyGoodᶜ ∪ h.resonantGoodᶜ) :=
          measure_mono hsub
    _ ≤ mu h.energyGoodᶜ + mu h.resonantGoodᶜ :=
          measure_union_le _ _
    _ ≤ h.failEnergy + h.failResonant :=
          add_le_add h.prob_energy_compl h.prob_resonant_compl

/-- Assemble Harper's proof-step decomposition into the explicit weighted
Proposition 3 certificate used downstream. -/
noncomputable def weightedHarperProp3ExplicitCertificate_of_proofSteps
    (h : WeightedHarperProp3ProofStepCertificate) :
    WeightedHarperProp3ExplicitCertificate where
  X := h.X
  R := h.R
  k := h.k
  B := h.B
  Q := h.Q
  ell := h.ell
  M := h.M
  G := h.G
  rho := h.rho
  C_B := h.C_B
  Cprime_B := h.Cprime_B
  H := h.H
  alpha := h.alpha
  good := weightedProp3ProofStepGood h
  fail := weightedProp3ProofStepFail h
  degreeBound := h.degreeBound
  weight := h.weight
  grid_spacing := h.grid_spacing
  barrier_large := h.barrier_large
  moment_range := h.moment_range
  Cprime_large := h.Cprime_large
  rhoM_pos := h.rhoM_pos
  moment_row_bound := by
    intro omega homega r hr
    have henergy : omega ∈ h.energyGood := homega.1
    have hres : omega ∈ h.resonantGood := homega.2
    have hdec := h.row_decomposition omega homega r hr
    have hnon := h.nonresonant_bound omega henergy r hr
    have hresb := h.resonant_bound omega hres r hr
    have hbar := h.barrier_bound omega hres r hr
    unfold weightedProp3ExplicitRowBound
    linarith
  rowBound_degree := h.rowBound_degree
  prob_good_compl := prob_weightedProp3ProofStepGood_compl_le h

/-- Forget the explicit bookkeeping constants and view the explicit weighted
Proposition 3 certificate as the row-bound certificate used by the
bad-neighbour counting lemma. -/
noncomputable def weightedHarperProp3Certificate_of_explicit
    (h : WeightedHarperProp3ExplicitCertificate) :
    WeightedHarperProp3Certificate where
  X := h.X
  R := h.R
  k := h.k
  B := h.B
  ell := h.ell
  M := h.M
  G := h.G
  rho := h.rho
  H := h.H
  alpha := h.alpha
  good := h.good
  fail := h.fail
  rowBound :=
    weightedProp3ExplicitRowBound h.X h.R h.k h.B h.Q h.M h.C_B h.weight.Cmu
  degreeBound := h.degreeBound
  weight_admissible := h.weight
  grid_spacing := h.grid_spacing
  rhoM_pos := h.rhoM_pos
  moment_row_bound := h.moment_row_bound
  rowBound_degree := h.rowBound_degree
  prob_good_compl := h.prob_good_compl

/-- Good weighted Proposition 3 event: all rows have bad degree bounded by
`degreeBound`. -/
def weightedProp3BadDegreeEvent
    (h : WeightedHarperProp3Certificate) : Set Omega :=
  {omega |
    ∀ r : ℕ, r < h.R →
      weightedBadDegreeReal h.X h.R h.H h.alpha h.rho h.M omega r ≤
        h.degreeBound}

/-- Deterministic bad-degree consequence of the weighted Proposition 3 row
moment bound. -/
theorem weightedBadDegree_of_weightedProp3
    (h : WeightedHarperProp3Certificate) :
    h.good ⊆ weightedProp3BadDegreeEvent h := by
  intro omega homega r hr
  exact
    (weighted_badDegreeReal_le_of_rowMoment
      (X := h.X) (R := h.R) (k := h.k) (H := h.H)
      (alpha := h.alpha) (rho := h.rho) (M := h.M)
      (rowBound := h.rowBound) (omega := omega) (r := r)
      h.rhoM_pos (h.moment_row_bound omega homega r hr)).trans
      h.rowBound_degree

/-- Probability form of the bad-degree consequence. -/
theorem prob_weightedProp3BadDegreeEvent_compl_le
    (h : WeightedHarperProp3Certificate) :
    mu (weightedProp3BadDegreeEvent h)ᶜ ≤ h.fail := by
  have hsub : (weightedProp3BadDegreeEvent h)ᶜ ⊆ h.goodᶜ := by
    intro omega hnot hgood
    exact hnot (weightedBadDegree_of_weightedProp3 h hgood)
  exact (measure_mono hsub).trans h.prob_good_compl

/-- The combined good event for weighted Proposition 3 plus Perron reduction. -/
def weightedPerronIncrementGood
    (h : WeightedPerronReductionCertificate) : Set Omega :=
  weightedProp3BadDegreeEvent h.prop3 ∩ h.perronGood

/-- The combined failure budget for weighted Proposition 3 plus Perron
reduction. -/
def weightedPerronIncrementFail
    (h : WeightedPerronReductionCertificate) : ℝ≥0∞ :=
  h.prop3.fail + h.failPerron

/-- On the combined good event, weighted bad-degree control transfers to
actual increment covariance bad-degree control. -/
theorem incrementCovarianceBadDegreeEvent_of_weightedPerron
    (h : WeightedPerronReductionCertificate) :
    weightedPerronIncrementGood h ⊆
      incrementCovarianceBadDegreeEvent h.prop3.X h.prop3.R h.leftEnd h.rightEnd
        h.rhoActual h.V h.prop3.degreeBound := by
  intro omega homega r hr
  have hweighted : omega ∈ weightedProp3BadDegreeEvent h.prop3 := homega.1
  have hperron_good : omega ∈ h.perronGood := homega.2
  have hperron_row :
      ∀ u : ℕ, u < h.prop3.R →
        |largePrimeIncrementCovariance omega h.prop3.X
          (h.leftEnd r) (h.rightEnd r) (h.leftEnd u) (h.rightEnd u)| ≤
          ‖weightedCovarianceIntegral h.prop3.X h.prop3.R
            h.prop3.H h.prop3.alpha omega r u‖ + h.err :=
    h.perron_error omega hperron_good r hr
  exact
    (incrementCovarianceBadDegree_le_weightedBadDegree
      (X := h.prop3.X) (R := h.prop3.R)
      (H := h.prop3.H) (alpha := h.prop3.alpha)
      (leftEnd := h.leftEnd) (rightEnd := h.rightEnd)
      (rhoActual := h.rhoActual) (V := h.V)
      (rhoWeighted := h.prop3.rho) (M := h.prop3.M)
      (err := h.err) (omega := omega) (r := r)
      h.threshold_slack hperron_row).trans
      (hweighted r hr)

/-- Probability form of the weighted Perron reduction. -/
theorem prob_incrementCovarianceBadDegreeEvent_compl_le_of_weightedPerron
    (h : WeightedPerronReductionCertificate) :
    mu (incrementCovarianceBadDegreeEvent h.prop3.X h.prop3.R
      h.leftEnd h.rightEnd h.rhoActual h.V h.prop3.degreeBound)ᶜ ≤
      weightedPerronIncrementFail h := by
  have hsub :
      (incrementCovarianceBadDegreeEvent h.prop3.X h.prop3.R
        h.leftEnd h.rightEnd h.rhoActual h.V h.prop3.degreeBound)ᶜ
        ⊆ (weightedProp3BadDegreeEvent h.prop3)ᶜ ∪ h.perronGoodᶜ := by
    intro omega hbad
    by_cases hw : omega ∈ weightedProp3BadDegreeEvent h.prop3
    · right
      intro hp
      exact hbad (incrementCovarianceBadDegreeEvent_of_weightedPerron h ⟨hw, hp⟩)
    · left
      exact hw
  calc
    mu (incrementCovarianceBadDegreeEvent h.prop3.X h.prop3.R
      h.leftEnd h.rightEnd h.rhoActual h.V h.prop3.degreeBound)ᶜ
        ≤ mu ((weightedProp3BadDegreeEvent h.prop3)ᶜ ∪ h.perronGoodᶜ) :=
          measure_mono hsub
    _ ≤ mu (weightedProp3BadDegreeEvent h.prop3)ᶜ + mu h.perronGoodᶜ :=
          measure_union_le _ _
    _ ≤ h.prop3.fail + h.failPerron :=
          add_le_add (prob_weightedProp3BadDegreeEvent_compl_le h.prop3)
            h.prob_perron_compl

/-- Probability form for the explicit weighted Proposition 3 certificate. -/
theorem prob_weightedProp3BadDegreeEvent_compl_le_of_explicit
    (h : WeightedHarperProp3ExplicitCertificate) :
    mu (weightedProp3BadDegreeEvent
      (weightedHarperProp3Certificate_of_explicit h))ᶜ ≤ h.fail :=
  prob_weightedProp3BadDegreeEvent_compl_le
    (weightedHarperProp3Certificate_of_explicit h)

end Problem1144
end Erdos
