import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem1144

/-- One affine resonance cell, retaining its actual integer label. -/
def candidateAffineResonanceSlice (a b : ℝ) (m : ℤ) (ε : ℝ) : Set ℝ :=
  {x | |a * x + b - (m : ℝ)| ≤ ε}

theorem candidate_measurableSet_affineResonanceSlice (a b : ℝ) (m : ℤ) (ε : ℝ) :
    MeasurableSet (candidateAffineResonanceSlice a b m ε) :=
  measurableSet_le (((measurable_const.mul measurable_id).add measurable_const).sub
    measurable_const).abs measurable_const

/-- Exact Lebesgue length of a nondegenerate affine resonance slice. -/
theorem candidate_volume_affineResonanceSlice {a : ℝ} (ha : a ≠ 0)
    (b : ℝ) (m : ℤ) {ε : ℝ} (hε : 0 ≤ ε) :
    volume (candidateAffineResonanceSlice a b m ε) = ENNReal.ofReal (2 * ε / |a|) := by
  have heq : candidateAffineResonanceSlice a b m ε =
      (fun x : ℝ => a * x) ⁻¹' Icc ((m : ℝ) - b - ε) ((m : ℝ) - b + ε) := by
    ext x
    simp only [candidateAffineResonanceSlice, mem_setOf_eq, mem_preimage, mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [heq, Real.volume_preimage_mul_left ha, Real.volume_Icc,
    show (m : ℝ) - b + ε - ((m : ℝ) - b - ε) = 2 * ε by ring,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_inv]
  ring

/-- A measurable gap weight bounded by `1/x` on a bounded positive
interval is integrable there. -/
theorem candidate_integrableOn_positiveGapWeight {δ l u : ℝ}
    (hδ : 0 < δ) (hδl : δ ≤ l) (w : ℝ → ℝ) (hw : Measurable w)
    (hn : ∀ x ∈ Icc l u, 0 ≤ w x) (hb : ∀ x ∈ Icc l u, w x ≤ 1 / x) :
    IntegrableOn w (Icc l u) := by
  apply Integrable.of_bound hw.aestronglyMeasurable (1 / δ)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (hn x hx)]
  exact (hb x hx).trans (one_div_le_one_div_of_le hδ (hδl.trans hx.1))

/-- A uniform nonnegative gap-weight bound pays exactly the affine slice
length; no upper endpoint factor is lost. -/
theorem candidate_integral_boundedGap_resonanceSlice_le {a l u ε K : ℝ}
    (ha : a ≠ 0) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (b : ℝ) (m : ℤ) (w : ℝ → ℝ) (hw : Measurable w)
    (hn : ∀ x ∈ Icc l u, 0 ≤ w x) (hb : ∀ x ∈ Icc l u, w x ≤ K) :
    (∫ x in Icc l u, (candidateAffineResonanceSlice a b m ε).indicator w x) ≤
      (2 * ε / |a|) * K := by
  let S := candidateAffineResonanceSlice a b m ε
  have hS : MeasurableSet S := candidate_measurableSet_affineResonanceSlice a b m ε
  have hi : IntegrableOn w (Icc l u) := by
    apply Integrable.of_bound hw.aestronglyMeasurable K
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hn x hx)]
    exact hb x hx
  have hpoint : ∀ x ∈ Icc l u, S.indicator w x ≤ S.indicator (fun _ => K) x := by
    intro x hx
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS]
      exact hb x hx
    · rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxS]
  have h := setIntegral_mono_on (hi.indicator hS)
    ((integrableOn_const (s := Icc l u) (C := K)
      (by rw [Real.volume_Icc]; finiteness)).indicator hS) measurableSet_Icc hpoint
  apply h.trans
  rw [integral_indicator hS, setIntegral_const, smul_eq_mul, measureReal_restrict_apply hS]
  have hvol := candidate_volume_affineResonanceSlice ha b m hε
  have hfinite : volume S ≠ ⊤ := by rw [show S = _ from rfl, hvol]; finiteness
  have hmono := measureReal_mono (s₁ := S ∩ Icc l u) (s₂ := S) inter_subset_left hfinite
  calc
    _ ≤ volume.real S * K := mul_le_mul_of_nonneg_right hmono hK
    _ = _ := by rw [Measure.real, hvol, ENNReal.toReal_ofReal (by positivity)]

/-- The reciprocal-plus-constant envelope furnished by the actual Euler
gap bound pays `A+B/δ`, with no factor involving the interval's upper end. -/
theorem candidate_integral_reciprocalGapEnvelope_resonanceSlice_le {a δ l u ε A B : ℝ}
    (ha : a ≠ 0) (hδ : 0 < δ) (hδl : δ ≤ l) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (b : ℝ) (m : ℤ)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hn : ∀ x ∈ Icc l u, 0 ≤ w x) (hb : ∀ x ∈ Icc l u, w x ≤ A + B / x) :
    (∫ x in Icc l u, (candidateAffineResonanceSlice a b m ε).indicator w x) ≤
      (2 * ε / |a|) * (A + B / δ) := by
  apply candidate_integral_boundedGap_resonanceSlice_le ha hε (by positivity) b m w hw hn
  intro x hx
  apply (hb x hx).trans
  exact add_le_add (le_refl A)
    (div_le_div_of_nonneg_left hB hδ (hδl.trans hx.1))

/-- The actual weighted resonance slice costs its length divided by the
positive lower gap scale. The coefficient factor `1/|a|` is retained. -/
theorem candidate_integral_positiveGap_resonanceSlice_le {a δ l u ε : ℝ}
    (ha : a ≠ 0) (hδ : 0 < δ) (hδl : δ ≤ l) (hε : 0 ≤ ε)
    (b : ℝ) (m : ℤ) (w : ℝ → ℝ) (hw : Measurable w)
    (hn : ∀ x ∈ Icc l u, 0 ≤ w x) (hb : ∀ x ∈ Icc l u, w x ≤ 1 / x) :
    (∫ x in Icc l u, (candidateAffineResonanceSlice a b m ε).indicator w x) ≤
      2 * ε / (|a| * δ) := by
  let S := candidateAffineResonanceSlice a b m ε
  have hS : MeasurableSet S := candidate_measurableSet_affineResonanceSlice a b m ε
  have hi := candidate_integrableOn_positiveGapWeight hδ hδl w hw hn hb
  have hpoint : ∀ x ∈ Icc l u, S.indicator w x ≤ S.indicator (fun _ => 1 / δ) x := by
    intro x hx
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS]
      exact (hb x hx).trans (one_div_le_one_div_of_le hδ (hδl.trans hx.1))
    · rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxS]
  have h := setIntegral_mono_on (hi.indicator hS)
    ((integrableOn_const (s := Icc l u) (C := 1 / δ) (by rw [Real.volume_Icc]; finiteness)).indicator hS) measurableSet_Icc hpoint
  apply h.trans
  rw [integral_indicator hS, setIntegral_const, smul_eq_mul,
    measureReal_restrict_apply hS]
  have hvol := candidate_volume_affineResonanceSlice ha b m hε
  have hfinite : volume S ≠ ⊤ := by rw [show S = _ from rfl, hvol]; finiteness
  have hmono := measureReal_mono (s₁ := S ∩ Icc l u) (s₂ := S) inter_subset_left hfinite
  calc
    _ ≤ volume.real S * (1 / δ) := mul_le_mul_of_nonneg_right hmono (by positivity)
    _ = _ := by
      rw [Measure.real, hvol, ENNReal.toReal_ofReal (by positivity)]
      ring

/-- A nonzero integer resonance coefficient has absolute value at least
one, giving the coefficient-free estimate used after the signed-gap count. -/
theorem candidate_integral_positiveGap_integerResonanceSlice_le
    {a : ℤ} (ha : a ≠ 0) {δ l u ε : ℝ}
    (hδ : 0 < δ) (hδl : δ ≤ l) (hε : 0 ≤ ε)
    (b : ℝ) (m : ℤ) (w : ℝ → ℝ) (hw : Measurable w)
    (hn : ∀ x ∈ Icc l u, 0 ≤ w x) (hb : ∀ x ∈ Icc l u, w x ≤ 1 / x) :
    (∫ x in Icc l u, (candidateAffineResonanceSlice (a : ℝ) b m ε).indicator w x) ≤
      2 * ε / δ := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have habs : (1 : ℝ) ≤ |(a : ℝ)| := by exact_mod_cast Int.one_le_abs ha
  apply (candidate_integral_positiveGap_resonanceSlice_le haR hδ hδl hε b m w hw hn hb).trans
  exact div_le_div_of_nonneg_left (by positivity) hδ (by nlinarith)

end Erdos.Problem1144
