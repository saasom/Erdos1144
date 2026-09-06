import Erdos.Problem1144.HarperCandidateCovarianceResonanceSlice

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem1144

/-- The offset may depend measurably on every coordinate other than the
selected gap. The integer resonance label is unchanged by slicing. -/
def candidateAffineResonanceGraph {Ω : Type*} (a : ℝ) (b : Ω → ℝ)
    (m : ℤ) (ε : ℝ) : Set (ℝ × Ω) :=
  {z | |a * z.1 + b z.2 - (m : ℝ)| ≤ ε}

theorem candidate_measurableSet_affineResonanceGraph {Ω : Type*} [MeasurableSpace Ω]
    (a : ℝ) {b : Ω → ℝ} (hb : Measurable b) (m : ℤ) (ε : ℝ) :
    MeasurableSet (candidateAffineResonanceGraph a b m ε) :=
  measurableSet_le (((measurable_const.mul measurable_fst).add
    (hb.comp measurable_snd)).sub measurable_const).abs measurable_const

/-- Fubini's actual weighted resonance slice. All other nonnegative
integrable coordinates are retained through their integral, even when they
shift the resonance cell in an arbitrary measurable way. -/
theorem candidate_integral_product_resonanceSlice_le
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [SFinite ν]
    {a l u ε K : ℝ} (ha : a ≠ 0) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (b : Ω → ℝ) (hb : Measurable b) (m : ℤ)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hwn : ∀ x ∈ Icc l u, 0 ≤ w x) (hwb : ∀ x ∈ Icc l u, w x ≤ K)
    (v : Ω → ℝ) (hvi : Integrable v ν) (hvn : ∀ᵐ z ∂ν, 0 ≤ v z) :
    (∫ z, (candidateAffineResonanceGraph a b m ε).indicator
      (fun z => w z.1 * v z.2) z ∂((volume.restrict (Icc l u)).prod ν)) ≤
      ((2 * ε / |a|) * K) * ∫ z, v z ∂ν := by
  let G := candidateAffineResonanceGraph a b m ε
  have hG : MeasurableSet G := candidate_measurableSet_affineResonanceGraph a hb m ε
  have hwi : IntegrableOn w (Icc l u) := by
    apply Integrable.of_bound hw.aestronglyMeasurable K
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hwn x hx)]
    exact hwb x hx
  have hi := (hwi.mul_prod hvi).indicator hG
  rw [integral_prod_symm _ hi]
  have hpoint (z : Ω) (hz : 0 ≤ v z) :
      (∫ x in Icc l u, G.indicator (fun z => w z.1 * v z.2) (x, z)) ≤
        ((2 * ε / |a|) * K) * v z := by
    have heq : (fun x => G.indicator (fun z => w z.1 * v z.2) (x, z)) =
        fun x => (candidateAffineResonanceSlice a (b z) m ε).indicator w x * v z := by
      funext x
      by_cases hx : x ∈ candidateAffineResonanceSlice a (b z) m ε
      · have hxG : (x, z) ∈ G := hx
        rw [Set.indicator_of_mem hxG, Set.indicator_of_mem hx]
      · have hxG : (x, z) ∉ G := hx
        rw [Set.indicator_of_notMem hxG, Set.indicator_of_notMem hx, zero_mul]
    rw [heq, integral_mul_const]
    exact mul_le_mul_of_nonneg_right
      (candidate_integral_boundedGap_resonanceSlice_le ha hε hK (b z) m w hw hwn hwb) hz
  have h := integral_mono_ae hi.integral_prod_right (hvi.const_mul ((2 * ε / |a|) * K))
    (hvn.mono fun z hz => hpoint z hz)
  rwa [integral_const_mul] at h

/-- Finite-product Fubini with every other one-coordinate weight retained
exactly. The displayed interval indicators are the actual bounded gap box,
and the offset can depend measurably on all of its coordinates. -/
theorem candidate_integral_finiteProduct_resonanceSlice_le
    {ι : Type*} [Fintype ι] {a l u ε K : ℝ}
    (ha : a ≠ 0) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (b : (ι → ℝ) → ℝ) (hb : Measurable b) (m : ℤ)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hwn : ∀ x ∈ Icc l u, 0 ≤ w x) (hwb : ∀ x ∈ Icc l u, w x ≤ K)
    (lower upper : ι → ℝ) (v : ι → ℝ → ℝ)
    (hvi : ∀ i, IntegrableOn (v i) (Icc (lower i) (upper i)))
    (hvn : ∀ i x, x ∈ Icc (lower i) (upper i) → 0 ≤ v i x) :
    (∫ z, (candidateAffineResonanceGraph a b m ε).indicator
      (fun z => w z.1 * ∏ i, (Icc (lower i) (upper i)).indicator (v i) (z.2 i)) z
        ∂((volume.restrict (Icc l u)).prod (Measure.pi fun _ : ι => (volume : Measure ℝ)))) ≤
      ((2 * ε / |a|) * K) * ∏ i, ∫ x in Icc (lower i) (upper i), v i x := by
  classical
  let V : (ι → ℝ) → ℝ := fun z => ∏ i, (Icc (lower i) (upper i)).indicator (v i) (z i)
  have hiV : Integrable V (Measure.pi fun _ : ι => (volume : Measure ℝ)) :=
    Integrable.fintype_prod (fun i => (hvi i).integrable_indicator measurableSet_Icc)
  have hnV (z : ι → ℝ) : 0 ≤ V z := by
    apply Finset.prod_nonneg
    intro i hi
    exact Set.indicator_nonneg (fun x hx => hvn i x hx) (z i)
  have h := candidate_integral_product_resonanceSlice_le _ ha hε hK b hb m w hw hwn hwb V hiV (ae_of_all _ hnV)
  convert h using 1
  unfold V
  rw [integral_fintype_prod_eq_prod]
  simp_rw [integral_indicator measurableSet_Icc]

/-- The reciprocal-plus-constant Euler gap envelope in the finite-product
resonance cell. Setting `A=0,B=1` gives the requested reciprocal-gap loss
`2ε/(|a|δ)`, times exactly the remaining one-coordinate integrals. -/
theorem candidate_integral_finiteProduct_reciprocalGap_resonanceSlice_le
    {ι : Type*} [Fintype ι] {a δ l u ε A B : ℝ}
    (ha : a ≠ 0) (hδ : 0 < δ) (hδl : δ ≤ l) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (b : (ι → ℝ) → ℝ) (hb : Measurable b) (m : ℤ)
    (w : ℝ → ℝ) (hw : Measurable w)
    (hwn : ∀ x ∈ Icc l u, 0 ≤ w x) (hwb : ∀ x ∈ Icc l u, w x ≤ A + B / x)
    (lower upper : ι → ℝ) (v : ι → ℝ → ℝ)
    (hvi : ∀ i, IntegrableOn (v i) (Icc (lower i) (upper i)))
    (hvn : ∀ i x, x ∈ Icc (lower i) (upper i) → 0 ≤ v i x) :
    (∫ z, (candidateAffineResonanceGraph a b m ε).indicator
      (fun z => w z.1 * ∏ i, (Icc (lower i) (upper i)).indicator (v i) (z.2 i)) z
        ∂((volume.restrict (Icc l u)).prod (Measure.pi fun _ : ι => (volume : Measure ℝ)))) ≤
      ((2 * ε / |a|) * (A + B / δ)) * ∏ i, ∫ x in Icc (lower i) (upper i), v i x := by
  apply candidate_integral_finiteProduct_resonanceSlice_le ha hε (by positivity)
    b hb m w hw hwn ?_ lower upper v hvi hvn
  intro x hx
  exact (hwb x hx).trans (add_le_add (le_refl A)
    (div_le_div_of_nonneg_left hB hδ (hδl.trans hx.1)))

end Erdos.Problem1144
