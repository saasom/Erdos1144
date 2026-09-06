import Erdos.Problem1144.HarperBivariateFejerInversion

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Unsmoothing the bivariate Fejer comparison

The local-limit theorem needs ordinary rectangle probabilities.  This module
turns the already compiled smoothed-rectangle estimate into an expanded
ordinary-rectangle estimate.  It uses only the explicit Fejer tail and set
containments; correlation of the comparison Gaussian is irrelevant here.
-/

/-- The scaled Fejer law has the full tunable tail inherited from the
unscaled law, not merely the fixed one-quarter specialization. -/
theorem harperFejerMeasureScaled_tail_le_two_div
    {T r : Real} (hT : 0 < T) (hr : 2 ≤ r) :
    (Problem520.harperFejerMeasureScaled T).real
        {x : Real | r / T < |x|} ≤ 2 / r := by
  have hset : (T⁻¹ * ·) ⁻¹' {x : Real | r / T < |x|} =
      {x : Real | r < |x|} := by
    ext x
    simp only [preimage_setOf_eq, mem_setOf_eq]
    rw [show T⁻¹ * x = x / T by field_simp, abs_div, abs_of_pos hT,
      div_lt_div_iff_of_pos_right hT]
  rw [Problem520.harperFejerMeasureScaled,
    map_measureReal_apply (by fun_prop)
      (measurableSet_lt measurable_const measurable_abs), hset]
  exact Problem520.harperFejerMeasure_tail_le_two_div hr

/-- CDF increment as the mass of an open-closed interval. -/
theorem cdf_sub_eq_measureReal_Ioc
    (kappa : Measure Real) [IsProbabilityMeasure kappa]
    {a b : Real} (hab : a ≤ b) :
    cdf kappa b - cdf kappa a = kappa.real (Ioc a b) := by
  rw [cdf_eq_real, cdf_eq_real]
  have hsub : Iic a ⊆ Iic b := Iic_subset_Iic.mpr hab
  rw [← measureReal_diff hsub measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_diff, Set.mem_Iic, Set.mem_Ioc]
  constructor
  · rintro ⟨hxb, hna⟩
    exact ⟨lt_of_not_ge hna, hxb⟩
  · rintro ⟨hax, hxb⟩
    exact ⟨hxb, not_le.mpr hax⟩

/-- The two CDF increments in the smoothed rectangle are exactly the product
kernel mass of the corresponding translated rectangle. -/
theorem cdf_product_eq_measureReal_translatedRectangle
    (kappa : Measure Real) [IsProbabilityMeasure kappa]
    {a b c d : Real} (hab : a ≤ b) (hcd : c ≤ d)
    (x : Real × Real) :
    (cdf kappa (b - x.1) - cdf kappa (a - x.1)) *
        (cdf kappa (d - x.2) - cdf kappa (c - x.2)) =
      (kappa.prod kappa).real
        (Ioc (a - x.1) (b - x.1) ×ˢ
          Ioc (c - x.2) (d - x.2)) := by
  rw [cdf_sub_eq_measureReal_Ioc kappa (by linarith),
    cdf_sub_eq_measureReal_Ioc kappa (by linarith),
    measureReal_prod_prod]

/-- The central interval has mass at least `1-alpha` when the absolute tail
beyond `delta` has mass at most `alpha`. -/
theorem one_sub_le_measureReal_Icc_of_tail_le
    (kappa : Measure Real) [IsProbabilityMeasure kappa]
    {delta alpha : Real}
    (htail : kappa.real {u : Real | delta < |u|} ≤ alpha) :
    1 - alpha ≤ kappa.real (Icc (-delta) delta) := by
  have hcompl : (Icc (-delta) delta)ᶜ = {u : Real | delta < |u|} := by
    ext u
    simp only [mem_compl_iff, Set.mem_Icc, mem_setOf_eq]
    rw [← abs_le, not_le]
  rw [← hcompl, measureReal_compl measurableSet_Icc,
    probReal_univ] at htail
  linarith

/-- If the spatial point is in a rectangle, then the expanded translated
kernel rectangle contains the central kernel square. -/
theorem centralSquare_subset_expandedTranslatedRectangle
    {a b c d delta : Real} {x : Real × Real}
    (hx : x ∈ Ioc a b ×ˢ Ioc c d) :
    Icc (-delta) delta ×ˢ Icc (-delta) delta ⊆
      Ioc (a - delta - x.1) (b + delta - x.1) ×ˢ
        Ioc (c - delta - x.2) (d + delta - x.2) := by
  intro u hu
  constructor
  · constructor <;> linarith [hx.1.1, hx.1.2, hu.1.1, hu.1.2]
  · constructor <;> linarith [hx.2.1, hx.2.2, hu.2.1, hu.2.2]

/-- Pointwise lower unsmoothing inequality on a rectangle. -/
theorem one_sub_sq_le_expanded_cdf_product
    (kappa : Measure Real) [IsProbabilityMeasure kappa]
    {a b c d delta alpha : Real}
    (hab : a ≤ b) (hcd : c ≤ d) (hdelta : 0 ≤ delta)
    (halpha1 : alpha ≤ 1)
    (htail : kappa.real {u : Real | delta < |u|} ≤ alpha)
    {x : Real × Real} (hx : x ∈ Ioc a b ×ˢ Ioc c d) :
    (1 - alpha) ^ (2 : Nat) ≤
      (cdf kappa (b + delta - x.1) -
        cdf kappa (a - delta - x.1)) *
      (cdf kappa (d + delta - x.2) -
        cdf kappa (c - delta - x.2)) := by
  rw [cdf_product_eq_measureReal_translatedRectangle kappa
    (by linarith) (by linarith)]
  have hgood := one_sub_le_measureReal_Icc_of_tail_le
    kappa htail
  have hmono :
      (kappa.prod kappa).real
          (Icc (-delta) delta ×ˢ Icc (-delta) delta) ≤
        (kappa.prod kappa).real
          (Ioc (a - delta - x.1) (b + delta - x.1) ×ˢ
            Ioc (c - delta - x.2) (d + delta - x.2)) :=
    measureReal_mono
      (centralSquare_subset_expandedTranslatedRectangle hx)
  rw [measureReal_prod_prod] at hmono
  have hone : 0 ≤ 1 - alpha := by linarith
  calc
    (1 - alpha) ^ (2 : Nat) = (1 - alpha) * (1 - alpha) := by ring
    _ ≤ kappa.real (Icc (-delta) delta) *
        kappa.real (Icc (-delta) delta) := by
      gcongr
    _ ≤ _ := hmono

/-- The rectangle kernel appearing in `harperBivariateSmoothRectangle` is
measurable, nonnegative, bounded by one, and hence integrable against any
probability law. -/
theorem integrable_bivariateCdfProduct
    (kappa : Measure Real) [IsProbabilityMeasure kappa]
    (mu : Measure (Real × Real)) [IsProbabilityMeasure mu]
    {a b c d : Real} (hab : a ≤ b) (hcd : c ≤ d) :
    Integrable (fun x : Real × Real ↦
      (cdf kappa (b - x.1) - cdf kappa (a - x.1)) *
        (cdf kappa (d - x.2) - cdf kappa (c - x.2))) mu := by
  let F : Real × Real → Real := fun x ↦
    (cdf kappa (b - x.1) - cdf kappa (a - x.1)) *
      (cdf kappa (d - x.2) - cdf kappa (c - x.2))
  have hFmeas : Measurable F := by
    exact (((monotone_cdf kappa).measurable.comp (by fun_prop)).sub
      ((monotone_cdf kappa).measurable.comp (by fun_prop))).mul
        (((monotone_cdf kappa).measurable.comp (by fun_prop)).sub
          ((monotone_cdf kappa).measurable.comp (by fun_prop)))
  have hF0 (x : Real × Real) : 0 ≤ F x := by
    apply mul_nonneg
    · exact sub_nonneg.mpr ((monotone_cdf kappa) (by linarith))
    · exact sub_nonneg.mpr ((monotone_cdf kappa) (by linarith))
  have hF1 (x : Real × Real) : F x ≤ 1 := by
    have h₁0 : 0 ≤ cdf kappa (b - x.1) - cdf kappa (a - x.1) := by
      exact sub_nonneg.mpr ((monotone_cdf kappa) (by linarith))
    have h₁1 : cdf kappa (b - x.1) - cdf kappa (a - x.1) ≤ 1 := by
      linarith [cdf_nonneg kappa (a - x.1), cdf_le_one kappa (b - x.1)]
    have h₂0 : 0 ≤ cdf kappa (d - x.2) - cdf kappa (c - x.2) := by
      exact sub_nonneg.mpr ((monotone_cdf kappa) (by linarith))
    have h₂1 : cdf kappa (d - x.2) - cdf kappa (c - x.2) ≤ 1 := by
      linarith [cdf_nonneg kappa (c - x.2), cdf_le_one kappa (d - x.2)]
    dsimp only [F]
    nlinarith
  change Integrable F mu
  refine (integrable_const (μ := mu) (1 : Real)).mono'
    hFmeas.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hF0 x)]
  exact hF1 x

/-- Lower unsmoothing: the expanded smoothed mass controls the original
ordinary rectangle mass, losing only the square of the kernel's good mass. -/
theorem one_sub_sq_mul_rectangleMass_le_smoothExpanded
    (kappa : Measure Real) [IsProbabilityMeasure kappa]
    (mu : Measure (Real × Real)) [IsProbabilityMeasure mu]
    {a b c d delta alpha : Real}
    (hab : a ≤ b) (hcd : c ≤ d) (hdelta : 0 ≤ delta)
    (halpha1 : alpha ≤ 1)
    (htail : kappa.real {u : Real | delta < |u|} ≤ alpha) :
    (1 - alpha) ^ (2 : Nat) *
        mu.real (Ioc a b ×ˢ Ioc c d) ≤
      harperBivariateSmoothRectangle kappa mu
        (a - delta) (b + delta) (c - delta) (d + delta) := by
  let F : Real × Real → Real := fun x ↦
    (cdf kappa (b + delta - x.1) -
      cdf kappa (a - delta - x.1)) *
    (cdf kappa (d + delta - x.2) -
      cdf kappa (c - delta - x.2))
  have hFint : Integrable F mu := by
    exact integrable_bivariateCdfProduct kappa mu
      (by linarith) (by linarith)
  have hF0 : ∀ x, 0 ≤ F x := by
    intro x
    apply mul_nonneg <;>
      exact sub_nonneg.mpr ((monotone_cdf kappa) (by linarith))
  calc
    (1 - alpha) ^ (2 : Nat) *
        mu.real (Ioc a b ×ˢ Ioc c d) ≤
        ∫ x in Ioc a b ×ˢ Ioc c d, F x ∂mu := by
      apply setIntegral_ge_of_const_le_real
        (measurableSet_Ioc.prod measurableSet_Ioc)
        (by finiteness)
      · intro x hx
        exact one_sub_sq_le_expanded_cdf_product kappa
          hab hcd hdelta halpha1 htail hx
      · exact hFint.integrableOn
    _ ≤ ∫ x, F x ∂mu :=
      setIntegral_le_integral hFint (ae_of_all _ hF0)
    _ = harperBivariateSmoothRectangle kappa mu
        (a - delta) (b + delta) (c - delta) (d + delta) := by
      rfl

/-- If a spatial coordinate lies outside the `delta`-expanded interval, a
kernel displacement landing it in the original interval must lie in the
absolute tail beyond `delta`. -/
theorem measureReal_translatedIoc_le_tail_of_not_mem_expanded
    (kappa : Measure Real) [IsFiniteMeasure kappa]
    {a b x delta alpha : Real} (hdelta : 0 ≤ delta)
    (htail : kappa.real {u : Real | delta < |u|} ≤ alpha)
    (hx : x ∉ Ioc (a - delta) (b + delta)) :
    kappa.real (Ioc (a - x) (b - x)) ≤ alpha := by
  have hcases : x ≤ a - delta ∨ b + delta < x := by
    simpa only [Set.mem_Ioc, not_and_or, not_lt, not_le] using hx
  apply (measureReal_mono (μ := kappa) ?_).trans htail
  intro u hu
  simp only [Set.mem_Ioc] at hu
  simp only [mem_setOf_eq]
  rcases hcases with hleft | hright
  · have hu0 : 0 ≤ u := by linarith [hu.1]
    rw [abs_of_nonneg hu0]
    linarith [hu.1]
  · have hu0 : u < 0 := by linarith [hu.2]
    rw [abs_of_neg hu0]
    linarith [hu.2]

/-- Pointwise upper unsmoothing inequality. -/
theorem cdf_product_le_expandedRectangleIndicator_add_tail
    (kappa : Measure Real) [IsProbabilityMeasure kappa]
    {a b c d delta alpha : Real}
    (hab : a ≤ b) (hcd : c ≤ d) (hdelta : 0 ≤ delta)
    (halpha0 : 0 ≤ alpha)
    (htail : kappa.real {u : Real | delta < |u|} ≤ alpha)
    (x : Real × Real) :
    (cdf kappa (b - x.1) - cdf kappa (a - x.1)) *
        (cdf kappa (d - x.2) - cdf kappa (c - x.2)) ≤
      (Ioc (a - delta) (b + delta) ×ˢ
        Ioc (c - delta) (d + delta)).indicator (fun _ ↦ (1 : Real)) x +
          alpha := by
  rw [cdf_product_eq_measureReal_translatedRectangle kappa hab hcd]
  rw [measureReal_prod_prod]
  let q₁ := kappa.real (Ioc (a - x.1) (b - x.1))
  let q₂ := kappa.real (Ioc (c - x.2) (d - x.2))
  have hq₁0 : 0 ≤ q₁ := measureReal_nonneg
  have hq₂0 : 0 ≤ q₂ := measureReal_nonneg
  have hq₁1 : q₁ ≤ 1 := by
    dsimp only [q₁]
    simpa only [probReal_univ] using
      (measureReal_mono (μ := kappa)
        (show Ioc (a - x.1) (b - x.1) ⊆ (Set.univ) from
        subset_univ _))
  have hq₂1 : q₂ ≤ 1 := by
    dsimp only [q₂]
    simpa only [probReal_univ] using
      (measureReal_mono (μ := kappa)
        (show Ioc (c - x.2) (d - x.2) ⊆ (Set.univ) from
        subset_univ _))
  by_cases hx : x ∈ Ioc (a - delta) (b + delta) ×ˢ
      Ioc (c - delta) (d + delta)
  · rw [Set.indicator_of_mem hx]
    dsimp only [q₁, q₂] at hq₁0 hq₂0 hq₁1 hq₂1 ⊢
    nlinarith
  · rw [Set.indicator_of_notMem hx, zero_add]
    have hcoord :
        x.1 ∉ Ioc (a - delta) (b + delta) ∨
          x.2 ∉ Ioc (c - delta) (d + delta) := by
      simpa only [Set.mem_prod, not_and_or] using hx
    rcases hcoord with hx₁ | hx₂
    · have hq₁a : q₁ ≤ alpha :=
        measureReal_translatedIoc_le_tail_of_not_mem_expanded
          kappa hdelta htail hx₁
      dsimp only [q₁, q₂] at hq₁0 hq₂0 hq₁1 hq₂1 hq₁a ⊢
      nlinarith
    · have hq₂a : q₂ ≤ alpha :=
        measureReal_translatedIoc_le_tail_of_not_mem_expanded
          kappa hdelta htail hx₂
      dsimp only [q₁, q₂] at hq₁0 hq₂0 hq₁1 hq₂1 hq₂a ⊢
      nlinarith

/-- Upper unsmoothing: a smoothed rectangle is bounded by the ordinary
`delta`-expanded rectangle plus the one-coordinate Fejer tail. -/
theorem smoothRectangle_le_expandedRectangleMass_add_tail
    (kappa : Measure Real) [IsProbabilityMeasure kappa]
    (mu : Measure (Real × Real)) [IsProbabilityMeasure mu]
    {a b c d delta alpha : Real}
    (hab : a ≤ b) (hcd : c ≤ d) (hdelta : 0 ≤ delta)
    (halpha0 : 0 ≤ alpha)
    (htail : kappa.real {u : Real | delta < |u|} ≤ alpha) :
    harperBivariateSmoothRectangle kappa mu a b c d ≤
      mu.real (Ioc (a - delta) (b + delta) ×ˢ
        Ioc (c - delta) (d + delta)) + alpha := by
  let R : Set (Real × Real) :=
    Ioc (a - delta) (b + delta) ×ˢ Ioc (c - delta) (d + delta)
  let F : Real × Real → Real := fun x ↦
    (cdf kappa (b - x.1) - cdf kappa (a - x.1)) *
      (cdf kappa (d - x.2) - cdf kappa (c - x.2))
  let G : Real × Real → Real := fun x ↦
    R.indicator (fun _ ↦ (1 : Real)) x + alpha
  have hFint : Integrable F mu :=
    integrable_bivariateCdfProduct kappa mu hab hcd
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hGint : Integrable G mu := by
    exact ((integrable_const (μ := mu) (1 : Real)).indicator hR).add
      (integrable_const (μ := mu) alpha)
  have hpoint : ∀ x, F x ≤ G x := by
    intro x
    exact cdf_product_le_expandedRectangleIndicator_add_tail
      kappa hab hcd hdelta halpha0 htail x
  change (∫ x, F x ∂mu) ≤ _
  calc
    (∫ x, F x ∂mu) ≤ ∫ x, G x ∂mu :=
      integral_mono hFint hGint hpoint
    _ = mu.real R + alpha := by
      unfold G
      rw [integral_add
        ((integrable_const (μ := mu) (1 : Real)).indicator hR)
        (integrable_const (μ := mu) alpha),
        integral_indicator hR, setIntegral_const, integral_const,
        probReal_univ, smul_eq_mul, mul_one, one_smul]
    _ = _ := by rfl

/-- Ordinary-rectangle local comparison for one scheduled tilted Rademacher
block.  Both smoothing steps and the bivariate Fourier comparison have been
composed; the Gaussian rectangle is enlarged by `2*delta`. -/
theorem harperScheduledTwoHeightRectangleMass_le_gaussianExpanded
    (y j : Nat) (t s T : Real)
    {a b c d delta alpha : Real}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hT : 0 < T)
    (hfrequency :
      4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hdelta : 0 ≤ delta) (halpha0 : 0 ≤ alpha)
    (halpha1 : alpha ≤ 1)
    (htail : (Problem520.harperFejerMeasureScaled T).real
      {u : Real | delta < |u|} ≤ alpha) :
    (1 - alpha) ^ (2 : Nat) *
        (harperTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y j) t s).real
            (Ioc a b ×ˢ Ioc c d) ≤
      (harperTwoHeightGaussianLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s).real
          (Ioc (a - 2 * delta) (b + 2 * delta) ×ˢ
            Ioc (c - 2 * delta) (d + 2 * delta)) +
        alpha +
        (2 * Real.pi)⁻¹ ^ (2 : Nat) *
          |(b + delta) - (a - delta)| *
          |(d + delta) - (c - delta)| *
          (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
            (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) := by
  let kappa := Problem520.harperFejerMeasureScaled T
  let mu := harperTwoHeightPrimeBlockVectorLaw y
    (Problem520.harperScheduledPrimeBlock y j) t s
  let nu := harperTwoHeightGaussianLaw y
    (Problem520.harperScheduledPrimeBlock y j) t s
  let E : Real :=
    (2 * Real.pi)⁻¹ ^ (2 : Nat) *
      |(b + delta) - (a - delta)| *
      |(d + delta) - (c - delta)| *
      (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
        (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat))
  have hlower := one_sub_sq_mul_rectangleMass_le_smoothExpanded
    kappa mu hab hcd hdelta halpha1 htail
  have hsmooth :=
    abs_harperScheduledTwoHeightSmoothRectangle_sub_gaussianLaw_le_unconditional
      y j t s T (a - delta) (b + delta) (c - delta) (d + delta)
      hT hfrequency
  have hsmoothOne :
      harperBivariateSmoothRectangle kappa mu
          (a - delta) (b + delta) (c - delta) (d + delta) ≤
        harperBivariateSmoothRectangle kappa nu
          (a - delta) (b + delta) (c - delta) (d + delta) + E := by
    have habs := le_abs_self
      (harperBivariateSmoothRectangle kappa mu
          (a - delta) (b + delta) (c - delta) (d + delta) -
        harperBivariateSmoothRectangle kappa nu
          (a - delta) (b + delta) (c - delta) (d + delta))
    have hle := habs.trans (by simpa only [kappa, mu, nu, E] using hsmooth)
    linarith
  have hupper := smoothRectangle_le_expandedRectangleMass_add_tail
    kappa nu
      (a := a - delta) (b := b + delta)
      (c := c - delta) (d := d + delta)
      (delta := delta) (alpha := alpha)
      (by linarith) (by linarith) hdelta halpha0 htail
  change (1 - alpha) ^ (2 : Nat) * mu.real (Ioc a b ×ˢ Ioc c d) ≤ _
  calc
    _ ≤ harperBivariateSmoothRectangle kappa mu
        (a - delta) (b + delta) (c - delta) (d + delta) := hlower
    _ ≤ harperBivariateSmoothRectangle kappa nu
        (a - delta) (b + delta) (c - delta) (d + delta) + E := hsmoothOne
    _ ≤ nu.real
          (Ioc ((a - delta) - delta) ((b + delta) + delta) ×ˢ
            Ioc ((c - delta) - delta) ((d + delta) + delta)) +
          alpha + E := by
      simpa only [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hupper E
    _ = nu.real
          (Ioc (a - 2 * delta) (b + 2 * delta) ×ˢ
            Ioc (c - 2 * delta) (d + 2 * delta)) + alpha + E := by
      ring_nf
    _ = _ := by rfl

/-- Fully explicit ordinary-rectangle comparison using the tunable Fejer
tail at `delta = r/T`, `alpha = 2/r`. -/
theorem harperScheduledTwoHeightRectangleMass_le_gaussianExpanded_explicit
    (y j : Nat) (t s T r : Real)
    {a b c d : Real} (hab : a ≤ b) (hcd : c ≤ d)
    (hT : 0 < T) (hr : 2 ≤ r)
    (hfrequency :
      4 * T ≤ Real.sqrt (Problem520.harperBlockEndpoint j : Real)) :
    (1 - 2 / r) ^ (2 : Nat) *
        (harperTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y j) t s).real
            (Ioc a b ×ˢ Ioc c d) ≤
      (harperTwoHeightGaussianLaw y
        (Problem520.harperScheduledPrimeBlock y j) t s).real
          (Ioc (a - 2 * (r / T)) (b + 2 * (r / T)) ×ˢ
            Ioc (c - 2 * (r / T)) (d + 2 * (r / T))) +
        2 / r +
        (2 * Real.pi)⁻¹ ^ (2 : Nat) *
          |(b + r / T) - (a - r / T)| *
          |(d + r / T) - (c - r / T)| *
          (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
            (512 * T ^ (5 : Nat) + 128 * T ^ (6 : Nat)) := by
  apply harperScheduledTwoHeightRectangleMass_le_gaussianExpanded
    y j t s T hab hcd hT hfrequency
  · positivity
  · positivity
  · rw [div_le_one (by positivity : (0 : Real) < r)]
    linarith
  · simpa only using harperFejerMeasureScaled_tail_le_two_div hT hr

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperFejerMeasureScaled_tail_le_two_div
#print axioms Erdos.Problem1144.one_sub_sq_le_expanded_cdf_product
#print axioms Erdos.Problem1144.one_sub_sq_mul_rectangleMass_le_smoothExpanded
#print axioms Erdos.Problem1144.smoothRectangle_le_expandedRectangleMass_add_tail
#print axioms Erdos.Problem1144.harperScheduledTwoHeightRectangleMass_le_gaussianExpanded_explicit
