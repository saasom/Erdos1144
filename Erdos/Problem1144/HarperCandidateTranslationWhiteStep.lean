import Erdos.Problem1144.HarperCandidateTranslationPrimeCoefficients

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Integrated white-noise step coefficient error

This is the literal complete-model white-noise kernel `a(t-v)/sqrt(v)`.
Each bin uses its right endpoint for its constant approximation. Both the
zero crossing of the process and final bins are covered by the same expected
square envelope as the prime coefficients.
-/

noncomputable def candidateWhiteStepSecondMoment (t y x : ℝ) : ℝ :=
  ∫ ω, (harperCandidateLogProcess ω (t - x) / Real.sqrt x -
    harperCandidateLogProcess ω (t - y) / Real.sqrt y) ^ 2 ∂mu

theorem candidateWhiteStepSecondMoment_nonneg (t y x : ℝ) :
    0 ≤ candidateWhiteStepSecondMoment t y x := integral_nonneg fun _ ↦ sq_nonneg _

theorem measurable_candidateWhiteStepSquare (t y : ℝ) :
    Measurable (fun z : ℝ × Omega ↦
      (harperCandidateLogProcess z.2 (t - z.1) / Real.sqrt z.1 -
        harperCandidateLogProcess z.2 (t - y) / Real.sqrt y) ^ 2) := by
  have hvariable : Measurable (fun z : ℝ × Omega ↦
      harperCandidateLogProcess z.2 (t - z.1) / Real.sqrt z.1) :=
    (measurable_harperCandidateLogProcess.comp
      (measurable_snd.prodMk (measurable_const.sub measurable_fst))).div
        (Real.continuous_sqrt.measurable.comp measurable_fst)
  have hconstant : Measurable (fun z : ℝ × Omega ↦
      harperCandidateLogProcess z.2 (t - y) / Real.sqrt y) :=
    (measurable_harperCandidateLogProcess.comp
      (measurable_snd.prodMk measurable_const)).div_const _
  exact (hvariable.sub hconstant).pow_const 2

theorem measurable_candidateWhiteStepSecondMoment (t y : ℝ) :
    Measurable (candidateWhiteStepSecondMoment t y) :=
  (measurable_candidateWhiteStepSquare t y).stronglyMeasurable.integral_prod_right.measurable

/-- The scalar expectation is uniformly dominated throughout a literal
logarithmic bin. -/
theorem candidateWhiteStepSecondMoment_le_bin
    {t T z h L x : ℝ} (hT : 0 < T) (hTz : T ≤ z) (_hh : 0 ≤ h)
    (htL : t - z ≤ L) (hL : 0 ≤ L) (hx : x ∈ Icc z (z + h)) :
    candidateWhiteStepSecondMoment t (z + h) x ≤
      (4 / T) * candidateLogWindowSecondMoment (t - (z + h)) (t - z) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * (1 + L) := by
  have he := candidate_logCoefficient_difference_sq_le_window hT
    (hTz.trans hx.1) hx.2 (by linarith [hx.1] : (z + h) - x ≤ h)
    (le_refl (t - (z + h))) (by linarith [hx.2] : t - (z + h) ≤ t - x)
    (by linarith [hx.1] : t - x ≤ t - z) htL hL
  simpa only [show (t - z) - (t - (z + h)) = h by ring] using he

theorem candidate_integrableOn_whiteStepSecondMoment
    {t T z h L : ℝ} (hT : 0 < T) (hTz : T ≤ z) (hh : 0 ≤ h)
    (htL : t - z ≤ L) (hL : 0 ≤ L) :
    IntegrableOn (candidateWhiteStepSecondMoment t (z + h)) (Ioc z (z + h)) := by
  refine (integrable_const (μ := volume.restrict (Ioc z (z + h)))
    ((4 / T) * candidateLogWindowSecondMoment (t - (z + h)) (t - z) +
      (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * (1 + L))).mono'
        (measurable_candidateWhiteStepSecondMoment t (z + h)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (candidateWhiteStepSecondMoment_nonneg _ _ _)]
  exact candidateWhiteStepSecondMoment_le_bin hT hTz hh htL hL ⟨hx.1.le, hx.2⟩

/-- Integration over one bin costs exactly its width. -/
theorem candidate_integral_whiteStepSecondMoment_le_bin
    {t T z h L : ℝ} (hT : 0 < T) (hTz : T ≤ z) (hh : 0 ≤ h)
    (htL : t - z ≤ L) (hL : 0 ≤ L) :
    (∫ x in Ioc z (z + h), candidateWhiteStepSecondMoment t (z + h) x) ≤
      h * ((4 / T) * candidateLogWindowSecondMoment (t - (z + h)) (t - z) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * (1 + L)) := by
  have hi := integral_mono_ae (candidate_integrableOn_whiteStepSecondMoment hT hTz hh htL hL)
    (integrable_const (μ := volume.restrict (Ioc z (z + h)))
      ((4 / T) * candidateLogWindowSecondMoment (t - (z + h)) (t - z) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * (1 + L)))
    (show ∀ᵐ x ∂volume.restrict (Ioc z (z + h)),
      candidateWhiteStepSecondMoment t (z + h) x ≤ _ from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact candidateWhiteStepSecondMoment_le_bin hT hTz hh htL hL ⟨hx.1.le, hx.2⟩)
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    Real.volume_real_Ioc_of_le (by linarith : z ≤ z + h), add_sub_cancel_left] using hi

/-- The literal white-noise coefficient step error over all complete bins.
Its leading term is `O(h L²/T)` when `n*h = O(L)`. -/
theorem candidate_sum_integral_whiteStepSecondMoment_le
    {t T h L : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h)
    (htL : t - T + h ≤ L) (hL : 0 ≤ L) :
    (∑ j ∈ Finset.range n, ∫ x in Ioc (T + (j : ℝ) * h) (T + (j : ℝ) * h + h),
      candidateWhiteStepSecondMoment t (T + (j : ℝ) * h + h) x) ≤
      (4 / T) * h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L) := by
  let a := t - T - (n : ℝ) * h
  let F : ℕ → ℝ := fun j ↦ candidateLogWindowSecondMoment
    (a + (j : ℝ) * h) (a + ((j + 1 : ℕ) : ℝ) * h)
  let I : ℕ → ℝ := fun j ↦ candidateLogWindowSecondMoment
    (t - (T + (j : ℝ) * h + h)) (t - (T + (j : ℝ) * h))
  let R := (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * (1 + L)
  have hbin (j : ℕ) :
      (∫ x in Ioc (T + (j : ℝ) * h) (T + (j : ℝ) * h + h),
        candidateWhiteStepSecondMoment t (T + (j : ℝ) * h + h) x) ≤
          h * ((4 / T) * I j + R) := by
    have hjh : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hh
    exact candidate_integral_whiteStepSecondMoment_le_bin hT (by linarith) hh (by linarith) hL
  have hreflect : (∑ j ∈ Finset.range n, I j) = ∑ j ∈ Finset.range n, F j := by
    calc
      _ = ∑ j ∈ Finset.range n, F (n - 1 - j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjn : n - 1 - j + j + 1 = n := by have := Finset.mem_range.mp hj; omega
        have hjR : ((n - 1 - j : ℕ) : ℝ) + (j : ℝ) + 1 = (n : ℝ) := by
          exact_mod_cast hjn
        dsimp only [I, F]
        congr 1 <;> dsimp only [a] <;> push_cast <;> nlinarith
      _ = _ := Finset.sum_range_reflect F n
  have hcover : a + ((n + 1 : ℕ) : ℝ) * h ≤ L := by
    dsimp only [a]
    push_cast
    linarith
  have hd := candidate_sum_logWindowSecondMoment_le_mesh hh hL hcover
  have hd' : h * (∑ j ∈ Finset.range n, F j) ≤
      h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) := by
    simpa only [Nat.cast_one, one_mul] using hd
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun j _ ↦ hbin j)
  have heq : (∑ j ∈ Finset.range n, h * ((4 / T) * I j + R)) =
      (4 / T) * (h * ∑ j ∈ Finset.range n, F j) + R * ((n : ℝ) * h) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, hreflect]
    ring
  rw [heq] at hsum
  have hm := mul_le_mul_of_nonneg_left hd' (by positivity : 0 ≤ 4 / T)
  dsimp only [R] at hsum
  nlinarith

/-- The literal squared step error is integrable jointly in time and signs. -/
theorem candidate_integrable_whiteStepSquare_product
    {t T z h L : ℝ} (hT : 0 < T) (hTz : T ≤ z) (hh : 0 ≤ h)
    (htL : t - z ≤ L) (hL : 0 ≤ L) :
    Integrable (fun q : ℝ × Omega ↦
      (harperCandidateLogProcess q.2 (t - q.1) / Real.sqrt q.1 -
        harperCandidateLogProcess q.2 (t - (z + h)) / Real.sqrt (z + h)) ^ 2)
      ((volume.restrict (Ioc z (z + h))).prod mu) := by
  apply (integrable_prod_iff
    (measurable_candidateWhiteStepSquare t (z + h)).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun x ↦
      candidate_integrable_logCoefficient_difference_sq x (z + h) (t - x) (t - (z + h))
  · simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    exact candidate_integrableOn_whiteStepSecondMoment hT hTz hh htL hL

/-- Fubini identifies the expectation of the squared Hilbert-kernel error
with the integral of the canonical scalar second moments. -/
theorem candidate_integral_whiteStepSquare_swap
    {t T z h L : ℝ} (hT : 0 < T) (hTz : T ≤ z) (hh : 0 ≤ h)
    (htL : t - z ≤ L) (hL : 0 ≤ L) :
    (∫ ω, (∫ x in Ioc z (z + h),
      (harperCandidateLogProcess ω (t - x) / Real.sqrt x -
        harperCandidateLogProcess ω (t - (z + h)) / Real.sqrt (z + h)) ^ 2) ∂mu) =
      ∫ x in Ioc z (z + h), candidateWhiteStepSecondMoment t (z + h) x := by
  exact (integral_integral_swap
    (candidate_integrable_whiteStepSquare_product hT hTz hh htL hL)).symm

/-- The expected sum of the literal squared white-noise kernel errors over
a finite collection of bins. No stochastic-process existence is assumed. -/
theorem candidate_integral_sum_whiteStepSquare_le
    {t T h L : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h)
    (htL : t - T + h ≤ L) (hL : 0 ≤ L) :
    (∫ ω, (∑ j ∈ Finset.range n,
      ∫ x in Ioc (T + (j : ℝ) * h) (T + (j : ℝ) * h + h),
        (harperCandidateLogProcess ω (t - x) / Real.sqrt x -
          harperCandidateLogProcess ω (t - (T + (j : ℝ) * h + h)) /
            Real.sqrt (T + (j : ℝ) * h + h)) ^ 2) ∂mu) ≤
      (4 / T) * h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L) := by
  have hTj (j : ℕ) : T ≤ T + (j : ℝ) * h :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hh)
  have htj (j : ℕ) : t - (T + (j : ℝ) * h) ≤ L := by
    have hj := hTj j
    linarith
  rw [integral_finset_sum]
  · simp_rw [candidate_integral_whiteStepSquare_swap hT (hTj _) hh (htj _) hL]
    exact candidate_sum_integral_whiteStepSecondMoment_le hT hh htL hL
  · intro j _
    exact (candidate_integrable_whiteStepSquare_product
      hT (hTj j) hh (htj j) hL).integral_prod_right

end Erdos.Problem1144
