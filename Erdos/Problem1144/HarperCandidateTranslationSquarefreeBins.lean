import Erdos.Problem1144.HarperCandidateTranslationSquarefree
import Erdos.Problem1144.HarperCandidateTranslationPrimeBins

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-!
# Literal squarefree prime and white-noise step errors

These are separate theorems for the candidate's squarefree process `m`.
They use its proved complete-model interval envelope; they do not identify
squarefree translations with complete-model translations.
-/

noncomputable def candidateSquarefreeWhiteStepSecondMoment (t y x : ℝ) : ℝ :=
  ∫ ω, (harperCandidateSquarefreeLogProcess ω (t - x) / Real.sqrt x -
    harperCandidateSquarefreeLogProcess ω (t - y) / Real.sqrt y) ^ 2 ∂mu

theorem candidateSquarefreeWhiteStepSecondMoment_nonneg (t y x : ℝ) :
    0 ≤ candidateSquarefreeWhiteStepSecondMoment t y x := integral_nonneg fun _ ↦ sq_nonneg _

theorem measurable_candidateSquarefreeWhiteStepSquare (t y : ℝ) :
    Measurable (fun z : ℝ × Omega ↦
      (harperCandidateSquarefreeLogProcess z.2 (t - z.1) / Real.sqrt z.1 -
        harperCandidateSquarefreeLogProcess z.2 (t - y) / Real.sqrt y) ^ 2) := by
  have hvariable : Measurable (fun z : ℝ × Omega ↦
      harperCandidateSquarefreeLogProcess z.2 (t - z.1) / Real.sqrt z.1) :=
    (measurable_harperCandidateSquarefreeLogProcess.comp
      (measurable_snd.prodMk (measurable_const.sub measurable_fst))).div
        (Real.continuous_sqrt.measurable.comp measurable_fst)
  have hconstant : Measurable (fun z : ℝ × Omega ↦
      harperCandidateSquarefreeLogProcess z.2 (t - y) / Real.sqrt y) :=
    (measurable_harperCandidateSquarefreeLogProcess.comp
      (measurable_snd.prodMk measurable_const)).div_const _
  exact (hvariable.sub hconstant).pow_const 2

theorem measurable_candidateSquarefreeWhiteStepSecondMoment (t y : ℝ) :
    Measurable (candidateSquarefreeWhiteStepSecondMoment t y) :=
  (measurable_candidateSquarefreeWhiteStepSquare t y).stronglyMeasurable.integral_prod_right
    |>.measurable

/-- The scalar expectation is uniformly dominated throughout a literal
logarithmic bin. -/
theorem candidateSquarefreeWhiteStepSecondMoment_le_bin
    {t T z h L x : ℝ} (hT : 0 < T) (hTz : T ≤ z) (_hh : 0 ≤ h)
    (htL : t - z ≤ L) (hL : 0 ≤ L) (hx : x ∈ Icc z (z + h)) :
    candidateSquarefreeWhiteStepSecondMoment t (z + h) x ≤
      (4 / T) * candidateLogWindowSecondMoment (t - (z + h)) (t - z) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * (1 + L) := by
  have he := candidate_squarefreeLogCoefficient_difference_sq_le_window hT
    (hTz.trans hx.1) hx.2 (by linarith [hx.1] : (z + h) - x ≤ h)
    (le_refl (t - (z + h))) (by linarith [hx.2] : t - (z + h) ≤ t - x)
    (by linarith [hx.1] : t - x ≤ t - z) htL hL
  simpa only [show (t - z) - (t - (z + h)) = h by ring] using he

theorem candidate_integrableOn_squarefreeWhiteStepSecondMoment
    {t T z h L : ℝ} (hT : 0 < T) (hTz : T ≤ z) (hh : 0 ≤ h)
    (htL : t - z ≤ L) (hL : 0 ≤ L) :
    IntegrableOn (candidateSquarefreeWhiteStepSecondMoment t (z + h)) (Ioc z (z + h)) := by
  refine (integrable_const (μ := volume.restrict (Ioc z (z + h)))
    ((4 / T) * candidateLogWindowSecondMoment (t - (z + h)) (t - z) +
      (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * (1 + L))).mono'
        (measurable_candidateSquarefreeWhiteStepSecondMoment t (z + h)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (candidateSquarefreeWhiteStepSecondMoment_nonneg _ _ _)]
  exact candidateSquarefreeWhiteStepSecondMoment_le_bin hT hTz hh htL hL ⟨hx.1.le, hx.2⟩

/-- Integration over one bin costs exactly its width. -/
theorem candidate_integral_squarefreeWhiteStepSecondMoment_le_bin
    {t T z h L : ℝ} (hT : 0 < T) (hTz : T ≤ z) (hh : 0 ≤ h)
    (htL : t - z ≤ L) (hL : 0 ≤ L) :
    (∫ x in Ioc z (z + h), candidateSquarefreeWhiteStepSecondMoment t (z + h) x) ≤
      h * ((4 / T) * candidateLogWindowSecondMoment (t - (z + h)) (t - z) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * (1 + L)) := by
  have hi := integral_mono_ae
    (candidate_integrableOn_squarefreeWhiteStepSecondMoment hT hTz hh htL hL)
    (integrable_const (μ := volume.restrict (Ioc z (z + h)))
      ((4 / T) * candidateLogWindowSecondMoment (t - (z + h)) (t - z) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * (1 + L)))
    (show ∀ᵐ x ∂volume.restrict (Ioc z (z + h)),
      candidateSquarefreeWhiteStepSecondMoment t (z + h) x ≤ _ from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact candidateSquarefreeWhiteStepSecondMoment_le_bin hT hTz hh htL hL ⟨hx.1.le, hx.2⟩)
  simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    Real.volume_real_Ioc_of_le (by linarith : z ≤ z + h), add_sub_cancel_left] using hi

/-- The literal white-noise coefficient step error over all complete bins.
Its leading term is `O(h L²/T)` when `n*h = O(L)`. -/
theorem candidate_sum_integral_squarefreeWhiteStepSecondMoment_le
    {t T h L : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h)
    (htL : t - T + h ≤ L) (hL : 0 ≤ L) :
    (∑ j ∈ Finset.range n, ∫ x in Ioc (T + (j : ℝ) * h) (T + (j : ℝ) * h + h),
      candidateSquarefreeWhiteStepSecondMoment t (T + (j : ℝ) * h + h) x) ≤
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
        candidateSquarefreeWhiteStepSecondMoment t (T + (j : ℝ) * h + h) x) ≤
          h * ((4 / T) * I j + R) := by
    have hjh : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hh
    exact candidate_integral_squarefreeWhiteStepSecondMoment_le_bin
      hT (by linarith) hh (by linarith) hL
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
theorem candidate_integrable_squarefreeWhiteStepSquare_product
    {t T z h L : ℝ} (hT : 0 < T) (hTz : T ≤ z) (hh : 0 ≤ h)
    (htL : t - z ≤ L) (hL : 0 ≤ L) :
    Integrable (fun q : ℝ × Omega ↦
      (harperCandidateSquarefreeLogProcess q.2 (t - q.1) / Real.sqrt q.1 -
        harperCandidateSquarefreeLogProcess q.2 (t - (z + h)) / Real.sqrt (z + h)) ^ 2)
      ((volume.restrict (Ioc z (z + h))).prod mu) := by
  apply (integrable_prod_iff
    (measurable_candidateSquarefreeWhiteStepSquare t (z + h)).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun x ↦
      candidate_integrable_squarefreeLogCoefficient_difference_sq x (z + h) (t - x) (t - (z + h))
  · simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    exact candidate_integrableOn_squarefreeWhiteStepSecondMoment hT hTz hh htL hL

/-- Fubini identifies the expectation of the squared Hilbert-kernel error
with the integral of the canonical scalar second moments. -/
theorem candidate_integral_squarefreeWhiteStepSquare_swap
    {t T z h L : ℝ} (hT : 0 < T) (hTz : T ≤ z) (hh : 0 ≤ h)
    (htL : t - z ≤ L) (hL : 0 ≤ L) :
    (∫ ω, (∫ x in Ioc z (z + h),
      (harperCandidateSquarefreeLogProcess ω (t - x) / Real.sqrt x -
        harperCandidateSquarefreeLogProcess ω (t - (z + h)) / Real.sqrt (z + h)) ^ 2) ∂mu) =
      ∫ x in Ioc z (z + h), candidateSquarefreeWhiteStepSecondMoment t (z + h) x := by
  exact (integral_integral_swap
    (candidate_integrable_squarefreeWhiteStepSquare_product hT hTz hh htL hL)).symm

/-- The expected sum of the literal squared white-noise kernel errors over
a finite collection of bins. No stochastic-process existence is assumed. -/
theorem candidate_integral_sum_squarefreeWhiteStepSquare_le
    {t T h L : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h)
    (htL : t - T + h ≤ L) (hL : 0 ≤ L) :
    (∫ ω, (∑ j ∈ Finset.range n,
      ∫ x in Ioc (T + (j : ℝ) * h) (T + (j : ℝ) * h + h),
        (harperCandidateSquarefreeLogProcess ω (t - x) / Real.sqrt x -
          harperCandidateSquarefreeLogProcess ω (t - (T + (j : ℝ) * h + h)) /
            Real.sqrt (T + (j : ℝ) * h + h)) ^ 2) ∂mu) ≤
      (4 / T) * h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L) := by
  have hTj (j : ℕ) : T ≤ T + (j : ℝ) * h :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hh)
  have htj (j : ℕ) : t - (T + (j : ℝ) * h) ≤ L := by
    have hj := hTj j
    linarith
  rw [integral_finset_sum]
  · simp_rw [candidate_integral_squarefreeWhiteStepSquare_swap hT (hTj _) hh (htj _) hL]
    exact candidate_sum_integral_squarefreeWhiteStepSecondMoment_le hT hh htL hL
  · intro j _
    exact (candidate_integrable_squarefreeWhiteStepSquare_product
      hT (hTj j) hh (htj j) hL).integral_prod_right

noncomputable def candidateSquarefreePrimeStepEnergy (ω : Omega) (t T h : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ∑ p ∈ candidateLogPrimeBin (T + (j : ℝ) * h) h,
    (Real.log (p : ℝ) / p) *
      (harperCandidateSquarefreeLogProcess ω (t - Real.log (p : ℝ)) / Real.sqrt (Real.log (p : ℝ)) -
        harperCandidateSquarefreeLogProcess ω (t - (T + (j : ℝ) * h + h)) /
          Real.sqrt (T + (j : ℝ) * h + h)) ^ 2

theorem candidateSquarefreePrimeStepEnergy_nonneg (ω : Omega) (t T h : ℝ) (n : ℕ) :
    0 ≤ candidateSquarefreePrimeStepEnergy ω t T h n := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (candidate_logPrimeBin_weight_nonneg hp) (sq_nonneg _)

theorem candidate_integrable_squarefreePrimeStepEnergy (t T h : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ candidateSquarefreePrimeStepEnergy ω t T h n) mu := by
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro p _
  exact (candidate_integrable_squarefreeLogCoefficient_difference_sq
    (Real.log (p : ℝ)) (T + (j : ℝ) * h + h)
    (t - Real.log (p : ℝ)) (t - (T + (j : ℝ) * h + h))).const_mul _

theorem candidate_integral_squarefreePrimeStepEnergy_eq_sum (t T h : ℝ) (n : ℕ) :
    (∫ ω, candidateSquarefreePrimeStepEnergy ω t T h n ∂mu) =
      ∑ j ∈ Finset.range n, ∑ p ∈ candidateLogPrimeBin (T + (j : ℝ) * h) h,
        (Real.log (p : ℝ) / p) *
          (∫ ω, (harperCandidateSquarefreeLogProcess ω (t - Real.log (p : ℝ)) /
            Real.sqrt (Real.log (p : ℝ)) -
              harperCandidateSquarefreeLogProcess ω (t - (T + (j : ℝ) * h + h)) /
                Real.sqrt (T + (j : ℝ) * h + h)) ^ 2 ∂mu) := by
  unfold candidateSquarefreePrimeStepEnergy
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
    · intro p _
      exact (candidate_integrable_squarefreeLogCoefficient_difference_sq _ _ _ _).const_mul _
  · intro j _
    exact integrable_finset_sum _ fun p _ ↦
      (candidate_integrable_squarefreeLogCoefficient_difference_sq _ _ _ _).const_mul _

/-- Finite-scale replacement bound for the actual primes in every bin. -/
theorem candidate_integral_squarefreePrimeStepEnergy_le_of_mass
    {t T h L C : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h) (hL : 0 ≤ L)
    (htL : t - T + h ≤ L) (hC : 0 ≤ C)
    (hmass : ∀ j ∈ Finset.range n,
      Problem520.weightedPrimeReciprocalBlock ⌊Real.exp (T + (j : ℝ) * h)⌋₊
        ⌊Real.exp (T + (j : ℝ) * h + h)⌋₊ ≤ C * h) :
    (∫ ω, candidateSquarefreePrimeStepEnergy ω t T h n ∂mu) ≤
      C * ((4 / T) * h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L)) := by
  let r : ℕ → ℕ := fun j ↦ n - 1 - j
  let z : ℕ → ℝ := fun j ↦ T + (r j : ℝ) * h
  let a := t - T - (n : ℝ) * h
  have hr (j : ℕ) (hj : j ∈ Finset.range n) : r j ∈ Finset.range n := by
    dsimp only [r]
    apply Finset.mem_range.mpr
    have := Finset.mem_range.mp hj
    omega
  have hcast (j : ℕ) (hj : j ∈ Finset.range n) : (r j : ℝ) + (j : ℝ) + 1 = (n : ℝ) := by
    have hnat : r j + j + 1 = n := by dsimp only [r]; have := Finset.mem_range.mp hj; omega
    exact_mod_cast hnat
  have heq (j : ℕ) (hj : j ∈ Finset.range n) :
      a + (j : ℝ) * h = t - (z j + h) ∧
        a + ((j + 1 : ℕ) : ℝ) * h = t - z j := by
    have hc := hcast j hj
    dsimp only [a, z]
    push_cast
    constructor <;> nlinarith
  have hcover : a + ((n + 1 : ℕ) : ℝ) * h ≤ L := by
    dsimp only [a]
    push_cast
    linarith
  have hbound := candidate_sum_weighted_squarefreeLogCoefficient_difference_sq_le
    (fun j ↦ candidateLogPrimeBin (z j) h)
    (fun _ p ↦ Real.log (p : ℝ) / p)
    (fun _ p ↦ Real.log (p : ℝ)) (fun j _ ↦ z j + h)
    (fun j _ ↦ t - (z j + h)) (fun _ p ↦ t - Real.log (p : ℝ))
    (a := a) (L := L) (h := h) (C := C) (T := T) (d := h) (n := n) (k := 1)
    hh hL hT hC hcover
    (fun _ _ _ hp ↦ candidate_logPrimeBin_weight_nonneg hp)
    (by intro j hj; exact hmass (r j) (hr j hj))
    (by intro j hj p hp
        have hlog := (candidate_mem_logPrimeBin_log_bounds hp).2.1
        have hn := mul_nonneg (Nat.cast_nonneg (r j)) hh
        dsimp only [z] at hlog
        linarith)
    (fun _ _ _ hp ↦ (candidate_mem_logPrimeBin_log_bounds hp).2.2)
    (by intro j hj p hp; have hb := (candidate_mem_logPrimeBin_log_bounds hp).2.1; linarith)
    (by intro j hj p hp; exact (heq j hj).1.le)
    (by intro j hj p hp; have hb := (candidate_mem_logPrimeBin_log_bounds hp).2.2; linarith)
    (by intro j hj p hp
        have hb := (candidate_mem_logPrimeBin_log_bounds hp).2.1
        rw [(heq j hj).2]
        linarith)
  simp only [Nat.cast_one, one_mul, mul_one] at hbound
  rw [candidate_integral_squarefreePrimeStepEnergy_eq_sum]
  have hreflect := Finset.sum_range_reflect
    (fun j ↦ ∑ p ∈ candidateLogPrimeBin (T + (j : ℝ) * h) h,
      (Real.log (p : ℝ) / p) *
        (∫ ω, (harperCandidateSquarefreeLogProcess ω (t - Real.log (p : ℝ)) /
          Real.sqrt (Real.log (p : ℝ)) -
            harperCandidateSquarefreeLogProcess ω (t - (T + (j : ℝ) * h + h)) /
              Real.sqrt (T + (j : ℝ) * h + h)) ^ 2 ∂mu)) n
  change _ ≤ _ at hbound
  dsimp only [z, r] at hbound
  rw [hreflect] at hbound
  exact hbound

/-- The finite literal prime replacement estimate with the PNT relative
mass error as its sole arithmetic input. -/
theorem candidate_integral_squarefreePrimeStepEnergy_le
    {t T h L : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 < h) (hL : 0 ≤ L)
    (htL : t - T + h ≤ L)
    (herr : ∀ j ∈ Finset.range n,
      |Problem520.weightedPrimeReciprocalBlock ⌊Real.exp (T + (j : ℝ) * h)⌋₊
        ⌊Real.exp (T + (j : ℝ) * h + h)⌋₊ / h - 1| ≤ 1) :
    (∫ ω, candidateSquarefreePrimeStepEnergy ω t T h n ∂mu) ≤
      2 * ((4 / T) * h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L)) := by
  exact candidate_integral_squarefreePrimeStepEnergy_le_of_mass hT hh.le hL htL (by norm_num)
    (fun j hj ↦ candidate_logPrimeBin_mass_le_two_mul hh (herr j hj))

/-- Literal prime replacement error decays faster than every fixed power,
uniformly in the coordinate and number of bins. The effective PNT is used
here; no bin-mass hypothesis remains in the conclusion. -/
theorem candidate_eventually_scaled_squarefreePrimeStepEnergy_lt
    (D q : ℝ) {ν ε : ℝ} (hD : 0 ≤ D) (hν : 0 < ν) (hνPNT : ν < 1 / 10)
    (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, ∀ n : ℕ,
      t - T ≤ D * T → (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      T ^ q * (∫ ω, candidateSquarefreePrimeStepEnergy ω t T (Real.exp (-(T ^ ν))) n ∂mu) < ε := by
  let C := 2 * ((D + 2) * (4 * (D + 1) * Real.exp 1 + 3 * D))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hrate : Tendsto (fun T : ℝ ↦ C * (T ^ (q + 2) * Real.exp (-(T ^ ν))))
      atTop (𝓝 0) := by simpa using (candidate_tendsto_rpow_mul_mesh (q + 2) hν).const_mul C
  have hpnt := candidate_eventually_log_prime_bin_relative_error (D + 1) 0 hνPNT
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_order.mp hrate).2 ε hε, hpnt] with T hT hrateT hpntT
  intro t n ht hn
  let h := Real.exp (-(T ^ ν))
  have hh : 0 < h := Real.exp_pos _
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (Real.rpow_nonneg (by linarith : 0 ≤ T) ν))
  have hT0 : 0 < T := by linarith
  have herr (j : ℕ) (hj : j ∈ Finset.range n) :
      |Problem520.weightedPrimeReciprocalBlock ⌊Real.exp (T + (j : ℝ) * h)⌋₊
        ⌊Real.exp (T + (j : ℝ) * h + h)⌋₊ / h - 1| ≤ 1 := by
    have hjR : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
    have hjh := mul_le_mul_of_nonneg_right hjR hh.le
    have hm := hpntT (T + (j : ℝ) * h)
      ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hh.le), by linarith⟩
    simpa only [Real.rpow_zero, one_mul] using hm.le
  have hfinite := candidate_integral_squarefreePrimeStepEnergy_le (t := t) (T := T) (h := h)
    (L := D * T + 1) (n := n) hT0 hh (by positivity) (by linarith) herr
  have hpoly := candidate_whiteStep_bound_le_polynomial hT hh.le hh1 hD
    (mul_nonneg (Nat.cast_nonneg n) hh.le) hn
  have hbound := hfinite.trans (mul_le_mul_of_nonneg_left hpoly (by norm_num : (0 : ℝ) ≤ 2))
  have hm := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hT0.le q)
  apply hm.trans_lt
  have heq : T ^ q * (2 * ((D + 2) * (4 * (D + 1) * Real.exp 1 + 3 * D) * h * T ^ 2)) =
      C * (T ^ (q + 2) * h) := by
    rw [Real.rpow_add hT0, Real.rpow_two]
    dsimp only [C]
    ring
  rw [heq]
  exact hrateT

theorem candidate_eventually_scaled_squarefreeWhiteStepSquare_lt
    (D q : ℝ) {ν ε : ℝ} (hD : 0 ≤ D) (hν : 0 < ν) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, ∀ n : ℕ,
      t - T ≤ D * T → (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      T ^ q * (∫ ω, (∑ j ∈ Finset.range n,
        ∫ x in Ioc (T + (j : ℝ) * Real.exp (-(T ^ ν)))
          (T + (j : ℝ) * Real.exp (-(T ^ ν)) + Real.exp (-(T ^ ν))),
          (harperCandidateSquarefreeLogProcess ω (t - x) / Real.sqrt x -
            harperCandidateSquarefreeLogProcess ω
              (t - (T + (j : ℝ) * Real.exp (-(T ^ ν)) + Real.exp (-(T ^ ν)))) /
                Real.sqrt (T + (j : ℝ) * Real.exp (-(T ^ ν)) +
                  Real.exp (-(T ^ ν)))) ^ 2) ∂mu) < ε := by
  let C := (D + 2) * (4 * (D + 1) * Real.exp 1 + 3 * D)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hrate : Tendsto (fun T : ℝ ↦ C * (T ^ (q + 2) * Real.exp (-(T ^ ν))))
      atTop (𝓝 0) := by simpa using (candidate_tendsto_rpow_mul_mesh (q + 2) hν).const_mul C
  filter_upwards [eventually_ge_atTop (1 : ℝ), (tendsto_order.mp hrate).2 ε hε] with T hT hrateT
  intro t n ht hn
  let h := Real.exp (-(T ^ ν))
  have hh : 0 ≤ h := (Real.exp_pos _).le
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (Real.rpow_nonneg (by linarith : 0 ≤ T) ν))
  have hT0 : 0 < T := by linarith
  have hfinite := candidate_integral_sum_squarefreeWhiteStepSquare_le (t := t) (T := T) (h := h)
    (L := D * T + 1) (n := n) hT0 hh (by linarith) (by positivity)
  have hpoly := candidate_whiteStep_bound_le_polynomial hT hh hh1 hD
    (mul_nonneg (Nat.cast_nonneg n) hh) hn
  have hbound := hfinite.trans hpoly
  have hm := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hT0.le q)
  apply hm.trans_lt
  have heq : T ^ q * (C * h * T ^ 2) = C * (T ^ (q + 2) * h) := by
    rw [Real.rpow_add hT0, Real.rpow_two]
    ring
  change T ^ q * (C * h * T ^ 2) < ε
  rw [heq]
  exact hrateT

end Erdos.Problem1144
