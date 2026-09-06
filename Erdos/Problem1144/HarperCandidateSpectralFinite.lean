import Erdos.Problem1144.HarperCandidateSpectralIntegrability
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- Arithmetic truncation of the squarefree log process. At every fixed time
this equals the literal process once the integer cutoff is large enough. -/
noncomputable def candidateSquarefreeLogApprox (ω : Omega) (N : ℕ) (t : ℝ) : ℝ :=
  GSquarefree ω (min N ⌊Real.exp t⌋₊) / Real.exp (t / 2)

theorem measurable_candidateSquarefreeLogApprox (N : ℕ) :
    Measurable fun z : Omega × ℝ => candidateSquarefreeLogApprox z.1 N z.2 := by
  have hG : Measurable fun z : Omega × ℕ => GSquarefree z.1 z.2 :=
    measurable_from_prod_countable_left measurable_GSquarefree
  exact (hG.comp (measurable_fst.prodMk
    (measurable_const.min (Real.measurable_exp.comp measurable_snd).nat_floor))).div
      (Real.measurable_exp.comp (measurable_snd.div_const 2))

theorem candidate_integrable_squarefreeLogApprox_sq (N : ℕ) (t : ℝ) :
    Integrable (fun ω => candidateSquarefreeLogApprox ω N t ^ 2) mu := by
  have hG := integrable_squarefreeWeightedSum_sq
    (Finset.Icc 1 (min N ⌊Real.exp t⌋₊)) (fun _ => 1)
  simpa only [candidateSquarefreeLogApprox, div_pow, squarefreeWeightedSum, one_mul,
    GSquarefree] using hG.div_const (Real.exp (t / 2) ^ 2)

theorem candidate_integrable_squarefreeLogApprox (N : ℕ) (t : ℝ) :
    Integrable (fun ω => candidateSquarefreeLogApprox ω N t) mu := by
  apply ((candidate_integrable_squarefreeLogApprox_sq N t).add
    (integrable_const (1 : ℝ))).mono'
    ((measurable_candidateSquarefreeLogApprox N).comp
      measurable_prodMk_right).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  change |candidateSquarefreeLogApprox ω N t| ≤ candidateSquarefreeLogApprox ω N t ^ 2 + 1
  nlinarith [sq_nonneg (|candidateSquarefreeLogApprox ω N t| - 1),
    sq_abs (candidateSquarefreeLogApprox ω N t)]

theorem candidate_integral_squarefreeLogApprox_sq_le_one (N : ℕ) (t : ℝ) :
    (∫ ω, candidateSquarefreeLogApprox ω N t ^ 2 ∂mu) ≤ 1 := by
  simp_rw [candidateSquarefreeLogApprox, div_pow]
  rw [integral_div]
  have hexp : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp, div_le_one (Real.exp_pos t)]
  exact (candidate_integral_GSquarefree_sq_le _).trans
    ((Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le (Real.exp_pos t).le))

theorem candidate_integral_abs_squarefreeLogApprox_le_two (N : ℕ) (t : ℝ) :
    (∫ ω, |candidateSquarefreeLogApprox ω N t| ∂mu) ≤ 2 := by
  have hi := candidate_integrable_squarefreeLogApprox N t
  have hs := candidate_integrable_squarefreeLogApprox_sq N t
  have h := integral_mono hi.abs (hs.add (integrable_const (1 : ℝ)))
    (fun ω => show |candidateSquarefreeLogApprox ω N t| ≤
        candidateSquarefreeLogApprox ω N t ^ 2 + 1 by
      nlinarith [sq_nonneg (|candidateSquarefreeLogApprox ω N t| - 1),
        sq_abs (candidateSquarefreeLogApprox ω N t)])
  simp only [Pi.add_apply] at h
  rw [integral_add hs (integrable_const (1 : ℝ))] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith [candidate_integral_squarefreeLogApprox_sq_le_one N t]

theorem candidate_eventually_squarefreeLogApprox_eq (t : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ ω,
      candidateSquarefreeLogApprox ω N t = harperCandidateSquarefreeLogProcess ω t := by
  filter_upwards [eventually_ge_atTop ⌊Real.exp t⌋₊] with N hN ω
  simp only [candidateSquarefreeLogApprox, min_eq_right hN,
    harperCandidateSquarefreeLogProcess_eq_quotient]

/-- Orthogonality bounds a finite real squarefree linear combination by the
sum of the squares of its coefficients. -/
theorem candidate_integral_squarefreeWeightedSum_sq_le
    (s : Finset ℕ) (w : ℕ → ℝ) (hs : ∀ n ∈ s, 0 < n) :
    (∫ ω, squarefreeWeightedSum s w ω ^ 2 ∂mu) ≤ ∑ n ∈ s, w n ^ 2 := by
  classical
  let s' := s.filter Squarefree
  have heq (ω : Omega) : squarefreeWeightedSum s w ω = squarefreeWeightedSum s' w ω := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hns
    have hsq : ¬Squarefree n := by
      intro h
      exact hns (Finset.mem_filter.mpr ⟨hn, h⟩)
    simp [gSquarefree_of_not_squarefree _ hsq]
  simp_rw [heq]
  rw [integral_squarefreeWeightedSum_sq_eq_diag s' w
    (fun n hn => hs n (Finset.mem_filter.mp hn).1)
    (fun _ hn => (Finset.mem_filter.mp hn).2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => sq_nonneg _)

/-- Squared norms of finite complex squarefree linear combinations are
integrable, by their real and imaginary weighted-square expansions. -/
theorem candidate_integrable_complex_squarefree_sum_norm_sq
    (s : Finset ℕ) (c : ℕ → ℂ) :
    Integrable (fun ω => ‖∑ n ∈ s, c n * (gSquarefree ω n : ℂ)‖ ^ 2) mu := by
  have h := (integrable_squarefreeWeightedSum_sq s (fun n => (c n).re)).add
    (integrable_squarefreeWeightedSum_sq s (fun n => (c n).im))
  apply h.congr
  filter_upwards [] with ω
  simp only [Pi.add_apply]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.re_sum, Complex.im_sum, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_add,
    squarefreeWeightedSum, pow_two]

/-- The finite complex version of squarefree orthogonality. -/
theorem candidate_integral_complex_squarefree_sum_norm_sq_le
    (s : Finset ℕ) (c : ℕ → ℂ) (hs : ∀ n ∈ s, 0 < n) :
    (∫ ω, ‖∑ n ∈ s, c n * (gSquarefree ω n : ℂ)‖ ^ 2 ∂mu) ≤
      ∑ n ∈ s, ‖c n‖ ^ 2 := by
  have heq (ω : Omega) : ‖∑ n ∈ s, c n * (gSquarefree ω n : ℂ)‖ ^ 2 =
      squarefreeWeightedSum s (fun n => (c n).re) ω ^ 2 +
        squarefreeWeightedSum s (fun n => (c n).im) ω ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.re_sum, Complex.im_sum,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, zero_add, squarefreeWeightedSum, pow_two]
  simp_rw [heq]
  rw [integral_add (integrable_squarefreeWeightedSum_sq _ _)
    (integrable_squarefreeWeightedSum_sq _ _)]
  calc
    _ ≤ (∑ n ∈ s, (c n).re ^ 2) + ∑ n ∈ s, (c n).im ^ 2 :=
      add_le_add (candidate_integral_squarefreeWeightedSum_sq_le s _ hs)
        (candidate_integral_squarefreeWeightedSum_sq_le s _ hs)
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring

/-- A logarithmic half-line atom with a complex Laplace exponent. -/
noncomputable def candidateComplexLaplaceAtom (s : ℂ) (n : ℕ) : ℝ → ℂ :=
  (Ici (Real.log (n : ℝ))).indicator (fun t => Complex.exp (-s * t))

theorem candidate_integrable_complexLaplaceAtom {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Integrable (candidateComplexLaplaceAtom s n) := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  exact (integrableOn_Ici_iff_integrableOn_Ioi (μ := volume)).mpr
    (integrableOn_exp_mul_complex_Ioi (by simpa using neg_lt_zero.mpr hs) _)

theorem candidate_integral_complexLaplaceAtom {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t, candidateComplexLaplaceAtom s n t) = Complex.exp (-s * Real.log n) / s := by
  rw [candidateComplexLaplaceAtom, integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi,
    integral_exp_mul_complex_Ioi (by simpa using neg_lt_zero.mpr hs)]
  simp

/-- The floor cutoff is exactly a finite sum of logarithmic threshold atoms. -/
theorem candidate_GSquarefree_min_eq_log_indicators (ω : Omega) (N : ℕ) (t : ℝ) :
    GSquarefree ω (min N ⌊Real.exp t⌋₊) =
      ∑ n ∈ Finset.Icc 1 N, if Real.log (n : ℝ) ≤ t then gSquarefree ω n else 0 := by
  classical
  have hset : (Finset.Icc 1 N).filter (fun n : ℕ => Real.log (n : ℝ) ≤ t) =
      Finset.Icc 1 (min N ⌊Real.exp t⌋₊) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨hn, hN⟩, hlog⟩
      exact ⟨hn, hN, (Nat.le_floor_iff (Real.exp_pos t).le).mpr
        ((Real.log_le_iff_le_exp (Nat.cast_pos.mpr hn)).mp hlog)⟩
    · rintro ⟨hn, hN, hfloor⟩
      exact ⟨⟨hn, hN⟩, (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hn)).mpr
        ((Nat.le_floor_iff (Real.exp_pos t).le).mp hfloor)⟩
  rw [← Finset.sum_filter, hset]
  rfl

/-- Fourier's `2π` convention agrees with the complex Laplace exponent in
angular frequency. -/
theorem candidate_angular_phase_exp (σ τ t : ℝ) :
    (Real.fourierChar (-(t * (τ / (2 * Real.pi)))) : ℂ) *
        ((Real.exp (-σ * t) / Real.exp (t / 2) : ℝ) : ℂ) =
      Complex.exp (-(((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) * t) := by
  have hfreq : 2 * Real.pi * (-(t * (τ / (2 * Real.pi)))) = -(t * τ) := by
    field_simp
  rw [Real.fourierChar_apply, hfreq, Complex.ofReal_div, Complex.ofReal_exp,
    Complex.ofReal_exp, div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact finite Dirichlet-polynomial formula for the Fourier transform of
the arithmetic approximation to the squarefree log process. -/
theorem candidate_squarefreeLogApprox_fourier_eq
    (ω : Omega) (N : ℕ) {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    Fourier.fourierIntegral Real.fourierChar volume
      (fun t => ((Real.exp (-σ * t) * candidateSquarefreeLogApprox ω N t : ℝ) : ℂ))
      (τ / (2 * Real.pi)) =
      ∑ n ∈ Finset.Icc 1 N,
        (Complex.exp (-(((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) * Real.log n) /
          (((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)) *
            (gSquarefree ω n : ℂ) := by
  let s : ℂ := ((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I
  have hs : 0 < s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
    linarith
  rw [Fourier.fourierIntegral_def]
  have heq (t : ℝ) :
      Real.fourierChar (-(t * (τ / (2 * Real.pi)))) •
        ((Real.exp (-σ * t) * candidateSquarefreeLogApprox ω N t : ℝ) : ℂ) =
      ∑ n ∈ Finset.Icc 1 N, candidateComplexLaplaceAtom s n t * (gSquarefree ω n : ℂ) := by
    simp only [candidateSquarefreeLogApprox, Complex.ofReal_mul, Complex.ofReal_div,
      Circle.smul_def, smul_eq_mul]
    rw [show (Real.fourierChar (-(t * (τ / (2 * Real.pi)))) : ℂ) *
        ((Real.exp (-σ * t) : ℂ) * ((GSquarefree ω (min N ⌊Real.exp t⌋₊) : ℂ) /
          (Real.exp (t / 2) : ℂ))) =
        ((Real.fourierChar (-(t * (τ / (2 * Real.pi)))) : ℂ) *
          ((Real.exp (-σ * t) / Real.exp (t / 2) : ℝ) : ℂ)) *
            (GSquarefree ω (min N ⌊Real.exp t⌋₊) : ℂ) by push_cast; ring]
    rw [candidate_angular_phase_exp, candidate_GSquarefree_min_eq_log_indicators,
      Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases ht : Real.log (n : ℝ) ≤ t
    · simp [candidateComplexLaplaceAtom, ht, s]
    · simp [candidateComplexLaplaceAtom, ht]
  simp_rw [heq]
  rw [integral_finset_sum (Finset.Icc 1 N)
    (fun n _ => (candidate_integrable_complexLaplaceAtom hs n).mul_const _)]
  apply Finset.sum_congr rfl
  intro n hn
  exact (MeasureTheory.integral_mul_const (μ := volume) (gSquarefree ω n : ℂ)
    (candidateComplexLaplaceAtom s n)).trans
      (congrArg (fun z : ℂ => z * (gSquarefree ω n : ℂ))
        (candidate_integral_complexLaplaceAtom hs n))

/-- The squared Dirichlet coefficient exhibits the exact angular-frequency
denominator. -/
theorem candidate_squarefree_dirichletCoefficient_norm_sq
    (σ τ : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Complex.exp (-(((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) * Real.log n) /
      (((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 =
      (n : ℝ) ^ (-(1 + 2 * σ)) / ((σ + 1 / 2) ^ 2 + τ ^ 2) := by
  rw [norm_div, div_pow]
  have hnum : ‖Complex.exp (-(((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) *
      Real.log n)‖ ^ 2 = (n : ℝ) ^ (-(1 + 2 * σ)) := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    rw [pow_two, ← Real.exp_add, Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
    congr 1
    ring
  rw [hnum, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_I_re, Complex.mul_I_im, neg_zero, add_zero, zero_add]
  congr 1
  ring

/-- Orthogonality supplies a uniform second-moment bound for the literal
Fourier transforms of all arithmetic truncations. -/
theorem candidate_integral_squarefreeLogApprox_fourier_norm_sq_le
    (N : ℕ) {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    (∫ ω, ‖Fourier.fourierIntegral Real.fourierChar volume
      (fun t => ((Real.exp (-σ * t) * candidateSquarefreeLogApprox ω N t : ℝ) : ℂ))
      (τ / (2 * Real.pi))‖ ^ 2 ∂mu) ≤
        (∑' n : ℕ, (n : ℝ) ^ (-(1 + 2 * σ))) / ((σ + 1 / 2) ^ 2 + τ ^ 2) := by
  simp_rw [candidate_squarefreeLogApprox_fourier_eq _ N hσ τ]
  apply (candidate_integral_complex_squarefree_sum_norm_sq_le
    (Finset.Icc 1 N) _ (fun n hn => (Finset.mem_Icc.mp hn).1)).trans
  calc
    _ = (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-(1 + 2 * σ))) /
        ((σ + 1 / 2) ^ 2 + τ ^ 2) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro n hn
      exact candidate_squarefree_dirichletCoefficient_norm_sq σ τ (Finset.mem_Icc.mp hn).1
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (Real.summable_nat_rpow.mpr (by linarith : -(1 + 2 * σ) < -1)).sum_le_tsum
        (Finset.Icc 1 N) (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Finite arithmetic Fourier transforms have finite second moments. -/
theorem candidate_integrable_squarefreeLogApprox_fourier_norm_sq
    (N : ℕ) {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    Integrable (fun ω => ‖Fourier.fourierIntegral Real.fourierChar volume
      (fun t => ((Real.exp (-σ * t) * candidateSquarefreeLogApprox ω N t : ℝ) : ℂ))
      (τ / (2 * Real.pi))‖ ^ 2) mu := by
  simp_rw [candidate_squarefreeLogApprox_fourier_eq _ N hσ τ]
  exact candidate_integrable_complex_squarefree_sum_norm_sq _ _

end Erdos.Problem1144
