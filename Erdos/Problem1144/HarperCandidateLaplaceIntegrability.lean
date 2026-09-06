import Erdos.Problem1144.HarperCandidateSquareError
import Erdos.Problem1144.HarperCandidateLogProcess
import Erdos.Problem1144.HarperCandidateEnvelope
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Absolute integrability of the candidate's full random Laplace transform

The squarefree-kernel expansion gives a logarithmic second-moment bound for
the complete sum. Fubini consequently gives almost-sure absolute Laplace
integrability at every fixed positive damping parameter, under the original
law and under every finite-cylinder conditional law.
-/

theorem candidate_integrable_normSum_sq (N : ℕ) :
    Integrable (fun ω : Omega ↦ normSum ω N ^ 2) mu := by
  simp_rw [normSum_eq_canonicalWeightedSum]
  exact integrable_squarefreeWeightedSum_sq _ _

/-- The complete-model second moment is bounded by the harmonic sum of the
squarefree coefficient majorants. -/
theorem candidate_integral_normSum_sq_le_harmonic (N : ℕ) :
    (∫ ω, normSum ω N ^ 2 ∂mu) ≤ (harmonic (N + 1) : ℝ) := by
  simp_rw [normSum_eq_canonicalWeightedSum]
  rw [integral_squarefreeWeightedSum_sq_eq_diag _ _
    (fun _ hd ↦ trackBGridErrorCanonicalSupport_pos hd)
    (fun _ hd ↦ trackBGridErrorCanonicalSupport_squarefree hd)]
  calc
    _ ≤ ∑ d ∈ trackBGridErrorCanonicalSupport N, (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos := trackBGridErrorCanonicalSupport_pos hd
      have hle : trackBCompleteCanonicalWeight N d ≤ (Real.sqrt (d : ℝ))⁻¹ := by
        have h := trackBGridErrorCanonicalWeight_le_zero_aux (Nat.succ_pos N) hdpos
        change trackBCompleteCanonicalWeight N d - (Real.sqrt (d : ℝ))⁻¹ ≤ 0 at h
        linarith
      have hnonneg : 0 ≤ trackBCompleteCanonicalWeight N d := by
        unfold trackBCompleteCanonicalWeight
        positivity
      calc
        trackBCompleteCanonicalWeight N d ^ 2 ≤ (Real.sqrt (d : ℝ))⁻¹ ^ 2 :=
          pow_le_pow_left₀ hnonneg hle 2
        _ = (d : ℝ)⁻¹ := by rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    _ ≤ ∑ d ∈ Finset.Icc 1 (N + 1), (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro d _ _
        positivity
    _ = (harmonic (N + 1) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem candidate_integrable_logProcess (t : ℝ) :
    Integrable (fun ω ↦ harperCandidateLogProcess ω t) mu := by
  apply Integrable.of_bound
    (measurable_harperCandidateLogProcess.comp measurable_prodMk_right).aestronglyMeasurable
    ((⌊Real.exp t⌋₊ : ℝ) / Real.exp (t / 2))
  filter_upwards [] with ω
  change ‖harperCandidateLogProcess ω t‖ ≤ (⌊Real.exp t⌋₊ : ℝ) / Real.exp (t / 2)
  by_cases ht : 0 ≤ t
  · simp only [harperCandidateLogProcess, if_pos ht, Real.norm_eq_abs, abs_div,
      abs_of_pos (Real.exp_pos _)]
    exact div_le_div_of_nonneg_right (abs_S_le ω _) (Real.exp_pos _).le
  · simp only [harperCandidateLogProcess, if_neg ht, norm_zero]
    positivity

theorem candidate_integrable_logProcess_sq (t : ℝ) :
    Integrable (fun ω ↦ harperCandidateLogProcess ω t ^ 2) mu := by
  by_cases ht : 0 ≤ t
  · have hcut := harperCandidateLogCutoff_pos ht
    have heq (ω : Omega) : harperCandidateLogProcess ω t =
        normSum ω (⌊Real.exp t⌋₊ - 1) * harperCandidateLogNormalization t := by
      rw [harperCandidateLogProcess_eq_cutoffNormSum_mul ω ht,
        normSum_eq_cutoffNormSum_succ, Nat.sub_add_cancel hcut]
    simp_rw [heq, mul_pow]
    exact (candidate_integrable_normSum_sq _).mul_const _
  · simpa only [harperCandidateLogProcess, if_neg ht, zero_pow (by decide : 2 ≠ 0)]
      using (integrable_const (μ := mu) (0 : ℝ))

/-- Candidate equation (2), with the explicit constant one. -/
theorem candidate_integral_logProcess_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, harperCandidateLogProcess ω t ^ 2 ∂mu) ≤ 1 + t := by
  have hcut := harperCandidateLogCutoff_pos ht
  have heq (ω : Omega) : harperCandidateLogProcess ω t =
      normSum ω (⌊Real.exp t⌋₊ - 1) * harperCandidateLogNormalization t := by
    rw [harperCandidateLogProcess_eq_cutoffNormSum_mul ω ht,
      normSum_eq_cutoffNormSum_succ, Nat.sub_add_cancel hcut]
  have hfactor := harperCandidateLogNormalization_mem_Icc t
  calc
    _ ≤ ∫ ω, normSum ω (⌊Real.exp t⌋₊ - 1) ^ 2 ∂mu := by
      apply integral_mono (candidate_integrable_logProcess_sq t)
        (candidate_integrable_normSum_sq _)
      intro ω
      dsimp only
      rw [heq, mul_pow]
      have hf : harperCandidateLogNormalization t ^ 2 ≤ 1 := by nlinarith [hfactor.1, hfactor.2]
      exact mul_le_of_le_one_right (sq_nonneg _) hf
    _ ≤ (harmonic ⌊Real.exp t⌋₊ : ℝ) := by
      simpa only [Nat.sub_add_cancel hcut] using
        candidate_integral_normSum_sq_le_harmonic (⌊Real.exp t⌋₊ - 1)
    _ ≤ 1 + t := by
      simpa only [Real.log_exp] using
        harmonic_floor_le_one_add_log (Real.exp t) (Real.one_le_exp_iff.mpr ht)

/-- A deliberately simple first-moment consequence sufficient for Fubini. -/
theorem candidate_integral_abs_logProcess_le {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, |harperCandidateLogProcess ω t| ∂mu) ≤ 2 + t := by
  have hpoint (ω : Omega) : |harperCandidateLogProcess ω t| ≤
      harperCandidateLogProcess ω t ^ 2 + 1 := by
    have hs := sq_abs (harperCandidateLogProcess ω t)
    nlinarith [sq_nonneg (|harperCandidateLogProcess ω t| - 1)]
  have h := integral_mono (candidate_integrable_logProcess t).abs
    ((candidate_integrable_logProcess_sq t).add (integrable_const (1 : ℝ))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (candidate_integrable_logProcess_sq t) (integrable_const (1 : ℝ))] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith [candidate_integral_logProcess_sq_le ht]

/-- The first-moment majorant is integrable against every positive
exponential damping rate. -/
theorem candidate_integrable_laplace_majorant {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-t / T) * (2 + t)) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-t / T)) (Ioi 0) := by
    simpa only [Real.rpow_one, div_eq_mul_inv, mul_comm, mul_neg, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := 1) (p := 1) (b := T⁻¹) (by norm_num) (by norm_num) (inv_pos.mpr hT)
  have he : IntegrableOn (fun t : ℝ ↦ Real.exp (-t / T)) (Ioi 0) := by
    simpa only [div_eq_mul_inv, mul_comm, mul_neg, neg_mul] using
      integrableOn_exp_mul_Ioi (a := -T⁻¹) (neg_lt_zero.mpr (inv_pos.mpr hT)) 0
  have hs : IntegrableOn (fun t : ℝ ↦ 2 * Real.exp (-t / T) +
      t * Real.exp (-t / T)) (Ioi 0) := (he.const_mul 2).add hi
  refine hs.congr (ae_of_all _ fun t ↦ ?_)
  ring

/-- Joint absolute integrability of the full process, not a smooth-prime
truncation. This is the Fubini input for the real Laplace transform. -/
theorem candidate_integrable_laplace_product {T : ℝ} (hT : 0 < T) :
    Integrable (fun z : ℝ × Omega ↦ Real.exp (-z.1 / T) *
      harperCandidateLogProcess z.2 z.1) ((volume.restrict (Ioi 0)).prod mu) := by
  let F : ℝ × Omega → ℝ := fun z ↦ Real.exp (-z.1 / T) *
    harperCandidateLogProcess z.2 z.1
  have hF : Measurable F := by
    exact (Real.measurable_exp.comp (measurable_fst.neg.div_const T)).mul
      (measurable_harperCandidateLogProcess.comp measurable_swap)
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun t ↦
      (candidate_integrable_logProcess t).const_mul (Real.exp (-t / T))
  · apply (candidate_integrable_laplace_majorant hT).mono'
      hF.norm.aestronglyMeasurable.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖∫ ω, ‖Real.exp (-t / T) * harperCandidateLogProcess ω t‖ ∂mu‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (candidate_integral_abs_logProcess_le ht.le)
      (Real.exp_pos _).le

/-- At every fixed `T > 0`, the full real Laplace transform is absolutely
integrable for almost every multiplicative-sign world. -/
theorem candidate_ae_integrable_laplace {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂mu, IntegrableOn
      (fun t ↦ Real.exp (-t / T) * harperCandidateLogProcess ω t) (Ioi 0) :=
  (candidate_integrable_laplace_product hT).prod_left_ae

/-- Conditioning on any fixed finite assignment preserves the almost-sure
Laplace integrability conclusion. -/
theorem candidateCylinderLaw_ae_integrable_laplace
    (s : Finset ℕ) (η : s → Bool) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, IntegrableOn
      (fun t ↦ Real.exp (-t / T) * harperCandidateLogProcess ω t) (Ioi 0) := by
  exact ProbabilityTheory.cond_absolutelyContinuous.ae_le (candidate_ae_integrable_laplace hT)

/-- The full Laplace transform itself is an integrable random variable. -/
theorem candidate_integrable_laplaceTransform {T : ℝ} (hT : 0 < T) :
    Integrable (fun ω ↦ ∫ t in Ioi 0,
      Real.exp (-t / T) * harperCandidateLogProcess ω t) mu :=
  (candidate_integrable_laplace_product hT).integral_prod_right

end Erdos.Problem1144
