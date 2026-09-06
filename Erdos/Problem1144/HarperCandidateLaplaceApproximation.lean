import Erdos.Problem1144.HarperCandidateLaplaceIntegrability
import Erdos.Problem1144.HarperCandidateLogScreen
import Erdos.Problem1144.HarperCandidateLaplaceSmooth
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-!
# Approximating the full Laplace transform by finite smooth transforms

The smooth cutoffs eventually equal the complete process at each fixed time.
Their first moments have one common integrable exponential majorant. Thus
their Laplace transforms converge in mean, without an infinite Euler-product
or analytic-continuation construction.
-/

theorem candidate_smoothSquareKernelWeight_le_harmonic (X N : ℕ) :
    smoothSquareKernelWeight X N ≤ (harmonic N : ℝ) := by
  classical
  unfold smoothSquareKernelWeight smoothSquareKernelSet
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N, (d : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro d _ _
      positivity
    _ = _ := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem candidate_integrable_logOld_sq (X : ℕ) (t : ℝ) :
    Integrable (fun ω ↦ harperCandidateLogOld ω X t ^ 2) mu := by
  unfold harperCandidateLogOld
  simp_rw [mul_pow]
  exact (integrable_smoothProcess_sq X _).mul_const _

theorem candidate_integrable_logOld (X : ℕ) (t : ℝ) :
    Integrable (fun ω ↦ harperCandidateLogOld ω X t) mu := by
  apply ((candidate_integrable_logOld_sq X t).add (integrable_const (1 : ℝ))).mono'
    (measurable_harperCandidateLogOld X t).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs]
  change |harperCandidateLogOld ω X t| ≤ harperCandidateLogOld ω X t ^ 2 + 1
  nlinarith [sq_nonneg (|harperCandidateLogOld ω X t| - 1),
    sq_abs (harperCandidateLogOld ω X t)]

/-- Uniform complete-model second moment after any smooth-prime truncation.
Nonnegative square-product correlations make the truncation harmless here. -/
theorem candidate_integral_logOld_sq_le (X : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, harperCandidateLogOld ω X t ^ 2 ∂mu) ≤ 1 + t := by
  let N := ⌊Real.exp t⌋₊
  have hN : 0 < N := harperCandidateLogCutoff_pos ht
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hf := harperCandidateLogNormalization_mem_Icc t
  have hfsq : harperCandidateLogNormalization t ^ 2 ≤ 1 := by nlinarith [hf.1, hf.2]
  calc
    _ ≤ ∫ ω, smoothProcess ω X N ^ 2 ∂mu := by
      apply integral_mono (candidate_integrable_logOld_sq X t) (integrable_smoothProcess_sq X N)
      intro ω
      dsimp only [harperCandidateLogOld]
      rw [mul_pow]
      exact mul_le_of_le_one_right (sq_nonneg _) hfsq
    _ = smoothPairCount X N / N := by
      rw [integral_smoothProcess_sq_eq_smoothPairCount_div, Real.sq_sqrt (Nat.cast_nonneg N)]
    _ ≤ smoothSquareKernelWeight X N := by
      exact (div_le_iff₀ hNR).mpr
        (by simpa only [mul_comm] using smoothPairCount_le_mul_smoothSquareKernelWeight X N)
    _ ≤ (harmonic N : ℝ) := candidate_smoothSquareKernelWeight_le_harmonic X N
    _ ≤ 1 + t := by
      simpa only [Real.log_exp] using
        harmonic_floor_le_one_add_log (Real.exp t) (Real.one_le_exp_iff.mpr ht)

theorem candidate_integral_abs_logOld_le (X : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ ω, |harperCandidateLogOld ω X t| ∂mu) ≤ 2 + t := by
  have hpoint (ω : Omega) : |harperCandidateLogOld ω X t| ≤
      harperCandidateLogOld ω X t ^ 2 + 1 := by
    nlinarith [sq_nonneg (|harperCandidateLogOld ω X t| - 1),
      sq_abs (harperCandidateLogOld ω X t)]
  have h := integral_mono (candidate_integrable_logOld X t).abs
    ((candidate_integrable_logOld_sq X t).add (integrable_const (1 : ℝ))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (candidate_integrable_logOld_sq X t) (integrable_const (1 : ℝ))] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith [candidate_integral_logOld_sq_le X ht]

theorem candidate_integrable_smooth_laplace_product (X : ℕ) {T : ℝ} (hT : 0 < T) :
    Integrable (fun z : ℝ × Omega ↦ Real.exp (-z.1 / T) *
      harperCandidateLogOld z.2 X z.1) ((volume.restrict (Ioi 0)).prod mu) := by
  let F : ℝ × Omega → ℝ := fun z ↦ Real.exp (-z.1 / T) *
    harperCandidateLogOld z.2 X z.1
  have hproc : Measurable (fun z : ℝ × Omega => harperCandidateLogOld z.2 X z.1) :=
    (measurable_harperCandidateLogOld_joint X).comp (f := Prod.swap) measurable_swap
  have hexp : Measurable (fun z : ℝ × Omega => Real.exp (-z.1 / T)) :=
    Real.measurable_exp.comp (measurable_fst.neg.div_const T)
  have hF : Measurable F := hexp.mul hproc
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun t ↦ (candidate_integrable_logOld X t).const_mul (Real.exp (-t / T))
  · apply (candidate_integrable_laplace_majorant hT).mono'
      hF.norm.aestronglyMeasurable.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖∫ ω, ‖Real.exp (-t / T) * harperCandidateLogOld ω X t‖ ∂mu‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (candidate_integral_abs_logOld_le X ht.le)
      (Real.exp_pos _).le

/-- At each fixed nonnegative time the prime-smooth process eventually
equals the complete process identically in the sign world. -/
theorem candidate_eventually_logOld_eq_logProcess {t : ℝ} (ht : 0 ≤ t) :
    ∀ᶠ X : ℕ in atTop, ∀ ω, harperCandidateLogOld ω X t =
      harperCandidateLogProcess ω t := by
  filter_upwards [eventually_gt_atTop ⌊Real.exp t⌋₊] with X hX ω
  rw [harperCandidateLogProcess_eq_cutoffNormSum_mul ω ht]
  unfold harperCandidateLogOld smoothProcess cutoffNormSum
  rw [smoothSum_eq_S_of_forall_smooth ω (fun n hn =>
    isXSmooth_of_lt ((Finset.mem_Icc.mp hn).2.trans_lt hX))]

/-- Integrated mean absolute error of the time-domain smooth approximation
tends to zero under every fixed positive Laplace damping. -/
theorem candidate_tendsto_integral_smooth_laplace_error {T : ℝ} (hT : 0 < T) :
    Tendsto (fun X : ℕ => ∫ t in Ioi 0, ∫ ω,
      |Real.exp (-t / T) *
        (harperCandidateLogOld ω X t - harperCandidateLogProcess ω t)| ∂mu)
      atTop (𝓝 0) := by
  let ν := volume.restrict (Ioi (0 : ℝ))
  let F : ℕ → ℝ → ℝ := fun X t => ∫ ω,
    |Real.exp (-t / T) *
      (harperCandidateLogOld ω X t - harperCandidateLogProcess ω t)| ∂mu
  have hF (X : ℕ) : Integrable (F X) ν := by
    simpa only [F, Pi.sub_apply, ← mul_sub, Real.norm_eq_abs] using
      ((candidate_integrable_smooth_laplace_product X hT).sub
        (candidate_integrable_laplace_product hT)).norm.integral_prod_left
  have hbound : Integrable (fun t : ℝ => 2 * (Real.exp (-t / T) * (2 + t))) ν :=
    (candidate_integrable_laplace_majorant hT).const_mul 2
  have hmajor (X : ℕ) : ∀ᵐ t ∂ν, ‖F X t‖ ≤
      2 * (Real.exp (-t / T) * (2 + t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hi := (candidate_integrable_logOld X t).sub (candidate_integrable_logProcess t)
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
    simp_rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [integral_const_mul]
    have htri : (∫ ω, |harperCandidateLogOld ω X t - harperCandidateLogProcess ω t| ∂mu) ≤
        (∫ ω, |harperCandidateLogOld ω X t| ∂mu) +
          ∫ ω, |harperCandidateLogProcess ω t| ∂mu := by
      rw [← integral_add (candidate_integrable_logOld X t).abs
        (candidate_integrable_logProcess t).abs]
      exact integral_mono hi.abs
        ((candidate_integrable_logOld X t).abs.add (candidate_integrable_logProcess t).abs)
        (fun ω => abs_sub _ _)
    have hsum := add_le_add (candidate_integral_abs_logOld_le X ht.le)
      (candidate_integral_abs_logProcess_le ht.le)
    nlinarith [mul_le_mul_of_nonneg_left (htri.trans hsum) (Real.exp_pos (-t / T)).le]
  have hlim : ∀ᵐ t ∂ν, Tendsto (fun X => F X t) atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [candidate_eventually_logOld_eq_logProcess ht.le] with X hX
    simp only [F, hX, sub_self, mul_zero, abs_zero, integral_zero]
  have h := tendsto_integral_of_dominated_convergence
    (fun t : ℝ => 2 * (Real.exp (-t / T) * (2 + t)))
    (fun X => (hF X).aestronglyMeasurable) hbound hmajor hlim
  simpa only [integral_zero] using h

/-- The smooth Laplace transforms converge in mean absolute distance to the
actual complete Laplace transform. -/
theorem candidate_tendsto_smooth_laplaceTransform_L1 {T : ℝ} (hT : 0 < T) :
    Tendsto (fun X : ℕ => ∫ ω,
      |(∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogOld ω X t) -
        ∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogProcess ω t| ∂mu)
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _) _
    (candidate_tendsto_integral_smooth_laplace_error hT)
  apply Eventually.of_forall
  intro X
  have hprod := (candidate_integrable_smooth_laplace_product X hT).sub
    (candidate_integrable_laplace_product hT)
  have hleft := ((candidate_integrable_smooth_laplace_product X hT).integral_prod_right.sub
    (candidate_integrable_laplaceTransform hT)).abs
  have hright := hprod.norm.integral_prod_right
  have hpoint : ∀ᵐ ω ∂mu,
      |(∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogOld ω X t) -
        ∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogProcess ω t| ≤
      ∫ t in Ioi 0, |Real.exp (-t / T) *
        (harperCandidateLogOld ω X t - harperCandidateLogProcess ω t)| := by
    filter_upwards [(candidate_integrable_smooth_laplace_product X hT).prod_left_ae,
      candidate_ae_integrable_laplace hT] with ω hX hfull
    rw [← integral_sub hX hfull]
    simpa only [Pi.sub_apply, Real.norm_eq_abs, ← mul_sub] using
      norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
        (fun t => Real.exp (-t / T) * harperCandidateLogOld ω X t -
          Real.exp (-t / T) * harperCandidateLogProcess ω t)
  have hright' : Integrable (fun ω => ∫ t in Ioi 0, |Real.exp (-t / T) *
      (harperCandidateLogOld ω X t - harperCandidateLogProcess ω t)|) mu := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs, ← mul_sub] using hright
  have hswap := integral_integral_swap (f := fun t ω =>
    ‖Real.exp (-t / T) * harperCandidateLogOld ω X t -
      Real.exp (-t / T) * harperCandidateLogProcess ω t‖) hprod.norm
  calc
    _ ≤ ∫ ω, (∫ t in Ioi 0, |Real.exp (-t / T) *
        (harperCandidateLogOld ω X t - harperCandidateLogProcess ω t)|) ∂mu :=
      integral_mono_ae hleft hright' hpoint
    _ = _ := by
      simpa only [Pi.sub_apply, Real.norm_eq_abs, ← mul_sub] using hswap.symm

/-- Nonnegative finite smooth transforms force the full transform to be
nonnegative almost surely. The approximation is proved above, not assumed. -/
theorem candidate_ae_laplace_nonneg_of_smooth {T : ℝ} (hT : 0 < T)
    (hpos : ∀ X : ℕ, ∀ᵐ ω ∂mu,
      0 ≤ ∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogOld ω X t) :
    ∀ᵐ ω ∂mu, 0 ≤ ∫ t in Ioi 0,
      Real.exp (-t / T) * harperCandidateLogProcess ω t := by
  let G : Omega → ℝ := fun ω => ∫ t in Ioi 0,
    Real.exp (-t / T) * harperCandidateLogProcess ω t
  let F : ℕ → Omega → ℝ := fun X ω => ∫ t in Ioi 0,
    Real.exp (-t / T) * harperCandidateLogOld ω X t
  have hG : Integrable G mu := candidate_integrable_laplaceTransform hT
  have hF (X : ℕ) : Integrable (F X) mu :=
    (candidate_integrable_smooth_laplace_product X hT).integral_prod_right
  have hneg : Integrable (fun ω => max (-G ω) 0) mu := hG.neg.sup (integrable_const (0 : ℝ))
  have hle (X : ℕ) : (∫ ω, max (-G ω) 0 ∂mu) ≤ ∫ ω, |F X ω - G ω| ∂mu := by
    apply integral_mono_ae hneg ((hF X).sub hG).abs
    filter_upwards [hpos X] with ω hω
    change max (-G ω) 0 ≤ |F X ω - G ω|
    apply max_le
    · have hf : 0 ≤ F X ω := hω
      linarith [le_abs_self (F X ω - G ω)]
    · exact abs_nonneg _
  have hzero : (∫ ω, max (-G ω) 0 ∂mu) = 0 := by
    apply le_antisymm _ (integral_nonneg fun _ => le_max_right _ _)
    exact ge_of_tendsto (candidate_tendsto_smooth_laplaceTransform_L1 hT)
      (Eventually.of_forall hle)
  have hae := (integral_eq_zero_iff_of_nonneg
    (fun ω => le_max_right (-G ω) 0) hneg).mp hzero
  filter_upwards [hae] with ω hω
  change max (-G ω) 0 = 0 at hω
  have hg := le_max_left (-G ω) 0
  change 0 ≤ G ω
  rw [hω] at hg
  linarith

/-- Nonnegativity of the full random Laplace transform is now unconditional:
finite positive Euler products and the proved mean approximation suffice. -/
theorem candidate_ae_laplace_nonneg {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂mu, 0 ≤ ∫ t in Ioi 0,
      Real.exp (-t / T) * harperCandidateLogProcess ω t :=
  candidate_ae_laplace_nonneg_of_smooth hT (fun X =>
    ae_of_all _ fun ω => candidate_integral_laplace_logOld_nonneg ω X hT)

/-- Every fixed cylinder inherits the proved full-transform positivity. -/
theorem candidateCylinderLaw_ae_laplace_nonneg
    (s : Finset ℕ) (η : s → Bool) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, 0 ≤ ∫ t in Ioi 0,
      Real.exp (-t / T) * harperCandidateLogProcess ω t :=
  ProbabilityTheory.cond_absolutelyContinuous.ae_le (candidate_ae_laplace_nonneg hT)

end Erdos.Problem1144
