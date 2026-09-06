import Erdos.Problem1144.HarperCandidateSpectralFinite

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace Erdos.Problem1144

private theorem candidate_integrable_damped_product_of_uniform_moment
    (a : Omega → ℝ → ℝ)
    (ha : Measurable fun z : Omega × ℝ => a z.1 z.2)
    (hi : ∀ t, Integrable (fun ω => a ω t) mu)
    (hb : ∀ t, (∫ ω, |a ω t| ∂mu) ≤ 2)
    (hz : ∀ ω t, t < 0 → a ω t = 0)
    {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun z : ℝ × Omega => Real.exp (-σ * z.1) * a z.2 z.1)
      (volume.prod mu) := by
  let B : ℝ → ℝ := (Ici 0).indicator (fun t => Real.exp (-σ * t) * 2)
  have hB : Integrable B := by
    apply (integrable_indicator_iff measurableSet_Ici).mpr
    exact (integrableOn_Ici_iff_integrableOn_Ioi (μ := volume)).mpr
      ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hσ) 0).mul_const 2)
  have hF : Measurable fun z : ℝ × Omega => Real.exp (-σ * z.1) * a z.2 z.1 :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
      (ha.comp measurable_swap)
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun t => (hi t).const_mul (Real.exp (-σ * t))
  · apply hB.mono' hF.norm.aestronglyMeasurable.integral_prod_right'
    filter_upwards [] with t
    by_cases ht : 0 ≤ t
    · simp only [B, Set.indicator, mem_Ici, if_pos ht]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp_rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le
    · simp only [hz _ _ (lt_of_not_ge ht), mul_zero, norm_zero, integral_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) t

/-- Joint absolute integrability of every arithmetic approximation on the
whole real time line. -/
theorem candidate_integrable_squarefreeLogApprox_damped_product
    (N : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun z : ℝ × Omega => Real.exp (-σ * z.1) *
      candidateSquarefreeLogApprox z.2 N z.1) (volume.prod mu) := by
  apply candidate_integrable_damped_product_of_uniform_moment
    (fun ω t => candidateSquarefreeLogApprox ω N t)
    (measurable_candidateSquarefreeLogApprox N)
    (candidate_integrable_squarefreeLogApprox N)
    (candidate_integral_abs_squarefreeLogApprox_le_two N) _ hσ
  intro ω t ht
  have hf : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr ht)
  simp [candidateSquarefreeLogApprox, hf, GSquarefree]

/-- The same joint whole-line integrability holds for the literal process. -/
theorem candidate_integrable_squarefree_damped_product_univ
    {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun z : ℝ × Omega => Real.exp (-σ * z.1) *
      harperCandidateSquarefreeLogProcess z.2 z.1) (volume.prod mu) := by
  apply candidate_integrable_damped_product_of_uniform_moment
    harperCandidateSquarefreeLogProcess measurable_harperCandidateSquarefreeLogProcess
    (fun t => by simpa only [pow_one] using candidate_integrable_squarefreeLog_pow t 1)
    candidate_integral_abs_squarefreeLog_le_two _ hσ
  intro ω t ht
  simp [harperCandidateSquarefreeLogProcess, not_le.mpr ht]

/-- Arithmetic cutoffs converge in integrated mean absolute distance in the
time domain, under every positive damping. -/
theorem candidate_tendsto_squarefreeLogApprox_damped_product_L1
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun N : ℕ => ∫ t, ∫ ω,
      |Real.exp (-σ * t) * (candidateSquarefreeLogApprox ω N t -
        harperCandidateSquarefreeLogProcess ω t)| ∂mu) atTop (𝓝 0) := by
  let B : ℝ → ℝ := (Ici 0).indicator (fun t => 4 * Real.exp (-σ * t))
  have hB : Integrable B := by
    apply (integrable_indicator_iff measurableSet_Ici).mpr
    exact (integrableOn_Ici_iff_integrableOn_Ioi (μ := volume)).mpr
      ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hσ) 0).const_mul 4)
  let F : ℕ → ℝ → ℝ := fun N t => ∫ ω,
    |Real.exp (-σ * t) * (candidateSquarefreeLogApprox ω N t -
      harperCandidateSquarefreeLogProcess ω t)| ∂mu
  have hi (N : ℕ) : Integrable (F N) := by
    simpa only [F, Pi.sub_apply, ← mul_sub, Real.norm_eq_abs] using
      ((candidate_integrable_squarefreeLogApprox_damped_product N hσ).sub
        (candidate_integrable_squarefree_damped_product_univ hσ)).norm.integral_prod_left
  have hbound (N : ℕ) : ∀ᵐ t, ‖F N t‖ ≤ B t := by
    filter_upwards [] with t
    by_cases ht : 0 ≤ t
    · have ha := candidate_integrable_squarefreeLogApprox N t
      have hb : Integrable (fun ω => harperCandidateSquarefreeLogProcess ω t) mu := by
        simpa only [pow_one] using candidate_integrable_squarefreeLog_pow t 1
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
      simp_rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      rw [integral_const_mul]
      have htri := integral_mono (ha.sub hb).abs (ha.abs.add hb.abs)
        (fun ω => abs_sub (candidateSquarefreeLogApprox ω N t)
          (harperCandidateSquarefreeLogProcess ω t))
      simp only [Pi.add_apply, Pi.sub_apply] at htri
      rw [integral_add ha.abs hb.abs] at htri
      have hsum := add_le_add (candidate_integral_abs_squarefreeLogApprox_le_two N t)
        (candidate_integral_abs_squarefreeLog_le_two t)
      simp only [B, Set.indicator, mem_Ici, if_pos ht]
      nlinarith [mul_le_mul_of_nonneg_left (htri.trans hsum) (Real.exp_pos (-σ * t)).le]
    · have hf : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr
        (Real.exp_lt_one_iff.mpr (lt_of_not_ge ht))
      simp [F, candidateSquarefreeLogApprox, harperCandidateSquarefreeLogProcess,
        hf, GSquarefree, ht, B]
  have hlim : ∀ᵐ t, Tendsto (fun N => F N t) atTop (𝓝 0) := by
    apply ae_of_all
    intro t
    apply tendsto_const_nhds.congr'
    filter_upwards [candidate_eventually_squarefreeLogApprox_eq t] with N hN
    simp only [F, hN, sub_self, mul_zero, abs_zero, integral_zero]
  simpa only [F, integral_zero] using
    tendsto_integral_of_dominated_convergence B
      (fun N => (hi N).aestronglyMeasurable) hB hbound hlim

/-- Multiplying a jointly integrable real signal by Fourier phases preserves
joint integrability. -/
theorem candidate_integrable_random_fourier_kernel
    {F : ℝ × Omega → ℝ} (hF : Measurable F) (hi : Integrable F (volume.prod mu)) (ξ : ℝ) :
    Integrable (fun z : ℝ × Omega => Real.fourierChar (-(z.1 * ξ)) • (F z : ℂ))
      (volume.prod mu) := by
  have hK : Measurable fun z : ℝ × Omega =>
      Real.fourierChar (-(z.1 * ξ)) • (F z : ℂ) := by
    simp only [Circle.smul_def, smul_eq_mul]
    exact (Real.continuous_fourierChar.subtype_val.measurable.comp
      (measurable_fst.mul_const ξ).neg).mul (Complex.measurable_ofReal.comp hF)
  apply (integrable_norm_iff hK.aestronglyMeasurable).mp
  simpa only [Circle.norm_smul, Complex.norm_real] using hi.norm

/-- Fourier transformation contracts integrated mean absolute error from
the time-domain product into the random-variable space. -/
theorem candidate_integral_fourier_error_le
    {F G : ℝ × Omega → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hiF : Integrable F (volume.prod mu)) (hiG : Integrable G (volume.prod mu)) (ξ : ℝ) :
    (∫ ω, ‖Fourier.fourierIntegral Real.fourierChar volume (fun t => (F (t, ω) : ℂ)) ξ -
      Fourier.fourierIntegral Real.fourierChar volume (fun t => (G (t, ω) : ℂ)) ξ‖ ∂mu) ≤
      ∫ t, ∫ ω, |F (t, ω) - G (t, ω)| ∂mu := by
  let KF : ℝ × Omega → ℂ := fun z => Real.fourierChar (-(z.1 * ξ)) • (F z : ℂ)
  let KG : ℝ × Omega → ℂ := fun z => Real.fourierChar (-(z.1 * ξ)) • (G z : ℂ)
  have hKF : Integrable KF (volume.prod mu) := candidate_integrable_random_fourier_kernel hF hiF ξ
  have hKG : Integrable KG (volume.prod mu) := candidate_integrable_random_fourier_kernel hG hiG ξ
  have hpoint : ∀ᵐ ω ∂mu,
      ‖(∫ t, KF (t, ω)) - ∫ t, KG (t, ω)‖ ≤ ∫ t, ‖KF (t, ω) - KG (t, ω)‖ := by
    filter_upwards [hKF.prod_left_ae, hKG.prod_left_ae] with ω hωF hωG
    rw [← integral_sub hωF hωG]
    exact norm_integral_le_integral_norm _
  have h := integral_mono_ae
    (hKF.integral_prod_right.sub hKG.integral_prod_right).norm
    (hKF.sub hKG).norm.integral_prod_right hpoint
  have hswap := integral_integral_swap (f := fun t ω => ‖KF (t, ω) - KG (t, ω)‖)
    (hKF.sub hKG).norm
  simp only [Pi.sub_apply] at h
  rw [← hswap] at h
  simpa only [Fourier.fourierIntegral_def, KF, KG, ← smul_sub, ← Complex.ofReal_sub,
    Circle.norm_smul, Complex.norm_real, Real.norm_eq_abs] using h

/-- Measurability of the damped finite arithmetic approximation. -/
theorem measurable_candidateSquarefreeLogApprox_damped (N : ℕ) (σ : ℝ) :
    Measurable fun z : ℝ × Omega => Real.exp (-σ * z.1) *
      candidateSquarefreeLogApprox z.2 N z.1 := by
  have hp : Measurable (fun z : ℝ × Omega => candidateSquarefreeLogApprox z.2 N z.1) :=
    (measurable_candidateSquarefreeLogApprox N).comp (f := Prod.swap) measurable_swap
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul hp

/-- Measurability of the damped literal squarefree signal. -/
theorem measurable_candidateSquarefree_damped (σ : ℝ) :
    Measurable fun z : ℝ × Omega => Real.exp (-σ * z.1) *
      harperCandidateSquarefreeLogProcess z.2 z.1 :=
  (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
    (measurable_harperCandidateSquarefreeLogProcess.comp measurable_swap)

/-- The finite arithmetic Fourier transforms converge in mean absolute
distance to the literal transform. -/
theorem candidate_tendsto_squarefreeLogApprox_fourier_L1
    {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    Tendsto (fun N : ℕ => ∫ ω,
      ‖Fourier.fourierIntegral Real.fourierChar volume
          (fun t => ((Real.exp (-σ * t) * candidateSquarefreeLogApprox ω N t : ℝ) : ℂ))
          (τ / (2 * Real.pi)) -
        Fourier.fourierIntegral Real.fourierChar volume
          (fun t => ((Real.exp (-σ * t) * harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ))
          (τ / (2 * Real.pi))‖ ∂mu) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => norm_nonneg _) _
    (candidate_tendsto_squarefreeLogApprox_damped_product_L1 hσ)
  apply Eventually.of_forall
  intro N
  simpa only [← mul_sub] using candidate_integral_fourier_error_le
    (measurable_candidateSquarefreeLogApprox_damped N σ)
    (measurable_candidateSquarefree_damped σ)
    (candidate_integrable_squarefreeLogApprox_damped_product N hσ)
    (candidate_integrable_squarefree_damped_product_univ hσ) (τ / (2 * Real.pi))

/-- A uniform second-moment bound passes through mean-L1 convergence. Fatou
also proves second-moment integrability of the limit. -/
theorem candidate_integrable_sq_and_integral_le_of_L1_limit
    {F : ℕ → Omega → ℂ} {G : Omega → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ N, Integrable (F N) mu) (hG : Integrable G mu)
    (hF2 : ∀ N, Integrable (fun ω => ‖F N ω‖ ^ 2) mu)
    (hb : ∀ N, (∫ ω, ‖F N ω‖ ^ 2 ∂mu) ≤ B)
    (hlim : Tendsto (fun N => ∫ ω, ‖F N ω - G ω‖ ∂mu) atTop (𝓝 0)) :
    Integrable (fun ω => ‖G ω‖ ^ 2) mu ∧ (∫ ω, ‖G ω‖ ^ 2 ∂mu) ≤ B := by
  have hLp : Tendsto (fun N => eLpNorm (F N - G) 1 mu) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.tendsto 0 |>.comp hlim
    simp only [ENNReal.ofReal_zero] at h
    convert h using 1
    funext N
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hF N).sub hG)]
    rfl
  have hm := tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (fun N => (hF N).aestronglyMeasurable) hG.aestronglyMeasurable hLp
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have hfatou : (∫⁻ ω, ENNReal.ofReal (‖G ω‖ ^ 2) ∂mu) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (‖F (ns n) ω‖ ^ 2)) atTop ∂mu := by
        apply lintegral_congr_ae
        filter_upwards [hae] with ω hω
        exact ((ENNReal.continuous_ofReal.tendsto _).comp (hω.norm.pow 2)).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (‖F (ns n) ω‖ ^ 2) ∂mu) atTop :=
        lintegral_liminf_le' (fun n =>
          ((hF (ns n)).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal B := by
        apply liminf_le_of_frequently_le'
        apply Frequently.of_forall
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hF2 (ns n))
          (ae_of_all _ fun ω => sq_nonneg ‖F (ns n) ω‖)]
        exact ENNReal.ofReal_le_ofReal (hb (ns n))
  have hg2 : AEStronglyMeasurable (fun ω => ‖G ω‖ ^ 2) mu :=
    hG.aestronglyMeasurable.norm.pow 2
  have hint : Integrable (fun ω => ‖G ω‖ ^ 2) mu := by
    refine ⟨hg2, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    simpa only [Real.enorm_eq_ofReal_abs, abs_pow, abs_norm] using
      lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun ω => sq_nonneg ‖G ω‖)]
  exact hfatou

/-- The high-frequency denominator bound for the literal squarefree Fourier
transform. Both existence of its second moment and the bound are unconditional. -/
theorem candidate_squarefree_fourier_second_moment
    {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    Integrable (fun ω => ‖Fourier.fourierIntegral Real.fourierChar volume
      (fun t => ((Real.exp (-σ * t) * harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ))
      (τ / (2 * Real.pi))‖ ^ 2) mu ∧
    (∫ ω, ‖Fourier.fourierIntegral Real.fourierChar volume
      (fun t => ((Real.exp (-σ * t) * harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ))
      (τ / (2 * Real.pi))‖ ^ 2 ∂mu) ≤
      (∑' n : ℕ, (n : ℝ) ^ (-(1 + 2 * σ))) / ((σ + 1 / 2) ^ 2 + τ ^ 2) := by
  apply candidate_integrable_sq_and_integral_le_of_L1_limit
      (F := fun N ω => Fourier.fourierIntegral Real.fourierChar volume
        (fun t => ((Real.exp (-σ * t) * candidateSquarefreeLogApprox ω N t : ℝ) : ℂ))
        (τ / (2 * Real.pi)))
  · exact div_nonneg (tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (by positivity)
  · intro N
    exact (candidate_integrable_random_fourier_kernel
      (measurable_candidateSquarefreeLogApprox_damped N σ)
      (candidate_integrable_squarefreeLogApprox_damped_product N hσ)
      (τ / (2 * Real.pi))).integral_prod_right
  · exact (candidate_integrable_random_fourier_kernel
      (measurable_candidateSquarefree_damped σ)
      (candidate_integrable_squarefree_damped_product_univ hσ)
      (τ / (2 * Real.pi))).integral_prod_right
  · exact fun N => candidate_integrable_squarefreeLogApprox_fourier_norm_sq N hσ τ
  · exact fun N => candidate_integral_squarefreeLogApprox_fourier_norm_sq_le N hσ τ
  · exact candidate_tendsto_squarefreeLogApprox_fourier_L1 hσ τ

end Erdos.Problem1144
