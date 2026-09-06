import Erdos.Problem1144.HarperCandidateSpectralLimit
import Erdos.Problem1144.HarperCandidateSpectralWindow
import Erdos.Problem1144.HarperCandidateGaussianMaxima
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

namespace Erdos.Problem1144

/-- The elementary Dirichlet mass bound, obtained from the existing
sum/integral identity for the zeta function. -/
theorem candidate_squarefree_dirichletMass_le {σ : ℝ} (hσ : 0 < σ) :
    (∑' n : ℕ, (n : ℝ) ^ (-(1 + 2 * σ))) ≤ 1 + 1 / (2 * σ) := by
  have hp : 1 < 1 + 2 * σ := by linarith
  have hz := ZetaAsymptotics.zeta_limit_aux1 hp
  have hnonneg : 0 ≤ (1 + 2 * σ) * ZetaAsymptotics.term_tsum (1 + 2 * σ) :=
    mul_nonneg (by linarith) (tsum_nonneg fun n => ZetaAsymptotics.term_nonneg _ _)
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + 2 * σ))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  rw [hsum.tsum_eq_zero_add]
  rw [Nat.cast_zero, Real.zero_rpow (by linarith : -(1 + 2 * σ) ≠ 0), zero_add]
  have heq : (∑' n : ℕ, ((n + 1 : ℕ) : ℝ) ^ (-(1 + 2 * σ))) =
      ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ (1 + 2 * σ) := by
    apply tsum_congr
    intro n
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    simp only [Nat.cast_add, Nat.cast_one, one_div]
  rw [heq]
  have hd : 1 + 2 * σ - 1 = 2 * σ := by ring
  rw [hd] at hz
  linarith

/-- The literal squarefree angular Fourier transform. -/
noncomputable def candidateSquarefreeAngularFourier (ω : Omega) (σ τ : ℝ) : ℂ :=
  Fourier.fourierIntegral Real.fourierChar volume
    (fun t => ((Real.exp (-σ * t) * harperCandidateSquarefreeLogProcess ω t : ℝ) : ℂ))
    (τ / (2 * Real.pi))

/-- Joint measurability is proved for the literal Fourier integral, including
all frequencies, rather than postulated for a spectral version. -/
theorem measurable_candidateSquarefreeAngularFourier (σ : ℝ) :
    Measurable fun z : Omega × ℝ => candidateSquarefreeAngularFourier z.1 σ z.2 := by
  let K : ℝ × (Omega × ℝ) → ℂ := fun z =>
    Real.fourierChar (-(z.1 * (z.2.2 / (2 * Real.pi)))) •
      ((Real.exp (-σ * z.1) * harperCandidateSquarefreeLogProcess z.2.1 z.1 : ℝ) : ℂ)
  have hproc : Measurable fun z : ℝ × (Omega × ℝ) =>
      harperCandidateSquarefreeLogProcess z.2.1 z.1 :=
    measurable_harperCandidateSquarefreeLogProcess.comp
      (measurable_snd.fst.prodMk measurable_fst)
  have hK : Measurable K := by
    simp only [K, Circle.smul_def, smul_eq_mul]
    exact (Real.continuous_fourierChar.subtype_val.measurable.comp
      (measurable_fst.mul (measurable_snd.snd.div_const (2 * Real.pi))).neg).mul
        (Complex.measurable_ofReal.comp
          ((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul hproc))
  exact hK.stronglyMeasurable.integral_prod_left.measurable

/-- Explicit pointwise high-frequency second moment of the literal Fourier
transform, valid at every positive damping rate. -/
theorem candidate_integral_squarefreeAngularFourier_norm_sq_le
    {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    (∫ ω, ‖candidateSquarefreeAngularFourier ω σ τ‖ ^ 2 ∂mu) ≤
      (1 + 1 / (2 * σ)) / ((σ + 1 / 2) ^ 2 + τ ^ 2) :=
  (candidate_squarefree_fourier_second_moment hσ τ).2.trans
    (div_le_div_of_nonneg_right (candidate_squarefree_dirichletMass_le hσ) (by positivity))

private theorem candidate_inv_sq_positive_tail {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun τ : ℝ => 1 / τ ^ 2) (Ioi H) ∧
      (∫ τ in Ioi H, 1 / τ ^ 2) = 1 / H := by
  have heq (τ : ℝ) : τ ^ (-2 : ℝ) = 1 / τ ^ (2 : ℕ) := by
    rw [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat]
    simp only [one_div]
  constructor
  · simpa only [heq] using integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH
  · have h := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hH
    simpa only [heq, show (-2 : ℝ) + 1 = -1 by norm_num,
      Real.rpow_neg_one, div_neg, div_one, neg_neg, one_div] using h

/-- Both frequency tails have inverse-square mass exactly `2/H`. -/
theorem candidate_inv_sq_absolute_tail {H : ℝ} (hH : 0 < H) :
    IntegrableOn (fun τ : ℝ => 1 / τ ^ 2) {τ | H < |τ|} ∧
      (∫ τ in {τ : ℝ | H < |τ|}, 1 / τ ^ 2) = 2 / H := by
  have hpos := candidate_inv_sq_positive_tail hH
  have hneg : IntegrableOn (fun τ : ℝ => 1 / τ ^ 2) (Iio (-H)) := by
    have hp : IntegrableOn (fun τ : ℝ => 1 / τ ^ 2) (Ioi (-(-H))) := by
      simpa only [neg_neg] using hpos.1
    simpa only [neg_sq] using hp.comp_neg_Iio
  have hnegeq : (∫ τ in Iio (-H), 1 / τ ^ 2) = 1 / H := by
    have h := integral_comp_neg_Iic (-H) (fun τ : ℝ => 1 / τ ^ 2)
    simpa only [neg_neg, neg_sq, hpos.2, integral_Iic_eq_integral_Iio] using h
  have hset : {τ : ℝ | H < |τ|} = Iio (-H) ∪ Ioi H := by
    ext τ
    simp only [mem_setOf_eq, mem_union, mem_Iio, mem_Ioi, lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  rw [hset]
  refine ⟨hneg.union hpos.1, ?_⟩
  rw [setIntegral_union (by
      apply Set.disjoint_left.mpr
      intro τ ht hn
      change τ < -H at ht
      change H < τ at hn
      linarith [ht, hn]) measurableSet_Ioi hneg hpos.1, hnegeq, hpos.2]
  ring

/-- The full squarefree Fourier energy is jointly integrable on every
positive high-frequency tail. -/
theorem candidate_integrable_squarefree_fourier_tail_product
    {σ H : ℝ} (hσ : 0 < σ) (hH : 0 < H) :
    Integrable (fun z : ℝ × Omega => ‖candidateSquarefreeAngularFourier z.2 σ z.1‖ ^ 2)
      ((volume.restrict {τ : ℝ | H < |τ|}).prod mu) := by
  have hf : Measurable fun z : ℝ × Omega => ‖candidateSquarefreeAngularFourier z.2 σ z.1‖ ^ 2 :=
    ((measurable_candidateSquarefreeAngularFourier σ).comp measurable_swap).norm.pow_const 2
  apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ fun τ => (candidate_squarefree_fourier_second_moment hσ τ).1
  · apply ((candidate_inv_sq_absolute_tail hH).1.const_mul (1 + 1 / (2 * σ))).mono'
      hf.norm.aestronglyMeasurable.integral_prod_right'
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const measurable_id.abs)] with τ hτ
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [Real.norm_eq_abs, abs_pow, abs_norm]
    calc
      _ ≤ (1 + 1 / (2 * σ)) / ((σ + 1 / 2) ^ 2 + τ ^ 2) :=
        candidate_integral_squarefreeAngularFourier_norm_sq_le hσ τ
      _ ≤ (1 + 1 / (2 * σ)) * (1 / τ ^ 2) := by
        rw [mul_one_div]
        apply div_le_div_of_nonneg_left (by positivity) _ (by nlinarith [sq_nonneg (σ + 1 / 2)])
        exact sq_pos_of_ne_zero (by intro h; simp only [h, abs_zero] at hτ; linarith)

/-- The actual unnormalized high-frequency Fourier energy has expected size
at most `2(1+1/(2σ))/H`. -/
theorem candidate_integral_squarefree_fourier_tail_le
    {σ H : ℝ} (hσ : 0 < σ) (hH : 0 < H) :
    (∫ ω, (∫ τ in {τ : ℝ | H < |τ|},
      ‖candidateSquarefreeAngularFourier ω σ τ‖ ^ 2) ∂mu) ≤
        2 * (1 + 1 / (2 * σ)) / H := by
  have hi := candidate_integrable_squarefree_fourier_tail_product hσ hH
  rw [← integral_integral_swap (f := fun τ ω =>
    ‖candidateSquarefreeAngularFourier ω σ τ‖ ^ 2) hi]
  have hbound : ∀ᵐ τ ∂volume.restrict {τ : ℝ | H < |τ|},
      (∫ ω, ‖candidateSquarefreeAngularFourier ω σ τ‖ ^ 2 ∂mu) ≤
        (1 + 1 / (2 * σ)) * (1 / τ ^ 2) := by
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const measurable_id.abs)] with τ hτ
    apply (candidate_integral_squarefreeAngularFourier_norm_sq_le hσ τ).trans
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left (by positivity) _ (by nlinarith [sq_nonneg (σ + 1 / 2)])
    exact sq_pos_of_ne_zero (by intro h; simp only [h, abs_zero] at hτ; linarith)
  have h := integral_mono_ae hi.integral_prod_left
    ((candidate_inv_sq_absolute_tail hH).1.const_mul (1 + 1 / (2 * σ))) hbound
  rw [integral_const_mul, (candidate_inv_sq_absolute_tail hH).2] at h
  convert h using 1
  ring

/-- The stationary squarefree spectral tail variance with scale `V=1/σ`.
It is defined from the literal Fourier transform. -/
noncomputable def candidateSquarefreeSpectralTailVariance (ω : Omega) (σ H : ℝ) : ℝ :=
  σ / (2 * Real.pi) * ∫ τ in {τ : ℝ | H < |τ|},
    ‖candidateSquarefreeAngularFourier ω σ τ‖ ^ 2

/-- Exact agreement with the spectral-density normalization used in the
complete-versus-squarefree comparison. -/
theorem candidateSquarefreeSpectralTailVariance_eq_density_integral
    (ω : Omega) {σ : ℝ} (hσ : 0 < σ) (H : ℝ) :
    candidateSquarefreeSpectralTailVariance ω σ H =
      ∫ τ in {τ : ℝ | H < |τ|},
        candidateLogSpectralDensity (harperCandidateSquarefreeLogProcess ω) σ (1 / σ) τ := by
  simp only [candidateSquarefreeSpectralTailVariance, candidateSquarefreeAngularFourier,
    candidateLogSpectralDensity, integral_div]
  field_simp

theorem candidateSquarefreeSpectralTailVariance_nonneg
    (ω : Omega) {σ : ℝ} (hσ : 0 ≤ σ) (H : ℝ) :
    0 ≤ candidateSquarefreeSpectralTailVariance ω σ H := by
  unfold candidateSquarefreeSpectralTailVariance
  exact mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)

theorem measurable_candidateSquarefreeSpectralTailVariance (σ H : ℝ) :
    Measurable (fun ω => candidateSquarefreeSpectralTailVariance ω σ H) := by
  have hf := (measurable_candidateSquarefreeAngularFourier σ).norm.pow_const 2
  have hi := StronglyMeasurable.integral_prod_right
    (f := fun ω τ => ‖candidateSquarefreeAngularFourier ω σ τ‖ ^ 2) hf.stronglyMeasurable
    (ν := volume.restrict {τ : ℝ | H < |τ|})
  exact measurable_const.mul hi.measurable

theorem candidate_integrable_squarefreeSpectralTailVariance
    {σ H : ℝ} (hσ : 0 < σ) (hH : 0 < H) :
    Integrable (fun ω => candidateSquarefreeSpectralTailVariance ω σ H) mu :=
  (candidate_integrable_squarefree_fourier_tail_product hσ hH).integral_prod_right.const_mul _

/-- Multiplication by the stationary normalization cancels the `1/σ` loss.
The expected actual spectral tail variance is at most `(σ+1/2)/(π H)`. -/
theorem candidate_integral_squarefreeSpectralTailVariance_le
    {σ H : ℝ} (hσ : 0 < σ) (hH : 0 < H) :
    (∫ ω, candidateSquarefreeSpectralTailVariance ω σ H ∂mu) ≤
      (σ + 1 / 2) / (Real.pi * H) := by
  simp only [candidateSquarefreeSpectralTailVariance]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (candidate_integral_squarefree_fourier_tail_le hσ hH)
    (show 0 ≤ σ / (2 * Real.pi) by positivity)
  convert h using 1
  field_simp

/-- Conditioning on a fixed finite assignment changes a nonnegative moment
bound by at most the reciprocal probability of that assignment. -/
theorem candidateCylinderLaw_integral_nonneg_le
    (s : Finset ℕ) (η : s → Bool) {f : Omega → ℝ}
    (hi : Integrable f mu) (hn : ∀ ω, 0 ≤ f ω) :
    Integrable f (candidateCylinderLaw s η) ∧
      (∫ ω, f ω ∂candidateCylinderLaw s η) ≤
        (∫ ω, f ω ∂mu) / mu.real (candidateCylinder s η) := by
  constructor
  · exact hi.restrict.smul_measure (ENNReal.inv_ne_top.mpr (mu_candidateCylinder_ne_zero s η))
  · rw [candidateCylinderLaw, ProbabilityTheory.cond, integral_smul_measure,
      ENNReal.toReal_inv]
    change (mu.real (candidateCylinder s η))⁻¹ * (∫ ω in candidateCylinder s η, f ω ∂mu) ≤ _
    have h := setIntegral_le_integral hi (ae_of_all _ hn) (s := candidateCylinder s η)
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left h
        (inv_nonneg.mpr (show 0 ≤ mu.real (candidateCylinder s η) from measureReal_nonneg))

/-- The same concrete high-frequency variance bound is available under every
fixed cylinder, with its exact conditioning factor. -/
theorem candidateCylinderLaw_integral_squarefreeSpectralTailVariance_le
    (s : Finset ℕ) (η : s → Bool) {σ H : ℝ} (hσ : 0 < σ) (hH : 0 < H) :
    Integrable (fun ω => candidateSquarefreeSpectralTailVariance ω σ H)
      (candidateCylinderLaw s η) ∧
    (∫ ω, candidateSquarefreeSpectralTailVariance ω σ H ∂candidateCylinderLaw s η) ≤
      (σ + 1 / 2) / (Real.pi * H * mu.real (candidateCylinder s η)) := by
  have h := candidateCylinderLaw_integral_nonneg_le s η
    (candidate_integrable_squarefreeSpectralTailVariance hσ hH)
    (fun ω => candidateSquarefreeSpectralTailVariance_nonneg ω hσ.le H)
  refine ⟨h.1, h.2.trans ?_⟩
  rw [div_mul_eq_div_div]
  exact div_le_div_of_nonneg_right (candidate_integral_squarefreeSpectralTailVariance_le hσ hH)
    measureReal_nonneg

/-- The proved high-frequency variance bound feeds the conditional Gaussian
maximum estimate directly. Gaussian coordinates may be arbitrarily correlated. -/
theorem candidate_gaussian_maximum_tail_le_squarefreeSpectralTail
    {Ξ ι : Type*} [MeasurableSpace Ξ] [Fintype ι] [Nonempty ι]
    {P : Measure Ξ} [IsProbabilityMeasure P]
    (s : Finset ℕ) (η : s → Bool) {d H r : ℝ} (hd : 0 < d) (hH : 0 < H)
    {X : ι → Omega × Ξ → ℝ} {v : Omega → ι → ℝ≥0}
    (hXmeas : ∀ i, Measurable (X i))
    (hX : ∀ ω i, P.map (fun ξ => X i (ω, ξ)) = ProbabilityTheory.gaussianReal 0 (v ω i))
    (hv : ∀ ω i, (v ω i : ℝ) ≤ candidateSquarefreeSpectralTailVariance ω d H)
    (hr : 0 < r) :
    ((candidateCylinderLaw s η).prod P).real {z | ∃ i, r ≤ |X i z|} ≤
      4 * Real.log (2 * Fintype.card ι) *
        ((d + 1 / 2) / (Real.pi * H * mu.real (candidateCylinder s η))) / r ^ 2 +
        1 / (2 * Fintype.card ι) := by
  let V : Omega → ℝ≥0 := fun ω => ⟨candidateSquarefreeSpectralTailVariance ω d H,
    candidateSquarefreeSpectralTailVariance_nonneg ω hd.le H⟩
  have hVi := candidateCylinderLaw_integral_squarefreeSpectralTailVariance_le s η hd hH
  have h := candidate_gaussian_maximum_tail_le_log_variance
    (V := V) hXmeas ((measurable_candidateSquarefreeSpectralTailVariance d H).subtype_mk)
    hX (fun ω i => hv ω i) hVi.1 hr
  apply h.trans
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left hVi.2
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))

/-- On the candidate's eventual damping range `0<σ≤1`, the expected
stationary tail variance is bounded by a fixed multiple of `1/H`. -/
theorem candidateCylinderLaw_integral_squarefreeSpectralTailVariance_le_small_damping
    (s : Finset ℕ) (η : s → Bool) {σ H : ℝ}
    (hσ : 0 < σ) (hσone : σ ≤ 1) (hH : 0 < H) :
    (∫ ω, candidateSquarefreeSpectralTailVariance ω σ H ∂candidateCylinderLaw s η) ≤
      3 / (2 * Real.pi * H * mu.real (candidateCylinder s η)) := by
  apply (candidateCylinderLaw_integral_squarefreeSpectralTailVariance_le s η hσ hH).2.trans
  have hq : 0 < mu.real (candidateCylinder s η) :=
    ENNReal.toReal_pos (mu_candidateCylinder_ne_zero s η) (measure_ne_top _ _)
  apply (div_le_div_iff₀ (by positivity : 0 < Real.pi * H * mu.real (candidateCylinder s η))
    (by positivity : 0 < 2 * Real.pi * H * mu.real (candidateCylinder s η))).mpr
  nlinarith [mul_le_mul_of_nonneg_right hσone
    (show 0 ≤ 2 * Real.pi * H * mu.real (candidateCylinder s η) by positivity)]

end Erdos.Problem1144

#print axioms Erdos.Problem1144.candidate_squarefree_dirichletMass_le
#print axioms Erdos.Problem1144.candidate_integral_squarefreeAngularFourier_norm_sq_le
#print axioms Erdos.Problem1144.candidate_integral_squarefree_fourier_tail_le
#print axioms Erdos.Problem1144.candidateCylinderLaw_integral_squarefreeSpectralTailVariance_le
#print axioms Erdos.Problem1144.candidate_gaussian_maximum_tail_le_squarefreeSpectralTail
