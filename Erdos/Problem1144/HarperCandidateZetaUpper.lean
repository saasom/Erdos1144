import Erdos.Problem520.External.PNT.ZetaBounds
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

open Complex Filter Set Topology MeasureTheory

namespace Erdos.Problem1144

noncomputable section

/-- The removable residue function, with the actual residue assigned at one. -/
def candidatePoleRemovedZetaResidue : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * riemannZeta s) 1 1

theorem continuous_candidatePoleRemovedZetaResidue :
    Continuous candidatePoleRemovedZetaResidue := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s = 1
  · subst s
    rw [candidatePoleRemovedZetaResidue, continuousAt_update_same]
    exact riemannZeta_residue_one
  · rw [candidatePoleRemovedZetaResidue, continuousAt_update_of_ne hs]
    exact (continuousAt_id.sub continuousAt_const).mul
      (differentiableAt_riemannZeta hs).continuousAt

/-- Uniform bounded-height upper bound retaining the pole distance. -/
theorem candidate_exists_zeta_upper_bounded_height :
    ∃ C : ℝ, 0 < C ∧ ∀ (v u : ℝ), v ∈ Icc 1 2 → |u| ≤ 3 →
      (v : ℂ) + u * I ≠ 1 →
      ‖riemannZeta (v + u * I)‖ ≤ C / ‖(v : ℂ) + u * I - 1‖ := by
  let K : Set ℂ := Icc (1 : ℝ) 2 ×ℂ Icc (-3 : ℝ) 3
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    continuous_candidatePoleRemovedZetaResidue.norm.continuousOn
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  intro v u hv hu hs
  have hz : (v : ℂ) + u * I ∈ K := by
    simpa [K, Complex.mem_reProdIm] using And.intro hv (abs_le.mp hu)
  have hb := hB (mem_image_of_mem (fun z => ‖candidatePoleRemovedZetaResidue z‖) hz)
  simp only [candidatePoleRemovedZetaResidue, Function.update_of_ne hs, norm_mul] at hb
  apply (le_div_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs))).mpr
  nlinarith [le_max_left B (0 : ℝ)]

/-- The existing #520 zeta upper bound specializes to the whole strip used
by the damped complete transform; it has no extra arithmetic premise. -/
theorem candidate_exists_zeta_upper_large_height :
    ∃ C : ℝ, 0 < C ∧ ∀ (v u : ℝ), v ∈ Icc 1 2 → 3 < |u| →
      ‖riemannZeta (v + u * I)‖ ≤ C * Real.log |u| := by
  obtain ⟨A, hA, C, hC, hbound⟩ := ZetaUpperBnd
  refine ⟨C, hC, ?_⟩
  intro v u hv hu
  apply hbound v u hu
  refine ⟨?_, hv.2⟩
  have hlog : 0 < Real.log |u| := Real.log_pos (by linarith)
  have hnonneg : 0 ≤ A / Real.log |u| := div_nonneg hA.1.le hlog.le
  linarith [hv.1]

/-- Simultaneous bounds for the literal zeta multiplier. At small height
the denominator includes the damping, so the central interval is covered. -/
theorem candidate_exists_shifted_zeta_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Ioc (0 : ℝ) (1 / 2), ∀ t : ℝ,
      (|t| ≤ 3 / 2 →
        ‖riemannZeta ((1 + 2 * σ : ℝ) + (2 * t : ℝ) * I)‖ ≤ C / (σ + |t|)) ∧
      (3 / 2 < |t| →
        ‖riemannZeta ((1 + 2 * σ : ℝ) + (2 * t : ℝ) * I)‖ ≤
          C * Real.log (2 * |t|)) := by
  obtain ⟨C₀, hC₀, hb⟩ := candidate_exists_zeta_upper_bounded_height
  obtain ⟨C₁, hC₁, hh⟩ := candidate_exists_zeta_upper_large_height
  refine ⟨max C₀ C₁, lt_of_lt_of_le hC₀ (le_max_left _ _), ?_⟩
  intro σ hσ t
  have hσpos := hσ.1
  have hv : 1 + 2 * σ ∈ Icc (1 : ℝ) 2 := ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hs : ((1 + 2 * σ : ℝ) : ℂ) + (2 * t : ℝ) * I ≠ 1 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    linarith [hσ.1]
  constructor
  · intro ht
    have h := hb (1 + 2 * σ) (2 * t) hv
      (by rw [abs_mul]; norm_num; linarith) hs
    have hnorm : σ + |t| ≤ ‖((1 + 2 * σ : ℝ) : ℂ) + (2 * t : ℝ) * I - 1‖ := by
      have hr := Complex.abs_re_le_norm (((1 + 2 * σ : ℝ) : ℂ) + (2 * t : ℝ) * I - 1)
      have hi := Complex.abs_im_le_norm (((1 + 2 * σ : ℝ) : ℂ) + (2 * t : ℝ) * I - 1)
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul,
        sub_zero, add_zero, Complex.one_re, add_sub_cancel_left, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hσ.1] at hr
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
        add_zero, zero_add, Complex.one_im, sub_zero, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hi
      linarith
    exact h.trans ((div_le_div_of_nonneg_left hC₀.le (by positivity) hnorm).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)))
  · intro ht
    have hu : 3 < |2 * t| := by rw [abs_mul]; norm_num; linarith
    have h := hh (1 + 2 * σ) (2 * t) hv hu
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.log_nonneg (by linarith)))

/-- Away from the central interval the zeta multiplier has a uniform weak
power bound. The exponent is chosen so its squared Cauchy weight is integrable. -/
theorem candidate_exists_shifted_zeta_power_upper {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Ioc (0 : ℝ) (1 / 2), ∀ t : ℝ, η ≤ |t| →
      ‖riemannZeta ((1 + 2 * σ : ℝ) + (2 * t : ℝ) * I)‖ ≤
        C * (1 + t ^ 2) ^ (1 / 8 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := candidate_exists_shifted_zeta_upper
  refine ⟨max (C / η) (8 * C), lt_of_lt_of_le (by positivity) (le_max_right _ _), ?_⟩
  intro σ hσ t ht
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hr : 1 ≤ (1 + t ^ 2) ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg t]) (by norm_num)
  by_cases hsmall : |t| ≤ 3 / 2
  · refine ((hbound σ hσ t).1 hsmall).trans ?_
    have hd : C / (σ + |t|) ≤ C / η :=
      div_le_div_of_nonneg_left hC.le hη (by linarith [hσ.1])
    exact hd.trans ((le_max_left _ _).trans
      (le_mul_of_one_le_right (le_trans (by positivity : (0 : ℝ) ≤ C / η)
        (le_max_left _ _)) hr))
  · have hh := (hbound σ hσ t).2 (lt_of_not_ge hsmall)
    have hl := Real.log_le_rpow_div (x := 2 * |t|) (by positivity)
      (by norm_num : (0 : ℝ) < 1 / 8)
    have habs : 2 * |t| ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (|t| - 1), sq_abs t]
    have hpow : (2 * |t|) ^ (1 / 8 : ℝ) ≤ (1 + t ^ 2) ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) habs (by norm_num)
    have hl' : Real.log (2 * |t|) ≤ 8 * (1 + t ^ 2) ^ (1 / 8 : ℝ) := by linarith
    calc
      _ ≤ C * Real.log (2 * |t|) := hh
      _ ≤ (8 * C) * (1 + t ^ 2) ^ (1 / 8 : ℝ) := by nlinarith [hC]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- The exact deterministic spectral weight of the complete normalized
partial-sum transform. -/
def candidateCompleteZetaWeight (σ t : ℝ) : ℝ :=
  ‖riemannZeta ((1 + 2 * σ : ℝ) + (2 * t : ℝ) * I)‖ ^ 2 /
    ((1 / 2 + σ) ^ 2 + t ^ 2)

theorem candidateCompleteZetaWeight_nonneg (σ t : ℝ) :
    0 ≤ candidateCompleteZetaWeight σ t := by unfold candidateCompleteZetaWeight; positivity

/-- An integrable majorant independent of the damping controls the complete
zeta weight outside every fixed central interval. -/
theorem candidate_complete_zeta_weight_integrable_majorant {η : ℝ} (hη : 0 < η) :
    ∃ g : ℝ → ℝ, Integrable g ∧ (∀ t, 0 ≤ g t) ∧
      ∀ σ ∈ Ioc (0 : ℝ) (1 / 2), ∀ t, η ≤ |t| →
        candidateCompleteZetaWeight σ t ≤ g t := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_shifted_zeta_power_upper hη
  let g : ℝ → ℝ := fun t => 4 * C ^ 2 * (1 + t ^ 2) ^ (-(3 / 4 : ℝ))
  have hi : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-(3 / 4 : ℝ))) := by
    have hi0 := (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (r := 3 / 2) (by norm_num))
    norm_num at hi0
    exact hi0
  refine ⟨g, hi.const_mul _, fun t => by dsimp [g]; positivity, ?_⟩
  intro σ hσ t ht
  have hσpos := hσ.1
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hd : 0 < (1 / 2 + σ) ^ 2 + t ^ 2 := by positivity
  have hden : (1 + t ^ 2) / 4 ≤ (1 / 2 + σ) ^ 2 + t ^ 2 := by
    nlinarith [sq_nonneg t]
  have hnum := pow_le_pow_left₀ (norm_nonneg _) (hb σ hσ t ht) 2
  have hpow : ((1 + t ^ 2) ^ (1 / 8 : ℝ)) ^ 2 = (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_mul_natCast hp.le]
    norm_num
  rw [mul_pow, hpow] at hnum
  have he : (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2) =
      (1 + t ^ 2) ^ (-(3 / 4 : ℝ)) := by
    have he0 := (Real.rpow_sub hp (1 / 4 : ℝ) 1).symm
    norm_num at he0
    exact he0
  unfold candidateCompleteZetaWeight
  calc
    _ ≤ (C ^ 2 * (1 + t ^ 2) ^ (1 / 4 : ℝ)) / ((1 / 2 + σ) ^ 2 + t ^ 2) :=
      div_le_div_of_nonneg_right hnum hd.le
    _ ≤ (C ^ 2 * (1 + t ^ 2) ^ (1 / 4 : ℝ)) / ((1 + t ^ 2) / 4) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = g t := by
      dsimp [g]
      rw [← he]
      field_simp

theorem continuous_candidateCompleteZetaWeight {σ : ℝ} (hσ : 0 < σ) :
    Continuous (candidateCompleteZetaWeight σ) := by
  have hz : Continuous (fun t : ℝ =>
      riemannZeta ((1 + 2 * σ : ℝ) + (2 * t : ℝ) * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : ((1 + 2 * σ : ℝ) : ℂ) + (2 * t : ℝ) * I ≠ 1 := by
      intro he
      have hre := congrArg Complex.re he
      simp at hre
      linarith
    have hf : ContinuousAt
        (fun u : ℝ => ((1 + 2 * σ : ℝ) : ℂ) + (2 * u : ℝ) * I) t := by fun_prop
    exact ContinuousAt.comp
      (g := riemannZeta)
      (f := fun u : ℝ => ((1 + 2 * σ : ℝ) : ℂ) + (2 * u : ℝ) * I)
      (differentiableAt_riemannZeta hne).continuousAt hf
  exact (hz.norm.pow 2).div (by fun_prop)
    (fun t => ne_of_gt (by positivity : 0 < (1 / 2 + σ) ^ 2 + t ^ 2))

/-- The high-frequency complete-transform weight has a uniformly bounded
integral, independent of the positive damping approaching zero. -/
theorem candidate_complete_zeta_weight_high_integral_bounded {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Ioc (0 : ℝ) (1 / 2),
      IntegrableOn (candidateCompleteZetaWeight σ) {t | η ≤ |t|} ∧
      (∫ t in {t | η ≤ |t|}, candidateCompleteZetaWeight σ t) ≤ C := by
  obtain ⟨g, hi, hg, hb⟩ := candidate_complete_zeta_weight_integrable_majorant hη
  have hE : MeasurableSet {t : ℝ | η ≤ |t|} := measurableSet_le measurable_const (by fun_prop)
  refine ⟨∫ t, g t, integral_nonneg hg, ?_⟩
  intro σ hσ
  have hf : IntegrableOn (candidateCompleteZetaWeight σ) {t | η ≤ |t|} := by
    apply hi.integrableOn.mono'
      (continuous_candidateCompleteZetaWeight hσ.1).measurable.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hE] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (candidateCompleteZetaWeight_nonneg σ t)]
      using hb σ hσ t ht
  refine ⟨hf, (setIntegral_mono_on hf hi.integrableOn hE (hb σ hσ)).trans ?_⟩
  exact setIntegral_le_integral hi (ae_of_all _ hg)

/-- The central complete-transform weight retains both the pole damping
and the frequency, with a uniform constant. -/
theorem candidate_complete_zeta_weight_central_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Ioc (0 : ℝ) (1 / 2), ∀ t : ℝ, |t| ≤ 3 / 2 →
      candidateCompleteZetaWeight σ t ≤ C / (σ + |t|) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := candidate_exists_shifted_zeta_upper
  refine ⟨4 * C ^ 2, by positivity, ?_⟩
  intro σ hσ t ht
  have hσpos := hσ.1
  have hd : 0 < (1 / 2 + σ) ^ 2 + t ^ 2 := by positivity
  have hden : (1 / 4 : ℝ) ≤ (1 / 2 + σ) ^ 2 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hnum := pow_le_pow_left₀ (norm_nonneg _) ((hb σ hσ t).1 ht) 2
  unfold candidateCompleteZetaWeight
  calc
    _ ≤ (C / (σ + |t|)) ^ 2 / ((1 / 2 + σ) ^ 2 + t ^ 2) :=
      div_le_div_of_nonneg_right hnum hd.le
    _ ≤ (C / (σ + |t|)) ^ 2 / (1 / 4) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) hden
    _ = _ := by rw [div_pow]; ring

end

end Erdos.Problem1144
