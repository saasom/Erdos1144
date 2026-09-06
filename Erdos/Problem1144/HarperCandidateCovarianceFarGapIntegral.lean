import Erdos.Problem1144.HarperCandidateCovarianceSumDifference
import Erdos.Problem1144.HarperCandidateCovarianceGapRootMass
import Erdos.Problem1144.HarperCandidateCovarianceKernelMass

open MeasureTheory Set

namespace Erdos.Problem1144
noncomputable section

/-- The actual far-pair frequency domain in the retained outer window. -/
def candidateCovarianceFarFrequencyDomain (M d : ℝ) : Set (ℝ × ℝ) :=
  {z | |z.1| ≤ M ∧ |z.2| ≤ M ∧ d ≤ |z.1 - z.2|}

theorem candidate_measurableSet_farFrequencyDomain (M d : ℝ) :
    MeasurableSet (candidateCovarianceFarFrequencyDomain M d) := by
  unfold candidateCovarianceFarFrequencyDomain
  exact (measurableSet_le measurable_fst.abs measurable_const).inter
    ((measurableSet_le measurable_snd.abs measurable_const).inter
      (measurableSet_le measurable_const (measurable_fst.sub measurable_snd).abs))

/-- The literal two-channel far integrand is integrable on the original
finite frequency domain, before any enlargement in sum/difference coordinates. -/
theorem candidate_integrableOn_far_gapKernel (start stop : ℕ)
    {T B : ℝ} (hT : 0 < T) (hTB : T ≤ B) (M d : ℝ) :
    IntegrableOn (fun z : ℝ × ℝ =>
      Real.sqrt (candidateCovarianceGapEnvelope start stop |z.1 - z.2|) *
        Real.sqrt (candidateCovarianceGapEnvelope start stop |z.1 + z.2|) *
        ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖)
      (candidateCovarianceFarFrequencyDomain M d) (volume.prod volume) := by
  let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
  let Q := Icc (-M) M ×ˢ Icc (-M) M
  have hL : 0 ≤ L := (Problem520.one_le_log_harperBlockEndpoint stop).trans' (by norm_num)
  have hQ : (volume.prod volume) Q ≠ ⊤ :=
    (isCompact_Icc.prod isCompact_Icc).measure_ne_top
  have hi : IntegrableOn (fun _z : ℝ × ℝ => L * Real.log (B / T)) Q
      (volume.prod volume) := integrableOn_const hQ
  have hm : Measurable (fun z : ℝ × ℝ =>
      Real.sqrt (candidateCovarianceGapEnvelope start stop |z.1 - z.2|) *
        Real.sqrt (candidateCovarianceGapEnvelope start stop |z.1 + z.2|) *
        ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖) := by
    have hG := (candidate_continuous_gapEnvelope start stop).measurable
    have hK := candidate_measurable_whiteKernel T B
    fun_prop
  apply IntegrableOn.mono_set (t := Q) ?_
    (fun z hz => ⟨abs_le.mp hz.1, abs_le.mp hz.2.1⟩)
  apply hi.mono' hm.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (Real.sqrt L * Real.sqrt L) *
        ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖ := by
      gcongr <;> exact candidate_gapEnvelope_le_top start stop _
    _ = L * ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖ := by
      rw [Real.mul_self_sqrt hL]
    _ ≤ _ := mul_le_mul_of_nonneg_left (candidate_whiteKernel_norm_le_log hT hTB _) hL

/-- Integrate both clipped correlation channels against the actual far
kernel. The sum/difference change contributes one half, and its sum-channel
mass is bounded by Cauchy--Schwarz. No singularity is discarded. -/
theorem candidate_integral_far_gapKernel_le (start stop : ℕ)
    {T B M d : ℝ} (hT : 0 < T) (hTB : T ≤ B) (hM : 0 ≤ M) (hd : 0 < d) :
    let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
    let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
    let U := A * (2 * M) + 3 * Real.log (1 + L * (2 * M))
    (∫ z in candidateCovarianceFarFrequencyDomain M d,
      Real.sqrt (candidateCovarianceGapEnvelope start stop |z.1 - z.2|) *
        Real.sqrt (candidateCovarianceGapEnvelope start stop |z.1 + z.2|) *
        ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖ ∂volume.prod volume) ≤
      Real.sqrt (A + 2 / d) *
        (2 * (Real.log (B / T) + 2) * Real.log (1 + T * (2 * M)) / T) *
        (Real.sqrt (2 * M) * Real.sqrt U) := by
  let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
  let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
  let R := 2 * M
  let U := A * R + 3 * Real.log (1 + L * R)
  let G := candidateCovarianceGapEnvelope start stop
  let q := Real.sqrt (A + 2 / d)
  let S := candidateCovarianceFarFrequencyDomain M d
  let f := (Icc (-R) R).indicator (fun u => ‖candidateCovarianceWhiteKernel T B u‖)
  let g := (Icc (-R) R).indicator (fun v => Real.sqrt (G |v|))
  let P := fun z : ℝ × ℝ => f (z.1 - z.2) * g (z.1 + z.2)
  let F := fun z : ℝ × ℝ => Real.sqrt (G |z.1 - z.2|) *
    Real.sqrt (G |z.1 + z.2|) * ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hf : Integrable f :=
    (candidate_integrable_local_whiteKernel_norm hT hTB R).integrable_indicator measurableSet_Icc
  have hc : Continuous (fun v : ℝ => Real.sqrt (G |v|)) :=
    ((candidate_continuous_gapEnvelope start stop).comp continuous_abs).sqrt
  have hg : Integrable g := hc.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hP : Integrable P (volume.prod volume) := candidate_integrable_sumDifference_product hf hg
  have hP0 (z : ℝ × ℝ) : 0 ≤ P z := mul_nonneg
    (indicator_nonneg (fun _ _ => norm_nonneg _) _)
    (indicator_nonneg (fun _ _ => Real.sqrt_nonneg _) _)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hpoint (z : ℝ × ℝ) (hz : z ∈ S) : F z ≤ q * P z := by
    have hdiff : |z.1 - z.2| ≤ R := (abs_sub _ _).trans (by dsimp [R]; linarith [hz.1, hz.2.1])
    have hsum : |z.1 + z.2| ≤ R := (abs_add_le _ _).trans (by dsimp [R]; linarith [hz.1, hz.2.1])
    have hG : G |z.1 - z.2| ≤ A + 2 / d :=
      (candidate_gapEnvelope_le_reciprocal start stop (hd.trans_le hz.2.2)).trans
        (add_le_add (le_refl A)
          (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hd hz.2.2))
    dsimp only [P, f, g]
    rw [indicator_of_mem (show z.1 - z.2 ∈ Icc (-R) R from abs_le.mp hdiff),
      indicator_of_mem (show z.1 + z.2 ∈ Icc (-R) R from abs_le.mp hsum)]
    dsimp only [F, q]
    calc
      _ ≤ Real.sqrt (A + 2 / d) * Real.sqrt (G |z.1 + z.2|) *
          ‖candidateCovarianceWhiteKernel T B (z.1 - z.2)‖ := by
        gcongr
      _ = _ := by ring
  have hFmeas : Measurable F := by
    have hGc := (candidate_continuous_gapEnvelope start stop).measurable
    have hK := candidate_measurable_whiteKernel T B
    dsimp only [F, G]
    fun_prop
  have hSi := candidate_measurableSet_farFrequencyDomain M d
  have hFi : IntegrableOn F S (volume.prod volume) := by
    apply (hP.const_mul q).integrableOn.mono' hFmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hSi] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [F]; positivity)]
    exact hpoint z hz
  have hint : (∫ z in S, F z ∂volume.prod volume) ≤
      q * ((1 / 2 : ℝ) * candidateCovarianceLocalKernelMass T B R *
        ∫ v in Icc (-R) R, Real.sqrt (G |v|)) := by
    calc
      _ ≤ ∫ z in S, q * P z ∂volume.prod volume := integral_mono_ae hFi
        (hP.const_mul q).integrableOn ((ae_restrict_mem hSi).mono fun z hz => hpoint z hz)
      _ ≤ ∫ z, q * P z ∂volume.prod volume := setIntegral_le_integral (hP.const_mul q)
        (ae_of_all _ fun z => mul_nonneg hq (hP0 z))
      _ = _ := by
        rw [integral_const_mul, candidate_integral_sumDifference_product]
        dsimp only [f, g, candidateCovarianceLocalKernelMass]
        rw [integral_indicator measurableSet_Icc, integral_indicator measurableSet_Icc]
  have hmass := candidate_integral_sqrt_gapEnvelope_abs_le start stop hR
  change (∫ v in Icc (-R) R, Real.sqrt (G |v|)) ≤ 2 * (Real.sqrt R * Real.sqrt U) at hmass
  have hlast : (∫ z in S, F z ∂volume.prod volume) ≤
      q * candidateCovarianceLocalKernelMass T B R * (Real.sqrt R * Real.sqrt U) := by
    calc
      _ ≤ q * ((1 / 2 : ℝ) * candidateCovarianceLocalKernelMass T B R *
          (2 * (Real.sqrt R * Real.sqrt U))) := hint.trans (by
        gcongr
        exact mul_nonneg (by norm_num) (candidateCovarianceLocalKernelMass_nonneg T B R))
      _ = _ := by ring
  dsimp only
  exact hlast.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (candidate_local_whiteKernel_mass_le hT hTB hR) hq)
    (mul_nonneg (Real.sqrt_nonneg R) (Real.sqrt_nonneg U)))

end
end Erdos.Problem1144
