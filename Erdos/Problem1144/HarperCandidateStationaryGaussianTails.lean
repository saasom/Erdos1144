import Erdos.Problem1144.HarperCandidateStationaryGaussianComparison
import Erdos.Problem1144.HarperCandidateGaussianRealization
import Erdos.Problem1144.HarperCandidateSpectralCovarianceTail
import Erdos.Problem1144.HarperCandidateStationaryTailUnconditional
import Erdos.Problem1144.HarperCandidateStationaryTimeGeometry

open MeasureTheory ProbabilityTheory Filter Set Matrix
open scoped BigOperators Topology NNReal

namespace Erdos.Problem1144

local instance {ι : Type*} : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

private theorem exists_maximumTail_realization
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (A : Omega → Matrix ι ι ℝ) (V : Omega → ℝ) (r : ℝ)
    (hA : Measurable A) (hV : ∀ ω, 0 ≤ V ω)
    (hgood : ∀ᵐ ω ∂Q, (A ω).PosSemidef ∧ ∀ i, A ω i i ≤ V ω) :
    ∃ (X : ι → Omega × EuclideanSpace ℝ ι → ℝ) (v : Omega → ι → ℝ≥0),
      (∀ i, Measurable (X i)) ∧
      (∀ ω i, (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).map
        (fun ξ => X i (ω, ξ)) = gaussianReal 0 (v ω i)) ∧
      (∀ ω i, (v ω i : ℝ) ≤ V ω) ∧
      Integrable (fun ω => candidateGaussianMaximumTail (A ω) r) Q ∧
      (∫ ω, candidateGaussianMaximumTail (A ω) r ∂Q) =
        (Q.prod (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)).real
          {z | ∃ i, r ≤ |X i z|} := by
  classical
  let G : Set Omega := {ω | (A ω).PosSemidef ∧ ∀ i, A ω i i ≤ V ω}
  have huniv : NullMeasurableSet (univ : Set Omega) Q := MeasurableSet.univ.nullMeasurableSet
  have hnull : NullMeasurableSet G Q := huniv.congr (by
    filter_upwards [hgood] with ω hω
    change True = ((A ω).PosSemidef ∧ ∀ i, A ω i i ≤ V ω)
    exact propext ⟨fun _ => hω, fun _ => True.intro⟩)
  obtain ⟨E, hEG, hE, hEGae⟩ := hnull.exists_measurable_subset_ae_eq
  have hEae : ∀ᵐ ω ∂Q, ω ∈ E := by
    filter_upwards [hgood, hEGae] with ω hg he
    exact he.mpr hg
  let B : Omega → Matrix ι ι ℝ := E.indicator A
  have hB : Measurable B := hA.indicator hE
  have hBpos (ω : Omega) : (B ω).PosSemidef := by
    by_cases hω : ω ∈ E
    · simpa only [B, indicator_of_mem hω] using (hEG hω).1
    · simp only [B, indicator_of_notMem hω]
      exact Matrix.PosSemidef.zero
  have hBdiag (ω : Omega) (i : ι) : B ω i i ≤ V ω := by
    by_cases hω : ω ∈ E
    · simpa only [B, indicator_of_mem hω] using (hEG hω).2 i
    · simpa only [B, indicator_of_notMem hω, Matrix.zero_apply] using hV ω
  have hBA : B =ᵐ[Q] A := by
    filter_upwards [hEae] with ω hω
    exact indicator_of_mem hω A
  let F := candidateConditionalGaussian B
  have hF : Measurable F := candidate_measurable_conditionalGaussian hB hBpos
  let X : ι → Omega × EuclideanSpace ℝ ι → ℝ := fun i z => F z i
  let v : Omega → ι → ℝ≥0 := fun ω i => (B ω i i).toNNReal
  have hXm (i : ι) : Measurable (X i) :=
    (show Measurable (fun x : EuclideanSpace ℝ ι => x i) by fun_prop).comp hF
  have hXmap (ω : Omega) (i : ι) :
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).map (fun ξ => X i (ω, ξ)) =
        gaussianReal 0 (v ω i) := by
    have hm : Measurable (fun ξ => F (ω, ξ)) := hF.comp measurable_prodMk_left
    rw [show (fun ξ => X i (ω, ξ)) = (fun x : EuclideanSpace ℝ ι => x i) ∘
        (fun ξ => F (ω, ξ)) from rfl, ← Measure.map_map (by fun_prop) hm,
      candidate_conditionalGaussian_map B hBpos ω]
    exact (measurePreserving_eval_multivariateGaussian (μ := 0) (hBpos ω) (i := i)).map_eq
  let U : Set (Omega × EuclideanSpace ℝ ι) := {z | ∃ i, r ≤ |X i z|}
  have hU : MeasurableSet U := by
    simp only [U, setOf_exists]
    exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (hXm i).abs
  have hbox : MeasurableSet {x : EuclideanSpace ℝ ι | ∃ i, r ≤ |x i|} := by
    simp only [setOf_exists]
    exact MeasurableSet.iUnion fun i => measurableSet_le measurable_const (by fun_prop)
  have hfiber (ω : Omega) :
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).real
        {ξ | (ω, ξ) ∈ U} = candidateGaussianMaximumTail (B ω) r := by
    have hpres : MeasurePreserving (fun ξ => F (ω, ξ))
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1)
        (multivariateGaussian 0 (B ω)) :=
      ⟨hF.comp measurable_prodMk_left, candidate_conditionalGaussian_map B hBpos ω⟩
    exact hpres.measureReal_preimage hbox.nullMeasurableSet
  have hiB : Integrable (fun ω => candidateGaussianMaximumTail (B ω) r) Q := by
    have hi : Integrable (fun ω => (multivariateGaussian (0 : EuclideanSpace ℝ ι) 1).real
        {ξ | (ω, ξ) ∈ U}) Q := Measure.integrable_measure_prodMk_left hU (by finiteness)
    simpa only [hfiber] using hi
  have heq : (fun ω => candidateGaussianMaximumTail (B ω) r) =ᵐ[Q]
      (fun ω => candidateGaussianMaximumTail (A ω) r) :=
    hBA.fun_comp (fun M => candidateGaussianMaximumTail M r)
  refine ⟨X, v, hXm, hXmap, fun ω i => ?_, hiB.congr heq, ?_⟩
  · simpa only [v, Real.coe_toNNReal _ (hBpos ω).diag_nonneg] using hBdiag ω i
  · rw [← integral_congr_ae heq]
    simp_rw [← hfiber]
    rw [measureReal_def, Measure.prod_apply hU]
    exact integral_toReal (measurable_measure_prodMk_left hU).aemeasurable
      (ae_of_all _ fun _ => measure_lt_top _ _)

/-- An almost-sure PSD covariance with a common diagonal budget has the
actual averaged Gaussian maximum bound. The null exceptional covariance
values require no measurable good-event premise. -/
theorem candidate_integral_gaussianMaximumTail_le_log_variance
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (A : Omega → Matrix ι ι ℝ) (V : Omega → ℝ) {r : ℝ}
    (hA : Measurable A) (hVm : Measurable V) (hV : ∀ ω, 0 ≤ V ω)
    (hgood : ∀ᵐ ω ∂Q, (A ω).PosSemidef ∧ ∀ i, A ω i i ≤ V ω)
    (hVi : Integrable V Q) (hr : 0 < r) :
    Integrable (fun ω => candidateGaussianMaximumTail (A ω) r) Q ∧
    (∫ ω, candidateGaussianMaximumTail (A ω) r ∂Q) ≤
      4 * Real.log (2 * Fintype.card ι) * (∫ ω, V ω ∂Q) / r ^ 2 +
        1 / (2 * Fintype.card ι) := by
  obtain ⟨X, v, hXm, hX, hv, hi, heq⟩ :=
    exists_maximumTail_realization Q A V r hA hV hgood
  refine ⟨hi, ?_⟩
  rw [heq]
  exact candidate_gaussian_maximum_tail_le_log_variance
    (V := fun ω => ⟨V ω, hV ω⟩) hXm hVm.subtype_mk hX hv hVi hr

/-- Every measurable almost-sure PSD covariance family has an integrable
actual maximum-tail probability, including empty grids and any threshold. -/
theorem candidate_integrable_gaussianMaximumTail_of_ae_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (A : Omega → Matrix ι ι ℝ) (hA : Measurable A)
    (hpos : ∀ᵐ ω ∂Q, (A ω).PosSemidef) (r : ℝ) :
    Integrable (fun ω => candidateGaussianMaximumTail (A ω) r) Q := by
  classical
  let V := fun ω => ∑ i, |A ω i i|
  have hV (ω : Omega) : 0 ≤ V ω := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hgood : ∀ᵐ ω ∂Q, (A ω).PosSemidef ∧ ∀ i, A ω i i ≤ V ω := by
    filter_upwards [hpos] with ω hp
    refine ⟨hp, fun i => ?_⟩
    exact (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (A ω j j))
      (Finset.mem_univ i))
  obtain ⟨_, _, _, _, _, hi, _⟩ := exists_maximumTail_realization Q A V r hA hV hgood
  exact hi

/-- The literal high-frequency squarefree covariance has a uniform averaged
maximum bound, independent of the locations of the finite grid. -/
theorem candidate_integral_squarefreeHighCovariance_tail_le
    (s : Finset ℕ) (η : s → Bool) {m : ℕ} (hm : 0 < m)
    (u : Fin m → ℝ) {σ H r : ℝ} (hσ : 0 < σ) (hH : 0 < H) (hr : 0 < r) :
    Integrable (fun ω => candidateGaussianMaximumTail
      (candidateSquarefreeHighCovariance ω σ H u) r) (candidateCylinderLaw s η) ∧
    (∫ ω, candidateGaussianMaximumTail (candidateSquarefreeHighCovariance ω σ H u) r
      ∂candidateCylinderLaw s η) ≤
      4 * Real.log (2 * m) * ((σ + 1 / 2) /
        (Real.pi * H * mu.real (candidateCylinder s η))) / r ^ 2 + 1 / (2 * m) := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hg : ∀ᵐ ω ∂candidateCylinderLaw s η,
      (candidateSquarefreeHighCovariance ω σ H u).PosSemidef ∧
      ∀ i, candidateSquarefreeHighCovariance ω σ H u i i ≤
        candidateSquarefreeSpectralTailVariance ω σ H := by
    filter_upwards [candidateCylinderLaw_ae_squarefree_covariance_split s η hσ] with ω hω
    exact ⟨(hω m u H).2.2.1, fun i => ((hω m u H).2.2.2 i).le⟩
  have hv := candidateCylinderLaw_integral_squarefreeSpectralTailVariance_le s η hσ hH
  have h := candidate_integral_gaussianMaximumTail_le_log_variance (candidateCylinderLaw s η)
    (fun ω => candidateSquarefreeHighCovariance ω σ H u)
    (fun ω => candidateSquarefreeSpectralTailVariance ω σ H)
    (measurable_candidateSquarefreeHighCovariance σ H u)
    (measurable_candidateSquarefreeSpectralTailVariance σ H)
    (fun ω => candidateSquarefreeSpectralTailVariance_nonneg ω hσ.le H) hg hv.1 hr
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [Fintype.card_fin]
  apply add_le_add _ le_rfl
  apply div_le_div_of_nonneg_right _ (sq_nonneg r)
  exact mul_le_mul_of_nonneg_left hv.2 (mul_nonneg (by norm_num)
    (Real.log_nonneg (by exact_mod_cast show 1 ≤ 2 * m by omega)))

/-- The actual omitted complete stationary covariance is measurable in the
sign environment, with its original scalar normalization. -/
theorem candidate_measurable_stationaryExtensionCovariance
    {ι : Type*} (u : ι → ℝ) (T W : ℝ) :
    Measurable (fun ω => candidateStationaryExtensionCovariance ω u T W) := by
  have hf (i : ι) : Measurable (fun z : Omega × ℝ =>
      harperCandidateLogProcess z.1 (u i - z.2) * Real.exp (-(W / T) * (u i - z.2))) :=
    (measurable_harperCandidateLogProcess.comp
      (measurable_fst.prodMk (measurable_const.sub measurable_snd))).mul (by fun_prop)
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact StronglyMeasurable.measurable
    (StronglyMeasurable.integral_prod_right
      (f := fun ω v => (1 / T) *
        (harperCandidateLogProcess ω (u i - v) * Real.exp (-(W / T) * (u i - v))) *
        (harperCandidateLogProcess ω (u j - v) * Real.exp (-(W / T) * (u j - v))))
      ((measurable_const.mul (hf i)).mul (hf j)).stronglyMeasurable
      (ν := volume.restrict (Iio T)))

/-- The actual extension-tail probability is integrable for every finite
grid; no lower-time or energy-budget hypothesis is needed for regularity. -/
theorem candidate_integrable_stationaryExtension_tail
    (s : Finset ℕ) (η : s → Bool) {m : ℕ} (u : Fin m → ℝ)
    {T W : ℝ} (hT : 0 < T) (hW : 0 < W) (r : ℝ) :
    Integrable (fun ω => candidateGaussianMaximumTail
      (candidateStationaryExtensionCovariance ω u T W) r) (candidateCylinderLaw s η) := by
  apply candidate_integrable_gaussianMaximumTail_of_ae_posSemidef (candidateCylinderLaw s η)
    (fun ω => candidateStationaryExtensionCovariance ω u T W)
    (candidate_measurable_stationaryExtensionCovariance u T W) _ r
  filter_upwards [candidateCylinderLaw_ae_complete_stationary_split s η hT hW] with ω hω
  exact (hω m u).2.2

/-- The literal omitted stationary Gaussian maximum is bounded by the
damped complete-energy moment. Both the law and its averaging are derived;
no Gaussian-realization or covariance-error premise remains. -/
theorem candidate_integral_stationaryExtension_tail_le_energy_moment
    (s : Finset ℕ) (η : s → Bool) {m : ℕ} (hm : 0 < m) (u : Fin m → ℝ)
    {c T W M q r : ℝ} (hc : 0 ≤ c) (hT : 0 < T) (hW : 0 < W)
    (hM : 0 < M) (hq : 0 < q) (hr : 0 < r)
    (hu : ∀ i, (1 + c) * T ≤ u i)
    (hMoment : Integrable (fun ω => candidateDampedCompleteEnergy (W / (2 * T)) ω ^ q)
      (candidateCylinderLaw s η)) :
    Integrable (fun ω => candidateGaussianMaximumTail
      (candidateStationaryExtensionCovariance ω u T W) r) (candidateCylinderLaw s η) ∧
    (∫ ω, candidateGaussianMaximumTail (candidateStationaryExtensionCovariance ω u T W) r
      ∂candidateCylinderLaw s η) ≤
      4 * Real.log (2 * m) * (2 * Real.exp (-c * W) / W * M) / r ^ 2 +
        1 / (2 * m) +
        (∫ ω, candidateDampedCompleteEnergy (W / (2 * T)) ω ^ q
          ∂candidateCylinderLaw s η) / M ^ q := by
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hgood : ∀ᵐ ω ∂candidateCylinderLaw s η,
      (candidateStationaryExtensionCovariance ω u T W).PosSemidef ∧
      ∀ i, candidateStationaryExtensionCovariance ω u T W i i ≤
        candidateCompleteStationaryTailVariance ω c T W := by
    filter_upwards [candidateCylinderLaw_ae_complete_stationary_split s η hT hW,
      candidateCylinderLaw_ae_stationaryExtension_diag_le s η hT hW] with ω hpos hdiag
    exact ⟨(hpos m u).2.2, hdiag m u hu⟩
  obtain ⟨X, v, hXm, hX, hv, hi, heq⟩ := exists_maximumTail_realization
    (candidateCylinderLaw s η) (fun ω => candidateStationaryExtensionCovariance ω u T W)
    (fun ω => candidateCompleteStationaryTailVariance ω c T W) r
    (candidate_measurable_stationaryExtensionCovariance u T W)
    (fun ω => by unfold candidateCompleteStationaryTailVariance; positivity) hgood
  refine ⟨hi, ?_⟩
  rw [heq]
  simpa only [Fintype.card_fin] using candidate_stationary_gaussian_maximum_le_energy_moment
    s η hc hT hW hM hq hr hXm hX (ae_of_all _ hv) hMoment

end Erdos.Problem1144
