import Erdos.Problem1144.HarperCandidateTranslationBinPartition
import Erdos.Problem1144.HarperCandidateTranslationSquarefreeBins

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Literal white kernels, finite support, and their step errors

The kernels vanish below the white-noise cutoff and above the coordinate's
summation endpoint. Their finite-bin representations therefore have exactly
the global Hilbert-space errors estimated in the preceding modules.
-/

theorem candidate_logProcess_abs_le_exp_half (ω : Omega) (t : ℝ) :
    |harperCandidateLogProcess ω t| ≤ Real.exp (t / 2) := by
  rw [candidate_logProcess_eq_S_div_exp, abs_div, abs_of_pos (Real.exp_pos _)]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have he : Real.exp (t / 2) * Real.exp (t / 2) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (abs_S_le ω _).trans (Nat.floor_le (Real.exp_pos t).le)

private theorem whiteKernel_memLp_two_of_bound (b : ℝ → ℝ) (hb : Measurable b)
    (hbound : ∀ s, |b s| ≤ Real.exp (s / 2)) (hzero : ∀ s < 0, b s = 0)
    (t : ℝ) {T : ℝ} (hT : 0 < T) :
    MemLp ((Ioi T).indicator (fun x ↦ b (t - x) / Real.sqrt x)) 2 volume := by
  let R := max T t
  let F : ℝ → ℝ := fun x ↦ b (t - x) / Real.sqrt x
  have hF : Measurable F := (hb.comp (measurable_const.sub measurable_id)).div
    Real.continuous_sqrt.measurable
  have heq : (Ioi T).indicator F = (Ioc T R).indicator F := by
    funext x
    by_cases hx : T < x
    · rw [Set.indicator_of_mem (show x ∈ Ioi T from hx)]
      by_cases hxR : x ≤ R
      · rw [Set.indicator_of_mem (show x ∈ Ioc T R from ⟨hx, hxR⟩)]
      · rw [Set.indicator_of_notMem (by simp only [mem_Ioc]; tauto)]
        have htx : t < x := (le_max_right T t).trans_lt (lt_of_not_ge hxR)
        simp only [F, hzero (t - x) (sub_neg.mpr htx), zero_div]
    · rw [Set.indicator_of_notMem (show x ∉ Ioi T from hx),
        Set.indicator_of_notMem (by simp only [mem_Ioc]; tauto)]
  rw [heq]
  apply (memLp_indicator_iff_restrict measurableSet_Ioc).mpr
  apply (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).mpr
  refine (integrable_const (μ := volume.restrict (Ioc T R))
    ((Real.exp ((t - T) / 2) / Real.sqrt T) ^ 2)).mono' (hF.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hbnd : |F x| ≤ Real.exp ((t - T) / 2) / Real.sqrt T := by
    rw [show F x = b (t - x) / Real.sqrt x by rfl, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg x)]
    apply div_le_div₀ (Real.exp_pos ((t - T) / 2)).le
      ((hbound (t - x)).trans (Real.exp_le_exp.mpr (by linarith [hx.1])))
      (Real.sqrt_pos.mpr hT) (Real.sqrt_le_sqrt hx.1.le)
  rw [Real.norm_eq_abs, abs_pow, sq_abs]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (F x)) hbnd 2

noncomputable def candidateCompleteWhiteKernel (ω : Omega) (t T x : ℝ) : ℝ :=
  (Ioi T).indicator (fun x ↦ harperCandidateLogProcess ω (t - x) / Real.sqrt x) x

noncomputable def candidateSquarefreeWhiteKernel (ω : Omega) (t T x : ℝ) : ℝ :=
  (Ioi T).indicator (fun x ↦ harperCandidateSquarefreeLogProcess ω (t - x) / Real.sqrt x) x

noncomputable def candidateCompleteWhiteStepKernel (ω : Omega) (t T h : ℝ) (n : ℕ) : ℝ → ℝ :=
  candidateWholeBinStep T h n (fun j ↦
    harperCandidateLogProcess ω (t - (T + (j : ℝ) * h + h)) / Real.sqrt (T + (j : ℝ) * h + h))

noncomputable def candidateSquarefreeWhiteStepKernel (ω : Omega) (t T h : ℝ) (n : ℕ) : ℝ → ℝ :=
  candidateWholeBinStep T h n (fun j ↦
    harperCandidateSquarefreeLogProcess ω (t - (T + (j : ℝ) * h + h)) /
      Real.sqrt (T + (j : ℝ) * h + h))

theorem candidate_memLp_completeWhiteKernel (ω : Omega) (t : ℝ) {T : ℝ} (hT : 0 < T) :
    MemLp (candidateCompleteWhiteKernel ω t T) 2 volume := by
  apply whiteKernel_memLp_two_of_bound (harperCandidateLogProcess ω)
    (measurable_harperCandidateLogProcess.comp measurable_prodMk_left)
    (candidate_logProcess_abs_le_exp_half ω) _ t hT
  intro s hs
  simp [harperCandidateLogProcess, not_le.mpr hs]

theorem candidate_memLp_squarefreeWhiteKernel (ω : Omega) (t : ℝ) {T : ℝ} (hT : 0 < T) :
    MemLp (candidateSquarefreeWhiteKernel ω t T) 2 volume := by
  apply whiteKernel_memLp_two_of_bound (harperCandidateSquarefreeLogProcess ω)
    (measurable_harperCandidateSquarefreeLogProcess.comp measurable_prodMk_left)
    (fun s ↦ candidate_squarefree_log_abs_le_exp_half ω (le_refl s)) _ t hT
  intro s hs
  simp [harperCandidateSquarefreeLogProcess, not_le.mpr hs]

theorem candidate_memLp_completeWhiteStepKernel (ω : Omega) (t T : ℝ) {h : ℝ}
    (hh : 0 ≤ h) (n : ℕ) : MemLp (candidateCompleteWhiteStepKernel ω t T h n) 2 volume :=
  candidate_memLp_wholeBinStep_two hh n _

theorem candidate_memLp_squarefreeWhiteStepKernel (ω : Omega) (t T : ℝ) {h : ℝ}
    (hh : 0 ≤ h) (n : ℕ) : MemLp (candidateSquarefreeWhiteStepKernel ω t T h n) 2 volume :=
  candidate_memLp_wholeBinStep_two hh n _

theorem candidateCompleteWhiteKernel_support (ω : Omega) {t T h : ℝ} {n : ℕ}
    (hcover : t ≤ T + (n : ℝ) * h) (x : ℝ) (hx : x ∉ Ioc T (T + (n : ℝ) * h)) :
    candidateCompleteWhiteKernel ω t T x = 0 := by
  by_cases hxT : T < x
  · have hxR : T + (n : ℝ) * h < x := by
      by_contra h
      exact hx ⟨hxT, le_of_not_gt h⟩
    have htx : t < x := hcover.trans_lt hxR
    rw [candidateCompleteWhiteKernel, Set.indicator_of_mem (show x ∈ Ioi T from hxT)]
    simp [harperCandidateLogProcess, not_le.mpr (sub_neg.mpr htx)]
  · exact Set.indicator_of_notMem (show x ∉ Ioi T from hxT) _

theorem candidateCompleteWhiteKernel_eq_of_mem_bin (ω : Omega) (t : ℝ) {T h x : ℝ}
    (hh : 0 ≤ h) {j : ℕ} (hx : x ∈ candidateWholeLogBin T h j) :
    candidateCompleteWhiteKernel ω t T x = harperCandidateLogProcess ω (t - x) / Real.sqrt x := by
  have hxT : T < x :=
    (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hh)).trans_lt hx.1
  exact Set.indicator_of_mem (show x ∈ Ioi T from hxT) _

/-- The global complete-model Hilbert-kernel error equals the literal
finite-bin error, including the bin crossing the coordinate's endpoint. -/
theorem candidate_completeWhiteKernel_step_error_eq (ω : Omega)
    {t T h : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h) (hcover : t ≤ T + (n : ℝ) * h) :
    (∫ x, (candidateCompleteWhiteKernel ω t T x -
      candidateCompleteWhiteStepKernel ω t T h n x) ^ 2) =
      ∑ j ∈ Finset.range n, ∫ x in Ioc (T + (j : ℝ) * h) (T + (j : ℝ) * h + h),
        (harperCandidateLogProcess ω (t - x) / Real.sqrt x -
          harperCandidateLogProcess ω (t - (T + (j : ℝ) * h + h)) /
            Real.sqrt (T + (j : ℝ) * h + h)) ^ 2 := by
  rw [candidateCompleteWhiteStepKernel, candidate_integral_sq_sub_wholeBinStep hh n _ _
    (candidate_memLp_completeWhiteKernel ω t hT) (candidateCompleteWhiteKernel_support ω hcover)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [candidateWholeLogBin_eq]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [candidateCompleteWhiteKernel_eq_of_mem_bin ω t hh
    (show x ∈ candidateWholeLogBin T h j by rwa [candidateWholeLogBin_eq])]

/-- Exact covariance of the literal complete white step kernel. -/
theorem candidate_completeWhiteStepKernel_gram_eq {ι : Type*} (ω : Omega)
    (t : ι → ℝ) (T : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    candidateWeightedGram volume (fun i ↦ candidateCompleteWhiteStepKernel ω (t i) T h n)
      (fun _ ↦ 1) = fun i k ↦ ∑ j ∈ Finset.range n,
        h * (harperCandidateLogProcess ω (t i - (T + (j : ℝ) * h + h)) /
          Real.sqrt (T + (j : ℝ) * h + h)) *
            (harperCandidateLogProcess ω (t k - (T + (j : ℝ) * h + h)) /
              Real.sqrt (T + (j : ℝ) * h + h)) :=
  candidate_wholeBinStep_gram_eq hh n _

/-- Expected global complete white/step Hilbert distance, with the actual
finite-bin analytic bound and no pathwise integrability hypothesis. -/
theorem candidate_integral_completeWhiteKernel_step_error_le
    {t T h L : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h)
    (htL : t - T + h ≤ L) (hL : 0 ≤ L) (hcover : t ≤ T + (n : ℝ) * h) :
    (∫ ω, (∫ x, (candidateCompleteWhiteKernel ω t T x -
      candidateCompleteWhiteStepKernel ω t T h n x) ^ 2) ∂mu) ≤
      (4 / T) * h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L) := by
  simp_rw [candidate_completeWhiteKernel_step_error_eq _ hT hh hcover]
  exact candidate_integral_sum_whiteStepSquare_le hT hh htL hL

theorem candidateSquarefreeWhiteKernel_support (ω : Omega) {t T h : ℝ} {n : ℕ}
    (hcover : t ≤ T + (n : ℝ) * h) (x : ℝ) (hx : x ∉ Ioc T (T + (n : ℝ) * h)) :
    candidateSquarefreeWhiteKernel ω t T x = 0 := by
  by_cases hxT : T < x
  · have hxR : T + (n : ℝ) * h < x := by
      by_contra h
      exact hx ⟨hxT, le_of_not_gt h⟩
    have htx : t < x := hcover.trans_lt hxR
    rw [candidateSquarefreeWhiteKernel, Set.indicator_of_mem (show x ∈ Ioi T from hxT)]
    simp [harperCandidateSquarefreeLogProcess, not_le.mpr (sub_neg.mpr htx)]
  · exact Set.indicator_of_notMem (show x ∉ Ioi T from hxT) _

theorem candidateSquarefreeWhiteKernel_eq_of_mem_bin (ω : Omega) (t : ℝ) {T h x : ℝ}
    (hh : 0 ≤ h) {j : ℕ} (hx : x ∈ candidateWholeLogBin T h j) :
    candidateSquarefreeWhiteKernel ω t T x =
      harperCandidateSquarefreeLogProcess ω (t - x) / Real.sqrt x := by
  have hxT : T < x :=
    (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hh)).trans_lt hx.1
  exact Set.indicator_of_mem (show x ∈ Ioi T from hxT) _

/-- The global squarefree-model Hilbert-kernel error equals the literal
finite-bin error, including the bin crossing the coordinate's endpoint. -/
theorem candidate_squarefreeWhiteKernel_step_error_eq (ω : Omega)
    {t T h : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h) (hcover : t ≤ T + (n : ℝ) * h) :
    (∫ x, (candidateSquarefreeWhiteKernel ω t T x -
      candidateSquarefreeWhiteStepKernel ω t T h n x) ^ 2) =
      ∑ j ∈ Finset.range n, ∫ x in Ioc (T + (j : ℝ) * h) (T + (j : ℝ) * h + h),
        (harperCandidateSquarefreeLogProcess ω (t - x) / Real.sqrt x -
          harperCandidateSquarefreeLogProcess ω (t - (T + (j : ℝ) * h + h)) /
            Real.sqrt (T + (j : ℝ) * h + h)) ^ 2 := by
  rw [candidateSquarefreeWhiteStepKernel, candidate_integral_sq_sub_wholeBinStep hh n _ _
    (candidate_memLp_squarefreeWhiteKernel ω t hT)
      (candidateSquarefreeWhiteKernel_support ω hcover)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [candidateWholeLogBin_eq]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [candidateSquarefreeWhiteKernel_eq_of_mem_bin ω t hh
    (show x ∈ candidateWholeLogBin T h j by rwa [candidateWholeLogBin_eq])]

/-- Exact covariance of the literal squarefree white step kernel. -/
theorem candidate_squarefreeWhiteStepKernel_gram_eq {ι : Type*} (ω : Omega)
    (t : ι → ℝ) (T : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    candidateWeightedGram volume (fun i ↦ candidateSquarefreeWhiteStepKernel ω (t i) T h n)
      (fun _ ↦ 1) = fun i k ↦ ∑ j ∈ Finset.range n,
        h * (harperCandidateSquarefreeLogProcess ω (t i - (T + (j : ℝ) * h + h)) /
          Real.sqrt (T + (j : ℝ) * h + h)) *
            (harperCandidateSquarefreeLogProcess ω (t k - (T + (j : ℝ) * h + h)) /
              Real.sqrt (T + (j : ℝ) * h + h)) :=
  candidate_wholeBinStep_gram_eq hh n _

/-- Expected global squarefree white/step Hilbert distance, with the actual
finite-bin analytic bound and no pathwise integrability hypothesis. -/
theorem candidate_integral_squarefreeWhiteKernel_step_error_le
    {t T h L : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h)
    (htL : t - T + h ≤ L) (hL : 0 ≤ L) (hcover : t ≤ T + (n : ℝ) * h) :
    (∫ ω, (∫ x, (candidateSquarefreeWhiteKernel ω t T x -
      candidateSquarefreeWhiteStepKernel ω t T h n x) ^ 2) ∂mu) ≤
      (4 / T) * h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L) := by
  simp_rw [candidate_squarefreeWhiteKernel_step_error_eq _ hT hh hcover]
  exact candidate_integral_sum_squarefreeWhiteStepSquare_le hT hh htL hL

theorem measurable_candidateCompleteWhiteKernel (t T : ℝ) :
    Measurable (fun z : Omega × ℝ ↦ candidateCompleteWhiteKernel z.1 t T z.2) := by
  have hF : Measurable (fun z : Omega × ℝ ↦
      harperCandidateLogProcess z.1 (t - z.2) / Real.sqrt z.2) :=
    (measurable_harperCandidateLogProcess.comp
      (measurable_fst.prodMk (measurable_const.sub measurable_snd))).div
        (Real.continuous_sqrt.measurable.comp measurable_snd)
  exact hF.ite (measurableSet_lt measurable_const measurable_snd) measurable_const

theorem measurable_candidateCompleteWhiteStepKernel (t T h : ℝ) (n : ℕ) :
    Measurable (fun z : Omega × ℝ ↦ candidateCompleteWhiteStepKernel z.1 t T h n z.2) := by
  unfold candidateCompleteWhiteStepKernel candidateWholeBinStep
  apply Finset.measurable_sum
  intro j _
  have hF : Measurable (fun z : Omega × ℝ ↦
      harperCandidateLogProcess z.1 (t - (T + (j : ℝ) * h + h)) /
        Real.sqrt (T + (j : ℝ) * h + h)) :=
    (measurable_harperCandidateLogProcess.comp
      (measurable_fst.prodMk measurable_const)).div_const _
  exact hF.ite ((measurableSet_candidateWholeLogBin T h j).preimage measurable_snd)
    measurable_const

theorem candidate_integrable_completeWhiteKernel_step_error
    {t T h : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h) (hcover : t ≤ T + (n : ℝ) * h) :
    Integrable (fun ω ↦ ∫ x, (candidateCompleteWhiteKernel ω t T x -
      candidateCompleteWhiteStepKernel ω t T h n x) ^ 2) mu := by
  simp_rw [candidate_completeWhiteKernel_step_error_eq _ hT hh hcover]
  apply integrable_finset_sum
  intro j _
  have hj : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hh
  exact (candidate_integrable_whiteStepSquare_product (L := max (t - T) 0)
    hT (by linarith) hh (by linarith [le_max_left (t - T) 0])
      (le_max_right (t - T) 0)).integral_prod_right

theorem measurable_candidateSquarefreeWhiteKernel (t T : ℝ) :
    Measurable (fun z : Omega × ℝ ↦ candidateSquarefreeWhiteKernel z.1 t T z.2) := by
  have hF : Measurable (fun z : Omega × ℝ ↦
      harperCandidateSquarefreeLogProcess z.1 (t - z.2) / Real.sqrt z.2) :=
    (measurable_harperCandidateSquarefreeLogProcess.comp
      (measurable_fst.prodMk (measurable_const.sub measurable_snd))).div
        (Real.continuous_sqrt.measurable.comp measurable_snd)
  exact hF.ite (measurableSet_lt measurable_const measurable_snd) measurable_const

theorem measurable_candidateSquarefreeWhiteStepKernel (t T h : ℝ) (n : ℕ) :
    Measurable (fun z : Omega × ℝ ↦ candidateSquarefreeWhiteStepKernel z.1 t T h n z.2) := by
  unfold candidateSquarefreeWhiteStepKernel candidateWholeBinStep
  apply Finset.measurable_sum
  intro j _
  have hF : Measurable (fun z : Omega × ℝ ↦
      harperCandidateSquarefreeLogProcess z.1 (t - (T + (j : ℝ) * h + h)) /
        Real.sqrt (T + (j : ℝ) * h + h)) :=
    (measurable_harperCandidateSquarefreeLogProcess.comp
      (measurable_fst.prodMk measurable_const)).div_const _
  exact hF.ite ((measurableSet_candidateWholeLogBin T h j).preimage measurable_snd)
    measurable_const

theorem candidate_integrable_squarefreeWhiteKernel_step_error
    {t T h : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h) (hcover : t ≤ T + (n : ℝ) * h) :
    Integrable (fun ω ↦ ∫ x, (candidateSquarefreeWhiteKernel ω t T x -
      candidateSquarefreeWhiteStepKernel ω t T h n x) ^ 2) mu := by
  simp_rw [candidate_squarefreeWhiteKernel_step_error_eq _ hT hh hcover]
  apply integrable_finset_sum
  intro j _
  have hj : 0 ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg j) hh
  exact (candidate_integrable_squarefreeWhiteStepSquare_product (L := max (t - T) 0)
    hT (by linarith) hh (by linarith [le_max_left (t - T) 0])
      (le_max_right (t - T) 0)).integral_prod_right

end Erdos.Problem1144
