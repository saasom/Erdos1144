import Erdos.Problem1144.HarperCandidateCovarianceScheduledDeletionBudget
import Erdos.Problem1144.HarperCandidateSpectralTail

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- The actual common retained-frequency error on the rounded schedule. -/
def candidateCovarianceScheduledRetainedError (J : ℕ) (T : ℝ) : Omega → ℝ :=
  candidateCovarianceRetainedError (candidateEulerTopCutoff T)
    (candidateCovarianceScheduleStart J T) (candidateCovarianceScheduleLength J T)
    (candidateCovarianceScheduleDepth T) (candidateCovarianceScheduleHeight T)
    (Real.log T) T (candidateCovarianceScheduleSelected J T)

/-- The literal retained-error expectation has the predicted decay rate.
All annulus, interior-prefix and terminal-prefix costs are included, and
the exact finite Euler normalizer is bounded by the proved Mertens theorem. -/
theorem candidate_exists_scheduledRetainedError_integral_le :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∃ K > 0, ∀ᶠ T : ℝ in atTop,
      (∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂mu) ≤
        K * Real.log (Real.log T) ^ 4 / Real.log T := by
  obtain ⟨C, hC, D, hD, J₀, hb⟩ := candidate_exists_retainedError_integral_bound
  refine ⟨J₀, ?_⟩
  intro J hJ
  obtain ⟨P, hP, hdel⟩ := candidate_exists_scheduledDeletionBudget_le C D hC hD J
  let Z := Real.exp (1 - Real.log (Real.log 2) + 2 * (Real.log 4 + 4) / Real.log 2)
  let R := 2 * Real.log (Problem520.harperBlockEndpoint 0 : ℝ)
  let K := (Z / (2 * Real.pi)) * (8 * R + 2 + 2 * Real.pi * P)
  have hZ : 0 < Z := Real.exp_pos _
  have hR : 0 < R := by
    have := Problem520.one_le_log_harperBlockEndpoint 0
    dsimp only [R]; linarith
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  have hq2 : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  filter_upwards [hdel, candidate_eventually_covarianceSchedule_geometry J,
    eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
    hq2.eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ))]
    with T hdelT hg hTbase hθ hbase
  obtain ⟨hT1, hq1, hstart, hN6, hstrong, hstop, ha3, hk, hlo, hd, hM0, hwin⟩ := hg
  let q := Real.log T
  let θ := Real.log q
  let N := candidateCovarianceScheduleLength J T
  let start := candidateCovarianceScheduleStart J T
  let M := candidateCovarianceScheduleHeight T
  let y := candidateEulerTopCutoff T
  let s := candidateCovarianceScheduleSelected J T
  have hT : 0 < T := by linarith
  change 1 ≤ q at hq1
  change 1 ≤ θ at hθ
  have hq : 0 < q := by linarith
  have hθ4 : 1 ≤ θ ^ 4 := one_le_pow₀ hθ
  have hM : (0 : ℝ) < M := by exact_mod_cast hM0
  have hMsq : q ^ 2 ≤ (M : ℝ) := (candidate_covarianceSchedule_height_bounds T).1
  have hy2 : 2 ≤ y := (by norm_num : 2 ≤ 16).trans
    (Problem520.harperBlockEndpoint_ge_sixteen _)
  have hY : Problem520.harperBlockEndpoint (start + N) ≤ y := by
    have hst : start ≤ candidateEulerTopIndex T := hstrong.le.trans hstop
    have he : start + N = candidateEulerTopIndex T := by
      dsimp only [N, candidateCovarianceScheduleLength, start] at *
      omega
    exact le_of_eq (congrArg Problem520.harperBlockEndpoint he)
  have hstart' : J₀ + candidateCovarianceScheduleDepth T ≤ start := by
    dsimp only [start, candidateCovarianceScheduleStart]; omega
  have ha : 3 ≤ N / 2 := by change 6 ≤ N at hN6; omega
  have hscreen : ∀ j ∈ s, N / 2 ≤ j ∧ j ≤ N := by
    intro j hj
    exact Finset.mem_Icc.mp hj
  have hnum := hb (candidateCovarianceScheduleDepth T) start M hstart'
    (by dsimp only [M]; omega) (by change 2 * (M : ℝ) ≤ _ at hwin; linarith)
    N (N / 2) (by change 6 ≤ N at hN6; omega) ha s hscreen y hY q T hq1 hT
  have hn : Problem520.primeEnergyNormalizer y / (2 * Real.pi * T) ≤ Z / (2 * Real.pi) := by
    have hm := (Problem520.primeEnergyNormalizer_le_mertensConstant_mul_log hy2).trans
      (mul_le_mul_of_nonneg_left (candidateEulerTopCutoff_log_bounds hTbase).2 hZ.le)
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi * T)).mpr
    convert hm using 1 <;> dsimp only [Z] <;> field_simp
  have hlow : (1 / 2 : ℝ) ^ (candidateCovarianceScheduleDepth T + 1) ≤ R / q := by
    have hh := candidate_covarianceSchedule_dyadic_le 0 hq hbase
    simp only [candidateCovarianceScheduleStart, Nat.zero_add] at hh
    calc
      _ ≤ (1 / 2 : ℝ) ^ candidateCovarianceScheduleDepth T :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ R / q ^ 2 := hh
      _ ≤ R / q := by gcongr; nlinarith
  have hhigh : 2 / (M : ℝ) ≤ 2 / q := by gcongr; nlinarith
  have hbracket :
      8 * (1 / 2 : ℝ) ^ (candidateCovarianceScheduleDepth T + 1) + 2 / (M : ℝ) +
        2 * Real.pi * (candidateCovarianceFrequencyDeletionBudget C q start N (N / 2) (s.erase N) +
          candidateCovarianceTerminalDeletionBudget D q start N) ≤
        (8 * R + 2 + 2 * Real.pi * P) * θ ^ 4 / q := by
    change candidateCovarianceFrequencyDeletionBudget C q start N (N / 2) (s.erase N) +
      candidateCovarianceTerminalDeletionBudget D q start N ≤ P * θ ^ 4 / q at hdelT
    have hh := mul_le_mul_of_nonneg_left hdelT (by positivity : 0 ≤ 2 * Real.pi)
    have hl : 8 * (R / q) ≤ 8 * R * θ ^ 4 / q := by
      convert div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (show 0 ≤ 8 * R by positivity) hθ4) hq.le using 1 <;> ring
    have hu : 2 / q ≤ 2 * θ ^ 4 / q :=
      div_le_div_of_nonneg_right (by linarith) hq.le
    have hl' := mul_le_mul_of_nonneg_left hlow (by norm_num : (0 : ℝ) ≤ 8)
    calc
      _ ≤ 8 * R * θ ^ 4 / q + 2 * θ ^ 4 / q +
          2 * Real.pi * (P * θ ^ 4 / q) := by linarith
      _ = _ := by ring
  change (∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂mu) ≤ _ at hnum
  apply hnum.trans
  calc
    _ ≤ (Z / (2 * Real.pi)) * ((8 * R + 2 + 2 * Real.pi * P) * θ ^ 4 / q) :=
      mul_le_mul hn hbracket (by
        have hdi := candidate_covarianceFrequencyDeletionBudget_nonneg hC hq1 start N (N / 2)
          (s.erase N)
        have hdt := candidate_covarianceTerminalDeletionBudget_nonneg hD hq1 start N
        positivity) (by positivity)
    _ = _ := by dsimp only [K]; ring

/-- Fixed cylinder conditioning only changes the multiplicative constant
in the actual retained-error estimate. -/
theorem candidate_exists_cylinder_scheduledRetainedError_integral_le :
    ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ (s : Finset ℕ) (η : s → Bool),
      ∃ K > 0, ∀ᶠ T : ℝ in atTop,
        (∫ ω, candidateCovarianceScheduledRetainedError J T ω ∂candidateCylinderLaw s η) ≤
          K * Real.log (Real.log T) ^ 4 / Real.log T := by
  obtain ⟨J₀, hb⟩ := candidate_exists_scheduledRetainedError_integral_le
  refine ⟨J₀, ?_⟩
  intro J hJ s η
  obtain ⟨K, hK, hbound⟩ := hb J hJ
  have hc : 0 < mu.real (candidateCylinder s η) :=
    ENNReal.toReal_pos (mu_candidateCylinder_ne_zero s η) (measure_ne_top _ _)
  refine ⟨(mu.real (candidateCylinder s η))⁻¹ * K, by positivity, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop (0 : ℝ)] with T hT hT0
  have hi : Integrable (candidateCovarianceScheduledRetainedError J T) mu :=
    candidate_integrable_retainedError _ _ _ _ _ _ _ _
  have hn : ∀ ω, 0 ≤ candidateCovarianceScheduledRetainedError J T ω :=
    fun ω => candidate_retainedError_nonneg _ _ _ _ _ _ hT0.le _ ω
  have hh := candidateCylinderLaw_integral_nonneg_le s η hi hn
  apply hh.2.trans
  convert mul_le_mul_of_nonneg_left hT (inv_nonneg.mpr hc.le) using 1 <;> ring

end
end Erdos.Problem1144
