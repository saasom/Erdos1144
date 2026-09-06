import Erdos.Problem1144.HarperLogBallotCertificate
import Erdos.Problem1144.HarperCandidateEnergyTerminalIntegral

open Filter
open scoped Topology

namespace Erdos.Problem1144

/-! The actual economical path with a fixed terminal gap. All multiplicative
constants below are absolute; only the eventual cutoff depends on the fixed
start, gap, and Rankin parameter. -/

/-- Every fixed-gap economical path becomes arbitrarily long. -/
theorem candidate_tendsto_energyGapPathLength_atTop (start gap : ℕ) :
    Tendsto (fun y : ℕ => Problem520.harperEconomicalPathLength y (start + gap) 0)
      atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop
    (Problem520.harperBlockEndpoint (start + gap + k))] with y hy
  have h := Problem520.add_four_le_harperAvailableLogScale_of_blockEndpoint_le hy
  simp only [Problem520.harperEconomicalPathLength, Problem520.harperEconomicalStart,
    Nat.add_zero]
  omega

/-- The inverse path length is bounded by three times the squared critical
scale. The number three comes from the existing `2*n+10` scale estimate. -/
theorem candidate_energyGapPathLength_inv_le_three_criticalScale_sq
    (start gap y : ℕ) (hy : 4 ≤ y)
    (hlarge : Problem520.harperBlockEndpoint (2 * (start + gap) + 20) ≤ y) :
    (1 : ℝ) / (Problem520.harperEconomicalPathLength y (start + gap) 0 : ℝ) ≤
      3 * harperInitialCriticalScale y ^ 2 := by
  let n := Problem520.harperEconomicalPathLength y (start + gap) 0
  have havail : 2 * (start + gap) + 24 ≤ Problem520.harperAvailableLogScale y := by
    have h := Problem520.add_four_le_harperAvailableLogScale_of_blockEndpoint_le hlarge
    omega
  have hn : 10 ≤ n := by
    dsimp only [n, Problem520.harperEconomicalPathLength, Problem520.harperEconomicalStart]
    omega
  have hscale := Problem520.one_add_logLogNat_le_two_mul_economicalPathLength_add_ten
    (y := y) (J := start + gap) (h := 0) (by omega) (by omega)
  change 1 + Problem520.logLogNat y ≤ 2 * (n : ℝ) + 10 at hscale
  have hnR : (10 : ℝ) ≤ n := by exact_mod_cast hn
  have hscaleThree : 1 + Problem520.logLogNat y ≤ 3 * (n : ℝ) := by linarith
  have hL := Problem520.one_add_logLogNat_pos_of_four_le hy
  have hrecip := one_div_le_one_div_of_le hL hscaleThree
  have hnNe : (n : ℝ) ≠ 0 := by linarith
  rw [harperInitialCriticalScale_sq_eq_inv hy]
  change (1 : ℝ) / (n : ℝ) ≤ 3 * (1 + Problem520.logLogNat y)⁻¹
  calc
    _ = 3 * (1 / (3 * (n : ℝ))) := by field_simp
    _ ≤ _ := by simpa only [one_div] using mul_le_mul_of_nonneg_left hrecip (by norm_num : (0 : ℝ) ≤ 3)

/-- Every fixed parameter choice eventually satisfies all literal cutoff,
path, shift, and scale conditions used by the first- and second-moment
energy estimates. No constant in the conclusion depends on those choices. -/
theorem candidate_eventually_energyGapSchedule_geometry
    (start gap : ℕ) (V : ℝ) (hV : 0 ≤ V) :
    ∀ᶠ y : ℕ in atTop,
      let n := Problem520.harperEconomicalPathLength y (start + gap) 0
      4 ≤ y ∧ 0 < n ∧
        Problem520.harperBlockEndpoint (start + n + gap) ≤ y ∧
        y < Problem520.harperBlockEndpoint (start + n + gap + 1) ∧
        (4 : ℝ) ^ gap ≤ (n : ℝ) ^ 3 ∧
        (1 + 4 * V) * Real.log 4 ≤ Real.log (y : ℝ) ∧
        0 ≤ 4 * V / Real.log (y : ℝ) ∧
        4 * V / Real.log (y : ℝ) ≤ 1 ∧
        (1 : ℝ) / (n : ℝ) ≤ 3 * harperInitialCriticalScale y ^ 2 := by
  have hn := candidate_tendsto_energyGapPathLength_atTop start gap
  have hgap := hn.eventually (candidate_eventually_terminalGap_absorbed gap)
  have hlog : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 4,
    eventually_ge_atTop (Problem520.harperBlockEndpoint (start + gap + 1)),
    eventually_ge_atTop (Problem520.harperBlockEndpoint (2 * (start + gap) + 20)),
    hgap, hlog.eventually_ge_atTop ((1 + 4 * V) * Real.log 4),
    hlog.eventually_ge_atTop (4 * V)] with y hy hroomY hlarge hg hl ha
  dsimp only
  have hroom : start + gap + 5 ≤ Problem520.harperAvailableLogScale y := by
    have h := Problem520.add_four_le_harperAvailableLogScale_of_blockEndpoint_le hroomY
    omega
  obtain ⟨hnpos, hlow, hupp⟩ := harperEconomicalPathLength_fixedStart_envelope hroom
  have hlogpos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  refine ⟨hy, hnpos, ?_, ?_, hg, hl, div_nonneg (by positivity) hlogpos.le,
    (div_le_one hlogpos).mpr ha,
    candidate_energyGapPathLength_inv_le_three_criticalScale_sq start gap y hy hlarge⟩
  · convert hlow using 1 <;> congr 1 <;> omega
  · convert hupp using 1 <;> congr 1 <;> omega

end Erdos.Problem1144
