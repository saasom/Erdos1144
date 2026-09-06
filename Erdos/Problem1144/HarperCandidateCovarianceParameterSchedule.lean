import Erdos.Problem1144.HarperCandidateCovarianceTopCutoff
import Erdos.Problem1144.HarperCandidateCovarianceGrowingHeight
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

namespace Erdos.Problem1144
noncomputable section

/-- Central-band depth rounded with the same exact endpoint convention as
the terminal Euler cutoff. -/
def candidateCovarianceScheduleDepth (T : ℝ) : ℕ :=
  candidateEulerTopIndex (Real.log T ^ 2)

/-- The fixed analytic offset is added explicitly to the band depth. -/
def candidateCovarianceScheduleStart (J : ℕ) (T : ℝ) : ℕ :=
  J + candidateCovarianceScheduleDepth T

def candidateCovarianceScheduleLength (J : ℕ) (T : ℝ) : ℕ :=
  candidateEulerTopIndex T - candidateCovarianceScheduleStart J T

/-- Absolute index of the inclusive strong screen, halfway along the path. -/
def candidateCovarianceScheduleStrong (J : ℕ) (T : ℝ) : ℕ :=
  candidateCovarianceScheduleStart J T + candidateCovarianceScheduleLength J T / 2

def candidateCovarianceScheduleLowerHeight (T : ℝ) : ℝ :=
  (1 / 2 : ℝ) ^ (candidateCovarianceScheduleDepth T + 1)

/-- Natural-valued height, usable directly by the common mesh event. -/
def candidateCovarianceScheduleHeight (T : ℝ) : ℕ := ⌈Real.log T ^ 2⌉₊

def candidateCovarianceScheduleWidth (T : ℝ) : ℝ := T ^ (-(3 : ℝ) / 4)

/-- The moment order is determined by the actual time, without a separate
truncation parameter. -/
def candidateCovarianceScheduleOrder (T : ℝ) : ℕ :=
  ⌊Real.log T / (4000 * Real.log (Real.log T))⌋₊

theorem candidate_schedule_log_block_add (a b : ℕ) :
    Real.log (Problem520.harperBlockEndpoint (a + b) : ℝ) =
      (2 : ℝ) ^ a * Real.log (Problem520.harperBlockEndpoint b : ℝ) := by
  rw [Problem520.log_harperBlockEndpoint_eq,
    Problem520.log_harperBlockEndpoint_eq, pow_add]
  ring

/-- The logarithmic initial cutoff has the intended squared-log scale,
with its fixed analytic offset visible in both constants. -/
theorem candidate_covarianceSchedule_start_log_bounds (J : ℕ) {T : ℝ}
    (hT : Real.log (Problem520.harperBlockEndpoint 0 : ℝ) ≤ Real.log T ^ 2) :
    (2 : ℝ) ^ J * (Real.log T ^ 2 / 2) <
        Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ) ∧
      Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStart J T) : ℝ) ≤
        (2 : ℝ) ^ J * Real.log T ^ 2 := by
  obtain ⟨hlo, hhi⟩ := candidateEulerTopCutoff_log_bounds hT
  rw [candidateCovarianceScheduleStart, candidate_schedule_log_block_add]
  exact ⟨mul_lt_mul_of_pos_left hlo (by positivity),
    mul_le_mul_of_nonneg_left hhi (by positivity)⟩

theorem candidate_covarianceSchedule_height_bounds (T : ℝ) :
    Real.log T ^ 2 ≤ (candidateCovarianceScheduleHeight T : ℝ) ∧
      (candidateCovarianceScheduleHeight T : ℝ) < Real.log T ^ 2 + 1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (sq_nonneg _)⟩

theorem candidate_covarianceSchedule_lowerHeight_pos (T : ℝ) :
    0 < candidateCovarianceScheduleLowerHeight T := by
  unfold candidateCovarianceScheduleLowerHeight
  positivity

/-- The central annulus and initial cutoff share one rounded depth, so
the reciprocal lower height is bounded by the same squared logarithm. -/
theorem candidate_covarianceSchedule_lowerHeight_inv_le {T : ℝ}
    (hT : Real.log (Problem520.harperBlockEndpoint 0 : ℝ) ≤ Real.log T ^ 2) :
    1 / candidateCovarianceScheduleLowerHeight T ≤ 2 * Real.log T ^ 2 := by
  have hbase := Problem520.one_le_log_harperBlockEndpoint 0
  have hdepth := (candidateEulerTopCutoff_log_bounds hT).2
  have heq : Real.log (candidateEulerTopCutoff (Real.log T ^ 2) : ℝ) =
      (2 : ℝ) ^ candidateCovarianceScheduleDepth T *
        Real.log (Problem520.harperBlockEndpoint 0 : ℝ) := by
    simpa only [Nat.add_zero] using
      candidate_schedule_log_block_add (candidateCovarianceScheduleDepth T) 0
  rw [heq] at hdepth
  have hp : (2 : ℝ) ^ candidateCovarianceScheduleDepth T ≤ Real.log T ^ 2 :=
    (le_mul_of_one_le_right (by positivity) hbase).trans hdepth
  unfold candidateCovarianceScheduleLowerHeight
  simp only [one_div, inv_pow, inv_inv, pow_succ]
  simp only [mul_inv_rev, inv_inv]
  linarith

/-- A block whose logarithm fits below the time lies before the selected
complete Euler endpoint. -/
theorem candidate_blockIndex_le_top_of_log_le {j : ℕ} {T : ℝ}
    (hT : Real.log (Problem520.harperBlockEndpoint 0 : ℝ) ≤ T)
    (hj : Real.log (Problem520.harperBlockEndpoint j : ℝ) ≤ T) :
    j ≤ candidateEulerTopIndex T := by
  by_contra h
  have hnext : candidateEulerTopIndex T + 1 ≤ j := by omega
  have hm : Real.log (Problem520.harperBlockEndpoint (candidateEulerTopIndex T + 1) : ℝ) ≤
      Real.log (Problem520.harperBlockEndpoint j : ℝ) := Real.log_le_log
    (by exact_mod_cast Problem520.harperBlockEndpoint_pos (candidateEulerTopIndex T + 1))
    (by exact_mod_cast Problem520.monotone_harperBlockEndpoint hnext)
  have hb := (candidateEulerTopCutoff_log_bounds hT).1
  have he : Real.log (Problem520.harperBlockEndpoint (candidateEulerTopIndex T + 1) : ℝ) =
      2 * Real.log (candidateEulerTopCutoff T : ℝ) := by
    rw [Nat.add_comm]
    simpa only [pow_one] using candidate_schedule_log_block_add 1 (candidateEulerTopIndex T)
  rw [he] at hm
  linarith

/-- Every fixed extra number of blocks eventually fits between the
scheduled start and the actual terminal cutoff. -/
theorem candidate_eventually_covarianceSchedule_room (J r : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      candidateCovarianceScheduleStart J T + r ≤ candidateEulerTopIndex T := by
  have hq : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  have hsmall := (Real.isLittleO_pow_log_id_atTop (n := 2)).tendsto_div_nhds_zero.const_mul
    ((2 : ℝ) ^ r * (2 : ℝ) ^ J)
  filter_upwards [eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    eventually_gt_atTop (0 : ℝ),
    hq.eventually_ge_atTop (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)),
    (tendsto_order.mp hsmall).2 1 (by norm_num)] with T hT hT0 hqT hs
  apply candidate_blockIndex_le_top_of_log_le hT
  have hb := (candidate_covarianceSchedule_start_log_bounds J hqT).2
  have he : Real.log (Problem520.harperBlockEndpoint
      (candidateCovarianceScheduleStart J T + r) : ℝ) =
      (2 : ℝ) ^ r * Real.log (Problem520.harperBlockEndpoint
        (candidateCovarianceScheduleStart J T) : ℝ) := by
    rw [Nat.add_comm]
    exact candidate_schedule_log_block_add _ _
  rw [he]
  have hs' : (2 : ℝ) ^ r * (2 : ℝ) ^ J * Real.log T ^ 2 ≤ T := by
    change (2 : ℝ) ^ r * (2 : ℝ) ^ J * (Real.log T ^ 2 / T) < 1 at hs
    have := (div_lt_iff₀ hT0).mp (show
      ((2 : ℝ) ^ r * (2 : ℝ) ^ J * Real.log T ^ 2) / T < 1 by simpa [mul_div_assoc] using hs)
    linarith
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans (by nlinarith [hs'])

theorem candidate_covarianceSchedule_length_tendsto (J : ℕ) :
    Tendsto (candidateCovarianceScheduleLength J) atTop atTop := by
  apply tendsto_atTop.2
  intro r
  filter_upwards [candidate_eventually_covarianceSchedule_room J r] with T hT
  unfold candidateCovarianceScheduleLength
  omega

/-- The midpoint index gives the square-root product scale for the strong
gap threshold, including its predecessor in the actual definition. -/
theorem candidate_covarianceSchedule_strong_log_le_sqrt (J : ℕ) (T : ℝ)
    (hST : candidateCovarianceScheduleStart J T ≤ candidateEulerTopIndex T) :
    Real.log (Problem520.harperBlockEndpoint (candidateCovarianceScheduleStrong J T - 1) : ℝ) ≤
      Real.sqrt (Real.log (Problem520.harperBlockEndpoint
        (candidateCovarianceScheduleStart J T) : ℝ) * Real.log (candidateEulerTopCutoff T : ℝ)) := by
  let s := candidateCovarianceScheduleStart J T
  let t := candidateEulerTopIndex T
  let a := candidateCovarianceScheduleStrong J T - 1
  have ha : 2 * a ≤ s + t := by
    dsimp only [a, s, t, candidateCovarianceScheduleStrong, candidateCovarianceScheduleLength]
    omega
  have hp : (2 : ℝ) ^ (2 * a) ≤ (2 : ℝ) ^ (s + t) :=
    pow_le_pow_right₀ (by norm_num) ha
  have hb : Real.log (Problem520.harperBlockEndpoint a : ℝ) ^ 2 ≤
      Real.log (Problem520.harperBlockEndpoint s : ℝ) *
        Real.log (Problem520.harperBlockEndpoint t : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left hp
      (sq_nonneg (Real.log (Problem520.harperBlockEndpoint 0 : ℝ)))
    rw [Nat.mul_comm 2 a, pow_mul, pow_add] at hc
    have hs := candidate_schedule_log_block_add s 0
    have ht := candidate_schedule_log_block_add t 0
    have haa := candidate_schedule_log_block_add a 0
    simp only [Nat.add_zero] at hs ht haa
    rw [hs, ht, haa]
    convert hc using 1 <;> ring
  have hl : 0 ≤ Real.log (Problem520.harperBlockEndpoint a : ℝ) :=
    zero_le_one.trans (Problem520.one_le_log_harperBlockEndpoint a)
  simpa only [Real.sqrt_sq hl] using Real.sqrt_le_sqrt hb

end
end Erdos.Problem1144
