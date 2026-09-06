import Erdos.Problem520.HarperScheduledSummableErrors

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

namespace Erdos.Problem1144
open Erdos.Problem520
noncomputable section

private theorem exists_log_blockEndpoint_gt (T : ℝ) :
    ∃ j : ℕ, T < Real.log (harperBlockEndpoint j : ℝ) := by
  have h := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp strictMono_harperBlockEndpoint.tendsto_atTop)
  exact (h.eventually (eventually_gt_atTop T)).exists

/-- The last complete Euler block below the exponential time scale. Below the
initial block, the index is zero by natural subtraction. -/
def candidateEulerTopIndex (T : ℝ) : ℕ :=
  Nat.find (exists_log_blockEndpoint_gt T) - 1

/-- Exact endpoint used to remove a full microscopic prefix. -/
def candidateEulerTopCutoff (T : ℝ) : ℕ :=
  harperBlockEndpoint (candidateEulerTopIndex T)

/-- Exact squaring of consecutive endpoints places the logarithm of the
complete cutoff between half the time and the time itself. -/
theorem candidateEulerTopCutoff_log_bounds {T : ℝ}
    (hT : Real.log (harperBlockEndpoint 0 : ℝ) ≤ T) :
    T / 2 < Real.log (candidateEulerTopCutoff T : ℝ) ∧
      Real.log (candidateEulerTopCutoff T : ℝ) ≤ T := by
  let n := Nat.find (exists_log_blockEndpoint_gt T)
  have hn : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    have hf := Nat.find_spec (exists_log_blockEndpoint_gt T)
    change T < Real.log (harperBlockEndpoint n : ℝ) at hf
    rw [he] at hf
    linarith
  have hmin : Real.log (harperBlockEndpoint (n - 1) : ℝ) ≤ T :=
    le_of_not_gt (Nat.find_min (exists_log_blockEndpoint_gt T) (by omega : n - 1 < n))
  have hmax := Nat.find_spec (exists_log_blockEndpoint_gt T)
  change T < Real.log (harperBlockEndpoint n : ℝ) at hmax
  have he : n = (n - 1) + 1 := by omega
  rw [he, log_harperBlockEndpoint_eq, pow_succ] at hmax
  change T / 2 < Real.log (harperBlockEndpoint (n - 1) : ℝ) ∧
    Real.log (harperBlockEndpoint (n - 1) : ℝ) ≤ T
  refine ⟨?_, hmin⟩
  rw [log_harperBlockEndpoint_eq]
  nlinarith

/-- Integer cutoff bounds used by the exact Fourier comparison. -/
theorem candidateEulerTopCutoff_exp_bounds {T : ℝ}
    (hT : Real.log (harperBlockEndpoint 0 : ℝ) ≤ T) :
    ⌊Real.exp (T / 2)⌋₊ ≤ candidateEulerTopCutoff T ∧
      candidateEulerTopCutoff T ≤ ⌊Real.exp T⌋₊ := by
  have hy : (0 : ℝ) < candidateEulerTopCutoff T := by
    exact_mod_cast harperBlockEndpoint_pos (candidateEulerTopIndex T)
  obtain ⟨hlo, hhi⟩ := candidateEulerTopCutoff_log_bounds hT
  constructor
  · apply Nat.floor_le_of_le
    exact (Real.exp_le_exp.mpr hlo.le).trans_eq (Real.exp_log hy)
  · apply (Nat.le_floor_iff (Real.exp_pos T).le).mpr
    exact (Real.exp_log hy).symm.trans_le (Real.exp_le_exp.mpr hhi)

/-- All coefficient prefixes needed in the scheduled window fit in the
complete endpoint, with room up to `3T/2`. -/
theorem candidateEulerTopCutoff_covers_prefix {T u : ℝ}
    (hT : Real.log (harperBlockEndpoint 0 : ℝ) ≤ T) (hu : u ≤ 3 / 2 * T) :
    ⌊Real.exp (u - T)⌋₊ ≤ candidateEulerTopCutoff T :=
  (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith : u - T ≤ T / 2))).trans
    (candidateEulerTopCutoff_exp_bounds hT).1

end
end Erdos.Problem1144
