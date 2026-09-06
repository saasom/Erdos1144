import Erdos.Problem1144.Statistics
import Mathlib.Data.Real.Sqrt

open MeasureTheory Filter

namespace Erdos
namespace Problem1144

/-- Normalized partial sum used in the statement of Erdős #1144.

The shift keeps the denominator away from zero while preserving the original
`N → ∞` assertion.
-/
noncomputable def normSum (omega : Omega) (N : ℕ) : ℝ :=
  S omega (N + 1) / Real.sqrt (((N + 1 : ℕ) : ℝ))

/-- For each cutoff, the normalized sum in the final statement is measurable. -/
theorem measurable_normSum (N : ℕ) :
    Measurable fun omega : Omega => normSum omega N := by
  unfold normSum
  exact (measurable_S (N + 1)).div_const _

/-- Deterministic envelope for every normalized partial sum. -/
theorem abs_normSum_le_sqrt (omega : Omega) (N : ℕ) :
    |normSum omega N| ≤ Real.sqrt (((N + 1 : ℕ) : ℝ)) := by
  rw [normSum, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqrt_pos : 0 < Real.sqrt (((N + 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos_of_pos (by positivity)
  rw [div_le_iff₀ hsqrt_pos]
  have hS := abs_S_le omega (N + 1)
  rw [← pow_two, Real.sq_sqrt (by positivity)]
  exact hS

/-- Positive unboundedness along the square subsequence. -/
def SquareTarget : Prop :=
  ∀ᵐ omega ∂mu, ∀ A : ℝ, ∃ᶠ r : ℕ in atTop, A ≤ Y omega r

/-- Erdős #1144 target, stated with `Frequently` instead of extended limsup. -/
def Erdos1144 : Prop :=
  ∀ᵐ omega ∂mu, ∀ A : ℝ, ∃ᶠ N : ℕ in atTop, A ≤ normSum omega N

/-- The square-root identity needed to pass from the square subsequence to all `N`. -/
theorem sqrt_sq_nat_succ (r : ℕ) :
    Real.sqrt ((((r + 1) ^ 2 : ℕ) : ℝ)) = (((r + 1 : ℕ) : ℝ)) := by
  rw [Nat.cast_pow]
  exact Real.sqrt_sq (by positivity)

/-- Pointwise square-subsequence reduction.

This pushes the frequent set of `r` through `N = (r + 1)^2 - 1` and uses
`sqrt_sq_nat_succ`.
-/
theorem erdos1144_of_squareTarget_pointwise
  (omega : Omega) :
  (∀ A : ℝ, ∃ᶠ r : ℕ in atTop, A ≤ Y omega r) →
    ∀ A : ℝ, ∃ᶠ N : ℕ in atTop, A ≤ normSum omega N := by
  intro h A
  rw [Filter.Frequently]
  intro hbad
  have hsubseq_tendsto :
      Tendsto (fun r : ℕ => (r + 1) ^ 2 - 1) atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop ?_ tendsto_id
    filter_upwards [] with r
    have hle : r + 1 ≤ (r + 1) ^ 2 :=
      Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) (r + 1)
    exact Nat.le_sub_of_add_le hle
  have hbad_subseq : ∀ᶠ r : ℕ in atTop,
      ¬ A ≤ normSum omega ((r + 1) ^ 2 - 1) :=
    hsubseq_tendsto.eventually hbad
  have hbad_square : ∀ᶠ r : ℕ in atTop, ¬ A ≤ Y omega r := by
    filter_upwards [hbad_subseq] with r hr
    have hsq_pos : 0 < (r + 1) ^ 2 := by positivity
    have hsucc :
        ((r + 1) ^ 2 - 1) + 1 = (r + 1) ^ 2 :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hsq_pos)
    have hnorm :
        normSum omega ((r + 1) ^ 2 - 1) = Y omega r := by
      rw [normSum, Y, hsucc, sqrt_sq_nat_succ]
    simpa [hnorm] using hr
  have hAfreq := h A
  rw [Filter.Frequently] at hAfreq
  exact hAfreq hbad_square

/-- Square-subsequence positive unboundedness implies the original target. -/
theorem erdos1144_of_squareTarget (h : SquareTarget) : Erdos1144 :=
  h.mono fun omega homega => erdos1144_of_squareTarget_pointwise omega homega

end Problem1144
end Erdos
