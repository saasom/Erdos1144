import Erdos.Problem1144.HarperProcess
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Set

namespace Erdos.Problem1144

/-!
# The stationary candidate's literal log-time process

The real-time process uses the exact cutoff `floor (exp t)` and the paper's
normalization `exp (t / 2)`, with value zero at negative times. Its relation
to the natural-cutoff normalization involves a deterministic factor in
`[0,1]`; this preserves every nonnegative upper envelope.
-/

/-- The complete-model process in the candidate's logarithmic time. -/
noncomputable def harperCandidateLogProcess (omega : Omega) (t : ℝ) : ℝ :=
  if 0 ≤ t then S omega ⌊Real.exp t⌋₊ / Real.exp (t / 2) else 0

/-- The deterministic factor converting natural-cutoff normalization to the
candidate's exponential normalization. -/
noncomputable def harperCandidateLogNormalization (t : ℝ) : ℝ :=
  Real.sqrt (⌊Real.exp t⌋₊ : ℝ) / Real.exp (t / 2)

/-- The literal log-time process is jointly measurable in the signs and time. -/
theorem measurable_harperCandidateLogProcess :
    Measurable (fun z : Omega × ℝ ↦ harperCandidateLogProcess z.1 z.2) := by
  have hS : Measurable (fun z : Omega × ℕ ↦ S z.1 z.2) :=
    measurable_from_prod_countable_left measurable_S
  have hnum : Measurable (fun z : Omega × ℝ ↦ S z.1 ⌊Real.exp z.2⌋₊) :=
    hS.comp (measurable_fst.prodMk (Real.measurable_exp.comp measurable_snd).nat_floor)
  exact (hnum.div (Real.measurable_exp.comp (measurable_snd.div_const 2))).ite
    (measurableSet_le measurable_const measurable_snd) measurable_const

/-- The normalization factor is measurable in logarithmic time. -/
theorem measurable_harperCandidateLogNormalization :
    Measurable harperCandidateLogNormalization := by
  unfold harperCandidateLogNormalization
  fun_prop

/-- The integer cutoff is positive at every nonnegative logarithmic time. -/
theorem harperCandidateLogCutoff_pos {t : ℝ} (ht : 0 ≤ t) :
    0 < ⌊Real.exp t⌋₊ :=
  Nat.floor_pos.mpr (Real.one_le_exp_iff.mpr ht)

/-- The exact normalizing factor always lies between zero and one. -/
theorem harperCandidateLogNormalization_mem_Icc (t : ℝ) :
    harperCandidateLogNormalization t ∈ Icc 0 1 := by
  constructor
  · unfold harperCandidateLogNormalization
    positivity
  · unfold harperCandidateLogNormalization
    apply (div_le_one (Real.exp_pos _)).2
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt (Nat.floor_le (Real.exp_pos t).le)

/-- Exact conversion between the candidate and natural-cutoff processes. -/
theorem harperCandidateLogProcess_eq_cutoffNormSum_mul
    (omega : Omega) {t : ℝ} (ht : 0 ≤ t) :
    harperCandidateLogProcess omega t =
      cutoffNormSum omega ⌊Real.exp t⌋₊ * harperCandidateLogNormalization t := by
  have hcut : (⌊Real.exp t⌋₊ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (harperCandidateLogCutoff_pos ht))
  have hsqrt : Real.sqrt (⌊Real.exp t⌋₊ : ℝ) ≠ 0 := by
    exact Real.sqrt_ne_zero'.mpr (by positivity)
  simp only [harperCandidateLogProcess, if_pos ht, cutoffNormSum,
    harperCandidateLogNormalization]
  field_simp

/-- Every nonnegative natural-cutoff upper envelope also bounds the entire
real log-time process, including negative times. -/
theorem harperCandidateLogProcess_le_of_cutoffNormSum_le
    (omega : Omega) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ N : ℕ, cutoffNormSum omega N ≤ M) (t : ℝ) :
    harperCandidateLogProcess omega t ≤ M := by
  by_cases ht : 0 ≤ t
  · rw [harperCandidateLogProcess_eq_cutoffNormSum_mul omega ht]
    have hfactor := harperCandidateLogNormalization_mem_Icc t
    calc
      _ ≤ M * harperCandidateLogNormalization t :=
        mul_le_mul_of_nonneg_right (hbound _) hfactor.1
      _ ≤ M := mul_le_of_le_one_right hM hfactor.2
  · simpa [harperCandidateLogProcess, ht] using hM

/-- The shifted natural endpoint envelope used in the final Erdős target
implies the corresponding real log-time envelope. -/
theorem harperCandidateLogProcess_le_of_normSum_le
    (omega : Omega) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ N : ℕ, normSum omega N ≤ M) (t : ℝ) :
    harperCandidateLogProcess omega t ≤ M := by
  apply harperCandidateLogProcess_le_of_cutoffNormSum_le omega hM _ t
  intro N
  cases N with
  | zero => simpa [cutoffNormSum] using hM
  | succ N => exact hbound N

/-- The exact complete-model fresh-prime decomposition at the real log-time
cutoff, with the candidate's exponential denominator on both terms. -/
theorem harperCandidateLogProcess_eq_smooth_add_fresh
    (omega : Omega) {X : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hcut : ⌊Real.exp t⌋₊ < X ^ 2) :
    harperCandidateLogProcess omega t =
      smoothSum omega X ⌊Real.exp t⌋₊ / Real.exp (t / 2) +
        largePrimeContribution omega X ⌊Real.exp t⌋₊ / Real.exp (t / 2) := by
  rw [harperCandidateLogProcess, if_pos ht,
    S_eq_smoothSum_add_largePrimeContribution omega hcut, add_div]

end Erdos.Problem1144
