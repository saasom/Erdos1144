import Erdos.Problem1144.HarperCandidateLogProcess
import Erdos.Problem1144.SquareConvolution
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- The squarefree process appearing in the candidate's stationary kernel,
with the exact floor cutoff and value zero at negative logarithmic times. -/
noncomputable def harperCandidateSquarefreeLogProcess (ω : Omega) (t : ℝ) : ℝ :=
  if 0 ≤ t then GSquarefree ω ⌊Real.exp t⌋₊ / Real.exp (t / 2) else 0

theorem measurable_harperCandidateSquarefreeLogProcess :
    Measurable fun z : Omega × ℝ => harperCandidateSquarefreeLogProcess z.1 z.2 := by
  have hG : Measurable fun z : Omega × ℕ => GSquarefree z.1 z.2 :=
    measurable_from_prod_countable_left measurable_GSquarefree
  exact ((hG.comp (measurable_fst.prodMk
    (Real.measurable_exp.comp measurable_snd).nat_floor)).div
    (Real.measurable_exp.comp (measurable_snd.div_const 2))).ite
    (measurableSet_le measurable_const measurable_snd) measurable_const

/-- The zero extension is already encoded by the natural floor when `t<0`. -/
theorem harperCandidateSquarefreeLogProcess_eq_quotient (ω : Omega) (t : ℝ) :
    harperCandidateSquarefreeLogProcess ω t =
      GSquarefree ω ⌊Real.exp t⌋₊ / Real.exp (t / 2) := by
  unfold harperCandidateSquarefreeLogProcess
  split_ifs with ht
  · rfl
  · have hf : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr
      (by simpa using Real.exp_lt_one_iff.mpr (lt_of_not_ge ht))
    simp [hf, GSquarefree]

/-- The same floor convention removes the apparent negative-time branch of
 the complete process. -/
theorem harperCandidateLogProcess_eq_quotient (ω : Omega) (t : ℝ) :
    harperCandidateLogProcess ω t = S ω ⌊Real.exp t⌋₊ / Real.exp (t / 2) := by
  unfold harperCandidateLogProcess
  split_ifs with ht
  · rfl
  · have hf : ⌊Real.exp t⌋₊ = 0 := Nat.floor_eq_zero.mpr
      (by simpa using Real.exp_lt_one_iff.mpr (lt_of_not_ge ht))
    simp [hf, S]

/-- Dividing the real cutoff by a square is exactly a logarithmic translation. -/
theorem candidate_exp_sub_two_log {r : ℕ} (hr : 0 < r) (t : ℝ) :
    Real.exp (t - 2 * Real.log r) = Real.exp t / (r : ℝ) ^ 2 := by
  rw [Real.exp_sub, show 2 * Real.log (r : ℝ) = Real.log ((r : ℝ) ^ 2) by
    rw [Real.log_pow]; norm_num,
    Real.exp_log (pow_pos (Nat.cast_pos.mpr hr) 2)]

theorem candidate_exp_half_sub_two_log {r : ℕ} (hr : 0 < r) (t : ℝ) :
    Real.exp ((t - 2 * Real.log r) / 2) = Real.exp (t / 2) / r := by
  rw [show (t - 2 * Real.log (r : ℝ)) / 2 = t / 2 - Real.log r by ring,
    Real.exp_sub, Real.exp_log (Nat.cast_pos.mpr hr)]

/-- Exact arithmetic/logarithmic cutoff conversion for every positive square
multiplier. No asymptotic floor estimate is involved. -/
theorem candidate_floor_exp_sub_two_log {r : ℕ} (hr : 0 < r) (t : ℝ) :
    ⌊Real.exp (t - 2 * Real.log r)⌋₊ = ⌊Real.exp t⌋₊ / r ^ 2 := by
  rw [candidate_exp_sub_two_log hr, ← Nat.cast_pow, Nat.floor_div_natCast]

/-- One term of square convolution after normalization. -/
theorem candidate_squarefree_log_translate_term
    (ω : Omega) {r : ℕ} (hr : 0 < r) (t : ℝ) :
    (1 / (r : ℝ)) * harperCandidateSquarefreeLogProcess ω (t - 2 * Real.log r) =
      GSquarefree ω (⌊Real.exp t⌋₊ / r ^ 2) / Real.exp (t / 2) := by
  rw [harperCandidateSquarefreeLogProcess_eq_quotient,
    candidate_floor_exp_sub_two_log hr, candidate_exp_half_sub_two_log hr]
  have hrR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  field_simp

/-- Literal finite log-time square convolution of the complete model with
its squarefree model, valid at every real time and every sign assignment. -/
theorem harperCandidateLogProcess_eq_finite_squarefree_translates (ω : Omega) (t : ℝ) :
    harperCandidateLogProcess ω t =
      ∑ r ∈ Finset.Icc 1 ⌊Real.exp t⌋₊,
        (1 / (r : ℝ)) * harperCandidateSquarefreeLogProcess ω (t - 2 * Real.log r) := by
  rw [harperCandidateLogProcess_eq_quotient, S_eq_squareSmoothing, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  exact (candidate_squarefree_log_translate_term ω (Finset.mem_Icc.mp hr).1 t).symm

/-- The logarithmic square-convolution summand is finitely supported at each
time. This justifies its infinite-sum notation without a convergence premise. -/
theorem candidate_squarefree_log_translate_vanishes
    (ω : Omega) (t : ℝ) {r : ℕ} (hr : r ∉ Finset.Icc 1 ⌊Real.exp t⌋₊) :
    (1 / (r : ℝ)) * harperCandidateSquarefreeLogProcess ω (t - 2 * Real.log r) = 0 := by
  by_cases hr0 : r = 0
  · simp [hr0]
  · have hrpos := Nat.pos_of_ne_zero hr0
    rw [candidate_squarefree_log_translate_term ω hrpos t]
    have hrlarge : ⌊Real.exp t⌋₊ < r := by
      by_contra h
      exact hr (Finset.mem_Icc.mpr ⟨hrpos, le_of_not_gt h⟩)
    have hr2 : ⌊Real.exp t⌋₊ < r ^ 2 :=
      hrlarge.trans_le (by simpa [pow_two] using Nat.le_mul_self r)
    simp [Nat.div_eq_of_lt hr2, GSquarefree]

/-- The complete normalized log process is the exact convolution by square
translations. The natural-index zero term vanishes by its coefficient. -/
theorem harperCandidateLogProcess_eq_tsum_squarefree_translates (ω : Omega) (t : ℝ) :
    harperCandidateLogProcess ω t =
      ∑' r : ℕ, (1 / (r : ℝ)) *
        harperCandidateSquarefreeLogProcess ω (t - 2 * Real.log r) := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp t⌋₊)
    (fun r hr => candidate_squarefree_log_translate_vanishes ω t hr)]
  exact harperCandidateLogProcess_eq_finite_squarefree_translates ω t

/-- The square-translation coefficient after exponential damping. -/
noncomputable def candidateSquareTranslationWeight (σ : ℝ) (r : ℕ) : ℝ :=
  (1 / (r : ℝ)) * Real.exp (-2 * σ * Real.log r)

theorem candidateSquareTranslationWeight_eq_rpow {σ : ℝ} (hσ : 0 < σ) (r : ℕ) :
    candidateSquareTranslationWeight σ r = (r : ℝ) ^ (-(1 + 2 * σ)) := by
  by_cases hr : r = 0
  · subst r
    simp only [candidateSquareTranslationWeight, Nat.cast_zero, div_zero, zero_mul]
    rw [Real.zero_rpow (by linarith : -(1 + 2 * σ) ≠ 0)]
  · have hrpos : (0 : ℝ) < r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hr)
    unfold candidateSquareTranslationWeight
    rw [Real.rpow_def_of_pos hrpos]
    have he : 1 / (r : ℝ) = Real.exp (-Real.log r) := by
      rw [Real.exp_neg, Real.exp_log hrpos]
      simp [one_div]
    rw [he, ← Real.exp_add]
    congr 1
    ring

/-- For every positive damping exponent the exact translation weights are
absolutely summable. -/
theorem summable_candidateSquareTranslationWeight {σ : ℝ} (hσ : 0 < σ) :
    Summable (candidateSquareTranslationWeight σ) := by
  rw [show candidateSquareTranslationWeight σ =
    (fun r : ℕ => (r : ℝ) ^ (-(1 + 2 * σ))) from
      funext (candidateSquareTranslationWeight_eq_rpow hσ)]
  exact Real.summable_nat_rpow.mpr (by linarith)

/-- Damping turns the square convolution into a summable weighted translation
operator. This is the real-variable identity behind the zeta multiplier. -/
theorem harperCandidateLogProcess_damped_eq_tsum_translates
    (ω : Omega) (σ t : ℝ) :
    Real.exp (-σ * t) * harperCandidateLogProcess ω t =
      ∑' r : ℕ, candidateSquareTranslationWeight σ r *
        (Real.exp (-σ * (t - 2 * Real.log r)) *
          harperCandidateSquarefreeLogProcess ω (t - 2 * Real.log r)) := by
  rw [harperCandidateLogProcess_eq_tsum_squarefree_translates, ← tsum_mul_left]
  apply tsum_congr
  intro r
  have he : Real.exp (-2 * σ * Real.log r) *
      Real.exp (-σ * (t - 2 * Real.log r)) = Real.exp (-σ * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold candidateSquareTranslationWeight
  calc
    _ = (1 / (r : ℝ)) * Real.exp (-σ * t) *
        harperCandidateSquarefreeLogProcess ω (t - 2 * Real.log r) := by ring
    _ = _ := by rw [← he]; ring

end Erdos.Problem1144

#print axioms Erdos.Problem1144.harperCandidateLogProcess_eq_finite_squarefree_translates
#print axioms Erdos.Problem1144.harperCandidateLogProcess_eq_tsum_squarefree_translates
#print axioms Erdos.Problem1144.summable_candidateSquareTranslationWeight
#print axioms Erdos.Problem1144.harperCandidateLogProcess_damped_eq_tsum_translates
