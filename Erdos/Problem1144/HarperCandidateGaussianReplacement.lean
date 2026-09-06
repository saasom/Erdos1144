import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Probability.Distributions.Gaussian.Real
import Erdos.Problem1144.HarperProcess
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- Global third-derivative control gives the exact cubic error after
subtracting the quadratic Taylor polynomial, for either sign of the input. -/
theorem candidate_cubic_taylor_bound
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {C : ℝ}
    (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (x : ℝ) :
    |f x - (f 0 + deriv f 0 * x + (iteratedDeriv 2 f 0 / 2) * x ^ 2)| ≤
      C * |x| ^ 3 / 6 := by
  by_cases hx : x = 0
  · simp [hx]
  have hx' : (0 : ℝ) ≠ x := Ne.symm hx
  have huniq : UniqueDiffOn ℝ (uIcc (0 : ℝ) x) :=
    uniqueDiffOn_Icc (by simpa only [min_lt_max] using hx')
  obtain ⟨z, _, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hx' hf.contDiffOn
  have hpoly : taylorWithinEval f 2 (uIcc (0 : ℝ) x) 0 x =
      f 0 + deriv f 0 * x + (iteratedDeriv 2 f 0 / 2) * x ^ 2 := by
    rw [taylorWithinEval_succ f 1, taylorWithinEval_succ f 0, taylor_within_zero_eval]
    norm_num only [Nat.reduceAdd]
    rw [iteratedDerivWithin_eq_iteratedDeriv huniq
        (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).contDiffAt (left_mem_uIcc),
      iteratedDerivWithin_eq_iteratedDeriv huniq
        (hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contDiffAt (left_mem_uIcc)]
    simp only [iteratedDeriv_one, smul_eq_mul]
    norm_num
    ring
  rw [hpoly] at hz
  rw [hz, abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hC z) (pow_nonneg (abs_nonneg x) 3)) (by norm_num)

/-- The absolute third moment appearing in the one-coordinate replacement
is a finite universal constant. -/
theorem candidate_integrable_gaussian_abs_cube :
    Integrable (fun x : ℝ => |x| ^ 3) (gaussianReal 0 1) := by
  have h : MemLp (id : ℝ → ℝ) (3 : ENNReal) (gaussianReal 0 1) :=
    memLp_id_gaussianReal (3 : NNReal)
  simpa only [Real.norm_eq_abs, id_eq] using h.integrable_norm_pow (by norm_num : 3 ≠ 0)

/-- One actual Lindeberg replacement: a fair sign and a standard normal
have matching constant, linear, and quadratic Taylor contributions. Only
their cubic errors survive. -/
theorem candidate_rademacher_gaussian_smooth_replacement
    {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {C D : ℝ}
    (hC : ∀ x, |iteratedDeriv 3 f x| ≤ C) (hD : ∀ x, |f x| ≤ D) :
    |(f 1 + f (-1)) / 2 - ∫ x, f x ∂gaussianReal 0 1| ≤
      (C / 6) * (1 + ∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 1) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let P : ℝ → ℝ := fun x => f 0 + deriv f 0 * x + (iteratedDeriv 2 f 0 / 2) * x ^ 2
  have hfi : Integrable f γ := Integrable.of_bound hf.continuous.measurable.aestronglyMeasurable
    D (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hD x)
  have hxi : Integrable (fun x : ℝ => x) γ := by
    have h : MemLp (id : ℝ → ℝ) 1 γ := memLp_id_gaussianReal (1 : NNReal)
    exact h.integrable (by norm_num)
  have hx2i : Integrable (fun x : ℝ => x ^ 2) γ := by
    exact (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mp
      (memLp_id_gaussianReal (2 : NNReal))
  have hPi : Integrable P γ :=
    ((integrable_const _).add (hxi.const_mul _)).add (hx2i.const_mul _)
  have hxmean : (∫ x : ℝ, x ∂γ) = 0 := integral_id_gaussianReal
  have hxsecond : (∫ x : ℝ, x ^ 2 ∂γ) = 1 := by
    have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_eq_integral (X := fun x : ℝ => x) measurable_id.aemeasurable,
      integral_id_gaussianReal] at h
    simpa only [sub_zero, NNReal.coe_one] using h
  have hPmean : (∫ x, P x ∂γ) = f 0 + iteratedDeriv 2 f 0 / 2 := by
    dsimp only [P]
    rw [integral_add (f := fun x => f 0 + deriv f 0 * x)
        (g := fun x => (iteratedDeriv 2 f 0 / 2) * x ^ 2)
        ((integrable_const _).add (hxi.const_mul _)) (hx2i.const_mul _),
      integral_add (f := fun _ => f 0) (g := fun x => deriv f 0 * x)
        (integrable_const _) (hxi.const_mul _), integral_const,
      integral_const_mul, integral_const_mul, hxmean, hxsecond]
    simp
  have hR : |(f 1 + f (-1)) / 2 - (∫ x, P x ∂γ)| ≤ C / 6 := by
    have hp : (P 1 + P (-1)) / 2 = ∫ x, P x ∂γ := by rw [hPmean]; dsimp [P]; ring
    have h1 := candidate_cubic_taylor_bound hf hC 1
    have hn := candidate_cubic_taylor_bound hf hC (-1)
    change |f 1 - P 1| ≤ C * |(1 : ℝ)| ^ 3 / 6 at h1
    change |f (-1) - P (-1)| ≤ C * |(-1 : ℝ)| ^ 3 / 6 at hn
    norm_num at h1 hn
    rw [← hp]
    calc
      _ = |(f 1 - P 1) + (f (-1) - P (-1))| / 2 := by
        have he : (f 1 + f (-1)) / 2 - (P 1 + P (-1)) / 2 =
            ((f 1 - P 1) + (f (-1) - P (-1))) / 2 := by ring
        rw [he, abs_div]
        norm_num
      _ ≤ (|f 1 - P 1| + |f (-1) - P (-1)|) / 2 :=
        div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
      _ ≤ C / 6 := by linarith
  have hG : |(∫ x, f x ∂γ) - ∫ x, P x ∂γ| ≤
      (C / 6) * ∫ x : ℝ, |x| ^ 3 ∂γ := by
    rw [← integral_sub hfi hPi]
    calc
      _ ≤ ∫ x, |f x - P x| ∂γ := abs_integral_le_integral_abs
      _ ≤ ∫ x : ℝ, (C / 6) * |x| ^ 3 ∂γ := by
        apply integral_mono (hfi.sub hPi).abs
          (candidate_integrable_gaussian_abs_cube.const_mul _)
        intro x
        exact (candidate_cubic_taylor_bound hf hC x).trans_eq (by ring)
      _ = _ := integral_const_mul _ _
  have h := abs_sub_le ((f 1 + f (-1)) / 2) (∫ x, P x ∂γ) (∫ x, f x ∂γ)
  rw [abs_sub_comm (∫ x, P x ∂γ)] at h
  dsimp only [γ] at hR hG h
  nlinarith

private theorem candidate_inverse_cube_step {x : ℝ} (hx : 1 ≤ x) :
    1 / (x + 1) ^ 3 + 1 / (x + 1) ^ 2 ≤ 1 / x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hx1 : 0 < x + 1 := by linarith
  field_simp
  nlinarith [sq_nonneg x]

/-- An elementary cubic tail estimate sufficient for the fresh-coordinate
Lindeberg budget. It needs no prime number theorem. -/
theorem candidate_sum_inverse_cube_tail {X N : ℕ} (hX : 1 ≤ X) :
    (∑ p ∈ Finset.Icc (X + 1) N, 1 / (p : ℝ) ^ 3) ≤ 1 / (X : ℝ) ^ 2 := by
  by_cases hXN : X ≤ N
  · have hstrong : (∑ p ∈ Finset.Icc (X + 1) N, 1 / (p : ℝ) ^ 3) ≤
        1 / (X : ℝ) ^ 2 - 1 / (N : ℝ) ^ 2 := by
      induction N, hXN using Nat.le_induction with
      | base => simp
      | succ n hn ih =>
          rw [Finset.sum_Icc_succ_top (by omega)]
          have hs := candidate_inverse_cube_step
            (show (1 : ℝ) ≤ n by exact_mod_cast hX.trans hn)
          simp only [Nat.cast_add, Nat.cast_one]
          linarith
    exact hstrong.trans (sub_le_self _ (by positivity))
  · have hempty : Finset.Icc (X + 1) N = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    simp only [hempty, Finset.sum_empty]
    positivity

/-- The exact real-time fresh coefficient is bounded by `exp(t/2)/p`,
including the natural floor and division. -/
theorem candidate_log_fresh_coefficient_abs_le
    (omega : Omega) (t : ℝ) {p : ℕ} (hp : 0 < p) :
    |S omega (⌊Real.exp t⌋₊ / p) / Real.exp (t / 2)| ≤ Real.exp (t / 2) / p := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  rw [abs_div, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ ((⌊Real.exp t⌋₊ / p : ℕ) : ℝ) / Real.exp (t / 2) :=
      div_le_div_of_nonneg_right (abs_S_le omega _) (Real.exp_pos _).le
    _ ≤ ((⌊Real.exp t⌋₊ : ℝ) / p) / Real.exp (t / 2) :=
      div_le_div_of_nonneg_right Nat.cast_div_le (Real.exp_pos _).le
    _ ≤ (Real.exp t / p) / Real.exp (t / 2) :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (Nat.floor_le (Real.exp_pos _).le) hp0.le)
        (Real.exp_pos _).le
    _ = Real.exp (t / 2) / p := by
      have hsq : Real.exp t = Real.exp (t / 2) ^ 2 := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      rw [hsq]
      field_simp

/-- A deterministic multivariate cubic coefficient budget for the literal
fresh process. All signs and all retained coordinate sets are allowed. -/
theorem candidate_log_fresh_cubic_coefficient_budget
    {ι : Type*} [Fintype ι] (omega : Omega) (u : ι → ℝ)
    {X N : ℕ} (hX : 1 ≤ X) (P : Finset ℕ)
    (hP : P ⊆ Finset.Icc (X + 1) N) {U : ℝ} (hU : ∀ i, u i ≤ U) :
    (∑ p ∈ P, (∑ i, |S omega (⌊Real.exp (u i)⌋₊ / p) / Real.exp (u i / 2)|) ^ 3) ≤
      (Fintype.card ι : ℝ) ^ 3 * Real.exp (3 * U / 2) / (X : ℝ) ^ 2 := by
  classical
  have hcoeff {p : ℕ} (hp : p ∈ P) :
      (∑ i, |S omega (⌊Real.exp (u i)⌋₊ / p) / Real.exp (u i / 2)|) ≤
        (Fintype.card ι : ℝ) * Real.exp (U / 2) / p := by
    have hp0 : 0 < p := by have := (Finset.mem_Icc.mp (hP hp)).1; omega
    calc
      _ ≤ ∑ _i : ι, Real.exp (U / 2) / p := by
        apply Finset.sum_le_sum
        intro i _
        exact (candidate_log_fresh_coefficient_abs_le omega (u i) hp0).trans
          (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hU i]))
            (Nat.cast_nonneg p))
      _ = _ := by simp; ring
  have htail : (∑ p ∈ P, 1 / (p : ℝ) ^ 3) ≤ 1 / (X : ℝ) ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hP (fun _ _ _ => by positivity)).trans
      (candidate_sum_inverse_cube_tail hX)
  have he : Real.exp (U / 2) ^ 3 = Real.exp (3 * U / 2) := by
    rw [pow_succ, pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ ∑ p ∈ P, ((Fintype.card ι : ℝ) * Real.exp (U / 2) / p) ^ 3 := by
      apply Finset.sum_le_sum
      intro p hp
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (hcoeff hp) 3
    _ = ((Fintype.card ι : ℝ) ^ 3 * Real.exp (3 * U / 2)) *
        ∑ p ∈ P, 1 / (p : ℝ) ^ 3 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [div_pow, mul_pow, he]
      ring
    _ ≤ ((Fintype.card ι : ℝ) ^ 3 * Real.exp (3 * U / 2)) * (1 / (X : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

/-- On the candidate's exponential cutoff, the entire multivariate cubic
budget has exponential decay as soon as the endpoint ratio is below `4/3`.
The factor four accounts explicitly for the natural floor. -/
theorem candidate_log_fresh_cubic_coefficient_budget_exp
    {ι : Type*} [Fintype ι] (omega : Omega) (u : ι → ℝ)
    {T β : ℝ} (hT : Real.log 2 ≤ T) {N : ℕ} (P : Finset ℕ)
    (hP : P ⊆ Finset.Icc (⌊Real.exp T⌋₊ + 1) N) (hU : ∀ i, u i ≤ β * T) :
    (∑ p ∈ P, (∑ i, |S omega (⌊Real.exp (u i)⌋₊ / p) / Real.exp (u i / 2)|) ^ 3) ≤
      4 * (Fintype.card ι : ℝ) ^ 3 * Real.exp ((3 * β / 2 - 2) * T) := by
  have heT : 2 ≤ Real.exp T := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hT
  have hfloor : Real.exp T / 2 ≤ (⌊Real.exp T⌋₊ : ℝ) := by
    have h := Nat.sub_one_lt_floor (Real.exp T)
    linarith
  have hX : 1 ≤ ⌊Real.exp T⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hbudget := candidate_log_fresh_cubic_coefficient_budget omega u hX P hP hU
  have heq : Real.exp (3 * (β * T) / 2) / (Real.exp T / 2) ^ 2 =
      4 * Real.exp ((3 * β / 2 - 2) * T) := by
    have hdiff : Real.exp ((3 * β / 2 - 2) * T) =
        Real.exp (3 * (β * T) / 2) / Real.exp T ^ 2 := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_sub]
      congr 1
      ring
    rw [hdiff]
    ring
  calc
    _ ≤ (Fintype.card ι : ℝ) ^ 3 * Real.exp (3 * (β * T) / 2) /
        (⌊Real.exp T⌋₊ : ℝ) ^ 2 := hbudget
    _ ≤ (Fintype.card ι : ℝ) ^ 3 * Real.exp (3 * (β * T) / 2) /
        (Real.exp T / 2) ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_left₀ (by positivity) hfloor 2
    _ = _ := by rw [mul_div_assoc, heq]; ring

/-- Every fixed polynomial factor is absorbed by the preceding exponential
budget in the candidate range `β<4/3`. -/
theorem candidate_polynomial_cubic_budget_tendsto_zero
    {β : ℝ} (hβ : β < 4 / 3) (d : ℕ) :
    Filter.Tendsto (fun T : ℝ => T ^ d * Real.exp ((3 * β / 2 - 2) * T))
      Filter.atTop (nhds 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (d : ℝ) (2 - 3 * β / 2) (by linarith)
  convert h using 1
  ext T
  rw [Real.rpow_natCast]
  congr 2
  ring

end Erdos.Problem1144
