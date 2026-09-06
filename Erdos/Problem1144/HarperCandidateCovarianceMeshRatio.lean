import Erdos.Problem1144.HarperCandidateWeightedEulerRatio
import Erdos.Problem1144.HarperCandidateCovarianceScreen

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

private theorem scalar_weighted_ratio {a b c : ℝ}
    (hm : a - c ≠ 0) (hp : a + c ≠ 0) :
    ((a - b) ^ 2 / (a - c) + (a + b) ^ 2 / (a + c)) / 2 =
      a * (1 + (b - c) ^ 2 / (a ^ 2 - c ^ 2)) := by
  have hd : a ^ 2 - c ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero hp hm
  field_simp
  ring

/-- Under the Euler-density weight, a change of height costs only a
quadratic prime-scale error.  This holds uniformly at every real height. -/
theorem candidate_integral_weighted_eulerRatio_prime_le {p : ℕ}
    (hp : p.Prime) (t u : ℝ) :
    (∫ b, Problem520.harperCoordinateFactor p t b ^ 2 /
      Problem520.harperCoordinateFactor p u b ∂Problem520.coin) ≤
      (1 + (p : ℝ)⁻¹) * Real.exp
        (16 * (t - u) ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ)) := by
  let a : ℝ := 1 + (p : ℝ)⁻¹
  let b : ℝ := 2 * Real.cos (t * Real.log (p : ℝ)) / Real.sqrt (p : ℝ)
  let c : ℝ := 2 * Real.cos (u * Real.log (p : ℝ)) / Real.sqrt (p : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpR).ne'
  have hs2 := Real.sq_sqrt hpR.le
  have hinv : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hp2
  have hc : c ^ 2 ≤ 4 * (p : ℝ)⁻¹ := by
    have hcos : Real.cos (u * Real.log (p : ℝ)) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (u * Real.log (p : ℝ)),
        sq_nonneg (Real.sin (u * Real.log (p : ℝ)))]
    dsimp only [c]
    rw [div_pow, mul_pow, hs2]
    norm_num only [show (2 : ℝ)^2 = 4 by norm_num]
    exact (div_le_iff₀ hpR).mpr (by nlinarith [mul_inv_cancel₀ hpR.ne'])
  have hd : 1 / 4 ≤ a ^ 2 - c ^ 2 := by
    dsimp only [a]
    nlinarith [sq_nonneg ((p : ℝ)⁻¹ - 1 / 2), inv_nonneg.mpr hpR.le]
  have hden : 0 < a ^ 2 - c ^ 2 := by linarith
  have habs := Real.abs_cos_sub_cos_le
    (t * Real.log (p : ℝ)) (u * Real.log (p : ℝ))
  have hdiff : (b - c) ^ 2 ≤ 4 * (t - u) ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ) := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) habs 2
    simp only [sq_abs] at hh
    have hbc : b - c = 2 * (Real.cos (t * Real.log (p : ℝ)) -
        Real.cos (u * Real.log (p : ℝ))) / Real.sqrt (p : ℝ) := by dsimp only [b, c]; ring
    rw [hbc, div_pow, mul_pow, hs2]
    apply div_le_div_of_nonneg_right _ hpR.le
    nlinarith
  have hratio : (b - c) ^ 2 / (a ^ 2 - c ^ 2) ≤
      16 * (t - u) ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ) := by
    calc
      _ ≤ (4 * (t - u) ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ)) / (1 / 4 : ℝ) :=
        div_le_div₀ (by positivity) hdiff (by norm_num) hd
      _ = _ := by ring
  have hm : a - c ≠ 0 := by
    intro h
    have hEq : a = c := sub_eq_zero.mp h
    rw [hEq] at hden
    linarith
  have hp' : a + c ≠ 0 := by
    intro h
    have hEq : a = -c := by linarith
    rw [hEq] at hden
    nlinarith
  have heq : (∫ b, Problem520.harperCoordinateFactor p t b ^ 2 /
      Problem520.harperCoordinateFactor p u b ∂Problem520.coin) =
      a * (1 + (b - c) ^ 2 / (a ^ 2 - c ^ 2)) := by
    rw [Problem520.integral_coin_bool]
    simp only [Problem520.harperCoordinateFactor, Problem520.harperEulerFactor_eq _ hp.pos,
      Problem520.ε, Bool.false_eq_true, if_false, if_true]
    convert scalar_weighted_ratio hm hp' using 1 <;> dsimp only [a, b, c] <;> ring
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (by dsimp only [a]; positivity)
  exact (add_le_add (le_refl 1) hratio).trans (by simpa only [add_comm] using Real.add_one_le_exp (16 * (t - u) ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ)))

/-- Finite products of literal coin observables are integrable on the
original infinite sign space. -/
theorem candidate_integrable_finiteCoinProduct (S : Finset ℕ) (g : ℕ → Bool → ℝ) :
    Integrable (fun ω : Problem520.Omega => ∏ p ∈ S, g p (ω p)) Problem520.μ := by
  let F : (S → Bool) → ℝ := fun η => ∏ p : S, g p.val (η p)
  have hm := (measurable_of_finite F).stronglyMeasurable.comp_measurable
    (Problem520.measurable_restrict_piFinset S)
  have hi := Problem520.integrable_of_stronglyMeasurable_piFinset hm
  convert hi using 1
  funext ω
  exact (Finset.prod_coe_sort S (fun p => g p (ω p))).symm

/-- Exact finite-product expectation under the original fair law. -/
theorem candidate_integral_finiteCoinProduct (S : Finset ℕ) (g : ℕ → Bool → ℝ) :
    (∫ ω : Problem520.Omega, ∏ p ∈ S, g p (ω p) ∂Problem520.μ) =
      ∏ p ∈ S, ∫ b, g p b ∂Problem520.coin := by
  let X : S → Problem520.Omega → ℝ := fun p ω => g p.val (ω p.val)
  have hi : iIndepFun X Problem520.μ := by
    exact (Problem520.iIndepFun_coordinates.precomp Subtype.val_injective).comp
      (fun p : S => g p.val) (fun _ => measurable_of_finite _)
  have hp := hi.integral_fun_prod_eq_prod_integral
    (fun p => ((measurable_of_finite (g p.val)).comp (measurable_pi_apply p.val)).aestronglyMeasurable)
  have hm (p : S) : (∫ ω, X p ω ∂Problem520.μ) = ∫ b, g p.val b ∂Problem520.coin := by
    rw [← Measure.infinitePi_map_eval (fun _ : ℕ => Problem520.coin) p.val,
      integral_map (measurable_pi_apply p.val).aemeasurable (measurable_of_finite _).aestronglyMeasurable]
    rfl
  have hh := hp.trans (Finset.prod_congr rfl fun p _ => hm p)
  calc
    _ = ∫ ω, ∏ p : S, g p.val (ω p.val) ∂Problem520.μ := by
      congr 1
      funext ω
      exact (Finset.prod_coe_sort S (fun p => g p (ω p))).symm
    _ = ∏ p : S, ∫ b, g p.val b ∂Problem520.coin := hh
    _ = _ := Finset.prod_coe_sort S (fun p => ∫ b, g p b ∂Problem520.coin)

private theorem prefix_subset {B y : ℕ} (hBy : B ≤ y) :
    (B + 1).primesBelow ⊆ (y + 1).primesBelow := by
  intro p hp
  rw [Nat.mem_primesBelow] at hp ⊢
  exact ⟨by omega, hp.2⟩

private theorem weighted_ratio_eq_product {B y : ℕ} (hBy : B ≤ y)
    (t u : ℝ) (ω : Problem520.Omega) :
    Problem520.harperEulerDensity y ω t *
      (Problem520.harperEulerDensity B ω t / Problem520.harperEulerDensity B ω u) =
      ∏ p ∈ (y + 1).primesBelow,
        Problem520.harperCoordinateFactor p t (ω p) *
          if p ∈ (B + 1).primesBelow then
            Problem520.harperCoordinateFactor p t (ω p) /
              Problem520.harperCoordinateFactor p u (ω p) else 1 := by
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.inter_eq_right.mpr (prefix_subset hBy), Finset.prod_div_distrib]
  have heq (p : ℕ) (v : ℝ) : Problem520.harperCoordinateFactor p v (ω p) =
      Problem520.harperEulerFactor ω p v := rfl
  simp only [heq, Problem520.harperEulerDensity]

/-- Integrability of the literal density-weighted mesh ratio. -/
theorem candidate_integrable_weighted_eulerRatio {B y : ℕ} (hBy : B ≤ y) (t u : ℝ) :
    Integrable (fun ω => Problem520.harperEulerDensity y ω t *
      (Problem520.harperEulerDensity B ω t / Problem520.harperEulerDensity B ω u)) Problem520.μ := by
  have heq := funext (weighted_ratio_eq_product hBy t u)
  rw [heq]
  exact candidate_integrable_finiteCoinProduct _ (fun p b => Problem520.harperCoordinateFactor p t b * if p ∈ (B + 1).primesBelow then Problem520.harperCoordinateFactor p t b / Problem520.harperCoordinateFactor p u b else 1)

/-- The literal mesh ratio under the final Euler-density weight, with an
explicit quadratic prime-sum budget and no restriction on the heights. -/
theorem candidate_integral_weighted_eulerRatio_le_exp {B y : ℕ} (hBy : B ≤ y) (t u : ℝ) :
    (∫ ω, Problem520.harperEulerDensity y ω t *
      (Problem520.harperEulerDensity B ω t / Problem520.harperEulerDensity B ω u) ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y * Real.exp (16 * (t - u) ^ 2 *
        ∑ p ∈ (B + 1).primesBelow, Real.log (p : ℝ) ^ 2 / (p : ℝ)) := by
  rw [funext (weighted_ratio_eq_product hBy t u), candidate_integral_finiteCoinProduct _ (fun p b => Problem520.harperCoordinateFactor p t b * if p ∈ (B + 1).primesBelow then Problem520.harperCoordinateFactor p t b / Problem520.harperCoordinateFactor p u b else 1)]
  let L : ℕ → ℝ := fun p => if p ∈ (B + 1).primesBelow then
    16 * (t - u) ^ 2 * Real.log (p : ℝ) ^ 2 / (p : ℝ) else 0
  calc
    _ ≤ ∏ p ∈ (y + 1).primesBelow, (1 + (p : ℝ)⁻¹) * Real.exp (L p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact integral_nonneg fun b => mul_nonneg
          (Problem520.harperCoordinateFactor_nonneg _ _ _) (by
            split_ifs
            · exact div_nonneg (Problem520.harperCoordinateFactor_nonneg _ _ _)
                (Problem520.harperCoordinateFactor_nonneg _ _ _)
            · norm_num)
      · intro p hp
        by_cases hpB : p ∈ (B + 1).primesBelow
        · simp only [hpB, if_true, L]
          have heq : (fun b => Problem520.harperCoordinateFactor p t b *
              (Problem520.harperCoordinateFactor p t b / Problem520.harperCoordinateFactor p u b)) =
              fun b => Problem520.harperCoordinateFactor p t b ^ 2 / Problem520.harperCoordinateFactor p u b := by
            funext b
            ring
          rw [heq]
          exact candidate_integral_weighted_eulerRatio_prime_le (Nat.prime_of_mem_primesBelow hp) t u
        · simp only [hpB, if_false, L, Real.exp_zero, mul_one]
          exact (Problem520.integral_coin_harperCoordinateFactor p t).le
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 1
      congr 1
      dsimp only [L]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (prefix_subset hBy), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- A mesh step of size at most `1/log B` has an absolute density-weighted
ratio cost, independent of the final cutoff and both heights. -/
theorem candidate_integral_weighted_eulerRatio_local_le {B y : ℕ}
    (hB : 2 ≤ B) (hBy : B ≤ y) {t u : ℝ} (htu : |t - u| ≤ (Real.log (B : ℝ))⁻¹) :
    (∫ ω, Problem520.harperEulerDensity y ω t *
      (Problem520.harperEulerDensity B ω t / Problem520.harperEulerDensity B ω u) ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y *
        Real.exp (16 * (1 + (Real.log 4 + 4) / Real.log 2)) := by
  have hly : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  have h2y : Real.log 2 ≤ Real.log (B : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hB)
  have ht2 : (t - u) ^ 2 ≤ (Real.log (B : ℝ))⁻¹ ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) htu 2
  have hlocal : (t - u) ^ 2 * Real.log (B : ℝ) ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right ht2 (sq_nonneg (Real.log (B : ℝ)))
    simpa [← mul_pow, hly.ne'] using h
  apply (candidate_integral_weighted_eulerRatio_le_exp hBy t u).trans
  apply mul_le_mul_of_nonneg_left _ (Problem520.primeEnergyNormalizer_pos y).le
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ 16 * (t - u) ^ 2 * (Real.log (B : ℝ) *
        (Real.log (B : ℝ) + (Real.log 4 + 4))) :=
      mul_le_mul_of_nonneg_left (candidate_sum_prime_log_sq_div_le (by omega)) (by positivity)
    _ = 16 * ((t - u) ^ 2 * Real.log (B : ℝ) ^ 2) *
        (1 + (Real.log 4 + 4) / Real.log (B : ℝ)) := by field_simp
    _ ≤ 16 * 1 * (1 + (Real.log 4 + 4) / Real.log 2) := by
      gcongr
    _ = _ := by ring

private theorem density_div_prefix_eq_product {B y : ℕ} (hBy : B ≤ y)
    (t : ℝ) (ω : Problem520.Omega) :
    Problem520.harperEulerDensity y ω t / Problem520.harperEulerDensity B ω t =
      ∏ p ∈ (y + 1).primesBelow,
        if p ∈ (B + 1).primesBelow then 1 else Problem520.harperCoordinateFactor p t (ω p) := by
  have hid : (∏ p ∈ (y + 1).primesBelow,
      Problem520.harperCoordinateFactor p t (ω p) /
        (if p ∈ (B + 1).primesBelow then Problem520.harperCoordinateFactor p t (ω p) else 1)) =
      Problem520.harperEulerDensity y ω t / Problem520.harperEulerDensity B ω t := by
    rw [Finset.prod_div_distrib, Finset.prod_ite_mem,
      Finset.inter_eq_right.mpr (prefix_subset hBy)]
    rfl
  rw [← hid]
  apply Finset.prod_congr rfl
  intro p hp
  by_cases h : p ∈ (B + 1).primesBelow
  · simp [h, (Problem520.harperCoordinateFactor_pos (Nat.prime_of_mem_primesBelow hp) t (ω p)).ne']
  · simp [h]

/-- Removing the initial Euler product leaves an integrable literal quotient. -/
theorem candidate_integrable_eulerDensity_div_prefix {B y : ℕ} (hBy : B ≤ y) (t : ℝ) :
    Integrable (fun ω => Problem520.harperEulerDensity y ω t /
      Problem520.harperEulerDensity B ω t) Problem520.μ := by
  rw [funext (density_div_prefix_eq_product hBy t)]
  exact candidate_integrable_finiteCoinProduct _
    (fun p b => if p ∈ (B + 1).primesBelow then 1 else Problem520.harperCoordinateFactor p t b)

/-- The lower D-star failure can be charged to the suffix normalizer, which
is at most the full normalizer. -/
theorem candidate_integral_eulerDensity_div_prefix_le {B y : ℕ} (hBy : B ≤ y) (t : ℝ) :
    (∫ ω, Problem520.harperEulerDensity y ω t / Problem520.harperEulerDensity B ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y := by
  rw [funext (density_div_prefix_eq_product hBy t), candidate_integral_finiteCoinProduct _
    (fun p b => if p ∈ (B + 1).primesBelow then 1 else Problem520.harperCoordinateFactor p t b)]
  unfold Problem520.primeEnergyNormalizer
  apply Finset.prod_le_prod
  · intro p hp
    exact integral_nonneg fun b => by
      split_ifs
      · norm_num
      · exact Problem520.harperCoordinateFactor_nonneg _ _ _
  · intro p hp
    by_cases h : p ∈ (B + 1).primesBelow
    · simp only [h, if_true, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
      linarith [inv_nonneg.mpr (show (0 : ℝ) ≤ (p : ℝ) by positivity)]
    · simp only [h, if_false]
      exact (Problem520.integral_coin_harperCoordinateFactor _ _).le

end Erdos.Problem1144
