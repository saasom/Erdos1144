import Erdos.Problem1144.HarperCandidateCovarianceArithmeticMoments

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- The exact signed quadratic prime exponent for two Euler moduli. The
negative second harmonics are retained, as required in the far-pair bound. -/
noncomputable def candidateHalfDensityPairPrimeExponent (p : ℕ) (t v : ℝ) : ℝ :=
  ((1 / 2 : ℝ) - Real.cos (2 * t * Real.log (p : ℝ)) / 4 -
      Real.cos (2 * v * Real.log (p : ℝ)) / 4 +
      Real.cos ((t - v) * Real.log (p : ℝ)) / 2 +
      Real.cos ((t + v) * Real.log (p : ℝ)) / 2) / p

private theorem sqrt_factor_le_exp (ω : Problem520.Omega) {p : ℕ}
    (hp : p.Prime) (hp4 : 4 ≤ p) (t : ℝ) :
    Real.sqrt (Problem520.harperEulerFactor ω p t) ≤
      Real.exp (Problem520.ε ω p * Real.cos (t * Real.log (p : ℝ)) / Real.sqrt (p : ℝ) -
        Real.cos (2 * (t * Real.log (p : ℝ))) / (2 * p) +
        (2 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3) := by
  have h := (abs_le.mp (Problem520.abs_harperLogPrimeIncrement_sub_main_le ω hp4 t)).2
  rw [Problem520.harperLogPrimeIncrement_eq_half_log_factor] at h
  have hlog : Real.log (Real.sqrt (Problem520.harperEulerFactor ω p t)) ≤
      Problem520.ε ω p * Real.cos (t * Real.log (p : ℝ)) / Real.sqrt (p : ℝ) -
        Real.cos (2 * (t * Real.log (p : ℝ))) / (2 * p) +
        (2 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
    rw [Real.log_sqrt (Problem520.harperEulerFactor_pos ω hp t).le]
    linarith
  simpa only [Real.exp_log (Real.sqrt_pos.mpr (Problem520.harperEulerFactor_pos ω hp t))] using
    Real.exp_le_exp.mpr hlog

/-- Fair one-prime half-density moment with the exact quadratic exponent
and the summable cubic Taylor error. -/
theorem candidate_integral_coin_halfDensityPair_le {p : ℕ}
    (hp : p.Prime) (hp4 : 4 ≤ p) (t v : ℝ) :
    (∫ b, Real.sqrt (Problem520.harperCoordinateFactor p t b) *
      Real.sqrt (Problem520.harperCoordinateFactor p v b) ∂Problem520.coin) ≤
      Real.exp (candidateHalfDensityPairPrimeExponent p t v +
        (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3) := by
  let L := (Real.cos (t * Real.log (p : ℝ)) + Real.cos (v * Real.log (p : ℝ))) /
    Real.sqrt (p : ℝ)
  let B := -(Real.cos (2 * (t * Real.log (p : ℝ))) +
      Real.cos (2 * (v * Real.log (p : ℝ)))) / (2 * p) +
        (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3
  have hprod (b : Bool) :
      Real.sqrt (Problem520.harperCoordinateFactor p t b) *
        Real.sqrt (Problem520.harperCoordinateFactor p v b) ≤
          Real.exp (Problem520.ε (fun _ => b) p * L + B) := by
    have h := mul_le_mul (sqrt_factor_le_exp (fun _ => b) hp hp4 t)
      (sqrt_factor_le_exp (fun _ => b) hp hp4 v) (Real.sqrt_nonneg _) (Real.exp_pos _).le
    rw [← Real.exp_add] at h
    convert h using 1
    congr 1
    dsimp only [L, B]
    ring
  have havg :
      (∫ b, Real.sqrt (Problem520.harperCoordinateFactor p t b) *
        Real.sqrt (Problem520.harperCoordinateFactor p v b) ∂Problem520.coin) ≤
          Real.exp B * Real.cosh L := by
    rw [Problem520.integral_coin_bool]
    have hf := hprod false
    have ht := hprod true
    simp only [Problem520.ε, Bool.false_eq_true, if_false, if_true,
      neg_one_mul, one_mul] at hf ht
    calc
      _ ≤ (Real.exp (-L + B) + Real.exp (L + B)) / 2 := by linarith
      _ = _ := by rw [Real.cosh_eq, Real.exp_add (-L) B, Real.exp_add L B]; ring
  have hmain : B + L ^ 2 / 2 = candidateHalfDensityPairPrimeExponent p t v +
      (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
    dsimp only [B, L, candidateHalfDensityPairPrimeExponent]
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    simp only [sub_mul, add_mul, mul_assoc, Real.cos_two_mul, Real.cos_sub, Real.cos_add]
    ring
  calc
    _ ≤ Real.exp B * Real.cosh L := havg
    _ ≤ Real.exp B * Real.exp (L ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq L) (Real.exp_pos B).le
    _ = _ := by rw [← Real.exp_add, hmain]

private theorem pair_prime_exponent_ge_neg_one {p : ℕ} (hp : p.Prime) (t v : ℝ) :
    -1 ≤ candidateHalfDensityPairPrimeExponent p t v := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hn : (-1 : ℝ) ≤ (1 / 2 : ℝ) - Real.cos (2 * t * Real.log (p : ℝ)) / 4 -
      Real.cos (2 * v * Real.log (p : ℝ)) / 4 +
      Real.cos ((t - v) * Real.log (p : ℝ)) / 2 +
      Real.cos ((t + v) * Real.log (p : ℝ)) / 2 := by
    linarith [Real.cos_le_one (2 * t * Real.log (p : ℝ)),
      Real.cos_le_one (2 * v * Real.log (p : ℝ)),
      Real.neg_one_le_cos ((t - v) * Real.log (p : ℝ)),
      Real.neg_one_le_cos ((t + v) * Real.log (p : ℝ))]
  unfold candidateHalfDensityPairPrimeExponent
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < p)).mpr
  nlinarith

private theorem sqrt_coordinateFactor_le_two {p : ℕ} (hp : p.Prime) (t : ℝ) (b : Bool) :
    Real.sqrt (Problem520.harperCoordinateFactor p t b) ≤ 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hs1 : (1 : ℝ) ≤ Real.sqrt p := Real.le_sqrt_of_sq_le (by simpa using hp1)
  have hinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
  have hdiv : (2 : ℝ) / Real.sqrt p ≤ 2 :=
    (div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hp.pos))).2 (by linarith)
  apply Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
  exact (Problem520.harperEulerFactor_le_uniformFactor (fun _ => b) hp.pos t).trans
    (by norm_num; linarith)

private theorem coin_pair_all_primes {p : ℕ} (hp : p.Prime) (t v : ℝ) :
    (∫ b, Real.sqrt (Problem520.harperCoordinateFactor p t b) *
      Real.sqrt (Problem520.harperCoordinateFactor p v b) ∂Problem520.coin) ≤
      Real.exp (candidateHalfDensityPairPrimeExponent p t v +
        (if p < 4 then (4 : ℝ) else 0) + (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3) := by
  by_cases hp4 : 4 ≤ p
  · simpa only [if_neg (not_lt.mpr hp4), add_zero] using
      candidate_integral_coin_halfDensityPair_le hp hp4 t v
  · have hp4' : p < 4 := by omega
    have havg : (∫ b, Real.sqrt (Problem520.harperCoordinateFactor p t b) *
        Real.sqrt (Problem520.harperCoordinateFactor p v b) ∂Problem520.coin) ≤ 4 := by
      rw [Problem520.integral_coin_bool]
      have hb (b : Bool) : Real.sqrt (Problem520.harperCoordinateFactor p t b) *
          Real.sqrt (Problem520.harperCoordinateFactor p v b) ≤ 4 := by
        exact (mul_le_mul (sqrt_coordinateFactor_le_two hp t b)
          (sqrt_coordinateFactor_le_two hp v b) (Real.sqrt_nonneg _) (by norm_num)).trans_eq
          (by norm_num)
      linarith [hb false, hb true]
    apply havg.trans
    rw [if_pos hp4']
    have hlog : Real.log 4 ≤ (3 : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    have he : Real.log 4 ≤ candidateHalfDensityPairPrimeExponent p t v + 4 +
        (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
      have hc : 0 ≤ (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by positivity
      linarith [pair_prime_exponent_ge_neg_one hp t v]
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 4)] using Real.exp_le_exp.mpr he

/-- Exact independence for the literal two-height Euler moduli. -/
theorem candidate_integral_halfDensityPair_eq_prime_product (Y : ℕ) (t v : ℝ) :
    (∫ ω, Real.sqrt (Problem520.harperEulerDensity Y ω t) *
      Real.sqrt (Problem520.harperEulerDensity Y ω v) ∂Problem520.μ) =
      ∏ p : Problem520.HarperPrimeIndex Y,
        ∫ b, Real.sqrt (Problem520.harperCoordinateFactor p.1 t b) *
          Real.sqrt (Problem520.harperCoordinateFactor p.1 v b) ∂Problem520.coin := by
  rw [← Problem520.integral_prod_harperFairCubeLaw Y,
    Problem520.harperFairCubeLaw, ← Problem520.integral_comp_harperPrimeRestriction_mu]
  apply integral_congr_ae
  filter_upwards [] with ω
  unfold Problem520.harperEulerDensity
  rw [Real.sqrt_prod _ (fun p hp => (Problem520.harperEulerFactor_pos ω
    (Nat.prime_of_mem_primesBelow hp) t).le),
    Real.sqrt_prod _ (fun p hp => (Problem520.harperEulerFactor_pos ω
    (Nat.prime_of_mem_primesBelow hp) v).le), ← Finset.prod_mul_distrib]
  exact (Finset.prod_coe_sort _ _).symm

/-- Uniform unscreened half-density moment on the actual infinite sign
space. Only an absolute constant absorbs the finitely many small primes
and the already summable cubic Taylor remainder. -/
theorem candidate_exists_halfDensity_pair_moment_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℕ) (t v : ℝ),
      (∫ ω, Real.sqrt (Problem520.harperEulerDensity Y ω t) *
        Real.sqrt (Problem520.harperEulerDensity Y ω v) ∂Problem520.μ) ≤
          C * Real.exp (∑ p ∈ (Y + 1).primesBelow,
            candidateHalfDensityPairPrimeExponent p t v) := by
  let R := (4 / 3 : ℝ) * ∑' p : ℕ, (Real.sqrt (p : ℝ))⁻¹ ^ 3
  refine ⟨Real.exp (16 + R), Real.exp_pos _, ?_⟩
  intro Y t v
  let P := (Y + 1).primesBelow
  have hsmall : (∑ p ∈ P, if p < 4 then (4 : ℝ) else 0) ≤ 16 := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hs : P.filter (fun p => p < 4) ⊆ Finset.range 4 := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    have hc : (P.filter (fun p => p < 4)).card ≤ 4 :=
      (Finset.card_le_card hs).trans_eq (Finset.card_range _)
    have hcR : ((P.filter (fun p => p < 4)).card : ℝ) ≤ 4 := by exact_mod_cast hc
    nlinarith
  have hcubic : (∑ p ∈ P, (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3) ≤ R := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (Problem520.summable_harperCubicScale.sum_le_tsum P (fun p _ => by positivity)) (by norm_num)
  calc
    _ = ∏ p : Problem520.HarperPrimeIndex Y,
        ∫ b, Real.sqrt (Problem520.harperCoordinateFactor p.1 t b) *
          Real.sqrt (Problem520.harperCoordinateFactor p.1 v b) ∂Problem520.coin :=
      candidate_integral_halfDensityPair_eq_prime_product Y t v
    _ ≤ ∏ p : Problem520.HarperPrimeIndex Y,
        Real.exp (candidateHalfDensityPairPrimeExponent p.1 t v +
          (if p.1 < 4 then (4 : ℝ) else 0) +
          (4 / 3 : ℝ) * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) := by
      exact Finset.prod_le_prod
        (fun p _ => integral_nonneg (fun b => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
        (fun p _ => coin_pair_all_primes (Nat.prime_of_mem_primesBelow p.2) t v)
    _ = Real.exp ((∑ p ∈ P, candidateHalfDensityPairPrimeExponent p t v) +
        (∑ p ∈ P, if p < 4 then (4 : ℝ) else 0) +
        ∑ p ∈ P, (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3) := by
      rw [← Real.exp_sum]
      let f : ℕ → ℝ := fun p => candidateHalfDensityPairPrimeExponent p t v +
        (if p < 4 then 4 else 0) + (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3
      change Real.exp (∑ p : P, f p.val) = _
      rw [Finset.sum_coe_sort P f]
      simp only [f, Finset.sum_add_distrib]
    _ ≤ Real.exp ((∑ p ∈ P, candidateHalfDensityPairPrimeExponent p t v) + 16 + R) :=
      Real.exp_le_exp.mpr (add_le_add (add_le_add (le_refl _) hsmall) hcubic)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos.Problem1144
