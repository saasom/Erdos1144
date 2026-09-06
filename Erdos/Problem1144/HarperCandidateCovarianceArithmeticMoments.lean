import Erdos.Problem520.HarperFairEulerProduct
import Erdos.Problem520.HarperTiltedOmega
import Erdos.Problem520.HarperLogTaylor
import Erdos.Problem520.HarperParsevalTail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

noncomputable section

/-!
# The literal mixed Euler moment in Harper's covariance argument

After the strong barrier removes the small-prime prefixes at the ordered
heights, the remaining expectation is a product of mixed one-prime moments.
The retained heights may depend on the prime.  The bound here keeps the
oscillatory quadratic term exactly: the diagonal contribution from the
Gaussian upper bound on `cosh` cancels the second harmonic in the logarithm
of a Rademacher Euler factor.  Its only error is the summable cubic Taylor
remainder, already proved for the literal Euler factors in Problem 520.

This is the local mixed-moment step in the proof of Proposition 3 of
Adam Harper, arXiv:2012.15809, Section 3.4.  It does not assert the subsequent
resonant integration or the strong-barrier deletion probability.
-/

/-- The sharp quadratic exponent and its summable one-prime remainder. -/
def candidateEulerMixedExponent {ι : Type*} (p : ℕ) (s : Finset ι)
    (t : ι → ℝ) : ℝ :=
  (2 * (∑ i ∈ s, Real.cos (t i * Real.log (p : ℝ))) ^ 2 -
      ∑ i ∈ s, Real.cos (2 * (t i * Real.log (p : ℝ)))) / (p : ℝ) +
    (4 / 3 : ℝ) * s.card * (Real.sqrt (p : ℝ))⁻¹ ^ 3

/-- The quadratic exponent has exactly the diagonal mass and the two
Rademacher oscillatory kernels at the sum and difference of each pair of
distinct heights. -/
theorem candidateEulerMixedExponent_eq_pairKernel {ι : Type*}
    (p : ℕ) (s : Finset ι) (t : ι → ℝ) :
    candidateEulerMixedExponent p s t =
      ((s.card : ℝ) + ∑ ij ∈ s.offDiag,
        (Real.cos ((t ij.1 - t ij.2) * Real.log (p : ℝ)) +
          Real.cos ((t ij.1 + t ij.2) * Real.log (p : ℝ)))) / p +
        (4 / 3 : ℝ) * s.card * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
  classical
  let c : ι → ℝ := fun i => Real.cos (t i * Real.log (p : ℝ))
  have hsq : (∑ i ∈ s, c i) ^ 2 =
      (∑ i ∈ s, c i ^ 2) + ∑ ij ∈ s.offDiag, c ij.1 * c ij.2 := by
    rw [pow_two, Finset.sum_mul_sum,
      ← Finset.sum_product s s (fun ij => c ij.1 * c ij.2),
      ← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag s),
      Finset.sum_diag]
    simp only [pow_two]
  have hsecond : (∑ i ∈ s, Real.cos (2 * (t i * Real.log (p : ℝ)))) =
      2 * (∑ i ∈ s, c i ^ 2) - s.card := by
    simp only [Real.cos_two_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one, c]
  have hpairs : (∑ ij ∈ s.offDiag,
      (Real.cos ((t ij.1 - t ij.2) * Real.log (p : ℝ)) +
        Real.cos ((t ij.1 + t ij.2) * Real.log (p : ℝ)))) =
      2 * ∑ ij ∈ s.offDiag, c ij.1 * c ij.2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ij _
    simp only [sub_mul, add_mul, Real.cos_sub, Real.cos_add, c]
    ring
  unfold candidateEulerMixedExponent
  rw [hsecond, hpairs]
  change (2 * (∑ i ∈ s, c i) ^ 2 - _) / _ + _ = _
  rw [hsq]
  ring

/-- The actual squared Euler factor is bounded by its linear sign term,
second harmonic, and the explicit cubic remainder. -/
theorem candidate_eulerFactor_le_exp_quadratic
    (ω : Problem520.Omega) {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) (t : ℝ) :
    Problem520.harperEulerFactor ω p t ≤
      Real.exp (2 * Problem520.ε ω p * Real.cos (t * Real.log (p : ℝ)) /
          Real.sqrt (p : ℝ) - Real.cos (2 * (t * Real.log (p : ℝ))) / p +
        (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3) := by
  have h := (abs_le.mp
    (Problem520.abs_harperLogPrimeIncrement_sub_main_le ω hp4 t)).2
  rw [Problem520.harperLogPrimeIncrement_eq_half_log_factor] at h
  have hlog : Real.log (Problem520.harperEulerFactor ω p t) ≤
      2 * Problem520.ε ω p * Real.cos (t * Real.log (p : ℝ)) /
          Real.sqrt (p : ℝ) - Real.cos (2 * (t * Real.log (p : ℝ))) / p +
        (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3 := by
    ring_nf at h ⊢
    linarith
  simpa only [Real.exp_log (Problem520.harperEulerFactor_pos ω hp t)] using
    Real.exp_le_exp.mpr hlog

/-- A mixed moment at one prime, retaining all correlations between the
heights.  No separation hypothesis on the heights is needed. -/
theorem candidate_integral_coin_mixedEuler_le {ι : Type*}
    {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) (s : Finset ι) (t : ι → ℝ) :
    (∫ b, ∏ i ∈ s, Problem520.harperCoordinateFactor p (t i) b
      ∂Problem520.coin) ≤ Real.exp (candidateEulerMixedExponent p s t) := by
  let L : ℝ := 2 * (∑ i ∈ s, Real.cos (t i * Real.log (p : ℝ))) /
    Real.sqrt (p : ℝ)
  let B : ℝ := -(∑ i ∈ s, Real.cos (2 * (t i * Real.log (p : ℝ)))) / p +
    (4 / 3 : ℝ) * s.card * (Real.sqrt (p : ℝ))⁻¹ ^ 3
  have hprod (b : Bool) :
      (∏ i ∈ s, Problem520.harperCoordinateFactor p (t i) b) ≤
        Real.exp (Problem520.ε (fun _ => b) p * L + B) := by
    calc
      (∏ i ∈ s, Problem520.harperCoordinateFactor p (t i) b) ≤
          ∏ i ∈ s, Real.exp
            (2 * Problem520.ε (fun _ => b) p *
                Real.cos (t i * Real.log (p : ℝ)) / Real.sqrt (p : ℝ) -
              Real.cos (2 * (t i * Real.log (p : ℝ))) / p +
              (4 / 3 : ℝ) * (Real.sqrt (p : ℝ))⁻¹ ^ 3) := by
        exact Finset.prod_le_prod
          (fun i _ => Problem520.harperCoordinateFactor_nonneg p (t i) b)
          (fun i _ => candidate_eulerFactor_le_exp_quadratic (fun _ => b) hp hp4 (t i))
      _ = Real.exp (Problem520.ε (fun _ => b) p * L + B) := by
        rw [← Real.exp_sum]
        congr 1
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, L, B]
        ring
  have havg :
      (∫ b, ∏ i ∈ s, Problem520.harperCoordinateFactor p (t i) b
        ∂Problem520.coin) ≤ Real.exp B * Real.cosh L := by
    rw [Problem520.integral_coin_bool]
    have hf := hprod false
    have ht := hprod true
    simp only [Problem520.ε, Bool.false_eq_true, if_false, if_true,
      neg_one_mul, one_mul] at hf ht
    calc
      _ ≤ (Real.exp (-L + B) + Real.exp (L + B)) / 2 := by linarith
      _ = Real.exp B * Real.cosh L := by
        rw [Real.cosh_eq, Real.exp_add (-L) B, Real.exp_add L B]
        ring
  have hmain : B + L ^ 2 / 2 = candidateEulerMixedExponent p s t := by
    dsimp [B, L, candidateEulerMixedExponent]
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    ring
  calc
    _ ≤ Real.exp B * Real.cosh L := havg
    _ ≤ Real.exp B * Real.exp (L ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq L) (Real.exp_pos B).le
    _ = Real.exp (candidateEulerMixedExponent p s t) := by
      rw [← Real.exp_add, hmain]

/-- Independence gives the literal mixed Euler-product bound on the finite
prime cube, with an arbitrary collection of retained heights at each prime. -/
theorem candidate_integral_mixedEuler_cube_le {ι : Type*}
    (y : ℕ) (I : Problem520.HarperPrimeIndex y → Finset ι) (t : ι → ℝ)
    (hsmall : ∀ p, p.1 < 4 → I p = ∅) :
    (∫ η, ∏ p : Problem520.HarperPrimeIndex y,
      ∏ i ∈ I p, Problem520.harperCoordinateFactor p.1 (t i) (η p)
      ∂Problem520.harperFairCubeLaw y) ≤
      Real.exp (∑ p : Problem520.HarperPrimeIndex y,
        candidateEulerMixedExponent p.1 (I p) t) := by
  rw [Problem520.integral_prod_harperFairCubeLaw y
    (fun p b => ∏ i ∈ I p, Problem520.harperCoordinateFactor p.1 (t i) b),
    Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p _
    exact integral_nonneg fun b => Finset.prod_nonneg fun i _ =>
      Problem520.harperCoordinateFactor_nonneg p.1 (t i) b
  · intro p _
    by_cases hp4 : 4 ≤ p.1
    · exact candidate_integral_coin_mixedEuler_le
        (Nat.prime_of_mem_primesBelow p.2) hp4 (I p) t
    · rw [hsmall p (by omega)]
      rw [Problem520.integral_coin_bool]
      simp [candidateEulerMixedExponent]

/-- The same bound for the literal Euler factors on the original infinite
Rademacher probability space; there is no distributional input left to supply. -/
theorem candidate_integral_mixedEuler_le {ι : Type*}
    (y : ℕ) (I : Problem520.HarperPrimeIndex y → Finset ι) (t : ι → ℝ)
    (hsmall : ∀ p, p.1 < 4 → I p = ∅) :
    (∫ ω, ∏ p : Problem520.HarperPrimeIndex y,
      ∏ i ∈ I p, Problem520.harperEulerFactor ω p.1 (t i) ∂Problem520.μ) ≤
      Real.exp (∑ p : Problem520.HarperPrimeIndex y,
        candidateEulerMixedExponent p.1 (I p) t) := by
  have h := candidate_integral_mixedEuler_cube_le y I t hsmall
  rw [Problem520.harperFairCubeLaw,
    ← Problem520.integral_comp_harperPrimeRestriction_mu] at h
  convert h using 1

private theorem coordinateFactor_le_four {p : ℕ} (hp : p.Prime)
    (t : ℝ) (b : Bool) : Problem520.harperCoordinateFactor p t b ≤ 4 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hs1 : (1 : ℝ) ≤ Real.sqrt p := by
    exact Real.le_sqrt_of_sq_le (by simpa using hp1)
  have hinv : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp1
  have hdiv : (2 : ℝ) / Real.sqrt p ≤ 2 := by
    exact (div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hp.pos))).2 (by linarith)
  exact (Problem520.harperEulerFactor_le_uniformFactor (fun _ => b) hp.pos t).trans
    (by linarith)

/-- All primes are allowed in the literal mixed product.  The two primes
below the Taylor range contribute their elementary finite-factor bound;
every larger prime retains the sharp oscillatory exponent. -/
theorem candidate_integral_mixedEuler_cube_le_all_primes {ι : Type*}
    (y : ℕ) (I : Problem520.HarperPrimeIndex y → Finset ι) (t : ι → ℝ) :
    (∫ η, ∏ p : Problem520.HarperPrimeIndex y,
      ∏ i ∈ I p, Problem520.harperCoordinateFactor p.1 (t i) (η p)
      ∂Problem520.harperFairCubeLaw y) ≤
      Real.exp (∑ p : Problem520.HarperPrimeIndex y,
        if 4 ≤ p.1 then candidateEulerMixedExponent p.1 (I p) t
        else (I p).card * Real.log 4) := by
  rw [Problem520.integral_prod_harperFairCubeLaw y
    (fun p b => ∏ i ∈ I p, Problem520.harperCoordinateFactor p.1 (t i) b),
    Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p _
    exact integral_nonneg fun b => Finset.prod_nonneg fun i _ =>
      Problem520.harperCoordinateFactor_nonneg p.1 (t i) b
  · intro p _
    split_ifs with hp4
    · exact candidate_integral_coin_mixedEuler_le
        (Nat.prime_of_mem_primesBelow p.2) hp4 (I p) t
    · have hprod (b : Bool) :
          (∏ i ∈ I p, Problem520.harperCoordinateFactor p.1 (t i) b) ≤
            (4 : ℝ) ^ (I p).card := by
        simpa using Finset.prod_le_prod
          (s := I p) (g := fun _ => (4 : ℝ))
          (fun i _ => Problem520.harperCoordinateFactor_nonneg p.1 (t i) b)
          (fun i _ => coordinateFactor_le_four
            (Nat.prime_of_mem_primesBelow p.2) (t i) b)
      rw [Problem520.integral_coin_bool, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      linarith [hprod false, hprod true]

/-- The all-prime version on the original infinite sign space. -/
theorem candidate_integral_mixedEuler_le_all_primes {ι : Type*}
    (y : ℕ) (I : Problem520.HarperPrimeIndex y → Finset ι) (t : ι → ℝ) :
    (∫ ω, ∏ p : Problem520.HarperPrimeIndex y,
      ∏ i ∈ I p, Problem520.harperEulerFactor ω p.1 (t i) ∂Problem520.μ) ≤
      Real.exp (∑ p : Problem520.HarperPrimeIndex y,
        if 4 ≤ p.1 then candidateEulerMixedExponent p.1 (I p) t
        else (I p).card * Real.log 4) := by
  have h := candidate_integral_mixedEuler_cube_le_all_primes y I t
  rw [Problem520.harperFairCubeLaw,
    ← Problem520.integral_comp_harperPrimeRestriction_mu] at h
  convert h using 1

end

end Erdos.Problem1144
