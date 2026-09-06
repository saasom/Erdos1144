import Erdos.Problem1144.HarperRestrictedBandProbability
import Erdos.Problem520.HarperScheduledSummableErrors

open Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Erdos
namespace Problem1144

/-!
# The complete Euler product as a deterministic square correction

At one prime, put `z = epsilon_p p^(-1/2-it)`.  The elementary identity

`(1 - z)⁻¹ = (1 + z) * (1 - z²)⁻¹`

shows that the critical complete Euler product is the squarefree Harper
product times a square-factor product.  The latter contains no random sign,
because `epsilon_p² = 1`.

This file first records the exact finite-product identity.  It then bounds
the square correction uniformly from below on the fixed band `[1/3,1/2]`
at the scheduled cutoffs used by the Harper certificate.  The analytic input
is only the already-proved summable strong-PNT bound for
`sum_p cos(2t log p) / p`.
-/

/-- The two problem namespaces use literally the same Boolean Rademacher
coordinate and the same infinite product law. -/
@[simp] theorem eps_eq_problem520_epsilon (omega : Omega) (p : ℕ) :
    eps omega p = Problem520.ε omega p := rfl

theorem mu_eq_problem520_mu : mu = Problem520.μ := rfl

/-- The squared inverse complete Euler factor at one prime. -/
noncomputable def harperCompleteEulerFactor
    (omega : Omega) (p : ℕ) (t : ℝ) : ℝ :=
  Complex.normSq
    (1 - Problem520.harperComplexPrimeTerm omega p t)⁻¹

/-- The inverse square-factor correction at one prime.  Although written
using `omega`, its square removes the Rademacher sign; a pointwise explicit
formula below makes that independence literal. -/
noncomputable def harperSquareCorrectionFactor
    (omega : Omega) (p : ℕ) (t : ℝ) : ℝ :=
  Complex.normSq
    (1 - Problem520.harperComplexPrimeTerm omega p t ^ 2)⁻¹

/-- The complete local factor is exactly the squarefree local factor times
the inverse square correction. -/
theorem harperCompleteEulerFactor_eq_square_mul_squarefree
    (omega : Omega) {p : ℕ} (hp : p.Prime) (t : ℝ) :
    harperCompleteEulerFactor omega p t =
      harperSquareCorrectionFactor omega p t *
        Problem520.harperEulerFactor omega p t := by
  let z : ℂ := Problem520.harperComplexPrimeTerm omega p t
  have hnorm : ‖z‖ < 1 := by
    rw [Problem520.norm_harperComplexPrimeTerm omega hp.pos t]
    have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hsqrt : (1 : ℝ) < Real.sqrt (p : ℝ) := by
      rw [Real.lt_sqrt (by norm_num)]
      simpa using hpR
    exact (inv_lt_one₀ (Real.sqrt_pos.2 (by positivity))).2 hsqrt
  have hplus : 1 + z ≠ 0 := by
    intro hzero
    have hz : z = -1 := eq_neg_of_add_eq_zero_right hzero
    rw [hz] at hnorm
    norm_num at hnorm
  have hfactor : (1 - z)⁻¹ = (1 + z) * (1 - z ^ 2)⁻¹ := by
    have hsq : 1 - z ^ 2 = (1 - z) * (1 + z) := by ring
    rw [hsq, mul_inv_rev, ← mul_assoc]
    rw [mul_inv_cancel₀ hplus, one_mul]
  unfold harperCompleteEulerFactor harperSquareCorrectionFactor
  change Complex.normSq (1 - z)⁻¹ =
    Complex.normSq (1 - z ^ 2)⁻¹ *
      Problem520.harperEulerFactor omega p t
  rw [hfactor, Complex.normSq_mul]
  rw [Problem520.harperEulerFactor_eq_normSq_complex]
  rw [Complex.sq_norm]
  ring

/-- The finite complete Euler density through `y`. -/
noncomputable def harperCompleteEulerDensity
    (y : ℕ) (omega : Omega) (t : ℝ) : ℝ :=
  ∏ p ∈ (y + 1).primesBelow, harperCompleteEulerFactor omega p t

/-- The finite deterministic square-correction density through `y`. -/
noncomputable def harperSquareCorrectionDensity
    (y : ℕ) (omega : Omega) (t : ℝ) : ℝ :=
  ∏ p ∈ (y + 1).primesBelow, harperSquareCorrectionFactor omega p t

/-- Exact finite-product factorization of the complete critical density. -/
theorem harperCompleteEulerDensity_eq_square_mul_squarefree
    (y : ℕ) (omega : Omega) (t : ℝ) :
    harperCompleteEulerDensity y omega t =
      harperSquareCorrectionDensity y omega t *
        Problem520.harperEulerDensity y omega t := by
  classical
  unfold harperCompleteEulerDensity harperSquareCorrectionDensity
    Problem520.harperEulerDensity
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact harperCompleteEulerFactor_eq_square_mul_squarefree omega
    (Nat.prime_of_mem_primesBelow hp) t

/-- Explicit real denominator of the deterministic square correction. -/
noncomputable def harperSquareCorrectionDenominator
    (p : ℕ) (t : ℝ) : ℝ :=
  1 + (p : ℝ)⁻¹ ^ 2 -
    2 * Real.cos (2 * (t * Real.log (p : ℝ))) / p

private theorem harperComplexPrimeTerm_sq_re
    (omega : Omega) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    (Problem520.harperComplexPrimeTerm omega p t ^ 2).re =
      Real.cos (2 * (t * Real.log (p : ℝ))) / p := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsqrt : Real.sqrt (p : ℝ) ≠ 0 := (Real.sqrt_pos.2 hpR).ne'
  have hsqrtSq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hpR.le
  have heps : Problem520.ε omega p ^ 2 = 1 := Problem520.ε_sq omega p
  rw [pow_two, Complex.mul_re]
  simp only [Problem520.harperComplexPrimeTerm_re,
    Problem520.harperComplexPrimeTerm_im]
  rw [Real.cos_two_mul]
  field_simp [hsqrt]
  rw [heps, hsqrtSq]
  nlinarith [Real.sin_sq_add_cos_sq (t * Real.log (p : ℝ))]

private theorem normSq_harperComplexPrimeTerm
    (omega : Omega) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    Complex.normSq (Problem520.harperComplexPrimeTerm omega p t) =
      (p : ℝ)⁻¹ := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [Complex.normSq_eq_norm_sq,
    Problem520.norm_harperComplexPrimeTerm omega hp t]
  rw [inv_pow, Real.sq_sqrt hpR.le]

/-- The correction is independent of the sign world and is the reciprocal
of the explicit positive real denominator. -/
theorem harperSquareCorrectionFactor_eq
    (omega : Omega) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    harperSquareCorrectionFactor omega p t =
      (harperSquareCorrectionDenominator p t)⁻¹ := by
  let z : ℂ := Problem520.harperComplexPrimeTerm omega p t
  have hnorm : Complex.normSq z = (p : ℝ)⁻¹ :=
    normSq_harperComplexPrimeTerm omega hp t
  have hre : (z ^ 2).re =
      Real.cos (2 * (t * Real.log (p : ℝ))) / p :=
    harperComplexPrimeTerm_sq_re omega hp t
  have hnormsq : Complex.normSq (z ^ 2) = (p : ℝ)⁻¹ ^ 2 := by
    rw [pow_two, Complex.normSq_mul, hnorm]
    simp [pow_two]
  have hconjre : (((starRingEnd ℂ) z) ^ 2).re = (z ^ 2).re := by
    simp [pow_two, Complex.mul_re]
  unfold harperSquareCorrectionFactor harperSquareCorrectionDenominator
  change Complex.normSq (1 - z ^ 2)⁻¹ = _
  rw [Complex.normSq_inv, Complex.normSq_sub, Complex.normSq_one,
    hnormsq]
  simp only [one_mul, map_pow, hconjre, hre]
  ring_nf

theorem harperSquareCorrectionDenominator_pos
    {p : ℕ} (hp : p.Prime) (t : ℝ) :
    0 < harperSquareCorrectionDenominator p t := by
  let a : ℝ := (p : ℝ)⁻¹
  let c : ℝ := Real.cos (2 * (t * Real.log (p : ℝ)))
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by
    dsimp [a]
    exact (inv_lt_one₀ (by positivity)).2 hpR
  have hc : c ≤ 1 := by
    dsimp [c]
    exact Real.cos_le_one _
  have hre : harperSquareCorrectionDenominator p t =
      1 + a ^ 2 - 2 * a * c := by
    dsimp [harperSquareCorrectionDenominator, a, c]
    field_simp
  rw [hre]
  nlinarith [sq_pos_of_pos (sub_pos.mpr ha1)]

/-- The elementary exponential majorant for one square denominator. -/
theorem harperSquareCorrectionDenominator_le_exp
    (p : ℕ) (t : ℝ) :
    harperSquareCorrectionDenominator p t ≤
      Real.exp ((p : ℝ)⁻¹ ^ 2 -
        2 * Real.cos (2 * (t * Real.log (p : ℝ))) / p) := by
  unfold harperSquareCorrectionDenominator
  have h := Real.add_one_le_exp
    ((p : ℝ)⁻¹ ^ 2 -
      2 * Real.cos (2 * (t * Real.log (p : ℝ))) / p)
  linarith

private theorem map_harperScheduledPrimeRangeFrom_eq_tailPrimes
    (start n : ℕ) :
    let y := Problem520.harperBlockEndpoint (start + n)
    (Problem520.harperScheduledPrimeRangeFrom y start n).map
        (Function.Embedding.subtype _) =
      ((y + 1).primesBelow.filter fun p ↦
        Problem520.harperBlockEndpoint start < p) := by
  classical
  dsimp only
  ext p
  simp only [Finset.mem_map, Finset.mem_filter, Nat.mem_primesBelow]
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hinterval :=
      (Problem520.mem_harperScheduledPrimeRangeFrom q).mp hq
    exact ⟨Nat.mem_primesBelow.mp q.property, hinterval.1⟩
  · rintro ⟨⟨hpy, hpprime⟩, hpstart⟩
    let q : Problem520.HarperPrimeIndex
        (Problem520.harperBlockEndpoint (start + n)) :=
      ⟨p, Nat.mem_primesBelow.mpr ⟨hpy, hpprime⟩⟩
    refine ⟨q, ?_, rfl⟩
    exact (Problem520.mem_harperScheduledPrimeRangeFrom q).mpr
      ⟨hpstart, by
        change p ≤ Problem520.harperBlockEndpoint (start + n)
        omega⟩

private theorem sum_primesBelow_eq_prefix_add_scheduled
    (start n : ℕ) (g : ℕ → ℝ) :
    let y := Problem520.harperBlockEndpoint (start + n)
    (∑ p ∈ (y + 1).primesBelow, g p) =
      (∑ p ∈ (Problem520.harperBlockEndpoint start + 1).primesBelow,
        g p) +
      ∑ p ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
        g p.1 := by
  classical
  dsimp only
  let y := Problem520.harperBlockEndpoint (start + n)
  let A := Problem520.harperBlockEndpoint start
  have hAy : A ≤ y :=
    Problem520.monotone_harperBlockEndpoint (by omega)
  have hprefix :
      ((y + 1).primesBelow.filter fun p ↦ p ≤ A) =
        (A + 1).primesBelow := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesBelow]
    constructor
    · rintro ⟨⟨hpy, hpprime⟩, hpA⟩
      exact ⟨by omega, hpprime⟩
    · rintro ⟨hpA, hpprime⟩
      exact ⟨⟨by omega, hpprime⟩, by omega⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := (y + 1).primesBelow) (p := fun p ↦ p ≤ A) (f := g)
  rw [hprefix] at hsplit
  have htail :
      (∑ p ∈ (y + 1).primesBelow.filter (fun p ↦ ¬p ≤ A), g p) =
        ∑ p ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
          g p.1 := by
    let e : Problem520.HarperPrimeIndex y ↪ ℕ :=
      Function.Embedding.subtype _
    calc
      (∑ p ∈ (y + 1).primesBelow.filter (fun p ↦ ¬p ≤ A), g p) =
          ∑ p ∈ (y + 1).primesBelow.filter (fun p ↦ A < p), g p := by
            congr 1
            ext p
            simp only [Finset.mem_filter]
            constructor <;> rintro ⟨hp, hbound⟩
            · exact ⟨hp, by omega⟩
            · exact ⟨hp, by omega⟩
      _ = ∑ p ∈
          (Problem520.harperScheduledPrimeRangeFrom y start n).map e,
            g p := by
          rw [map_harperScheduledPrimeRangeFrom_eq_tailPrimes start n]
      _ = ∑ p ∈ Problem520.harperScheduledPrimeRangeFrom y start n,
            g p.1 := by
          rw [Finset.sum_map]
          rfl
  rw [htail] at hsplit
  exact hsplit.symm

/-- On the fixed Harper band, the deterministic square correction has one
uniform positive lower bound along a cofinal scheduled sequence of cutoffs. -/
theorem exists_harperSquareCorrectionDensity_scheduled_lower :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ start : ℕ,
      ∀ n : ℕ, ∀ omega : Omega, ∀ t ∈ harperLowerVerticalBand,
        kappa ≤ harperSquareCorrectionDensity
          (Problem520.harperBlockEndpoint (start + n)) omega t := by
  classical
  obtain ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, hcum⟩ :=
    Problem520.exists_harperScheduledDyadicCumulativeErrorBounds
  let start : ℕ := J + 1
  let A : ℕ := Problem520.harperBlockEndpoint start
  let prefixBudget : ℝ :=
    ∑ p ∈ (A + 1).primesBelow,
      ((p : ℝ)⁻¹ ^ 2 + 2 * (p : ℝ)⁻¹)
  let oscillationBudget : ℝ :=
    Problem520.harperScheduledErrorTail
      (Problem520.harperScheduledDyadicOscillationEnvelope 1 c C) start
  let squareBudget : ℝ :=
    Problem520.harperScheduledErrorTail
      Problem520.harperScheduledSquareEnvelope start
  let K : ℝ := prefixBudget + 2 * oscillationBudget + squareBudget
  let kappa : ℝ := Real.exp (-K)
  have hkappa : 0 < kappa := by dsimp [kappa]; positivity
  refine ⟨kappa, hkappa, start, ?_⟩
  intro n omega t ht
  let y : ℕ := Problem520.harperBlockEndpoint (start + n)
  let u : Fin n → ℝ := fun _ ↦ t
  have htBand : (1 : ℝ) / 3 ≤ t ∧ t ≤ (1 : ℝ) / 2 := ht
  have htPos : 0 < t := by linarith
  have htLower : ∀ i : Fin n, (1 / 2 : ℝ) ^ (1 + 1) < |u i| := by
    intro i
    dsimp [u]
    rw [abs_of_pos htPos]
    norm_num
    linarith
  have htUpper : ∀ i : Fin n, |u i| ≤ 1 := by
    intro i
    dsimp [u]
    rw [abs_of_pos htPos]
    linarith
  have hmesh : ∀ i : Fin n,
      |u i - u i| *
        Real.log (Problem520.harperBlockEndpoint
          (start + (i : ℕ) + 1) : ℝ) ≤ 1 := by
    intro i
    simp
  have herr := hcum 1 start n y (by dsimp [start]; omega)
    (by simp [y]) u u htLower htUpper hmesh
  let S := Problem520.harperScheduledPrimeRangeFrom y start n
  let osc : ℝ :=
    ∑ p ∈ S,
      Real.cos (2 * t * Real.log (p.1 : ℝ)) / p.1
  have hoscEq :
      (∑ i : Fin n,
          Problem520.harperScheduledOscillationMass y
            (start + (i : ℕ)) (2 * t)) = osc := by
    simpa only [osc, S, mul_assoc] using
      sum_harperScheduledOscillationMass_eq_rangeFrom y start n (2 * t)
  have hoscAbs : |osc| ≤ oscillationBudget := by
    calc
      |osc| = |∑ i : Fin n,
          Problem520.harperScheduledOscillationMass y
            (start + (i : ℕ)) (2 * t)| := by rw [hoscEq]
      _ ≤ ∑ i : Fin n,
          |Problem520.harperScheduledOscillationMass y
            (start + (i : ℕ)) (2 * t)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ oscillationBudget := by simpa [oscillationBudget] using herr.2.1
  have hsquare :
      (∑ p ∈ S, (p.1 : ℝ)⁻¹ ^ 2) ≤ squareBudget := by
    rw [← sum_harperScheduledSquareMass_eq_rangeFrom y start n]
    simpa [squareBudget] using herr.2.2
  let exponent : ℕ → ℝ := fun p ↦
    (p : ℝ)⁻¹ ^ 2 -
      2 * Real.cos (2 * (t * Real.log (p : ℝ))) / p
  have htailExponent :
      (∑ p ∈ S, exponent p.1) ≤
        2 * oscillationBudget + squareBudget := by
    have hexact :
        (∑ p ∈ S, exponent p.1) =
          (∑ p ∈ S, (p.1 : ℝ)⁻¹ ^ 2) - 2 * osc := by
      dsimp [exponent, osc]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      ring_nf
    rw [hexact]
    have hoscLower : -oscillationBudget ≤ osc := by
      exact (neg_le_of_abs_le hoscAbs)
    linarith
  have hprefixExponent :
      (∑ p ∈ (A + 1).primesBelow, exponent p) ≤ prefixBudget := by
    dsimp [prefixBudget]
    apply Finset.sum_le_sum
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hpPosR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hcos := Real.neg_one_le_cos
      (2 * (t * Real.log (p : ℝ)))
    dsimp [exponent]
    have hinv : 0 ≤ (p : ℝ)⁻¹ := (inv_pos.mpr hpPosR).le
    have hdiv :
        -(2 * Real.cos (2 * (t * Real.log (p : ℝ))) / p) ≤
          2 * (p : ℝ)⁻¹ := by
      rw [div_eq_mul_inv]
      nlinarith
    linarith
  have htotalExponent :
      (∑ p ∈ (y + 1).primesBelow, exponent p) ≤ K := by
    rw [show (∑ p ∈ (y + 1).primesBelow, exponent p) =
        (∑ p ∈ (A + 1).primesBelow, exponent p) +
          ∑ p ∈ S, exponent p.1 by
      simpa only [y, A, S] using
        sum_primesBelow_eq_prefix_add_scheduled start n exponent]
    dsimp [K]
    linarith
  let denominatorProduct : ℝ :=
    ∏ p ∈ (y + 1).primesBelow,
      harperSquareCorrectionDenominator p t
  have hdenomPos : 0 < denominatorProduct := by
    dsimp [denominatorProduct]
    apply Finset.prod_pos
    intro p hp
    exact harperSquareCorrectionDenominator_pos
      (Nat.prime_of_mem_primesBelow hp) t
  have hdenomExp : denominatorProduct ≤ Real.exp K := by
    calc
      denominatorProduct ≤
          ∏ p ∈ (y + 1).primesBelow, Real.exp (exponent p) := by
        dsimp [denominatorProduct]
        apply Finset.prod_le_prod
        · intro p hp
          exact (harperSquareCorrectionDenominator_pos
            (Nat.prime_of_mem_primesBelow hp) t).le
        · intro p hp
          simpa only [exponent] using
            harperSquareCorrectionDenominator_le_exp p t
      _ = Real.exp (∑ p ∈ (y + 1).primesBelow, exponent p) := by
        rw [Real.exp_sum]
      _ ≤ Real.exp K := Real.exp_le_exp.mpr htotalExponent
  have hdensity :
      harperSquareCorrectionDensity y omega t = denominatorProduct⁻¹ := by
    unfold harperSquareCorrectionDensity
    calc
      (∏ p ∈ (y + 1).primesBelow,
          harperSquareCorrectionFactor omega p t) =
          ∏ p ∈ (y + 1).primesBelow,
            (harperSquareCorrectionDenominator p t)⁻¹ := by
        apply Finset.prod_congr rfl
        intro p hp
        exact harperSquareCorrectionFactor_eq omega
          (Nat.Prime.pos (Nat.prime_of_mem_primesBelow hp)) t
      _ = denominatorProduct⁻¹ := by
        rw [Finset.prod_inv_distrib]
  rw [show harperSquareCorrectionDensity
      (Problem520.harperBlockEndpoint (start + n)) omega t =
        harperSquareCorrectionDensity y omega t by rfl, hdensity]
  have hkappaEq : kappa = (Real.exp K)⁻¹ := by
    dsimp [kappa]
    rw [Real.exp_neg]
  rw [hkappaEq]
  exact inv_anti₀ hdenomPos hdenomExp

/-! ## Transfer of the fixed-band energy -/

/-- The complete critical Euler energy on a finite vertical set. -/
noncomputable def harperCompleteEulerSetEnergy
    (y : ℕ) (I : Set ℝ) (omega : Omega) : ℝ :=
  (∫ t in I, harperCompleteEulerDensity y omega t) /
    Real.log (y : ℝ)

theorem harperCompleteEulerDensity_nonneg
    (y : ℕ) (omega : Omega) (t : ℝ) :
    0 ≤ harperCompleteEulerDensity y omega t := by
  unfold harperCompleteEulerDensity harperCompleteEulerFactor
  exact Finset.prod_nonneg fun p hp ↦ Complex.normSq_nonneg _

theorem continuous_harperSquareCorrectionFactor_vertical
    (omega : Omega) {p : ℕ} (hp : p.Prime) :
    Continuous (fun t : ℝ ↦ harperSquareCorrectionFactor omega p t) := by
  rw [show (fun t : ℝ ↦ harperSquareCorrectionFactor omega p t) =
      fun t ↦ (harperSquareCorrectionDenominator p t)⁻¹ by
    funext t
    exact harperSquareCorrectionFactor_eq omega hp.pos t]
  apply Continuous.inv₀
  · unfold harperSquareCorrectionDenominator
    fun_prop
  · intro t
    exact (harperSquareCorrectionDenominator_pos hp t).ne'

theorem continuous_harperSquareCorrectionDensity_vertical
    (y : ℕ) (omega : Omega) :
    Continuous (fun t : ℝ ↦ harperSquareCorrectionDensity y omega t) := by
  unfold harperSquareCorrectionDensity
  exact continuous_finset_prod (y + 1).primesBelow fun p hp ↦
    continuous_harperSquareCorrectionFactor_vertical omega
      (Nat.prime_of_mem_primesBelow hp)

theorem continuous_harperCompleteEulerDensity_vertical
    (y : ℕ) (omega : Omega) :
    Continuous (fun t : ℝ ↦ harperCompleteEulerDensity y omega t) := by
  rw [show (fun t : ℝ ↦ harperCompleteEulerDensity y omega t) =
      fun t ↦ harperSquareCorrectionDensity y omega t *
        Problem520.harperEulerDensity y omega t by
    funext t
    exact harperCompleteEulerDensity_eq_square_mul_squarefree y omega t]
  exact (continuous_harperSquareCorrectionDensity_vertical y omega).mul
    (Problem520.continuous_harperEulerDensity_vertical y omega)

theorem integrableOn_harperCompleteEulerDensity_lowerBand
    (y : ℕ) (omega : Omega) :
    IntegrableOn (harperCompleteEulerDensity y omega)
      harperLowerVerticalBand := by
  rw [show harperLowerVerticalBand =
      Set.Icc ((1 : ℝ) / 3) ((1 : ℝ) / 2) by rfl]
  exact (continuous_harperCompleteEulerDensity_vertical y omega).continuousOn
    |>.integrableOn_compact isCompact_Icc

/-- A pointwise lower bound for the deterministic square correction transfers
directly to a lower bound for the corresponding normalized band energies. -/
theorem mul_harperEulerSetEnergy_le_complete_of_squareCorrection_lower
    {y : ℕ} (hy : 1 < y) {kappa : ℝ}
    (omega : Omega)
    (hlower : ∀ t ∈ harperLowerVerticalBand,
      kappa ≤ harperSquareCorrectionDensity y omega t) :
    kappa * Problem520.harperEulerSetEnergy
        y harperLowerVerticalBand omega ≤
      harperCompleteEulerSetEnergy y harperLowerVerticalBand omega := by
  let squarefree : ℝ → ℝ := fun t ↦
    Problem520.harperEulerDensity y omega t
  let complete : ℝ → ℝ := fun t ↦
    harperCompleteEulerDensity y omega t
  have hsquarefree : IntegrableOn squarefree harperLowerVerticalBand := by
    rw [show harperLowerVerticalBand =
        Set.Icc ((1 : ℝ) / 3) ((1 : ℝ) / 2) by rfl]
    exact (Problem520.continuous_harperEulerDensity_vertical y omega).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hcomplete : IntegrableOn complete harperLowerVerticalBand := by
    simpa only [complete] using
      integrableOn_harperCompleteEulerDensity_lowerBand y omega
  have hpoint : ∀ t ∈ harperLowerVerticalBand,
      kappa * squarefree t ≤ complete t := by
    intro t ht
    rw [show complete t =
        harperSquareCorrectionDensity y omega t * squarefree t by
      simpa only [complete, squarefree] using
        harperCompleteEulerDensity_eq_square_mul_squarefree y omega t]
    exact mul_le_mul_of_nonneg_right (hlower t ht)
      (Problem520.harperEulerDensity_nonneg y omega t)
  have hint :
      (∫ t in harperLowerVerticalBand, kappa * squarefree t) ≤
        ∫ t in harperLowerVerticalBand, complete t :=
    setIntegral_mono_on (hsquarefree.const_mul kappa) hcomplete
      measurableSet_harperLowerVerticalBand hpoint
  rw [integral_const_mul] at hint
  have hlog : 0 ≤ Real.log (y : ℝ) :=
    (Real.log_pos (by exact_mod_cast hy)).le
  unfold Problem520.harperEulerSetEnergy harperCompleteEulerSetEnergy
  change kappa * ((∫ t in harperLowerVerticalBand, squarefree t) /
      Real.log (y : ℝ)) ≤
    (∫ t in harperLowerVerticalBand, complete t) / Real.log (y : ℝ)
  calc
    kappa * ((∫ t in harperLowerVerticalBand, squarefree t) /
        Real.log (y : ℝ)) =
      (kappa * ∫ t in harperLowerVerticalBand, squarefree t) /
        Real.log (y : ℝ) := by ring
    _ ≤ (∫ t in harperLowerVerticalBand, complete t) /
        Real.log (y : ℝ) := div_le_div_of_nonneg_right hint hlog

private theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
      omega

private theorem self_le_harperBlockEndpoint (j : ℕ) :
    j ≤ Problem520.harperBlockEndpoint j := by
  unfold Problem520.harperBlockEndpoint
  have hmiddle : j ≤ 16 * 2 ^ j := by
    have hpow := self_le_two_pow j
    have hpos : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
    omega
  exact hmiddle.trans (self_le_two_pow (16 * 2 ^ j))

/-- The one-height squarefree theorem therefore survives unchanged, up to a
fixed constant, for the complete Euler product along a cofinal scheduled
sequence.  This is the analytic payoff of separating the squarefree kernel
from the independent screen randomness. -/
theorem
    exists_harperCompleteLowerVerticalBandEnergy_fixedProbability_unconditional :
    ∃ delta : ℝ, 0 < delta ∧ ∃ c : ℝ, 0 < c ∧ ∃ start : ℕ,
      ∀ n : ℕ,
        delta ≤ Problem520.μ.real
          {omega |
            c * harperInitialCriticalScale
                (Problem520.harperBlockEndpoint (start + n)) ≤
              harperCompleteEulerSetEnergy
                (Problem520.harperBlockEndpoint (start + n))
                harperLowerVerticalBand omega} := by
  obtain ⟨delta, hdelta, c, hc, Y, hlowerEnergy⟩ :=
    exists_harperLowerVerticalBandEnergy_fixedProbability_unconditional
  obtain ⟨kappa, hkappa, start₀, hlowerCorrection⟩ :=
    exists_harperSquareCorrectionDensity_scheduled_lower
  let start : ℕ := start₀ + Y
  refine ⟨delta, hdelta, kappa * c, mul_pos hkappa hc, start, ?_⟩
  intro n
  let y : ℕ := Problem520.harperBlockEndpoint (start + n)
  have hYindex : Y ≤ start + n := by dsimp [start]; omega
  have hYy : Y ≤ y :=
    hYindex.trans (self_le_harperBlockEndpoint (start + n))
  have hy4 : 4 ≤ y := by
    exact (by omega : 4 ≤ 16).trans
      (Problem520.harperBlockEndpoint_ge_sixteen (start + n))
  have hprob := hlowerEnergy y hYy hy4
  have hcorrection : ∀ omega : Omega, ∀ t ∈ harperLowerVerticalBand,
      kappa ≤ harperSquareCorrectionDensity y omega t := by
    intro omega t ht
    have hindex : start + n = start₀ + (Y + n) := by
      dsimp [start]
      omega
    simpa only [y, hindex] using
      hlowerCorrection (Y + n) omega t ht
  have hsubset :
      {omega |
        c * harperInitialCriticalScale y ≤
          Problem520.harperEulerSetEnergy
            y harperLowerVerticalBand omega} ⊆
      {omega |
        (kappa * c) * harperInitialCriticalScale y ≤
          harperCompleteEulerSetEnergy
            y harperLowerVerticalBand omega} := by
    intro omega homega
    have htransfer :=
      mul_harperEulerSetEnergy_le_complete_of_squareCorrection_lower
        (show 1 < y by omega) omega (hcorrection omega)
    have hmul :
        kappa * (c * harperInitialCriticalScale y) ≤
          kappa * Problem520.harperEulerSetEnergy
            y harperLowerVerticalBand omega :=
      mul_le_mul_of_nonneg_left homega hkappa.le
    change (kappa * c) * harperInitialCriticalScale y ≤ _
    rw [mul_assoc]
    exact hmul.trans htransfer
  change delta ≤ Problem520.μ.real
    {omega |
      (kappa * c) * harperInitialCriticalScale y ≤
        harperCompleteEulerSetEnergy y harperLowerVerticalBand omega}
  exact hprob.trans (measureReal_mono hsubset)

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperCompleteEulerFactor_eq_square_mul_squarefree
#print axioms Erdos.Problem1144.harperCompleteEulerDensity_eq_square_mul_squarefree
#print axioms Erdos.Problem1144.exists_harperSquareCorrectionDensity_scheduled_lower
#print axioms Erdos.Problem1144.exists_harperCompleteLowerVerticalBandEnergy_fixedProbability_unconditional
