import Erdos.Problem1144.HarperCompleteCauchyEnergy
import Erdos.Problem1144.HarperMiddlePrimeScreen

open Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Erdos
namespace Problem1144

/-!
# Finite complete-model Harman--Parseval

The complete Euler product has an infinite smooth Dirichlet-series expansion.
This file isolates the wholly finite part of that statement: truncate by the
integer carried by the Dirichlet coefficient, expand the squared norm, and
apply the already-verified finite Harman--Parseval theorem.  No limit or
interchange of infinite sums occurs here.
-/

/-- The critical complete Dirichlet coefficient as a multiplicative map with
zero.  This is the exact coefficient whose prime value is Harper's complex
prime term. -/
noncomputable def harperCompleteCoefficientHom
    (omega : Omega) (t : ℝ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else
    ((f omega n / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      Complex.exp ((-(t * Real.log (n : ℝ)) : ℝ) * Complex.I)
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    have hmPos : 0 < m := Nat.pos_of_ne_zero hm
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmPos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
    simp only [hm, hn, mul_eq_zero, or_false, if_false]
    rw [f_mul_of_ne_zero omega hm hn, Nat.cast_mul,
      Real.sqrt_mul hmR.le, Real.log_mul hmR.ne' hnR.ne']
    rw [show
      ((-(t * (Real.log (m : ℝ) + Real.log (n : ℝ))) : ℝ) : ℂ) *
          Complex.I =
        (((-(t * Real.log (m : ℝ)) : ℝ) : ℂ) * Complex.I) +
          (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
    rw [Complex.exp_add]
    have hsm : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.2 hmR).ne'
    have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
    push_cast
    field_simp

theorem harperCompleteCoefficientHom_apply_prime
    (omega : Omega) {p : ℕ} (hp : p.Prime) (t : ℝ) :
    harperCompleteCoefficientHom omega t p =
      Problem520.harperComplexPrimeTerm omega p t := by
  change (if p = 0 then 0 else
    ((f omega p / Real.sqrt (p : ℝ) : ℝ) : ℂ) *
      Complex.exp ((-(t * Real.log (p : ℝ)) : ℝ) * Complex.I)) = _
  rw [if_neg hp.ne_zero]
  rw [f_prime omega hp, eps_eq_problem520_epsilon]
  rfl

theorem norm_harperCompleteCoefficientHom_of_pos
    (omega : Omega) (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖harperCompleteCoefficientHom omega t n‖ =
      (Real.sqrt (n : ℝ))⁻¹ := by
  change ‖(if n = 0 then 0 else
    ((f omega n / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      Complex.exp ((-(t * Real.log (n : ℝ)) : ℝ) * Complex.I))‖ = _
  rw [if_neg hn.ne', norm_mul,
    Complex.norm_exp_ofReal_mul_I]
  simp only [mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_div, abs_f, abs_of_pos (Real.sqrt_pos.2 (by exact_mod_cast hn))]
  simp

/-- The complex complete Euler product before taking its squared norm. -/
noncomputable def harperCompleteEulerProduct
    (y : ℕ) (omega : Omega) (t : ℝ) : ℂ :=
  ∏ p ∈ (y + 1).primesBelow,
    (1 - Problem520.harperComplexPrimeTerm omega p t)⁻¹

theorem harperCompleteEulerDensity_eq_normSq_product
    (y : ℕ) (omega : Omega) (t : ℝ) :
    harperCompleteEulerDensity y omega t =
      Complex.normSq (harperCompleteEulerProduct y omega t) := by
  classical
  unfold harperCompleteEulerDensity harperCompleteEulerFactor
    harperCompleteEulerProduct
  rw [map_prod]

/-- Absolute convergence and exact Euler-product summation over the complete
smooth-number subtype. -/
theorem summable_and_hasSum_harperCompleteCoefficientHom_smooth
    (y : ℕ) (omega : Omega) (t : ℝ) :
    Summable (fun m : (y + 1).smoothNumbers ↦
        ‖harperCompleteCoefficientHom omega t m‖) ∧
      HasSum (fun m : (y + 1).smoothNumbers ↦
        harperCompleteCoefficientHom omega t m)
        (harperCompleteEulerProduct y omega t) := by
  have hprime : ∀ {p : ℕ}, p.Prime →
      ‖harperCompleteCoefficientHom omega t p‖ < 1 := by
    intro p hp
    rw [harperCompleteCoefficientHom_apply_prime omega hp t,
      Problem520.norm_harperComplexPrimeTerm omega hp.pos t]
    have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hsqrt : (1 : ℝ) < Real.sqrt (p : ℝ) := by
      rw [Real.lt_sqrt (by norm_num)]
      simpa using hpR
    exact (inv_lt_one₀ (Real.sqrt_pos.2 (by positivity))).2 hsqrt
  have h :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
      (f := (harperCompleteCoefficientHom omega t).toMonoidHom) hprime (y + 1)
  constructor
  · simpa using h.1
  · have hproduct :
        (∏ p ∈ (y + 1).primesBelow,
          (1 - (harperCompleteCoefficientHom omega t).toMonoidHom p)⁻¹) =
            harperCompleteEulerProduct y omega t := by
        unfold harperCompleteEulerProduct
        apply Finset.prod_congr rfl
        intro p hp
        change (1 - harperCompleteCoefficientHom omega t p)⁻¹ = _
        rw [harperCompleteCoefficientHom_apply_prime omega
          (Nat.prime_of_mem_primesBelow hp) t]
    rw [← hproduct]
    simpa using h.2

/-- Positive `y`-smooth integers at most `M`. -/
noncomputable def completeSmoothSupport (y M : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 M).filter (fun n ↦ IsXSmooth y n)

theorem mem_completeSmoothSupport {y M n : ℕ} :
    n ∈ completeSmoothSupport y M ↔
      1 ≤ n ∧ n ≤ M ∧ IsXSmooth y n := by
  classical
  rw [completeSmoothSupport, Finset.mem_filter, Finset.mem_Icc]
  aesop

theorem mem_smoothNumbers_succ_iff_isXSmooth
    {y n : ℕ} (hn : n ≠ 0) :
    n ∈ (y + 1).smoothNumbers ↔ IsXSmooth y n := by
  constructor
  · intro hsmooth p hp
    have hpBelow := Nat.primeFactors_subset_of_mem_smoothNumbers hsmooth hp
    exact Nat.le_of_lt_succ (Nat.mem_primesBelow.mp hpBelow).1
  · intro hsmooth
    apply Nat.mem_smoothNumbers_of_primeFactors_subset hn
    intro p hp
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hsmooth p hp)

/-- The complete-model Dirichlet polynomial truncated at coefficient index
`M`.  The sign of the vertical phase is immaterial after taking the squared
norm; the positive convention makes the cosine expansion literal. -/
noncomputable def harperCompleteFiniteDirichletPolynomial
    (y M : ℕ) (omega : Omega) (t : ℝ) : ℂ :=
  ∑ n ∈ completeSmoothSupport y M,
    ((f omega n / Real.sqrt (n : ℝ) : ℝ) : ℂ) *
      Complex.exp ((-(t * Real.log (n : ℝ)) : ℝ) * Complex.I)

/-- The expanded real density of the number-truncated complete Dirichlet
polynomial. -/
noncomputable def harperCompleteFiniteCosineDensity
    (y M : ℕ) (omega : Omega) (t : ℝ) : ℝ :=
  ∑ n ∈ completeSmoothSupport y M,
    ∑ m ∈ completeSmoothSupport y M,
      (f omega n * f omega m /
          (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ))) *
        Real.cos
          (t * (Real.log (n : ℝ) - Real.log (m : ℝ)))

/-- The finite inverse-maximum energy corresponding to the same coefficient
truncation. -/
noncomputable def harperCompleteFiniteMaxEnergy
    (y M : ℕ) (omega : Omega) : ℝ :=
  ∑ n ∈ completeSmoothSupport y M,
    ∑ m ∈ completeSmoothSupport y M,
      f omega n * f omega m / max (n : ℝ) (m : ℝ)

theorem harperCompleteFiniteDirichletPolynomial_eq_sum_coefficientHom
    (y M : ℕ) (omega : Omega) (t : ℝ) :
    harperCompleteFiniteDirichletPolynomial y M omega t =
      ∑ n ∈ completeSmoothSupport y M,
        harperCompleteCoefficientHom omega t n := by
  classical
  unfold harperCompleteFiniteDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n :=
    lt_of_lt_of_le Nat.zero_lt_one (mem_completeSmoothSupport.mp hn).1
  change _ = if n = 0 then 0 else _
  rw [if_neg hnPos.ne']

/-- Extend the smooth-subtype coefficient series by zero to all naturals. -/
noncomputable def harperCompleteCoefficientSeries
    (y : ℕ) (omega : Omega) (t : ℝ) (n : ℕ) : ℂ :=
  if n ∈ (y + 1).smoothNumbers then
    harperCompleteCoefficientHom omega t n else 0

theorem norm_harperCompleteCoefficientSeries_independent_vertical
    (y : ℕ) (omega : Omega) (t s : ℝ) (n : ℕ) :
    ‖harperCompleteCoefficientSeries y omega t n‖ =
      ‖harperCompleteCoefficientSeries y omega s n‖ := by
  unfold harperCompleteCoefficientSeries
  split_ifs with hsmooth
  · have hn : 0 < n := Nat.pos_of_ne_zero
      (Nat.ne_zero_of_mem_smoothNumbers hsmooth)
    rw [norm_harperCompleteCoefficientHom_of_pos omega t hn,
      norm_harperCompleteCoefficientHom_of_pos omega s hn]
  · rfl

theorem hasSum_harperCompleteCoefficientSeries
    (y : ℕ) (omega : Omega) (t : ℝ) :
    HasSum (harperCompleteCoefficientSeries y omega t)
      (harperCompleteEulerProduct y omega t) := by
  let g : (y + 1).smoothNumbers → ℕ := fun m ↦ m.1
  have hg : Function.Injective g := by
    intro a b hab
    exact Subtype.ext hab
  have hout : ∀ n ∉ Set.range g,
      harperCompleteCoefficientSeries y omega t n = 0 := by
    intro n hnRange
    unfold harperCompleteCoefficientSeries
    split_ifs with hsmooth
    · exact False.elim (hnRange ⟨⟨n, hsmooth⟩, rfl⟩)
    · rfl
  have hsub :=
    (summable_and_hasSum_harperCompleteCoefficientHom_smooth
      y omega t).2
  apply (hg.hasSum_iff hout).mp
  apply hsub.congr_fun
  intro m
  simp [g, harperCompleteCoefficientSeries, m.property]

theorem sum_range_harperCompleteCoefficientSeries_eq_polynomial
    (y M : ℕ) (omega : Omega) (t : ℝ) :
    (∑ n ∈ Finset.range (M + 1),
      harperCompleteCoefficientSeries y omega t n) =
        harperCompleteFiniteDirichletPolynomial y M omega t := by
  classical
  rw [harperCompleteFiniteDirichletPolynomial_eq_sum_coefficientHom]
  unfold harperCompleteCoefficientSeries
  rw [← Finset.sum_filter]
  congr 1
  ext n
  rw [Finset.mem_filter, Finset.mem_range,
    mem_completeSmoothSupport]
  constructor
  · rintro ⟨hnM, hsmooth⟩
    have hn0 : n ≠ 0 := Nat.ne_zero_of_mem_smoothNumbers hsmooth
    exact ⟨Nat.one_le_iff_ne_zero.mpr hn0, Nat.le_of_lt_succ hnM,
      (mem_smoothNumbers_succ_iff_isXSmooth hn0).mp hsmooth⟩
  · rintro ⟨hn1, hnM, hsmooth⟩
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
    exact ⟨Nat.lt_succ_of_le hnM,
      (mem_smoothNumbers_succ_iff_isXSmooth hn0).mpr hsmooth⟩

/-- Number truncations of the complete critical Dirichlet series converge
pointwise to the literal finite Euler product. -/
theorem tendsto_harperCompleteFiniteDirichletPolynomial
    (y : ℕ) (omega : Omega) (t : ℝ) :
    Filter.Tendsto
      (fun M ↦ harperCompleteFiniteDirichletPolynomial y M omega t)
      Filter.atTop (nhds (harperCompleteEulerProduct y omega t)) := by
  have h := (hasSum_harperCompleteCoefficientSeries y omega t).tendsto_sum_nat
  have hshift := h.comp (Filter.tendsto_add_atTop_nat 1)
  apply hshift.congr
  intro M
  exact sum_range_harperCompleteCoefficientSeries_eq_polynomial
    y M omega t

theorem summable_norm_harperCompleteCoefficientSeries
    (y : ℕ) (omega : Omega) (t : ℝ) :
    Summable (fun n : ℕ ↦
      ‖harperCompleteCoefficientSeries y omega t n‖) := by
  let g : (y + 1).smoothNumbers → ℕ := fun m ↦ m.1
  have hg : Function.Injective g := by
    intro a b hab
    exact Subtype.ext hab
  let F : ℕ → ℝ := fun n ↦
    ‖harperCompleteCoefficientSeries y omega t n‖
  have hout : ∀ n ∉ Set.range g, F n = 0 := by
    intro n hnRange
    unfold F harperCompleteCoefficientSeries
    split_ifs with hsmooth
    · exact False.elim (hnRange ⟨⟨n, hsmooth⟩, rfl⟩)
    · simp
  have hsub :=
    (summable_and_hasSum_harperCompleteCoefficientHom_smooth
      y omega t).1
  have hsubHas : HasSum
      (fun m : (y + 1).smoothNumbers ↦
        ‖harperCompleteCoefficientHom omega t m‖)
      (∑' m : (y + 1).smoothNumbers,
        ‖harperCompleteCoefficientHom omega t m‖) := hsub.hasSum
  have hcomp : HasSum (F ∘ g)
      (∑' m : (y + 1).smoothNumbers,
        ‖harperCompleteCoefficientHom omega t m‖) := by
    apply hsubHas.congr_fun
    intro m
    simp [F, g, harperCompleteCoefficientSeries, m.property]
  exact ((hg.hasSum_iff hout).mp hcomp).summable

/-- A single absolute-series constant dominates every number truncation of
the complete Dirichlet polynomial. -/
theorem norm_harperCompleteFiniteDirichletPolynomial_le_tsum
    (y M : ℕ) (omega : Omega) (t : ℝ) :
    ‖harperCompleteFiniteDirichletPolynomial y M omega t‖ ≤
      ∑' n : ℕ, ‖harperCompleteCoefficientSeries y omega t n‖ := by
  rw [← sum_range_harperCompleteCoefficientSeries_eq_polynomial]
  exact (norm_sum_le _ _).trans
    ((summable_norm_harperCompleteCoefficientSeries y omega t).sum_le_tsum
      (Finset.range (M + 1)) (fun n hn ↦ norm_nonneg _))

/-- A vertical-parameter-independent absolute-series majorant. -/
noncomputable def harperCompleteAbsoluteCoefficientSum
    (y : ℕ) (omega : Omega) : ℝ :=
  ∑' n : ℕ, ‖harperCompleteCoefficientSeries y omega 0 n‖

theorem tsum_norm_harperCompleteCoefficientSeries_eq_absoluteSum
    (y : ℕ) (omega : Omega) (t : ℝ) :
    (∑' n : ℕ, ‖harperCompleteCoefficientSeries y omega t n‖) =
      harperCompleteAbsoluteCoefficientSum y omega := by
  unfold harperCompleteAbsoluteCoefficientSum
  apply tsum_congr
  intro n
  exact norm_harperCompleteCoefficientSeries_independent_vertical
    y omega t 0 n

theorem harperCompleteAbsoluteCoefficientSum_nonneg
    (y : ℕ) (omega : Omega) :
    0 ≤ harperCompleteAbsoluteCoefficientSum y omega := by
  unfold harperCompleteAbsoluteCoefficientSum
  exact tsum_nonneg fun n ↦ norm_nonneg _

theorem norm_harperCompleteFiniteDirichletPolynomial_le_absoluteSum
    (y M : ℕ) (omega : Omega) (t : ℝ) :
    ‖harperCompleteFiniteDirichletPolynomial y M omega t‖ ≤
      harperCompleteAbsoluteCoefficientSum y omega := by
  rw [← tsum_norm_harperCompleteCoefficientSeries_eq_absoluteSum y omega t]
  exact norm_harperCompleteFiniteDirichletPolynomial_le_tsum y M omega t

/-- The discrete inverse-square weight on endpoint `N`, with the entire tail
beyond the coefficient cutoff `M` placed at the final endpoint. -/
noncomputable def harperCompleteFiniteEndpointWeight (M N : ℕ) : ℝ :=
  (1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ)) +
    if N = M then 1 / ((M + 1 : ℕ) : ℝ) else 0

theorem harperCompleteFiniteEndpointWeight_nonneg
    {M N : ℕ} (hN : 1 ≤ N) (_hNM : N ≤ M) :
    0 ≤ harperCompleteFiniteEndpointWeight M N := by
  unfold harperCompleteFiniteEndpointWeight
  apply add_nonneg
  · apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
    · exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    · exact_mod_cast Nat.le_succ N
  · split_ifs <;> positivity

/-- The finite endpoint form of the coefficient-truncated energy. -/
noncomputable def harperCompleteFiniteEndpointEnergy
    (y M : ℕ) (omega : Omega) : ℝ :=
  ∑ N ∈ Finset.Icc 1 M,
    harperCompleteFiniteEndpointWeight M N * smoothSum omega y N ^ 2

/-- The endpoint weights telescope to the reciprocal of the lower endpoint.
This is the discrete form of integrating `z⁻²` from that endpoint to
infinity. -/
theorem sum_harperCompleteFiniteEndpointWeight_Icc
    (m M : ℕ) (hmM : m ≤ M) :
    (∑ N ∈ Finset.Icc m M,
      harperCompleteFiniteEndpointWeight M N) = 1 / (m : ℝ) := by
  have hset : Finset.Icc m M = Finset.Ico m (M + 1) := by
    ext N
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have htel :
      (∑ N ∈ Finset.Ico m (M + 1),
        (1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ))) =
          1 / (m : ℝ) - 1 / ((M + 1 : ℕ) : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have h := Finset.sum_range_sub'
      (fun i : ℕ ↦ (1 / ((m + i : ℕ) : ℝ))) (M + 1 - m)
    rw [show m + (M + 1 - m) = M + 1 by omega] at h
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero,
      add_assoc] using h
  rw [hset]
  unfold harperCompleteFiniteEndpointWeight
  simp_rw [Finset.sum_add_distrib]
  rw [htel]
  have hMmem : M ∈ Finset.Ico m (M + 1) := by simp [hmM]
  simp [hMmem]

/-- A smaller complete smooth sum can be written over a fixed larger support
by inserting the natural cutoff indicator. -/
theorem smoothSum_eq_sum_completeSmoothSupport_indicator
    (omega : Omega) (y : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    smoothSum omega y N =
      ∑ n ∈ completeSmoothSupport y M,
        if n ≤ N then f omega n else 0 := by
  classical
  have hsupport :
      completeSmoothSupport y N =
        (completeSmoothSupport y M).filter (fun n ↦ n ≤ N) := by
    ext n
    simp only [mem_completeSmoothSupport, Finset.mem_filter]
    constructor
    · rintro ⟨hn1, hnN, hsmooth⟩
      exact ⟨⟨hn1, hnN.trans hNM, hsmooth⟩, hnN⟩
    · rintro ⟨⟨hn1, hnM, hsmooth⟩, hnN⟩
      exact ⟨hn1, hnN, hsmooth⟩
  change (∑ n ∈ completeSmoothSupport y N, f omega n) = _
  rw [hsupport, Finset.sum_filter]

/-- Expanding a complete smooth partial-sum square on a fixed finite support
produces the expected maximum-cutoff indicator. -/
theorem smoothSum_sq_eq_sum_completeSmoothSupport_maxIndicator
    (omega : Omega) (y : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    smoothSum omega y N ^ 2 =
      ∑ n ∈ completeSmoothSupport y M,
        ∑ m ∈ completeSmoothSupport y M,
          if max n m ≤ N then f omega n * f omega m else 0 := by
  rw [smoothSum_eq_sum_completeSmoothSupport_indicator omega y hNM,
    pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hnN : n ≤ N <;> by_cases hmN : m ≤ N <;>
    simp [hnN, hmN]

private theorem normSq_sum_real_mul_exp_complete
    {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    Complex.normSq
        (∑ i ∈ s, ((a i : ℝ) : ℂ) *
          Complex.exp ((b i : ℝ) * Complex.I)) =
      ∑ i ∈ s, ∑ j ∈ s,
        a i * a j * Real.cos (b i - b j) := by
  classical
  have hre :
      (∑ i ∈ s, ((a i : ℝ) : ℂ) *
          Complex.exp ((b i : ℝ) * Complex.I)).re =
        ∑ i ∈ s, a i * Real.cos (b i) := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  have him :
      (∑ i ∈ s, ((a i : ℝ) : ℂ) *
          Complex.exp ((b i : ℝ) * Complex.I)).im =
        ∑ i ∈ s, a i * Real.sin (b i) := by
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  rw [Complex.normSq_apply, hre, him]
  calc
    (∑ i ∈ s, a i * Real.cos (b i)) *
          (∑ j ∈ s, a j * Real.cos (b j)) +
        (∑ i ∈ s, a i * Real.sin (b i)) *
          (∑ j ∈ s, a j * Real.sin (b j)) =
        (∑ i ∈ s, ∑ j ∈ s,
          (a i * Real.cos (b i)) * (a j * Real.cos (b j))) +
        (∑ i ∈ s, ∑ j ∈ s,
          (a i * Real.sin (b i)) * (a j * Real.sin (b j))) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s,
          ((a i * Real.cos (b i)) * (a j * Real.cos (b j)) +
            (a i * Real.sin (b i)) * (a j * Real.sin (b j))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
    _ = ∑ i ∈ s, ∑ j ∈ s,
          a i * a j * Real.cos (b i - b j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.cos_sub]
      ring

/-- The finite complete cosine density is literally the squared norm of its
Dirichlet polynomial. -/
theorem harperCompleteFiniteCosineDensity_eq_normSq
    (y M : ℕ) (omega : Omega) (t : ℝ) :
    harperCompleteFiniteCosineDensity y M omega t =
      Complex.normSq
        (harperCompleteFiniteDirichletPolynomial y M omega t) := by
  classical
  unfold harperCompleteFiniteCosineDensity
    harperCompleteFiniteDirichletPolynomial
  rw [normSq_sum_real_mul_exp_complete]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  congr 1
  · ring
  · rw [show
      -(t * Real.log (n : ℝ)) - -(t * Real.log (m : ℝ)) =
        -(t * (Real.log (n : ℝ) - Real.log (m : ℝ))) by ring,
      Real.cos_neg]

theorem harperCompleteFiniteCosineDensity_le_absoluteSum_sq
    (y M : ℕ) (omega : Omega) (t : ℝ) :
    harperCompleteFiniteCosineDensity y M omega t ≤
      harperCompleteAbsoluteCoefficientSum y omega ^ 2 := by
  rw [harperCompleteFiniteCosineDensity_eq_normSq, ← Complex.sq_norm]
  exact (sq_le_sq₀ (norm_nonneg _)
    (harperCompleteAbsoluteCoefficientSum_nonneg y omega)).2
      (norm_harperCompleteFiniteDirichletPolynomial_le_absoluteSum
        y M omega t)

theorem tendsto_harperCompleteFiniteCosineDensity
    (y : ℕ) (omega : Omega) (t : ℝ) :
    Filter.Tendsto
      (fun M ↦ harperCompleteFiniteCosineDensity y M omega t)
      Filter.atTop (nhds (harperCompleteEulerDensity y omega t)) := by
  rw [harperCompleteEulerDensity_eq_normSq_product]
  have h := tendsto_harperCompleteFiniteDirichletPolynomial y omega t
  have hnormSq :=
    Complex.continuous_normSq.continuousAt.tendsto.comp h
  apply hnormSq.congr
  intro M
  exact (harperCompleteFiniteCosineDensity_eq_normSq y M omega t).symm

theorem harperCompleteFiniteCosineDensity_nonneg
    (y M : ℕ) (omega : Omega) (t : ℝ) :
    0 ≤ harperCompleteFiniteCosineDensity y M omega t := by
  rw [harperCompleteFiniteCosineDensity_eq_normSq]
  exact Complex.normSq_nonneg _

theorem continuous_harperCompleteFiniteCosineDensity
    (y M : ℕ) (omega : Omega) :
    Continuous (fun t : ℝ ↦
      harperCompleteFiniteCosineDensity y M omega t) := by
  unfold harperCompleteFiniteCosineDensity
  fun_prop

/-- Dominated convergence through the Cauchy kernel upgrades pointwise
Dirichlet-series convergence to convergence of the exact Parseval energies. -/
theorem tendsto_integral_harperCompleteFiniteCosineDensity
    (y : ℕ) (omega : Omega) :
    Filter.Tendsto
      (fun M ↦ ∫ t : ℝ,
        harperCompleteFiniteCosineDensity y M omega t /
          ((1 / 4 : ℝ) + t ^ 2))
      Filter.atTop
      (nhds (∫ t : ℝ,
        harperCompleteEulerDensity y omega t /
          ((1 / 4 : ℝ) + t ^ 2))) := by
  let A : ℝ := harperCompleteAbsoluteCoefficientSum y omega
  let bound : ℝ → ℝ := fun t ↦
    A ^ 2 * (1 / ((1 / 4 : ℝ) + t ^ 2))
  have hboundIntegrable : Integrable bound := by
    have hkernel : Integrable (fun t : ℝ ↦
        1 / ((1 / 4 : ℝ) + t ^ 2)) := by
      simpa only [show ((1 / 2 : ℝ) ^ 2) = 1 / 4 by norm_num] using
        Problem520.integrable_one_div_harperCauchyKernel
    exact hkernel.const_mul (A ^ 2)
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
  · exact Filter.Eventually.of_forall fun M ↦
      ((continuous_harperCompleteFiniteCosineDensity y M omega).div
        (by fun_prop) (fun t ↦ ne_of_gt (by positivity))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun M ↦ ae_of_all _ fun t ↦ by
      have hden : 0 < (1 / 4 : ℝ) + t ^ 2 := by positivity
      have hnonneg : 0 ≤ harperCompleteFiniteCosineDensity y M omega t /
          ((1 / 4 : ℝ) + t ^ 2) :=
        div_nonneg
          (harperCompleteFiniteCosineDensity_nonneg y M omega t) hden.le
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      change harperCompleteFiniteCosineDensity y M omega t /
          ((1 / 4 : ℝ) + t ^ 2) ≤
        A ^ 2 * (1 / ((1 / 4 : ℝ) + t ^ 2))
      rw [show A = harperCompleteAbsoluteCoefficientSum y omega by rfl]
      calc
        harperCompleteFiniteCosineDensity y M omega t /
              ((1 / 4 : ℝ) + t ^ 2) ≤
            harperCompleteAbsoluteCoefficientSum y omega ^ 2 /
              ((1 / 4 : ℝ) + t ^ 2) :=
          (div_le_div_iff_of_pos_right hden).2
            (harperCompleteFiniteCosineDensity_le_absoluteSum_sq
              y M omega t)
        _ = harperCompleteAbsoluteCoefficientSum y omega ^ 2 *
              (1 / ((1 / 4 : ℝ) + t ^ 2)) := by ring
  · exact hboundIntegrable
  · exact ae_of_all _ fun t ↦
      (tendsto_harperCompleteFiniteCosineDensity y omega t).div_const
        ((1 / 4 : ℝ) + t ^ 2)

/-- Exact finite Harman--Parseval for complete smooth coefficients. -/
theorem integral_harperCompleteFiniteCosineDensity_div_cauchyKernel
    (y M : ℕ) (omega : Omega) :
    (∫ t : ℝ, harperCompleteFiniteCosineDensity y M omega t /
        ((1 / 4 : ℝ) + t ^ 2)) =
      2 * Real.pi * harperCompleteFiniteMaxEnergy y M omega := by
  classical
  let P := completeSmoothSupport y M
  have hpos (n : ℕ) (hn : n ∈ P) : 0 < (n : ℝ) := by
    have hn1 : 1 ≤ n := (mem_completeSmoothSupport.mp hn).1
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have h := Problem520.integral_finiteDirichletCosineDensity P
    (fun n ↦ f omega n) (fun n ↦ (n : ℝ)) hpos
  simpa only [P, harperCompleteFiniteCosineDensity,
    harperCompleteFiniteMaxEnergy] using h

/-- The inverse-maximum coefficient energy is exactly the finite weighted
endpoint energy.  This is finite Abel summation, with no analytic limit. -/
theorem harperCompleteFiniteEndpointEnergy_eq_maxEnergy
    (y M : ℕ) (omega : Omega) :
    harperCompleteFiniteEndpointEnergy y M omega =
      harperCompleteFiniteMaxEnergy y M omega := by
  classical
  let P := completeSmoothSupport y M
  let T := Finset.Icc 1 M
  unfold harperCompleteFiniteEndpointEnergy
    harperCompleteFiniteMaxEnergy
  change
    (∑ N ∈ T,
      harperCompleteFiniteEndpointWeight M N * smoothSum omega y N ^ 2) =
      ∑ n ∈ P, ∑ m ∈ P,
        f omega n * f omega m / max (n : ℝ) (m : ℝ)
  calc
    (∑ N ∈ T,
        harperCompleteFiniteEndpointWeight M N * smoothSum omega y N ^ 2) =
        ∑ N ∈ T, harperCompleteFiniteEndpointWeight M N *
          ∑ n ∈ P, ∑ m ∈ P,
            if max n m ≤ N then f omega n * f omega m else 0 := by
      apply Finset.sum_congr rfl
      intro N hN
      rw [smoothSum_sq_eq_sum_completeSmoothSupport_maxIndicator
        omega y (Finset.mem_Icc.mp hN).2]
    _ = ∑ n ∈ P, ∑ m ∈ P, ∑ N ∈ T,
          harperCompleteFiniteEndpointWeight M N *
            (if max n m ≤ N then f omega n * f omega m else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_comm]
    _ = ∑ n ∈ P, ∑ m ∈ P,
          (f omega n * f omega m) *
            ∑ N ∈ T,
              if max n m ≤ N then
                harperCompleteFiniteEndpointWeight M N else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      by_cases hmax : max n m ≤ N <;> simp [hmax] <;> ring
    _ = ∑ n ∈ P, ∑ m ∈ P,
          f omega n * f omega m / max (n : ℝ) (m : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      have hnData := mem_completeSmoothSupport.mp hn
      have hmData := mem_completeSmoothSupport.mp hm
      have hmaxOne : 1 ≤ max n m := le_max_of_le_left hnData.1
      have hmaxM : max n m ≤ M := max_le hnData.2.1 hmData.2.1
      have hfilter :
          T.filter (fun N ↦ max n m ≤ N) = Finset.Icc (max n m) M := by
        ext N
        simp only [T, Finset.mem_filter, Finset.mem_Icc]
        omega
      have htail :
          (∑ N ∈ T,
            if max n m ≤ N then
              harperCompleteFiniteEndpointWeight M N else 0) =
            1 / ((max n m : ℕ) : ℝ) := by
        rw [← Finset.sum_filter, hfilter,
          sum_harperCompleteFiniteEndpointWeight_Icc (max n m) M hmaxM]
      rw [htail]
      simp only [Nat.cast_max]
      ring

/-- Fully assembled finite Parseval identity in endpoint language. -/
theorem integral_harperCompleteFiniteCosineDensity_eq_endpointEnergy
    (y M : ℕ) (omega : Omega) :
    (∫ t : ℝ, harperCompleteFiniteCosineDensity y M omega t /
        ((1 / 4 : ℝ) + t ^ 2)) =
      2 * Real.pi * harperCompleteFiniteEndpointEnergy y M omega := by
  rw [integral_harperCompleteFiniteCosineDensity_div_cauchyKernel,
    harperCompleteFiniteEndpointEnergy_eq_maxEnergy]

/-- The full complete smooth energy, defined as the limit target singled out
by the finite Parseval theorem. -/
noncomputable def harperCompleteSmoothEnergy
    (y : ℕ) (omega : Omega) : ℝ :=
  (∫ t : ℝ, harperCompleteEulerDensity y omega t /
      ((1 / 4 : ℝ) + t ^ 2)) / (2 * Real.pi)

theorem tendsto_harperCompleteFiniteEndpointEnergy
    (y : ℕ) (omega : Omega) :
    Filter.Tendsto
      (fun M ↦ harperCompleteFiniteEndpointEnergy y M omega)
      Filter.atTop (nhds (harperCompleteSmoothEnergy y omega)) := by
  have h := (tendsto_integral_harperCompleteFiniteCosineDensity y omega).div_const
    (2 * Real.pi)
  unfold harperCompleteSmoothEnergy
  apply h.congr
  intro M
  rw [integral_harperCompleteFiniteCosineDensity_eq_endpointEnergy]
  field_simp [Real.pi_ne_zero]

/-- Every strict lower bound for the full complete smooth energy is already
seen by a sufficiently long finite coefficient truncation.  This is the soft
localization consequence of complete Parseval; it deliberately makes no
claim that the cutoff lies below `y^2`. -/
theorem exists_completeFiniteEndpointEnergy_gt_of_lt_smoothEnergy
    (y : ℕ) (omega : Omega) {B : ℝ}
    (hB : B < harperCompleteSmoothEnergy y omega) :
    ∃ M : ℕ, B < harperCompleteFiniteEndpointEnergy y M omega := by
  exact ((tendsto_harperCompleteFiniteEndpointEnergy y omega).eventually
    (eventually_gt_nhds hB)).exists

/-- Eventual form of soft finite localization. -/
theorem eventually_completeFiniteEndpointEnergy_gt_of_lt_smoothEnergy
    (y : ℕ) (omega : Omega) {B : ℝ}
    (hB : B < harperCompleteSmoothEnergy y omega) :
    ∀ᶠ M : ℕ in Filter.atTop,
      B < harperCompleteFiniteEndpointEnergy y M omega :=
  (tendsto_harperCompleteFiniteEndpointEnergy y omega).eventually
    (eventually_gt_nhds hB)

theorem harperCompleteCauchyEnergy_eq_smoothEnergy
    (y : ℕ) (omega : Omega) :
    harperCompleteCauchyEnergy y omega =
      2 * Real.pi * harperCompleteSmoothEnergy y omega /
        Real.log (y : ℝ) := by
  unfold harperCompleteCauchyEnergy harperCompleteSmoothEnergy
  field_simp [Real.pi_ne_zero]
  ring

/-- The unconditional complete Cauchy-energy event is equivalently a
fixed-probability lower bound for the full complete smooth endpoint energy. -/
theorem exists_harperCompleteSmoothEnergy_fixedProbability_unconditional :
    ∃ delta : ℝ, 0 < delta ∧ ∃ c : ℝ, 0 < c ∧ ∃ start : ℕ,
      ∀ n : ℕ,
        delta ≤ Problem520.μ.real
          {omega |
            c * harperInitialCriticalScale
                (Problem520.harperBlockEndpoint (start + n)) *
                Real.log
                  (Problem520.harperBlockEndpoint (start + n) : ℝ) ≤
              harperCompleteSmoothEnergy
                (Problem520.harperBlockEndpoint (start + n)) omega} := by
  obtain ⟨delta, hdelta, c, hc, start, henergy⟩ :=
    exists_harperCompleteCauchyEnergy_fixedProbability_unconditional
  let c' : ℝ := c / (2 * Real.pi)
  refine ⟨delta, hdelta, c', div_pos hc (mul_pos (by norm_num) Real.pi_pos),
    start, ?_⟩
  intro n
  let y : ℕ := Problem520.harperBlockEndpoint (start + n)
  have hy : 1 < y := by
    have := Problem520.harperBlockEndpoint_ge_sixteen (start + n)
    omega
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hsubset :
      {omega |
        c * harperInitialCriticalScale y ≤
          harperCompleteCauchyEnergy y omega} ⊆
      {omega |
        c' * harperInitialCriticalScale y * Real.log (y : ℝ) ≤
          harperCompleteSmoothEnergy y omega} := by
    intro omega homega
    change c * harperInitialCriticalScale y ≤
      harperCompleteCauchyEnergy y omega at homega
    change c' * harperInitialCriticalScale y * Real.log (y : ℝ) ≤
      harperCompleteSmoothEnergy y omega
    rw [harperCompleteCauchyEnergy_eq_smoothEnergy] at homega
    calc
      c' * harperInitialCriticalScale y * Real.log (y : ℝ) =
          (c * harperInitialCriticalScale y) * Real.log (y : ℝ) /
            (2 * Real.pi) := by
        dsimp only [c']
        ring
      _ ≤ (2 * Real.pi * harperCompleteSmoothEnergy y omega /
            Real.log (y : ℝ)) * Real.log (y : ℝ) /
              (2 * Real.pi) := by
        gcongr
      _ = harperCompleteSmoothEnergy y omega := by
        field_simp [hlog.ne', htwoPi.ne']
  change delta ≤ Problem520.μ.real
    {omega |
      c' * harperInitialCriticalScale y * Real.log (y : ℝ) ≤
        harperCompleteSmoothEnergy y omega}
  exact (henergy n).trans (measureReal_mono hsubset)

/-- The independent middle-prime screen lifts the exact finite endpoint
energy throughout the sub-square range.  This is the finite deterministic
form of the proposed `X^(1/3)` structural split. -/
theorem card_mul_completeFiniteEndpointEnergy_le_sum_middleScreenWorld
    (omega : Omega) {Y X M : ℕ} (hYX : Y ≤ X) (hM : M < Y ^ 2) :
    ((2 ^ (middlePrimeCoordinates Y X).card : ℕ) : ℝ) *
        harperCompleteFiniteEndpointEnergy Y M omega ≤
      ∑ eta : MiddleScreenWorld (middlePrimeCoordinates Y X),
        harperCompleteFiniteEndpointEnergy X M
          (middleScreenOverwrite
            (middlePrimeCoordinates Y X) eta omega) := by
  have hweight : ∀ N ∈ Finset.Icc 1 M,
      0 ≤ harperCompleteFiniteEndpointWeight M N := by
    intro N hN
    exact harperCompleteFiniteEndpointWeight_nonneg
      (Finset.mem_Icc.mp hN).1 (Finset.mem_Icc.mp hN).2
  have hsubsquare : ∀ N ∈ Finset.Icc 1 M, N < Y ^ 2 := by
    intro N hN
    exact (Finset.mem_Icc.mp hN).2.trans_lt hM
  simpa only [harperCompleteFiniteEndpointEnergy] using
    card_mul_sum_weight_mul_smoothSum_sq_le_sum_middleScreenWorld
      omega hYX (Finset.Icc 1 M)
        (harperCompleteFiniteEndpointWeight M) hweight hsubsquare

/-- Equivalent coefficient-space statement: below the square of the lower
cutoff, the finite complete Parseval energy can only increase on average when
the independent screen primes are adjoined. -/
theorem card_mul_completeFiniteMaxEnergy_le_sum_middleScreenWorld
    (omega : Omega) {Y X M : ℕ} (hYX : Y ≤ X) (hM : M < Y ^ 2) :
    ((2 ^ (middlePrimeCoordinates Y X).card : ℕ) : ℝ) *
        harperCompleteFiniteMaxEnergy Y M omega ≤
      ∑ eta : MiddleScreenWorld (middlePrimeCoordinates Y X),
        harperCompleteFiniteMaxEnergy X M
          (middleScreenOverwrite
            (middlePrimeCoordinates Y X) eta omega) := by
  simpa only [← harperCompleteFiniteEndpointEnergy_eq_maxEnergy] using
    card_mul_completeFiniteEndpointEnergy_le_sum_middleScreenWorld
      omega hYX hM

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperCompleteFiniteCosineDensity_eq_normSq
#print axioms Erdos.Problem1144.integral_harperCompleteFiniteCosineDensity_div_cauchyKernel
#print axioms Erdos.Problem1144.harperCompleteFiniteEndpointEnergy_eq_maxEnergy
#print axioms Erdos.Problem1144.integral_harperCompleteFiniteCosineDensity_eq_endpointEnergy
#print axioms Erdos.Problem1144.harperCompleteCoefficientHom
#print axioms Erdos.Problem1144.summable_and_hasSum_harperCompleteCoefficientHom_smooth
#print axioms Erdos.Problem1144.tendsto_harperCompleteFiniteDirichletPolynomial
#print axioms Erdos.Problem1144.tendsto_integral_harperCompleteFiniteCosineDensity
#print axioms Erdos.Problem1144.tendsto_harperCompleteFiniteEndpointEnergy
#print axioms Erdos.Problem1144.exists_completeFiniteEndpointEnergy_gt_of_lt_smoothEnergy
#print axioms Erdos.Problem1144.exists_harperCompleteSmoothEnergy_fixedProbability_unconditional
#print axioms Erdos.Problem1144.card_mul_completeFiniteEndpointEnergy_le_sum_middleScreenWorld
#print axioms Erdos.Problem1144.card_mul_completeFiniteMaxEnergy_le_sum_middleScreenWorld
