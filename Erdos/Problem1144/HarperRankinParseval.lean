import Erdos.Problem1144.HarperRankinEulerProduct
import Erdos.Problem1144.HarperShiftedCoefficientLocalization
import Erdos.Problem1144.HarperRestrictedGraphEnergy
import Erdos.Problem520.HarperParseval

open Finset MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Harman--Parseval on the Rankin-shifted Euler line

The Rankin shift used to localize the coefficient energy is not merely a
probabilistic tilt.  On the line `Re(s) = (1+a)/2`, the same Cauchy-transform
calculation identifies the full vertical Euler-product mass with the shifted
smooth energy.  This file supplies that deterministic bridge.
-/

private theorem integrableOn_rankinTail
    {m : ℝ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    IntegrableOn (fun z : ℝ ↦
      if m ≤ z then (c / z ^ 2) * z ^ (-a) else 0) (Ioi (1 : ℝ)) := by
  have hexp : -2 - a < (-1 : ℝ) := by linarith
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hpow : IntegrableOn (fun z : ℝ ↦ c * z ^ (-2 - a)) (Ioi m) :=
    (integrableOn_Ioi_rpow_of_lt hexp hm0).const_mul c
  have hpowIci : IntegrableOn (fun z : ℝ ↦ c * z ^ (-2 - a)) (Ici m) :=
    hpow.congr_set_ae Ioi_ae_eq_Ici.symm
  have htermIci : IntegrableOn
      (fun z : ℝ ↦ (c / z ^ 2) * z ^ (-a)) (Ici m) := by
    apply hpowIci.congr_fun
    · intro z hz
      have hzpos : 0 < z := hm0.trans_le hz
      change c * z ^ (-2 - a) = (c / z ^ (2 : ℕ)) * z ^ (-a)
      rw [show z ^ (2 : ℕ) = z ^ (2 : ℝ) by norm_num,
        div_eq_mul_inv, ← Real.rpow_neg hzpos.le]
      calc
        c * z ^ (-2 - a) = c * z ^ ((-2 : ℝ) + (-a)) := by ring
        _ = c * (z ^ (-2 : ℝ) * z ^ (-a)) := by
          rw [Real.rpow_add hzpos]
        _ = c * z ^ (-2 : ℝ) * z ^ (-a) := by ring
    · exact measurableSet_Ici
  rw [← integrable_indicator_iff measurableSet_Ioi]
  have hi := htermIci.integrable_indicator measurableSet_Ici
  apply hi.congr
  filter_upwards [volume.ae_ne (1 : ℝ)] with z hzOne
  by_cases hz : m ≤ z
  · have hz1 : 1 ≤ z := hm.trans hz
    have hzgt : 1 < z := lt_of_le_of_ne hz1 (Ne.symm hzOne)
    simp [Set.indicator, hz, hzgt]
  · simp [Set.indicator, hz]

/-- A Rankin-weighted inverse-square tail.  The lower integration endpoint is
`1`, matching the coefficient energy; every squarefree-product endpoint is
at least `1`. -/
private theorem integral_rankinTail
    {m : ℝ} (hm : 1 ≤ m) {a : ℝ} (ha : 0 ≤ a) (c : ℝ) :
    (∫ z in Ioi (1 : ℝ),
        if m ≤ z then (c / z ^ 2) * z ^ (-a) else 0) =
      c / (1 + a) * m ^ (-(1 + a)) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hexp : -2 - a < (-1 : ℝ) := by linarith
  calc
    (∫ z in Ioi (1 : ℝ),
        if m ≤ z then (c / z ^ 2) * z ^ (-a) else 0) =
        ∫ z in Ici m, (c / z ^ 2) * z ^ (-a) := by
      rw [← integral_indicator measurableSet_Ioi,
        ← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards [volume.ae_ne (1 : ℝ)] with z hzOne
      by_cases hz : m ≤ z
      · have hz1 : 1 ≤ z := hm.trans hz
        have hzgt : 1 < z := lt_of_le_of_ne hz1 (Ne.symm hzOne)
        simp [Set.indicator, hz, hzgt]
      · simp [Set.indicator, hz]
    _ = ∫ z in Ioi m, (c / z ^ 2) * z ^ (-a) :=
      integral_Ici_eq_integral_Ioi
    _ = ∫ z in Ioi m, c * z ^ (-2 - a) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      have hzpos : 0 < z := hm0.trans hz
      change (c / z ^ (2 : ℕ)) * z ^ (-a) = c * z ^ (-2 - a)
      rw [show z ^ (2 : ℕ) = z ^ (2 : ℝ) by norm_num,
        div_eq_mul_inv, ← Real.rpow_neg hzpos.le]
      calc
        c * z ^ (-2 : ℝ) * z ^ (-a) =
            c * (z ^ (-2 : ℝ) * z ^ (-a)) := by ring
        _ = c * z ^ ((-2 : ℝ) + (-a)) := by
          rw [Real.rpow_add hzpos]
        _ = c * z ^ (-2 - a) := by ring
    _ = c * ∫ z in Ioi m, z ^ (-2 - a) := by
      rw [integral_const_mul]
    _ = c / (1 + a) * m ^ (-(1 + a)) := by
      rw [integral_Ioi_rpow_of_lt hexp hm0]
      have hden : 1 + a ≠ 0 := ne_of_gt (by linarith)
      rw [show -2 - a + 1 = -(1 + a) by ring]
      field_simp [hden]

/-- Exact finite double-sum formula for the Rankin-shifted smooth energy. -/
theorem harperSquarefreeShiftedSmoothEnergy_eq_sum_powerset_max
    (omega : Problem520.Omega) (y : ℕ) {a : ℝ} (ha : 0 ≤ a) :
    harperSquarefreeShiftedSmoothEnergy y a omega =
      ∑ S ∈ (y + 1).primesBelow.powerset,
        ∑ T ∈ (y + 1).primesBelow.powerset,
          (Problem520.freshCharacter omega S *
              Problem520.freshCharacter omega T) /
              (1 + a) *
            (max (Problem520.freshProduct S : ℝ)
              (Problem520.freshProduct T : ℝ)) ^ (-(1 + a)) := by
  classical
  let P : Finset (Finset ℕ) := (y + 1).primesBelow.powerset
  have hprodOne (S : Finset ℕ) (hS : S ∈ P) :
      (1 : ℝ) ≤ Problem520.freshProduct S := by
    have hsub : S ⊆ (y + 1).primesBelow := by
      simpa only [P, Finset.mem_powerset] using hS
    have hnat : 0 < Problem520.freshProduct S :=
      Problem520.freshProduct_pos_of_primes fun p hp ↦
        Nat.prime_of_mem_primesBelow (hsub hp)
    exact_mod_cast hnat
  have hmaxOne (S : Finset ℕ) (hS : S ∈ P)
      (T : Finset ℕ) (hT : T ∈ P) :
      (1 : ℝ) ≤ max (Problem520.freshProduct S : ℝ)
        (Problem520.freshProduct T : ℝ) :=
    (hprodOne S hS).trans (le_max_left _ _)
  unfold harperSquarefreeShiftedSmoothEnergy
  calc
    (∫ z in Ioi (1 : ℝ),
        (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-a)) =
        ∫ z in Ioi (1 : ℝ),
          ∑ S ∈ P, ∑ T ∈ P,
            if max (Problem520.freshProduct S : ℝ)
                (Problem520.freshProduct T : ℝ) ≤ z then
              ((Problem520.freshCharacter omega S *
                  Problem520.freshCharacter omega T) / z ^ 2) * z ^ (-a)
            else 0 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro z hz
      change
        (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-a) = _
      rw [Problem520.abs_ΨReal_sq_eq_sum_powerset_maxIndicator omega y
        ((by norm_num : (0 : ℝ) ≤ 1).trans hz.le)]
      change
        ((∑ S ∈ P, ∑ T ∈ P,
          if max (Problem520.freshProduct S : ℝ)
              (Problem520.freshProduct T : ℝ) ≤ z then
            Problem520.freshCharacter omega S *
              Problem520.freshCharacter omega T else 0) / z ^ 2) * z ^ (-a) = _
      simp_rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hmax : max (Problem520.freshProduct S : ℝ)
          (Problem520.freshProduct T : ℝ) ≤ z <;> simp [hmax]
    _ = ∑ S ∈ P, ∑ T ∈ P,
        ∫ z in Ioi (1 : ℝ),
          if max (Problem520.freshProduct S : ℝ)
              (Problem520.freshProduct T : ℝ) ≤ z then
            ((Problem520.freshCharacter omega S *
                Problem520.freshCharacter omega T) / z ^ 2) * z ^ (-a)
          else 0 := by
      rw [integral_finset_sum P]
      · apply Finset.sum_congr rfl
        intro S hS
        rw [integral_finset_sum P]
        intro T hT
        exact integrableOn_rankinTail
          (hmaxOne S hS T hT) ha _
      · intro S hS
        exact integrable_finset_sum P fun T hT ↦
          integrableOn_rankinTail
            (hmaxOne S hS T hT) ha _
    _ = ∑ S ∈ P, ∑ T ∈ P,
        (Problem520.freshCharacter omega S *
            Problem520.freshCharacter omega T) /
            (1 + a) *
          (max (Problem520.freshProduct S : ℝ)
            (Problem520.freshProduct T : ℝ)) ^ (-(1 + a)) := by
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro T hT
      exact integral_rankinTail (hmaxOne S hS T hT) ha _

/-! ## The shifted Euler product as a finite Dirichlet polynomial -/

private theorem log_freshProduct_rankin
    {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime) :
    Real.log (Problem520.freshProduct S : ℝ) =
      ∑ p ∈ S, Real.log (p : ℝ) := by
  unfold Problem520.freshProduct
  rw [Nat.cast_prod, Real.log_prod]
  intro p hp
  exact_mod_cast (hprime p hp).ne_zero

private theorem prod_rankinRadius
    {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime) (a : ℝ) :
    (∏ p ∈ S, harperRankinEulerRadius p a) =
      (Problem520.freshProduct S : ℝ) ^ (-(1 + a) / 2) := by
  unfold harperRankinEulerRadius Problem520.freshProduct
  rw [Real.finset_prod_rpow]
  · rw [Nat.cast_prod]
  · intro p hp
    positivity

private theorem rankinRadiusProduct_eq_inv_sqrt
    {S : Finset ℕ} (hprime : ∀ p ∈ S, p.Prime)
    {a : ℝ} (ha : 0 ≤ a) :
    (∏ p ∈ S, harperRankinEulerRadius p a) =
      (Real.sqrt ((Problem520.freshProduct S : ℝ) ^ (1 + a)))⁻¹ := by
  have hm : 0 ≤ (Problem520.freshProduct S : ℝ) := by positivity
  have hmPos : 0 < (Problem520.freshProduct S : ℝ) := by
    exact_mod_cast Problem520.freshProduct_pos_of_primes hprime
  rw [prod_rankinRadius hprime a, Real.sqrt_eq_rpow,
    ← Real.rpow_neg (Real.rpow_nonneg hm (1 + a)),
    ← Real.rpow_mul hm]
  congr 2
  ring

private theorem prod_rankinPrimeMonomial
    (omega : Problem520.Omega) (t : ℝ) {S : Finset ℕ}
    (hprime : ∀ p ∈ S, p.Prime) {a : ℝ} (ha : 0 ≤ a) :
    (∏ p ∈ S,
        (((Problem520.ε omega p * harperRankinEulerRadius p a : ℝ) : ℂ) *
          Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))) =
      ((Problem520.freshCharacter omega S /
          Real.sqrt ((Problem520.freshProduct S : ℝ) ^ (1 + a)) : ℝ) : ℂ) *
        Complex.exp ((t * Real.log (Problem520.freshProduct S : ℝ) : ℝ) *
          Complex.I) := by
  rw [Finset.prod_mul_distrib]
  have hcoeffR :
      (∏ p ∈ S,
          Problem520.ε omega p * harperRankinEulerRadius p a) =
        Problem520.freshCharacter omega S /
          Real.sqrt ((Problem520.freshProduct S : ℝ) ^ (1 + a)) := by
    rw [Finset.prod_mul_distrib, rankinRadiusProduct_eq_inv_sqrt hprime ha]
    unfold Problem520.freshCharacter
    ring
  have hcoeffC :
      (∏ p ∈ S,
          ((Problem520.ε omega p * harperRankinEulerRadius p a : ℝ) : ℂ)) =
        ((Problem520.freshCharacter omega S /
          Real.sqrt ((Problem520.freshProduct S : ℝ) ^ (1 + a)) : ℝ) : ℂ) := by
    norm_cast
  rw [hcoeffC, ← Complex.exp_sum]
  congr 2
  have hlog :
      (∑ p ∈ S, t * Real.log (p : ℝ)) =
        t * Real.log (Problem520.freshProduct S : ℝ) := by
    rw [← Finset.mul_sum, ← log_freshProduct_rankin hprime]
  calc
    ∑ p ∈ S,
        (((t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) =
        (((∑ p ∈ S, t * Real.log (p : ℝ) : ℝ) : ℂ) * Complex.I) := by
      push_cast
      rw [Finset.sum_mul]
    _ = (((t * Real.log (Problem520.freshProduct S : ℝ) : ℝ) : ℂ) *
          Complex.I) := by rw [hlog]

/-- The literal finite squarefree Dirichlet polynomial, with positive
angular phase. Evaluate at `-t` for the negative Fourier convention. -/
noncomputable def harperRankinDirichletPolynomial
    (y : ℕ) (a : ℝ) (omega : Problem520.Omega) (t : ℝ) : ℂ :=
  ∑ S ∈ (y + 1).primesBelow.powerset,
    ((Problem520.freshCharacter omega S /
        Real.sqrt ((Problem520.freshProduct S : ℝ) ^ (1 + a)) : ℝ) : ℂ) *
      Complex.exp ((t * Real.log (Problem520.freshProduct S : ℝ) : ℝ) *
        Complex.I)

private noncomputable def harperRankinComplexEulerFactor
    (omega : Problem520.Omega) (p : ℕ) (a t : ℝ) : ℂ :=
  1 + (((Problem520.ε omega p * harperRankinEulerRadius p a : ℝ) : ℂ) *
    Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))

private theorem prod_harperRankinComplexEulerFactor_eq_dirichletPolynomial
    (y : ℕ) (omega : Problem520.Omega) (t : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (∏ p ∈ (y + 1).primesBelow,
        harperRankinComplexEulerFactor omega p a t) =
      harperRankinDirichletPolynomial y a omega t := by
  classical
  unfold harperRankinComplexEulerFactor harperRankinDirichletPolynomial
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro S hS
  apply prod_rankinPrimeMonomial omega t
    (fun p hp ↦ Nat.prime_of_mem_primesBelow ((Finset.mem_powerset.mp hS) hp)) ha

private theorem normSq_harperRankinComplexEulerFactor
    (omega : Problem520.Omega) (p : ℕ) (a t : ℝ) :
    Complex.normSq (harperRankinComplexEulerFactor omega p a t) =
      harperRankinEulerFactor omega p a t := by
  unfold harperRankinComplexEulerFactor harperRankinEulerFactor
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, sub_zero, zero_add, mul_zero, add_zero]
  ring

/-- The shifted Euler density is exactly the squared norm of its finite
Dirichlet expansion. Exported for the finite-to-infinite Fourier passage. -/
theorem harperRankinEulerDensity_eq_normSq_dirichletPolynomial
    (y : ℕ) (a : ℝ) (omega : Problem520.Omega) (t : ℝ) (ha : 0 ≤ a) :
    harperRankinEulerDensity y a omega t =
      Complex.normSq (harperRankinDirichletPolynomial y a omega t) := by
  rw [← prod_harperRankinComplexEulerFactor_eq_dirichletPolynomial y omega t ha]
  unfold harperRankinEulerDensity
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro p hp
  symm
  exact normSq_harperRankinComplexEulerFactor omega p a t

private theorem normSq_sum_rankin_real_mul_exp
    {ι : Type*} (s : Finset ι) (c b : ι → ℝ) :
    Complex.normSq
        (∑ i ∈ s, ((c i : ℝ) : ℂ) *
          Complex.exp ((b i : ℝ) * Complex.I)) =
      ∑ i ∈ s, ∑ j ∈ s,
        c i * c j * Real.cos (b i - b j) := by
  classical
  have hre :
      (∑ i ∈ s, ((c i : ℝ) : ℂ) *
          Complex.exp ((b i : ℝ) * Complex.I)).re =
        ∑ i ∈ s, c i * Real.cos (b i) := by
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  have him :
      (∑ i ∈ s, ((c i : ℝ) : ℂ) *
          Complex.exp ((b i : ℝ) * Complex.I)).im =
        ∑ i ∈ s, c i * Real.sin (b i) := by
    simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, add_zero]
  rw [Complex.normSq_apply, hre, him]
  calc
    (∑ i ∈ s, c i * Real.cos (b i)) *
          (∑ j ∈ s, c j * Real.cos (b j)) +
        (∑ i ∈ s, c i * Real.sin (b i)) *
          (∑ j ∈ s, c j * Real.sin (b j)) =
        (∑ i ∈ s, ∑ j ∈ s,
          (c i * Real.cos (b i)) * (c j * Real.cos (b j))) +
        (∑ i ∈ s, ∑ j ∈ s,
          (c i * Real.sin (b i)) * (c j * Real.sin (b j))) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s,
          ((c i * Real.cos (b i)) * (c j * Real.cos (b j)) +
            (c i * Real.sin (b i)) * (c j * Real.sin (b j))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
    _ = ∑ i ∈ s, ∑ j ∈ s,
          c i * c j * Real.cos (b i - b j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.cos_sub]
      ring

/-- Pointwise cosine expansion of the Rankin-shifted Euler density. -/
theorem harperRankinEulerDensity_eq_sum_powerset_cosine
    (y : ℕ) (omega : Problem520.Omega) (t : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    harperRankinEulerDensity y a omega t =
      ∑ S ∈ (y + 1).primesBelow.powerset,
        ∑ T ∈ (y + 1).primesBelow.powerset,
          (Problem520.freshCharacter omega S *
              Problem520.freshCharacter omega T /
              (Real.sqrt ((Problem520.freshProduct S : ℝ) ^ (1 + a)) *
                Real.sqrt ((Problem520.freshProduct T : ℝ) ^ (1 + a)))) *
            Real.cos
              (t * (Real.log (Problem520.freshProduct S : ℝ) -
                Real.log (Problem520.freshProduct T : ℝ))) := by
  rw [harperRankinEulerDensity_eq_normSq_dirichletPolynomial y a omega t ha]
  unfold harperRankinDirichletPolynomial
  rw [normSq_sum_rankin_real_mul_exp]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  · ring
  · congr 1
    ring

private theorem max_rpow_of_nonneg
    {x y b : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hb : 0 ≤ b) :
    max (x ^ b) (y ^ b) = (max x y) ^ b := by
  by_cases hxy : x ≤ y
  · rw [max_eq_right hxy, max_eq_right]
    exact Real.rpow_le_rpow hx hxy hb
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [max_eq_left hyx, max_eq_left]
    exact Real.rpow_le_rpow hy hyx hb

/-- Exact shifted Parseval identity before changing the vertical variable.
Writing `b = 1+a`, the shifted Euler density is sampled at height `b*u`.
This form is the direct output of the already verified generic finite
Dirichlet-polynomial identity. -/
theorem integral_harperRankinEulerDensity_mul_div_cauchyKernel
    (y : ℕ) (omega : Problem520.Omega) {a : ℝ} (ha : 0 ≤ a) :
    (∫ u : ℝ, harperRankinEulerDensity y a omega ((1 + a) * u) /
        ((1 / 4 : ℝ) + u ^ 2)) =
      2 * Real.pi * (1 + a) *
        harperSquarefreeShiftedSmoothEnergy y a omega := by
  classical
  let P : Finset (Finset ℕ) := (y + 1).primesBelow.powerset
  let b : ℝ := 1 + a
  let d : Finset ℕ → ℝ := fun S ↦
    (Problem520.freshProduct S : ℝ) ^ b
  have hb : 0 < b := by dsimp [b]; linarith
  have hprodPos (S : Finset ℕ) (hS : S ∈ P) :
      0 < (Problem520.freshProduct S : ℝ) := by
    have hsub : S ⊆ (y + 1).primesBelow := by
      simpa only [P, Finset.mem_powerset] using hS
    have hnat : 0 < Problem520.freshProduct S :=
      Problem520.freshProduct_pos_of_primes fun p hp ↦
        Nat.prime_of_mem_primesBelow (hsub hp)
    exact_mod_cast hnat
  have hd (S : Finset ℕ) (hS : S ∈ P) : 0 < d S := by
    exact Real.rpow_pos_of_pos (hprodPos S hS) b
  have hpoint (u : ℝ) :
      harperRankinEulerDensity y a omega (b * u) =
        ∑ S ∈ P, ∑ T ∈ P,
          (Problem520.freshCharacter omega S *
              Problem520.freshCharacter omega T /
              (Real.sqrt (d S) * Real.sqrt (d T))) *
            Real.cos (u * (Real.log (d S) - Real.log (d T))) := by
    rw [harperRankinEulerDensity_eq_sum_powerset_cosine y omega (b * u) ha]
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    dsimp only [d, b]
    congr 1
    rw [Real.log_rpow (hprodPos S hS), Real.log_rpow (hprodPos T hT)]
    congr 1
    ring
  have hFourier := Problem520.integral_finiteDirichletCosineDensity P
    (fun S ↦ Problem520.freshCharacter omega S) d hd
  have hleft :
      (∫ u : ℝ, harperRankinEulerDensity y a omega (b * u) /
          ((1 / 4 : ℝ) + u ^ 2)) =
        2 * Real.pi *
          ∑ S ∈ P, ∑ T ∈ P,
            Problem520.freshCharacter omega S *
              Problem520.freshCharacter omega T / max (d S) (d T) := by
    simpa only [hpoint] using hFourier
  have hsum :
      (∑ S ∈ P, ∑ T ∈ P,
          Problem520.freshCharacter omega S *
            Problem520.freshCharacter omega T / max (d S) (d T)) =
        b * harperSquarefreeShiftedSmoothEnergy y a omega := by
    rw [harperSquarefreeShiftedSmoothEnergy_eq_sum_powerset_max omega y ha]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    have hm0 : 0 ≤ max (Problem520.freshProduct S : ℝ)
        (Problem520.freshProduct T : ℝ) := by positivity
    have hmax : max (d S) (d T) =
        (max (Problem520.freshProduct S : ℝ)
          (Problem520.freshProduct T : ℝ)) ^ b := by
      exact max_rpow_of_nonneg (by positivity) (by positivity) hb.le
    rw [hmax, div_eq_mul_inv,
      ← Real.rpow_neg hm0]
    dsimp only [b]
    field_simp [hb.ne']
  rw [show 1 + a = b by rfl]
  calc
    (∫ u : ℝ, harperRankinEulerDensity y a omega (b * u) /
        ((1 / 4 : ℝ) + u ^ 2)) =
        2 * Real.pi *
          ∑ S ∈ P, ∑ T ∈ P,
            Problem520.freshCharacter omega S *
              Problem520.freshCharacter omega T / max (d S) (d T) := hleft
    _ = 2 * Real.pi * b *
        harperSquarefreeShiftedSmoothEnergy y a omega := by rw [hsum]; ring

/-- Exact shifted Harman--Parseval identity in the original height variable.
The Cauchy kernel broadens from `1/4+t^2` to `(1+a)^2/4+t^2`, and no other
correction survives. -/
theorem integral_harperRankinEulerDensity_div_shiftedCauchyKernel
    (y : ℕ) (omega : Problem520.Omega) {a : ℝ} (ha : 0 ≤ a) :
    (∫ t : ℝ, harperRankinEulerDensity y a omega t /
        (((1 + a) ^ 2) / 4 + t ^ 2)) =
      2 * Real.pi * harperSquarefreeShiftedSmoothEnergy y a omega := by
  let b : ℝ := 1 + a
  let g : ℝ → ℝ := fun t ↦
    harperRankinEulerDensity y a omega t / (b ^ 2 / 4 + t ^ 2)
  let I : ℝ := ∫ u : ℝ,
    harperRankinEulerDensity y a omega (b * u) /
      ((1 / 4 : ℝ) + u ^ 2)
  have hb : 0 < b := by dsimp only [b]; linarith
  have hcomp : (fun u : ℝ ↦ g (b * u)) = fun u ↦
      b⁻¹ ^ (2 : ℕ) *
        (harperRankinEulerDensity y a omega (b * u) /
          ((1 / 4 : ℝ) + u ^ 2)) := by
    funext u
    dsimp only [g]
    have hden : (1 / 4 : ℝ) + u ^ 2 ≠ 0 := by positivity
    field_simp [hb.ne', hden]
  have hscaled : I =
      2 * Real.pi * b *
        harperSquarefreeShiftedSmoothEnergy y a omega := by
    simpa only [I, b] using
      integral_harperRankinEulerDensity_mul_div_cauchyKernel y omega ha
  have hleft : (∫ u : ℝ, g (b * u)) = b⁻¹ ^ (2 : ℕ) * I := by
    rw [hcomp, integral_const_mul]
  have hchange : (∫ u : ℝ, g (b * u)) = b⁻¹ * ∫ t : ℝ, g t := by
    have h := Measure.integral_comp_mul_left g b
    rw [abs_of_pos (inv_pos.mpr hb)] at h
    simpa only [smul_eq_mul] using h
  have hraw : b⁻¹ ^ (2 : ℕ) * I = b⁻¹ * ∫ t : ℝ, g t := by
    rw [← hleft, hchange]
  rw [hscaled] at hraw
  change (∫ t : ℝ, g t) =
    2 * Real.pi * harperSquarefreeShiftedSmoothEnergy y a omega
  field_simp [hb.ne'] at hraw ⊢
  nlinarith

private theorem integrable_cos_mul_div_rankinCauchyKernel
    (u : ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun t : ℝ ↦
      Real.cos (t * u) / (b ^ 2 / 4 + t ^ 2)) := by
  let scale : ℝ := 2 / b
  have hscale : scale ≠ 0 := by dsimp only [scale]; positivity
  have hbase : Integrable (fun t : ℝ ↦
      (1 + (scale * t) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' hscale
  have hdom : Integrable (fun t : ℝ ↦
      (4 / b ^ 2) * (1 + (scale * t) ^ 2)⁻¹) :=
    hbase.const_mul (4 / b ^ 2)
  apply hdom.mono'
  · have hnum : Continuous (fun t : ℝ ↦ Real.cos (t * u)) := by
      fun_prop
    have hdenC : Continuous (fun t : ℝ ↦ b ^ 2 / 4 + t ^ 2) := by
      fun_prop
    exact (hnum.div hdenC (fun t ↦ by positivity)).aestronglyMeasurable
  · exact ae_of_all volume fun t ↦ by
      have hden : 0 < b ^ 2 / 4 + t ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hden]
      dsimp only [scale]
      have hidentity :
          (4 / b ^ 2) * (1 + (2 / b * t) ^ 2)⁻¹ =
            (b ^ 2 / 4 + t ^ 2)⁻¹ := by
        field_simp [hb.ne']
        ring
      rw [hidentity, inv_eq_one_div]
      exact (div_le_div_iff_of_pos_right hden).2
        (Real.abs_cos_le_one (t * u))

/-- Global integrability of the shifted Euler density against its broadened
Cauchy kernel. -/
theorem integrable_harperRankinEulerDensity_div_shiftedCauchyKernel
    (y : ℕ) (omega : Problem520.Omega) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun t : ℝ ↦ harperRankinEulerDensity y a omega t /
      (((1 + a) ^ 2) / 4 + t ^ 2)) := by
  classical
  let P : Finset (Finset ℕ) := (y + 1).primesBelow.powerset
  let term : Finset ℕ → Finset ℕ → ℝ → ℝ := fun S T t ↦
    (Problem520.freshCharacter omega S *
        Problem520.freshCharacter omega T /
        (Real.sqrt ((Problem520.freshProduct S : ℝ) ^ (1 + a)) *
          Real.sqrt ((Problem520.freshProduct T : ℝ) ^ (1 + a)))) *
      (Real.cos (t * (Real.log (Problem520.freshProduct S : ℝ) -
        Real.log (Problem520.freshProduct T : ℝ))) /
          (((1 + a) ^ 2) / 4 + t ^ 2))
  have hb : 0 < 1 + a := by linarith
  have hterm (S T : Finset ℕ) : Integrable (term S T) :=
    (integrable_cos_mul_div_rankinCauchyKernel
      (Real.log (Problem520.freshProduct S : ℝ) -
        Real.log (Problem520.freshProduct T : ℝ)) hb).const_mul _
  have hsum : Integrable (fun t : ℝ ↦
      ∑ S ∈ P, ∑ T ∈ P, term S T t) :=
    integrable_finset_sum P fun S hS ↦
      integrable_finset_sum P fun T hT ↦ hterm S T
  apply hsum.congr
  exact ae_of_all volume fun t ↦ by
    change (∑ S ∈ P, ∑ T ∈ P, term S T t) =
      harperRankinEulerDensity y a omega t /
        (((1 + a) ^ 2) / 4 + t ^ 2)
    rw [harperRankinEulerDensity_eq_sum_powerset_cosine y omega t ha]
    change
      (∑ S ∈ P, ∑ T ∈ P,
        (Problem520.freshCharacter omega S *
            Problem520.freshCharacter omega T /
            (Real.sqrt ((Problem520.freshProduct S : ℝ) ^ (1 + a)) *
              Real.sqrt ((Problem520.freshProduct T : ℝ) ^ (1 + a)))) *
          (Real.cos (t * (Real.log (Problem520.freshProduct S : ℝ) -
            Real.log (Problem520.freshProduct T : ℝ))) /
              (((1 + a) ^ 2) / 4 + t ^ 2))) = _
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    ring

/-- The unweighted shifted Euler mass on Harper's fixed central band is
bounded by `5/4` times its full Cauchy-weighted mass whenever `0 ≤ a ≤ 1`. -/
theorem integral_harperLowerVerticalBand_harperRankinEulerDensity_le
    (y : ℕ) (omega : Problem520.Omega) {a : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ t in harperLowerVerticalBand,
        harperRankinEulerDensity y a omega t) ≤
      (5 / 4 : ℝ) * (2 * Real.pi) *
        harperSquarefreeShiftedSmoothEnergy y a omega := by
  let weighted : ℝ → ℝ := fun t ↦
    harperRankinEulerDensity y a omega t /
      (((1 + a) ^ 2) / 4 + t ^ 2)
  have hweighted : Integrable weighted := by
    simpa only [weighted] using
      integrable_harperRankinEulerDensity_div_shiftedCauchyKernel
        y omega ha
  have hbase : IntegrableOn
      (fun t ↦ harperRankinEulerDensity y a omega t)
      harperLowerVerticalBand := by
    have hcont : Continuous (fun t ↦ harperRankinEulerDensity y a omega t) := by
      unfold harperRankinEulerDensity harperRankinEulerFactor
      fun_prop
    exact hcont.integrableOn_Icc
  have hpoint (t : ℝ) (ht : t ∈ harperLowerVerticalBand) :
      harperRankinEulerDensity y a omega t ≤ (5 / 4 : ℝ) * weighted t := by
    have htBounds : (1 : ℝ) / 3 ≤ t ∧ t ≤ (1 : ℝ) / 2 := ht
    have ht0 : 0 ≤ t := by linarith
    have hden : 0 < ((1 + a) ^ 2) / 4 + t ^ 2 := by positivity
    have hdenLe : ((1 + a) ^ 2) / 4 + t ^ 2 ≤ (5 / 4 : ℝ) := by
      nlinarith [sq_nonneg (1 - a), sq_nonneg t]
    have hrho := harperRankinEulerDensity_nonneg y a omega t
    dsimp only [weighted]
    calc
      harperRankinEulerDensity y a omega t ≤
          harperRankinEulerDensity y a omega t * (5 / 4 : ℝ) /
            (((1 + a) ^ 2) / 4 + t ^ 2) := by
        rw [le_div_iff₀ hden]
        exact mul_le_mul_of_nonneg_left hdenLe hrho
      _ = (5 / 4 : ℝ) *
          (harperRankinEulerDensity y a omega t /
            (((1 + a) ^ 2) / 4 + t ^ 2)) := by ring
  have hband :
      (∫ t in harperLowerVerticalBand,
          harperRankinEulerDensity y a omega t) ≤
        ∫ t in harperLowerVerticalBand, (5 / 4 : ℝ) * weighted t :=
    setIntegral_mono_on hbase (hweighted.const_mul (5 / 4)).integrableOn
      measurableSet_harperLowerVerticalBand hpoint
  have hfull :
      (∫ t in harperLowerVerticalBand, weighted t) ≤ ∫ t, weighted t :=
    setIntegral_le_integral hweighted (ae_of_all _ fun t ↦
      div_nonneg (harperRankinEulerDensity_nonneg y a omega t)
        (by positivity))
  calc
    (∫ t in harperLowerVerticalBand,
        harperRankinEulerDensity y a omega t) ≤
        ∫ t in harperLowerVerticalBand, (5 / 4 : ℝ) * weighted t := hband
    _ = (5 / 4 : ℝ) * ∫ t in harperLowerVerticalBand, weighted t := by
      rw [integral_const_mul]
    _ ≤ (5 / 4 : ℝ) * ∫ t, weighted t := by gcongr
    _ = (5 / 4 : ℝ) * (2 * Real.pi) *
        harperSquarefreeShiftedSmoothEnergy y a omega := by
      rw [integral_harperRankinEulerDensity_div_shiftedCauchyKernel
        y omega ha]
      ring

#print axioms Erdos.Problem1144.harperSquarefreeShiftedSmoothEnergy_eq_sum_powerset_max
#print axioms Erdos.Problem1144.harperRankinEulerDensity_eq_sum_powerset_cosine
#print axioms Erdos.Problem1144.integral_harperRankinEulerDensity_mul_div_cauchyKernel
#print axioms Erdos.Problem1144.integral_harperRankinEulerDensity_div_shiftedCauchyKernel
#print axioms Erdos.Problem1144.integral_harperLowerVerticalBand_harperRankinEulerDensity_le

end

end Problem1144
end Erdos
