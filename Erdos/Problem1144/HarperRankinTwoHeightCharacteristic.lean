import Erdos.Problem1144.HarperRankinTwoHeightTilt
import Erdos.Problem1144.HarperTwoHeightCharacteristic

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Rankin two-height block characteristic comparison

The shifted pair coordinates remain independent.  The one-prime cubic
estimate therefore accumulates over scheduled blocks with the same numerical
Fourier budget as at the critical line.
-/

noncomputable def harperRankinTwoHeightProjectedPrimeBlockSum
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a t s v w : ℝ) (eta : Problem520.HarperPrimeCube y) : ℝ :=
  ∑ p ∈ S,
    harperRankinTwoHeightProjectedPrimeIncrement p.1 a t s v w (eta p)

noncomputable def harperRankinTwoHeightProjectedCubeCharacteristic
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ) : ℂ :=
  ∫ eta, Complex.exp
      (((harperRankinTwoHeightProjectedPrimeBlockSum
        y S a t s v w eta : ℝ) : ℂ) * Complex.I)
    ∂harperRankinTwoHeightCubeLaw y a ha t s

theorem integral_harperRankinTwoHeightCube_eval_complex
    (y : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s : ℝ)
    (p : Problem520.HarperPrimeIndex y) (g : Bool → ℂ) :
    (∫ eta, g (eta p) ∂harperRankinTwoHeightCubeLaw y a ha t s) =
      ∫ b, g b ∂harperRankinTwoHeightCoin p.1
        (Nat.prime_of_mem_primesBelow p.property) a ha t s := by
  have hmp := measurePreserving_harperRankinTwoHeightCube_eval
    y a ha t s p
  calc
    (∫ eta, g (eta p) ∂harperRankinTwoHeightCubeLaw y a ha t s) =
        ∫ b, g b ∂Measure.map
          (fun eta : Problem520.HarperPrimeCube y ↦ eta p)
          (harperRankinTwoHeightCubeLaw y a ha t s) := by
      symm
      exact integral_map hmp.measurable.aemeasurable
        (measurable_of_finite g).aestronglyMeasurable
    _ = _ := by rw [hmp.map_eq]

noncomputable def harperRankinTwoHeightProjectedBlockCharacteristic
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ) : ℂ :=
  ∏ p ∈ S, harperRankinTwoHeightProjectedPrimeCharacteristic p.1
    (Nat.prime_of_mem_primesBelow p.property) a ha t s v w

theorem harperRankinTwoHeightProjectedCubeCharacteristic_eq_block
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ) :
    harperRankinTwoHeightProjectedCubeCharacteristic
        y S a ha t s v w =
      harperRankinTwoHeightProjectedBlockCharacteristic
        y S a ha t s v w := by
  let coord : S → Problem520.HarperPrimeCube y → Bool :=
    fun p eta ↦ eta p.1
  let g : (p : S) → Bool → ℂ := fun p b ↦
    Complex.exp
      (((harperRankinTwoHeightProjectedPrimeIncrement
        p.1.1 a t s v w b : ℝ) : ℂ) * Complex.I)
  have hcoord : iIndepFun coord
      (harperRankinTwoHeightCubeLaw y a ha t s) := by
    exact iIndepFun.precomp Subtype.val_injective
      (iIndepFun_harperRankinTwoHeightCube_coordinates y a ha t s)
  have hfunctions : iIndepFun
      (fun p : S ↦ g p ∘ coord p)
      (harperRankinTwoHeightCubeLaw y a ha t s) :=
    hcoord.comp g (fun _ ↦ measurable_of_finite _)
  have hprod := hfunctions.integral_fun_prod_eq_prod_integral
    (fun p ↦ (measurable_of_finite (g p ∘ coord p)).aestronglyMeasurable)
  calc
    harperRankinTwoHeightProjectedCubeCharacteristic
        y S a ha t s v w =
        ∫ eta, ∏ p ∈ S, Complex.exp
          (((harperRankinTwoHeightProjectedPrimeIncrement
            p.1 a t s v w (eta p) : ℝ) : ℂ) * Complex.I)
          ∂harperRankinTwoHeightCubeLaw y a ha t s := by
      unfold harperRankinTwoHeightProjectedCubeCharacteristic
        harperRankinTwoHeightProjectedPrimeBlockSum
      apply integral_congr_ae
      exact ae_of_all _ fun eta ↦ by
        change
          Complex.exp
              (((∑ p ∈ S,
                harperRankinTwoHeightProjectedPrimeIncrement
                  p.1 a t s v w (eta p) : ℝ) : ℂ) * Complex.I) =
            ∏ p ∈ S, Complex.exp
              (((harperRankinTwoHeightProjectedPrimeIncrement
                p.1 a t s v w (eta p) : ℝ) : ℂ) * Complex.I)
        rw [← Complex.exp_sum]
        congr 1
        push_cast
        rw [Finset.sum_mul]
    _ = ∫ eta, ∏ p : S, Complex.exp
          (((harperRankinTwoHeightProjectedPrimeIncrement
            p.1.1 a t s v w (eta p.1) : ℝ) : ℂ) * Complex.I)
          ∂harperRankinTwoHeightCubeLaw y a ha t s := by
      congr 1
      funext eta
      exact (Finset.prod_coe_sort S (fun p ↦ Complex.exp
        (((harperRankinTwoHeightProjectedPrimeIncrement
          p.1 a t s v w (eta p) : ℝ) : ℂ) * Complex.I))).symm
    _ = ∏ p : S, ∫ eta, Complex.exp
          (((harperRankinTwoHeightProjectedPrimeIncrement
            p.1.1 a t s v w (eta p.1) : ℝ) : ℂ) * Complex.I)
          ∂harperRankinTwoHeightCubeLaw y a ha t s := by
      simpa only [g, coord, Function.comp_apply] using hprod
    _ = ∏ p : S,
        harperRankinTwoHeightProjectedPrimeCharacteristic p.1.1
          (Nat.prime_of_mem_primesBelow p.1.property)
          a ha t s v w := by
      apply Finset.prod_congr rfl
      intro p hpS
      exact integral_harperRankinTwoHeightCube_eval_complex
        y a ha t s p.1 (fun b ↦ Complex.exp
          (((harperRankinTwoHeightProjectedPrimeIncrement
            p.1.1 a t s v w b : ℝ) : ℂ) * Complex.I))
    _ = harperRankinTwoHeightProjectedBlockCharacteristic
        y S a ha t s v w := by
      unfold harperRankinTwoHeightProjectedBlockCharacteristic
      exact Finset.prod_coe_sort S (fun p ↦
        harperRankinTwoHeightProjectedPrimeCharacteristic p.1
          (Nat.prime_of_mem_primesBelow p.property) a ha t s v w)

noncomputable def harperRankinTwoHeightProjectedBlockVariance
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ) : ℝ :=
  ∑ p ∈ S, harperRankinTwoHeightProjectedPrimeVariance p.1
    (Nat.prime_of_mem_primesBelow p.property) a ha t s v w

theorem harperRankinTwoHeightProjectedBlockVariance_nonneg
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ) :
    0 ≤ harperRankinTwoHeightProjectedBlockVariance
      y S a ha t s v w := by
  unfold harperRankinTwoHeightProjectedBlockVariance
  exact Finset.sum_nonneg fun p hpS ↦
    harperRankinTwoHeightProjectedPrimeVariance_nonneg p.1
      (Nat.prime_of_mem_primesBelow p.property) a ha t s v w

/-- Finite-block Cramer--Wold comparison with the exact shifted covariance
quadratic form. -/
theorem norm_harperRankinTwoHeightProjectedBlockCharacteristic_sub_gaussian_le
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ)
    (hsmall : ∀ p ∈ S,
      2 * (|v| + |w|) * (Real.sqrt (p.1 : ℝ))⁻¹ ≤ 1)
    (hquad : ∀ p ∈ S,
      harperRankinTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) a ha t s v w / 2 ≤
        1 / 2) :
    ‖harperRankinTwoHeightProjectedBlockCharacteristic
          y S a ha t s v w -
        Complex.exp
          (-((harperRankinTwoHeightProjectedBlockVariance
            y S a ha t s v w / 2 : ℝ) : ℂ))‖ ≤
      (∑ p ∈ S,
        (2 * (|v| + |w|) *
          (Real.sqrt (p.1 : ℝ))⁻¹) ^ 3) +
      ∑ p ∈ S,
        (harperRankinTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) a ha t s v w / 2) ^ 2 := by
  let phi : Problem520.HarperPrimeIndex y → ℂ := fun p ↦
    harperRankinTwoHeightProjectedPrimeCharacteristic p.1
      (Nat.prime_of_mem_primesBelow p.property) a ha t s v w
  let q : Problem520.HarperPrimeIndex y → ℝ := fun p ↦
    harperRankinTwoHeightProjectedPrimeVariance p.1
      (Nat.prime_of_mem_primesBelow p.property) a ha t s v w / 2
  let linear : Problem520.HarperPrimeIndex y → ℂ := fun p ↦
    1 - (q p : ℂ)
  let gaussian : Problem520.HarperPrimeIndex y → ℂ := fun p ↦
    Complex.exp (-(q p : ℂ))
  have hphi : ∀ p ∈ S, ‖phi p‖ ≤ 1 := by
    intro p hpS
    exact norm_harperRankinTwoHeightProjectedPrimeCharacteristic_le_one
      p.1 (Nat.prime_of_mem_primesBelow p.property) a ha t s v w
  have hqNonneg : ∀ p, 0 ≤ q p := by
    intro p
    exact div_nonneg
      (harperRankinTwoHeightProjectedPrimeVariance_nonneg p.1
        (Nat.prime_of_mem_primesBelow p.property) a ha t s v w)
      (by norm_num)
  have hlinear : ∀ p ∈ S, ‖linear p‖ ≤ 1 := by
    intro p hpS
    have hqle : q p ≤ 1 := (hquad p hpS).trans (by norm_num)
    change ‖(1 : ℂ) - (q p : ℂ)‖ ≤ 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hqle)]
    linarith [hqNonneg p]
  have hgaussian : ∀ p ∈ S, ‖gaussian p‖ ≤ 1 := by
    intro p hpS
    change ‖Complex.exp (-(q p : ℂ))‖ ≤ 1
    rw [Complex.norm_exp]
    simp only [Complex.neg_re, Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hqNonneg p))
  have hfirst := Problem520.norm_prod_sub_prod_le_sum_norm_sub
    S phi linear hphi hlinear
  have hsecond := Problem520.norm_prod_sub_prod_le_sum_norm_sub
    S linear gaussian hlinear hgaussian
  have hfirstBound :
      ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, linear p‖ ≤
        ∑ p ∈ S,
          (2 * (|v| + |w|) *
            (Real.sqrt (p.1 : ℝ))⁻¹) ^ 3 := by
    exact hfirst.trans (Finset.sum_le_sum fun p hpS ↦ by
      simpa only [phi, linear, q] using
        norm_harperRankinTwoHeightProjectedPrimeCharacteristic_sub_quadratic_le
          (Nat.prime_of_mem_primesBelow p.property) ha t s v w
          (hsmall p hpS))
  have hsecondBound :
      ‖(∏ p ∈ S, linear p) - ∏ p ∈ S, gaussian p‖ ≤
        ∑ p ∈ S, (q p) ^ 2 := by
    exact hsecond.trans (Finset.sum_le_sum fun p hpS ↦ by
      simpa only [linear, gaussian] using
        Problem520.norm_one_sub_sub_exp_neg_le_sq
          (hqNonneg p) ((hquad p hpS).trans (by norm_num)))
  have hprodGaussian :
      (∏ p ∈ S, gaussian p) =
        Complex.exp
          (-((harperRankinTwoHeightProjectedBlockVariance
            y S a ha t s v w / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_sum]
    congr 1
    unfold harperRankinTwoHeightProjectedBlockVariance
    dsimp only [gaussian, q]
    push_cast
    rw [Finset.sum_neg_distrib, Finset.sum_div]
  change
    ‖(∏ p ∈ S, phi p) -
        Complex.exp
          (-((harperRankinTwoHeightProjectedBlockVariance
            y S a ha t s v w / 2 : ℝ) : ℂ))‖ ≤ _
  rw [← hprodGaussian]
  calc
    ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, gaussian p‖ ≤
        ‖(∏ p ∈ S, phi p) - ∏ p ∈ S, linear p‖ +
          ‖(∏ p ∈ S, linear p) - ∏ p ∈ S, gaussian p‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (∑ p ∈ S,
          (2 * (|v| + |w|) *
            (Real.sqrt (p.1 : ℝ))⁻¹) ^ 3) +
        ∑ p ∈ S, (q p) ^ 2 :=
      add_le_add hfirstBound hsecondBound
    _ = _ := by rfl

theorem norm_harperRankinTwoHeightProjectedCubeCharacteristic_sub_gaussian_le
    (y : ℕ) (S : Finset (Problem520.HarperPrimeIndex y))
    (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ)
    (hsmall : ∀ p ∈ S,
      2 * (|v| + |w|) * (Real.sqrt (p.1 : ℝ))⁻¹ ≤ 1)
    (hquad : ∀ p ∈ S,
      harperRankinTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) a ha t s v w / 2 ≤
        1 / 2) :
    ‖harperRankinTwoHeightProjectedCubeCharacteristic
          y S a ha t s v w -
        Complex.exp
          (-((harperRankinTwoHeightProjectedBlockVariance
            y S a ha t s v w / 2 : ℝ) : ℂ))‖ ≤
      (∑ p ∈ S,
        (2 * (|v| + |w|) *
          (Real.sqrt (p.1 : ℝ))⁻¹) ^ 3) +
      ∑ p ∈ S,
        (harperRankinTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) a ha t s v w / 2) ^ 2 := by
  rw [harperRankinTwoHeightProjectedCubeCharacteristic_eq_block]
  exact
    norm_harperRankinTwoHeightProjectedBlockCharacteristic_sub_gaussian_le
      y S a ha t s v w hsmall hquad

/-- Scheduled shifted blocks have the same doubly-exponentially small
two-dimensional characteristic error as the critical-line blocks. -/
theorem norm_harperRankinTwoHeightScheduledProjectedCubeCharacteristic_sub_gaussian_le
    (y j : ℕ) (a : ℝ) (ha : 0 ≤ a) (t s v w : ℝ)
    (hfrequency :
      2 * (|v| + |w|) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : ℝ)) :
    ‖harperRankinTwoHeightProjectedCubeCharacteristic y
          (Problem520.harperScheduledPrimeBlock y j)
          a ha t s v w -
        Complex.exp
          (-((harperRankinTwoHeightProjectedBlockVariance y
            (Problem520.harperScheduledPrimeBlock y j)
            a ha t s v w / 2 : ℝ) : ℂ))‖ ≤
      (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
        (16 * (|v| + |w|) ^ 3 +
          2 * (|v| + |w|) ^ 4) := by
  let S := Problem520.harperScheduledPrimeBlock y j
  let R : ℝ := |v| + |w|
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hsmall : ∀ p ∈ S,
      2 * R * (Real.sqrt (p.1 : ℝ))⁻¹ ≤ 1 := by
    intro p hpS
    have hpPos : (0 : ℝ) < p.1 := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow p.property).pos
    have hsqrtPos : 0 < Real.sqrt (p.1 : ℝ) := Real.sqrt_pos.2 hpPos
    have hpA : (Problem520.harperBlockEndpoint j : ℝ) ≤ p.1 := by
      exact_mod_cast
        ((Problem520.mem_harperScheduledPrimeBlock p).mp hpS).1.le
    have hsqrtOrder :
        Real.sqrt (Problem520.harperBlockEndpoint j : ℝ) ≤
          Real.sqrt (p.1 : ℝ) := Real.sqrt_le_sqrt hpA
    have hnum : 2 * R ≤ Real.sqrt (p.1 : ℝ) :=
      hfrequency.trans hsqrtOrder
    rw [mul_inv_le_iff₀ hsqrtPos]
    simpa only [one_mul] using hnum
  have hquad : ∀ p ∈ S,
      harperRankinTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) a ha t s v w / 2 ≤
        1 / 2 := by
    intro p hpS
    let B : ℝ := 2 * R * (Real.sqrt (p.1 : ℝ))⁻¹
    have hB0 : 0 ≤ B := by dsimp only [B]; positivity
    have hB1 : B ≤ 1 := hsmall p hpS
    have hvar :=
      harperRankinTwoHeightProjectedPrimeVariance_le_envelope
        (Nat.prime_of_mem_primesBelow p.property) ha t s v w
    have hBsq : B ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - B)]
    have hvarB :
        harperRankinTwoHeightProjectedPrimeVariance p.1
            (Nat.prime_of_mem_primesBelow p.property) a ha t s v w ≤
          B ^ 2 := by
      simpa only [B, R] using hvar
    nlinarith
  have hbase :=
    norm_harperRankinTwoHeightProjectedCubeCharacteristic_sub_gaussian_le
      y S a ha t s v w
      (by simpa only [R] using hsmall) hquad
  have hcubicEq :
      (∑ p ∈ S,
        (2 * R * (Real.sqrt (p.1 : ℝ))⁻¹) ^ 3) =
        12 * R ^ 3 * Problem520.harperBlockCubicRemainder y S := by
    unfold Problem520.harperBlockCubicRemainder
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hpS
    ring
  have hquarticPoint : ∀ p ∈ S,
      (harperRankinTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) a ha t s v w / 2) ^ 2 ≤
        R ^ 4 * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3 := by
    intro p hpS
    let z : ℝ := (Real.sqrt (p.1 : ℝ))⁻¹
    let q : ℝ := harperRankinTwoHeightProjectedPrimeVariance p.1
      (Nat.prime_of_mem_primesBelow p.property) a ha t s v w / 2
    have hpPrime := Nat.prime_of_mem_primesBelow p.property
    have hp16 : 16 ≤ p.1 :=
      Problem520.sixteen_le_prime_of_mem_harperScheduledPrimeBlock hpS
    have hpPos : (0 : ℝ) < p.1 := by exact_mod_cast hpPrime.pos
    have hsqrtPos : 0 < Real.sqrt (p.1 : ℝ) := Real.sqrt_pos.2 hpPos
    have hz0 : 0 ≤ z := by dsimp only [z]; positivity
    have hsqrtFour : (4 : ℝ) ≤ Real.sqrt (p.1 : ℝ) := by
      have h16 : (16 : ℝ) ≤ p.1 := by exact_mod_cast hp16
      have h := Real.sqrt_le_sqrt h16
      norm_num at h ⊢
      exact h
    have hzQuarter : z ≤ (1 / 4 : ℝ) := by
      dsimp only [z]
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4)
          hsqrtFour)
    have hq0 : 0 ≤ q := by
      dsimp only [q]
      exact div_nonneg
        (harperRankinTwoHeightProjectedPrimeVariance_nonneg p.1 hpPrime
          a ha t s v w) (by norm_num)
    have hvar :=
      harperRankinTwoHeightProjectedPrimeVariance_le_envelope
        hpPrime ha t s v w
    have hqle : q ≤ 2 * R ^ 2 * z ^ 2 := by
      dsimp only [q, z, R] at hvar ⊢
      nlinarith
    have hqSq := pow_le_pow_left₀ hq0 hqle 2
    calc
      q ^ 2 ≤ (2 * R ^ 2 * z ^ 2) ^ 2 := hqSq
      _ = R ^ 4 * z ^ 3 * (4 * z) := by ring
      _ ≤ R ^ 4 * z ^ 3 * 1 := by
        gcongr
        nlinarith
      _ = R ^ 4 * z ^ 3 := by ring
  have hquartic :
      (∑ p ∈ S,
        (harperRankinTwoHeightProjectedPrimeVariance p.1
          (Nat.prime_of_mem_primesBelow p.property) a ha t s v w / 2) ^ 2) ≤
        (3 / 2 : ℝ) * R ^ 4 *
          Problem520.harperBlockCubicRemainder y S := by
    calc
      (∑ p ∈ S,
          (harperRankinTwoHeightProjectedPrimeVariance p.1
            (Nat.prime_of_mem_primesBelow p.property)
              a ha t s v w / 2) ^ 2) ≤
          ∑ p ∈ S,
            R ^ 4 * (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3 :=
        Finset.sum_le_sum hquarticPoint
      _ = (3 / 2 : ℝ) * R ^ 4 *
          Problem520.harperBlockCubicRemainder y S := by
        unfold Problem520.harperBlockCubicRemainder
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hpS
        ring
  have hremainder := Problem520.harperBlockCubicRemainder_scheduled_le y j
  change
    ‖harperRankinTwoHeightProjectedCubeCharacteristic
          y S a ha t s v w -
        Complex.exp
          (-((harperRankinTwoHeightProjectedBlockVariance
            y S a ha t s v w / 2 : ℝ) : ℂ))‖ ≤ _
  calc
    _ ≤ (∑ p ∈ S,
          (2 * R * (Real.sqrt (p.1 : ℝ))⁻¹) ^ 3) +
        ∑ p ∈ S,
          (harperRankinTwoHeightProjectedPrimeVariance p.1
            (Nat.prime_of_mem_primesBelow p.property)
              a ha t s v w / 2) ^ 2 := by
      simpa only [R] using hbase
    _ ≤ 12 * R ^ 3 * Problem520.harperBlockCubicRemainder y S +
        (3 / 2 : ℝ) * R ^ 4 *
          Problem520.harperBlockCubicRemainder y S := by
      rw [hcubicEq]
      gcongr
    _ ≤ 12 * R ^ 3 *
          ((4 / 3 : ℝ) *
            (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹) +
        (3 / 2 : ℝ) * R ^ 4 *
          ((4 / 3 : ℝ) *
            (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹) := by
      gcongr
    _ = (Real.sqrt (Problem520.harperBlockEndpoint j : ℝ))⁻¹ *
        (16 * R ^ 3 + 2 * R ^ 4) := by ring
    _ = _ := by rfl

#print axioms Erdos.Problem1144.harperRankinTwoHeightProjectedCubeCharacteristic_eq_block
#print axioms Erdos.Problem1144.harperRankinTwoHeightProjectedBlockVariance_nonneg
#print axioms Erdos.Problem1144.norm_harperRankinTwoHeightProjectedCubeCharacteristic_sub_gaussian_le
#print axioms Erdos.Problem1144.norm_harperRankinTwoHeightScheduledProjectedCubeCharacteristic_sub_gaussian_le

end


end Problem1144
end Erdos
