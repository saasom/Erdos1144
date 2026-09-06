import Erdos.Problem1144.HarperCandidateTranslationEnvelope

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Replacement of the inverse-square-root logarithmic factor

Together with the arithmetic bin envelope, these estimates bound replacement
of the full coefficient `a(t-v)/sqrt(v)` across each logarithmic prime bin.
-/

/-- A squared Lipschitz bound for the inverse square root away from zero. -/
theorem candidate_inv_sqrt_sub_sq_le {T x y : ℝ}
    (hT : 0 < T) (hTx : T ≤ x) (hxy : x ≤ y) :
    (1 / Real.sqrt x - 1 / Real.sqrt y) ^ 2 ≤ (y - x) ^ 2 / T ^ 3 := by
  have hx : 0 < x := hT.trans_le hTx
  have hy : 0 < y := hx.trans_le hxy
  have hsT := Real.sqrt_pos.mpr hT
  have hsx := Real.sqrt_pos.mpr hx
  have hsy := Real.sqrt_pos.mpr hy
  have hT2 := Real.sq_sqrt hT.le
  have hx2 := Real.sq_sqrt hx.le
  have hy2 := Real.sq_sqrt hy.le
  have hTsx := Real.sqrt_le_sqrt hTx
  have hTsy := Real.sqrt_le_sqrt (hTx.trans hxy)
  have hprod : T ≤ Real.sqrt x * Real.sqrt y := by
    have hm := mul_le_mul hTsx hTsy hsT.le hsx.le
    nlinarith
  have hden : T * Real.sqrt T ≤
      Real.sqrt x * Real.sqrt y * (Real.sqrt x + Real.sqrt y) := by
    exact mul_le_mul hprod (by linarith) hsT.le (mul_nonneg hsx.le hsy.le)
  have heq : 1 / Real.sqrt x - 1 / Real.sqrt y =
      (y - x) / (Real.sqrt x * Real.sqrt y * (Real.sqrt x + Real.sqrt y)) := by
    have hnum : y - x = (Real.sqrt y - Real.sqrt x) * (Real.sqrt x + Real.sqrt y) := by
      nlinarith
    rw [hnum]
    field_simp
  have hbound : 1 / Real.sqrt x - 1 / Real.sqrt y ≤ (y - x) / (T * Real.sqrt T) := by
    rw [heq]
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) (mul_pos hT hsT) hden
  have hnonneg : 0 ≤ 1 / Real.sqrt x - 1 / Real.sqrt y := by
    rw [heq]
    exact div_nonneg (sub_nonneg.mpr hxy) (by positivity)
  have hsq := pow_le_pow_left₀ hnonneg hbound 2
  apply hsq.trans_eq
  rw [div_pow, mul_pow, Real.sq_sqrt hT.le]
  congr 1

theorem candidate_integrable_logCoefficient_difference_sq (x y u v : ℝ) :
    Integrable (fun ω ↦ (harperCandidateLogProcess ω u / Real.sqrt x -
      harperCandidateLogProcess ω v / Real.sqrt y) ^ 2) mu := by
  have hu := (memLp_two_iff_integrable_sq
    (candidate_integrable_logProcess u).aestronglyMeasurable).mpr
    (candidate_integrable_logProcess_sq u)
  have hv := (memLp_two_iff_integrable_sq
    (candidate_integrable_logProcess v).aestronglyMeasurable).mpr
    (candidate_integrable_logProcess_sq v)
  simpa only [div_eq_mul_inv] using
    ((hu.mul_const (Real.sqrt x)⁻¹).sub (hv.mul_const (Real.sqrt y)⁻¹)).integrable_sq

/-- Coefficient replacement splits into the complete-process translation
error and the deterministic inverse-square-root variation. -/
theorem candidate_integral_logCoefficient_difference_sq_le
    {T x y : ℝ} (hT : 0 < T) (hTx : T ≤ x) (hxy : x ≤ y) (u v : ℝ) :
    (∫ ω, (harperCandidateLogProcess ω u / Real.sqrt x -
      harperCandidateLogProcess ω v / Real.sqrt y) ^ 2 ∂mu) ≤
      (2 / T) * (∫ ω, (harperCandidateLogProcess ω u -
        harperCandidateLogProcess ω v) ^ 2 ∂mu) +
          (2 * (y - x) ^ 2 / T ^ 3) * candidateLogSecondMoment v := by
  have hx : 0 < x := hT.trans_le hTx
  have hy : 0 < y := hx.trans_le hxy
  have hb := candidate_inv_sqrt_sub_sq_le hT hTx hxy
  have hi : 1 / x ≤ 1 / T := one_div_le_one_div_of_le hT hTx
  have hp (ω : Omega) :
      (harperCandidateLogProcess ω u / Real.sqrt x -
        harperCandidateLogProcess ω v / Real.sqrt y) ^ 2 ≤
      (2 / T) * (harperCandidateLogProcess ω u - harperCandidateLogProcess ω v) ^ 2 +
        (2 * (y - x) ^ 2 / T ^ 3) * harperCandidateLogProcess ω v ^ 2 := by
    let A := harperCandidateLogProcess ω u - harperCandidateLogProcess ω v
    let B := harperCandidateLogProcess ω v
    have hid : harperCandidateLogProcess ω u / Real.sqrt x -
        harperCandidateLogProcess ω v / Real.sqrt y =
          A / Real.sqrt x + B * (1 / Real.sqrt x - 1 / Real.sqrt y) := by
      dsimp only [A, B]
      ring
    rw [hid]
    have hAB := sq_nonneg (A / Real.sqrt x - B * (1 / Real.sqrt x - 1 / Real.sqrt y))
    have hA := mul_le_mul_of_nonneg_right hi (sq_nonneg A)
    have hB := mul_le_mul_of_nonneg_right hb (sq_nonneg B)
    have hAsq : (A / Real.sqrt x) ^ 2 = (1 / x) * A ^ 2 := by
      rw [div_pow, Real.sq_sqrt hx.le]
      ring
    have hpre : (A / Real.sqrt x + B * (1 / Real.sqrt x - 1 / Real.sqrt y)) ^ 2 ≤
        2 * (A / Real.sqrt x) ^ 2 + 2 * (1 / Real.sqrt x - 1 / Real.sqrt y) ^ 2 * B ^ 2 := by
      nlinarith
    rw [hAsq] at hpre
    change _ ≤ (2 / T) * A ^ 2 + (2 * (y - x) ^ 2 / T ^ 3) * B ^ 2
    simp only [div_eq_mul_inv] at hA hB hpre ⊢
    nlinarith
  have hD : Integrable (fun ω ↦
      (harperCandidateLogProcess ω u - harperCandidateLogProcess ω v) ^ 2) mu := by
    simpa only [show v + (u - v) = u by ring] using
      candidate_integrable_logProcess_translation_sq (u - v) v
  have hV := candidate_integrable_logProcess_sq v
  have hcoeff := candidate_integrable_logCoefficient_difference_sq x y u v
  have hint := integral_mono hcoeff
    ((hD.const_mul (2 / T)).add (hV.const_mul (2 * (y - x) ^ 2 / T ^ 3))) hp
  change _ ≤ ∫ ω, (2 / T) * (harperCandidateLogProcess ω u - harperCandidateLogProcess ω v) ^ 2 +
    (2 * (y - x) ^ 2 / T ^ 3) * harperCandidateLogProcess ω v ^ 2 ∂mu at hint
  rw [integral_add (hD.const_mul (2 / T)) (hV.const_mul (2 * (y - x) ^ 2 / T ^ 3)),
    integral_const_mul, integral_const_mul] at hint
  exact hint

/-- The complete inverse-square-root coefficient is uniformly controlled by
one enclosing arithmetic window. -/
theorem candidate_logCoefficient_difference_sq_le_window
    {T x y d a u v b L : ℝ} (hT : 0 < T) (hTx : T ≤ x) (hxy : x ≤ y)
    (hd : y - x ≤ d) (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hbL : b ≤ L) (hL : 0 ≤ L) :
    (∫ ω, (harperCandidateLogProcess ω v / Real.sqrt x -
      harperCandidateLogProcess ω u / Real.sqrt y) ^ 2 ∂mu) ≤
      (4 / T) * candidateLogWindowSecondMoment a b +
        ((b - a) ^ 2 / T + 2 * d ^ 2 / T ^ 3) * (1 + L) := by
  have hcoeff := candidate_integral_logCoefficient_difference_sq_le hT hTx hxy v u
  have hdiff := candidate_logProcess_difference_sq_le_window hau huv hvb
  have hV := candidateLogSecondMoment_le_of_le hL (huv.trans (hvb.trans hbL))
  have hlen2 : (y - x) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (sub_nonneg.mpr hxy) hd 2
  have hpos : 0 ≤ (b - a) ^ 2 / T + 2 * d ^ 2 / T ^ 3 := by positivity
  have hdm := mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ 2 / T)
  have hVm := mul_le_mul_of_nonneg_left hV hpos
  have hV0 := candidateLogSecondMoment_nonneg u
  have hlenm := mul_le_mul_of_nonneg_right hlen2
    (by positivity : 0 ≤ 2 / T ^ 3 * candidateLogSecondMoment u)
  simp only [div_eq_mul_inv] at hcoeff hdm hVm hlenm ⊢
  nlinarith

/-- Uniform expected squared replacement error for all weighted samples in
a finite collection of logarithmic bins, including the `1/sqrt(v)` factor.
The sample positions and weights are arbitrary; the complete multiplicative
process and all its second moments are the concrete canonical model. -/
theorem candidate_sum_weighted_logCoefficient_difference_sq_le
    {ι : Type*} (s : ℕ → Finset ι) (weight x y u v : ℕ → ι → ℝ)
    {a L h C T d : ℝ} {n k : ℕ} (hh : 0 ≤ h) (hL : 0 ≤ L)
    (hT : 0 < T) (hC : 0 ≤ C)
    (hcover : a + ((n + k : ℕ) : ℝ) * h ≤ L)
    (hw : ∀ j ∈ Finset.range n, ∀ i ∈ s j, 0 ≤ weight j i)
    (hmass : ∀ j ∈ Finset.range n, (∑ i ∈ s j, weight j i) ≤ C * h)
    (hTx : ∀ j ∈ Finset.range n, ∀ i ∈ s j, T ≤ x j i)
    (hxy : ∀ j ∈ Finset.range n, ∀ i ∈ s j, x j i ≤ y j i)
    (hd : ∀ j ∈ Finset.range n, ∀ i ∈ s j, y j i - x j i ≤ d)
    (hleft : ∀ j ∈ Finset.range n, ∀ i ∈ s j, a + (j : ℝ) * h ≤ u j i)
    (hordered : ∀ j ∈ Finset.range n, ∀ i ∈ s j, u j i ≤ v j i)
    (hright : ∀ j ∈ Finset.range n, ∀ i ∈ s j,
      v j i ≤ a + ((j + k : ℕ) : ℝ) * h) :
    (∑ j ∈ Finset.range n, ∑ i ∈ s j, weight j i *
      (∫ ω, (harperCandidateLogProcess ω (v j i) / Real.sqrt (x j i) -
        harperCandidateLogProcess ω (u j i) / Real.sqrt (y j i)) ^ 2 ∂mu)) ≤
      C * ((4 / T) * (k : ℝ) * h *
        (1 + (n : ℝ) * h * Real.exp ((k : ℝ) * h)) * (1 + L) +
          (((k : ℝ) * h) ^ 2 / T + 2 * d ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L)) := by
  let I : ℕ → ℝ := fun j ↦ candidateLogWindowSecondMoment
    (a + (j : ℝ) * h) (a + ((j + k : ℕ) : ℝ) * h)
  let R := (((k : ℝ) * h) ^ 2 / T + 2 * d ^ 2 / T ^ 3) * (1 + L)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hpoint (j : ℕ) (hj : j ∈ Finset.range n) (i : ι) (hi : i ∈ s j) :
      (∫ ω, (harperCandidateLogProcess ω (v j i) / Real.sqrt (x j i) -
        harperCandidateLogProcess ω (u j i) / Real.sqrt (y j i)) ^ 2 ∂mu) ≤
          (4 / T) * I j + R := by
    have hbL : a + ((j + k : ℕ) : ℝ) * h ≤ L := by
      have hjn : j + k ≤ n + k := by have := Finset.mem_range.mp hj; omega
      have hjnR : ((j + k : ℕ) : ℝ) ≤ (n + k : ℕ) := by exact_mod_cast hjn
      have hm := mul_le_mul_of_nonneg_right hjnR hh
      linarith
    have hp := candidate_logCoefficient_difference_sq_le_window hT
      (hTx j hj i hi) (hxy j hj i hi) (hd j hj i hi)
      (hleft j hj i hi) (hordered j hj i hi) (hright j hj i hi) hbL hL
    have hlen : (a + ((j + k : ℕ) : ℝ) * h) - (a + (j : ℝ) * h) =
        (k : ℝ) * h := by push_cast; ring
    simpa only [hlen] using hp
  have hbin (j : ℕ) (hj : j ∈ Finset.range n) :
      (∑ i ∈ s j, weight j i * (∫ ω,
        (harperCandidateLogProcess ω (v j i) / Real.sqrt (x j i) -
          harperCandidateLogProcess ω (u j i) / Real.sqrt (y j i)) ^ 2 ∂mu)) ≤
            C * h * ((4 / T) * I j + R) := by
    calc
      _ ≤ ∑ i ∈ s j, weight j i * ((4 / T) * I j + R) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hpoint j hj i hi) (hw j hj i hi)
      _ = (∑ i ∈ s j, weight j i) * ((4 / T) * I j + R) := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hmass j hj)
        (add_nonneg (mul_nonneg (by positivity) (candidateLogWindowSecondMoment_nonneg _ _)) hR)
  have hsum := Finset.sum_le_sum (s := Finset.range n) hbin
  have heq : (∑ j ∈ Finset.range n, C * h * ((4 / T) * I j + R)) =
      C * ((4 / T) * (h * ∑ j ∈ Finset.range n, I j) + R * ((n : ℝ) * h)) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [heq] at hsum
  have hdisc := candidate_sum_logWindowSecondMoment_le_mesh hh hL hcover
  change h * (∑ j ∈ Finset.range n, I j) ≤ _ at hdisc
  have hm := mul_le_mul_of_nonneg_left hdisc (by positivity : 0 ≤ C * (4 / T))
  dsimp only [R] at hsum
  nlinarith

end Erdos.Problem1144
