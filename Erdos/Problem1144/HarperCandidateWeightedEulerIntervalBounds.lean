import Erdos.Problem1144.HarperCandidateWeightedEulerIntervalSplit
import Erdos.Problem1144.HarperCandidateEnergyNormalizerUpper

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-!
# Uniform arithmetic interval bounds after summing the prime factors

Both prime normalizers and the small-prime damping are discharged by
proved arithmetic estimates. These bounds concern the squarefree Euler
product; the complete spectral weight remains a separate exact factor.
-/

/-- A fully arithmetic bound for the literal finite Euler interval energy,
uniform in the terminal prime cutoff and the allowed positive shift. -/
theorem candidate_integral_shifted_euler_interval_arithmetic_le
    {y Y : ℕ} (hy : 4 ≤ y) (hyY : y ≤ Y) {a u v : ℝ}
    (ha : 0 < a) (hay : a * Real.log (y : ℝ) ≤ 1) (huv : u ≤ v)
    (hwindow : ∀ t ∈ Icc u v, |t| ≤ (Real.log (y : ℝ))⁻¹) :
    (∫ ω, candidateShiftedEulerIntervalEnergy Y a u v ω ^ (1 / 8 : ℝ)
        ∂Problem520.μ) ≤
      Real.exp (-(Real.log (Real.log (y : ℝ)) +
        Real.log candidateRankinNormalizerConstant) / 16) *
      (((1 + 1 / a) / (candidateRankinNormalizerConstant * Real.log (y : ℝ))) *
        Real.exp (8 * (1 + (Real.log 4 + 4) / Real.log 2)) *
        (v - u)) ^ (1 / 8 : ℝ) := by
  have hmass := candidate_shifted_prime_square_mass_lower hy ha.le hay
  have hnorm := candidate_largePrime_rankinNormalizer_upper hy hyY ha hay
  have hnorm0 : 0 ≤ ∏ p ∈ (Y + 1).primesBelow \ (y + 1).primesBelow,
      harperRankinEulerNormalizer p a :=
    Finset.prod_nonneg fun p _ ↦ (harperRankinEulerNormalizer_pos p a).le
  refine (candidate_integral_shifted_euler_interval_large_eighth_le
    (by omega) hyY ha.le huv hwindow).trans ?_
  apply mul_le_mul
  · apply Real.exp_le_exp.mpr
    linarith
  · apply Real.rpow_le_rpow
    · exact mul_nonneg (mul_nonneg hnorm0 (Real.exp_pos _).le) (sub_nonneg.mpr huv)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnorm (Real.exp_pos _).le) (sub_nonneg.mpr huv)
    · norm_num
  · exact Real.rpow_nonneg
      (mul_nonneg (mul_nonneg hnorm0 (Real.exp_pos _).le) (sub_nonneg.mpr huv)) _
  · positivity

private theorem cutoff_log_bounds {U : ℝ} (hU : 0 < U) (hU1 : U ≤ 1 / 4) :
    4 ≤ ⌊Real.exp (1 / (2 * U))⌋₊ ∧
      1 / (4 * U) ≤ Real.log (⌊Real.exp (1 / (2 * U))⌋₊ : ℝ) ∧
      Real.log (⌊Real.exp (1 / (2 * U))⌋₊ : ℝ) ≤ 1 / (2 * U) := by
  let L := 1 / (2 * U)
  have hL : Real.log 4 ≤ L := by
    have hl4 : Real.log 4 ≤ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact hl4.trans ((le_div_iff₀ (by positivity : 0 < 2 * U)).mpr (by nlinarith))
  have he : (4 : ℝ) ≤ Real.exp L := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 4)] using Real.exp_le_exp.mpr hL
  have hy : 4 ≤ ⌊Real.exp L⌋₊ := (Nat.le_floor_iff (Real.exp_pos L).le).mpr he
  have hypos : (0 : ℝ) < (⌊Real.exp L⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊Real.exp L⌋₊)
  have hfloor := Nat.lt_floor_add_one (Real.exp L)
  have hy4 : (4 : ℝ) ≤ (⌊Real.exp L⌋₊ : ℝ) := by exact_mod_cast hy
  have hhalf : Real.exp L / 2 ≤ (⌊Real.exp L⌋₊ : ℝ) := by linarith
  have hlower := Real.log_le_log (by positivity : 0 < Real.exp L / 2) hhalf
  rw [Real.log_div (Real.exp_pos L).ne' (by norm_num), Real.log_exp] at hlower
  have hl4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Real.log_le_log hypos (Nat.floor_le (Real.exp_pos L).le)
  rw [Real.log_exp] at hupper
  refine ⟨hy, ?_, hupper⟩
  have : L / 2 ≤ Real.log (⌊Real.exp L⌋₊ : ℝ) := by linarith
  simpa only [L, div_div, show (2 : ℝ) * U * 2 = 4 * U by ring] using this

/-- An absolute constant for the actual normalized small-height energy. -/
def candidateEulerIntervalMomentConstant : ℝ :=
  Real.exp ((Real.log 4 - Real.log candidateRankinNormalizerConstant) / 16) *
    (8 * Real.exp (8 * (1 + (Real.log 4 + 4) / Real.log 2)) /
      candidateRankinNormalizerConstant) ^ (1 / 8 : ℝ)

/-- On a height band of size `U`, the actual normalized finite Euler energy
has a positive `U^(1/16)` saving. All prime cutoffs and shift inequalities
are literal; the terminal cutoff `Y` is arbitrary above the small cutoff. -/
theorem candidate_integral_shifted_euler_interval_scaled_le
    {U a u v : ℝ} (hU : 0 < U) (hU1 : U ≤ 1 / 4)
    (ha : 0 < a) (haU : a ≤ 2 * U) (huv : u ≤ v) (hlen : v - u ≤ U)
    (hwindow : ∀ t ∈ Icc u v, |t| ≤ 2 * U)
    {Y : ℕ} (hY : ⌊Real.exp (1 / (2 * U))⌋₊ ≤ Y) :
    (∫ ω, (a / U ^ 2 * candidateShiftedEulerIntervalEnergy Y a u v ω) ^
        (1 / 8 : ℝ) ∂Problem520.μ) ≤
      candidateEulerIntervalMomentConstant * U ^ (1 / 16 : ℝ) := by
  let y := ⌊Real.exp (1 / (2 * U))⌋₊
  obtain ⟨hy, hlower, hupper⟩ := cutoff_log_bounds hU hU1
  change 4 ≤ y at hy
  change 1 / (4 * U) ≤ Real.log (y : ℝ) at hlower
  change Real.log (y : ℝ) ≤ 1 / (2 * U) at hupper
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hc := candidateRankinNormalizerConstant_pos
  have ha1 : a ≤ 1 := by linarith
  have hlen0 : 0 ≤ v - u := sub_nonneg.mpr huv
  have hay : a * Real.log (y : ℝ) ≤ 1 := by
    calc
      _ ≤ (2 * U) * (1 / (2 * U)) := mul_le_mul haU hupper hlog.le (by positivity)
      _ = 1 := by field_simp
  have hw (t : ℝ) (ht : t ∈ Icc u v) : |t| ≤ (Real.log (y : ℝ))⁻¹ := by
    apply (hwindow t ht).trans
    rw [← one_div]
    apply (le_div_iff₀ hlog).mpr
    exact (mul_le_mul_of_nonneg_left hupper (by positivity : 0 ≤ 2 * U)).trans_eq (by field_simp)
  let C := Real.exp (8 * (1 + (Real.log 4 + 4) / Real.log 2))
  let c := candidateRankinNormalizerConstant
  let N := (1 + 1 / a) / (c * Real.log (y : ℝ))
  have hN0 : 0 ≤ N := by dsimp [N, c]; positivity
  have hN : N ≤ 8 * U / (a * c) := by
    have hn : 1 + 1 / a ≤ 2 / a := by
      apply (le_div_iff₀ ha).mpr
      field_simp
      linarith
    calc
      N ≤ (2 / a) / (c * (1 / (4 * U))) := by
        dsimp only [N]
        apply div_le_div₀ (by positivity) hn (by dsimp [c]; positivity)
        exact mul_le_mul_of_nonneg_left hlower hc.le
      _ = _ := by field_simp; ring
  have hb : a / U ^ 2 * (N * C * (v - u)) ≤ 8 * C / c := by
    calc
      _ ≤ a / U ^ 2 * ((8 * U / (a * c)) * C * U) := by
        gcongr
      _ = _ := by field_simp
  have hd : Real.exp (-(Real.log (Real.log (y : ℝ)) + Real.log c) / 16) ≤
      Real.exp ((Real.log 4 - Real.log c) / 16) * U ^ (1 / 16 : ℝ) := by
    rw [Real.rpow_def_of_pos hU, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl := Real.log_le_log (by positivity : 0 < 1 / (4 * U)) hlower
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hU.ne'] at hl
    linarith
  have hI := candidate_integral_shifted_euler_interval_arithmetic_le hy hY ha hay huv hw
  have hscalar : 0 ≤ a / U ^ 2 := by positivity
  simp_rw [Real.mul_rpow hscalar (candidate_shifted_euler_interval_nonneg Y a u v _)]
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hI (Real.rpow_nonneg hscalar _)).trans ?_
  change (a / U ^ 2) ^ (1 / 8 : ℝ) *
    (Real.exp (-(Real.log (Real.log (y : ℝ)) + Real.log c) / 16) *
      (N * C * (v - u)) ^ (1 / 8 : ℝ)) ≤ _
  have hbudget0 : 0 ≤ N * C * (v - u) := by positivity
  calc
    _ = Real.exp (-(Real.log (Real.log (y : ℝ)) + Real.log c) / 16) *
        (a / U ^ 2 * (N * C * (v - u))) ^ (1 / 8 : ℝ) := by
      rw [Real.mul_rpow hscalar hbudget0]
      ring
    _ ≤ (Real.exp ((Real.log 4 - Real.log c) / 16) * U ^ (1 / 16 : ℝ)) *
        (8 * C / c) ^ (1 / 8 : ℝ) := by
      apply mul_le_mul hd
      · exact Real.rpow_le_rpow (mul_nonneg hscalar hbudget0) hb (by norm_num)
      · exact Real.rpow_nonneg (mul_nonneg hscalar hbudget0) _
      · positivity
    _ = _ := by dsimp [candidateEulerIntervalMomentConstant, C, c]; ring

end
end Erdos.Problem1144
