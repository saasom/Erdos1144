import Erdos.Problem520.HarperPrimeBlockAsymptotic

open Set Filter Finset
open scoped BigOperators

noncomputable section

namespace Erdos
namespace Problem1144

/-!
# Wide-interval reciprocal-prime mass for the #1144 sampling step

The prime-sampling change of variables produces intervals whose endpoints
are different fixed powers of the ambient cutoff.  They are much shorter than
the square blocks used by the #520 schedule, but still have logarithmic width
comparable with their height.  This file extracts the corresponding uniform
positive reciprocal-prime mass from the already kernel-checked medium PNT.
-/

open Problem520

/-- A relative theta error, logarithmic interval width, and a coarse upper
comparison for `log B` imply a positive reciprocal-prime mass. -/
theorem freshReciprocalSum_lower_of_wide_log_interval
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) {delta K : ℝ}
    (hdelta : delta ≤ 1 / 4)
    (hlogWidth : 2 ≤ Real.log ((B : ℝ) / A))
    (hK : 0 < K)
    (hlogB : Real.log (B : ℝ) ≤ K * Real.log ((B : ℝ) / A))
    (herror : ∀ x ∈ Set.Icc (A : ℝ) B,
      |thetaError x| ≤ delta * x) :
    1 / (2 * K) ≤ freshReciprocalSum A B := by
  let L : ℝ := Real.log ((B : ℝ) / A)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have habs := abs_weightedPrimeReciprocalBlock_sub_log_le_of_thetaError
    hA hAB herror
  have hdeltaL : delta * L ≤ L / 4 := by
    exact (mul_le_mul_of_nonneg_right hdelta hLpos.le).trans_eq (by ring)
  have htwodelta : 2 * delta ≤ L / 4 := by
    have : 2 * delta ≤ 1 / 2 := by linarith
    linarith
  have hweighted : L / 2 ≤ weightedPrimeReciprocalBlock A B := by
    have hneg := neg_le_of_abs_le habs
    dsimp [L] at hneg hdeltaL htwodelta ⊢
    linarith
  have hsum_nonneg : 0 ≤ freshReciprocalSum A B := by
    unfold freshReciprocalSum
    positivity
  have hweightedUpper :=
    weightedPrimeReciprocalBlock_le_log_mul_freshReciprocalSum
      (A := A) (B := B)
  have hlogMul :
      Real.log (B : ℝ) * freshReciprocalSum A B ≤
        (K * L) * freshReciprocalSum A B :=
    mul_le_mul_of_nonneg_right (by simpa [L] using hlogB) hsum_nonneg
  have hcancel : (1 / 2 : ℝ) ≤ K * freshReciprocalSum A B := by
    apply (mul_le_mul_iff_of_pos_left hLpos).mp
    calc
      L * (1 / 2 : ℝ) = L / 2 := by ring
      _ ≤ weightedPrimeReciprocalBlock A B := hweighted
      _ ≤ Real.log (B : ℝ) * freshReciprocalSum A B := hweightedUpper
      _ ≤ (K * L) * freshReciprocalSum A B := hlogMul
      _ = L * (K * freshReciprocalSum A B) := by ring
  calc
    1 / (2 * K) = (1 / 2 : ℝ) / K := by ring
    _ ≤ freshReciprocalSum A B := by
      rw [div_le_iff₀ hK]
      simpa [mul_comm] using hcancel

theorem mediumThetaBlockDelta_mono_upper_of_le_square
    {c C : ℝ} {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B)
    (hB : B ≤ A ^ 2) :
    mediumThetaBlockDelta c C A B ≤ mediumThetaBlockDelta c C A (A ^ 2) := by
  have hApos : (0 : ℝ) < A := by positivity
  have hBpos : (0 : ℝ) < B := hApos.trans_le (by exact_mod_cast hAB)
  have hlog : Real.log (B : ℝ) ≤ Real.log ((A ^ 2 : ℕ) : ℝ) :=
    Real.log_le_log hBpos (by exact_mod_cast hB)
  unfold mediumThetaBlockDelta
  gcongr

/-- Reciprocal-prime mass is monotone in the upper endpoint. -/
theorem freshReciprocalSum_mono_right
    {A B C : ℕ} (hBC : B ≤ C) :
    freshReciprocalSum A B ≤ freshReciprocalSum A C := by
  unfold freshReciprocalSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [mem_freshPrimes] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.trans hBC⟩
  · intro p _hpC _hpB
    positivity

/-- Every subinterval of a sufficiently large square block has uniformly
bounded reciprocal-prime mass.  This is the upper estimate used under an
endpoint screen: the fresh conditional variance cannot concentrate into an
arbitrarily high spike. -/
theorem exists_mediumPNT_square_range_primeReciprocalBlock_upper :
    ∃ N : ℕ, ∀ A B : ℕ, N ≤ A → A ≤ B → B ≤ A ^ 2 →
      freshReciprocalSum A B ≤ 3 / 2 := by
  obtain ⟨N, hN⟩ := exists_mediumPNT_square_primeReciprocalBlock_bounds
  refine ⟨N, ?_⟩
  intro A B hNA _hAB hBA2
  exact (freshReciprocalSum_mono_right hBA2).trans (hN A hNA).2

/-- Unconditional medium-PNT lower bound, uniform over every sufficiently
large interval whose logarithmic width is at least two, whose upper endpoint
is at most the square of its lower endpoint, and with
`log B <= 10 log(B/A)`.  The constant `1/20` is intentionally loose. -/
theorem exists_mediumPNT_wide_primeReciprocalBlock_lower :
    ∃ N : ℕ, ∀ A B : ℕ, N ≤ A → A ≤ B → B ≤ A ^ 2 →
      2 ≤ Real.log ((B : ℝ) / A) →
      Real.log (B : ℝ) ≤ 10 * Real.log ((B : ℝ) / A) →
      (1 / 20 : ℝ) ≤ freshReciprocalSum A B := by
  obtain ⟨c, hc, C, hC, X₀, _hX₀two, htheta⟩ := exists_mediumThetaError
  obtain ⟨Ndelta, hNdelta⟩ :=
    exists_mediumThetaBlockDelta_square_le_quarter (C := C) hc
  obtain ⟨NX, hNX⟩ := exists_nat_ge X₀
  let N := max 2 (max Ndelta NX)
  refine ⟨N, ?_⟩
  intro A B hNA hAB hBA2 hwidth hlogB
  have hA2 : 2 ≤ A := (le_max_left 2 _).trans hNA
  have hAdelta : Ndelta ≤ A :=
    (le_max_left Ndelta NX).trans ((le_max_right 2 _).trans hNA)
  have hANX : NX ≤ A :=
    (le_max_right Ndelta NX).trans ((le_max_right 2 _).trans hNA)
  let delta := mediumThetaBlockDelta c C A B
  have hdelta : delta ≤ 1 / 4 := by
    exact (mediumThetaBlockDelta_mono_upper_of_le_square
      hA2 hAB hBA2).trans (hNdelta A hAdelta)
  have hX₀A : X₀ ≤ (A : ℝ) := hNX.trans (by exact_mod_cast hANX)
  have herror : ∀ x ∈ Set.Icc (A : ℝ) B,
      |thetaError x| ≤ delta * x := by
    intro x hx
    exact thetaError_le_mediumThetaBlockDelta hc hC.le htheta
      hA2 hAB hX₀A hx
  have hlower := freshReciprocalSum_lower_of_wide_log_interval
    (A := A) (B := B) (delta := delta) (K := 10)
    (show 1 ≤ A by omega) hAB hdelta hwidth
    (by norm_num) hlogB herror
  norm_num at hlower ⊢
  exact hlower

theorem log_nat_two_pow (e : ℕ) :
    Real.log (((2 ^ e : ℕ) : ℝ)) = (e : ℝ) * Real.log 2 := by
  push_cast
  rw [Real.log_pow]

theorem natCast_two_pow_div_two_pow {a b : ℕ} (hab : a ≤ b) :
    (((2 ^ b : ℕ) : ℝ) / ((2 ^ a : ℕ) : ℝ)) =
      (2 : ℝ) ^ (b - a) := by
  push_cast
  rw [div_eq_iff (by positivity : (2 : ℝ) ^ a ≠ 0)]
  rw [← pow_add]
  congr 1
  omega

/-- On the power-of-two schedule `X = 2^(21m)`, division by the dyadic
energy mesh `z = 2^k` produces the exact prime interval

`(2^(24m-k), 2^(28m-1-k)]`.

Every such interval with `0 <= k <= 3m` has a uniform reciprocal-prime mass.
This is the floor-free arithmetic core of the #1144 prime-sampling step. -/
theorem exists_powerTwo_primeSampling_mass :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ k : ℕ, k ≤ 3 * m →
      (1 / 20 : ℝ) ≤
        freshReciprocalSum (2 ^ (24 * m - k)) (2 ^ (28 * m - 1 - k)) := by
  obtain ⟨N, hN⟩ := exists_mediumPNT_wide_primeReciprocalBlock_lower
  let m₀ := max N 1
  refine ⟨m₀, ?_⟩
  intro m hm k hk
  let a := 24 * m - k
  let b := 28 * m - 1 - k
  have hm1 : 1 ≤ m := (le_max_right N 1).trans hm
  have hNm : N ≤ m := (le_max_left N 1).trans hm
  have hka : k ≤ 24 * m := by omega
  have hkb : k ≤ 28 * m - 1 := by omega
  have ha : a = 24 * m - k := rfl
  have hb : b = 28 * m - 1 - k := rfl
  have habExp : a ≤ b := by dsimp [a, b]; omega
  have hbTwoA : b ≤ 2 * a := by dsimp [a, b]; omega
  have hNA : N ≤ 2 ^ a := by
    have hma : m ≤ a := by dsimp [a]; omega
    exact hNm.trans ((Nat.lt_two_pow_self (n := m)).le.trans
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hma))
  have hAB : 2 ^ a ≤ 2 ^ b :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) habExp
  have hBA2 : 2 ^ b ≤ (2 ^ a) ^ 2 := by
    calc
      2 ^ b ≤ 2 ^ (2 * a) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hbTwoA
      _ = (2 ^ a) ^ 2 := by
        rw [Nat.mul_comm 2 a, ← pow_mul]
  have hdiff : b - a = 4 * m - 1 := by dsimp [a, b]; omega
  have hratio :
      Real.log ((((2 ^ b : ℕ) : ℝ) / ((2 ^ a : ℕ) : ℝ))) =
        ((4 * m - 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [natCast_two_pow_div_two_pow habExp, Real.log_pow]
    rw [hdiff]
  have hwidth :
      2 ≤ Real.log ((((2 ^ b : ℕ) : ℝ) / ((2 ^ a : ℕ) : ℝ))) := by
    rw [hratio]
    have hexp : (3 : ℝ) ≤ ((4 * m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 ≤ 4 * m - 1 by omega)
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    calc
      (2 : ℝ) ≤ 3 * Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      _ ≤ ((4 * m - 1 : ℕ) : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hexp hlog.le
  have hlogB :
      Real.log (((2 ^ b : ℕ) : ℝ)) ≤
        10 * Real.log ((((2 ^ b : ℕ) : ℝ) / ((2 ^ a : ℕ) : ℝ))) := by
    rw [log_nat_two_pow, hratio]
    have hcoeff : (b : ℝ) ≤ 10 * ((4 * m - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show b ≤ 10 * (4 * m - 1) by
        dsimp [b]
        omega)
    have hlog2nonneg : (0 : ℝ) ≤ Real.log 2 :=
      (Real.log_pos (by norm_num)).le
    calc
      (b : ℝ) * Real.log 2 ≤
          (10 * ((4 * m - 1 : ℕ) : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hcoeff hlog2nonneg
      _ = 10 * (((4 * m - 1 : ℕ) : ℝ) * Real.log 2) := by ring
  exact hN (2 ^ a) (2 ^ b) hNA hAB hBA2 hwidth hlogB

/-- Shell-safe version of the sampling interval.  If `2^k <= z <= 2^(k+1)`,
the fixed interval below sits strictly inside the transformed interval
`(2^(24m)/z, 2^(28m-1)/z]`.  The extra two powers of two remove all
floor/ceiling bookkeeping while preserving a uniform reciprocal mass. -/
theorem exists_powerTwo_shell_primeSampling_mass :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ k : ℕ, k ≤ 3 * m →
      (1 / 20 : ℝ) ≤
        freshReciprocalSum (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) := by
  obtain ⟨N, hN⟩ := exists_mediumPNT_wide_primeReciprocalBlock_lower
  let m₀ := max N 3
  refine ⟨m₀, ?_⟩
  intro m hm k hk
  let a := 24 * m - k
  let b := 28 * m - 3 - k
  have hm3 : 3 ≤ m := (le_max_right N 3).trans hm
  have hNm : N ≤ m := (le_max_left N 3).trans hm
  have hka : k ≤ 24 * m := by omega
  have hkb : k ≤ 28 * m - 3 := by omega
  have habExp : a ≤ b := by dsimp [a, b]; omega
  have hbTwoA : b ≤ 2 * a := by dsimp [a, b]; omega
  have hNA : N ≤ 2 ^ a := by
    have hma : m ≤ a := by dsimp [a]; omega
    exact hNm.trans ((Nat.lt_two_pow_self (n := m)).le.trans
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hma))
  have hAB : 2 ^ a ≤ 2 ^ b :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) habExp
  have hBA2 : 2 ^ b ≤ (2 ^ a) ^ 2 := by
    calc
      2 ^ b ≤ 2 ^ (2 * a) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hbTwoA
      _ = (2 ^ a) ^ 2 := by
        rw [Nat.mul_comm 2 a, ← pow_mul]
  have hdiff : b - a = 4 * m - 3 := by dsimp [a, b]; omega
  have hratio :
      Real.log ((((2 ^ b : ℕ) : ℝ) / ((2 ^ a : ℕ) : ℝ))) =
        ((4 * m - 3 : ℕ) : ℝ) * Real.log 2 := by
    rw [natCast_two_pow_div_two_pow habExp, Real.log_pow]
    rw [hdiff]
  have hwidth :
      2 ≤ Real.log ((((2 ^ b : ℕ) : ℝ) / ((2 ^ a : ℕ) : ℝ))) := by
    rw [hratio]
    have hexp : (5 : ℝ) ≤ ((4 * m - 3 : ℕ) : ℝ) := by
      exact_mod_cast (show 5 ≤ 4 * m - 3 by omega)
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    calc
      (2 : ℝ) ≤ 5 * Real.log 2 := by
        nlinarith [Real.log_two_gt_d9]
      _ ≤ ((4 * m - 3 : ℕ) : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hexp hlog.le
  have hlogB :
      Real.log (((2 ^ b : ℕ) : ℝ)) ≤
        10 * Real.log ((((2 ^ b : ℕ) : ℝ) / ((2 ^ a : ℕ) : ℝ))) := by
    rw [log_nat_two_pow, hratio]
    have hcoeff : (b : ℝ) ≤ 10 * ((4 * m - 3 : ℕ) : ℝ) := by
      exact_mod_cast (show b ≤ 10 * (4 * m - 3) by
        dsimp [b]
        omega)
    have hlog2nonneg : (0 : ℝ) ≤ Real.log 2 :=
      (Real.log_pos (by norm_num)).le
    calc
      (b : ℝ) * Real.log 2 ≤
          (10 * ((4 * m - 3 : ℕ) : ℝ)) * Real.log 2 :=
        mul_le_mul_of_nonneg_right hcoeff hlog2nonneg
      _ = 10 * (((4 * m - 3 : ℕ) : ℝ) * Real.log 2) := by ring
  exact hN (2 ^ a) (2 ^ b) hNA hAB hBA2 hwidth hlogB

/-- Deterministic containment behind the shell-safe interval: every selected
prime sends every `z` in the `k`th dyadic shell into the endpoint window, with
one additional factor-of-two margin at the upper end. -/
theorem powerTwo_shell_prime_product_bounds
    {m k p : ℕ} {z : ℝ}
    (hm : 1 ≤ m)
    (hk : k ≤ 3 * m)
    (hzLower : (((2 ^ k : ℕ) : ℝ)) ≤ z)
    (hzUpper : z ≤ (((2 ^ (k + 1) : ℕ) : ℝ)))
    (hpLower : 2 ^ (24 * m - k) < p)
    (hpUpper : p ≤ 2 ^ (28 * m - 3 - k)) :
    (((2 ^ (24 * m) : ℕ) : ℝ)) < (p : ℝ) * z ∧
      (p : ℝ) * z ≤ (((2 ^ (28 * m - 2) : ℕ) : ℝ)) := by
  have hkm24 : k ≤ 24 * m := by omega
  have hkm28 : k ≤ 28 * m - 3 := by omega
  have hpowkPos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hpNonneg : (0 : ℝ) ≤ p := by positivity
  have hzNonneg : (0 : ℝ) ≤ z :=
    le_trans (by positivity : (0 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ)) hzLower
  constructor
  · calc
      (((2 ^ (24 * m) : ℕ) : ℝ)) =
          (((2 ^ (24 * m - k) : ℕ) : ℝ)) *
            (((2 ^ k : ℕ) : ℝ)) := by
        push_cast
        rw [← pow_add]
        congr 1
        omega
      _ < (p : ℝ) * (((2 ^ k : ℕ) : ℝ)) := by
        exact mul_lt_mul_of_pos_right (by exact_mod_cast hpLower) hpowkPos
      _ ≤ (p : ℝ) * z :=
        mul_le_mul_of_nonneg_left hzLower hpNonneg
  · calc
      (p : ℝ) * z ≤
          (((2 ^ (28 * m - 3 - k) : ℕ) : ℝ)) *
            (((2 ^ (k + 1) : ℕ) : ℝ)) :=
        mul_le_mul (by exact_mod_cast hpUpper) hzUpper hzNonneg (by positivity)
      _ = (((2 ^ (28 * m - 2) : ℕ) : ℝ)) := by
        push_cast
        rw [← pow_add]
        have hexp : (28 * m - 3 - k) + (k + 1) = 28 * m - 2 := by
          omega
        rw [hexp]

/-- Division form of `powerTwo_shell_prime_product_bounds`.  Thus the fixed
prime interval from `exists_powerTwo_shell_primeSampling_mass` is genuinely a
subinterval of the transformed prime range for every real point of the shell;
there is no floor or ceiling loss. -/
theorem powerTwo_shell_prime_division_bounds
    {m k p : ℕ} {z : ℝ}
    (hm : 1 ≤ m)
    (hk : k ≤ 3 * m)
    (hzLower : (((2 ^ k : ℕ) : ℝ)) ≤ z)
    (hzUpper : z ≤ (((2 ^ (k + 1) : ℕ) : ℝ)))
    (hpLower : 2 ^ (24 * m - k) < p)
    (hpUpper : p ≤ 2 ^ (28 * m - 3 - k)) :
    (((2 ^ (24 * m) : ℕ) : ℝ)) / z < (p : ℝ) ∧
      (p : ℝ) ≤ (((2 ^ (28 * m - 1) : ℕ) : ℝ)) / z := by
  have hzPos : 0 < z :=
    (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ)).trans_le hzLower
  obtain ⟨hpzLower, hpzUpper⟩ := powerTwo_shell_prime_product_bounds
    hm hk hzLower hzUpper hpLower hpUpper
  constructor
  · rwa [div_lt_iff₀ hzPos]
  · rw [le_div_iff₀ hzPos]
    refine hpzUpper.trans ?_
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (show 28 * m - 2 ≤ 28 * m - 1 by omega)

/-- The whole dyadic `z`-shell lies inside the scaled integration interval
attached to every prime in the shell-safe block. -/
theorem powerTwo_shell_scaled_interval_bounds
    {m k p : ℕ}
    (hm : 1 ≤ m)
    (hk : k ≤ 3 * m)
    (hpLower : 2 ^ (24 * m - k) < p)
    (hpUpper : p ≤ 2 ^ (28 * m - 3 - k)) :
    (((2 ^ (24 * m) : ℕ) : ℝ)) / p ≤ (((2 ^ k : ℕ) : ℝ)) ∧
      (((2 ^ (k + 1) : ℕ) : ℝ)) ≤
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)) / p := by
  have hpNatPos : 0 < p :=
    (by positivity : 0 < 2 ^ (24 * m - k)).trans hpLower
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpNatPos
  have hkPow : (2 ^ k : ℕ) ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hLow := (powerTwo_shell_prime_product_bounds
    (z := ((2 ^ k : ℕ) : ℝ)) hm hk le_rfl (by exact_mod_cast hkPow)
      hpLower hpUpper).1
  have hHigh := (powerTwo_shell_prime_product_bounds
    (z := ((2 ^ (k + 1) : ℕ) : ℝ)) hm hk (by exact_mod_cast hkPow) le_rfl
      hpLower hpUpper).2
  constructor
  · rw [div_le_iff₀ hpPos]
    simpa [mul_comm] using hLow.le
  · rw [le_div_iff₀ hpPos]
    have hPower := Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (show 28 * m - 2 ≤ 28 * m - 1 by omega)
    have hHigh' :
        (((2 ^ (k + 1) : ℕ) : ℝ)) * p ≤
          (((2 ^ (28 * m - 2) : ℕ) : ℝ)) := by
      simpa [mul_comm] using hHigh
    have hPower' :
        (((2 ^ (28 * m - 2) : ℕ) : ℝ)) ≤
          (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
      exact_mod_cast hPower
    exact hHigh'.trans hPower'

/-- On the same schedule, the entire fresh-prime range of every candidate
endpoint is contained in one square block.  Its reciprocal mass is therefore
bounded by the absolute constant `3/2`, uniformly in the endpoint. -/
theorem exists_powerTwo_freshReciprocalMass_upper :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ x : ℕ,
      2 ^ (24 * m) ≤ x → x ≤ 2 ^ (28 * m - 1) →
      freshReciprocalSum (2 ^ (21 * m)) (2 * x) ≤ 3 / 2 := by
  obtain ⟨N, hN⟩ := exists_mediumPNT_square_range_primeReciprocalBlock_upper
  let m₀ := max N 1
  refine ⟨m₀, ?_⟩
  intro m hm x hxLower hxUpper
  have hm1 : 1 ≤ m := (le_max_right N 1).trans hm
  have hNm : N ≤ m := (le_max_left N 1).trans hm
  have hNA : N ≤ 2 ^ (21 * m) :=
    hNm.trans ((Nat.lt_two_pow_self (n := m)).le.trans
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)))
  have hAB : 2 ^ (21 * m) ≤ 2 * x := by
    calc
      2 ^ (21 * m) ≤ 2 ^ (24 * m) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
      _ ≤ x := hxLower
      _ ≤ 2 * x := Nat.le_mul_of_pos_left x (by norm_num)
  have hBupper : 2 * x ≤ 2 ^ (28 * m) := by
    calc
      2 * x ≤ 2 * 2 ^ (28 * m - 1) :=
        Nat.mul_le_mul_left 2 hxUpper
      _ = 2 ^ (28 * m) := by
        calc
          2 * 2 ^ (28 * m - 1) = 2 ^ (28 * m - 1) * 2 := by omega
          _ = 2 ^ ((28 * m - 1) + 1) := (pow_succ _ _).symm
          _ = 2 ^ (28 * m) := by congr 1; omega
  have hExp : 28 * m ≤ 42 * m := by omega
  have hBA2 : 2 * x ≤ (2 ^ (21 * m)) ^ 2 := by
    calc
      2 * x ≤ 2 ^ (28 * m) := hBupper
      _ ≤ 2 ^ (42 * m) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hExp
      _ = (2 ^ (21 * m)) ^ 2 := by
        rw [show 42 * m = (21 * m) * 2 by omega, ← pow_mul]
  exact hN (2 ^ (21 * m)) (2 * x) hNA hAB hBA2

/-- Uniform reciprocal mass bound for one fixed prime universe containing all
fresh primes used by the power-of-two endpoint window. -/
theorem exists_powerTwo_globalFreshReciprocalMass_upper :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      freshReciprocalSum (2 ^ (21 * m)) (2 ^ (28 * m)) ≤ 3 / 2 := by
  obtain ⟨m₀, hm₀⟩ := exists_powerTwo_freshReciprocalMass_upper
  refine ⟨max m₀ 1, ?_⟩
  intro m hm
  have hmOne : 1 ≤ m := (le_max_right m₀ 1).trans hm
  have hLower : 2 ^ (24 * m) ≤ 2 ^ (28 * m - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have h := hm₀ m ((le_max_left m₀ 1).trans hm)
    (2 ^ (28 * m - 1)) hLower le_rfl
  have htwo : 2 * 2 ^ (28 * m - 1) = 2 ^ (28 * m) := by
    calc
      2 * 2 ^ (28 * m - 1) = 2 ^ (28 * m - 1) * 2 := by omega
      _ = 2 ^ ((28 * m - 1) + 1) := (pow_succ 2 (28 * m - 1)).symm
      _ = 2 ^ (28 * m) := by congr 1; omega
  rwa [htwo] at h

end Problem1144
end Erdos
