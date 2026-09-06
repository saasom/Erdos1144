import Erdos.Problem1144.HarperPrimeSampling
import Erdos.Problem1144.Statistics
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Filter
open scoped Interval

namespace Erdos
namespace Problem1144

/-!
# The scaling identity behind logarithmic variance averaging

For one prime `p`, the substitution `x = p*z` converts the `x⁻²`-weighted
fresh-variance term into `p⁻¹` times the inverse-square energy on the scaled
interval.  This is the exact analytic core of the variance-averaging needle.
-/

/-- Abstract inverse-square scaling identity.  Written in this form, the
change of variables is a direct specialization of interval-integral scaling
and does not require any continuity of `f`. -/
theorem intervalIntegral_inv_sq_smul_comp_div
    (f : ℝ → ℝ) {a b p : ℝ} (hp : p ≠ 0) :
    (∫ x in a..b, p⁻¹ ^ 2 * f (x / p)) =
      p⁻¹ * ∫ z in a / p..b / p, f z := by
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_div f hp]
  simp only [smul_eq_mul]
  field_simp

/-- Real step-function extension of the summatory function. -/
noncomputable def realStepSum (omega : Omega) (x : ℝ) : ℝ :=
  S omega ⌊x⌋₊

/-- Dyadic increment of the real step-function extension. -/
noncomputable def realDyadicIncrement (omega : Omega) (x : ℝ) : ℝ :=
  realStepSum omega (2 * x) - realStepSum omega x

/-- Inverse-square dyadic-increment energy density. -/
noncomputable def realDyadicIncrementEnergyDensity
    (omega : Omega) (x : ℝ) : ℝ :=
  realDyadicIncrement omega x ^ 2 / x ^ 2

/-- The `k`th dyadic shell after scaling by a prime coordinate. -/
def powerTwoScaledShell (p k : ℕ) : Set ℝ :=
  Set.Ioc ((p : ℝ) * ((2 ^ k : ℕ) : ℝ))
    ((p : ℝ) * ((2 ^ (k + 1) : ℕ) : ℝ))

/-- A positive point belongs to at most one scaled dyadic shell for a fixed
positive prime coordinate. -/
theorem powerTwoScaledShell_mem_unique
    {p k l : ℕ} {x : ℝ} (hp : 0 < p)
    (hk : x ∈ powerTwoScaledShell p k)
    (hl : x ∈ powerTwoScaledShell p l) :
    k = l := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hkl | hlk
  · have hpow : (2 ^ (k + 1) : ℕ) ≤ 2 ^ l :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    have hscaled :
        (p : ℝ) * ((2 ^ (k + 1) : ℕ) : ℝ) ≤
          (p : ℝ) * ((2 ^ l : ℕ) : ℝ) := by
      gcongr
    exact (hl.1.trans_le (hk.2.trans hscaled)).false
  · have hpow : (2 ^ (l + 1) : ℕ) ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    have hscaled :
        (p : ℝ) * ((2 ^ (l + 1) : ℕ) : ℝ) ≤
          (p : ℝ) * ((2 ^ k : ℕ) : ℝ) := by
      gcongr
    exact (hk.1.trans_le (hl.2.trans hscaled)).false

noncomputable def powerTwoShellIndices
    (s : Finset ℕ) (p : ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact s.filter fun k => x ∈ powerTwoScaledShell p k

theorem card_powerTwoShellIndices_le_one
    (s : Finset ℕ) {p : ℕ} {x : ℝ} (hp : 0 < p) :
    (powerTwoShellIndices s p x).card ≤ 1 := by
  classical
  unfold powerTwoShellIndices
  rw [Finset.card_le_one_iff]
  intro k l hk hl
  exact powerTwoScaledShell_mem_unique hp
    (Finset.mem_filter.mp hk).2 (Finset.mem_filter.mp hl).2

/-- Shell indices whose shell-safe prime block contains `p` and whose scaled
shell contains `x`. -/
noncomputable def selectedPowerTwoShells (m p : ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (3 * m + 1)).filter fun k =>
    p ∈ Problem520.freshPrimes
      (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) ∧
    x ∈ powerTwoScaledShell p k

theorem card_selectedPowerTwoShells_le_one
    {m p : ℕ} {x : ℝ} (hp : 0 < p) :
    (selectedPowerTwoShells m p x).card ≤ 1 := by
  classical
  have hsubset : selectedPowerTwoShells m p x ⊆
      powerTwoShellIndices (Finset.range (3 * m + 1)) p x := by
    intro k hk
    have hkData := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hkData.1, hkData.2.2⟩
  exact (Finset.card_le_card hsubset).trans
    (card_powerTwoShellIndices_le_one (Finset.range (3 * m + 1)) hp)

/-- The multiplicity-free shell-restricted fresh-variance density, regrouped
by prime. -/
noncomputable def restrictedPowerTwoFreshVarianceDensity
    (omega : Omega) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Problem520.freshPrimes (2 ^ (21 * m)) (2 ^ (28 * m)),
    ((selectedPowerTwoShells m p x).card : ℝ) *
      (realDyadicIncrement omega (x / p) ^ 2 / x ^ 2)

/-- Full fresh-variance density on the fixed endpoint window. -/
noncomputable def fullPowerTwoFreshVarianceDensity
    (omega : Omega) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Problem520.freshPrimes (2 ^ (21 * m)) (2 ^ (28 * m)),
    if (p : ℝ) ≤ 2 * x then
      realDyadicIncrement omega (x / p) ^ 2 / x ^ 2
    else 0

/-- Indicator-sum presentation of the restricted density.  This is convenient
for integrating shell by shell; the regrouped cardinality presentation above
is convenient for pointwise comparison with the full variance. -/
noncomputable def restrictedPowerTwoFreshVarianceIndicatorDensity
    (omega : Omega) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ Problem520.freshPrimes (2 ^ (21 * m)) (2 ^ (28 * m)),
    ∑ k ∈ Finset.range (3 * m + 1),
      if p ∈ Problem520.freshPrimes
          (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
        (powerTwoScaledShell p k).indicator
          (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x
      else 0

theorem restrictedPowerTwoFreshVarianceIndicatorDensity_eq
    (omega : Omega) (m : ℕ) (x : ℝ) :
    restrictedPowerTwoFreshVarianceIndicatorDensity omega m x =
      restrictedPowerTwoFreshVarianceDensity omega m x := by
  classical
  unfold restrictedPowerTwoFreshVarianceIndicatorDensity
    restrictedPowerTwoFreshVarianceDensity
  apply Finset.sum_congr rfl
  intro p hp
  unfold selectedPowerTwoShells
  simp only [Set.indicator_apply]
  simp_rw [← ite_and]
  rw [← Finset.sum_filter]
  simp

theorem shellSafeFreshPrimes_subset_global
    {m k : ℕ} (hk : k ≤ 3 * m) :
    Problem520.freshPrimes
        (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) ⊆
      Problem520.freshPrimes (2 ^ (21 * m)) (2 ^ (28 * m)) := by
  intro p hp
  obtain ⟨hpPrime, hpLower, hpUpper⟩ := Problem520.mem_freshPrimes.mp hp
  apply Problem520.mem_freshPrimes.mpr
  refine ⟨hpPrime, ?_, ?_⟩
  · exact (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)).trans_lt hpLower
  · exact hpUpper.trans
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))

theorem powerTwoScaledShell_subset_endpointWindow
    {m k p : ℕ} (hm : 1 ≤ m) (hk : k ≤ 3 * m)
    (hp : p ∈ Problem520.freshPrimes
      (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k))) :
    powerTwoScaledShell p k ⊆
      Set.Ioc (((2 ^ (24 * m) : ℕ) : ℝ))
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
  have hpData := Problem520.mem_freshPrimes.mp hp
  have hkPow : (2 ^ k : ℕ) ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hLow := (powerTwo_shell_prime_product_bounds
    (z := ((2 ^ k : ℕ) : ℝ)) hm hk le_rfl (by exact_mod_cast hkPow)
      hpData.2.1 hpData.2.2).1
  have hHigh := (powerTwo_shell_prime_product_bounds
    (z := ((2 ^ (k + 1) : ℕ) : ℝ)) hm hk (by exact_mod_cast hkPow) le_rfl
      hpData.2.1 hpData.2.2).2
  have hHighEndpoint :
      (p : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ)) ≤
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    refine hHigh.trans ?_
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (show 28 * m - 2 ≤ 28 * m - 1 by omega)
  intro x hx
  exact ⟨hLow.trans hx.1, hx.2.trans hHighEndpoint⟩

theorem intervalIntegrable_setIndicator
    {f : ℝ → ℝ} {s : Set ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) volume a b :=
  ⟨hf.1.indicator hs, hf.2.indicator hs⟩

theorem intervalIntegral_indicator_Ioc_eq_of_subset
    (f : ℝ → ℝ) {A B a b : ℝ}
    (hAB : A ≤ B) (hab : a ≤ b) (hsub : Set.Ioc a b ⊆ Set.Ioc A B) :
    (∫ x in A..B, (Set.Ioc a b).indicator f x) = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hAB,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_right.mpr hsub,
    intervalIntegral.integral_of_le hab]

theorem intervalIntegral_powerTwoScaledShell_indicator_eq
    (omega : Omega) {m k p : ℕ}
    (hm : 1 ≤ m) (hk : k ≤ 3 * m)
    (hp : p ∈ Problem520.freshPrimes
      (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k))) :
    (∫ x in
        (((2 ^ (24 * m) : ℕ) : ℝ))..
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
      (powerTwoScaledShell p k).indicator
        (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x) =
      ∫ x in
          (p : ℝ) * (((2 ^ k : ℕ) : ℝ))..
          (p : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ)),
        realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 := by
  have hAB :
      (((2 ^ (24 * m) : ℕ) : ℝ)) ≤
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hshell :
      (p : ℝ) * (((2 ^ k : ℕ) : ℝ)) ≤
        (p : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg p)
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  exact intervalIntegral_indicator_Ioc_eq_of_subset _ hAB hshell
    (powerTwoScaledShell_subset_endpointWindow hm hk hp)

/-- Pointwise multiplicity-free comparison with the full fresh variance. -/
theorem restrictedPowerTwoFreshVarianceDensity_le_full
    (omega : Omega) (m : ℕ) (x : ℝ) :
    restrictedPowerTwoFreshVarianceDensity omega m x ≤
      fullPowerTwoFreshVarianceDensity omega m x := by
  classical
  unfold restrictedPowerTwoFreshVarianceDensity
    fullPowerTwoFreshVarianceDensity
  apply Finset.sum_le_sum
  intro p hpGlobal
  have hpPos : 0 < p := (Problem520.mem_freshPrimes.mp hpGlobal).1.pos
  have hcard := card_selectedPowerTwoShells_le_one
    (m := m) (x := x) hpPos
  by_cases hzero : (selectedPowerTwoShells m p x).card = 0
  · rw [hzero]
    simp only [Nat.cast_zero, zero_mul]
    split_ifs <;> positivity
  · have hcardPos : 0 < (selectedPowerTwoShells m p x).card :=
      Nat.pos_of_ne_zero hzero
    have hcardOne : (selectedPowerTwoShells m p x).card = 1 := by omega
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hcardPos
    have hshell : x ∈ powerTwoScaledShell p k :=
      (Finset.mem_filter.mp hk).2.2
    have hpRealPos : (0 : ℝ) < p := by exact_mod_cast hpPos
    have hpowOne : (1 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_two_pow
    have hpLeX : (p : ℝ) ≤ x := by
      calc
        (p : ℝ) = (p : ℝ) * 1 := by ring
        _ ≤ (p : ℝ) * ((2 ^ k : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hpowOne hpRealPos.le
        _ ≤ x := hshell.1.le
    have hpLeTwoX : (p : ℝ) ≤ 2 * x := by linarith
    simp [hcardOne, hpLeTwoX]

/-- A global square-root endpoint screen gives a loose but uniform screen for
every dyadic increment. -/
theorem abs_realDyadicIncrement_le_three_mul_sqrt
    (omega : Omega) {M t : ℝ} (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hScreen : ∀ u : ℝ, 0 ≤ u →
      |realStepSum omega u| ≤ M * Real.sqrt u) :
    |realDyadicIncrement omega t| ≤ 3 * M * Real.sqrt t := by
  have htTwo : 0 ≤ 2 * t := by positivity
  have hsqrt : Real.sqrt (2 * t) ≤ 2 * Real.sqrt t := by
    have hsqrtT := Real.sq_sqrt ht
    have hsqrtTwoT := Real.sq_sqrt htTwo
    have hsqrtTNonneg := Real.sqrt_nonneg t
    have hsqrtTwoTNonneg := Real.sqrt_nonneg (2 * t)
    nlinarith
  unfold realDyadicIncrement
  calc
    |realStepSum omega (2 * t) - realStepSum omega t| ≤
        |realStepSum omega (2 * t)| + |realStepSum omega t| := abs_sub _ _
    _ ≤ M * Real.sqrt (2 * t) + M * Real.sqrt t :=
      add_le_add (hScreen (2 * t) htTwo) (hScreen t ht)
    _ ≤ M * (2 * Real.sqrt t) + M * Real.sqrt t := by
      gcongr
    _ = 3 * M * Real.sqrt t := by ring

/-- Pointwise coefficient-square bound under the endpoint screen. -/
theorem realDyadicIncrement_comp_div_sq_div_sq_le
    (omega : Omega) {M x : ℝ} {p : ℕ}
    (hM : 0 ≤ M) (hx : 0 < x) (hp : 0 < p)
    (hScreen : ∀ u : ℝ, 0 ≤ u →
      |realStepSum omega u| ≤ M * Real.sqrt u) :
    realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 ≤
      9 * M ^ 2 * (p : ℝ)⁻¹ / x := by
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have ht : 0 ≤ x / (p : ℝ) := (div_pos hx hpReal).le
  have hinc := abs_realDyadicIncrement_le_three_mul_sqrt
    omega hM ht hScreen
  have hsq : realDyadicIncrement omega (x / p) ^ 2 ≤
      (3 * M * Real.sqrt (x / p)) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg
      (mul_nonneg (by norm_num) hM) (Real.sqrt_nonneg _))]
    exact hinc
  have hsqrtSq := Real.sq_sqrt ht
  calc
    realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 ≤
        (3 * M * Real.sqrt (x / p)) ^ 2 / x ^ 2 :=
      div_le_div_of_nonneg_right hsq (sq_nonneg x)
    _ = 9 * M ^ 2 * (Real.sqrt (x / p) ^ 2) / x ^ 2 := by ring
    _ = 9 * M ^ 2 * (p : ℝ)⁻¹ / x := by
      rw [hsqrtSq]
      field_simp

/-- Uniform full fresh-variance density bound from a reciprocal-prime mass
bound and a square-root endpoint screen. -/
theorem fullPowerTwoFreshVarianceDensity_le_of_screen
    (omega : Omega) {m : ℕ} {M x : ℝ}
    (hM : 0 ≤ M) (hx : 0 < x)
    (hScreen : ∀ u : ℝ, 0 ≤ u →
      |realStepSum omega u| ≤ M * Real.sqrt u)
    (hmass : Problem520.freshReciprocalSum
      (2 ^ (21 * m)) (2 ^ (28 * m)) ≤ 3 / 2) :
    fullPowerTwoFreshVarianceDensity omega m x ≤
      (27 / 2) * M ^ 2 / x := by
  classical
  unfold fullPowerTwoFreshVarianceDensity
  calc
    (∑ p ∈ Problem520.freshPrimes (2 ^ (21 * m)) (2 ^ (28 * m)),
        if (p : ℝ) ≤ 2 * x then
          realDyadicIncrement omega (x / p) ^ 2 / x ^ 2
        else 0) ≤
      ∑ p ∈ Problem520.freshPrimes (2 ^ (21 * m)) (2 ^ (28 * m)),
        9 * M ^ 2 * (p : ℝ)⁻¹ / x := by
      apply Finset.sum_le_sum
      intro p hpSet
      split_ifs
      · exact realDyadicIncrement_comp_div_sq_div_sq_le omega hM hx
          (Problem520.mem_freshPrimes.mp hpSet).1.pos hScreen
      · positivity
    _ = (9 * M ^ 2 / x) * Problem520.freshReciprocalSum
        (2 ^ (21 * m)) (2 ^ (28 * m)) := by
      rw [Problem520.freshReciprocalSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (9 * M ^ 2 / x) * (3 / 2) :=
      mul_le_mul_of_nonneg_left hmass (div_nonneg (by positivity) hx.le)
    _ = (27 / 2) * M ^ 2 / x := by ring

/-- Unconditional scheduled screen upper bound, with the reciprocal-prime
constant supplied by the internal PNT. -/
theorem exists_fullPowerTwoFreshVarianceDensity_screen_upper :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (omega : Omega) (M x : ℝ),
      0 ≤ M → 0 < x →
      (∀ u : ℝ, 0 ≤ u →
        |realStepSum omega u| ≤ M * Real.sqrt u) →
      fullPowerTwoFreshVarianceDensity omega m x ≤
        (27 / 2) * M ^ 2 / x := by
  obtain ⟨m₀, hm₀⟩ := exists_powerTwo_globalFreshReciprocalMass_upper
  refine ⟨m₀, ?_⟩
  intro m hm omega M x hM hx hScreen
  exact fullPowerTwoFreshVarianceDensity_le_of_screen
    omega hM hx hScreen (hm₀ m hm)

theorem measurable_realStepSum (omega : Omega) :
    Measurable (realStepSum omega) := by
  exact (measurable_of_countable (fun n : ℕ => S omega n)).comp
    measurable_id.nat_floor

theorem measurable_realDyadicIncrement (omega : Omega) :
    Measurable (realDyadicIncrement omega) := by
  exact ((measurable_realStepSum omega).comp
    (measurable_const.mul measurable_id)).sub (measurable_realStepSum omega)

theorem measurable_realDyadicIncrementEnergyDensity (omega : Omega) :
    Measurable (realDyadicIncrementEnergyDensity omega) := by
  exact ((measurable_realDyadicIncrement omega).pow_const 2).div
    (measurable_id.pow_const 2)

/-- The step-function energy density is integrable on every compact interval
bounded away from zero.  This discharges the only regularity premise in the
variance-averaging argument. -/
theorem integrableOn_realDyadicIncrementEnergyDensity_Icc
    (omega : Omega) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (realDyadicIncrementEnergyDensity omega) (Set.Icc a b) := by
  have hbNonneg : 0 ≤ b := ha.le.trans hab
  refine Measure.integrableOn_of_bounded (μ := volume) (s := Set.Icc a b)
    (M := (3 * b) ^ 2 / a ^ 2) measure_Icc_lt_top.ne
    (measurable_realDyadicIncrementEnergyDensity omega).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hxPos : 0 < x := ha.trans_le hx.1
  have hstepX : |realStepSum omega x| ≤ b := by
    exact (abs_S_le omega ⌊x⌋₊).trans ((Nat.floor_le hxPos.le).trans hx.2)
  have hxTwo : 0 ≤ 2 * x := by positivity
  have hstepTwoX : |realStepSum omega (2 * x)| ≤ 2 * b := by
    exact (abs_S_le omega ⌊2 * x⌋₊).trans
      ((Nat.floor_le hxTwo).trans (mul_le_mul_of_nonneg_left hx.2 (by norm_num)))
  have hinc : |realDyadicIncrement omega x| ≤ 3 * b := by
    unfold realDyadicIncrement
    calc
      |realStepSum omega (2 * x) - realStepSum omega x| ≤
          |realStepSum omega (2 * x)| + |realStepSum omega x| := abs_sub _ _
      _ ≤ 2 * b + b := add_le_add hstepTwoX hstepX
      _ = 3 * b := by ring
  have hincSq : realDyadicIncrement omega x ^ 2 ≤ (3 * b) ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg (mul_nonneg (by norm_num) hbNonneg)]
    exact hinc
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos ha
  have haSqLe : a ^ 2 ≤ x ^ 2 :=
    (sq_le_sq₀ ha.le hxPos.le).2 hx.1
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    unfold realDyadicIncrementEnergyDensity
    positivity)]
  unfold realDyadicIncrementEnergyDensity
  exact div_le_div₀ (sq_nonneg (3 * b)) hincSq haSqPos haSqLe

theorem intervalIntegrable_realDyadicIncrementEnergyDensity
    (omega : Omega) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (realDyadicIncrementEnergyDensity omega) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact integrableOn_realDyadicIncrementEnergyDensity_Icc omega ha hab

/-- Algebraic identity matching a fresh-variance summand with the scaled
inverse-square energy density. -/
theorem inv_sq_mul_realDyadicIncrementEnergyDensity_comp_div
    (omega : Omega) (x : ℝ) {p : ℕ} (hp : 0 < p) :
    (((p : ℝ)⁻¹) ^ 2) *
        realDyadicIncrementEnergyDensity omega (x / p) =
      realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 := by
  unfold realDyadicIncrementEnergyDensity
  by_cases hx : x = 0
  · simp [hx]
  · have hpReal : (p : ℝ) ≠ 0 := by positivity
    field_simp

/-- Prime-by-prime scaling identity for the actual dyadic-increment energy
density.  This is the equality used after Tonelli in the fresh-variance
average. -/
theorem intervalIntegral_realDyadicIncrementEnergyDensity_comp_div
    (omega : Omega) {a b : ℝ} {p : ℕ} (hp : 0 < p) :
    (∫ x in a..b,
        (((p : ℝ)⁻¹) ^ 2) *
          realDyadicIncrementEnergyDensity omega (x / p)) =
      (p : ℝ)⁻¹ *
        ∫ z in a / p..b / p,
          realDyadicIncrementEnergyDensity omega z := by
  exact intervalIntegral_inv_sq_smul_comp_div
    (realDyadicIncrementEnergyDensity omega) (by positivity)

/-- Prime-by-prime form used directly in the variance average:

`∫ D(x/p)^2 dx/x^2 = p⁻¹ ∫ D(z)^2 dz/z^2`.
-/
theorem intervalIntegral_realDyadicIncrement_comp_div_sq_div_sq
    (omega : Omega) {a b : ℝ} {p : ℕ} (hp : 0 < p) :
    (∫ x in a..b,
        realDyadicIncrement omega (x / p) ^ 2 / x ^ 2) =
      (p : ℝ)⁻¹ *
        ∫ z in a / p..b / p,
          realDyadicIncrement omega z ^ 2 / z ^ 2 := by
  rw [show
      (fun x : ℝ => realDyadicIncrement omega (x / p) ^ 2 / x ^ 2) =
        fun x : ℝ => (((p : ℝ)⁻¹) ^ 2) *
          realDyadicIncrementEnergyDensity omega (x / p) by
    funext x
    exact (inv_sq_mul_realDyadicIncrementEnergyDensity_comp_div
      omega x hp).symm]
  simpa only [realDyadicIncrementEnergyDensity] using
    intervalIntegral_realDyadicIncrementEnergyDensity_comp_div omega hp

/-- The fresh-variance summand is automatically interval integrable on every
positive compact interval. -/
theorem intervalIntegrable_realDyadicIncrement_comp_div_sq_div_sq
    (omega : Omega) {a b : ℝ} {p : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hp : 0 < p) :
    IntervalIntegrable
      (fun x : ℝ => realDyadicIncrement omega (x / p) ^ 2 / x ^ 2)
      volume a b := by
  have hpReal : (0 : ℝ) < p := by exact_mod_cast hp
  have hscaled := intervalIntegrable_realDyadicIncrementEnergyDensity
    omega (div_pos ha hpReal) (div_le_div_of_nonneg_right hab hpReal.le)
  have hcomp := hscaled.comp_mul_left (c := (p : ℝ)⁻¹)
  have hcomp' : IntervalIntegrable
      (fun x : ℝ => realDyadicIncrementEnergyDensity omega (x / p))
      volume a b := by
    convert hcomp using 1 <;> field_simp
  have hmul := hcomp'.const_mul (((p : ℝ)⁻¹) ^ 2)
  exact hmul.congr fun x _ =>
    inv_sq_mul_realDyadicIncrementEnergyDensity_comp_div omega x hp

/-- Exact shell-restricted scaling.  Keeping the `x`-integral on
`[p*a,p*b]` is what makes different dyadic shells disjoint when the estimates
are later summed. -/
theorem intervalIntegral_prime_mul_shell_eq_inv_mul_shell_energy
    (omega : Omega) {a b : ℝ} {p : ℕ} (hp : 0 < p) :
    (∫ x in (p : ℝ) * a..(p : ℝ) * b,
        realDyadicIncrement omega (x / p) ^ 2 / x ^ 2) =
      (p : ℝ)⁻¹ *
        ∫ z in a..b, realDyadicIncrement omega z ^ 2 / z ^ 2 := by
  have h := intervalIntegral_realDyadicIncrement_comp_div_sq_div_sq
    (omega := omega) (a := (p : ℝ) * a) (b := (p : ℝ) * b) hp
  convert h using 1
  all_goals field_simp

/-- Finite Tonelli/scaling identity for any positive finite prime-coordinate
set.  The only explicit premise is interval integrability of the finitely many
step-function summands; no probabilistic input is involved. -/
theorem intervalIntegral_sum_realDyadicIncrement_comp_div_sq_div_sq
    (omega : Omega) {a b : ℝ} (s : Finset ℕ)
    (hpos : ∀ p ∈ s, 0 < p)
    (hint : ∀ p ∈ s, IntervalIntegrable
      (fun x : ℝ => realDyadicIncrement omega (x / p) ^ 2 / x ^ 2)
      volume a b) :
    (∫ x in a..b,
        ∑ p ∈ s, realDyadicIncrement omega (x / p) ^ 2 / x ^ 2) =
      ∑ p ∈ s, (p : ℝ)⁻¹ *
        ∫ z in a / p..b / p,
          realDyadicIncrement omega z ^ 2 / z ^ 2 := by
  rw [intervalIntegral.integral_finset_sum hint]
  apply Finset.sum_congr rfl
  intro p hp
  exact intervalIntegral_realDyadicIncrement_comp_div_sq_div_sq
    omega (hpos p hp)

/-- Every shell-safe prime contributes at least the full dyadic-shell energy
after the scaling substitution. -/
theorem powerTwo_shell_energy_le_scaled_prime_energy
    (omega : Omega) {m k p : ℕ}
    (hm : 1 ≤ m)
    (hk : k ≤ 3 * m)
    (hpLower : 2 ^ (24 * m - k) < p)
    (hpUpper : p ≤ 2 ^ (28 * m - 3 - k)) :
    (∫ z in (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
        realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
      ∫ z in
          (((2 ^ (24 * m) : ℕ) : ℝ)) / p..
          (((2 ^ (28 * m - 1) : ℕ) : ℝ)) / p,
        realDyadicIncrement omega z ^ 2 / z ^ 2 := by
  obtain ⟨hleft, hright⟩ := powerTwo_shell_scaled_interval_bounds
    hm hk hpLower hpUpper
  have hshell :
      (((2 ^ k : ℕ) : ℝ)) ≤ (((2 ^ (k + 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hpNatPos : 0 < p :=
    (by positivity : 0 < 2 ^ (24 * m - k)).trans hpLower
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpNatPos
  have hscaledLeftPos :
      0 < (((2 ^ (24 * m) : ℕ) : ℝ)) / p := div_pos (by positivity) hpPos
  have hscaled :
      (((2 ^ (24 * m) : ℕ) : ℝ)) / p ≤
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)) / p :=
    hleft.trans (hshell.trans hright)
  exact intervalIntegral.integral_mono_interval hleft hshell hright
    (Eventually.of_forall fun z => by positivity)
    (intervalIntegrable_realDyadicIncrementEnergyDensity
      omega hscaledLeftPos hscaled)

/-- Finite shell form of the variance-averaging inequality.  Once the fixed
prime block has reciprocal mass at least `1/20`, the scaled prime sum captures
at least `1/20` of the whole dyadic-shell increment energy. -/
theorem one_twentieth_mul_shell_energy_le_scaled_prime_sum
    (omega : Omega) {m k : ℕ}
    (hm : 1 ≤ m)
    (hk : k ≤ 3 * m)
    (hmass : (1 / 20 : ℝ) ≤
      Problem520.freshReciprocalSum
        (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k))) :
    (1 / 20 : ℝ) *
        (∫ z in (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
          realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
      ∑ p ∈ Problem520.freshPrimes
          (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
        (p : ℝ)⁻¹ *
          ∫ z in
              (((2 ^ (24 * m) : ℕ) : ℝ)) / p..
              (((2 ^ (28 * m - 1) : ℕ) : ℝ)) / p,
            realDyadicIncrement omega z ^ 2 / z ^ 2 := by
  let E : ℝ :=
    ∫ z in (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
      realDyadicIncrement omega z ^ 2 / z ^ 2
  have hshell :
      (((2 ^ k : ℕ) : ℝ)) ≤ (((2 ^ (k + 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hE : 0 ≤ E := by
    dsimp [E]
    exact intervalIntegral.integral_nonneg_of_forall hshell
      (fun z => by positivity)
  calc
    (1 / 20 : ℝ) * E ≤
        Problem520.freshReciprocalSum
          (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) * E :=
      mul_le_mul_of_nonneg_right hmass hE
    _ = ∑ p ∈ Problem520.freshPrimes
          (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
        (p : ℝ)⁻¹ * E := by
      rw [Problem520.freshReciprocalSum, Finset.sum_mul]
    _ ≤ ∑ p ∈ Problem520.freshPrimes
          (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
        (p : ℝ)⁻¹ *
          ∫ z in
              (((2 ^ (24 * m) : ℕ) : ℝ)) / p..
              (((2 ^ (28 * m - 1) : ℕ) : ℝ)) / p,
            realDyadicIncrement omega z ^ 2 / z ^ 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := (Problem520.mem_freshPrimes.mp hp)
      exact mul_le_mul_of_nonneg_left
        (powerTwo_shell_energy_le_scaled_prime_energy omega hm hk
          hpData.2.1 hpData.2.2) (by positivity)

/-- Correct disjoint-shell form of the prime-sampling inequality.  Each prime
is integrated only where `x/p` belongs to the chosen shell, so summing this
statement over `k` introduces no multiplicity loss. -/
theorem one_twentieth_mul_shell_energy_le_restricted_prime_integrals
    (omega : Omega) {m k : ℕ}
    (hmass : (1 / 20 : ℝ) ≤
      Problem520.freshReciprocalSum
        (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k))) :
    (1 / 20 : ℝ) *
        (∫ z in (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
          realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
      ∑ p ∈ Problem520.freshPrimes
          (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
        ∫ x in
            (p : ℝ) * (((2 ^ k : ℕ) : ℝ))..
            (p : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ)),
          realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 := by
  let E : ℝ :=
    ∫ z in (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
      realDyadicIncrement omega z ^ 2 / z ^ 2
  have hshell :
      (((2 ^ k : ℕ) : ℝ)) ≤ (((2 ^ (k + 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hE : 0 ≤ E := by
    dsimp [E]
    exact intervalIntegral.integral_nonneg_of_forall hshell
      (fun z => by positivity)
  calc
    (1 / 20 : ℝ) * E ≤
        Problem520.freshReciprocalSum
          (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) * E :=
      mul_le_mul_of_nonneg_right hmass hE
    _ = ∑ p ∈ Problem520.freshPrimes
          (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
        (p : ℝ)⁻¹ * E := by
      rw [Problem520.freshReciprocalSum, Finset.sum_mul]
    _ = ∑ p ∈ Problem520.freshPrimes
          (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
        ∫ x in
            (p : ℝ) * (((2 ^ k : ℕ) : ℝ))..
            (p : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ)),
          realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpPos := (Problem520.mem_freshPrimes.mp hp).1.pos
      exact (intervalIntegral_prime_mul_shell_eq_inv_mul_shell_energy
        (omega := omega) (a := (((2 ^ k : ℕ) : ℝ)))
        (b := (((2 ^ (k + 1) : ℕ) : ℝ))) hpPos).symm

/-- Unrestricted single-shell form of the averaged-variance estimate.  This is
useful one shell at a time; use the restricted theorem below before summing in
`k`, because adjacent shell-safe prime blocks overlap. -/
theorem one_twentieth_mul_shell_energy_le_prime_integral
    (omega : Omega) {m k : ℕ}
    (hm : 1 ≤ m)
    (hk : k ≤ 3 * m)
    (hmass : (1 / 20 : ℝ) ≤
      Problem520.freshReciprocalSum
        (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k))) :
    (1 / 20 : ℝ) *
        (∫ z in (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
          realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
      ∫ x in
          (((2 ^ (24 * m) : ℕ) : ℝ))..
          (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
        ∑ p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
          realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 := by
  let s := Problem520.freshPrimes
    (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k))
  have hAB : 24 * m ≤ 28 * m - 1 := by omega
  have hEndpoint :
      (((2 ^ (24 * m) : ℕ) : ℝ)) ≤
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) hAB
  have hpos : ∀ p ∈ s, 0 < p := by
    intro p hp
    exact (Problem520.mem_freshPrimes.mp hp).1.pos
  have hint : ∀ p ∈ s, IntervalIntegrable
      (fun x : ℝ => realDyadicIncrement omega (x / p) ^ 2 / x ^ 2)
      volume
      (((2 ^ (24 * m) : ℕ) : ℝ))
      (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    intro p hp
    exact intervalIntegrable_realDyadicIncrement_comp_div_sq_div_sq omega
      (by positivity) hEndpoint (hpos p hp)
  calc
    (1 / 20 : ℝ) *
        (∫ z in (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
          realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
      ∑ p ∈ s, (p : ℝ)⁻¹ *
        ∫ z in
            (((2 ^ (24 * m) : ℕ) : ℝ)) / p..
            (((2 ^ (28 * m - 1) : ℕ) : ℝ)) / p,
          realDyadicIncrement omega z ^ 2 / z ^ 2 :=
      one_twentieth_mul_shell_energy_le_scaled_prime_sum omega hm hk hmass
    _ = ∫ x in
          (((2 ^ (24 * m) : ℕ) : ℝ))..
          (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
        ∑ p ∈ s,
          realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 := by
      symm
      exact intervalIntegral_sum_realDyadicIncrement_comp_div_sq_div_sq
        omega s hpos hint

/-- Unconditional scheduled form: the internal PNT supplies a single threshold
after which every admissible dyadic shell satisfies the `1/20` variance-energy
capture inequality. -/
theorem exists_powerTwo_shell_energy_capture :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (omega : Omega) (k : ℕ), k ≤ 3 * m →
      (1 / 20 : ℝ) *
          (∫ z in (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
            realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
        ∑ p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
          (p : ℝ)⁻¹ *
            ∫ z in
                (((2 ^ (24 * m) : ℕ) : ℝ)) / p..
                (((2 ^ (28 * m - 1) : ℕ) : ℝ)) / p,
              realDyadicIncrement omega z ^ 2 / z ^ 2 := by
  obtain ⟨m₀, hm₀⟩ := exists_powerTwo_shell_primeSampling_mass
  refine ⟨max m₀ 1, ?_⟩
  intro m hm omega k hk
  exact one_twentieth_mul_shell_energy_le_scaled_prime_sum omega
    ((le_max_right m₀ 1).trans hm) hk
    (hm₀ m ((le_max_left m₀ 1).trans hm) k hk)

/-- Assumption-free unrestricted integral form for one shell.  This theorem is
not the simultaneous shell handoff; that role belongs to
`exists_powerTwo_all_shells_energy_capture_restricted`. -/
theorem exists_powerTwo_shell_energy_capture_integral :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (omega : Omega) (k : ℕ), k ≤ 3 * m →
      (1 / 20 : ℝ) *
          (∫ z in (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
            realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
        ∫ x in
            (((2 ^ (24 * m) : ℕ) : ℝ))..
            (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
          ∑ p ∈ Problem520.freshPrimes
              (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
            realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 := by
  obtain ⟨m₀, hm₀⟩ := exists_powerTwo_shell_primeSampling_mass
  refine ⟨max m₀ 1, ?_⟩
  intro m hm omega k hk
  exact one_twentieth_mul_shell_energy_le_prime_integral omega
    ((le_max_right m₀ 1).trans hm) hk
    (hm₀ m ((le_max_left m₀ 1).trans hm) k hk)

/-- Simultaneous, multiplicity-free capture of every shell up to `3*m`.
This is the form that may safely be compared with the full fresh variance:
for a fixed prime the integration intervals indexed by `k` are disjoint. -/
theorem exists_powerTwo_all_shells_energy_capture_restricted :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ omega : Omega,
      (1 / 20 : ℝ) *
          ∑ k ∈ Finset.range (3 * m + 1),
            (∫ z in
                (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
              realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
        ∑ k ∈ Finset.range (3 * m + 1),
          ∑ p ∈ Problem520.freshPrimes
              (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
            ∫ x in
                (p : ℝ) * (((2 ^ k : ℕ) : ℝ))..
                (p : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ)),
              realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 := by
  obtain ⟨m₀, hm₀⟩ := exists_powerTwo_shell_primeSampling_mass
  refine ⟨m₀, ?_⟩
  intro m hm omega
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hkBound : k ≤ 3 * m := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  exact one_twentieth_mul_shell_energy_le_restricted_prime_integrals omega
    (hm₀ m hm k hkBound)

/-- Integrating the multiplicity-free indicator density is exactly the
restricted double sum of the scaled shell integrals. -/
theorem intervalIntegral_restrictedPowerTwoFreshVarianceIndicatorDensity_eq
    (omega : Omega) {m : ℕ} (hm : 1 ≤ m) :
    (∫ x in
        (((2 ^ (24 * m) : ℕ) : ℝ))..
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
      restrictedPowerTwoFreshVarianceIndicatorDensity omega m x) =
      ∑ k ∈ Finset.range (3 * m + 1),
        ∑ p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
          ∫ x in
              (p : ℝ) * (((2 ^ k : ℕ) : ℝ))..
              (p : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ)),
            realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 := by
  classical
  let G := Problem520.freshPrimes (2 ^ (21 * m)) (2 ^ (28 * m))
  let R := Finset.range (3 * m + 1)
  have hAB :
      (((2 ^ (24 * m) : ℕ) : ℝ)) ≤
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hterm : ∀ p ∈ G, ∀ k ∈ R, IntervalIntegrable
      (fun x : ℝ =>
        if p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
          (powerTwoScaledShell p k).indicator
            (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x
        else 0)
      volume
      (((2 ^ (24 * m) : ℕ) : ℝ))
      (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    intro p hpGlobal k hk
    split_ifs
    · exact intervalIntegrable_setIndicator
        (intervalIntegrable_realDyadicIncrement_comp_div_sq_div_sq omega
          (by positivity) hAB
          (Problem520.mem_freshPrimes.mp hpGlobal).1.pos)
        measurableSet_Ioc
    · exact intervalIntegrable_const
  have hlocal : ∀ p ∈ G, ∀ k ∈ R,
      (∫ x in
          (((2 ^ (24 * m) : ℕ) : ℝ))..
          (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
        if p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
          (powerTwoScaledShell p k).indicator
            (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x
        else 0) =
        if p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
          ∫ x in
              (p : ℝ) * (((2 ^ k : ℕ) : ℝ))..
              (p : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ)),
            realDyadicIncrement omega (x / p) ^ 2 / x ^ 2
        else 0 := by
    intro p hpGlobal k hk
    have hkLe : k ≤ 3 * m := by
      simpa [R, Finset.mem_range] using hk
    by_cases hp : p ∈ Problem520.freshPrimes
        (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k))
    · simp only [hp, ↓reduceIte]
      exact intervalIntegral_powerTwoScaledShell_indicator_eq omega hm hkLe hp
    · simp only [hp, ↓reduceIte, intervalIntegral.integral_zero]
  unfold restrictedPowerTwoFreshVarianceIndicatorDensity
  change (∫ x in
      (((2 ^ (24 * m) : ℕ) : ℝ))..
      (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
    ∑ p ∈ G, ∑ k ∈ R,
      if p ∈ Problem520.freshPrimes
          (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
        (powerTwoScaledShell p k).indicator
          (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x
      else 0) = _
  have hinnerInt : ∀ p ∈ G, IntervalIntegrable
      (fun x : ℝ => ∑ k ∈ R,
        if p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
          (powerTwoScaledShell p k).indicator
            (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x
        else 0)
      volume
      (((2 ^ (24 * m) : ℕ) : ℝ))
      (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    intro p hp
    exact (IntervalIntegrable.sum R (hterm p hp)).congr fun x hx => by
      simp only [Finset.sum_apply]
  calc
    (∫ x in
        (((2 ^ (24 * m) : ℕ) : ℝ))..
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
      ∑ p ∈ G, ∑ k ∈ R,
        if p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
          (powerTwoScaledShell p k).indicator
            (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x
        else 0) =
      ∑ p ∈ G,
        ∫ x in
            (((2 ^ (24 * m) : ℕ) : ℝ))..
            (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
          ∑ k ∈ R,
            if p ∈ Problem520.freshPrimes
                (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
              (powerTwoScaledShell p k).indicator
                (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x
            else 0 := by
        simpa only [Finset.sum_apply] using
          intervalIntegral.integral_finset_sum hinnerInt
    _ = ∑ p ∈ G, ∑ k ∈ R,
        ∫ x in
            (((2 ^ (24 * m) : ℕ) : ℝ))..
            (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
          if p ∈ Problem520.freshPrimes
              (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
            (powerTwoScaledShell p k).indicator
              (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x
          else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        simpa only [Finset.sum_apply] using
          intervalIntegral.integral_finset_sum (hterm p hp)
    _ = ∑ p ∈ G, ∑ k ∈ R,
        if p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
          ∫ x in
              (p : ℝ) * (((2 ^ k : ℕ) : ℝ))..
              (p : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ)),
            realDyadicIncrement omega (x / p) ^ 2 / x ^ 2
        else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro k hk
        exact hlocal p hp k hk
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      have hkLe : k ≤ 3 * m := by
        simpa [R, Finset.mem_range] using hk
      let Pk := Problem520.freshPrimes
        (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k))
      have hPk : Pk ⊆ G := shellSafeFreshPrimes_subset_global hkLe
      have hfilter : G.filter (fun p => p ∈ Pk) = Pk := by
        ext p
        simp only [Finset.mem_filter]
        exact and_iff_right_of_imp (fun hp => hPk hp)
      rw [← Finset.sum_filter, hfilter]

/-- The full fresh-variance density is interval integrable on the scheduled
endpoint window. -/
theorem intervalIntegrable_fullPowerTwoFreshVarianceDensity
    (omega : Omega) {m : ℕ} (hm : 1 ≤ m) :
    IntervalIntegrable (fullPowerTwoFreshVarianceDensity omega m) volume
      (((2 ^ (24 * m) : ℕ) : ℝ))
      (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
  classical
  let G := Problem520.freshPrimes (2 ^ (21 * m)) (2 ^ (28 * m))
  have hAB :
      (((2 ^ (24 * m) : ℕ) : ℝ)) ≤
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hterm : ∀ p ∈ G, IntervalIntegrable
      (fun x : ℝ => if (p : ℝ) ≤ 2 * x then
        realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 else 0)
      volume
      (((2 ^ (24 * m) : ℕ) : ℝ))
      (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    intro p hp
    let s : Set ℝ := {x | (p : ℝ) ≤ 2 * x}
    have hs : MeasurableSet s := by
      exact measurableSet_le measurable_const (measurable_const.mul measurable_id)
    have hbase := intervalIntegrable_realDyadicIncrement_comp_div_sq_div_sq
      omega (by positivity) hAB (Problem520.mem_freshPrimes.mp hp).1.pos
    exact (intervalIntegrable_setIndicator hbase hs).congr fun x hx => by
      simp only [Set.indicator_apply, s, Set.mem_setOf_eq]
  unfold fullPowerTwoFreshVarianceDensity
  exact (IntervalIntegrable.sum G hterm).congr fun x hx => by
    simp only [Finset.sum_apply, G]

/-- The regrouped restricted density is integrable, via its pointwise-equal
indicator presentation. -/
theorem intervalIntegrable_restrictedPowerTwoFreshVarianceDensity
    (omega : Omega) {m : ℕ} (hm : 1 ≤ m) :
    IntervalIntegrable (restrictedPowerTwoFreshVarianceDensity omega m) volume
      (((2 ^ (24 * m) : ℕ) : ℝ))
      (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
  classical
  let G := Problem520.freshPrimes (2 ^ (21 * m)) (2 ^ (28 * m))
  let R := Finset.range (3 * m + 1)
  have hAB :
      (((2 ^ (24 * m) : ℕ) : ℝ)) ≤
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hterm : ∀ p ∈ G, ∀ k ∈ R, IntervalIntegrable
      (fun x : ℝ =>
        if p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
          (powerTwoScaledShell p k).indicator
            (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x
        else 0)
      volume
      (((2 ^ (24 * m) : ℕ) : ℝ))
      (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    intro p hp k hk
    split_ifs
    · exact intervalIntegrable_setIndicator
        (intervalIntegrable_realDyadicIncrement_comp_div_sq_div_sq omega
          (by positivity) hAB (Problem520.mem_freshPrimes.mp hp).1.pos)
        measurableSet_Ioc
    · exact intervalIntegrable_const
  have hinner : ∀ p ∈ G, IntervalIntegrable
      (fun x : ℝ => ∑ k ∈ R,
        if p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)) then
          (powerTwoScaledShell p k).indicator
            (fun y => realDyadicIncrement omega (y / p) ^ 2 / y ^ 2) x
        else 0)
      volume
      (((2 ^ (24 * m) : ℕ) : ℝ))
      (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    intro p hp
    exact (IntervalIntegrable.sum R (hterm p hp)).congr fun x hx => by
      simp only [Finset.sum_apply]
  have hindicator : IntervalIntegrable
      (restrictedPowerTwoFreshVarianceIndicatorDensity omega m) volume
      (((2 ^ (24 * m) : ℕ) : ℝ))
      (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    unfold restrictedPowerTwoFreshVarianceIndicatorDensity
    exact (IntervalIntegrable.sum G hinner).congr fun x hx => by
      simp only [Finset.sum_apply, G, R]
  exact hindicator.congr fun x hx =>
    restrictedPowerTwoFreshVarianceIndicatorDensity_eq omega m x

/-- The multiplicity-free restricted integral is bounded by the actual full
fresh-prime variance integral. -/
theorem intervalIntegral_restrictedPowerTwoFreshVarianceDensity_le_full
    (omega : Omega) {m : ℕ} (hm : 1 ≤ m) :
    (∫ x in
        (((2 ^ (24 * m) : ℕ) : ℝ))..
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
      restrictedPowerTwoFreshVarianceDensity omega m x) ≤
      ∫ x in
          (((2 ^ (24 * m) : ℕ) : ℝ))..
          (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
        fullPowerTwoFreshVarianceDensity omega m x := by
  have hAB :
      (((2 ^ (24 * m) : ℕ) : ℝ)) ≤
        (((2 ^ (28 * m - 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  exact intervalIntegral.integral_mono hAB
    (intervalIntegrable_restrictedPowerTwoFreshVarianceDensity omega hm)
    (intervalIntegrable_fullPowerTwoFreshVarianceDensity omega hm)
    (restrictedPowerTwoFreshVarianceDensity_le_full omega m)

/-- Final multiplicity-free variance-averaging handoff: total dyadic-increment
energy on the first `3*m+1` shells forces averaged full fresh-prime variance
on the scheduled endpoint window. -/
theorem exists_powerTwo_fullFreshVariance_energy_capture :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ omega : Omega,
      (1 / 20 : ℝ) *
          ∑ k ∈ Finset.range (3 * m + 1),
            (∫ z in
                (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
              realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
        ∫ x in
            (((2 ^ (24 * m) : ℕ) : ℝ))..
            (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
          fullPowerTwoFreshVarianceDensity omega m x := by
  obtain ⟨m₀, hm₀⟩ := exists_powerTwo_all_shells_energy_capture_restricted
  refine ⟨max m₀ 1, ?_⟩
  intro m hm omega
  have hmOne : 1 ≤ m := (le_max_right m₀ 1).trans hm
  calc
    (1 / 20 : ℝ) *
        ∑ k ∈ Finset.range (3 * m + 1),
          (∫ z in
              (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
            realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
      ∑ k ∈ Finset.range (3 * m + 1),
        ∑ p ∈ Problem520.freshPrimes
            (2 ^ (24 * m - k)) (2 ^ (28 * m - 3 - k)),
          ∫ x in
              (p : ℝ) * (((2 ^ k : ℕ) : ℝ))..
              (p : ℝ) * (((2 ^ (k + 1) : ℕ) : ℝ)),
            realDyadicIncrement omega (x / p) ^ 2 / x ^ 2 :=
      hm₀ m ((le_max_left m₀ 1).trans hm) omega
    _ = ∫ x in
          (((2 ^ (24 * m) : ℕ) : ℝ))..
          (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
        restrictedPowerTwoFreshVarianceIndicatorDensity omega m x :=
      (intervalIntegral_restrictedPowerTwoFreshVarianceIndicatorDensity_eq
        omega hmOne).symm
    _ = ∫ x in
          (((2 ^ (24 * m) : ℕ) : ℝ))..
          (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
        restrictedPowerTwoFreshVarianceDensity omega m x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact restrictedPowerTwoFreshVarianceIndicatorDensity_eq omega m x
    _ ≤ ∫ x in
          (((2 ^ (24 * m) : ℕ) : ℝ))..
          (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
        fullPowerTwoFreshVarianceDensity omega m x :=
      intervalIntegral_restrictedPowerTwoFreshVarianceDensity_le_full
        omega hmOne

/-- The finite dyadic-shell energy sum is exactly the energy on the combined
interval. -/
theorem sum_powerTwo_shell_energy_eq
    (omega : Omega) (n : ℕ) :
    (∑ k ∈ Finset.range n,
        ∫ z in
            (((2 ^ k : ℕ) : ℝ))..(((2 ^ (k + 1) : ℕ) : ℝ)),
          realDyadicIncrement omega z ^ 2 / z ^ 2) =
      ∫ z in (1 : ℝ)..(((2 ^ n : ℕ) : ℝ)),
        realDyadicIncrement omega z ^ 2 / z ^ 2 := by
  have hint : ∀ k < n, IntervalIntegrable
      (realDyadicIncrementEnergyDensity omega) volume
      (((2 ^ k : ℕ) : ℝ)) (((2 ^ (k + 1) : ℕ) : ℝ)) := by
    intro k hk
    apply intervalIntegrable_realDyadicIncrementEnergyDensity
    · positivity
    · exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  simpa only [realDyadicIncrementEnergyDensity, pow_zero, Nat.cast_one] using
    intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (((2 ^ k : ℕ) : ℝ))) hint

/-- Combined-interval form of the variance-averaging handoff. -/
theorem exists_powerTwo_fullFreshVariance_combined_energy_capture :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ omega : Omega,
      (1 / 20 : ℝ) *
          (∫ z in (1 : ℝ)..(((2 ^ (3 * m + 1) : ℕ) : ℝ)),
            realDyadicIncrement omega z ^ 2 / z ^ 2) ≤
        ∫ x in
            (((2 ^ (24 * m) : ℕ) : ℝ))..
            (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
          fullPowerTwoFreshVarianceDensity omega m x := by
  obtain ⟨m₀, hm₀⟩ := exists_powerTwo_fullFreshVariance_energy_capture
  refine ⟨m₀, ?_⟩
  intro m hm omega
  rw [← sum_powerTwo_shell_energy_eq omega (3 * m + 1)]
  exact hm₀ m hm omega

/-! ## Direct continuous endpoint-to-increment energy transfer -/

/-- Inverse-square endpoint-energy density for the real step extension. -/
noncomputable def realEndpointEnergyDensity
    (omega : Omega) (x : ℝ) : ℝ :=
  realStepSum omega x ^ 2 / x ^ 2

theorem measurable_realEndpointEnergyDensity (omega : Omega) :
    Measurable (realEndpointEnergyDensity omega) := by
  exact ((measurable_realStepSum omega).pow_const 2).div
    (measurable_id.pow_const 2)

/-- The endpoint-energy density is integrable on every positive compact
interval. -/
theorem integrableOn_realEndpointEnergyDensity_Icc
    (omega : Omega) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (realEndpointEnergyDensity omega) (Set.Icc a b) := by
  have hbNonneg : 0 ≤ b := ha.le.trans hab
  refine Measure.integrableOn_of_bounded (μ := volume) (s := Set.Icc a b)
    (M := b ^ 2 / a ^ 2) measure_Icc_lt_top.ne
    (measurable_realEndpointEnergyDensity omega).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hxPos : 0 < x := ha.trans_le hx.1
  have hstep : |realStepSum omega x| ≤ b := by
    exact (abs_S_le omega ⌊x⌋₊).trans ((Nat.floor_le hxPos.le).trans hx.2)
  have hstepSq : realStepSum omega x ^ 2 ≤ b ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hbNonneg]
    exact hstep
  have haSqPos : 0 < a ^ 2 := sq_pos_of_pos ha
  have haSqLe : a ^ 2 ≤ x ^ 2 :=
    (sq_le_sq₀ ha.le hxPos.le).2 hx.1
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    unfold realEndpointEnergyDensity
    positivity)]
  unfold realEndpointEnergyDensity
  exact div_le_div₀ (sq_nonneg b) hstepSq haSqPos haSqLe

theorem intervalIntegrable_realEndpointEnergyDensity
    (omega : Omega) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (realEndpointEnergyDensity omega) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact integrableOn_realEndpointEnergyDensity_Icc omega ha hab

/-- Pointwise contracted dyadic recurrence.  The coefficient `3/4` is the
feature that makes the continuous energy transfer stable. -/
theorem two_mul_endpointEnergyDensity_two_mul_le
    (omega : Omega) (t : ℝ) :
    2 * realEndpointEnergyDensity omega (2 * t) ≤
      (3 / 4 : ℝ) * realEndpointEnergyDensity omega t +
        (3 / 2 : ℝ) * realDyadicIncrementEnergyDensity omega t := by
  by_cases ht : t = 0
  · simp [ht, realEndpointEnergyDensity,
      realDyadicIncrementEnergyDensity]
  · have hrec : realStepSum omega (2 * t) =
        realStepSum omega t + realDyadicIncrement omega t := by
      unfold realDyadicIncrement
      ring
    have hnum : (1 / 2 : ℝ) * realStepSum omega (2 * t) ^ 2 ≤
        (3 / 4 : ℝ) * realStepSum omega t ^ 2 +
          (3 / 2 : ℝ) * realDyadicIncrement omega t ^ 2 := by
      rw [hrec]
      nlinarith [sq_nonneg
        ((1 / 2 : ℝ) * realStepSum omega t - realDyadicIncrement omega t)]
    unfold realEndpointEnergyDensity realDyadicIncrementEnergyDensity
    calc
      2 * (realStepSum omega (2 * t) ^ 2 / (2 * t) ^ 2) =
          ((1 / 2 : ℝ) * realStepSum omega (2 * t) ^ 2) / t ^ 2 := by
        field_simp
      _ ≤ ((3 / 4 : ℝ) * realStepSum omega t ^ 2 +
          (3 / 2 : ℝ) * realDyadicIncrement omega t ^ 2) / t ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg t)
      _ = (3 / 4 : ℝ) * (realStepSum omega t ^ 2 / t ^ 2) +
          (3 / 2 : ℝ) * (realDyadicIncrement omega t ^ 2 / t ^ 2) := by
        ring

/-- Exact dyadic rescaling of the endpoint-energy tail. -/
theorem intervalIntegral_endpointEnergyDensity_two_scale
    (omega : Omega) (Y : ℝ) :
    (∫ x in (2 : ℝ)..Y, realEndpointEnergyDensity omega x) =
      ∫ t in (1 : ℝ)..Y / 2,
        2 * realEndpointEnergyDensity omega (2 * t) := by
  have h := intervalIntegral.smul_integral_comp_mul_left
    (f := realEndpointEnergyDensity omega) (a := (1 : ℝ))
    (b := Y / 2) (2 : ℝ)
  have hright : (2 : ℝ) * (Y / 2) = Y := by ring
  rw [mul_one, hright] at h
  simpa only [smul_eq_mul, intervalIntegral.integral_const_mul] using h.symm

/-- Contracted tail estimate obtained from the exact dyadic recurrence. -/
theorem intervalIntegral_endpointEnergyDensity_tail_le
    (omega : Omega) {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ x in (2 : ℝ)..Y, realEndpointEnergyDensity omega x) ≤
      (3 / 4 : ℝ) *
          (∫ t in (1 : ℝ)..Y / 2, realEndpointEnergyDensity omega t) +
        (3 / 2 : ℝ) *
          (∫ t in (1 : ℝ)..Y / 2,
            realDyadicIncrementEnergyDensity omega t) := by
  have hOneHalf : (1 : ℝ) ≤ Y / 2 := by linarith
  have hTwoY : (2 : ℝ) ≤ Y := hY
  have hEndpointTail := intervalIntegrable_realEndpointEnergyDensity
    omega (by norm_num : (0 : ℝ) < 2) hTwoY
  have hEndpointComp := hEndpointTail.comp_mul_left (c := (2 : ℝ))
  have hleft : IntervalIntegrable
      (fun t : ℝ => 2 * realEndpointEnergyDensity omega (2 * t))
      volume 1 (Y / 2) := by
    convert hEndpointComp.const_mul 2 using 1
    all_goals norm_num
  have hEndpointHalf := intervalIntegrable_realEndpointEnergyDensity
    omega (by norm_num : (0 : ℝ) < 1) hOneHalf
  have hIncrementHalf := intervalIntegrable_realDyadicIncrementEnergyDensity
    omega (by norm_num : (0 : ℝ) < 1) hOneHalf
  have hright : IntervalIntegrable
      (fun t : ℝ =>
        (3 / 4 : ℝ) * realEndpointEnergyDensity omega t +
          (3 / 2 : ℝ) * realDyadicIncrementEnergyDensity omega t)
      volume 1 (Y / 2) :=
    (hEndpointHalf.const_mul (3 / 4)).add
      (hIncrementHalf.const_mul (3 / 2))
  have hmono := intervalIntegral.integral_mono hOneHalf hleft hright
    (two_mul_endpointEnergyDensity_two_mul_le omega)
  rw [← intervalIntegral_endpointEnergyDensity_two_scale omega Y,
    intervalIntegral.integral_add
      (hEndpointHalf.const_mul (3 / 4))
      (hIncrementHalf.const_mul (3 / 2)),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-- Direct continuous endpoint-to-increment transfer.  No discretization or
Schur kernel is needed: the dyadic rescaling contracts the old endpoint
energy by `3/4`. -/
theorem intervalIntegral_endpointEnergyDensity_le_boundary_add_increment
    (omega : Omega) {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ x in (1 : ℝ)..Y, realEndpointEnergyDensity omega x) ≤
      4 * (∫ x in (1 : ℝ)..2, realEndpointEnergyDensity omega x) +
        6 * (∫ x in (1 : ℝ)..Y,
          realDyadicIncrementEnergyDensity omega x) := by
  have hOneY : (1 : ℝ) ≤ Y := by linarith
  have hOneHalf : (1 : ℝ) ≤ Y / 2 := by linarith
  have hHalfY : Y / 2 ≤ Y := by linarith
  have hEndpointFull := intervalIntegrable_realEndpointEnergyDensity
    omega (by norm_num : (0 : ℝ) < 1) hOneY
  have hEndpointInitial := intervalIntegrable_realEndpointEnergyDensity
    omega (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 2)
  have hEndpointTail := intervalIntegrable_realEndpointEnergyDensity
    omega (by norm_num : (0 : ℝ) < 2) hY
  have hIncrementFull := intervalIntegrable_realDyadicIncrementEnergyDensity
    omega (by norm_num : (0 : ℝ) < 1) hOneY
  have hEndpointHalfLe :
      (∫ x in (1 : ℝ)..Y / 2, realEndpointEnergyDensity omega x) ≤
        ∫ x in (1 : ℝ)..Y, realEndpointEnergyDensity omega x := by
    exact intervalIntegral.integral_mono_interval le_rfl hOneHalf hHalfY
      (Eventually.of_forall fun x => by
        unfold realEndpointEnergyDensity
        positivity)
      hEndpointFull
  have hIncrementHalfLe :
      (∫ x in (1 : ℝ)..Y / 2,
          realDyadicIncrementEnergyDensity omega x) ≤
        ∫ x in (1 : ℝ)..Y,
          realDyadicIncrementEnergyDensity omega x := by
    exact intervalIntegral.integral_mono_interval le_rfl hOneHalf hHalfY
      (Eventually.of_forall fun x => by
        unfold realDyadicIncrementEnergyDensity
        positivity)
      hIncrementFull
  have hTail := intervalIntegral_endpointEnergyDensity_tail_le omega hY
  have hTail' :
      (∫ x in (2 : ℝ)..Y, realEndpointEnergyDensity omega x) ≤
        (3 / 4 : ℝ) *
            (∫ x in (1 : ℝ)..Y, realEndpointEnergyDensity omega x) +
          (3 / 2 : ℝ) *
            (∫ x in (1 : ℝ)..Y,
              realDyadicIncrementEnergyDensity omega x) := by
    calc
      (∫ x in (2 : ℝ)..Y, realEndpointEnergyDensity omega x) ≤
          (3 / 4 : ℝ) *
              (∫ x in (1 : ℝ)..Y / 2,
                realEndpointEnergyDensity omega x) +
            (3 / 2 : ℝ) *
              (∫ x in (1 : ℝ)..Y / 2,
                realDyadicIncrementEnergyDensity omega x) := hTail
      _ ≤ (3 / 4 : ℝ) *
              (∫ x in (1 : ℝ)..Y, realEndpointEnergyDensity omega x) +
            (3 / 2 : ℝ) *
              (∫ x in (1 : ℝ)..Y,
                realDyadicIncrementEnergyDensity omega x) := by
        gcongr
  have hSplit := intervalIntegral.integral_add_adjacent_intervals
    hEndpointInitial hEndpointTail
  nlinarith

/-- Lower-floor form used by the variance-averaging route. -/
theorem intervalIntegral_incrementEnergyDensity_lower_of_endpointFloor
    (omega : Omega) {Y endpointFloor : ℝ} (hY : 2 ≤ Y)
    (hfloor : endpointFloor ≤
      ∫ x in (1 : ℝ)..Y, realEndpointEnergyDensity omega x) :
    (endpointFloor -
        4 * (∫ x in (1 : ℝ)..2, realEndpointEnergyDensity omega x)) / 6 ≤
      ∫ x in (1 : ℝ)..Y,
        realDyadicIncrementEnergyDensity omega x := by
  have htransfer :=
    intervalIntegral_endpointEnergyDensity_le_boundary_add_increment omega hY
  nlinarith

/-- Endpoint-energy form of the complete variance-averaging handoff.  The only
loss outside the universal factor `120` is the fixed initial interval
`[1,2]`. -/
theorem exists_powerTwo_fullFreshVariance_endpoint_energy_capture :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ omega : Omega,
      ((∫ z in (1 : ℝ)..(((2 ^ (3 * m + 1) : ℕ) : ℝ)),
          realEndpointEnergyDensity omega z) -
        4 * (∫ z in (1 : ℝ)..2, realEndpointEnergyDensity omega z)) / 120 ≤
        ∫ x in
            (((2 ^ (24 * m) : ℕ) : ℝ))..
            (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
          fullPowerTwoFreshVarianceDensity omega m x := by
  obtain ⟨m₀, hm₀⟩ :=
    exists_powerTwo_fullFreshVariance_combined_energy_capture
  refine ⟨m₀, ?_⟩
  intro m hm omega
  let Y : ℝ := (((2 ^ (3 * m + 1) : ℕ) : ℝ))
  have hY : (2 : ℝ) ≤ Y := by
    dsimp [Y]
    have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ (3 * m + 1) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    norm_num at hpow
    exact_mod_cast hpow
  have hIncrement :=
    intervalIntegral_incrementEnergyDensity_lower_of_endpointFloor
      omega hY (endpointFloor :=
        ∫ z in (1 : ℝ)..Y, realEndpointEnergyDensity omega z) le_rfl
  have hScaled := mul_le_mul_of_nonneg_left hIncrement
    (by norm_num : (0 : ℝ) ≤ 1 / 20)
  calc
    ((∫ z in (1 : ℝ)..Y, realEndpointEnergyDensity omega z) -
        4 * (∫ z in (1 : ℝ)..2, realEndpointEnergyDensity omega z)) / 120 =
      (1 / 20 : ℝ) *
        (((∫ z in (1 : ℝ)..Y, realEndpointEnergyDensity omega z) -
          4 * (∫ z in (1 : ℝ)..2, realEndpointEnergyDensity omega z)) / 6) := by
      ring
    _ ≤ (1 / 20 : ℝ) *
        (∫ z in (1 : ℝ)..Y,
          realDyadicIncrementEnergyDensity omega z) := hScaled
    _ ≤ ∫ x in
          (((2 ^ (24 * m) : ℕ) : ℝ))..
          (((2 ^ (28 * m - 1) : ℕ) : ℝ)),
        fullPowerTwoFreshVarianceDensity omega m x := hm₀ m hm omega

end Problem1144
end Erdos
