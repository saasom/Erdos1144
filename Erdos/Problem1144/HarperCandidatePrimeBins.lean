import Erdos.Problem520.HarperPrimeBlockArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter MeasureTheory Set
open scoped Topology

namespace Erdos.Problem1144

/-!
# Prime mass in the candidate's logarithmic bins

The effective theta estimate is already checked in the #520 development.
This module moves its Abel-summation consequence to real logarithmic bins,
retaining the integer-cutoff errors explicitly.
-/

/-- Rounding an exponential endpoint loses at most the reciprocal integer
cutoff in logarithmic coordinates. -/
theorem candidate_log_floor_exp_error {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ u - Real.log (⌊Real.exp u⌋₊ : ℝ) ∧
      u - Real.log (⌊Real.exp u⌋₊ : ℝ) ≤ (⌊Real.exp u⌋₊ : ℝ)⁻¹ := by
  let A := ⌊Real.exp u⌋₊
  have hA : 1 ≤ A := by
    apply (Nat.one_le_floor_iff _).mpr
    exact Real.one_le_exp_iff.mpr hu
  have hApos : (0 : ℝ) < A := by exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hfloor : (A : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
  have hnext : Real.exp u < (A : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp u)
  have hlog : Real.log (A : ℝ) ≤ u := by
    simpa using Real.log_le_log hApos hfloor
  refine ⟨sub_nonneg.mpr hlog, ?_⟩
  have h := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos u) hApos)
  rw [Real.log_div (Real.exp_ne_zero u) hApos.ne', Real.log_exp] at h
  apply h.trans
  rw [sub_le_iff_le_add, div_le_iff₀ hApos]
  calc
    Real.exp u ≤ (A : ℝ) + 1 := hnext.le
    _ = ((A : ℝ)⁻¹ + 1) * A := by field_simp; ring

/-- The logarithmic length of a rounded bin differs from its exact length
by at most the reciprocal of its left integer endpoint. -/
theorem candidate_log_floor_exp_bin_error {u d : ℝ} (hu : 0 ≤ u) (hd : 0 ≤ d) :
    |Real.log ((⌊Real.exp (u + d)⌋₊ : ℝ) / ⌊Real.exp u⌋₊) - d| ≤
      (⌊Real.exp u⌋₊ : ℝ)⁻¹ := by
  have hA : 1 ≤ ⌊Real.exp u⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hu)
  have hAB : ⌊Real.exp u⌋₊ ≤ ⌊Real.exp (u + d)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have hApos : (0 : ℝ) < ⌊Real.exp u⌋₊ := by exact_mod_cast (by omega : 0 < ⌊Real.exp u⌋₊)
  have hBpos : (0 : ℝ) < ⌊Real.exp (u + d)⌋₊ := by
    exact_mod_cast (by omega : 0 < ⌊Real.exp (u + d)⌋₊)
  have ha := candidate_log_floor_exp_error hu
  have hb := candidate_log_floor_exp_error (add_nonneg hu hd)
  have hi : (⌊Real.exp (u + d)⌋₊ : ℝ)⁻¹ ≤ (⌊Real.exp u⌋₊ : ℝ)⁻¹ :=
    inv_le_inv₀ hBpos hApos |>.mpr (by exact_mod_cast hAB)
  rw [Real.log_div hBpos.ne' hApos.ne', abs_le]
  constructor <;> linarith

/-- The short-bin prime mass estimate with a relative theta-error bound.
The constants come from the two Abel endpoints, its integral, and rounding. -/
theorem candidate_prime_bin_mass_error_of_theta
    {u d δ : ℝ} (hu : 0 ≤ u) (hd : 0 ≤ d) (hd1 : d ≤ 1) (hδ : 0 ≤ δ)
    (herror : ∀ x ∈ Icc (⌊Real.exp u⌋₊ : ℝ) ⌊Real.exp (u + d)⌋₊,
      |Problem520.thetaError x| ≤ δ * x) :
    |Problem520.weightedPrimeReciprocalBlock ⌊Real.exp u⌋₊ ⌊Real.exp (u + d)⌋₊ - d| ≤
      4 * δ + (⌊Real.exp u⌋₊ : ℝ)⁻¹ := by
  have hA : 1 ≤ ⌊Real.exp u⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hu)
  have hAB : ⌊Real.exp u⌋₊ ≤ ⌊Real.exp (u + d)⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr (by linarith))
  have hinv : (⌊Real.exp u⌋₊ : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast hA)
  have hround := candidate_log_floor_exp_bin_error hu hd
  have hmass := Problem520.abs_weightedPrimeReciprocalBlock_sub_log_le_of_thetaError
    hA hAB herror
  have hlog : Real.log ((⌊Real.exp (u + d)⌋₊ : ℝ) / ⌊Real.exp u⌋₊) ≤ 2 :=
    by linarith [(abs_le.mp hround).2]
  calc
    _ ≤ |Problem520.weightedPrimeReciprocalBlock ⌊Real.exp u⌋₊ ⌊Real.exp (u + d)⌋₊ -
        Real.log ((⌊Real.exp (u + d)⌋₊ : ℝ) / ⌊Real.exp u⌋₊)| +
        |Real.log ((⌊Real.exp (u + d)⌋₊ : ℝ) / ⌊Real.exp u⌋₊) - d| :=
      abs_sub_le _ _ _
    _ ≤ 4 * δ + (⌊Real.exp u⌋₊ : ℝ)⁻¹ := by
      nlinarith [mul_le_mul_of_nonneg_left hlog hδ]

/-- Effective prime mass on every sufficiently late real logarithmic bin.
This uses the proved `1/10` PNT exponent, not a stronger classical rate. -/
theorem exists_candidate_prime_bin_mass_error :
    ∃ c > 0, ∃ C > 0, ∃ U : ℝ, 2 ≤ U ∧
      ∀ u ≥ U, ∀ d ∈ Icc (0 : ℝ) 1,
        |Problem520.weightedPrimeReciprocalBlock ⌊Real.exp u⌋₊ ⌊Real.exp (u + d)⌋₊ - d| ≤
          4 * (C * Real.exp (-c * (u / 2) ^ ((1 : ℝ) / 10)) +
            2 * (u + 1) * Real.exp (-u / 4)) + 2 * Real.exp (-u) := by
  obtain ⟨c, hc, C, hC, X₀, hX₀, htheta⟩ := Problem520.exists_mediumThetaError
  refine ⟨c, hc, C, hC, max 2 (Real.log (X₀ + 1)), le_max_left _ _, ?_⟩
  intro u hu d hd
  have hu2 : 2 ≤ u := (le_max_left _ _).trans hu
  have hu0 : 0 ≤ u := by linarith
  let A := ⌊Real.exp u⌋₊
  let B := ⌊Real.exp (u + d)⌋₊
  have hA1 : 1 ≤ A := (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hu0)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hAB : A ≤ B := Nat.floor_mono (Real.exp_le_exp.mpr (by linarith [hd.1]))
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hfloor : (A : ℝ) ≤ Real.exp u := Nat.floor_le (Real.exp_pos u).le
  have hnext : Real.exp u < (A : ℝ) + 1 := Nat.lt_floor_add_one (Real.exp u)
  have hXA : X₀ ≤ (A : ℝ) := by
    have huX : Real.log (X₀ + 1) ≤ u := (le_max_right _ _).trans hu
    have he := Real.exp_le_exp.mpr huX
    rw [Real.exp_log (by linarith : 0 < X₀ + 1)] at he
    linarith
  have hA2 : 2 ≤ A := by exact_mod_cast hX₀.trans hXA
  have hlogA : u / 2 ≤ Real.log (A : ℝ) := by
    have he := (candidate_log_floor_exp_error hu0).2
    have hi : (A : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hA1)
    change u - Real.log (A : ℝ) ≤ (A : ℝ)⁻¹ at he
    linarith [he]
  have hlogB : Real.log (B : ℝ) ≤ u + 1 := by
    have he := Real.log_le_log hBpos (Nat.floor_le (Real.exp_pos (u + d)).le)
    rw [Real.log_exp] at he
    linarith [hd.2]
  have hlogB0 : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hA1.trans hAB))
  have hsqrt : Real.exp (u / 4) ≤ Real.sqrt A := by
    have he : u / 4 ≤ Real.log (Real.sqrt A) := by
      rw [Real.log_sqrt hApos.le]
      linarith
    simpa only [Real.exp_log (Real.sqrt_pos.mpr hApos)] using Real.exp_le_exp.mpr he
  have hdelta : Problem520.mediumThetaBlockDelta c C A B ≤
      C * Real.exp (-c * (u / 2) ^ ((1 : ℝ) / 10)) +
        2 * (u + 1) * Real.exp (-u / 4) := by
    unfold Problem520.mediumThetaBlockDelta
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ (by linarith : -c ≤ 0)
      exact Real.rpow_le_rpow (by linarith) hlogA (by norm_num)
    · rw [show -u / 4 = -(u / 4) by ring, Real.exp_neg, ← div_eq_mul_inv]
      exact div_le_div₀ (by positivity) (by linarith) (Real.exp_pos _) hsqrt
  have hδpos : 0 ≤ Problem520.mediumThetaBlockDelta c C A B := by
    unfold Problem520.mediumThetaBlockDelta
    positivity
  have hm := candidate_prime_bin_mass_error_of_theta hu0 hd.1 hd.2 hδpos
    (fun x hx => Problem520.thetaError_le_mediumThetaBlockDelta hc hC.le htheta
      hA2 hAB hXA hx)
  have hinv : (A : ℝ)⁻¹ ≤ 2 * Real.exp (-u) := by
    rw [Real.exp_neg]
    have he : Real.exp u ≤ 2 * (A : ℝ) := by
      have hone : (1 : ℝ) ≤ A := by exact_mod_cast hA1
      linarith
    calc
      (A : ℝ)⁻¹ = 1 / (A : ℝ) := (one_div _).symm
      _ ≤ 2 / Real.exp u := (div_le_div_iff₀ hApos (Real.exp_pos u)).mpr (by simpa using he)
      _ = _ := by ring
  exact hm.trans (by linarith)

/-- A lower stretched exponential is negligible against a higher one,
even after multiplication by any fixed power. This permits exactly the
candidate bin exponents below the checked PNT exponent. -/
theorem candidate_tendsto_rpow_mul_exp_rpow_sub
    (q : ℝ) {ν a c : ℝ} (ha : 0 < a) (hν : ν < a) (hc : 0 < c) :
    Tendsto (fun T : ℝ => T ^ q * Real.exp (T ^ ν - c * T ^ a)) atTop (𝓝 0) := by
  have hratio : Tendsto (fun T : ℝ => T ^ ν / T ^ a) atTop (𝓝 0) := by
    apply (tendsto_rpow_neg_atTop (sub_pos.mpr hν)).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [neg_sub, Real.rpow_sub hT]
  have hsmall : ∀ᶠ T : ℝ in atTop, T ^ ν ≤ (c / 2) * T ^ a := by
    filter_upwards [(tendsto_order.mp hratio).2 (c / 2) (by positivity),
      eventually_gt_atTop (0 : ℝ)] with T hT hTpos
    have he := (div_lt_iff₀ (Real.rpow_pos_of_pos hTpos a)).mp hT
    exact he.le
  have hmain : Tendsto (fun T : ℝ => T ^ q * Real.exp (-(c / 2) * T ^ a))
      atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (q / a) (c / 2) (by positivity)).comp (tendsto_rpow_atTop ha)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul hT.le, mul_div_cancel₀ q ha.ne']
  apply squeeze_zero' _ _ hmain
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact mul_nonneg (Real.rpow_nonneg hT q) (Real.exp_pos _).le
  · filter_upwards [hsmall, eventually_ge_atTop (0 : ℝ)] with T hT hTpos
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hTpos q)
    apply Real.exp_le_exp.mpr
    linarith

/-- A common deterministic bound for all bins starting in `[T, β*T]`. -/
noncomputable def candidatePrimeBinError (c C β T : ℝ) : ℝ :=
  4 * (C * Real.exp (-c * (T / 2) ^ ((1 : ℝ) / 10)) +
    2 * (β * T + 1) * Real.exp (-T / 4)) + 2 * Real.exp (-T)

/-- The effective estimate is uniform over the whole logarithmic window,
including the floor errors at both bin endpoints. -/
theorem exists_candidate_prime_bin_uniform_error :
    ∃ c > 0, ∃ C > 0, ∃ U : ℝ, 2 ≤ U ∧
      ∀ β T : ℝ, U ≤ T → ∀ u ∈ Icc T (β * T), ∀ d ∈ Icc (0 : ℝ) 1,
        |Problem520.weightedPrimeReciprocalBlock ⌊Real.exp u⌋₊ ⌊Real.exp (u + d)⌋₊ - d| ≤
          candidatePrimeBinError c C β T := by
  obtain ⟨c, hc, C, hC, U, hU, hmass⟩ := exists_candidate_prime_bin_mass_error
  refine ⟨c, hc, C, hC, U, hU, ?_⟩
  intro β T hT u hu d hd
  apply (hmass u (hT.trans hu.1) d hd).trans
  have hT0 : 0 ≤ T := by linarith
  have hu0 : 0 ≤ u := hT0.trans hu.1
  have hp : (T / 2) ^ ((1 : ℝ) / 10) ≤ (u / 2) ^ ((1 : ℝ) / 10) :=
    Real.rpow_le_rpow (by positivity) (by linarith [hu.1]) (by norm_num)
  have he : C * Real.exp (-c * (u / 2) ^ ((1 : ℝ) / 10)) ≤
      C * Real.exp (-c * (T / 2) ^ ((1 : ℝ) / 10)) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hp (by linarith)
  have he2 : 2 * (u + 1) * Real.exp (-u / 4) ≤
      2 * (β * T + 1) * Real.exp (-T / 4) := by
    apply mul_le_mul
    · linarith [hu.2]
    · exact Real.exp_le_exp.mpr (by linarith [hu.1])
    · exact (Real.exp_pos _).le
    · linarith [hu.2]
  have he3 : Real.exp (-u) ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith [hu.1])
  unfold candidatePrimeBinError
  linarith

/-- The bin's relative error is smaller than every inverse power of `T`
when its width is `exp(-T^ν)` with `ν < 1/10`. -/
theorem candidate_tendsto_prime_bin_relative_error
    (q C β : ℝ) {c ν : ℝ} (hc : 0 < c) (hν : ν < 1 / 10) :
    Tendsto (fun T : ℝ => T ^ q * candidatePrimeBinError c C β T /
      Real.exp (-(T ^ ν))) atTop (𝓝 0) := by
  have ha : (0 : ℝ) < 1 / 10 := by norm_num
  have hfirst := candidate_tendsto_rpow_mul_exp_rpow_sub q ha hν
    (show 0 < c / (2 : ℝ) ^ ((1 : ℝ) / 10) by positivity)
  have hν1 : ν < 1 := by linarith
  have hsecond := candidate_tendsto_rpow_mul_exp_rpow_sub q zero_lt_one hν1
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hsecond' := candidate_tendsto_rpow_mul_exp_rpow_sub (q + 1) zero_lt_one hν1
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hthird := candidate_tendsto_rpow_mul_exp_rpow_sub q zero_lt_one hν1 zero_lt_one
  have h := ((hfirst.const_mul (4 * C)).add
    ((hsecond'.const_mul (8 * β)).add (hsecond.const_mul 8))).add (hthird.const_mul 2)
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  unfold candidatePrimeBinError
  rw [Real.div_rpow hT.le (by norm_num)]
  simp only [Real.rpow_one, one_mul, Real.rpow_add hT, Real.exp_sub,
    Real.exp_neg, div_eq_mul_inv]
  simp only [neg_mul, Real.exp_neg, inv_inv]
  rw [show c * (T ^ (10 : ℝ)⁻¹ * ((2 : ℝ) ^ (10 : ℝ)⁻¹)⁻¹) =
    c * ((2 : ℝ) ^ (10 : ℝ)⁻¹)⁻¹ * T ^ (10 : ℝ)⁻¹ by ring,
    show T * (4 : ℝ)⁻¹ = (4 : ℝ)⁻¹ * T by ring]
  ring

/-- Candidate equation (13) on every bin of width `exp(-T^ν)` in the
prescribed window: the relative error decays faster than every fixed power.
The admissible exponent comes from the checked effective PNT. -/
theorem candidate_eventually_log_prime_bin_relative_error
    (β q : ℝ) {ν : ℝ} (hν : ν < 1 / 10) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc T (β * T),
      T ^ q * |Problem520.weightedPrimeReciprocalBlock
          ⌊Real.exp u⌋₊ ⌊Real.exp (u + Real.exp (-(T ^ ν)))⌋₊ /
            Real.exp (-(T ^ ν)) - 1| < ε := by
  obtain ⟨c, hc, C, _, U, _, hmass⟩ := exists_candidate_prime_bin_uniform_error
  have herr := candidate_tendsto_prime_bin_relative_error q C β hc hν
  filter_upwards [eventually_ge_atTop U, eventually_gt_atTop (0 : ℝ),
    (tendsto_order.mp herr).2 ε hε] with T hTU hT hsmall u hu
  let δ := Real.exp (-(T ^ ν))
  have hδ : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg hT.le ν))
  have hm := hmass β T hTU u hu δ ⟨hδ.le, hδ1⟩
  have heq : |Problem520.weightedPrimeReciprocalBlock
      ⌊Real.exp u⌋₊ ⌊Real.exp (u + δ)⌋₊ / δ - 1| =
      |Problem520.weightedPrimeReciprocalBlock
        ⌊Real.exp u⌋₊ ⌊Real.exp (u + δ)⌋₊ - δ| / δ := by
    calc
      _ = |(Problem520.weightedPrimeReciprocalBlock
          ⌊Real.exp u⌋₊ ⌊Real.exp (u + δ)⌋₊ - δ) / δ| := by
        rw [sub_div, div_self hδ.ne']
      _ = _ := by rw [abs_div, abs_of_pos hδ]
  change T ^ q * |Problem520.weightedPrimeReciprocalBlock
      ⌊Real.exp u⌋₊ ⌊Real.exp (u + δ)⌋₊ / δ - 1| < ε
  rw [heq]
  calc
    _ ≤ T ^ q * (candidatePrimeBinError c C β T / δ) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hm hδ.le) (Real.rpow_nonneg hT.le q)
    _ < ε := by simpa only [mul_div_assoc] using hsmall

end Erdos.Problem1144
