import Erdos.Problem1144.HarperCandidateTranslationRates
import Erdos.Problem1144.HarperCandidatePrimeBins

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-!
# Literal prime-bin coefficient replacement

The bins contain exactly the primes between the integer parts of their
exponential endpoints. We reverse their order when using the increasing
process-time arithmetic envelope. Whole bins remain present past a coordinate's
endpoint; the complete process's zero extension handles the crossing bin.
-/

noncomputable def candidateLogPrimeBin (z h : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊Real.exp z⌋₊ ⌊Real.exp (z + h)⌋₊).filter Nat.Prime

theorem candidate_mem_logPrimeBin_log_bounds {z h : ℝ} {p : ℕ}
    (hp : p ∈ candidateLogPrimeBin z h) :
    Nat.Prime p ∧ z < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ z + h := by
  obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpL, hpR⟩ := Finset.mem_Ioc.mp hpI
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpP.pos
  have hL : Real.exp z < p := by
    have hc : (⌊Real.exp z⌋₊ : ℝ) + 1 ≤ p := by exact_mod_cast hpL
    exact (Nat.lt_floor_add_one (Real.exp z)).trans_le hc
  have hR : (p : ℝ) ≤ Real.exp (z + h) :=
    (by exact_mod_cast hpR : (p : ℝ) ≤ ⌊Real.exp (z + h)⌋₊).trans
      (Nat.floor_le (Real.exp_pos _).le)
  exact ⟨hpP, (Real.lt_log_iff_exp_lt hp0).mpr hL, (Real.log_le_iff_le_exp hp0).mpr hR⟩

theorem candidate_logPrimeBin_weight_nonneg {z h : ℝ} {p : ℕ}
    (hp : p ∈ candidateLogPrimeBin z h) : 0 ≤ Real.log (p : ℝ) / p := by
  have hpP := (candidate_mem_logPrimeBin_log_bounds hp).1
  apply div_nonneg (Real.log_nonneg _) (Nat.cast_nonneg p)
  exact_mod_cast hpP.one_le

theorem candidate_logPrimeBin_mass (z h : ℝ) :
    (∑ p ∈ candidateLogPrimeBin z h, Real.log (p : ℝ) / p) =
      Problem520.weightedPrimeReciprocalBlock ⌊Real.exp z⌋₊ ⌊Real.exp (z + h)⌋₊ := rfl

/-- The prime-bin coefficient is exactly the original prime Gaussian
coefficient written with the logarithmic prime-mass factor. -/
theorem candidate_prime_logCoefficient_factor (ω : Omega) (t : ℝ) {p : ℕ}
    (hp : Nat.Prime p) :
    Real.sqrt (Real.log (p : ℝ) / p) *
      (harperCandidateLogProcess ω (t - Real.log (p : ℝ)) / Real.sqrt (Real.log (p : ℝ))) =
        harperCandidateLogProcess ω (t - Real.log (p : ℝ)) / Real.sqrt (p : ℝ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog := Real.log_pos hp1
  rw [Real.sqrt_div hlog.le]
  field_simp

/-- Primes beyond the coordinate's real endpoint contribute exactly zero. -/
theorem candidate_prime_logCoefficient_eq_zero (ω : Omega) {t : ℝ} {p : ℕ}
    (ht : t < Real.log (p : ℝ)) :
    harperCandidateLogProcess ω (t - Real.log (p : ℝ)) / Real.sqrt (Real.log (p : ℝ)) = 0 := by
  simp [harperCandidateLogProcess, not_le.mpr (sub_neg.mpr ht)]

/-- Every whole bin beyond the coordinate's endpoint has zero replacement
energy; the crossing bin is retained and covered by the earlier envelope. -/
theorem candidate_primeStepBinEnergy_eq_zero (ω : Omega) {t z h : ℝ} (htz : t ≤ z) :
    (∑ p ∈ candidateLogPrimeBin z h, (Real.log (p : ℝ) / p) *
      (harperCandidateLogProcess ω (t - Real.log (p : ℝ)) / Real.sqrt (Real.log (p : ℝ)) -
        harperCandidateLogProcess ω (t - (z + h)) / Real.sqrt (z + h)) ^ 2) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hb := (candidate_mem_logPrimeBin_log_bounds hp).2
  have hpast : t < Real.log (p : ℝ) := htz.trans_lt hb.1
  have hend : t < z + h := hpast.trans_le hb.2
  rw [candidate_prime_logCoefficient_eq_zero ω hpast]
  simp [harperCandidateLogProcess, not_le.mpr (sub_neg.mpr hend)]

/-- The actual squared prime coefficient replacement energy, before averaging
in the multiplicative signs. -/
noncomputable def candidatePrimeStepEnergy (ω : Omega) (t T h : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, ∑ p ∈ candidateLogPrimeBin (T + (j : ℝ) * h) h,
    (Real.log (p : ℝ) / p) *
      (harperCandidateLogProcess ω (t - Real.log (p : ℝ)) / Real.sqrt (Real.log (p : ℝ)) -
        harperCandidateLogProcess ω (t - (T + (j : ℝ) * h + h)) /
          Real.sqrt (T + (j : ℝ) * h + h)) ^ 2

theorem candidatePrimeStepEnergy_nonneg (ω : Omega) (t T h : ℝ) (n : ℕ) :
    0 ≤ candidatePrimeStepEnergy ω t T h n := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (candidate_logPrimeBin_weight_nonneg hp) (sq_nonneg _)

theorem candidate_integrable_primeStepEnergy (t T h : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ candidatePrimeStepEnergy ω t T h n) mu := by
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro p _
  exact (candidate_integrable_logCoefficient_difference_sq
    (Real.log (p : ℝ)) (T + (j : ℝ) * h + h)
    (t - Real.log (p : ℝ)) (t - (T + (j : ℝ) * h + h))).const_mul _

theorem candidate_integral_primeStepEnergy_eq_sum (t T h : ℝ) (n : ℕ) :
    (∫ ω, candidatePrimeStepEnergy ω t T h n ∂mu) =
      ∑ j ∈ Finset.range n, ∑ p ∈ candidateLogPrimeBin (T + (j : ℝ) * h) h,
        (Real.log (p : ℝ) / p) *
          (∫ ω, (harperCandidateLogProcess ω (t - Real.log (p : ℝ)) /
            Real.sqrt (Real.log (p : ℝ)) -
              harperCandidateLogProcess ω (t - (T + (j : ℝ) * h + h)) /
                Real.sqrt (T + (j : ℝ) * h + h)) ^ 2 ∂mu) := by
  unfold candidatePrimeStepEnergy
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum]
    · simp_rw [integral_const_mul]
    · intro p _
      exact (candidate_integrable_logCoefficient_difference_sq _ _ _ _).const_mul _
  · intro j _
    exact integrable_finset_sum _ fun p _ ↦
      (candidate_integrable_logCoefficient_difference_sq _ _ _ _).const_mul _

/-- Finite-scale replacement bound for the actual primes in every bin. -/
theorem candidate_integral_primeStepEnergy_le_of_mass
    {t T h L C : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 ≤ h) (hL : 0 ≤ L)
    (htL : t - T + h ≤ L) (hC : 0 ≤ C)
    (hmass : ∀ j ∈ Finset.range n,
      Problem520.weightedPrimeReciprocalBlock ⌊Real.exp (T + (j : ℝ) * h)⌋₊
        ⌊Real.exp (T + (j : ℝ) * h + h)⌋₊ ≤ C * h) :
    (∫ ω, candidatePrimeStepEnergy ω t T h n ∂mu) ≤
      C * ((4 / T) * h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L)) := by
  let r : ℕ → ℕ := fun j ↦ n - 1 - j
  let z : ℕ → ℝ := fun j ↦ T + (r j : ℝ) * h
  let a := t - T - (n : ℝ) * h
  have hr (j : ℕ) (hj : j ∈ Finset.range n) : r j ∈ Finset.range n := by
    dsimp only [r]
    apply Finset.mem_range.mpr
    have := Finset.mem_range.mp hj
    omega
  have hcast (j : ℕ) (hj : j ∈ Finset.range n) : (r j : ℝ) + (j : ℝ) + 1 = (n : ℝ) := by
    have hnat : r j + j + 1 = n := by dsimp only [r]; have := Finset.mem_range.mp hj; omega
    exact_mod_cast hnat
  have heq (j : ℕ) (hj : j ∈ Finset.range n) :
      a + (j : ℝ) * h = t - (z j + h) ∧
        a + ((j + 1 : ℕ) : ℝ) * h = t - z j := by
    have hc := hcast j hj
    dsimp only [a, z]
    push_cast
    constructor <;> nlinarith
  have hcover : a + ((n + 1 : ℕ) : ℝ) * h ≤ L := by
    dsimp only [a]
    push_cast
    linarith
  have hbound := candidate_sum_weighted_logCoefficient_difference_sq_le
    (fun j ↦ candidateLogPrimeBin (z j) h)
    (fun _ p ↦ Real.log (p : ℝ) / p)
    (fun _ p ↦ Real.log (p : ℝ)) (fun j _ ↦ z j + h)
    (fun j _ ↦ t - (z j + h)) (fun _ p ↦ t - Real.log (p : ℝ))
    (a := a) (L := L) (h := h) (C := C) (T := T) (d := h) (n := n) (k := 1)
    hh hL hT hC hcover
    (fun _ _ _ hp ↦ candidate_logPrimeBin_weight_nonneg hp)
    (by intro j hj; exact hmass (r j) (hr j hj))
    (by intro j hj p hp
        have hlog := (candidate_mem_logPrimeBin_log_bounds hp).2.1
        have hn := mul_nonneg (Nat.cast_nonneg (r j)) hh
        dsimp only [z] at hlog
        linarith)
    (fun _ _ _ hp ↦ (candidate_mem_logPrimeBin_log_bounds hp).2.2)
    (by intro j hj p hp; have hb := (candidate_mem_logPrimeBin_log_bounds hp).2.1; linarith)
    (by intro j hj p hp; exact (heq j hj).1.le)
    (by intro j hj p hp; have hb := (candidate_mem_logPrimeBin_log_bounds hp).2.2; linarith)
    (by intro j hj p hp
        have hb := (candidate_mem_logPrimeBin_log_bounds hp).2.1
        rw [(heq j hj).2]
        linarith)
  simp only [Nat.cast_one, one_mul, mul_one] at hbound
  rw [candidate_integral_primeStepEnergy_eq_sum]
  have hreflect := Finset.sum_range_reflect
    (fun j ↦ ∑ p ∈ candidateLogPrimeBin (T + (j : ℝ) * h) h,
      (Real.log (p : ℝ) / p) *
        (∫ ω, (harperCandidateLogProcess ω (t - Real.log (p : ℝ)) /
          Real.sqrt (Real.log (p : ℝ)) -
            harperCandidateLogProcess ω (t - (T + (j : ℝ) * h + h)) /
              Real.sqrt (T + (j : ℝ) * h + h)) ^ 2 ∂mu)) n
  change _ ≤ _ at hbound
  dsimp only [z, r] at hbound
  rw [hreflect] at hbound
  exact hbound

/-- A relative prime-mass error at most one gives the required upper mass.
The numerical factor two is the direct consequence of this inequality. -/
theorem candidate_logPrimeBin_mass_le_two_mul {z h : ℝ} (hh : 0 < h)
    (herr : |Problem520.weightedPrimeReciprocalBlock
      ⌊Real.exp z⌋₊ ⌊Real.exp (z + h)⌋₊ / h - 1| ≤ 1) :
    Problem520.weightedPrimeReciprocalBlock
      ⌊Real.exp z⌋₊ ⌊Real.exp (z + h)⌋₊ ≤ 2 * h := by
  have he := (abs_le.mp herr).2
  exact (div_le_iff₀ hh).mp (by linarith)

/-- The finite literal prime replacement estimate with the PNT relative
mass error as its sole arithmetic input. -/
theorem candidate_integral_primeStepEnergy_le
    {t T h L : ℝ} {n : ℕ} (hT : 0 < T) (hh : 0 < h) (hL : 0 ≤ L)
    (htL : t - T + h ≤ L)
    (herr : ∀ j ∈ Finset.range n,
      |Problem520.weightedPrimeReciprocalBlock ⌊Real.exp (T + (j : ℝ) * h)⌋₊
        ⌊Real.exp (T + (j : ℝ) * h + h)⌋₊ / h - 1| ≤ 1) :
    (∫ ω, candidatePrimeStepEnergy ω t T h n ∂mu) ≤
      2 * ((4 / T) * h * (1 + (n : ℝ) * h * Real.exp h) * (1 + L) +
        (h ^ 2 / T + 2 * h ^ 2 / T ^ 3) * ((n : ℝ) * h) * (1 + L)) := by
  exact candidate_integral_primeStepEnergy_le_of_mass hT hh.le hL htL (by norm_num)
    (fun j hj ↦ candidate_logPrimeBin_mass_le_two_mul hh (herr j hj))

/-- Literal prime replacement error decays faster than every fixed power,
uniformly in the coordinate and number of bins. The effective PNT is used
here; no bin-mass hypothesis remains in the conclusion. -/
theorem candidate_eventually_scaled_primeStepEnergy_lt
    (D q : ℝ) {ν ε : ℝ} (hD : 0 ≤ D) (hν : 0 < ν) (hνPNT : ν < 1 / 10)
    (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ t : ℝ, ∀ n : ℕ,
      t - T ≤ D * T → (n : ℝ) * Real.exp (-(T ^ ν)) ≤ D * T →
      T ^ q * (∫ ω, candidatePrimeStepEnergy ω t T (Real.exp (-(T ^ ν))) n ∂mu) < ε := by
  let C := 2 * ((D + 2) * (4 * (D + 1) * Real.exp 1 + 3 * D))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hrate : Tendsto (fun T : ℝ ↦ C * (T ^ (q + 2) * Real.exp (-(T ^ ν))))
      atTop (𝓝 0) := by simpa using (candidate_tendsto_rpow_mul_mesh (q + 2) hν).const_mul C
  have hpnt := candidate_eventually_log_prime_bin_relative_error (D + 1) 0 hνPNT
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_order.mp hrate).2 ε hε, hpnt] with T hT hrateT hpntT
  intro t n ht hn
  let h := Real.exp (-(T ^ ν))
  have hh : 0 < h := Real.exp_pos _
  have hh1 : h ≤ 1 := Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (Real.rpow_nonneg (by linarith : 0 ≤ T) ν))
  have hT0 : 0 < T := by linarith
  have herr (j : ℕ) (hj : j ∈ Finset.range n) :
      |Problem520.weightedPrimeReciprocalBlock ⌊Real.exp (T + (j : ℝ) * h)⌋₊
        ⌊Real.exp (T + (j : ℝ) * h + h)⌋₊ / h - 1| ≤ 1 := by
    have hjR : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
    have hjh := mul_le_mul_of_nonneg_right hjR hh.le
    have hm := hpntT (T + (j : ℝ) * h)
      ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hh.le), by linarith⟩
    simpa only [Real.rpow_zero, one_mul] using hm.le
  have hfinite := candidate_integral_primeStepEnergy_le (t := t) (T := T) (h := h)
    (L := D * T + 1) (n := n) hT0 hh (by positivity) (by linarith) herr
  have hpoly := candidate_whiteStep_bound_le_polynomial hT hh.le hh1 hD
    (mul_nonneg (Nat.cast_nonneg n) hh.le) hn
  have hbound := hfinite.trans (mul_le_mul_of_nonneg_left hpoly (by norm_num : (0 : ℝ) ≤ 2))
  have hm := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hT0.le q)
  apply hm.trans_lt
  have heq : T ^ q * (2 * ((D + 2) * (4 * (D + 1) * Real.exp 1 + 3 * D) * h * T ^ 2)) =
      C * (T ^ (q + 2) * h) := by
    rw [Real.rpow_add hT0, Real.rpow_two]
    dsimp only [C]
    ring
  rw [heq]
  exact hrateT

end Erdos.Problem1144
