import Erdos.Problem1144.HarperCompleteFiniteParseval
import Erdos.Problem1144.HarperCandidateLogScreen
import Erdos.Problem1144.HarperCandidateLaplaceIntegrability

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Positivity of every finite-smooth real Laplace transform

The absolutely convergent smooth Euler series is available at every positive
real exponent. Integrating its step-function expansion identifies the smooth
Laplace transform with a positive finite Euler product.
-/

noncomputable def candidateRealDirichletHom (ω : Omega) (σ : ℝ) : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else f ω n * Real.exp (-σ * Real.log (n : ℝ))
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [hm, hn, mul_eq_zero, or_false, if_false]
    rw [f_mul_of_ne_zero ω hm hn, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hn), mul_add,
      Real.exp_add]
    ring

theorem candidateRealDirichletHom_apply {ω : Omega} {σ : ℝ} {n : ℕ} (hn : 0 < n) :
    candidateRealDirichletHom ω σ n = f ω n * Real.exp (-σ * Real.log (n : ℝ)) := by
  simp only [candidateRealDirichletHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    if_neg hn.ne']

theorem norm_candidateRealDirichletHom {ω : Omega} {σ : ℝ} {n : ℕ} (hn : 0 < n) :
    ‖candidateRealDirichletHom ω σ n‖ = Real.exp (-σ * Real.log (n : ℝ)) := by
  rw [candidateRealDirichletHom_apply hn, norm_mul, Real.norm_eq_abs, abs_f,
    one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem norm_candidateRealDirichletHom_prime_lt_one
    (ω : Omega) {σ : ℝ} (hσ : 0 < σ) {p : ℕ} (hp : p.Prime) :
    ‖candidateRealDirichletHom ω σ p‖ < 1 := by
  rw [norm_candidateRealDirichletHom hp.pos, Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hσ)
    (Real.log_pos (by exact_mod_cast hp.one_lt))

theorem candidateRealDirichletHom_smooth_hasSum
    (ω : Omega) (X : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : (X + 1).smoothNumbers ↦ ‖candidateRealDirichletHom ω σ n‖) ∧
      HasSum (fun n : (X + 1).smoothNumbers ↦ candidateRealDirichletHom ω σ n)
        (∏ p ∈ (X + 1).primesBelow, (1 - candidateRealDirichletHom ω σ p)⁻¹) :=
  EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := (candidateRealDirichletHom ω σ).toMonoidHom)
    (norm_candidateRealDirichletHom_prime_lt_one ω hσ) (X + 1)

theorem candidateRealDirichletHom_smooth_product_pos
    (ω : Omega) (X : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    0 < ∏ p ∈ (X + 1).primesBelow, (1 - candidateRealDirichletHom ω σ p)⁻¹ := by
  apply Finset.prod_pos
  intro p hp
  apply inv_pos.mpr
  have h := norm_candidateRealDirichletHom_prime_lt_one ω hσ
    (Nat.prime_of_mem_primesBelow hp)
  have hle := le_abs_self (candidateRealDirichletHom ω σ p)
  rw [Real.norm_eq_abs] at h
  linarith

/-- The Laplace atom contributed by one positive integer. -/
noncomputable def candidateLaplaceAtom (σ : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (Set.Ici (Real.log (n : ℝ))).indicator (fun t ↦ Real.exp (-σ * t)) t

theorem integrable_candidateLaplaceAtom {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    Integrable (candidateLaplaceAtom σ n) volume := by
  apply (integrable_indicator_iff measurableSet_Ici).mpr
  exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hσ) _)

theorem integral_candidateLaplaceAtom {σ : ℝ} (hσ : 0 < σ) (n : ℕ) :
    (∫ t, candidateLaplaceAtom σ n t) = Real.exp (-σ * Real.log (n : ℝ)) / σ := by
  unfold candidateLaplaceAtom
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (neg_neg_of_pos hσ)]
  simp

theorem candidateLaplaceAtom_nonneg (σ : ℝ) (n : ℕ) (t : ℝ) :
    0 ≤ candidateLaplaceAtom σ n t :=
  Set.indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) _

/-- At each real time only finitely many smooth Laplace atoms are nonzero,
and their sum is exactly the exponentially weighted smooth partial sum. -/
theorem tsum_candidateLaplaceAtoms_eq_smoothSum
    (ω : Omega) (X : ℕ) (σ t : ℝ) :
    (∑' n : (X + 1).smoothNumbers, f ω n * candidateLaplaceAtom σ n t) =
      Real.exp (-σ * t) * smoothSum ω X ⌊Real.exp t⌋₊ := by
  classical
  rw [tsum_subtype (X + 1).smoothNumbers (fun n ↦ f ω n * candidateLaplaceAtom σ n t)]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊Real.exp t⌋₊)]
  · unfold smoothSum
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
    have hlog : Real.log (n : ℝ) ≤ t :=
      (Real.log_le_iff_le_exp (by exact_mod_cast hnpos)).mpr
        ((Nat.le_floor_iff (Real.exp_pos _).le).mp (Finset.mem_Icc.mp hn).2)
    have hs := mem_smoothNumbers_succ_iff_isXSmooth (y := X) hnpos.ne'
    by_cases hsm : IsXSmooth X n
    · simp only [Set.indicator, hs, hsm, if_true, candidateLaplaceAtom,
        Set.mem_Ici, hlog]
      ring
    · simp only [Set.indicator, hs, hsm, if_false, mul_zero]
  · intro n hn
    by_cases hsm : n ∈ (X + 1).smoothNumbers
    · have hnpos := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hsm)
      have hlog : ¬ Real.log (n : ℝ) ≤ t := by
        intro hlog
        apply hn
        exact Finset.mem_Icc.mpr ⟨hnpos,
          (Nat.le_floor_iff (Real.exp_pos _).le).mpr
            ((Real.log_le_iff_le_exp (by exact_mod_cast hnpos)).mp hlog)⟩
      simp only [Set.indicator, hsm, if_true, candidateLaplaceAtom, Set.mem_Ici,
        hlog, if_false, mul_zero]
    · simp only [Set.indicator, hsm, if_false]

/-- Absolute summability of the integrated atom norms follows from the
finite-smooth Euler series, even below the absolute-convergence line for the
all-prime Dirichlet series. -/
theorem summable_integral_norm_candidateLaplaceAtoms
    (ω : Omega) (X : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : (X + 1).smoothNumbers ↦
      ∫ t, ‖f ω n * candidateLaplaceAtom σ n t‖) := by
  have hnpos (n : (X + 1).smoothNumbers) : 0 < (n : ℕ) :=
    Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
  have heq (n : (X + 1).smoothNumbers) :
      (∫ t, ‖f ω n * candidateLaplaceAtom σ n t‖) =
        ‖candidateRealDirichletHom ω σ n‖ / σ := by
    rw [norm_candidateRealDirichletHom (hnpos n)]
    simp_rw [norm_mul, Real.norm_eq_abs, abs_f, one_mul,
      abs_of_nonneg (candidateLaplaceAtom_nonneg σ _ _)]
    rw [integral_candidateLaplaceAtom hσ]
  simp_rw [heq]
  exact (candidateRealDirichletHom_smooth_hasSum ω X hσ).1.div_const σ

/-- The full real-line Laplace transform of a finite-smooth partial sum is
the finite Euler product divided by its real Dirichlet exponent. -/
theorem candidate_integral_smoothSum_exp_eq_product
    (ω : Omega) (X : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ t, Real.exp (-σ * t) * smoothSum ω X ⌊Real.exp t⌋₊) =
      (∏ p ∈ (X + 1).primesBelow, (1 - candidateRealDirichletHom ω σ p)⁻¹) / σ := by
  have h := integral_tsum_of_summable_integral_norm
    (fun n : (X + 1).smoothNumbers ↦
      (integrable_candidateLaplaceAtom hσ (n : ℕ)).const_mul (f ω n))
    (summable_integral_norm_candidateLaplaceAtoms ω X hσ)
  have heq (n : (X + 1).smoothNumbers) :
      (∫ t, f ω n * candidateLaplaceAtom σ n t) = candidateRealDirichletHom ω σ n / σ := by
    rw [integral_const_mul, integral_candidateLaplaceAtom hσ,
      candidateRealDirichletHom_apply
        (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property))]
    ring
  simp_rw [heq, tsum_candidateLaplaceAtoms_eq_smoothSum] at h
  rw [tsum_div_const, (candidateRealDirichletHom_smooth_hasSum ω X hσ).2.tsum_eq] at h
  exact h.symm

/-- The literal old process has the exponential denominator, including at
times when the integer cutoff vanishes. -/
theorem candidate_logOld_eq_smoothSum_div_exp
    (ω : Omega) (X : ℕ) (t : ℝ) :
    harperCandidateLogOld ω X t = smoothSum ω X ⌊Real.exp t⌋₊ / Real.exp (t / 2) := by
  unfold harperCandidateLogOld smoothProcess harperCandidateLogNormalization
  by_cases hN : ⌊Real.exp t⌋₊ = 0
  · simp [hN, smoothSum]
  · have hsqrt : Real.sqrt (⌊Real.exp t⌋₊ : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))
    field_simp

theorem candidate_weighted_logOld_eq_smoothSum_exp
    (ω : Omega) (X : ℕ) (T t : ℝ) :
    Real.exp (-t / T) * harperCandidateLogOld ω X t =
      Real.exp (-(1 / 2 + T⁻¹) * t) * smoothSum ω X ⌊Real.exp t⌋₊ := by
  rw [candidate_logOld_eq_smoothSum_div_exp]
  calc
    _ = (Real.exp (-t / T) * Real.exp (-(t / 2))) *
        smoothSum ω X ⌊Real.exp t⌋₊ := by rw [Real.exp_neg]; ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- Exact finite-smooth Laplace identity in the candidate's normalization. -/
theorem candidate_integral_laplace_logOld_eq_product
    (ω : Omega) (X : ℕ) {T : ℝ} (hT : 0 < T) :
    (∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogOld ω X t) =
      (∏ p ∈ (X + 1).primesBelow,
        (1 - candidateRealDirichletHom ω (1 / 2 + T⁻¹) p)⁻¹) / (1 / 2 + T⁻¹) := by
  simp_rw [candidate_weighted_logOld_eq_smoothSum_exp]
  rw [← integral_Ici_eq_integral_Ioi]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact candidate_integral_smoothSum_exp_eq_product ω X (by positivity)
  · intro t ht
    have htneg : t < 0 := not_le.mp ht
    have hfloor : ⌊Real.exp t⌋₊ = 0 :=
      Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr htneg)
    simp [hfloor, smoothSum]

/-- Every finite-smooth real Laplace transform is strictly positive. This
uses only an absolutely convergent finite-prime Euler product. -/
theorem candidate_integral_laplace_logOld_pos
    (ω : Omega) (X : ℕ) {T : ℝ} (hT : 0 < T) :
    0 < ∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogOld ω X t := by
  rw [candidate_integral_laplace_logOld_eq_product ω X hT]
  exact div_pos (candidateRealDirichletHom_smooth_product_pos ω X (by positivity))
    (by positivity)

/-- The nonnegative form needed when passing to the full-process limit. -/
theorem candidate_integral_laplace_logOld_nonneg
    (ω : Omega) (X : ℕ) {T : ℝ} (hT : 0 < T) :
    0 ≤ ∫ t in Ioi 0, Real.exp (-t / T) * harperCandidateLogOld ω X t :=
  (candidate_integral_laplace_logOld_pos ω X hT).le

end Erdos.Problem1144
