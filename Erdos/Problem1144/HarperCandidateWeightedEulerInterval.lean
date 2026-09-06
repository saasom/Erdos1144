import Erdos.Problem1144.HarperCandidateWeightedEulerFractional

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-!
# Fractional moments of actual finite-prime interval energies

The exponent is fixed at `1/8`. The arithmetic inputs are the proved
real-axis quarter moment and the uniform shifted Euler ratio. All interval
integrals below are literal integrals of the squarefree Euler density.
-/

/-- The local vertical energy of the actual finite shifted Euler product. -/
def candidateShiftedEulerIntervalEnergy (y : ℕ) (a u v : ℝ)
    (ω : Problem520.Omega) : ℝ :=
  ∫ t in Icc u v, harperRankinEulerDensity y a ω t

/-- Continuity of the finite shifted density in its vertical coordinate. -/
theorem candidate_continuous_shifted_euler_density (y : ℕ) (a : ℝ)
    (ω : Problem520.Omega) : Continuous (harperRankinEulerDensity y a ω) := by
  unfold harperRankinEulerDensity harperRankinEulerFactor
  fun_prop

/-- The real-axis finite shifted density is strictly positive. -/
theorem candidate_shifted_euler_density_zero_pos (y : ℕ)
    {a : ℝ} (ha : 0 ≤ a) (ω : Problem520.Omega) :
    0 < harperRankinEulerDensity y a ω 0 := by
  unfold harperRankinEulerDensity
  apply Finset.prod_pos
  intro p hp
  have hpP := (Nat.mem_primesBelow.mp hp).2
  have hr0 := harperRankinEulerRadius_nonneg p a
  have hr1 : harperRankinEulerRadius p a < 1 := by
    refine (harperRankinEulerRadius_le_inv_sqrt hpP.one_le ha).trans_lt ?_
    apply inv_lt_one_of_one_lt₀
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
    exact_mod_cast hpP.one_lt
  simp only [harperRankinEulerFactor, zero_mul, Real.cos_zero,
    Real.sin_zero, mul_one, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
  apply sq_pos_of_pos
  cases he : ω p <;> simp [Problem520.ε, he] <;> linarith

/-- Finite interval energies are nonnegative. -/
theorem candidate_shifted_euler_interval_nonneg (y : ℕ) (a u v : ℝ)
    (ω : Problem520.Omega) :
    0 ≤ candidateShiftedEulerIntervalEnergy y a u v ω :=
  integral_nonneg fun t ↦ harperRankinEulerDensity_nonneg y a ω t

private theorem finite_integral_swap {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ → ℝ)
    (u v : ℝ) (hf : ∀ ω, IntegrableOn (f ω) (Icc u v)) :
    (∫ ω, (∫ t in Icc u v, f ω t) ∂P) =
      ∫ t in Icc u v, ∫ ω, f ω t ∂P := by
  simp_rw [integral_fintype (Integrable.of_finite : Integrable _ P), smul_eq_mul]
  rw [integral_finset_sum _ (fun ω _ ↦ (hf ω).const_mul _)]
  simp_rw [integral_const_mul]

private theorem finite_jensen {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → ℝ)
    (hR : ∀ ω, 0 ≤ R ω) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫ ω, R ω ^ q ∂P) ≤ (∫ ω, R ω ∂P) ^ q := by
  exact (Real.concaveOn_rpow hq0 hq1).le_map_integral
    (Real.continuous_rpow_const hq0).continuousOn isClosed_Ici
    (ae_of_all P hR) Integrable.of_finite Integrable.of_finite

private theorem finite_eighth_moment_split {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A R : Ω → ℝ)
    (hA : ∀ ω, 0 ≤ A ω) (hR : ∀ ω, 0 ≤ R ω) :
    (∫ ω, (A ω * R ω) ^ (1 / 8 : ℝ) ∂P) ≤
      (∫ ω, A ω ^ (1 / 4 : ℝ) ∂P) ^ (1 / 2 : ℝ) *
        (∫ ω, R ω ∂P) ^ (1 / 8 : ℝ) := by
  have hm (f : Ω → ℝ) : MemLp f (ENNReal.ofReal (2 : ℝ)) P :=
    ⟨(measurable_of_finite f).aestronglyMeasurable, eLpNorm_lt_top_of_finite⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := P) (p := (2 : ℝ)) (q := (2 : ℝ))
    (Real.holderConjugate_iff.mpr (by norm_num))
    (ae_of_all P fun ω ↦ Real.rpow_nonneg (hA ω) (1 / 8 : ℝ))
    (ae_of_all P fun ω ↦ Real.rpow_nonneg (hR ω) (1 / 8 : ℝ))
    (hm (fun ω ↦ A ω ^ (1 / 8 : ℝ)))
    (hm (fun ω ↦ R ω ^ (1 / 8 : ℝ)))
  have hp (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) (ω : Ω) :
      (f ω ^ (1 / 8 : ℝ)) ^ (2 : ℝ) = f ω ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_mul (hf ω)]
    norm_num
  simp_rw [hp A hA, hp R hR] at h
  calc
    _ = ∫ ω, A ω ^ (1 / 8 : ℝ) * R ω ^ (1 / 8 : ℝ) ∂P := by
      apply integral_congr_ae
      exact ae_of_all P fun ω ↦ Real.mul_rpow (hA ω) (hR ω)
    _ ≤ _ := h
    _ ≤ (∫ ω, A ω ^ (1 / 4 : ℝ) ∂P) ^ (1 / 2 : ℝ) *
        ((∫ ω, R ω ∂P) ^ (1 / 4 : ℝ)) ^ (1 / 2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow
          (integral_nonneg fun ω ↦ Real.rpow_nonneg (hR ω) _)
          (finite_jensen P R hR (q := (1 / 4 : ℝ)) (by norm_num) (by norm_num))
          (by norm_num)
      · exact Real.rpow_nonneg
          (integral_nonneg fun ω ↦ Real.rpow_nonneg (hA ω) _) _
    _ = _ := by
      rw [← Real.rpow_mul (integral_nonneg hR)]
      norm_num

/-- The literal finite-prime local energy has the small fractional moment
needed for the proposed integrated-energy substitute. No random barrier or
unproved moment statement is assumed. -/
theorem candidate_integral_shifted_euler_interval_eighth_le {y : ℕ}
    (hy : 2 ≤ y) {a u v : ℝ} (ha : 0 ≤ a) (huv : u ≤ v)
    (hwindow : ∀ t ∈ Icc u v, |t| ≤ (Real.log (y : ℝ))⁻¹) :
    (∫ ω, candidateShiftedEulerIntervalEnergy y a u v ω ^ (1 / 8 : ℝ)
        ∂Problem520.μ) ≤
      Real.exp (-(∑ p ∈ (y + 1).primesBelow,
        harperRankinEulerRadius p a ^ 2) / 16) *
      (Real.exp (8 * (1 + (Real.log 4 + 4) / Real.log 2)) *
        (v - u)) ^ (1 / 8 : ℝ) := by
  let P := Problem520.harperFairCubeLaw y
  let D : Problem520.HarperPrimeCube y → ℝ → ℝ :=
    fun η t ↦ harperRankinCubeDensity y a t η
  let A : Problem520.HarperPrimeCube y → ℝ := fun η ↦ D η 0
  let R : Problem520.HarperPrimeCube y → ℝ := fun η ↦
    ∫ t in Icc u v, D η t / A η
  let C := Real.exp (8 * (1 + (Real.log 4 + 4) / Real.log 2))
  have hD (η : Problem520.HarperPrimeCube y) (t : ℝ) : 0 ≤ D η t := by
    unfold D harperRankinCubeDensity
    exact Finset.prod_nonneg fun p _ ↦
      harperRankinEulerFactor_nonneg (fun _ ↦ η p) p.1 a t
  have hcont (η : Problem520.HarperPrimeCube y) : Continuous (D η) := by
    unfold D harperRankinCubeDensity harperRankinCoordinateFactor harperRankinEulerFactor
    fun_prop
  have hApos (η : Problem520.HarperPrimeCube y) : 0 < A η := by
    let ω : Problem520.Omega := fun n ↦
      if h : n ∈ (y + 1).primesBelow then η ⟨n, h⟩ else false
    have he : Problem520.harperPrimeRestriction y ω = η := by
      funext p
      simp [Problem520.harperPrimeRestriction, ω, p.2]
    rw [show A η = harperRankinEulerDensity y a ω 0 by
      dsimp only [A, D]
      rw [← he, harperRankinCubeDensity_harperPrimeRestriction]]
    exact candidate_shifted_euler_density_zero_pos y ha ω
  have hR : ∀ η, 0 ≤ R η := fun η ↦
    integral_nonneg fun t ↦ div_nonneg (hD η t) (hApos η).le
  have hfactor (η : Problem520.HarperPrimeCube y) :
      (∫ t in Icc u v, D η t) = A η * R η := by
    dsimp [R]
    rw [integral_div]
    field_simp [(hApos η).ne']
  have hRmean : (∫ η, R η ∂P) ≤ C * (v - u) := by
    rw [show R = _ from rfl, finite_integral_swap P _ u v
      (fun η ↦ ((hcont η).div_const (A η)).integrableOn_Icc)]
    have hbound (t : ℝ) (ht : t ∈ Icc u v) :
        (∫ η, D η t / A η ∂P) ≤ C := by
      have hpull := Problem520.integral_comp_harperPrimeRestriction_mu y
        (fun η ↦ D η t / A η)
      have he : (fun ω ↦ D (Problem520.harperPrimeRestriction y ω) t /
          A (Problem520.harperPrimeRestriction y ω)) =
          candidateShiftedEulerRatio y a t := by
        funext ω
        simp only [D, A, harperRankinCubeDensity_harperPrimeRestriction,
          candidateShiftedEulerRatio]
      rw [he] at hpull
      change (∫ η, D η t / A η
        ∂Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦ Problem520.coin)) ≤ C
      rw [← hpull]
      exact candidate_integral_shifted_euler_ratio_local_le hy ha (hwindow t ht)
    have hmeancont : Continuous (fun t ↦ ∫ η, D η t / A η ∂P) := by
      simp_rw [integral_fintype (Integrable.of_finite : Integrable _ P)]
      fun_prop
    calc
      _ ≤ ∫ t in Icc u v, C := by
        apply setIntegral_mono_on (μ := volume) hmeancont.integrableOn_Icc
          (continuous_const.integrableOn_Icc : IntegrableOn (fun _ : ℝ ↦ C) (Icc u v))
          measurableSet_Icc
        exact hbound
      _ = C * (v - u) := by
        simp [Real.volume_real_Icc_of_le huv, mul_comm]
  have hAmean : (∫ η, A η ^ (1 / 4 : ℝ) ∂P) ≤
      Real.exp (-(∑ p ∈ (y + 1).primesBelow,
        harperRankinEulerRadius p a ^ 2) / 8) := by
    have hpull := Problem520.integral_comp_harperPrimeRestriction_mu y
      (fun η ↦ A η ^ (1 / 4 : ℝ))
    simp only [A, D, harperRankinCubeDensity_harperPrimeRestriction] at hpull
    change (∫ η, harperRankinCubeDensity y a 0 η ^ (1 / 4 : ℝ)
      ∂Measure.pi (fun _ : Problem520.HarperPrimeIndex y ↦ Problem520.coin)) ≤ _
    rw [← hpull]
    exact candidate_integral_shifted_euler_quarter_le_exp y ha
  have hpull := Problem520.integral_comp_harperPrimeRestriction_mu y
    (fun η ↦ (∫ t in Icc u v, D η t) ^ (1 / 8 : ℝ))
  have he : (fun ω ↦ (∫ t in Icc u v,
      D (Problem520.harperPrimeRestriction y ω) t) ^ (1 / 8 : ℝ)) =
      (fun ω ↦ candidateShiftedEulerIntervalEnergy y a u v ω ^ (1 / 8 : ℝ)) := by
    funext ω
    simp only [D, harperRankinCubeDensity_harperPrimeRestriction,
      candidateShiftedEulerIntervalEnergy]
  rw [he] at hpull
  rw [hpull]
  simp_rw [hfactor]
  refine (finite_eighth_moment_split P A R (fun η ↦ (hApos η).le) hR).trans ?_
  calc
    _ ≤ (Real.exp (-(∑ p ∈ (y + 1).primesBelow,
        harperRankinEulerRadius p a ^ 2) / 8)) ^ (1 / 2 : ℝ) *
        (C * (v - u)) ^ (1 / 8 : ℝ) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow
          (integral_nonneg fun η ↦ Real.rpow_nonneg (hApos η).le _) hAmean (by norm_num)
      · exact Real.rpow_le_rpow (integral_nonneg hR) hRmean (by norm_num)
      · exact Real.rpow_nonneg (integral_nonneg hR) _
      · positivity
    _ = _ := by
      rw [← Real.exp_mul]
      congr 2
      ring

end
end Erdos.Problem1144
