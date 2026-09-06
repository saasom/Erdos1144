import Erdos.Problem1144.HarperCandidateCovarianceScreen
import Erdos.Problem520.HarperVerticalMesh
import Erdos.Problem520.MertensProduct

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

/-- A literal cutoff-dependent approximation, at the scale needed for the
weighted Euler-ratio bound. -/
noncomputable def candidateCovarianceMeshPoint (j : ℕ) (t : ℝ) : ℝ :=
  Problem520.harperVerticalMeshPoint
    (Real.log (Problem520.harperBlockEndpoint j : ℝ))⁻¹ 0 t

/-- The finite mesh covering the full frequency window. -/
noncomputable def candidateCovarianceMeshGrid (j : ℕ) (M : ℝ) : Finset ℝ :=
  Problem520.harperVerticalMeshGridOn
    (Real.log (Problem520.harperBlockEndpoint j : ℝ))⁻¹ 0 M

/-- Harper's mesh event has only an upper bound. The lower D-star bound is
paid for later by the density-weighted deletion. -/
def candidateCovarianceMeshEvent (start N : ℕ) (t W : ℝ) : Set Problem520.Omega :=
  {ω | ∀ j : Fin (N + 1), Real.sqrt (Problem520.harperEulerDensity
    (Problem520.harperBlockEndpoint (start + j.val)) ω
      (candidateCovarianceMeshPoint (start + j.val) t)) ≤
    Real.log (Problem520.harperBlockEndpoint (start + j.val) : ℝ) * W ^ 5}

/-- One common event enforces the upper mesh bounds over the whole window. -/
def candidateCovarianceCommonMeshEvent (start N : ℕ) (M W : ℝ) : Set Problem520.Omega :=
  {ω | ∀ j : Fin (N + 1), ∀ u ∈ candidateCovarianceMeshGrid (start + j.val) M,
    Real.sqrt (Problem520.harperEulerDensity
      (Problem520.harperBlockEndpoint (start + j.val)) ω u) ≤
    Real.log (Problem520.harperBlockEndpoint (start + j.val) : ℝ) * W ^ 5}

theorem candidate_covarianceMeshPoint_close (j : ℕ) (t : ℝ) :
    |t - candidateCovarianceMeshPoint j t| ≤
      (Real.log (Problem520.harperBlockEndpoint j : ℝ))⁻¹ := by
  have hlog : 0 < Real.log (Problem520.harperBlockEndpoint j : ℝ) :=
    lt_of_lt_of_le zero_lt_one (Problem520.one_le_log_harperBlockEndpoint j)
  simpa only [candidateCovarianceMeshPoint, Problem520.harperVerticalMeshSpacing,
    pow_zero, Nat.cast_one, one_mul] using
    (Problem520.abs_sub_harperVerticalMeshPoint_lt_spacing (inv_pos.mpr hlog) 0 t).le

theorem candidate_covarianceCommonMesh_subset (start N : ℕ) (M W t : ℝ)
    (ht : |t| ≤ M) :
    candidateCovarianceCommonMeshEvent start N M W ⊆ candidateCovarianceMeshEvent start N t W := by
  intro ω hω j
  apply hω j
  exact Problem520.harperVerticalMeshPoint_mem_gridOn_of_abs_le
    (by have := Problem520.one_le_log_harperBlockEndpoint (start + j.val); positivity) 0 ht

theorem candidate_measurableSet_covarianceCommonMesh (start N : ℕ) (M W : ℝ) :
    MeasurableSet (candidateCovarianceCommonMeshEvent start N M W) := by
  rw [show candidateCovarianceCommonMeshEvent start N M W =
    ⋂ j : Fin (N + 1), ⋂ u : candidateCovarianceMeshGrid (start + j.val) M,
      {ω | Real.sqrt (Problem520.harperEulerDensity
        (Problem520.harperBlockEndpoint (start + j.val)) ω u.val) ≤
        Real.log (Problem520.harperBlockEndpoint (start + j.val) : ℝ) * W ^ 5} by
      ext ω
      simp [candidateCovarianceCommonMeshEvent]]
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun u => ?_
  exact measurableSet_le (Problem520.stronglyMeasurable_harperEulerDensity _ _).measurable.sqrt measurable_const

theorem candidate_measurable_covarianceMeshPoint (j : ℕ) : Measurable (candidateCovarianceMeshPoint j) := by
  unfold candidateCovarianceMeshPoint Problem520.harperVerticalMeshPoint Problem520.harperRoundDown
  fun_prop

theorem candidate_measurableSet_covarianceMesh_joint (start N : ℕ) (W : ℝ) :
    MeasurableSet {z : ℝ × Problem520.Omega | z.2 ∈ candidateCovarianceMeshEvent start N z.1 W} := by
  rw [show {z : ℝ × Problem520.Omega | z.2 ∈ candidateCovarianceMeshEvent start N z.1 W} =
      ⋂ j : Fin (N + 1), {z : ℝ × Problem520.Omega |
        Real.sqrt (Problem520.harperEulerDensity
          (Problem520.harperBlockEndpoint (start + j.val)) z.2
          (candidateCovarianceMeshPoint (start + j.val) z.1)) ≤
        Real.log (Problem520.harperBlockEndpoint (start + j.val) : ℝ) * W ^ 5} by
      ext z
      simp [candidateCovarianceMeshEvent]]
  apply MeasurableSet.iInter
  intro j
  have hp : Measurable (fun z : ℝ × Problem520.Omega =>
      (candidateCovarianceMeshPoint (start + j.val) z.1, z.2)) :=
    (((candidate_measurable_covarianceMeshPoint (start + j.val)).comp
      (measurable_fst : Measurable (Prod.fst : ℝ × Problem520.Omega → ℝ))).prodMk measurable_snd)
  have hm := (Problem520.measurable_harperEulerDensity_joint
    (Problem520.harperBlockEndpoint (start + j.val))).comp hp
  exact measurableSet_le hm.sqrt measurable_const

private theorem modulus_tail_le (y : ℕ) (t : ℝ) {U : ℝ} (hU : 0 < U) :
    Problem520.μ.real {ω | U < Real.sqrt (Problem520.harperEulerDensity y ω t)} ≤
      Problem520.primeEnergyNormalizer y / U ^ 2 := by
  have hsub : {ω | U < Real.sqrt (Problem520.harperEulerDensity y ω t)} ⊆
      {ω | U ^ 2 ≤ Problem520.harperEulerDensity y ω t} := by
    intro ω hω
    have hs := Real.sq_sqrt (Problem520.harperEulerDensity_nonneg y ω t)
    have hp := Real.sqrt_nonneg (Problem520.harperEulerDensity y ω t)
    dsimp only [Set.mem_setOf_eq] at hω ⊢
    nlinarith
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ fun ω => Problem520.harperEulerDensity_nonneg y ω t)
    (Problem520.integrable_harperEulerDensity y t) (U ^ 2)
  rw [Problem520.integral_harperEulerDensity] at hm
  exact (measureReal_mono hsub).trans ((le_div_iff₀ (by positivity)).mpr (by nlinarith [hm]))

/-- Explicit probability budget for one common mesh event. In particular,
`M=W²` and a path with `N=O(W)` have a vanishing failure probability. -/
theorem candidate_exists_covarianceCommonMesh_failure_le :
    ∃ C > 0, ∀ start N : ℕ, ∀ M W : ℝ, 0 ≤ M → 0 < W →
      Problem520.μ.real (candidateCovarianceCommonMeshEvent start N M W)ᶜ ≤
        C * (2 * M + 3) * (N + 1 : ℕ) / W ^ 10 := by
  let C := Real.exp (1 - Real.log (Real.log 2) + 2 * (Real.log 4 + 4) / Real.log 2)
  refine ⟨C, Real.exp_pos _, ?_⟩
  intro start N M W hM hW
  let B : Fin (N + 1) → ℕ := fun j => Problem520.harperBlockEndpoint (start + j.val)
  let bad : Fin (N + 1) → ℝ → Set Problem520.Omega := fun j u =>
    {ω | Real.log (B j : ℝ) * W ^ 5 < Real.sqrt (Problem520.harperEulerDensity (B j) ω u)}
  have heq : (candidateCovarianceCommonMeshEvent start N M W)ᶜ =
      ⋃ j : Fin (N + 1), ⋃ u ∈ candidateCovarianceMeshGrid (start + j.val) M, bad j u := by
    ext ω
    simp [candidateCovarianceCommonMeshEvent, bad, B, not_forall, not_le]
  rw [heq]
  have hlocal (j : Fin (N + 1)) :
      Problem520.μ.real (⋃ u ∈ candidateCovarianceMeshGrid (start + j.val) M, bad j u) ≤
        C * (2 * M + 3) / W ^ 10 := by
    let L := Real.log (B j : ℝ)
    have hL : 1 ≤ L := Problem520.one_le_log_harperBlockEndpoint _
    have hLp : 0 < L := by linarith
    have hB : 2 ≤ B j := by
      dsimp only [B]
      have := Problem520.harperBlockEndpoint_ge_sixteen (start + j.val)
      omega
    have hc := Problem520.card_harperVerticalMeshGridOn_le L⁻¹ 0 M
    have hceil := (Nat.ceil_lt_add_one (show 0 ≤ M * L by positivity)).le
    have hcard : (candidateCovarianceMeshGrid (start + j.val) M).card ≤ 2 * ⌈M * L⌉₊ + 1 := by
      simpa only [candidateCovarianceMeshGrid, Problem520.harperVerticalMeshSpacing,
        pow_zero, Nat.cast_one, one_mul, div_inv_eq_mul, L, B] using hc
    have hcardR : ((candidateCovarianceMeshGrid (start + j.val) M).card : ℝ) ≤ (2 * M + 3) * L := by
      have hh : ((candidateCovarianceMeshGrid (start + j.val) M).card : ℝ) ≤
          2 * (⌈M * L⌉₊ : ℝ) + 1 := by exact_mod_cast hcard
      nlinarith
    calc
      _ ≤ ∑ u ∈ candidateCovarianceMeshGrid (start + j.val) M, Problem520.μ.real (bad j u) :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _u ∈ candidateCovarianceMeshGrid (start + j.val) M, C / (L * W ^ 10) := by
        apply Finset.sum_le_sum
        intro u hu
        have ht := modulus_tail_le (B j) u (mul_pos hLp (pow_pos hW 5))
        have hnormal := Problem520.primeEnergyNormalizer_le_mertensConstant_mul_log hB
        change Problem520.μ.real (bad j u) ≤ _
        apply ht.trans
        calc
          _ ≤ (C * L) / (L * W ^ 5) ^ 2 := div_le_div_of_nonneg_right hnormal (by positivity)
          _ = _ := by field_simp
      _ = ((candidateCovarianceMeshGrid (start + j.val) M).card : ℝ) * (C / (L * W ^ 10)) := by simp
      _ ≤ ((2 * M + 3) * L) * (C / (L * W ^ 10)) :=
        mul_le_mul_of_nonneg_right hcardR (by dsimp only [C]; positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ j : Fin (N + 1), Problem520.μ.real
        (⋃ u ∈ candidateCovarianceMeshGrid (start + j.val) M, bad j u) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin (N + 1), C * (2 * M + 3) / W ^ 10 := Finset.sum_le_sum fun j _ => hlocal j
    _ = _ := by simp; ring

end Erdos.Problem1144
