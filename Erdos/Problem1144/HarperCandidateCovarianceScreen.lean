import Erdos.Problem1144.HarperCandidateCovarianceGrowingHeightDeletion
import Erdos.Problem520.HarperParsevalTail

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-!
# Literal full-product D-star and strong covariance screens

At exact dyadic-logarithmic cutoffs `B_j = 2^(16·2^j)`, D-star requires
`W⁻¹ ≤ |F(B_j,1/2+it)| ≤ log(B_j) W^6`. The stronger barrier at selected
interior locations is `|F(B_j,1/2+it)| ≤ log(B_j)/W^1000`.
The square root below is the actual Euler-product modulus, since
`harperEulerDensity` is its squared modulus. All logarithmic parameters and
the initial-prefix corridor are derived from these literal inequalities.
-/

/-- The literal two-sided D-star screen at every dyadic cutoff, including
the initial prefix. -/
def candidateCovarianceDStarEvent (start N : ℕ) (t W : ℝ) : Set Problem520.Omega :=
  {ω | ∀ j : Fin (N + 1), W⁻¹ ≤ Real.sqrt
      (Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + j.val)) ω t) ∧
    Real.sqrt (Problem520.harperEulerDensity
      (Problem520.harperBlockEndpoint (start + j.val)) ω t) ≤
      Real.log (Problem520.harperBlockEndpoint (start + j.val) : ℝ) * W ^ 6}

/-- The stronger full Euler-product barrier on the selected interior
cutoffs. The exponent 1000 is Harper's covariance barrier parameter. -/
def candidateCovarianceStrongScreenEvent (start : ℕ) (t W : ℝ)
    (s : Finset ℕ) : Set Problem520.Omega :=
  {ω | ∀ j ∈ s, Real.sqrt
    (Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + j)) ω t) ≤
    Real.log (Problem520.harperBlockEndpoint (start + j) : ℝ) / W ^ 1000}

/-- Exact logarithmic scale increment for the integer cutoff schedule. -/
theorem candidate_log_log_blockEndpoint_add (start j : ℕ) :
    Real.log (Real.log (Problem520.harperBlockEndpoint (start + j) : ℝ)) =
      Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + (j : ℝ) * Real.log 2 := by
  have heq : Real.log (Problem520.harperBlockEndpoint (start + j) : ℝ) =
      Real.log (Problem520.harperBlockEndpoint start : ℝ) * (2 : ℝ) ^ j := by
    rw [Problem520.log_harperBlockEndpoint_eq, Problem520.log_harperBlockEndpoint_eq, pow_add]
    ring
  rw [heq, Real.log_mul (by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (Problem520.one_le_log_harperBlockEndpoint start)))
    (by positivity), Real.log_pow]

/-- The literal D-star screen supplies every parameter in the existing
full-product initial-corridor adapter. No extra barrier or drift premise is
introduced. -/
theorem candidate_covariance_DStar_deletion_subset_full
    (start N : ℕ) (t W : ℝ) (hW : 1 ≤ W) (s : Finset ℕ) :
    candidateCovarianceDStarEvent start N t W \ candidateCovarianceStrongScreenEvent start t W s ⊆
      candidateFullEulerStrongBarrierDeletionEvent start N t
        (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 6 * Real.log W)
        (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) - 1000 * Real.log W)
        (-Real.log W)
        (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 6 * Real.log W) s := by
  intro ω hω
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hlogB (j : ℕ) : 0 < Real.log (Problem520.harperBlockEndpoint (start + j) : ℝ) :=
    lt_of_lt_of_le zero_lt_one (Problem520.one_le_log_harperBlockEndpoint (start + j))
  have hupper (j : ℕ) (hj : j ≤ N) :
      (1 / 2 : ℝ) * Real.log (Problem520.harperEulerDensity
        (Problem520.harperBlockEndpoint (start + j)) ω t) - (j : ℝ) * Real.log 2 ≤
      Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 6 * Real.log W := by
    have hjbound := (hω.1 (⟨j, by omega⟩ : Fin (N + 1))).2
    have hl := Real.log_le_log
      (Real.sqrt_pos.mpr (Problem520.harperEulerDensity_pos _ ω t)) hjbound
    rw [Real.log_sqrt (Problem520.harperEulerDensity_pos _ ω t).le,
      Real.log_mul (hlogB j).ne' (pow_ne_zero 6 hWpos.ne'), Real.log_pow,
      candidate_log_log_blockEndpoint_add] at hl
    norm_num only [Nat.cast_ofNat] at hl
    linarith
  have hzero := (hω.1 (⟨0, by omega⟩ : Fin (N + 1))).1
  have hlo := Real.log_le_log (inv_pos.mpr hWpos) hzero
  rw [Real.log_inv, Real.log_sqrt (Problem520.harperEulerDensity_pos _ ω t).le] at hlo
  simp only [Fin.val_zero, add_zero] at hlo
  have hbad := hω.2
  simp only [candidateCovarianceStrongScreenEvent, Set.mem_setOf_eq,
    not_forall, not_le] at hbad
  obtain ⟨j, hj, hjbad⟩ := hbad
  have hl := Real.log_le_log (div_pos (hlogB j) (pow_pos hWpos 1000)) hjbad.le
  rw [Real.log_div (hlogB j).ne' (pow_ne_zero 1000 hWpos.ne'), Real.log_pow,
    Real.log_sqrt (Problem520.harperEulerDensity_pos _ ω t).le,
    candidate_log_log_blockEndpoint_add] at hl
  norm_num only [Nat.cast_ofNat] at hl
  refine ⟨by linarith, ?_, ?_, j, hj, by linarith⟩
  · have h := hupper 0 (by omega)
    simpa only [add_zero, Nat.cast_zero, zero_mul, sub_zero] using h
  · intro k
    exact hupper (k.val + 1) (by omega)

private theorem screen_mass_le_range
    (y start N : ℕ) (hy : Problem520.harperBlockEndpoint (start + N) ≤ y)
    (t W : ℝ) (hW : 1 ≤ W) (s : Finset ℕ) (hs : ∀ j ∈ s, j ≤ N) :
    (∫ ω in candidateCovarianceDStarEvent start N t W \ candidateCovarianceStrongScreenEvent start t W s,
      Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
    (∫ ω in Problem520.harperPrimeRestriction y ⁻¹'
      candidateEulerStrongBarrierDeletionEvent y start N t
        (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 7 * Real.log W)
        (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 1013 * Real.log W) s,
      Problem520.harperEulerDensity y ω t ∂Problem520.μ) := by
  have hsub := candidate_covariance_DStar_deletion_subset_full start N t W hW s
  have hfirst := setIntegral_mono_set (Problem520.integrable_harperEulerDensity y t).integrableOn
    (Filter.Eventually.of_forall fun ω => (Problem520.harperEulerDensity_pos y ω t).le)
    (Filter.Eventually.of_forall hsub)
  have hsecond := candidate_fullEuler_deletion_mass_le_range y start N hy t
    (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 6 * Real.log W)
    (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) - 1000 * Real.log W)
    (-Real.log W)
    (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 6 * Real.log W) s hs
  convert hfirst.trans hsecond using 1 <;> congr 2 <;> ring

/-- Actual D-star strong-screen deletion uniformly throughout a growing
noncentral frequency window, with its initial corridor already discharged. -/
theorem candidate_exists_growingHeight_DStar_deletion_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ start M : ℕ, J ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      ∀ N a : ℕ, 3 ≤ a → ∀ s : Finset ℕ,
      (∀ j ∈ s, a ≤ j ∧ j < N) → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ W : ℝ, 1 ≤ W →
      (∫ ω in candidateCovarianceDStarEvent start N t W \ candidateCovarianceStrongScreenEvent start t W s,
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y *
        (candidateEulerDeletionPrefactor C
          (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 7 * Real.log W)
          (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 1013 * Real.log W) *
          (2 * Real.sqrt (N : ℝ) / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) +
          (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start)) := by
  obtain ⟨C, hC, J, hJ⟩ := candidate_exists_growingHeight_eulerWeighted_strongBarrier_deletion_le
  refine ⟨C, hC, J, ?_⟩
  intro start M hstart hM N a ha s hs y hy t htlo hthi W hW
  have hlogW := Real.log_nonneg hW
  have hlogB := Real.log_nonneg (Problem520.one_le_log_harperBlockEndpoint start)
  exact (screen_mass_le_range y start N hy t W hW s (fun j hj => (hs j hj).2.le)).trans
    (hJ start M hstart hM N a ha s hs y hy t htlo hthi _ _ (by positivity) (by positivity))

/-- Actual D-star strong-screen deletion on every shrinking central band,
with the explicit absolute-plus-band-depth initial shift. -/
theorem candidate_exists_centralBand_DStar_deletion_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start →
      ∀ N a : ℕ, 3 ≤ a → ∀ s : Finset ℕ,
      (∀ j ∈ s, a ≤ j ∧ j < N) → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ t : ℝ, (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ (1 / 2 : ℝ) ^ d →
      ∀ W : ℝ, 1 ≤ W →
      (∫ ω in candidateCovarianceDStarEvent start N t W \ candidateCovarianceStrongScreenEvent start t W s,
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y *
        (candidateEulerDeletionPrefactor C
          (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 7 * Real.log W)
          (Real.log (Real.log (Problem520.harperBlockEndpoint start : ℝ)) + 1013 * Real.log W) *
          (2 * Real.sqrt (N : ℝ) / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) +
          (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start)) := by
  obtain ⟨C, hC, J, hJ⟩ := candidate_exists_centralBand_eulerWeighted_strongBarrier_deletion_le
  refine ⟨C, hC, J, ?_⟩
  intro d start hstart N a ha s hs y hy t htlo hthi W hW
  have hlogW := Real.log_nonneg hW
  have hlogB := Real.log_nonneg (Problem520.one_le_log_harperBlockEndpoint start)
  exact (screen_mass_le_range y start N hy t W hW s (fun j hj => (hs j hj).2.le)).trans
    (hJ d start hstart N a ha s hs y hy t htlo hthi _ _ (by positivity) (by positivity))


/-- The literal D-star screen is jointly measurable in the height and the
infinite prime signs, so it can be inserted into the covariance integral. -/
theorem candidate_measurableSet_covarianceDStar_joint (start N : ℕ) (W : ℝ) :
    MeasurableSet {z : ℝ × Problem520.Omega | z.2 ∈ candidateCovarianceDStarEvent start N z.1 W} := by
  have heq : {z : ℝ × Problem520.Omega | z.2 ∈ candidateCovarianceDStarEvent start N z.1 W} =
      ⋂ j : Fin (N + 1), {z : ℝ × Problem520.Omega |
        W⁻¹ ≤ Real.sqrt (Problem520.harperEulerDensity
          (Problem520.harperBlockEndpoint (start + j.val)) z.2 z.1) ∧
        Real.sqrt (Problem520.harperEulerDensity
          (Problem520.harperBlockEndpoint (start + j.val)) z.2 z.1) ≤
        Real.log (Problem520.harperBlockEndpoint (start + j.val) : ℝ) * W ^ 6} := by
    ext z
    simp [candidateCovarianceDStarEvent]
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  have hm := (Problem520.measurable_harperEulerDensity_joint
    (Problem520.harperBlockEndpoint (start + j.val))).sqrt
  exact (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)

/-- The selected strong screen is jointly measurable without restrictions
on its numerical parameters. -/
theorem candidate_measurableSet_covarianceStrongScreen_joint
    (start : ℕ) (W : ℝ) (s : Finset ℕ) :
    MeasurableSet {z : ℝ × Problem520.Omega |
      z.2 ∈ candidateCovarianceStrongScreenEvent start z.1 W s} := by
  have heq : {z : ℝ × Problem520.Omega |
      z.2 ∈ candidateCovarianceStrongScreenEvent start z.1 W s} =
      ⋂ j ∈ s, {z : ℝ × Problem520.Omega |
        Real.sqrt (Problem520.harperEulerDensity
          (Problem520.harperBlockEndpoint (start + j)) z.2 z.1) ≤
        Real.log (Problem520.harperBlockEndpoint (start + j) : ℝ) / W ^ 1000} := by
    ext z
    simp [candidateCovarianceStrongScreenEvent]
  rw [heq]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro hj
  exact measurableSet_le
    ((Problem520.measurable_harperEulerDensity_joint
      (Problem520.harperBlockEndpoint (start + j))).sqrt) measurable_const

end

end Erdos.Problem1144
