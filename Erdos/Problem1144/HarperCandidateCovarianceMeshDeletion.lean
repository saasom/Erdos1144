import Erdos.Problem1144.HarperCandidateCovarianceMesh
import Erdos.Problem1144.HarperCandidateCovarianceMeshRatio

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

private theorem lower_failure_charge {x d W : ℝ} (hx : 0 ≤ x) (hd : 0 < d) (hW : 0 < W)
    (hbad : Real.sqrt d < W⁻¹) : x ≤ W⁻¹ ^ 2 * (x / d) := by
  have hs := Real.sq_sqrt hd.le
  have hsp := Real.sqrt_nonneg d
  have hWinv := inv_pos.mpr hW
  have hdW : d ≤ W⁻¹ ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hdW (div_nonneg hx hd.le)
  have heq : x / d * d = x := div_mul_cancel₀ x hd.ne'
  nlinarith

private theorem upper_failure_charge {x d e L W : ℝ}
    (hx : 0 ≤ x) (hd : 0 < d) (he : 0 < e) (hL : 0 < L) (hW : 0 < W)
    (hmesh : Real.sqrt e ≤ L * W ^ 5) (hbad : L * W ^ 6 < Real.sqrt d) :
    x ≤ W⁻¹ ^ 2 * (x * (d / e)) := by
  have heS := Real.sq_sqrt he.le
  have hdS := Real.sq_sqrt hd.le
  have heP := Real.sqrt_nonneg e
  have hdP := Real.sqrt_nonneg d
  have hmeshSq : e ≤ (L * W ^ 5) ^ 2 := by nlinarith [mul_pos hL (pow_pos hW 5)]
  have hbadSq : (L * W ^ 6) ^ 2 ≤ d := by nlinarith [mul_pos hL (pow_pos hW 6)]
  have heD : W ^ 2 * e ≤ d := by
    calc
      _ ≤ W ^ 2 * (L * W ^ 5) ^ 2 := mul_le_mul_of_nonneg_left hmeshSq (sq_nonneg W)
      _ = (L * W ^ 6) ^ 2 := by ring
      _ ≤ d := hbadSq
  have hratio : W ^ 2 ≤ d / e := (le_div_iff₀ he).mpr heD
  have hh := mul_le_mul_of_nonneg_left hratio (mul_nonneg (sq_nonneg W⁻¹) hx)
  have heq : W⁻¹ ^ 2 * x * W ^ 2 = x := by field_simp
  nlinarith

/-- The actual mesh-to-height loss for Harper's D and D-star events.
The bound is uniform in the height, including the growing and central
windows; the only cutoff condition is that every screened prefix is present. -/
theorem candidate_covarianceMesh_DStar_weighted_deletion_le
    (start N y : ℕ) (hy : Problem520.harperBlockEndpoint (start + N) ≤ y)
    (t W : ℝ) (hW : 0 < W) :
    (∫ ω in candidateCovarianceMeshEvent start N t W \
      candidateCovarianceDStarEvent start N t W,
      Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
    Problem520.primeEnergyNormalizer y *
      (Real.exp (16 * (1 + (Real.log 4 + 4) / Real.log 2)) + 1) *
      (N + 1 : ℕ) / W ^ 2 := by
  let B : Fin (N + 1) → ℕ := fun j => Problem520.harperBlockEndpoint (start + j.val)
  let u : Fin (N + 1) → ℝ := fun j => candidateCovarianceMeshPoint (start + j.val) t
  let R : Fin (N + 1) → Problem520.Omega → ℝ := fun j ω =>
    Problem520.harperEulerDensity y ω t *
      (Problem520.harperEulerDensity (B j) ω t / Problem520.harperEulerDensity (B j) ω (u j))
  let Q : Fin (N + 1) → Problem520.Omega → ℝ := fun j ω =>
    Problem520.harperEulerDensity y ω t / Problem520.harperEulerDensity (B j) ω t
  let S := candidateCovarianceMeshEvent start N t W \ candidateCovarianceDStarEvent start N t W
  let C := Real.exp (16 * (1 + (Real.log 4 + 4) / Real.log 2))
  have hBy (j : Fin (N + 1)) : B j ≤ y :=
    (Problem520.strictMono_harperBlockEndpoint.monotone (by omega)).trans hy
  have hB2 (j : Fin (N + 1)) : 2 ≤ B j := by
    dsimp only [B]
    have := Problem520.harperBlockEndpoint_ge_sixteen (start + j.val)
    omega
  have hR (j : Fin (N + 1)) : Integrable (R j) Problem520.μ :=
    candidate_integrable_weighted_eulerRatio (hBy j) t (u j)
  have hQ (j : Fin (N + 1)) : Integrable (Q j) Problem520.μ :=
    candidate_integrable_eulerDensity_div_prefix (hBy j) t
  have hRbound (j : Fin (N + 1)) : (∫ ω, R j ω ∂Problem520.μ) ≤ Problem520.primeEnergyNormalizer y * C :=
    candidate_integral_weighted_eulerRatio_local_le (hB2 j) (hBy j)
      (candidate_covarianceMeshPoint_close (start + j.val) t)
  have hQbound (j : Fin (N + 1)) : (∫ ω, Q j ω ∂Problem520.μ) ≤ Problem520.primeEnergyNormalizer y :=
    candidate_integral_eulerDensity_div_prefix_le (hBy j) t
  have hnonneg (j : Fin (N + 1)) (ω : Problem520.Omega) : 0 ≤ R j ω ∧ 0 ≤ Q j ω := by
    dsimp only [R, Q]
    constructor
    · exact mul_nonneg (Problem520.harperEulerDensity_nonneg _ _ _)
        (div_nonneg (Problem520.harperEulerDensity_nonneg _ _ _) (Problem520.harperEulerDensity_nonneg _ _ _))
    · exact div_nonneg (Problem520.harperEulerDensity_nonneg _ _ _) (Problem520.harperEulerDensity_nonneg _ _ _)
  have hpair : Measurable (fun ω : Problem520.Omega => (t, ω)) :=
    measurable_const.prodMk measurable_id
  have hmD := (candidate_measurableSet_covarianceMesh_joint start N W).preimage hpair
  have hmStar := (candidate_measurableSet_covarianceDStar_joint start N W).preimage hpair
  have hS : MeasurableSet S := hmD.diff hmStar
  have hpoint (ω : Problem520.Omega) :
      S.indicator (fun ω => Problem520.harperEulerDensity y ω t) ω ≤
        W⁻¹ ^ 2 * ∑ j : Fin (N + 1), (R j ω + Q j ω) := by
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      obtain ⟨hD, hnot⟩ := hω
      change ¬ (∀ j : Fin (N + 1), _ ∧ _) at hnot
      simp only [not_forall, not_and_or, not_le] at hnot
      obtain ⟨j, hbad⟩ := hnot
      have hsum : R j ω + Q j ω ≤ ∑ k : Fin (N + 1), (R k ω + Q k ω) :=
        Finset.single_le_sum (fun k _ => add_nonneg (hnonneg k ω).1 (hnonneg k ω).2) (Finset.mem_univ j)
      have hcharge : Problem520.harperEulerDensity y ω t ≤ W⁻¹ ^ 2 * (R j ω + Q j ω) := by
        rcases hbad with hlower | hupper
        · have h := lower_failure_charge (Problem520.harperEulerDensity_nonneg y ω t)
            (Problem520.harperEulerDensity_pos _ _ _) hW hlower
          exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hnonneg j ω).1) (sq_nonneg _))
        · have h := upper_failure_charge (Problem520.harperEulerDensity_nonneg y ω t)
            (Problem520.harperEulerDensity_pos _ _ _) (Problem520.harperEulerDensity_pos _ _ _)
            (lt_of_lt_of_le zero_lt_one (Problem520.one_le_log_harperBlockEndpoint _)) hW (hD j) hupper
          exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hnonneg j ω).2) (sq_nonneg _))
      exact hcharge.trans (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
    · rw [Set.indicator_of_notMem hω]
      exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => add_nonneg (hnonneg j ω).1 (hnonneg j ω).2)
  have hsumInt : Integrable (fun ω => ∑ j : Fin (N + 1), (R j ω + Q j ω)) Problem520.μ :=
    integrable_finset_sum _ fun j _ => (hR j).add (hQ j)
  rw [← integral_indicator hS]
  have hmono := integral_mono ((Problem520.integrable_harperEulerDensity y t).indicator hS)
    (hsumInt.const_mul (W⁻¹ ^ 2)) hpoint
  apply hmono.trans
  rw [integral_const_mul, integral_finset_sum Finset.univ
    (f := fun j ω => R j ω + Q j ω) (fun j _ => (hR j).add (hQ j))]
  calc
    _ ≤ W⁻¹ ^ 2 * ∑ _j : Fin (N + 1),
        (Problem520.primeEnergyNormalizer y * C + Problem520.primeEnergyNormalizer y) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro j hj
      rw [integral_add (hR j) (hQ j)]
      exact add_le_add (hRbound j) (hQbound j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp only [C]; ring

end Erdos.Problem1144
