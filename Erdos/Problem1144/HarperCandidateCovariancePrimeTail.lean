import Erdos.Problem1144.HarperCandidateCovarianceGrowingHeight
import Mathlib.Algebra.BigOperators.Intervals

open Finset Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

/-- Uniform cancellation on every final partial prime block, including
arbitrarily small nonzero frequencies. The strong-PNT error is summable
over later blocks and uniform throughout the supported height window. -/
theorem candidate_exists_growingHeight_primeBlockPartial_bound :
    ∃ K > 0, ∃ J : ℕ, ∀ start j y : ℕ, J ≤ start → start ≤ j →
      Problem520.harperBlockEndpoint j ≤ y →
      y ≤ Problem520.harperBlockEndpoint (j + 1) →
      ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ candidateCovarianceHeightWindow start →
        |∑ p ∈ (Ioc (Problem520.harperBlockEndpoint j) y).filter Nat.Prime,
          Real.cos (τ * Real.log (p : ℝ)) / p| ≤
          (2 / |τ|) * Problem520.invLog (Problem520.harperBlockEndpoint j) +
            K * Problem520.invLog (Problem520.harperBlockEndpoint j) ^ 2 := by
  obtain ⟨c, hc, C, hC, X, hX2, htheta⟩ := Problem520.exists_mediumThetaError
  have hBX := ((tendsto_natCast_atTop_atTop.comp
    Problem520.strictMono_harperBlockEndpoint.tendsto_atTop).eventually_ge_atTop X)
  obtain ⟨JX, hJX⟩ := eventually_atTop.mp hBX
  obtain ⟨Jt, hJt⟩ := eventually_atTop.mp
    (candidate_eventually_heightWindow_mul_theta_le hc hC.le)
  refine ⟨4 * (C + 1), by positivity, max JX Jt, ?_⟩
  intro start j y hstart hsj hAy hyB τ hτ hτwin
  let A := Problem520.harperBlockEndpoint j
  let B := Problem520.harperBlockEndpoint (j + 1)
  let δ := Problem520.harperScheduledThetaEnvelope c C j
  let ell := Problem520.invLog A
  have hA2 : 2 ≤ A := by have := Problem520.harperBlockEndpoint_ge_sixteen j; omega
  have hAB : A ≤ B := Problem520.monotone_harperBlockEndpoint (by omega)
  have hAp : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hδ : 0 ≤ δ := Problem520.harperScheduledThetaEnvelope_nonneg hC.le j
  have hell : 0 ≤ ell := (Problem520.invLog_harperBlockEndpoint_pos j).le
  have hell1 : ell ≤ 1 := Problem520.invLog_harperBlockEndpoint_le_one j
  have hθ : ∀ x ∈ Set.Icc (A : ℝ) y, |Problem520.thetaError x| ≤ δ * x := by
    intro x hx
    exact Problem520.thetaError_le_mediumThetaBlockDelta hc hC.le htheta hA2 hAB
      (hJX j (by omega)) ⟨hx.1, hx.2.trans (by exact_mod_cast hyB)⟩
  have hraw := Problem520.abs_primeOscillation_le_of_thetaError hA2 hAy hτ hδ hθ
  have hratio : (B : ℝ) / A = A := by
    dsimp only [B, A]
    rw [Problem520.harperBlockEndpoint_succ]
    push_cast
    field_simp
  have hlogle : Real.log ((y : ℝ) / A) ≤ Real.log (A : ℝ) := by
    calc
      _ ≤ Real.log ((B : ℝ) / A) :=
        Real.log_le_log (div_pos (hAp.trans_le (by exact_mod_cast hAy)) hAp)
          (div_le_div_of_nonneg_right (by exact_mod_cast hyB) hAp.le)
      _ = _ := congrArg Real.log hratio
  have hcancel : Real.log (A : ℝ) * ell = 1 :=
    mul_inv_cancel₀ (lt_of_lt_of_le zero_lt_one
      (Problem520.one_le_log_harperBlockEndpoint j)).ne'
  have hwin1 : 1 ≤ candidateCovarianceHeightWindow j := by
    unfold candidateCovarianceHeightWindow
    exact Real.one_le_exp (by positivity)
  have hτj : |τ| ≤ candidateCovarianceHeightWindow j :=
    hτwin.trans (candidateCovarianceHeightWindow_monotone hsj)
  have hcoef : 2 * ell + 1 + |τ| ≤ 4 * candidateCovarianceHeightWindow j := by
    linarith
  have hθj := hJt j (by omega)
  change |∑ p ∈ (Ioc A y).filter Nat.Prime,
    Real.cos (τ * Real.log (p : ℝ)) / p| ≤ _
  calc
    _ ≤ (2 / |τ| + 2 * δ + δ * (1 + |τ|) *
        Real.log ((y : ℝ) / A)) * ell := hraw
    _ ≤ (2 / |τ| + 2 * δ + δ * (1 + |τ|) *
        Real.log (A : ℝ)) * ell := by gcongr
    _ = (2 / |τ|) * ell + 2 * δ * ell +
        δ * (1 + |τ|) * (Real.log (A : ℝ) * ell) := by ring
    _ = (2 / |τ|) * ell + δ * (2 * ell + 1 + |τ|) := by rw [hcancel]; ring
    _ ≤ (2 / |τ|) * ell + 4 * (candidateCovarianceHeightWindow j * δ) := by
      nlinarith [mul_le_mul_of_nonneg_left hcoef hδ]
    _ ≤ _ := by
      dsimp only [δ, ell, A] at *
      nlinarith [hθj]

/-- The actual prime cosine tail has a bound independent of the upper
cutoff. Exact halving of the inverse block logarithms absorbs all full
blocks and the final partial block. -/
theorem candidate_exists_growingHeight_primeTail_bound :
    ∃ C > 0, ∃ J : ℕ, ∀ start y : ℕ, J ≤ start →
      Problem520.harperBlockEndpoint start ≤ y →
      ∀ τ : ℝ, τ ≠ 0 → |τ| ≤ candidateCovarianceHeightWindow start →
        |∑ p ∈ (Ioc (Problem520.harperBlockEndpoint start) y).filter Nat.Prime,
          Real.cos (τ * Real.log (p : ℝ)) / p| ≤
          (4 / |τ|) * Problem520.invLog (Problem520.harperBlockEndpoint start) +
            C * Problem520.invLog (Problem520.harperBlockEndpoint start) ^ 2 := by
  obtain ⟨K, hK, J, hblock⟩ := candidate_exists_growingHeight_primeBlockPartial_bound
  refine ⟨2 * K, by positivity, J, ?_⟩
  intro start y hstart hy τ hτ hτwin
  let ell : ℕ → ℝ := fun j => Problem520.invLog (Problem520.harperBlockEndpoint j)
  let P : ℕ → ℝ := fun j => (4 / |τ|) * ell j + 2 * K * ell j ^ 2
  have hP0 (j : ℕ) : 0 ≤ P j := by
    have := (Problem520.invLog_harperBlockEndpoint_pos j).le
    dsimp only [P, ell]
    positivity
  have hell (j : ℕ) : ell (j + 1) = ell j / 2 := by
    dsimp only [ell]
    rw [Problem520.invLog_harperBlockEndpoint_eq,
      Problem520.invLog_harperBlockEndpoint_eq, pow_succ]
    ring
  have hstep (j : ℕ) : (2 / |τ|) * ell j + K * ell j ^ 2 + P (j + 1) ≤ P j := by
    dsimp only [P]
    rw [hell]
    simp only [div_eq_mul_inv]
    nlinarith [mul_nonneg hK.le (sq_nonneg (ell j))]
  have hpartial (j z : ℕ) (hj : start ≤ j)
      (hz : Problem520.harperBlockEndpoint j ≤ z)
      (hz' : z ≤ Problem520.harperBlockEndpoint (j + 1)) :
      |∑ p ∈ (Ioc (Problem520.harperBlockEndpoint j) z).filter Nat.Prime,
        Real.cos (τ * Real.log (p : ℝ)) / p| ≤ (2 / |τ|) * ell j + K * ell j ^ 2 :=
    hblock start j z hstart hj hz hz' τ hτ hτwin
  have htotal (n : ℕ) : ∀ j : ℕ, start ≤ j → ∀ z : ℕ,
      Problem520.harperBlockEndpoint j ≤ z →
      z ≤ Problem520.harperBlockEndpoint (j + n) →
      |∑ p ∈ (Ioc (Problem520.harperBlockEndpoint j) z).filter Nat.Prime,
        Real.cos (τ * Real.log (p : ℝ)) / p| ≤ P j := by
    induction n with
    | zero =>
        intro j hj z hz hz'
        have he : z = Problem520.harperBlockEndpoint j := by simpa using Nat.le_antisymm hz' hz
        subst z
        simpa using hP0 j
    | succ n ih =>
        intro j hj z hz hz'
        by_cases hshort : z ≤ Problem520.harperBlockEndpoint (j + 1)
        · exact (hpartial j z hj hz hshort).trans
            ((le_add_of_nonneg_right (hP0 (j + 1))).trans (hstep j))
        · have hnext : Problem520.harperBlockEndpoint (j + 1) ≤ z := by omega
          have hAB : Problem520.harperBlockEndpoint j ≤
              Problem520.harperBlockEndpoint (j + 1) :=
            Problem520.monotone_harperBlockEndpoint (by omega)
          have hrest := ih (j + 1) (by omega) z hnext (by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz')
          have hsplit : (∑ p ∈ (Ioc (Problem520.harperBlockEndpoint j) z).filter Nat.Prime,
              Real.cos (τ * Real.log (p : ℝ)) / p) =
              (∑ p ∈ (Ioc (Problem520.harperBlockEndpoint j)
                (Problem520.harperBlockEndpoint (j + 1))).filter Nat.Prime,
                Real.cos (τ * Real.log (p : ℝ)) / p) +
              (∑ p ∈ (Ioc (Problem520.harperBlockEndpoint (j + 1)) z).filter Nat.Prime,
                Real.cos (τ * Real.log (p : ℝ)) / p) := by
            simp only [Finset.sum_filter]
            exact (Finset.sum_Ioc_consecutive _ hAB hnext).symm
          rw [hsplit]
          exact (abs_add_le _ _).trans
            ((add_le_add (hpartial j _ hj hAB le_rfl) hrest).trans (hstep j))
  exact htotal y start le_rfl y hy
    ((Nat.le_add_left y start).trans (Problem520.strictMono_harperBlockEndpoint.id_le (start + y)))

end Erdos.Problem1144
