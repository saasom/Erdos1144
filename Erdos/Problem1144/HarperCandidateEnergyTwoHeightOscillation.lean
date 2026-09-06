import Erdos.Problem520.HarperOscillatoryPrime

open Finset Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144

private theorem candidate_sum_Ioc_weighted_by_parts
    (f w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    (∑ k ∈ Ioc A B, w k * f k) =
      w (B + 1) * (∑ k ∈ Ioc A B, f k) +
        ∑ k ∈ Ioc A B, (w k - w (k + 1)) * (∑ i ∈ Ioc A k, f i) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    simp only [Finset.sum_Ioc_succ_top hAB]
    rw [ih]
    ring

private theorem candidate_sum_Ioc_weight_differences
    (w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    w (B + 1) + (∑ k ∈ Ioc A B, (w k - w (k + 1))) = w (A + 1) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [Finset.sum_Ioc_succ_top hAB]
    linarith

private theorem candidate_abs_weighted_sum_le_partial_bound
    (f w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) {K : ℝ}
    (hK : 0 ≤ K) (hpartial : ∀ N ∈ Icc A B, |∑ k ∈ Ioc A N, f k| ≤ K)
    (hw : 0 ≤ w (B + 1)) (hfirst : w (A + 1) ≤ 1)
    (hmono : ∀ k ∈ Ioc A B, w (k + 1) ≤ w k) :
    |∑ k ∈ Ioc A B, w k * f k| ≤ K := by
  rw [candidate_sum_Ioc_weighted_by_parts f w hAB]
  calc
    _ ≤ |w (B + 1) * (∑ k ∈ Ioc A B, f k)| +
        ∑ k ∈ Ioc A B, |(w k - w (k + 1)) * (∑ i ∈ Ioc A k, f i)| :=
      (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ w (B + 1) * K + ∑ k ∈ Ioc A B, (w k - w (k + 1)) * K := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hw]
        exact mul_le_mul_of_nonneg_left (hpartial B (by simp [hAB])) hw
      · apply Finset.sum_le_sum
        intro k hk
        have hnonneg := sub_nonneg.mpr (hmono k hk)
        rw [abs_mul, abs_of_nonneg hnonneg]
        exact mul_le_mul_of_nonneg_left
          (hpartial k (by rcases mem_Ioc.mp hk with ⟨hAk, hkB⟩; simp [hAk.le, hkB])) hnonneg
    _ = w (A + 1) * K := by
      rw [← Finset.sum_mul, ← add_mul, candidate_sum_Ioc_weight_differences w hAB]
    _ ≤ K := mul_le_of_le_one_left hK hfirst

/-- Radial damping preserves a uniform critical prime partial-sum bound.
This finite Abel estimate has no dependence on the damping parameter. -/
theorem candidate_rankinPrimeOscillation_le_of_critical_partials
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) {a τ K : ℝ} (ha : 0 ≤ a)
    (hK : 0 ≤ K)
    (hpartial : ∀ N ∈ Icc A B,
      |∑ p ∈ (Ioc A N).filter Nat.Prime,
        Real.cos (τ * Real.log (p : ℝ)) / p| ≤ K) :
    |∑ p ∈ (Ioc A B).filter Nat.Prime,
      Real.cos (τ * Real.log (p : ℝ)) / p * (p : ℝ) ^ (-a)| ≤ K := by
  let f : ℕ → ℝ := fun p => if p.Prime then Real.cos (τ * Real.log (p : ℝ)) / p else 0
  let w : ℕ → ℝ := fun p => (p : ℝ) ^ (-a)
  have hbound := candidate_abs_weighted_sum_le_partial_bound f w hAB hK
    (fun N hN => by simpa only [f, ← Finset.sum_filter] using hpartial N hN)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ A + 1 by omega))
      (neg_nonpos.mpr ha))
    (fun k hk => Real.rpow_le_rpow_of_nonpos
      (by exact_mod_cast (show 0 < k by have := (mem_Ioc.mp hk).1; omega))
      (by exact_mod_cast Nat.le_succ k) (neg_nonpos.mpr ha))
  convert hbound using 1
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  dsimp only [f, w]
  split_ifs <;> ring

/-- Strong-PNT prime cancellation survives every nonnegative Rankin shift
with the same explicit bound. -/
theorem candidate_rankinPrimeOscillation_le_of_thetaError
    {A B : ℕ} (hA : 2 ≤ A) (hAB : A ≤ B) {a τ δ : ℝ}
    (ha : 0 ≤ a) (hτ : τ ≠ 0) (hδ : 0 ≤ δ)
    (herror : ∀ x ∈ Set.Icc (A : ℝ) B, |Problem520.thetaError x| ≤ δ * x) :
    |∑ p ∈ (Ioc A B).filter Nat.Prime,
      Real.cos (τ * Real.log (p : ℝ)) / p * (p : ℝ) ^ (-a)| ≤
      (2 / |τ| + 2 * δ + δ * (1 + |τ|) * Real.log ((B : ℝ) / A)) *
        Problem520.invLog A := by
  have hAp : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hratio : 1 ≤ (B : ℝ) / A := (le_div_iff₀ hAp).mpr (by simpa using (show (A : ℝ) ≤ B by exact_mod_cast hAB))
  apply candidate_rankinPrimeOscillation_le_of_critical_partials (by omega) hAB ha
  · have hlog := Real.log_nonneg hratio
    have hinv := (Problem520.invLog_pos (x := (A : ℝ)) (by exact_mod_cast (show 1 < A by omega))).le
    positivity
  · intro N hN
    obtain ⟨hAN, hNB⟩ := mem_Icc.mp hN
    have h := Problem520.abs_primeOscillation_le_of_thetaError hA hAN hτ hδ
      (fun x hx => herror x ⟨hx.1, hx.2.trans (by exact_mod_cast hNB)⟩)
    refine h.trans ?_
    have hNp : (0 : ℝ) < N := hAp.trans_le (by exact_mod_cast hAN)
    have hlog : Real.log ((N : ℝ) / A) ≤ Real.log ((B : ℝ) / A) :=
      Real.log_le_log (div_pos hNp hAp)
        (div_le_div_of_nonneg_right (by exact_mod_cast hNB) hAp.le)
    have hinv := (Problem520.invLog_pos (x := (A : ℝ)) (by exact_mod_cast (show 1 < A by omega))).le
    gcongr

/-- Unconditional arithmetic cancellation on every prime block, uniform in
the real nonnegative Rankin shift. -/
theorem candidate_exists_mediumPNT_rankinPrimeOscillation_bound :
    ∃ c > 0, ∃ C > 0, ∃ X₀ : ℝ, 2 ≤ X₀ ∧
      ∀ A B : ℕ, X₀ ≤ A → 2 ≤ A → A ≤ B →
        ∀ a τ : ℝ, 0 ≤ a → τ ≠ 0 →
          |∑ p ∈ (Ioc A B).filter Nat.Prime,
            Real.cos (τ * Real.log (p : ℝ)) / p * (p : ℝ) ^ (-a)| ≤
            (2 / |τ| + 2 * Problem520.mediumThetaBlockDelta c C A B +
              Problem520.mediumThetaBlockDelta c C A B * (1 + |τ|) *
                Real.log ((B : ℝ) / A)) * Problem520.invLog A := by
  obtain ⟨c, hc, C, hC, X₀, hX₀, htheta⟩ := Problem520.exists_mediumThetaError
  refine ⟨c, hc, C, hC, X₀, hX₀, ?_⟩
  intro A B hX₀A hA hAB a τ ha hτ
  have hδ : 0 ≤ Problem520.mediumThetaBlockDelta c C A B := by
    unfold Problem520.mediumThetaBlockDelta
    have hAp : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
    have hlog : 0 ≤ Real.log (B : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
    positivity
  exact candidate_rankinPrimeOscillation_le_of_thetaError hA hAB ha hτ hδ
    (fun x hx => Problem520.thetaError_le_mediumThetaBlockDelta
      hc hC.le htheta hA hAB hX₀A hx)

end Erdos.Problem1144
