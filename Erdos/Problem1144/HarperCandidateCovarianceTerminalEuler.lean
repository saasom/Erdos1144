import Erdos.Problem1144.HarperCandidateCovarianceTerminalTilted

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-- Literal terminal-strip cost after the bounded Euler-log approximation. -/
def candidateEulerTerminalDeletionPrefactor (C x r : ℝ) : ℝ :=
  Real.exp 2 * 8192 * (x + C + 4) * (r + 2 * C + 6) * (r + 2 * C + 4)

theorem candidate_eulerTerminalDeletionPrefactor_nonneg {C x r : ℝ}
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hr : 0 ≤ r) :
    0 ≤ candidateEulerTerminalDeletionPrefactor C x r := by
  unfold candidateEulerTerminalDeletionPrefactor
  positivity

theorem candidate_eulerTerminalDeletionPrefactor_mono {C D x r : ℝ}
    (hC : 0 ≤ C) (hCD : C ≤ D) (hx : 0 ≤ x) (hr : 0 ≤ r) :
    candidateEulerTerminalDeletionPrefactor C x r ≤ candidateEulerTerminalDeletionPrefactor D x r := by
  have hD : 0 ≤ D := hC.trans hCD
  unfold candidateEulerTerminalDeletionPrefactor
  gcongr

private theorem euler_internalBarrier_subset
    (y start N j : ℕ) (t x r C : ℝ)
    (hclose : ∀ η : Problem520.HarperPrimeCube y, ∀ k : Fin N,
      |candidateEulerPrefixLog y start (k.val + 1) t η -
        Problem520.harperPathPartialSum
          (Problem520.harperScheduledCenteredBlockVectorVarying y start N t (fun _ => t) η) k| ≤ C) :
    ∃ lower : Fin N → ℝ,
      (∀ k, k.val + 1 = j → (x + C) - (r + 2 * C) ≤ lower k) ∧
      candidateEulerInternalBarrierEvent y start N j t x r ⊆
        (Problem520.harperScheduledCenteredBlockVectorVarying y start N t (fun _ => t)) ⁻¹'
          Problem520.harperPartialSumBarrierSet lower (fun _ => x + C) := by
  classical
  let path := Problem520.harperScheduledCenteredBlockVectorVarying y start N t (fun _ => t)
  let L : Fin N → ℝ := fun k =>
    -∑ η : Problem520.HarperPrimeCube y, |Problem520.harperPathPartialSum (path η) k|
  let lower : Fin N → ℝ := fun k => if k.val + 1 = j then x - r - C else L k
  refine ⟨lower, ?_, ?_⟩
  · intro k hk
    dsimp [lower]
    rw [if_pos hk]
    linarith
  · intro η hη
    apply Problem520.mem_harperPartialSumBarrierSet.mpr
    intro k
    have hc := abs_le.mp (hclose η k)
    have hu := hη.1 k
    refine ⟨?_, by linarith [hc.1]⟩
    dsimp [lower]
    split_ifs with hk
    · have hl := hη.2
      rw [hk] at hc
      linarith [hc.2]
    · have habs : |Problem520.harperPathPartialSum (path η) k| ≤
          ∑ ζ : Problem520.HarperPrimeCube y, |Problem520.harperPathPartialSum (path ζ) k| :=
        Finset.single_le_sum (f := fun ζ : Problem520.HarperPrimeCube y =>
          |Problem520.harperPathPartialSum (path ζ) k|)
          (fun ζ _ => abs_nonneg _) (Finset.mem_univ η)
      dsimp [L]
      exact (neg_le_neg habs).trans (neg_abs_le _)


theorem candidate_exists_growingHeight_euler_terminalBarrier_probability_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ start M : ℕ, J ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      ∀ n : ℕ, 3 ≤ n → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + n) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ x r : ℝ, 0 ≤ x → 0 ≤ r →
      (Problem520.harperTiltedCubeLaw y t).real
        (candidateEulerInternalBarrierEvent y start n n t x r) ≤
      candidateEulerTerminalDeletionPrefactor C x r /
        (Real.sqrt ((n / 3 : ℕ) : ℝ)) ^ 3 +
          64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨C, hC, Jc, hc⟩ := candidate_exists_growingHeight_eulerPrefixLog_centered_close
  obtain ⟨Jp, hp⟩ := candidate_exists_growingHeight_tilted_terminalBarrier_probability_le_all_lengths
  refine ⟨C, hC, max Jc Jp, ?_⟩
  intro start M hstart hM n hn y hy t htlo hthi x r hx hr
  obtain ⟨lower, hlower, hsubset⟩ := euler_internalBarrier_subset y start n n t x r C
    (hc start n M y (by omega) hM hy t htlo hthi)
  have h := hp start M (by omega) hM n hn y hy t htlo hthi (fun _ => t)
    (by intro i; simp) (x + C) (r + 2 * C) (by positivity) (by positivity)
    lower (fun _ => x + C) (fun _ => le_rfl) hlower
  refine (measureReal_mono hsubset).trans ?_
  convert h using 1 <;> unfold candidateEulerTerminalDeletionPrefactor <;> ring


theorem candidate_exists_centralBand_euler_terminalBarrier_probability_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start →
      ∀ n : ℕ, 3 ≤ n → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + n) ≤ y →
      ∀ t : ℝ, (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ (1 / 2 : ℝ) ^ d →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r →
      (Problem520.harperTiltedCubeLaw y t).real
        (candidateEulerInternalBarrierEvent y start n n t x r) ≤
      candidateEulerTerminalDeletionPrefactor C x r /
        (Real.sqrt ((n / 3 : ℕ) : ℝ)) ^ 3 +
          64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨C, hC, Jc, _, hc⟩ := candidate_exists_eulerPrefixLog_centered_close
  obtain ⟨Jp, hp⟩ := candidate_exists_centralBand_tilted_terminalBarrier_probability_le_all_lengths
  refine ⟨C, hC, max Jc Jp, ?_⟩
  intro d start hstart n hn y hy t htlo hthi x r hx hr
  obtain ⟨lower, hlower, hsubset⟩ := euler_internalBarrier_subset
    y start n n t x r C (hc d start n y (by omega) hy t htlo hthi)
  have h := hp d start (by omega) n hn y hy t htlo hthi (fun _ => t)
    (by intro i; simp) (x + C) (r + 2 * C) (by positivity) (by positivity)
    lower (fun _ => x + C) (fun _ => le_rfl) hlower
  refine (measureReal_mono hsubset).trans ?_
  convert h using 1 <;> unfold candidateEulerTerminalDeletionPrefactor <;> ring




end

end Erdos.Problem1144
