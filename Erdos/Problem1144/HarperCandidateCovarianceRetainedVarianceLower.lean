import Erdos.Problem1144.HarperCandidateCovarianceRetainedVariance

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144

/-- The proved squarefree variance probability survives on the actual retained
Euler kernels, with the explicit mesh and common-error Markov losses. The
white lower-probability input is instantiated, not assumed by the caller. -/
theorem candidate_exists_retainedWhite_variance_lower_probability :
    ∃ delta : ℝ, 0 < delta ∧ ∀ α β : ℝ, 1 < α → α ≤ 2 → α ≤ β →
      ∀ (q : Finset ℕ) (η : q → Bool), ∃ v > 0,
        ∀ᶠ T : ℝ in atTop, ∀ n : ℕ, ∀ u : Fin n → ℝ,
          (∀ i, u i ∈ Icc (α * T) (β * T)) →
          ∀ y start N depth M : ℕ, ∀ W : ℝ, ∀ s : Finset ℕ,
          ∀ H B : ℝ, (M : ℝ) ≤ H → 0 < H →
          (∀ i, u i ≤ B) → (∀ i, ⌊Real.exp (u i - T)⌋₊ ≤ y) →
          let vT := v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)
          delta - (candidateCylinderLaw q η).real
              (candidateCovarianceCommonMeshEvent start N M W)ᶜ -
            (8 / vT) *
              ((∫ ω, candidateCovarianceRetainedError y start N depth M W T s ω ∂mu) +
                ∫ ω, candidateEulerBandWhiteTotalError y u H T B ω ∂mu) /
                mu.real (candidateCylinder q η) ≤
            (candidateCylinderLaw q η).real
              (candidateRetainedWhiteVarianceFloor y start N depth M W s u T B (vT / 4)) := by
  obtain ⟨delta, hdelta, hvar⟩ := candidate_exists_squarefree_white_variance_lower_probability
  refine ⟨delta, hdelta, ?_⟩
  intro α β hα hα2 hαβ q η
  obtain ⟨v, hv, hvar⟩ := hvar α β hα hα2 hαβ q η
  refine ⟨v, hv, ?_⟩
  filter_upwards [hvar, eventually_ge_atTop (1 : ℝ)] with T hvar hT
  intro n u hpoints y start N depth M W s H B hH hH0 hu hy
  have hvT : 0 < v * (1 + Real.log T) ^ (-(1 : ℝ) / 2) :=
    mul_pos hv (Real.rpow_pos_of_pos (by linarith [Real.log_nonneg hT]) _)
  have h := candidate_retainedWhiteVariance_probability_ge q η y start N depth M W s u
    hH hH0 (by linarith : 0 < T) B hu hy hvT
  have hp := hvar n u hpoints
  dsimp only
  linarith

end Erdos.Problem1144
