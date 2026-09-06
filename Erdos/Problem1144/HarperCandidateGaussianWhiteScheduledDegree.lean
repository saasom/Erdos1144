import Erdos.Problem1144.HarperCandidateGaussianWhiteSelected
import Erdos.Problem1144.HarperCandidateScheduleThinning
import Erdos.Problem1144.HarperCandidatePrimeWhiteComparisonCrossing

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace Erdos.Problem1144

/-- On the literal schedule and old-negative selector, only the covariance
degree event remains. The retained cardinality, variance event, Gaussian
thinning, and growing threshold criterion are all instantiated. -/
theorem candidateSchedule_exists_squarefreeWhite_retained_crossing_of_degree :
    ∃ delta : ℝ, 0 < delta ∧ ∀ α β κ ρ : ℝ,
      1 < α → α ≤ β → β < 4 / 3 → 0 < κ → 0 < ρ → ρ ≤ 1 →
      ∀ (s : Finset ℕ) (η : s → Bool), ∃ v > 0,
        ∀ a : ℝ, 0 ≤ a → a < 1 → ∀ A : ℝ, 0 ≤ A → ∀ ℓ : ℕ,
        ∀ᶠ T : ℝ in atTop, ∀ k < candidateScheduleN α β κ T,
          ∀ shift ∈ Ioc (0 : ℝ) (2 * Real.pi), ∀ b : ℝ,
          ∀ D : Set Omega, MeasurableSet D →
          let u := fun i : Fin (candidateScheduleM κ T) =>
            candidateSchedulePoint α κ T k i shift
          let J := candidateRetainedIndices
            (fun ω i => harperCandidateLogOld ω (candidateScheduleX T) (u i)) b ρ
          (∀ ω ∈ D, ∀ i ∈ J ω,
            ((J ω).filter fun j => j ≠ i ∧
              (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 2 <
                |candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T i j|).card ≤
                  ⌊T ^ a⌋₊) →
          (delta - (candidateCylinderLaw s η).real Dᶜ) / 4 ≤
            ∫ ω, candidateComparisonWhiteCrossing true u T J
              (A * Real.log (1 + Real.log T) ^ ℓ) ω ∂candidateCylinderLaw s η := by
  obtain ⟨delta, hdelta, hcross⟩ := candidate_exists_squarefreeWhite_selected_crossing_of_degree
  refine ⟨delta, hdelta, ?_⟩
  intro α β κ ρ hα hαβ hβ hκ hρ hρ1 s η
  obtain ⟨v, hv, hcross⟩ := hcross α β hα (by linarith) hαβ s η
  refine ⟨v, hv, ?_⟩
  intro a ha ha1 A hA ℓ
  let γ := (1 - a) / 2
  have hγ : 0 < γ := by dsimp only [γ]; linarith
  have haγ : a + γ < 1 := by dsimp only [γ]; linarith
  filter_upwards [hcross γ hγ A hA ℓ,
    candidateSchedule_retained_card_div_degree_ge_rpow hκ hρ hρ1 ha haγ,
    eventually_ge_atTop (1 : ℝ)] with T hcross hcard hT1
  intro k hk shift hshift b D hD
  dsimp only
  let u := fun i : Fin (candidateScheduleM κ T) =>
    candidateSchedulePoint α κ T k i shift
  let J := candidateRetainedIndices
    (fun ω i => harperCandidateLogOld ω (candidateScheduleX T) (u i)) b ρ
  intro hdegree
  have hT : 0 < T := by linarith
  have hwindow (i : Fin (candidateScheduleM κ T)) : u i ∈ Icc (α * T) (β * T) := by
    have hi := candidate_grid_point_mem_window (by positivity : 0 ≤ 2 * Real.pi)
      (candidateSchedule_cover hαβ hT.le) hk i.isLt hshift
    exact ⟨hi.1.le, hi.2⟩
  have hJ (i : Fin (candidateScheduleM κ T)) : MeasurableSet {ω | i ∈ J ω} :=
    measurableSet_mem_candidateRetainedIndices _
      (fun i => measurable_harperCandidateLogOld _ (u i)) b ρ i
  have hc := hcross _ u hwindow J hJ D hD ⌊T ^ a⌋₊ hdegree
    (fun ω _ => hcard _ b ω ⌊T ^ a⌋₊ (Nat.floor_le (Real.rpow_pos_of_pos hT _).le))
  change (delta - (candidateCylinderLaw s η).real Dᶜ) / 4 ≤
    ∫ ω, candidateComparisonWhiteCrossing true u T J
      (A * Real.log (1 + Real.log T) ^ ℓ) ω ∂candidateCylinderLaw s η
  simpa only [candidateComparisonWhiteCrossing, candidateComparisonWhite, ↓reduceIte,
    candidate_squarefreeWhiteKernel_gram_eq_whiteCovariance _ u hT] using hc

end Erdos.Problem1144
