import Erdos.Problem1144.HarperCandidateCovarianceResonanceGapIntegral
import Erdos.Problem1144.HarperCandidateCovarianceGapExpectedIntegral

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-- The literal strong-screen gap profile satisfies the weighted resonant
box bound. The nonsingular clipped envelope includes microscopic full-prefix
removals, and the last coordinate contributes exactly the endpoint length.
All logarithmic masses and powers of the screen parameter are explicit. -/
theorem candidate_integral_screenedGapBox_resonance_le
    (start stop a : ℕ) {n : ℕ} (hn : 1 ≤ n)
    (signs : Fin (n + 1) → ℤ) (hsigns : ∀ i, signs i = 1 ∨ signs i = -1)
    (k : ℕ) (hk : 2 * k ≤ n + 1)
    {M ε W : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hW : 1 ≤ W) (m : ℤ) :
    let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
    let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
    let δ := Problem520.invLog (Problem520.harperBlockEndpoint (a - 1))
    let U := A * M + 3 * Real.log (1 + L * M)
    (∫ g in Set.univ.pi (fun _ : Fin (n + 1) => Icc (0 : ℝ) M),
      {g : Fin (n + 1) → ℝ |
        |(∑ i, (candidateGapCoefficients n signs i : ℝ) * g i) - (m : ℝ)| ≤ ε}.indicator
        (candidateCovarianceGapProductProfile start stop a W n) g) ≤
      W ^ (12 * n) * M *
        (U ^ n / W ^ (2012 * k) + 2 * ε * n * (A + 2 / δ) * U ^ (n - 1)) := by
  let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
  let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
  let δ := Problem520.invLog (Problem520.harperBlockEndpoint (a - 1))
  let U := A * M + 3 * Real.log (1 + L * M)
  let G := candidateCovarianceGapEnvelope start stop
  have hA : 0 ≤ A := (Problem520.one_le_log_harperBlockEndpoint start).trans' (by norm_num)
  have hδ : 0 < δ := Problem520.invLog_harperBlockEndpoint_pos (a - 1)
  have hGn : ∀ x, 0 ≤ G x := candidate_gapEnvelope_nonneg start stop
  have hGU : (∫ x in Icc (0 : ℝ) M, G x) ≤ U := candidate_integral_gapEnvelope_le start stop hM
  have hU : 0 ≤ U := (integral_nonneg hGn).trans hGU
  have hK : 0 ≤ A + 2 / δ := add_nonneg hA (by positivity)
  have hGK (x : ℝ) (_hx : x ∈ Icc (0 : ℝ) M) (hd : δ ≤ x) : G x ≤ A + 2 / δ := by
    exact (candidate_gapEnvelope_le_reciprocal start stop (hδ.trans_le hd)).trans
      (add_le_add (le_refl A) (div_le_div_of_nonneg_left (by norm_num) hδ hd))
  have h := candidate_integral_gapBox_resonance_le hn signs hsigns k hk hM hε hK hU hW m G
    (candidate_continuous_gapEnvelope start stop).measurable
    (candidate_continuous_gapEnvelope start stop).integrableOn_Icc hGn hGK hGU
  dsimp only
  change (∫ g, _ ∂(Measure.pi (fun _ : Fin (n + 1) => (volume : Measure ℝ))).restrict
    (Set.univ.pi (fun _ : Fin (n + 1) => Icc (0 : ℝ) M))) ≤ _
  rw [Measure.restrict_pi_pi]
  exact h

end Erdos.Problem1144
