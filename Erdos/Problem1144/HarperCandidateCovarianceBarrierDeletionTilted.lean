import Erdos.Problem1144.HarperCandidateCovarianceBarrierDeletionGaussian
import Erdos.Problem520.HarperTiltedModerateTail
import Erdos.Problem520.HarperCentralBandBarrier

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-! Sharp internal-barrier estimates for the literal tilted prime-block
path. Retaining the surviving suffix supplies the additional inverse square
root needed when summing strong-barrier deletion contributions. -/

/-- Expanding the Gaussian cells retains the internal lower pinch, with
the explicit bounded enlargement of both barriers. -/
theorem candidate_gaussianExpanded_internalBarrier_probability_le
    (start m q : ℕ) (hm : 3 ≤ m) (hq : 0 < q) (v : Fin (m + q) → ℝ≥0)
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (lower upper : Fin (m + q) → ℝ)
    (hupper : ∀ i, upper i ≤ x)
    (hpinch : ∀ i, i.val + 1 = m → x - r ≤ lower i)
    (hlo : ∀ i, (1 / 4 : ℝ≥0) ≤ v i) (hhi : ∀ i, v i ≤ (1 / 2 : ℝ≥0)) :
    (Measure.pi (fun i : Fin (m + q) => gaussianReal 0 (v i))).real
      (Problem520.harperExpandedPartialSumBarrierSet lower upper
        (Problem520.harperScheduledRelativeCellWidth start (m + q))) ≤
      (8192 * (x + 4) * (r + 6) * (r + 4) /
        (Real.sqrt ((m / 3 : ℕ) : ℝ)) ^ 3) *
      (64 * (r + 6) / Real.sqrt (q : ℝ)) := by
  have hwidth := Problem520.harperCumulativeScheduledRelativeCellWidth_le_two start (m + q)
  have h := candidate_gaussian_internalBarrier_probability_le m q hm hq v
    (x + 2) (r + 4) (by linarith) (by linarith)
    (fun i => lower i - Problem520.harperCumulativeCellWidth
      (Problem520.harperScheduledRelativeCellWidth start (m + q)) i)
    (fun i => upper i + Problem520.harperCumulativeCellWidth
      (Problem520.harperScheduledRelativeCellWidth start (m + q)) i)
    (fun i => by linarith [hupper i, hwidth i])
    (fun i hi => by linarith [hpinch i hi, hwidth i]) hlo hhi
  convert h using 1 <;> congr 1 <;> ring

/-- A sharp terminal-near bound for the actual tilted, varying-height
centered prime-block path.  The hypotheses are those already proved for the
effective off-diagonal block comparison; no Gaussian approximation premise
remains. -/
theorem candidate_exists_tilted_internalBarrier_probability_le (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ m q : ℕ, 3 ≤ m → 0 < q → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + (m + q)) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin (m + q) → ℝ,
      (∀ i, |u i - t| * Real.log
        (Problem520.harperBlockEndpoint (start + i.val + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r → ∀ lower upper : Fin (m + q) → ℝ,
      (∀ i, upper i ≤ x) →
      (∀ i, i.val + 1 = m → x - r ≤ lower i) →
      (Problem520.harperTiltedCubeLaw y t).real
        ((Problem520.harperScheduledCenteredBlockVectorVarying y start (m + q) t u) ⁻¹'
          Problem520.harperPartialSumBarrierSet lower upper) ≤
        Real.exp 2 * (8192 * (x + 4) * (r + 6) * (r + 4) /
          (Real.sqrt ((m / 3 : ℕ) : ℝ)) ^ 3 * (64 * (r + 6) / Real.sqrt (q : ℝ))) + 64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨Jc, hJc⟩ :=
    Problem520.exists_eventually_harperScheduledOffDiagonalModerateBoxBarrierProbability_le_exp_two_mul_gaussian M
  obtain ⟨Jv, hJv⟩ :=
    Problem520.exists_eventually_harperScheduledOffDiagonalGaussianVariance_quarter_half M
  obtain ⟨Jt, hJt⟩ :=
    Problem520.exists_eventually_harperTiltedCubeVaryingModerateBox_compl_probability_le M
  refine ⟨max Jc (max Jv Jt), ?_⟩
  intro start hstart m q hm hq y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal
  have hc : Jc ≤ start := (le_max_left _ _).trans hstart
  have hv : Jv ≤ start := (le_max_left _ _).trans ((le_max_right _ _).trans hstart)
  have ht : Jt ≤ start := (le_max_right _ _).trans ((le_max_right _ _).trans hstart)
  let N := m + q
  let path := Problem520.harperScheduledCenteredBlockVectorVarying y start N t u
  let barrier := Problem520.harperPartialSumBarrierSet lower upper
  let box := Problem520.harperCoordinateBox (Problem520.harperScheduledModerateRadius start N)
  let V := Problem520.harperScheduledOffDiagonalGaussianVariance y start N t u
  let b := (8192 * (x + 4) * (r + 6) * (r + 4) / (Real.sqrt ((m / 3 : ℕ) : ℝ)) ^ 3) * (64 * (r + 6) / Real.sqrt (q : ℝ))
  have hvar := hJv start hv N y hy t htlo hthi u hu
  have hgauss :
      (Measure.pi (fun i : Fin N => Problem520.harperGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t (u i))).real
        (Problem520.harperExpandedPartialSumBarrierSet lower upper
          (Problem520.harperScheduledRelativeCellWidth start N)) ≤ b := by
    exact candidate_gaussianExpanded_internalBarrier_probability_le start m q hm hq V x r hx hr
      lower upper hupper hterminal (fun i => (hvar i).1) (fun i => (hvar i).2)
  have hmod : (Problem520.harperTiltedCubeLaw y t).real
      (path ⁻¹' (barrier ∩ box)) ≤ Real.exp 2 * b := by
    rw [Problem520.harperTiltedCubeLaw_real_preimage_centeredBlockVectorVarying_eq_pi
      y start N t u (barrier ∩ box)
      ((Problem520.measurableSet_harperPartialSumBarrierSet lower upper).inter
        (Problem520.measurableSet_harperCoordinateBox _))]
    exact (hJc start hc N y hy t htlo hthi u hu lower upper).trans
      (mul_le_mul_of_nonneg_left hgauss (Real.exp_pos 2).le)
  have htail := hJt start ht N y hy t htlo hthi u hu
  have hsubset : path ⁻¹' barrier ⊆ path ⁻¹' (barrier ∩ box) ∪ path ⁻¹' boxᶜ := by
    intro η hη
    by_cases hbox : path η ∈ box
    · exact Or.inl ⟨hη, hbox⟩
    · exact Or.inr hbox
  calc
    _ ≤ (Problem520.harperTiltedCubeLaw y t).real
        (path ⁻¹' (barrier ∩ box) ∪ path ⁻¹' boxᶜ) := measureReal_mono hsubset
    _ ≤ (Problem520.harperTiltedCubeLaw y t).real (path ⁻¹' (barrier ∩ box)) +
        (Problem520.harperTiltedCubeLaw y t).real (path ⁻¹' boxᶜ) := measureReal_union_le _ _
    _ ≤ _ := add_le_add hmod htail

/-- The same terminal-near bound on shrinking central frequency bands.
The required initial block shift is explicit in the band index: `J + d`. -/
theorem candidate_exists_centralBand_tilted_internalBarrier_probability_le :
    ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start → ∀ m q : ℕ, 3 ≤ m → 0 < q → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + (m + q)) ≤ y →
      ∀ t : ℝ, (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ (1 / 2 : ℝ) ^ d →
      ∀ u : Fin (m + q) → ℝ,
      (∀ i, |u i - t| * Real.log
        (Problem520.harperBlockEndpoint (start + i.val + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r → ∀ lower upper : Fin (m + q) → ℝ,
      (∀ i, upper i ≤ x) →
      (∀ i, i.val + 1 = m → x - r ≤ lower i) →
      (Problem520.harperTiltedCubeLaw y t).real
        ((Problem520.harperScheduledCenteredBlockVectorVarying y start (m + q) t u) ⁻¹'
          Problem520.harperPartialSumBarrierSet lower upper) ≤
        Real.exp 2 * (8192 * (x + 4) * (r + 6) * (r + 4) /
          (Real.sqrt ((m / 3 : ℕ) : ℝ)) ^ 3 * (64 * (r + 6) / Real.sqrt (q : ℝ))) + 64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨Jc, hJc⟩ :=
    Problem520.exists_harperScheduledCentralBandModerateBoxBarrierProbability_le_exp_two_mul_gaussian
  obtain ⟨Jv, hJv⟩ := Problem520.exists_harperScheduledCentralBandVarianceVector_quarter_half
  refine ⟨max 8 (max Jc Jv), ?_⟩
  intro d start hstart m q hm hq y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal
  have hc : Jc + d ≤ start := by omega
  have hv : Jv + d ≤ start := by omega
  have h8 : 8 ≤ start := by omega
  let N := m + q
  let path := Problem520.harperScheduledCenteredBlockVectorVarying y start N t u
  let barrier := Problem520.harperPartialSumBarrierSet lower upper
  let box := Problem520.harperCoordinateBox (Problem520.harperScheduledModerateRadius start N)
  let V := Problem520.harperScheduledOffDiagonalGaussianVariance y start N t u
  let b := (8192 * (x + 4) * (r + 6) * (r + 4) / (Real.sqrt ((m / 3 : ℕ) : ℝ)) ^ 3) * (64 * (r + 6) / Real.sqrt (q : ℝ))
  have hvar := hJv d start hv N y hy t htlo hthi u hu
  have hgauss :
      (Measure.pi (fun i : Fin N => Problem520.harperGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t (u i))).real
        (Problem520.harperExpandedPartialSumBarrierSet lower upper
          (Problem520.harperScheduledRelativeCellWidth start N)) ≤ b := by
    apply candidate_gaussianExpanded_internalBarrier_probability_le start m q hm hq V x r hx hr
      lower upper hupper hterminal
    · intro i
      exact_mod_cast (hvar i).1.le
    · intro i
      exact_mod_cast (hvar i).2.le
  have hmod : (Problem520.harperTiltedCubeLaw y t).real
      (path ⁻¹' (barrier ∩ box)) ≤ Real.exp 2 * b := by
    rw [Problem520.harperTiltedCubeLaw_real_preimage_centeredBlockVectorVarying_eq_pi
      y start N t u (barrier ∩ box)
      ((Problem520.measurableSet_harperPartialSumBarrierSet lower upper).inter
        (Problem520.measurableSet_harperCoordinateBox _))]
    exact (hJc d start hc N y hy t htlo hthi u hu lower upper).trans
      (mul_le_mul_of_nonneg_left hgauss (Real.exp_pos 2).le)
  have htail := Problem520.harperTiltedCubeLaw_real_preimage_moderateBox_compl_le
    t u h8 (fun i => (hvar i).2.le)
  have hsubset : path ⁻¹' barrier ⊆ path ⁻¹' (barrier ∩ box) ∪ path ⁻¹' boxᶜ := by
    intro η hη
    by_cases hbox : path η ∈ box
    · exact Or.inl ⟨hη, hbox⟩
    · exact Or.inr hbox
  calc
    _ ≤ (Problem520.harperTiltedCubeLaw y t).real
        (path ⁻¹' (barrier ∩ box) ∪ path ⁻¹' boxᶜ) := measureReal_mono hsubset
    _ ≤ (Problem520.harperTiltedCubeLaw y t).real (path ⁻¹' (barrier ∩ box)) +
        (Problem520.harperTiltedCubeLaw y t).real (path ⁻¹' boxᶜ) := measureReal_union_le _ _
    _ ≤ _ := add_le_add hmod htail


end

end Erdos.Problem1144
