import Erdos.Problem1144.HarperCandidateCovarianceGrowingHeightDeletion

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-- The terminal cell retains the sharp inverse-three-halves strip bound
for every path length, without introducing a nonexistent surviving suffix. -/
theorem candidate_gaussianExpanded_terminalBarrier_probability_le_all_lengths
    (start n : ℕ) (hn : 3 ≤ n) (v : Fin n → ℝ≥0)
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (lower upper : Fin n → ℝ) (hupper : ∀ i, upper i ≤ x)
    (hterminal : ∀ i, i.val + 1 = n → x - r ≤ lower i)
    (hlo : ∀ i, (1 / 4 : ℝ≥0) ≤ v i) (hhi : ∀ i, v i ≤ (1 / 2 : ℝ≥0)) :
    (Measure.pi (fun i : Fin n => gaussianReal 0 (v i))).real
      (Problem520.harperExpandedPartialSumBarrierSet lower upper
        (Problem520.harperScheduledRelativeCellWidth start n)) ≤
      8192 * (x + 4) * (r + 6) * (r + 4) / (Real.sqrt ((n / 3 : ℕ) : ℝ)) ^ 3 := by
  have hsub : Problem520.harperExpandedPartialSumBarrierSet lower upper
      (Problem520.harperScheduledRelativeCellWidth start n) ⊆
        gaussianWalkTerminalNearSet n (x + 2) (r + 4) := by
    intro ω hω
    have hwidth := Problem520.harperCumulativeScheduledRelativeCellWidth_le_two start n
    refine ⟨?_, ?_⟩
    · apply (gaussianWalkSurvives_iff_harperPathPartialSum_le n (x + 2) ω).2
      intro i
      have hi := (Problem520.mem_harperPartialSumBarrierSet.mp hω i).2
      linarith [hupper i, hwidth i]
    · let last : Fin n := ⟨n - 1, by omega⟩
      have hlast : last.val + 1 = n := by dsimp [last]; omega
      have hi := (Problem520.mem_harperPartialSumBarrierSet.mp hω last).1
      rw [harperPathPartialSum_eq_terminal_sum ω last hlast] at hi
      change x + 2 - (∑ i, ω i) ≤ r + 4
      linarith [hterminal last hlast, hwidth last]
  have h := candidate_gaussianWalkTerminalNear_probability_le_all_lengths n hn v
    (x + 2) (r + 4) (by linarith) (by linarith) hlo hhi
  convert (measureReal_mono hsub).trans h using 1 <;> congr 1 <;> ring

theorem candidate_exists_growingHeight_tilted_terminalBarrier_probability_le_all_lengths :
    ∃ J : ℕ, ∀ start M : ℕ, J ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start → ∀ n : ℕ, 3 ≤ n → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + n) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
      ∀ u : Fin n → ℝ,
      (∀ i, |u i - t| * Real.log
        (Problem520.harperBlockEndpoint (start + i.val + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r → ∀ lower upper : Fin n → ℝ,
      (∀ i, upper i ≤ x) →
      (∀ i, i.val + 1 = n → x - r ≤ lower i) →
      (Problem520.harperTiltedCubeLaw y t).real
        ((Problem520.harperScheduledCenteredBlockVectorVarying y start n t u) ⁻¹'
          Problem520.harperPartialSumBarrierSet lower upper) ≤
        Real.exp 2 * (8192 * (x + 4) * (r + 6) * (r + 4) /
          (Real.sqrt ((n / 3 : ℕ) : ℝ)) ^ 3) + 64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨Jc, hJc⟩ := Filter.eventually_atTop.mp
    Problem520.eventually_harperScheduledOffDiagonalModerateBoxBarrierProbability_le_exp_two_mul_gaussian_of_variance
  obtain ⟨Jv, hJv⟩ := candidate_exists_growingHeight_variance_quarter_half
  refine ⟨max 8 (max Jc Jv), ?_⟩
  intro start M hstart hM n hn y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal
  have hc : Jc ≤ start := by omega
  have hv : Jv ≤ start := by omega
  have h8 : 8 ≤ start := by omega
  let N := n
  let path := Problem520.harperScheduledCenteredBlockVectorVarying y start N t u
  let barrier := Problem520.harperPartialSumBarrierSet lower upper
  let box := Problem520.harperCoordinateBox (Problem520.harperScheduledModerateRadius start N)
  let V := Problem520.harperScheduledOffDiagonalGaussianVariance y start N t u
  let b := (8192 * (x + 4) * (r + 6) * (r + 4) / (Real.sqrt ((n / 3 : ℕ) : ℝ)) ^ 3)
  have hvar (i : Fin N) := hJv start (start + i.val) M y hv (by omega) hM
    ((Problem520.monotone_harperBlockEndpoint (by dsimp [N] at *; omega)).trans hy)
    t htlo hthi (u i) (hu i)
  have hgauss :
      (Measure.pi (fun i : Fin N => Problem520.harperGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t (u i))).real
        (Problem520.harperExpandedPartialSumBarrierSet lower upper
          (Problem520.harperScheduledRelativeCellWidth start N)) ≤ b := by
    apply candidate_gaussianExpanded_terminalBarrier_probability_le_all_lengths start n hn V x r hx hr
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
    exact (hJc start hc N y t u hvar lower upper).trans
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


theorem candidate_exists_centralBand_tilted_terminalBarrier_probability_le_all_lengths :
    ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start → ∀ n : ℕ, 3 ≤ n → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + n) ≤ y →
      ∀ t : ℝ, (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ (1 / 2 : ℝ) ^ d →
      ∀ u : Fin n → ℝ,
      (∀ i, |u i - t| * Real.log
        (Problem520.harperBlockEndpoint (start + i.val + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r → ∀ lower upper : Fin n → ℝ,
      (∀ i, upper i ≤ x) →
      (∀ i, i.val + 1 = n → x - r ≤ lower i) →
      (Problem520.harperTiltedCubeLaw y t).real
        ((Problem520.harperScheduledCenteredBlockVectorVarying y start n t u) ⁻¹'
          Problem520.harperPartialSumBarrierSet lower upper) ≤
        Real.exp 2 * (8192 * (x + 4) * (r + 6) * (r + 4) /
          (Real.sqrt ((n / 3 : ℕ) : ℝ)) ^ 3) + 64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨Jc, hJc⟩ :=
    Problem520.exists_harperScheduledCentralBandModerateBoxBarrierProbability_le_exp_two_mul_gaussian
  obtain ⟨Jv, hJv⟩ := Problem520.exists_harperScheduledCentralBandVarianceVector_quarter_half
  refine ⟨max 8 (max Jc Jv), ?_⟩
  intro d start hstart n hn y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal
  have hc : Jc + d ≤ start := by omega
  have hv : Jv + d ≤ start := by omega
  have h8 : 8 ≤ start := by omega
  let N := n
  let path := Problem520.harperScheduledCenteredBlockVectorVarying y start N t u
  let barrier := Problem520.harperPartialSumBarrierSet lower upper
  let box := Problem520.harperCoordinateBox (Problem520.harperScheduledModerateRadius start N)
  let V := Problem520.harperScheduledOffDiagonalGaussianVariance y start N t u
  let b := (8192 * (x + 4) * (r + 6) * (r + 4) / (Real.sqrt ((n / 3 : ℕ) : ℝ)) ^ 3)
  have hvar := hJv d start hv N y hy t htlo hthi u hu
  have hgauss :
      (Measure.pi (fun i : Fin N => Problem520.harperGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t (u i))).real
        (Problem520.harperExpandedPartialSumBarrierSet lower upper
          (Problem520.harperScheduledRelativeCellWidth start N)) ≤ b := by
    apply candidate_gaussianExpanded_terminalBarrier_probability_le_all_lengths start n hn V x r hx hr
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
