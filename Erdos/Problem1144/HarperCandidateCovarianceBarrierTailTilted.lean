import Erdos.Problem1144.HarperCandidateCovarianceBarrierTailGaussian
import Erdos.Problem520.HarperTiltedModerateTail
import Erdos.Problem520.HarperTiltedOmega
import Erdos.Problem520.HarperCentralBandBarrier

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-!
# Terminal-near mass for the actual tilted prime-block path

The proved finite-slicing comparison retains both sides of every partial-sum
barrier.  In particular it retains a terminal interval.  Combining it with
the three-block Gaussian estimate gives inverse-three-halves decay for the
literal centered prime-block path, up to the proved moderate-box tail.

The height hypotheses below are precisely those of the existing effective
prime-block comparisons, including shrinking central bands with the explicit
initial shift `J + d`.  Translating the Euler-product strong barrier and
summing the deletion contributions are not asserted here.
-/

private theorem expandedBarrier_subset_terminalNear
    (start n : ℕ) (hn : 0 < n) (x r : ℝ) (lower upper : Fin n → ℝ)
    (hupper : ∀ i, upper i ≤ x)
    (hterminal : ∀ i, i.val + 1 = n → x - r ≤ lower i) :
    Problem520.harperExpandedPartialSumBarrierSet lower upper
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

/-- The arbitrary expanded two-sided Gaussian barrier keeps the terminal
interval, with only the explicit total cell-width enlargement. -/
theorem candidate_gaussianExpanded_terminalBarrier_probability_le
    (start m : ℕ) (hm : 0 < m) (v : Fin (m + (m + m)) → ℝ≥0)
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (lower upper : Fin (m + (m + m)) → ℝ)
    (hupper : ∀ i, upper i ≤ x)
    (hterminal : ∀ i, i.val + 1 = m + (m + m) → x - r ≤ lower i)
    (hlo : ∀ i, (1 / 4 : ℝ≥0) ≤ v i) (hhi : ∀ i, v i ≤ (1 / 2 : ℝ≥0)) :
    (Measure.pi (fun i : Fin (m + (m + m)) => gaussianReal 0 (v i))).real
      (Problem520.harperExpandedPartialSumBarrierSet lower upper
        (Problem520.harperScheduledRelativeCellWidth start (m + (m + m)))) ≤
      8192 * (x + 4) * (r + 6) * (r + 4) / (Real.sqrt (m : ℝ)) ^ 3 := by
  refine (measureReal_mono
    (expandedBarrier_subset_terminalNear start (m + (m + m)) (by omega)
      x r lower upper hupper hterminal)).trans ?_
  have h := candidate_gaussianWalkTerminalNear_probability_le_three_halves m hm v
    (x + 2) (r + 4) (by linarith) (by linarith) hlo hhi
  convert h using 1 <;> congr 1 <;> ring

/-- A sharp terminal-near bound for the actual tilted, varying-height
centered prime-block path.  The hypotheses are those already proved for the
effective off-diagonal block comparison; no Gaussian approximation premise
remains. -/
theorem candidate_exists_tilted_terminalBarrier_probability_le (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ m : ℕ, 0 < m → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + (m + (m + m))) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin (m + (m + m)) → ℝ,
      (∀ i, |u i - t| * Real.log
        (Problem520.harperBlockEndpoint (start + i.val + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r → ∀ lower upper : Fin (m + (m + m)) → ℝ,
      (∀ i, upper i ≤ x) →
      (∀ i, i.val + 1 = m + (m + m) → x - r ≤ lower i) →
      (Problem520.harperTiltedCubeLaw y t).real
        ((Problem520.harperScheduledCenteredBlockVectorVarying y start (m + (m + m)) t u) ⁻¹'
          Problem520.harperPartialSumBarrierSet lower upper) ≤
        Real.exp 2 * (8192 * (x + 4) * (r + 6) * (r + 4) /
          (Real.sqrt (m : ℝ)) ^ 3) + 64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨Jc, hJc⟩ :=
    Problem520.exists_eventually_harperScheduledOffDiagonalModerateBoxBarrierProbability_le_exp_two_mul_gaussian M
  obtain ⟨Jv, hJv⟩ :=
    Problem520.exists_eventually_harperScheduledOffDiagonalGaussianVariance_quarter_half M
  obtain ⟨Jt, hJt⟩ :=
    Problem520.exists_eventually_harperTiltedCubeVaryingModerateBox_compl_probability_le M
  refine ⟨max Jc (max Jv Jt), ?_⟩
  intro start hstart m hm y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal
  have hc : Jc ≤ start := (le_max_left _ _).trans hstart
  have hv : Jv ≤ start := (le_max_left _ _).trans ((le_max_right _ _).trans hstart)
  have ht : Jt ≤ start := (le_max_right _ _).trans ((le_max_right _ _).trans hstart)
  let N := m + (m + m)
  let path := Problem520.harperScheduledCenteredBlockVectorVarying y start N t u
  let barrier := Problem520.harperPartialSumBarrierSet lower upper
  let box := Problem520.harperCoordinateBox (Problem520.harperScheduledModerateRadius start N)
  let V := Problem520.harperScheduledOffDiagonalGaussianVariance y start N t u
  let b := 8192 * (x + 4) * (r + 6) * (r + 4) / (Real.sqrt (m : ℝ)) ^ 3
  have hvar := hJv start hv N y hy t htlo hthi u hu
  have hgauss :
      (Measure.pi (fun i : Fin N => Problem520.harperGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t (u i))).real
        (Problem520.harperExpandedPartialSumBarrierSet lower upper
          (Problem520.harperScheduledRelativeCellWidth start N)) ≤ b := by
    exact candidate_gaussianExpanded_terminalBarrier_probability_le start m hm V x r hx hr
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

/-- The corresponding sharp weighted mass on the original infinite sign
space.  The weight is the actual unnormalized squared Euler product. -/
theorem candidate_exists_eulerWeighted_terminalBarrier_mass_le (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ m : ℕ, 0 < m → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + (m + (m + m))) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin (m + (m + m)) → ℝ,
      (∀ i, |u i - t| * Real.log
        (Problem520.harperBlockEndpoint (start + i.val + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r → ∀ lower upper : Fin (m + (m + m)) → ℝ,
      (∀ i, upper i ≤ x) →
      (∀ i, i.val + 1 = m + (m + m) → x - r ≤ lower i) →
      (∫ ω in Problem520.harperPrimeRestriction y ⁻¹'
        ((Problem520.harperScheduledCenteredBlockVectorVarying y start (m + (m + m)) t u) ⁻¹'
          Problem520.harperPartialSumBarrierSet lower upper),
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
        Problem520.primeEnergyNormalizer y *
          (Real.exp 2 * (8192 * (x + 4) * (r + 6) * (r + 4) /
            (Real.sqrt (m : ℝ)) ^ 3) + 64 * (1 / 2 : ℝ) ^ start) := by
  obtain ⟨J, hJ⟩ := candidate_exists_tilted_terminalBarrier_probability_le M
  refine ⟨J, ?_⟩
  intro start hstart m hm y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal
  have hdensity : (fun ω => Problem520.harperEulerDensity y ω t) =
      fun ω => Problem520.primeEnergyNormalizer y *
        Problem520.normalizedHarperEulerDensity y ω t := by
    funext ω
    unfold Problem520.normalizedHarperEulerDensity
    exact (mul_div_cancel₀ _ (Problem520.primeEnergyNormalizer_pos y).ne').symm
  rw [hdensity, integral_const_mul, ← Problem520.harperTiltedCubeLaw_real_apply_eq_omega]
  exact mul_le_mul_of_nonneg_left
    (hJ start hstart m hm y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal)
    (Problem520.primeEnergyNormalizer_pos y).le

/-- The same terminal-near bound on shrinking central frequency bands.
The required initial block shift is explicit in the band index: `J + d`. -/
theorem candidate_exists_centralBand_tilted_terminalBarrier_probability_le :
    ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start → ∀ m : ℕ, 0 < m → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + (m + (m + m))) ≤ y →
      ∀ t : ℝ, (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ (1 / 2 : ℝ) ^ d →
      ∀ u : Fin (m + (m + m)) → ℝ,
      (∀ i, |u i - t| * Real.log
        (Problem520.harperBlockEndpoint (start + i.val + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r → ∀ lower upper : Fin (m + (m + m)) → ℝ,
      (∀ i, upper i ≤ x) →
      (∀ i, i.val + 1 = m + (m + m) → x - r ≤ lower i) →
      (Problem520.harperTiltedCubeLaw y t).real
        ((Problem520.harperScheduledCenteredBlockVectorVarying y start (m + (m + m)) t u) ⁻¹'
          Problem520.harperPartialSumBarrierSet lower upper) ≤
        Real.exp 2 * (8192 * (x + 4) * (r + 6) * (r + 4) /
          (Real.sqrt (m : ℝ)) ^ 3) + 64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨Jc, hJc⟩ :=
    Problem520.exists_harperScheduledCentralBandModerateBoxBarrierProbability_le_exp_two_mul_gaussian
  obtain ⟨Jv, hJv⟩ := Problem520.exists_harperScheduledCentralBandVarianceVector_quarter_half
  refine ⟨max 8 (max Jc Jv), ?_⟩
  intro d start hstart m hm y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal
  have hc : Jc + d ≤ start := by omega
  have hv : Jv + d ≤ start := by omega
  have h8 : 8 ≤ start := by omega
  let N := m + (m + m)
  let path := Problem520.harperScheduledCenteredBlockVectorVarying y start N t u
  let barrier := Problem520.harperPartialSumBarrierSet lower upper
  let box := Problem520.harperCoordinateBox (Problem520.harperScheduledModerateRadius start N)
  let V := Problem520.harperScheduledOffDiagonalGaussianVariance y start N t u
  let b := 8192 * (x + 4) * (r + 6) * (r + 4) / (Real.sqrt (m : ℝ)) ^ 3
  have hvar := hJv d start hv N y hy t htlo hthi u hu
  have hgauss :
      (Measure.pi (fun i : Fin N => Problem520.harperGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y (start + i.val)) t (u i))).real
        (Problem520.harperExpandedPartialSumBarrierSet lower upper
          (Problem520.harperScheduledRelativeCellWidth start N)) ≤ b := by
    apply candidate_gaussianExpanded_terminalBarrier_probability_le start m hm V x r hx hr
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

/-- The central-band terminal estimate as a literal Euler-weighted mass,
uniformly under the explicit initial shift `start ≥ J + d`. -/
theorem candidate_exists_centralBand_eulerWeighted_terminalBarrier_mass_le :
    ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start → ∀ m : ℕ, 0 < m → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + (m + (m + m))) ≤ y →
      ∀ t : ℝ, (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ (1 / 2 : ℝ) ^ d →
      ∀ u : Fin (m + (m + m)) → ℝ,
      (∀ i, |u i - t| * Real.log
        (Problem520.harperBlockEndpoint (start + i.val + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r → ∀ lower upper : Fin (m + (m + m)) → ℝ,
      (∀ i, upper i ≤ x) →
      (∀ i, i.val + 1 = m + (m + m) → x - r ≤ lower i) →
      (∫ ω in Problem520.harperPrimeRestriction y ⁻¹'
        ((Problem520.harperScheduledCenteredBlockVectorVarying y start (m + (m + m)) t u) ⁻¹'
          Problem520.harperPartialSumBarrierSet lower upper),
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
        Problem520.primeEnergyNormalizer y *
          (Real.exp 2 * (8192 * (x + 4) * (r + 6) * (r + 4) /
            (Real.sqrt (m : ℝ)) ^ 3) + 64 * (1 / 2 : ℝ) ^ start) := by
  obtain ⟨J, hJ⟩ := candidate_exists_centralBand_tilted_terminalBarrier_probability_le
  refine ⟨J, ?_⟩
  intro d start hstart m hm y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal
  have hdensity : (fun ω => Problem520.harperEulerDensity y ω t) =
      fun ω => Problem520.primeEnergyNormalizer y *
        Problem520.normalizedHarperEulerDensity y ω t := by
    funext ω
    unfold Problem520.normalizedHarperEulerDensity
    exact (mul_div_cancel₀ _ (Problem520.primeEnergyNormalizer_pos y).ne').symm
  rw [hdensity, integral_const_mul, ← Problem520.harperTiltedCubeLaw_real_apply_eq_omega]
  exact mul_le_mul_of_nonneg_left
    (hJ d start hstart m hm y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal)
    (Problem520.primeEnergyNormalizer_pos y).le

end

end Erdos.Problem1144
