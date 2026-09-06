import Erdos.Problem1144.HarperCandidateCovarianceGrowingHeightMoments
import Erdos.Problem1144.HarperCandidateCovarianceBarrierDeletion

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-! Literal Euler strong-barrier deletion throughout the quantitative
growing frequency window. All starting thresholds below are absolute. -/

/-- The actual tilted path retains the internal pinch and surviving suffix
uniformly throughout the growing frequency window. -/
theorem candidate_exists_growingHeight_tilted_internalBarrier_probability_le :
    ∃ J : ℕ, ∀ start M : ℕ, J ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start → ∀ m q : ℕ, 3 ≤ m → 0 < q → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + (m + q)) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
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
  obtain ⟨Jc, hJc⟩ := Filter.eventually_atTop.mp
    Problem520.eventually_harperScheduledOffDiagonalModerateBoxBarrierProbability_le_exp_two_mul_gaussian_of_variance
  obtain ⟨Jv, hJv⟩ := candidate_exists_growingHeight_variance_quarter_half
  refine ⟨max 8 (max Jc Jv), ?_⟩
  intro start M hstart hM m q hm hq y hy t htlo hthi u hu x r hx hr lower upper hupper hterminal
  have hc : Jc ≤ start := by omega
  have hv : Jv ≤ start := by omega
  have h8 : 8 ≤ start := by omega
  let N := m + q
  let path := Problem520.harperScheduledCenteredBlockVectorVarying y start N t u
  let barrier := Problem520.harperPartialSumBarrierSet lower upper
  let box := Problem520.harperCoordinateBox (Problem520.harperScheduledModerateRadius start N)
  let V := Problem520.harperScheduledOffDiagonalGaussianVariance y start N t u
  let b := (8192 * (x + 4) * (r + 6) * (r + 4) / (Real.sqrt ((m / 3 : ℕ) : ℝ)) ^ 3) * (64 * (r + 6) / Real.sqrt (q : ℝ))
  have hvar (i : Fin N) := hJv start (start + i.val) M y hv (by omega) hM
    ((Problem520.monotone_harperBlockEndpoint (by dsimp [N] at *; omega)).trans hy)
    t htlo hthi (u i) (hu i)
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


private theorem taylorAllowance_le_one (start : ℕ) :
    (4 / 3 : ℝ) * (Real.sqrt (Problem520.harperBlockEndpoint start : ℝ))⁻¹ ≤ 1 := by
  have he : (16 : ℝ) ≤ Problem520.harperBlockEndpoint start := by
    exact_mod_cast Problem520.harperBlockEndpoint_ge_sixteen start
  have hs : (4 : ℝ) ≤ Real.sqrt (Problem520.harperBlockEndpoint start : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact Problem520.harperBlockEndpoint_ge_sixteen start
  have hpos : 0 < Real.sqrt (Problem520.harperBlockEndpoint start : ℝ) := by linarith
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  linarith

private theorem prefixLog_close_of_drift (y start n : ℕ) (t D : ℝ)
    (hD : ∀ k : Fin n,
      |Problem520.harperLogMainBlockMean y
        (Problem520.harperScheduledPrimeRangeFrom y start (k.val + 1)) t t -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ D)
    (η : Problem520.HarperPrimeCube y) (k : Fin n) :
    |candidateEulerPrefixLog y start (k.val + 1) t η -
      Problem520.harperPathPartialSum
        (Problem520.harperScheduledCenteredBlockVectorVarying y start n t (fun _ => t) η) k| ≤
      D + 1 := by
  have hTaylor := (Problem520.abs_harperLogRangeFrom_sub_centered_add_mean_le
    y start (k.val + 1) t t η).trans (taylorAllowance_le_one start)
  rw [harper1144_centeredRangeFrom_eq_pathPartialSum y start n t η k] at hTaylor
  rw [candidateEulerPrefixLog_eq]
  have hd := hD k
  rw [abs_le] at hTaylor hd ⊢
  constructor <;> linarith [hTaylor.1, hTaylor.2, hd.1, hd.2]

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


/-- Uniform approximation of actual Euler-prefix logarithms by their
centered path over the growing frequency window. -/
theorem candidate_exists_growingHeight_eulerPrefixLog_centered_close :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ start n M y : ℕ, J ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      Problem520.harperBlockEndpoint (start + n) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
      ∀ η : Problem520.HarperPrimeCube y, ∀ k : Fin n,
      |candidateEulerPrefixLog y start (k.val + 1) t η -
        Problem520.harperPathPartialSum
          (Problem520.harperScheduledCenteredBlockVectorVarying y start n t (fun _ => t) η) k| ≤ C := by
  obtain ⟨D, hD, J, hJ⟩ := candidate_exists_growingHeight_diagonalDrift_close
  refine ⟨D + 1, by positivity, J, ?_⟩
  intro start n M y hstart hM hy t htlo hthi η k
  exact prefixLog_close_of_drift y start n t D (fun i => hJ start (i.val + 1) M y
    hstart hM ((Problem520.monotone_harperBlockEndpoint (by omega)).trans hy) t htlo hthi) η k

/-- Literal Euler deletion at one location, uniformly at growing heights. -/
theorem candidate_exists_growingHeight_euler_internalBarrier_probability_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ start M : ℕ, J ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      ∀ m q : ℕ, 3 ≤ m → 0 < q → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + (m + q)) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ x r : ℝ, 0 ≤ x → 0 ≤ r →
      (Problem520.harperTiltedCubeLaw y t).real
        (candidateEulerInternalBarrierEvent y start (m + q) m t x r) ≤
      candidateEulerDeletionPrefactor C x r /
        ((Real.sqrt ((m / 3 : ℕ) : ℝ)) ^ 3 * Real.sqrt (q : ℝ)) +
          64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨C, hC, Jc, hc⟩ := candidate_exists_growingHeight_eulerPrefixLog_centered_close
  obtain ⟨Jp, hp⟩ := candidate_exists_growingHeight_tilted_internalBarrier_probability_le
  refine ⟨C, hC, max Jc Jp, ?_⟩
  intro start M hstart hM m q hm hq y hy t htlo hthi x r hx hr
  obtain ⟨lower, hlower, hsubset⟩ := euler_internalBarrier_subset y start (m + q) m t x r C
    (hc start (m + q) M y (by omega) hM hy t htlo hthi)
  have h := hp start M (by omega) hM m q hm hq y hy t htlo hthi (fun _ => t)
    (by intro i; simp) (x + C) (r + 2 * C) (by positivity) (by positivity)
    lower (fun _ => x + C) (fun _ => le_rfl) hlower
  refine (measureReal_mono hsubset).trans ?_
  convert h using 1 <;> unfold candidateEulerDeletionPrefactor <;> ring

private theorem deletion_probability_le
    (y start N a : ℕ) (ha : 3 ≤ a) (s : Finset ℕ)
    (hs : ∀ j ∈ s, a ≤ j ∧ j < N) (t x r C : ℝ)
    (hC : 0 ≤ C) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hp : ∀ j ∈ s,
      (Problem520.harperTiltedCubeLaw y t).real
        (candidateEulerInternalBarrierEvent y start N j t x r) ≤
      candidateEulerDeletionPrefactor C x r /
        ((Real.sqrt ((j / 3 : ℕ) : ℝ)) ^ 3 * Real.sqrt ((N - j : ℕ) : ℝ)) +
          64 * (1 / 2 : ℝ) ^ start) :
    (Problem520.harperTiltedCubeLaw y t).real
      (candidateEulerStrongBarrierDeletionEvent y start N t x r s) ≤
      candidateEulerDeletionPrefactor C x r *
        (2 * Real.sqrt (N : ℝ) / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) +
      (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start) := by
  classical
  have hsubset : candidateEulerStrongBarrierDeletionEvent y start N t x r s ⊆
      ⋃ j ∈ s, candidateEulerInternalBarrierEvent y start N j t x r := by
    intro η hη
    obtain ⟨j, hj, hlarge⟩ := hη.2
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hη.1, hlarge⟩⟩
  have hP : 0 ≤ candidateEulerDeletionPrefactor C x r := by
    unfold candidateEulerDeletionPrefactor
    positivity
  calc
    _ ≤ (Problem520.harperTiltedCubeLaw y t).real
        (⋃ j ∈ s, candidateEulerInternalBarrierEvent y start N j t x r) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ ∑ j ∈ s, (Problem520.harperTiltedCubeLaw y t).real
        (candidateEulerInternalBarrierEvent y start N j t x r) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ s, (candidateEulerDeletionPrefactor C x r /
        ((Real.sqrt ((j / 3 : ℕ) : ℝ)) ^ 3 * Real.sqrt ((N - j : ℕ) : ℝ)) +
          64 * (1 / 2 : ℝ) ^ start) := Finset.sum_le_sum hp
    _ = candidateEulerDeletionPrefactor C x r *
        (∑ j ∈ s, 1 /
          ((Real.sqrt ((j / 3 : ℕ) : ℝ)) ^ 3 * Real.sqrt ((N - j : ℕ) : ℝ))) +
        (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro j hj
        ring
      · simp
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (candidate_sum_internalBarrier_kernel_le N a ha s hs) hP) le_rfl



/-- The complete summed Euler-weighted deletion estimate with an absolute
threshold and the explicit growing frequency window. -/
theorem candidate_exists_growingHeight_eulerWeighted_strongBarrier_deletion_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ start M : ℕ, J ≤ start →
      (M : ℝ) ≤ candidateCovarianceHeightWindow start →
      ∀ N a : ℕ, 3 ≤ a → ∀ s : Finset ℕ,
      (∀ j ∈ s, a ≤ j ∧ j < N) → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ x r : ℝ, 0 ≤ x → 0 ≤ r →
      (∫ ω in Problem520.harperPrimeRestriction y ⁻¹'
        candidateEulerStrongBarrierDeletionEvent y start N t x r s,
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y *
        (candidateEulerDeletionPrefactor C x r *
          (2 * Real.sqrt (N : ℝ) / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) +
          (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start)) := by
  obtain ⟨C, hC, J, hp⟩ := candidate_exists_growingHeight_euler_internalBarrier_probability_le
  refine ⟨C, hC, J, ?_⟩
  intro start M hstart hM N a ha s hs y hy t htlo hthi x r hx hr
  have hprob := deletion_probability_le y start N a ha s hs t x r C hC hx hr
    (fun j hj => by
      have hjN := (hs j hj).2
      have hN : j + (N - j) = N := Nat.add_sub_of_le hjN.le
      have h := hp start M hstart hM j (N - j) (by have := (hs j hj).1; omega)
        (by omega) y (by simpa only [hN] using hy) t htlo hthi x r hx hr
      simpa only [hN] using h)
  have hdensity : (fun ω => Problem520.harperEulerDensity y ω t) =
      fun ω => Problem520.primeEnergyNormalizer y *
        Problem520.normalizedHarperEulerDensity y ω t := by
    funext ω
    unfold Problem520.normalizedHarperEulerDensity
    exact (mul_div_cancel₀ _ (Problem520.primeEnergyNormalizer_pos y).ne').symm
  rw [hdensity, integral_const_mul, ← Problem520.harperTiltedCubeLaw_real_apply_eq_omega]
  exact mul_le_mul_of_nonneg_left hprob (Problem520.primeEnergyNormalizer_pos y).le

end

end Erdos.Problem1144
