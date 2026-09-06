import Erdos.Problem1144.HarperCandidateCovarianceBarrierDeletionEuler
import Erdos.Problem1144.HarperCandidateCovarianceBarrierDeletionTilted

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-!
# Strong-barrier deletion for literal finite Euler products

The weak upper barrier is imposed on every prefix. A deleted configuration
violates the stronger barrier at one of the selected interior locations.
The estimate retains both the terminal-near prefix and the surviving suffix.
-/

/-- Explicit polynomial cost of translating the Euler barriers and applying
the sharp Gaussian internal-barrier bound. -/
def candidateEulerDeletionPrefactor (C x r : ℝ) : ℝ :=
  Real.exp 2 * 524288 * (x + C + 4) * (r + 2 * C + 6) ^ 2 * (r + 2 * C + 4)

/-- The literal deleted event: every weak prefix barrier holds, but one of
the stronger barriers at the selected locations fails. -/
def candidateEulerStrongBarrierDeletionEvent (y start N : ℕ)
    (t x r : ℝ) (s : Finset ℕ) : Set (Problem520.HarperPrimeCube y) :=
  {η | (∀ k : Fin N, candidateEulerPrefixLog y start (k.val + 1) t η ≤ x) ∧
    ∃ j ∈ s, x - r ≤ candidateEulerPrefixLog y start j t η}

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

/-- Actual noncentral Euler-prefix deletion at one interior location. No
barrier approximation or probability estimate remains among the premises. -/
theorem candidate_exists_euler_internalBarrier_probability_le (M : ℕ) :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ start : ℕ, J ≤ start →
      ∀ m q : ℕ, 3 ≤ m → 0 < q → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + (m + q)) ≤ y →
      ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r →
      (Problem520.harperTiltedCubeLaw y t).real
        (candidateEulerInternalBarrierEvent y start (m + q) m t x r) ≤
      candidateEulerDeletionPrefactor C x r /
        ((Real.sqrt ((m / 3 : ℕ) : ℝ)) ^ 3 * Real.sqrt (q : ℝ)) +
          64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨C, hC, Jc, hc, _⟩ := candidate_exists_eulerPrefixLog_centered_close
  obtain ⟨Jp, hp⟩ := candidate_exists_tilted_internalBarrier_probability_le M
  refine ⟨C, hC, max (Jc + Nat.clog 2 (M + 1)) Jp, ?_⟩
  intro start hstart m q hm hq y hy t htlo hthi x r hx hr
  obtain ⟨lower, hlower, hsubset⟩ := euler_internalBarrier_subset
    y start (m + q) m t x r C (hc M start (m + q) y (by omega) hy t htlo hthi)
  have h := hp start (by omega) m q hm hq y hy t htlo hthi (fun _ => t)
    (by intro i; simp) (x + C) (r + 2 * C) (by positivity) (by positivity)
    lower (fun _ => x + C) (fun _ => le_rfl) hlower
  refine (measureReal_mono hsubset).trans ?_
  convert h using 1 <;> unfold candidateEulerDeletionPrefactor <;> ring

/-- The same literal deletion estimate uniformly over all central bands,
with the explicit required initial shift `start ≥ J+d`. -/
theorem candidate_exists_centralBand_euler_internalBarrier_probability_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start →
      ∀ m q : ℕ, 3 ≤ m → 0 < q → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + (m + q)) ≤ y →
      ∀ t : ℝ, (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ (1 / 2 : ℝ) ^ d →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r →
      (Problem520.harperTiltedCubeLaw y t).real
        (candidateEulerInternalBarrierEvent y start (m + q) m t x r) ≤
      candidateEulerDeletionPrefactor C x r /
        ((Real.sqrt ((m / 3 : ℕ) : ℝ)) ^ 3 * Real.sqrt (q : ℝ)) +
          64 * (1 / 2 : ℝ) ^ start := by
  obtain ⟨C, hC, Jc, _, hc⟩ := candidate_exists_eulerPrefixLog_centered_close
  obtain ⟨Jp, hp⟩ := candidate_exists_centralBand_tilted_internalBarrier_probability_le
  refine ⟨C, hC, max Jc Jp, ?_⟩
  intro d start hstart m q hm hq y hy t htlo hthi x r hx hr
  obtain ⟨lower, hlower, hsubset⟩ := euler_internalBarrier_subset
    y start (m + q) m t x r C (hc d start (m + q) y (by omega) hy t htlo hthi)
  have h := hp d start (by omega) m q hm hq y hy t htlo hthi (fun _ => t)
    (by intro i; simp) (x + C) (r + 2 * C) (by positivity) (by positivity)
    lower (fun _ => x + C) (fun _ => le_rfl) hlower
  refine (measureReal_mono hsubset).trans ?_
  convert h using 1 <;> unfold candidateEulerDeletionPrefactor <;> ring


/-- The suffix ballot costs sum to at most twice the square root of the
available time. -/
theorem candidate_sum_inverse_sqrt_succ_le (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / Real.sqrt ((k + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt (n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := by positivity
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)
    have hsq' := Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℕ) by positivity)
    have hstep : 2 * Real.sqrt (n : ℝ) +
        1 / Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
      apply (le_sub_iff_add_le').mp
      apply (div_le_iff₀ hpos).2
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
      nlinarith [hcast, sq_nonneg (Real.sqrt (n : ℝ) - Real.sqrt ((n + 1 : ℕ) : ℝ))]
    exact (add_le_add ih le_rfl).trans hstep

private theorem sum_suffix_inverse_sqrt_le (N : ℕ) (s : Finset ℕ)
    (hs : ∀ j ∈ s, j < N) :
    (∑ j ∈ s, 1 / Real.sqrt ((N - j : ℕ) : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  classical
  let f : ℕ → ℕ := fun j => N - j - 1
  have hf : Set.InjOn f (s : Set ℕ) := by
    intro j hj k hk heq
    have hjN := hs j hj
    have hkN := hs k hk
    dsimp [f] at heq
    omega
  have hsub : s.image f ⊆ Finset.range N := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hjN := hs j hj
    simp only [Finset.mem_range]
    dsimp [f]
    omega
  calc
    _ = ∑ k ∈ s.image f, 1 / Real.sqrt ((k + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_image hf]
      apply Finset.sum_congr rfl
      intro j hj
      have hjN := hs j hj
      have heq : f j + 1 = N - j := by dsimp [f]; omega
      rw [heq]
    _ ≤ ∑ k ∈ Finset.range N, 1 / Real.sqrt ((k + 1 : ℕ) : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ _ := candidate_sum_inverse_sqrt_succ_le N

/-- Summing all admissible internal violation locations preserves the
inverse-time saving when the first allowed location is a fixed fraction
of the total length. -/
theorem candidate_sum_internalBarrier_kernel_le
    (N a : ℕ) (ha : 3 ≤ a) (s : Finset ℕ)
    (hs : ∀ j ∈ s, a ≤ j ∧ j < N) :
    (∑ j ∈ s, 1 /
      ((Real.sqrt ((j / 3 : ℕ) : ℝ)) ^ 3 * Real.sqrt ((N - j : ℕ) : ℝ))) ≤
      2 * Real.sqrt (N : ℝ) / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3 := by
  have haR : (0 : ℝ) < (a / 3 : ℕ) := by exact_mod_cast (show 0 < a / 3 by omega)
  have hsa : 0 < (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3 := by positivity
  calc
    _ ≤ ∑ j ∈ s, 1 /
        ((Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3 * Real.sqrt ((N - j : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hqR : (0 : ℝ) < (N - j : ℕ) := by exact_mod_cast (show 0 < N - j by have := (hs j hj).2; omega)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      gcongr
      exact (hs j hj).1
    _ = (1 / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) *
        ∑ j ∈ s, 1 / Real.sqrt ((N - j : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (1 / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) * (2 * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_suffix_inverse_sqrt_le N s (fun j hj => (hs j hj).2))
        (by positivity)
    _ = _ := by ring

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


/-- Summed strong-barrier deletion for the actual Euler weight on the
infinite fair-sign space. The first allowed violation location `a` is
explicit, as is the negligible finite-slicing error. -/
theorem candidate_exists_eulerWeighted_strongBarrier_deletion_le (M : ℕ) :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ start : ℕ, J ≤ start →
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
  obtain ⟨C, hC, J, hp⟩ := candidate_exists_euler_internalBarrier_probability_le M
  refine ⟨C, hC, J, ?_⟩
  intro start hstart N a ha s hs y hy t htlo hthi x r hx hr
  have hprob := deletion_probability_le y start N a ha s hs t x r C hC hx hr
    (fun j hj => by
      have hjN := (hs j hj).2
      have hN : j + (N - j) = N := Nat.add_sub_of_le hjN.le
      have h := hp start hstart j (N - j) (by have := (hs j hj).1; omega)
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

/-- The complete summed Euler-weighted deletion estimate on shrinking
central bands. Both numerical constants are uniform in the band depth. -/
theorem candidate_exists_centralBand_eulerWeighted_strongBarrier_deletion_le :
    ∃ C ≥ 0, ∃ J : ℕ, ∀ d start : ℕ, J + d ≤ start →
      ∀ N a : ℕ, 3 ≤ a → ∀ s : Finset ℕ,
      (∀ j ∈ s, a ≤ j ∧ j < N) → ∀ y : ℕ,
      Problem520.harperBlockEndpoint (start + N) ≤ y →
      ∀ t : ℝ, (1 / 2 : ℝ) ^ (d + 1) < |t| → |t| ≤ (1 / 2 : ℝ) ^ d →
      ∀ x r : ℝ, 0 ≤ x → 0 ≤ r →
      (∫ ω in Problem520.harperPrimeRestriction y ⁻¹'
        candidateEulerStrongBarrierDeletionEvent y start N t x r s,
        Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
      Problem520.primeEnergyNormalizer y *
        (candidateEulerDeletionPrefactor C x r *
          (2 * Real.sqrt (N : ℝ) / (Real.sqrt ((a / 3 : ℕ) : ℝ)) ^ 3) +
          (s.card : ℝ) * (64 * (1 / 2 : ℝ) ^ start)) := by
  obtain ⟨C, hC, J, hp⟩ := candidate_exists_centralBand_euler_internalBarrier_probability_le
  refine ⟨C, hC, J, ?_⟩
  intro d start hstart N a ha s hs y hy t htlo hthi x r hx hr
  have hprob := deletion_probability_le y start N a ha s hs t x r C hC hx hr
    (fun j hj => by
      have hjN := (hs j hj).2
      have hN : j + (N - j) = N := Nat.add_sub_of_le hjN.le
      have h := hp d start hstart j (N - j) (by have := (hs j hj).1; omega)
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


/-- Full cutoff Euler products with an initial-prefix corridor. Subtracting
`j log 2` expresses both upper barriers on the same amplitude scale. -/
def candidateFullEulerStrongBarrierDeletionEvent (start N : ℕ)
    (t U L bLo bHi : ℝ) (s : Finset ℕ) : Set Problem520.Omega :=
  {ω | bLo ≤ (1 / 2 : ℝ) * Real.log
      (Problem520.harperEulerDensity (Problem520.harperBlockEndpoint start) ω t) ∧
    (1 / 2 : ℝ) * Real.log
      (Problem520.harperEulerDensity (Problem520.harperBlockEndpoint start) ω t) ≤ bHi ∧
    (∀ k : Fin N, (1 / 2 : ℝ) * Real.log
      (Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + (k.val + 1))) ω t) -
      ((k.val + 1 : ℕ) : ℝ) * Real.log 2 ≤ U) ∧
    ∃ j ∈ s, L ≤ (1 / 2 : ℝ) * Real.log
      (Problem520.harperEulerDensity (Problem520.harperBlockEndpoint (start + j)) ω t) -
      (j : ℝ) * Real.log 2}

/-- Full-product weak and strong barriers become the literal range-product
barriers after bounding only the initial prefix. This is a deterministic
inclusion, not a new probability assumption. -/
theorem candidate_fullEuler_deletion_subset_range
    (y start N : ℕ) (hy : Problem520.harperBlockEndpoint (start + N) ≤ y)
    (t U L bLo bHi : ℝ) (s : Finset ℕ) (hs : ∀ j ∈ s, j ≤ N) :
    candidateFullEulerStrongBarrierDeletionEvent start N t U L bLo bHi s ⊆
      Problem520.harperPrimeRestriction y ⁻¹'
        candidateEulerStrongBarrierDeletionEvent y start N t
          (U - bLo) ((U - bLo) - (L - bHi)) s := by
  intro ω hω
  obtain ⟨hbLo, hbHi, hweak, j, hj, hstrong⟩ := hω
  refine ⟨?_, j, hj, ?_⟩
  · intro k
    rw [candidateEulerPrefixLog_eq_full_density_ratio y start (k.val + 1)
      ((Problem520.monotone_harperBlockEndpoint (by omega)).trans hy)]
    have hk := hweak k
    linarith
  · rw [candidateEulerPrefixLog_eq_full_density_ratio y start j
      ((Problem520.monotone_harperBlockEndpoint (by have := hs j hj; omega)).trans hy)]
    linarith

/-- The full-cutoff deletion mass is bounded by the range-product mass
already estimated above. The Euler weight and both events are literal
functions of the original prime signs. -/
theorem candidate_fullEuler_deletion_mass_le_range
    (y start N : ℕ) (hy : Problem520.harperBlockEndpoint (start + N) ≤ y)
    (t U L bLo bHi : ℝ) (s : Finset ℕ) (hs : ∀ j ∈ s, j ≤ N) :
    (∫ ω in candidateFullEulerStrongBarrierDeletionEvent start N t U L bLo bHi s,
      Problem520.harperEulerDensity y ω t ∂Problem520.μ) ≤
    (∫ ω in Problem520.harperPrimeRestriction y ⁻¹'
      candidateEulerStrongBarrierDeletionEvent y start N t
        (U - bLo) ((U - bLo) - (L - bHi)) s,
      Problem520.harperEulerDensity y ω t ∂Problem520.μ) := by
  exact setIntegral_mono_set (Problem520.integrable_harperEulerDensity y t).integrableOn
    (Filter.Eventually.of_forall fun ω => (Problem520.harperEulerDensity_pos y ω t).le)
    (Filter.Eventually.of_forall (candidate_fullEuler_deletion_subset_range
      y start N hy t U L bLo bHi s hs))

end

end Erdos.Problem1144
