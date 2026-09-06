import Erdos.Problem1144.HarperCandidateCovarianceMixedSurvivors
import Erdos.Problem1144.HarperCandidateCovarianceMixedOrdered

open Finset Set MeasureTheory
open scoped BigOperators Classical

namespace Erdos.Problem1144

noncomputable section

private theorem rootedScale_pos {ι : Type*} (j : ι → ℕ) (i : Option ι) :
    0 < candidateMixedRootedScale j i := by
  cases i with
  | none => norm_num [candidateMixedRootedScale]
  | some i => exact Problem520.invLog_harperBlockEndpoint_pos (j i)

/-- The rooted literal moment with its ordered interactions fully summed.
The exponential loss is `32 m log(m+1) + O(m)`, plus the explicit summable
PNT error. The hypotheses are only the actual cutoff, cap, and height
geometry inequalities. -/
theorem candidate_exists_rooted_ordered_prefixBarrier_mixedEuler_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ {ι : Type} [Fintype ι], ∀ y start : ℕ, 3 ≤ y → J ≤ start →
    ∀ j : ι → ℕ, (∀ i, start ≤ j i) →
      (∀ i, Problem520.harperBlockEndpoint (j i) ≤ y) →
    ∀ t : Option ι → ℝ, Function.Injective t →
      (∀ i, 0 ≤ t i ∧ t i ≤ candidateCovarianceHeightWindow start / 2) →
      (∀ a b, t a < t b → candidateMixedRootedScale j a ≤ t b - t a) →
    ∀ A : ι → ℝ, (∀ i, 0 ≤ A i) →
    let m := Fintype.card (Option ι)
    (∫ ω, {ω | ∀ i : ι, Problem520.harperEulerDensity
      (Problem520.harperBlockEndpoint (j i)) ω (t (some i)) ≤ A i}.indicator
        (fun ω => ∏ i : Option ι, Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      (∏ i, A i) * (D ^ m * (Real.log (y : ℝ) / Real.log 3) *
      (∏ i, Real.log (y : ℝ) / Real.log (Problem520.harperBlockEndpoint (j i) : ℝ)) *
      Real.exp ((4 * Real.log 4 + 8 / 3) * m + 32 * m * Real.log ((m : ℝ) + 1) +
        2 * C * (m : ℝ) ^ 2 * Problem520.invLog (Problem520.harperBlockEndpoint start) ^ 2)) := by
  classical
  obtain ⟨C, D, hC, hD, J, hres⟩ := candidate_exists_rooted_prefixBarrier_mixedEuler_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro ι _ y start hy hstart j hj hjy t hinj ht hgap A hA
  dsimp only
  have hfreq : ∀ a b, a ≠ b → t a - t b ≠ 0 ∧ t a + t b ≠ 0 ∧
      |t a - t b| ≤ candidateCovarianceHeightWindow start ∧
      |t a + t b| ≤ candidateCovarianceHeightWindow start := by
    intro a b hab
    have ha := ht a
    have hb := ht b
    have hne : t a ≠ t b := fun h => hab (hinj h)
    refine ⟨sub_ne_zero.mpr hne, ?_, ?_, ?_⟩
    · intro h
      exact hne (by linarith)
    · apply abs_le.mpr
      constructor <;> linarith
    · rw [abs_of_nonneg (add_nonneg ha.1 hb.1)]
      linarith
  have hraw := hres y start hy hstart j hj hjy t hfreq A hA
  dsimp only at hraw
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun i _ => hA i)
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have hpair := candidate_sum_fintype_rademacher_interactions_le
      (candidateMixedRootedScale j) t (rootedScale_pos j) (fun i => (ht i).1) hinj hgap
    have herr := candidate_sum_rooted_pair_square_scales_le start j hj
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left herr (by positivity : 0 ≤ 2 * C)]
  · have hlogy : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ y))
    have hlogs (i : ι) : 0 ≤ Real.log (Problem520.harperBlockEndpoint (j i) : ℝ) :=
      (Problem520.one_le_log_harperBlockEndpoint (j i)).trans' (by norm_num)
    exact mul_nonneg (mul_nonneg (pow_nonneg hD.le _) (div_nonneg hlogy (by positivity)))
      (Finset.prod_nonneg fun i _ => div_nonneg hlogy (hlogs i))

/-- Full top prefixes are extracted before the mixed expectation and its
height interactions are estimated. No injectivity or gap condition is
placed on any deleted height. All original prefix caps remain in the
prefactor, so both ordinary and paid strong caps are supported. -/
theorem candidate_exists_fullPrefix_survivor_mixedEuler_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ {ι : Type} [Fintype ι], ∀ start stop : ℕ, J ≤ start →
    ∀ j : ι → ℕ, (∀ i, start ≤ j i) → (∀ i, j i ≤ stop) →
    ∀ t : Option ι → ℝ, ∀ A : ι → ℝ, (∀ i, 0 ≤ A i) →
    let y := Problem520.harperBlockEndpoint stop
    let s := Finset.univ.filter (fun i => j i < stop)
    let t' : Option s → ℝ := fun i => t (i.map Subtype.val)
    let j' : s → ℕ := fun i => j i
    let m := Fintype.card (Option s)
    Function.Injective t' →
      (∀ i, 0 ≤ t' i ∧ t' i ≤ candidateCovarianceHeightWindow start / 2) →
      (∀ a b, t' a < t' b → candidateMixedRootedScale j' a ≤ t' b - t' a) →
    (∫ ω, {ω | ∀ i : ι, Problem520.harperEulerDensity
      (Problem520.harperBlockEndpoint (j i)) ω (t (some i)) ≤ A i}.indicator
        (fun ω => ∏ i : Option ι, Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      (∏ i, A i) * (D ^ m * (Real.log (y : ℝ) / Real.log 3) *
      (∏ i : s, Real.log (y : ℝ) / Real.log (Problem520.harperBlockEndpoint (j i) : ℝ)) *
      Real.exp ((4 * Real.log 4 + 8 / 3) * m + 32 * m * Real.log ((m : ℝ) + 1) +
        2 * C * (m : ℝ) ^ 2 * Problem520.invLog (Problem520.harperBlockEndpoint start) ^ 2)) := by
  classical
  obtain ⟨C, D, hC, hD, J, hbound⟩ :=
    candidate_exists_rooted_ordered_prefixBarrier_mixedEuler_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro ι _ start stop hstart j hj hjstop t A hA
  dsimp only
  let y := Problem520.harperBlockEndpoint stop
  let s := Finset.univ.filter (fun i => j i < stop)
  let t' : Option s → ℝ := fun i => t (i.map Subtype.val)
  let j' : s → ℕ := fun i => j i
  intro hinj ht hgap
  have hcy : ∀ i, Problem520.harperBlockEndpoint (j i) ≤ y := fun i =>
    Problem520.monotone_harperBlockEndpoint (hjstop i)
  have hdrop := candidate_integral_rooted_prefixBarrier_drop_fullPrefixes y
    (fun i => Problem520.harperBlockEndpoint (j i)) hcy t A hA
  dsimp only at hdrop
  rw [candidate_blockEndpoint_survivors_eq stop j] at hdrop
  have hsurv := hbound y start
    (by have := Problem520.harperBlockEndpoint_ge_sixteen stop; dsimp [y]; omega)
    hstart j' (fun i => hj i) (fun i => hcy i) t' hinj ht hgap
    (fun i : s => A i) (fun i => hA i)
  dsimp only at hsurv
  have hprodA : (∏ i ∈ sᶜ, A i) * (∏ i : s, A i) = ∏ i : ι, A i := by
    rw [Finset.prod_coe_sort s A, mul_comm]
    exact Finset.prod_mul_prod_compl s A
  apply hdrop.trans
  have h := mul_le_mul_of_nonneg_left hsurv
    (Finset.prod_nonneg (s := sᶜ) (fun i _ => hA i))
  rw [← mul_assoc, hprodA] at h
  exact h

end

end Erdos.Problem1144
