import Erdos.Problem1144.HarperCandidateCovarianceMixedSpacing
import Erdos.Problem1144.HarperCandidateCovarianceScreen
import Erdos.Problem1144.HarperCandidateCovarianceBarrierMoments

open Finset Set MeasureTheory
open scoped BigOperators

namespace Erdos.Problem1144

/-! Ordered height gaps can select the actual scheduled prime endpoints.
Rounding upward costs at most two in the logarithmic cutoff, except at the
explicit lower clipping endpoint. These are precisely the endpoints on
which the literal D-star and strong screen are already defined. -/

private theorem invLog_endpoint_succ (j : ℕ) :
    Problem520.invLog (Problem520.harperBlockEndpoint j) =
      2 * Problem520.invLog (Problem520.harperBlockEndpoint (j + 1)) := by
  rw [Problem520.invLog_harperBlockEndpoint_eq,
    Problem520.invLog_harperBlockEndpoint_eq, pow_succ]
  ring

/-- Choose the first allowed endpoint whose inverse logarithm fits the
actual gap. The endpoint stays below the given top endpoint, and incurs
at most a factor two unless it equals the lower clipping endpoint. -/
theorem candidate_exists_gap_matched_blockEndpoint
    (start stop : ℕ) (hstart : start ≤ stop) (g : ℝ)
    (hfit : Problem520.invLog (Problem520.harperBlockEndpoint stop) ≤ g) :
    ∃ j : ℕ, start ≤ j ∧ j ≤ stop ∧
      Problem520.invLog (Problem520.harperBlockEndpoint j) ≤ g ∧
      (j = start ∨ g < 2 * Problem520.invLog (Problem520.harperBlockEndpoint j)) := by
  have hex : ∃ n : ℕ, Problem520.invLog (Problem520.harperBlockEndpoint (start + n)) ≤ g := by
    refine ⟨stop - start, ?_⟩
    simpa [Nat.add_sub_of_le hstart] using hfit
  let n := Nat.find hex
  refine ⟨start + n, by omega, ?_, Nat.find_spec hex, ?_⟩
  · have hn : n ≤ stop - start := Nat.find_min' hex (by
      simpa [Nat.add_sub_of_le hstart] using hfit)
    omega
  · by_cases hn : n = 0
    · exact Or.inl (by omega)
    · right
      have hprev : ¬Problem520.invLog (Problem520.harperBlockEndpoint (start + (n - 1))) ≤ g :=
        Nat.find_min hex (by dsimp only [n]; omega)
      have heq : start + n = (start + (n - 1)) + 1 := by omega
      rw [heq, ← invLog_endpoint_succ]
      exact lt_of_not_ge hprev

/-- Every selected actual endpoint below the top cutoff has exactly the
strong prefix bound required by the literal mixed-moment theorem. -/
theorem candidate_strongScreen_implies_selected_prefix_bounds
    {ι : Type*} (start : ℕ) (W : ℝ)
    (s : Finset ℕ) (j : ι → ℕ) (hj : ∀ i, j i ∈ s)
    (t : ι → ℝ) (ω : Problem520.Omega)
    (hgood : ∀ i, ω ∈ candidateCovarianceStrongScreenEvent start (t i) W s) :
    ∀ i, Problem520.harperEulerDensity
      (Problem520.harperBlockEndpoint (start + j i)) ω (t i) ≤
        (Real.log (Problem520.harperBlockEndpoint (start + j i) : ℝ) / W ^ 1000) ^ 2 := by
  intro i
  have h := hgood i (j i) (hj i)
  have hs := Real.sq_sqrt (Problem520.harperEulerDensity_nonneg
    (Problem520.harperBlockEndpoint (start + j i)) ω (t i))
  have hnonneg := Real.sqrt_nonneg (Problem520.harperEulerDensity
    (Problem520.harperBlockEndpoint (start + j i)) ω (t i))
  nlinarith

private theorem integrable_mixed_density {ι : Type*} [Fintype ι]
    (y : ℕ) (t : ι → ℝ) :
    Integrable (fun ω => ∏ i, Problem520.harperEulerDensity y ω (t i)) Problem520.μ := by
  have hm : Measurable (fun ω => ∏ i, Problem520.harperEulerDensity y ω (t i)) :=
    Finset.measurable_prod _ fun i _ =>
      (Problem520.stronglyMeasurable_harperEulerDensity y (t i)).measurable
  apply Integrable.of_bound hm.aestronglyMeasurable
    (Problem520.harperEulerDensityUniformBound y ^ Fintype.card ι)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (prod_nonneg fun i _ =>
    Problem520.harperEulerDensity_nonneg y ω (t i))]
  simpa using Finset.prod_le_prod (s := univ)
    (g := fun _ : ι => Problem520.harperEulerDensityUniformBound y)
    (fun i _ => Problem520.harperEulerDensity_nonneg y ω (t i))
    (fun i _ => Problem520.harperEulerDensity_le_uniformBound y ω (t i))

/-- The literal strong screen now enters the actual joint Euler expectation
at independently selected scheduled cutoffs. Its residual prime exponent is
explicit, retaining both Rademacher interaction frequencies. -/
theorem candidate_integral_strongScreen_mixedEuler_le
    {ι : Type*} [Fintype ι] (y start : ℕ) (W : ℝ) (s : Finset ℕ)
    (j : ι → ℕ) (hj : ∀ i, j i ∈ s)
    (hy : ∀ i, Problem520.harperBlockEndpoint (start + j i) ≤ y)
    (t : ι → ℝ) :
    (∫ ω, {ω | ∀ i, ω ∈ candidateCovarianceStrongScreenEvent start (t i) W s}.indicator
      (fun ω => ∏ i, Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      (∏ i, (Real.log (Problem520.harperBlockEndpoint (start + j i) : ℝ) / W ^ 1000) ^ 2) *
        Real.exp (∑ p : Problem520.HarperPrimeIndex y,
          if 4 ≤ p.1 then candidateEulerMixedExponent p.1
            (Finset.univ.filter (fun i => Problem520.harperBlockEndpoint (start + j i) < p.1)) t
          else (Finset.univ.filter
            (fun i => Problem520.harperBlockEndpoint (start + j i) < p.1)).card * Real.log 4) := by
  classical
  let c : ι → ℕ := fun i => Problem520.harperBlockEndpoint (start + j i)
  let B : ι → ℝ := fun i => (Real.log (c i : ℝ) / W ^ 1000) ^ 2
  let E := {ω | ∀ i, Problem520.harperEulerDensity (c i) ω (t i) ≤ B i}
  have hE : MeasurableSet E := by
    rw [show E = ⋂ i, {ω | Problem520.harperEulerDensity (c i) ω (t i) ≤ B i} by
      ext ω; simp [E]]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (Problem520.stronglyMeasurable_harperEulerDensity (c i) (t i)).measurable measurable_const
  have hbound := candidate_integral_prefixBarrier_mixedEuler_le y c hy t B (fun i => sq_nonneg _)
  have hprod0 (ω : Problem520.Omega) : 0 ≤ ∏ i, Problem520.harperEulerDensity y ω (t i) :=
    prod_nonneg fun i _ => Problem520.harperEulerDensity_nonneg y ω (t i)
  have hleft0 : ∀ᵐ ω ∂Problem520.μ,
      0 ≤ {ω | ∀ i, ω ∈ candidateCovarianceStrongScreenEvent start (t i) W s}.indicator
        (fun ω => ∏ i, Problem520.harperEulerDensity y ω (t i)) ω :=
    Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun ω _ => hprod0 ω) ω
  apply le_trans _ hbound
  refine integral_mono_of_nonneg hleft0 ((integrable_mixed_density y t).indicator hE) ?_
  filter_upwards [] with ω
  by_cases hg : ω ∈ {ω | ∀ i, ω ∈ candidateCovarianceStrongScreenEvent start (t i) W s}
  · have he : ω ∈ E := candidate_strongScreen_implies_selected_prefix_bounds start W s j hj t ω hg
    rw [Set.indicator_of_mem hg, Set.indicator_of_mem he]
  · rw [Set.indicator_of_notMem hg]
    exact Set.indicator_nonneg (fun ω _ => hprod0 ω) ω

/-- The precise rooted residual moment from Harper's ordered-height proof:
one full Euler factor remains, while the other factors lose their selected
strong prefixes. The unremoved factor is indexed by `none`. -/
theorem candidate_integral_rooted_strongScreen_mixedEuler_le
    {ι : Type*} [Fintype ι] (y start : ℕ) (W : ℝ) (s : Finset ℕ)
    (j : ι → ℕ) (hj : ∀ i, j i ∈ s)
    (hy : ∀ i, Problem520.harperBlockEndpoint (start + j i) ≤ y)
    (t : Option ι → ℝ) :
    let c : Option ι → ℕ := fun i => i.elim 0
      (fun i => Problem520.harperBlockEndpoint (start + j i))
    (∫ ω, {ω | ∀ i : ι, ω ∈ candidateCovarianceStrongScreenEvent start (t (some i)) W s}.indicator
      (fun ω => ∏ i : Option ι, Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      (∏ i : ι, (Real.log (Problem520.harperBlockEndpoint (start + j i) : ℝ) / W ^ 1000) ^ 2) *
        Real.exp (∑ p : Problem520.HarperPrimeIndex y,
          if 4 ≤ p.1 then candidateEulerMixedExponent p.1
            (Finset.univ.filter (fun i : Option ι => c i < p.1)) t
          else (Finset.univ.filter (fun i : Option ι => c i < p.1)).card * Real.log 4) := by
  classical
  dsimp only
  let c : Option ι → ℕ := fun i => i.elim 0
    (fun i => Problem520.harperBlockEndpoint (start + j i))
  let B : Option ι → ℝ := fun i => i.elim 1
    (fun i => (Real.log (Problem520.harperBlockEndpoint (start + j i) : ℝ) / W ^ 1000) ^ 2)
  let E := {ω | ∀ i : Option ι, Problem520.harperEulerDensity (c i) ω (t i) ≤ B i}
  have hE : MeasurableSet E := by
    rw [show E = ⋂ i, {ω | Problem520.harperEulerDensity (c i) ω (t i) ≤ B i} by
      ext ω; simp [E]]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (Problem520.stronglyMeasurable_harperEulerDensity (c i) (t i)).measurable measurable_const
  have hcy : ∀ i, c i ≤ y := by intro i; cases i <;> simp [c, hy]
  have hB : ∀ i, 0 ≤ B i := by intro i; cases i <;> simp [B, sq_nonneg]
  have hbound := candidate_integral_prefixBarrier_mixedEuler_le y c hcy t B hB
  have hprod : (∏ i : Option ι, B i) =
      ∏ i : ι, (Real.log (Problem520.harperBlockEndpoint (start + j i) : ℝ) / W ^ 1000) ^ 2 := by
    rw [Fintype.prod_option]
    simp [B]
  rw [hprod] at hbound
  apply le_trans _ hbound
  have hprod0 (ω : Problem520.Omega) : 0 ≤ ∏ i, Problem520.harperEulerDensity y ω (t i) :=
    prod_nonneg fun i _ => Problem520.harperEulerDensity_nonneg y ω (t i)
  have hleft0 : ∀ᵐ ω ∂Problem520.μ,
      0 ≤ {ω | ∀ i : ι, ω ∈ candidateCovarianceStrongScreenEvent start (t (some i)) W s}.indicator
        (fun ω => ∏ i : Option ι, Problem520.harperEulerDensity y ω (t i)) ω :=
    Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun ω _ => hprod0 ω) ω
  refine integral_mono_of_nonneg hleft0 ((integrable_mixed_density y t).indicator hE) ?_
  filter_upwards [] with ω
  by_cases hg : ω ∈ {ω | ∀ i : ι, ω ∈ candidateCovarianceStrongScreenEvent start (t (some i)) W s}
  · have he : ω ∈ E := by
      intro i
      cases i with
      | none =>
          have hp : Nat.primesBelow 1 = ∅ := by decide
          simp [c, B, Problem520.harperEulerDensity, hp]
      | some i =>
          exact candidate_strongScreen_implies_selected_prefix_bounds
            start W s j hj (fun i => t (some i)) ω hg i
    rw [Set.indicator_of_mem hg, Set.indicator_of_mem he]
  · rw [Set.indicator_of_notMem hg]
    exact Set.indicator_nonneg (fun ω _ => hprod0 ω) ω

end Erdos.Problem1144
