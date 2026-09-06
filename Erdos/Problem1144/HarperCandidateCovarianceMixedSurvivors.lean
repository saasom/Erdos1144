import Erdos.Problem1144.HarperCandidateCovarianceMixedExponentBounds

open Finset Set MeasureTheory
open scoped BigOperators Classical

namespace Erdos.Problem1144

noncomputable section

private theorem integrable_mixed_density {ι : Type*} [Fintype ι]
    (y : ℕ) (t : ι → ℝ) :
    Integrable (fun ω => ∏ i, Problem520.harperEulerDensity y ω (t i)) Problem520.μ := by
  have hm := Finset.measurable_prod univ (fun i _ =>
    (Problem520.stronglyMeasurable_harperEulerDensity y (t i)).measurable)
  apply Integrable.of_bound hm.aestronglyMeasurable
    (Problem520.harperEulerDensityUniformBound y ^ Fintype.card ι)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (prod_nonneg fun i _ =>
    Problem520.harperEulerDensity_nonneg y ω (t i))]
  simpa using Finset.prod_le_prod (s := univ)
    (g := fun _ : ι => Problem520.harperEulerDensityUniformBound y)
    (fun i _ => Problem520.harperEulerDensity_nonneg y ω (t i))
    (fun i _ => Problem520.harperEulerDensity_le_uniformBound y ω (t i))

private theorem prod_option_split {ι : Type*} [Fintype ι]
    (s : Finset ι) (f : Option ι → ℝ) :
    (∏ i : Option ι, f i) =
      (∏ i ∈ sᶜ, f (some i)) *
        ∏ i : Option s, f (i.map Subtype.val) := by
  classical
  rw [Fintype.prod_option, Fintype.prod_option]
  simp only [Option.map_none, Option.map_some]
  rw [Finset.prod_coe_sort s (fun i => f (some i))]
  rw [← Finset.prod_mul_prod_compl s (fun i => f (some i))]
  ring

/-- Fully removed prefixes contribute only their literal caps. Their
heights disappear from the remaining Euler expectation, even when two
such heights are arbitrarily close. The root stays unremoved. -/
theorem candidate_integral_rooted_prefixBarrier_drop_fullPrefixes
    {ι : Type*} [Fintype ι] (y : ℕ) (c : ι → ℕ) (hc : ∀ i, c i ≤ y)
    (t : Option ι → ℝ) (A : ι → ℝ) (hA : ∀ i, 0 ≤ A i) :
    let s := Finset.univ.filter (fun i => c i < y)
    (∫ ω, {ω | ∀ i : ι, Problem520.harperEulerDensity (c i) ω (t (some i)) ≤ A i}.indicator
      (fun ω => ∏ i : Option ι, Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      (∏ i ∈ sᶜ, A i) *
      ∫ ω, {ω | ∀ i : s, Problem520.harperEulerDensity (c i) ω (t (some i)) ≤ A i}.indicator
        (fun ω => ∏ i : Option s,
          Problem520.harperEulerDensity y ω (t (i.map Subtype.val))) ω ∂Problem520.μ := by
  classical
  dsimp only
  let s := Finset.univ.filter (fun i => c i < y)
  let E := {ω | ∀ i : s, Problem520.harperEulerDensity (c i) ω (t (some i)) ≤ A i}
  let F := fun ω : Problem520.Omega => ∏ i : Option s,
    Problem520.harperEulerDensity y ω (t (i.map Subtype.val))
  have hE : MeasurableSet E := by
    rw [show E = ⋂ i : s, {ω | Problem520.harperEulerDensity (c i) ω (t (some i)) ≤ A i} by
      ext ω; simp [E]]
    exact MeasurableSet.iInter fun i => measurableSet_le
      (Problem520.stronglyMeasurable_harperEulerDensity (c i) (t (some i))).measurable
      measurable_const
  have hcap0 : 0 ≤ ∏ i ∈ sᶜ, A i := Finset.prod_nonneg fun i _ => hA i
  have hF0 (ω) : 0 ≤ F ω := Finset.prod_nonneg fun i _ =>
    Problem520.harperEulerDensity_nonneg y ω _
  have hInt : Integrable (E.indicator F) Problem520.μ :=
    (integrable_mixed_density y (fun i : Option s => t (i.map Subtype.val))).indicator hE
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg
      (fun ω _ => Finset.prod_nonneg fun i _ => Problem520.harperEulerDensity_nonneg y ω (t i)) ω)
    (hInt.const_mul (∏ i ∈ sᶜ, A i)) ?_
  filter_upwards [] with ω
  by_cases hg : ω ∈ {ω | ∀ i : ι,
    Problem520.harperEulerDensity (c i) ω (t (some i)) ≤ A i}
  · have hgs : ω ∈ E := fun i => hg i
    rw [Set.indicator_of_mem hg, Set.indicator_of_mem hgs,
      prod_option_split s (fun i => Problem520.harperEulerDensity y ω (t i))]
    apply mul_le_mul_of_nonneg_right _ (hF0 ω)
    apply Finset.prod_le_prod
    · intro i _
      exact Problem520.harperEulerDensity_nonneg y ω _
    · intro i hi
      have hci : c i = y := by
        have hnot : ¬c i < y := by simpa [s] using Finset.mem_compl.mp hi
        have := hc i
        omega
      simpa only [hci] using hg i
  · rw [Set.indicator_of_notMem hg]
    exact mul_nonneg hcap0 (Set.indicator_nonneg (fun ω _ => hF0 ω) ω)

/-- At an exact top endpoint, the survivor set is exactly the indices
whose selected endpoint is strictly below the top. -/
theorem candidate_blockEndpoint_survivors_eq {ι : Type*} [Fintype ι]
    (stop : ℕ) (j : ι → ℕ) :
    Finset.univ.filter (fun i => Problem520.harperBlockEndpoint (j i) <
      Problem520.harperBlockEndpoint stop) = Finset.univ.filter (fun i => j i < stop) := by
  classical
  ext i
  simp [Problem520.strictMono_harperBlockEndpoint.lt_iff_lt]

end

end Erdos.Problem1144
