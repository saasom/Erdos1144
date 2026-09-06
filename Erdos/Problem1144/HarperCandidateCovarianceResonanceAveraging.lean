import Erdos.Problem1144.HarperCandidateCovarianceResonanceLabels

open MeasureTheory Set Finset
open scoped BigOperators

namespace Erdos.Problem1144

/-- A frequency window holding almost everywhere suffices to retain the
finite integer-label range. This applies directly to the actual restricted
row measure, whose full ambient coordinate space is unbounded. -/
theorem candidate_integral_ae_bounded_resonance_le_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (hXm : Measurable X) (R e : ℝ)
    (hR : ∀ᵐ ω ∂μ, |X ω| ≤ R)
    (f : Ω → ℝ) (hf : Integrable f μ) (hf0 : ∀ ω, 0 ≤ f ω) :
    (∫ ω in {ω | candidateIntegerDistance (X ω) ≤ e}, f ω ∂μ) ≤
      ∑ m ∈ candidateCovarianceResonanceLabels 1 R e,
        ∫ ω in {ω | |X ω - (m : ℝ)| ≤ e}, f ω ∂μ := by
  classical
  let E := {ω | candidateIntegerDistance (X ω) ≤ e}
  let C := fun m : ℤ => {ω | |X ω - (m : ℝ)| ≤ e}
  let L := candidateCovarianceResonanceLabels 1 R e
  have hE : MeasurableSet E := measurableSet_le
    (candidateIntegerDistance_lipschitz.continuous.measurable.comp hXm) measurable_const
  have hC (m : ℤ) : MeasurableSet (C m) :=
    measurableSet_le (hXm.sub_const _).abs measurable_const
  have hCi (m : ℤ) : Integrable ((C m).indicator f) μ := hf.indicator (hC m)
  have hC0 (m : ℤ) (ω : Ω) : 0 ≤ (C m).indicator f ω :=
    indicator_nonneg (fun x _ => hf0 x) ω
  have hpoint : ∀ᵐ ω ∂μ, E.indicator f ω ≤ ∑ m ∈ L, (C m).indicator f ω := by
    filter_upwards [hR] with ω hωR
    by_cases hω : ω ∈ E
    · obtain ⟨m, hm⟩ := (candidateIntegerDistance_le_iff (X ω) e).mp hω
      have hmL : m ∈ L := by
        rw [candidate_mem_resonanceLabels_iff]
        simp only [Nat.cast_one, one_mul]
        calc
          |(m : ℝ)| = |X ω - (X ω - (m : ℝ))| := by ring_nf
          _ ≤ |X ω| + |X ω - (m : ℝ)| := abs_sub _ _
          _ ≤ R + e := add_le_add hωR hm
      rw [indicator_of_mem hω]
      calc
        f ω = (C m).indicator f ω :=
          (indicator_of_mem (show ω ∈ C m from hm) f).symm
        _ ≤ ∑ j ∈ L, (C j).indicator f ω :=
          Finset.single_le_sum (fun j _ => hC0 j ω) hmL
    · rw [indicator_of_notMem hω]
      exact Finset.sum_nonneg fun m _ => hC0 m ω
  change (∫ ω in E, f ω ∂μ) ≤ ∑ m ∈ L, ∫ ω in C m, f ω ∂μ
  rw [← integral_indicator hE]
  calc
    _ ≤ ∫ ω, ∑ m ∈ L, (C m).indicator f ω ∂μ :=
      integral_mono_ae (hf.indicator hE) (integrable_finset_sum L fun m _ => hCi m) hpoint
    _ = ∑ m ∈ L, ∫ ω, (C m).indicator f ω ∂μ :=
      integral_finset_sum L fun m _ => hCi m
    _ = _ := Finset.sum_congr rfl fun m _ => integral_indicator (hC m)

end Erdos.Problem1144
