import Erdos.Problem1144.HarperCandidateGaussianLowerMaximum
import Erdos.Problem1144.HarperCandidateGaussianLowerTailAsymptotics

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace Erdos.Problem1144

/-- A growing Gaussian family with unit variances and correlations at most
one half has a uniform positive upper-maximum crossing probability for every
threshold whose square is negligible compared with the logarithmic size. -/
theorem candidate_unitGaussian_eventually_max_ge_quarter
    {α : Type*} {l : Filter α} {m : α → ℕ} {K r : α → ℝ}
    (A : (t : α) → Matrix (Fin (m t)) (Fin (m t)) ℝ)
    (hm : Tendsto (fun t => (m t : ℝ)) l atTop)
    (hKsmall : (fun t => K t ^ 2) =o[l] (fun t => Real.log (m t : ℝ)))
    (hK : ∀ᶠ t in l, 0 ≤ K t) (hr : ∀ᶠ t in l, r t ∈ Icc 0 (1 / 2))
    (hA : ∀ᶠ t in l, (A t).PosSemidef)
    (hdiag : ∀ᶠ t in l, ∀ i, A t i i = 1)
    (hcov : ∀ᶠ t in l, ∀ i j, i ≠ j → A t i j ≤ r t) :
    ∀ᶠ t in l, (1 / 4 : ℝ) ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin (m t))) (A t)).real
        {z | ∃ i, K t < z i} := by
  have hsize := (candidate_tendsto_mul_gaussianPDFReal_atTop hm hKsmall).eventually_ge_atTop
    (Real.log 2)
  filter_upwards [hsize, hK, hr, hA, hdiag, hcov] with t ht hKt hrt hAt hdt hct
  exact candidate_unitGaussian_max_ge_quarter_of_half_correlation
    (A t) hAt hdt hrt.1 hrt.2 hct hKt ht

/-- In particular correlations tending to zero give the same universal
positive crossing bound. All Gaussian comparison and tail estimates are
already instantiated; the premises here are scalar asymptotics and the
literal covariance geometry. -/
theorem candidate_unitGaussian_eventually_max_ge_quarter_of_correlation_tendsto_zero
    {α : Type*} {l : Filter α} {m : α → ℕ} {K r : α → ℝ}
    (A : (t : α) → Matrix (Fin (m t)) (Fin (m t)) ℝ)
    (hm : Tendsto (fun t => (m t : ℝ)) l atTop)
    (hKsmall : (fun t => K t ^ 2) =o[l] (fun t => Real.log (m t : ℝ)))
    (hK : ∀ᶠ t in l, 0 ≤ K t) (hr0 : ∀ᶠ t in l, 0 ≤ r t)
    (hr : Tendsto r l (𝓝 0)) (hA : ∀ᶠ t in l, (A t).PosSemidef)
    (hdiag : ∀ᶠ t in l, ∀ i, A t i i = 1)
    (hcov : ∀ᶠ t in l, ∀ i j, i ≠ j → A t i j ≤ r t) :
    ∀ᶠ t in l, (1 / 4 : ℝ) ≤
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin (m t))) (A t)).real
        {z | ∃ i, K t < z i} := by
  apply candidate_unitGaussian_eventually_max_ge_quarter A hm hKsmall hK _ hA hdiag hcov
  filter_upwards [hr0, hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with t ht hrt
  exact ⟨ht, hrt.le⟩

end Erdos.Problem1144
