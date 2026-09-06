import Erdos.Problem1144.HarperCandidateGaussianVarianceAsymptotics

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144

local instance candidateWhiteSelectedMatrixMeasurableSpace {ι : Type*} :
    MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

/-- The actual squarefree Gaussian crossing is reduced to covariance degree
and retained cardinality alone. The lower-energy probability, covariance
regularity, thinning and scalar Gaussian-tail asymptotics are instantiated.
The exceptional covariance event is paid by its literal probability. -/
theorem candidate_exists_squarefreeWhite_selected_crossing_of_degree :
    ∃ delta : ℝ, 0 < delta ∧ ∀ α β : ℝ, 1 < α → α ≤ 2 → α ≤ β →
      ∀ (s : Finset ℕ) (η : s → Bool), ∃ v > 0,
        ∀ γ : ℝ, 0 < γ → ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ,
        ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, ∀ u : Fin N → ℝ,
          (∀ i, u i ∈ Icc (α * T) (β * T)) →
          ∀ J : Omega → Finset (Fin N), (∀ i, MeasurableSet {ω | i ∈ J ω}) →
          ∀ D : Set Omega, MeasurableSet D → ∀ d : ℕ,
          (∀ ω ∈ D, ∀ i ∈ J ω,
            ((J ω).filter fun j => j ≠ i ∧
              (v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / 2 <
                |candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T i j|).card ≤ d) →
          (∀ ω ∈ D, T ^ γ ≤ (J ω).card / (d + 1 : ℝ)) →
          (delta - (candidateCylinderLaw s η).real Dᶜ) / 4 ≤
            ∫ ω, (multivariateGaussian (0 : EuclideanSpace ℝ (Fin N))
              (candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T)).real
                {z | ∃ i ∈ J ω, A * Real.log (1 + Real.log T) ^ k < |z i|}
              ∂candidateCylinderLaw s η := by
  obtain ⟨delta, hdelta, hvar⟩ := candidate_exists_squarefree_white_variance_lower_probability
  refine ⟨delta, hdelta, ?_⟩
  intro α β hα hα2 hαβ s η
  obtain ⟨v, hv, hvar⟩ := hvar α β hα hα2 hαβ s η
  refine ⟨v, hv, ?_⟩
  intro γ hγ A hA k
  have hscalar :=
    (candidate_tendsto_polynomialSize_gaussianPDF_loglog_threshold hv hγ A k).eventually_ge_atTop
      (Real.log 2)
  filter_upwards [hvar, hscalar, eventually_ge_atTop (1 : ℝ)] with T hvar hscalar hT1
  intro N u hwindow J hJ D hD d hdegree hcard
  let Q := candidateCylinderLaw s η
  let C : Omega → Matrix (Fin N) (Fin N) ℝ := fun ω =>
    candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T
  let vT := v * (1 + Real.log T) ^ (-(1 : ℝ) / 2)
  let K := A * Real.log (1 + Real.log T) ^ k
  let E : Set Omega := {ω | ∀ i, vT ≤ C ω i i}
  have hT : 0 < T := by linarith
  have hvT : 0 < vT := mul_pos hv (Real.rpow_pos_of_pos
    (by linarith [Real.log_nonneg hT1]) _)
  have hK : 0 ≤ K := mul_nonneg hA (pow_nonneg
    (Real.log_nonneg (by linarith [Real.log_nonneg hT1])) _)
  have hE : MeasurableSet E := candidate_measurableSet_squarefreeWhiteVariance_floor u hT vT
  have hmass : delta - Q.real Dᶜ ≤ Q.real (E ∩ D) := by
    have hvar' : delta ≤ Q.real E := hvar N u hwindow
    have hsplit := measureReal_inter_add_diff (μ := Q) (s := E) hD
    have hdiff : Q.real (E \ D) ≤ Q.real Dᶜ :=
      measureReal_mono (by intro ω hω; exact hω.2)
    linarith
  have hsize (ω : Omega) (hω : ω ∈ E ∩ D) :
      Real.log 2 ≤ (J ω).card / (d + 1 : ℝ) *
        gaussianPDFReal 0 1 (Real.sqrt 2 * (K / Real.sqrt vT) + 1) :=
    hscalar.trans (mul_le_mul_of_nonneg_right (hcard ω hω.2)
      (gaussianPDFReal_nonneg _ _ _))
  have hcross := candidate_integral_gaussian_selected_ge_quarter_of_bad_degree Q C
    (candidate_measurable_squarefreeWhiteCovariance u hT)
    (fun ω => candidate_squarefreeWhiteCovariance_posSemidef ω u hT) J hJ
    (E ∩ D) (hE.inter hD) (fun _ => d) (fun _ => vT) hK
    (fun _ _ => hvT) (fun ω hω i _ => hω.1 i)
    (fun ω hω i hi => hdegree ω hω.2 i hi) hsize
  exact (div_le_div_of_nonneg_right hmass (by norm_num : (0 : ℝ) ≤ 4)).trans hcross

end Erdos.Problem1144
