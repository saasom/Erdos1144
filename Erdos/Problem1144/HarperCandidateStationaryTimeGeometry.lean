import Erdos.Problem1144.HarperCandidateStationaryGaussianComparison
import Erdos.Problem1144.HarperCandidateStationaryTailCovariance
import Erdos.Problem1144.HarperCandidatePrimeWhiteComparisonCrossing

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators
namespace Erdos.Problem1144
noncomputable section

/-- The complete stationary covariance retained on prime times at least T. -/
def candidateStationaryTruncatedCovariance {ι : Type*}
    (ω : Omega) (u : ι → ℝ) (T W : ℝ) : Matrix ι ι ℝ :=
  candidateWeightedGram (volume.restrict (Ici T))
    (fun i v => harperCandidateLogProcess ω (u i - v) *
      Real.exp (-(W / T) * (u i - v))) (fun _ => 1 / T)

private theorem white_kernel_eq (sf : Bool) (ω : Omega) (u T : ℝ) :
    candidateComparisonWhite sf ω u T =
      (Ioi T).indicator (fun v => candidateComparisonProcess sf ω (u - v) / Real.sqrt v) := by
  cases sf <;> rfl

/-- Both literal white kernels have exactly the reciprocal-time covariance. -/
theorem candidate_comparisonWhite_gram_eq_whiteCovariance
    {ι : Type*} (sf : Bool) (ω : Omega) (u : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    candidateWeightedGram volume (fun i => candidateComparisonWhite sf ω (u i) T)
      (fun _ => 1) = candidateWhiteCovariance (candidateComparisonProcess sf ω) u T := by
  ext i j
  unfold candidateWhiteCovariance candidateWeightedGram
  rw [integral_Ici_eq_integral_Ioi, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with v
  by_cases hv : T < v
  · simp only [white_kernel_eq,
      indicator_of_mem (show v ∈ Ioi T from hv), one_mul]
    calc
      _ = (candidateComparisonProcess sf ω (u i - v) *
        candidateComparisonProcess sf ω (u j - v)) / (Real.sqrt v) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt (hT.trans hv).le]; ring
  · simp [white_kernel_eq, hv]

/-- Both actual white covariance families are positive semidefinite. -/
theorem candidate_comparisonWhiteCovariance_posSemidef {ι : Type*} [Finite ι]
    (sf : Bool) (ω : Omega) (u : ι → ℝ) {T : ℝ} (hT : 0 < T) :
    (candidateWhiteCovariance (candidateComparisonProcess sf ω) u T).PosSemidef := by
  rw [← candidate_comparisonWhite_gram_eq_whiteCovariance sf ω u hT]
  apply candidateWeightedGram_posSemidef _ _ _
  · intro i j
    simpa only [one_mul] using (candidate_memLp_comparisonWhite sf ω (u i) hT).integrable_mul
      (candidate_memLp_comparisonWhite sf ω (u j) hT)
  · exact ae_of_all _ fun _ => Or.inl zero_le_one

private theorem white_entry_integrable (sf : Bool) (ω : Omega) (u v : ℝ)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x => (1 / x) * candidateComparisonProcess sf ω (u - x) *
      candidateComparisonProcess sf ω (v - x)) (Ici T) := by
  apply (integrableOn_Ici_iff_integrableOn_Ioi (μ := volume)).mpr
  have hi := ((candidate_memLp_comparisonWhite sf ω u hT).integrable_mul
    (candidate_memLp_comparisonWhite sf ω v hT)).integrableOn (s := Ioi T)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [Pi.mul_apply, white_kernel_eq, indicator_of_mem hx]
  rw [show candidateComparisonProcess sf ω (u - x) / Real.sqrt x *
      (candidateComparisonProcess sf ω (v - x) / Real.sqrt x) =
      (candidateComparisonProcess sf ω (u - x) * candidateComparisonProcess sf ω (v - x)) /
        (Real.sqrt x) ^ 2 by ring, Real.sq_sqrt (hT.trans hx).le]
  ring

private theorem damped_entry_integrable {a : ℝ → ℝ} {σ : ℝ}
    (ha : MemLp (fun t => Real.exp (-σ * t) * a t) 2 volume) (u v L : ℝ) :
    Integrable (fun x => (1 / L) * (a (u - x) * Real.exp (-σ * (u - x))) *
      (a (v - x) * Real.exp (-σ * (v - x)))) := by
  have hu := ha.comp_measurePreserving (volume.measurePreserving_sub_left u)
  have hv := ha.comp_measurePreserving (volume.measurePreserving_sub_left v)
  convert (hu.integrable_mul hv).const_mul (1 / L) using 1
  funext x
  dsimp only [Function.comp_def, Pi.mul_apply]
  ring

private theorem shifted_entry_integrable {a : ℝ → ℝ} {σ : ℝ}
    (ha : MemLp (fun t => Real.exp (-σ * t) * a t) 2 volume) (u v L t₀ : ℝ) :
    Integrable (fun x => Real.exp (2 * σ * (x - t₀)) / L * a (u - x) * a (v - x)) := by
  have h := (damped_entry_integrable ha u v L).const_mul (Real.exp (σ * (u + v - 2 * t₀)))
  convert h using 1
  funext x
  have he : Real.exp (σ * (u + v - 2 * t₀)) * Real.exp (-σ * (u - x)) *
      Real.exp (-σ * (v - x)) = Real.exp (2 * σ * (x - t₀)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (σ * (u + v - 2 * t₀)) * Real.exp (-σ * (u - x)) *
      Real.exp (-σ * (v - x))) / L * a (u - x) * a (v - x) := by rw [he]
    _ = _ := by ring

/-- Stationary time covariance depends only on coordinate differences;
the whole grid may be translated without changing its Gaussian law. -/
theorem candidateStationaryCovariance_translate {ι : Type*}
    (a : ℝ → ℝ) (u : ι → ℝ) (σ L b : ℝ) :
    candidateStationaryCovariance a (fun i => u i + b) σ L =
      candidateStationaryCovariance a u σ L := by
  ext i j
  unfold candidateStationaryCovariance candidateWeightedGram
  have h := integral_add_right_eq_self (μ := volume)
    (fun x => (1 / L) * (a (u i - x) * Real.exp (-σ * (u i - x))) *
      (a (u j - x) * Real.exp (-σ * (u j - x)))) (-b)
  convert h using 1
  congr 1
  funext x
  congr 3 <;> ring

/-- The first time-domain PSD comparison holds almost surely for the
actual squarefree process, with all entry-integrability premises discharged. -/
theorem candidateCylinderLaw_ae_squarefree_white_stationary_domination
    (s : Finset ℕ) (η : s → Bool) {σ V : ℝ} (hσ : 0 < σ) (hV : 0 < V) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ (m : ℕ) (u : Fin m → ℝ),
      (candidateStationaryCovariance (harperCandidateSquarefreeLogProcess ω) u σ V -
        candidateCovarianceDiagonal (fun i => Real.exp (-σ * (u i - V)))
          (candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u V)).PosSemidef := by
  filter_upwards [candidateCylinderLaw_ae_damped_L1_L2 s η hσ] with ω hω
  intro m u
  apply candidate_stationary_squarefree_covariance_domination _ u hσ.le hV
  · intro i j
    convert (shifted_entry_integrable hω.2.2 (u i) (u j) V V).const_mul
      (Real.exp (-σ * (u i - V)) * Real.exp (-σ * (u j - V))) using 1
    funext x
    ring
  · intro i j
    have hi : Integrable (fun x => (1 / x) * harperCandidateSquarefreeLogProcess ω (u i - x) *
      harperCandidateSquarefreeLogProcess ω (u j - x)) (volume.restrict (Ici V)) :=
        white_entry_integrable true ω (u i) (u j) hV
    change Integrable _ (volume.restrict (Ici V))
    convert hi.const_mul
      (Real.exp (-σ * (u i - V)) * Real.exp (-σ * (u j - V))) using 1
    funext x
    change _ = _ * ((1 / x) * harperCandidateSquarefreeLogProcess ω (u i - x) *
      harperCandidateSquarefreeLogProcess ω (u j - x))
    ring

/-- The complete stationary matrix is exactly retained plus omitted
covariance, and both pieces are PSD almost surely on every fixed cylinder. -/
theorem candidateCylinderLaw_ae_complete_stationary_split
    (s : Finset ℕ) (η : s → Bool) {T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ (m : ℕ) (u : Fin m → ℝ),
      candidateStationaryCovariance (harperCandidateLogProcess ω) u (W / T) T =
        candidateStationaryTruncatedCovariance ω u T W +
        candidateStationaryExtensionCovariance ω u T W ∧
      (candidateStationaryTruncatedCovariance ω u T W).PosSemidef ∧
      (candidateStationaryExtensionCovariance ω u T W).PosSemidef := by
  filter_upwards [candidateCylinderLaw_ae_damped_L1_L2 s η (div_pos hW hT)] with ω hω
  intro m u
  have hi (i j : Fin m) := damped_entry_integrable hω.1.2 (u i) (u j) T
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [candidateStationaryCovariance, candidateStationaryTruncatedCovariance,
      candidateStationaryExtensionCovariance, candidateWeightedGram, Matrix.add_apply]
    simpa only [compl_Ici] using (integral_add_compl measurableSet_Ici (hi i j)).symm
  · exact candidateWeightedGram_posSemidef _ _ _ (fun i j => (hi i j).integrableOn)
      (ae_of_all _ fun _ => Or.inl (by positivity))
  · exact candidateWeightedGram_posSemidef _ _ _ (fun i j => (hi i j).integrableOn)
      (ae_of_all _ fun _ => Or.inl (by positivity))

/-- The last time-domain comparison holds almost surely for the actual
complete process, including the exact diagonal normalization. -/
theorem candidateCylinderLaw_ae_complete_stationary_white_domination
    (s : Finset ℕ) (η : s → Bool) {T W : ℝ} (hT : 0 < T) (hW : 0 < W) :
    ∀ᵐ ω ∂candidateCylinderLaw s η, ∀ (m : ℕ) (u : Fin m → ℝ) (β t₀ D : ℝ),
      (∀ i, u i ≤ β * T) → (∀ i, u i ≤ t₀ + D) →
      ((β * Real.exp (2 * (W / T) * D)) •
        candidateWhiteCovariance (harperCandidateLogProcess ω) u T -
        candidateCovarianceDiagonal (fun i => Real.exp ((W / T) * (u i - t₀)))
          (candidateStationaryTruncatedCovariance ω u T W)).PosSemidef := by
  filter_upwards [candidateCylinderLaw_ae_damped_L1_L2 s η (div_pos hW hT)] with ω hω
  intro m u β t₀ D hβ hD
  rw [candidateStationaryTruncatedCovariance, candidate_truncated_covariance_rescale_eq]
  apply candidate_complete_white_covariance_domination _ u hT (div_pos hW hT).le hβ hD
  · intro t ht
    simp [harperCandidateLogProcess, not_le.mpr ht]
  · intro i j
    exact (shifted_entry_integrable hω.1.2 (u i) (u j) T t₀).integrableOn
  · intro i j
    exact white_entry_integrable false ω (u i) (u j) hT

end
end Erdos.Problem1144
