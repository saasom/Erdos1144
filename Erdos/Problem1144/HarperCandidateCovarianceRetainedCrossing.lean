import Erdos.Problem1144.HarperCandidateCovarianceRetainedComparison
import Erdos.Problem1144.HarperCandidateCovarianceRetainedDegree
import Erdos.Problem1144.HarperCandidateGaussianSelectedLower

open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The literal whole-row count bounds the bad degree within any selected
finite coordinate set. The covariance threshold may be increased. -/
theorem candidate_retainedWhiteKernel_filtered_degree_le
    (start stop a depth M : ℕ) (W d : ℝ) {T B θ b v : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (hθ : 0 < θ) (hθv : θ ≤ v / 2)
    (Ngrid k degree : ℕ) (hb : b ≤ degree) {ω : Omega}
    (hω : ω ∈ candidateCovarianceDegreeControlEvent start stop a W
      ((1 / 2 : ℝ) ^ (depth + 1)) M T B d k Ngrid ((2 * Real.pi) ^ 2 * θ) b)
    (origin : ℝ) (J : Finset (Fin Ngrid)) (i : Fin Ngrid) :
    let u := fun j : Fin Ngrid => origin + j * (2 * Real.pi)
    let C := candidateWeightedGram volume
      (fun j => candidateEulerScreenWhiteKernel (Problem520.harperBlockEndpoint stop) ω
        (candidateCovarianceRetainedFrequencySet start (stop - start) depth M W
          (Finset.Icc (a - start) (stop - start)) ω) T B (u j)) (fun _ => 1)
    (J.filter fun j => j ≠ i ∧ v / 2 < |C i j|).card ≤ degree := by
  classical
  dsimp only
  let u := fun j : Fin Ngrid => origin + j * (2 * Real.pi)
  let f := fun x => candidateEulerScreenWhiteKernel (Problem520.harperBlockEndpoint stop) ω
    (candidateCovarianceRetainedFrequencySet start (stop - start) depth M W
      (Finset.Icc (a - start) (stop - start)) ω) T B x
  have hraw := candidate_retainedWhiteKernel_bad_degree_le_of_control start stop a depth M W d
    hT hTB hθ Ngrid k hω (u i) origin
  have hcard : (J.filter fun j => j ≠ i ∧ v / 2 < |∫ r, f (u i) r * f (u j) r|).card ≤
      ((Finset.range Ngrid).filter fun j : ℕ => θ ≤ |∫ r, f (u i) r *
        f (origin + j * (2 * Real.pi)) r|).card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro j hj
      have hj' := (Finset.mem_filter.mp hj).2.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, hθv.trans hj'.le⟩
    · intro j _ l _ h
      exact Fin.ext h
  have hnat : ((Finset.range Ngrid).filter fun j : ℕ => θ ≤ |∫ r, f (u i) r *
      f (origin + j * (2 * Real.pi)) r|).card ≤ degree := by
    exact_mod_cast hraw.trans hb
  simpa only [candidateWeightedGram, one_mul, f, u] using hcard.trans hnat

/-- The actual retained Euler Gaussian law crosses with probability at least
one quarter of any common event carrying its variance floor and row control.
Only the numerical Gaussian size inequality remains in this finite theorem. -/
theorem candidate_retainedEuler_crossing_ge_quarter_of_control
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (start stop a depth M : ℕ) (W d : ℝ) {T B θ b v K : ℝ}
    (hT : 0 < T) (hTB : T ≤ B) (hθ : 0 < θ) (hv : 0 < v) (hθv : θ ≤ v / 2)
    (hK : 0 ≤ K) (Ngrid k degree : ℕ) (hb : b ≤ degree) (origin : ℝ)
    (J : Omega → Finset (Fin Ngrid)) (hJ : ∀ i, MeasurableSet {ω | i ∈ J ω})
    (G : Set Omega) (hG : MeasurableSet G)
    (hcontrol : ∀ ω ∈ G, ω ∈ candidateCovarianceDegreeControlEvent start stop a W
      ((1 / 2 : ℝ) ^ (depth + 1)) M T B d k Ngrid ((2 * Real.pi) ^ 2 * θ) b)
    (hdiag : ∀ ω ∈ G, ∀ i ∈ J ω, v ≤ ∫ r,
      (candidateEulerScreenWhiteKernel (Problem520.harperBlockEndpoint stop) ω
        (candidateCovarianceRetainedFrequencySet start (stop - start) depth M W
          (Finset.Icc (a - start) (stop - start)) ω) T B
        (origin + i * (2 * Real.pi)) r) ^ 2)
    (hsize : ∀ ω ∈ G, Real.log 2 ≤ ((J ω).card : ℝ) / (degree + 1) *
      gaussianPDFReal 0 1 (Real.sqrt 2 * (K / Real.sqrt v) + 1)) :
    Q.real G / 4 ≤ ∫ ω, candidateRetainedEulerWhiteCrossing
      (Problem520.harperBlockEndpoint stop) start (stop - start) depth M W
      (Finset.Icc (a - start) (stop - start))
      (fun i : Fin Ngrid => origin + i * (2 * Real.pi)) T B J K ω ∂Q := by
  let S := candidateCovarianceRetainedFrequencySet start (stop - start) depth M W
    (Finset.Icc (a - start) (stop - start))
  let f := fun (i : Fin Ngrid) ω => candidateEulerScreenWhiteKernel
    (Problem520.harperBlockEndpoint stop) ω (S ω) T B (origin + i * (2 * Real.pi))
  have hf (i : Fin Ngrid) : Measurable (Function.uncurry (f i)) :=
    candidate_measurable_eulerScreenWhiteKernel_joint _ S
      (candidate_measurableSet_retainedFrequencyGraph _ _ _ _ _ _) T B _
  have hf2 (ω : Omega) (i : Fin Ngrid) : MemLp (f i ω) 2 :=
    candidate_memLp_eulerScreenWhiteKernel _ ω
      (candidate_measurableSet_retainedFrequencySet _ _ _ _ _ _ ω) M
      (candidate_retainedFrequencySet_subset_band _ _ _ _ _ _ ω le_rfl) B _ hT
  let C := fun ω => candidateWeightedGram volume (fun i => f i ω) (fun _ => 1)
  have hpos (ω : Omega) : (C ω).PosSemidef := candidateWeightedGram_posSemidef _ _ _
    (fun i j => by simpa only [one_mul] using (hf2 ω i).integrable_mul (hf2 ω j))
    (ae_of_all _ fun _ => Or.inl zero_le_one)
  apply candidate_integral_gaussian_selected_ge_quarter_of_bad_degree Q C
    (candidate_measurable_random_gram volume f hf) hpos J hJ G hG
    (fun _ => degree) (fun _ => v) hK (fun _ _ => hv)
  · intro ω hω i hi
    simpa only [C, candidateWeightedGram, one_mul, ← sq, f, S] using hdiag ω hω i hi
  · intro ω hω i _
    exact candidate_retainedWhiteKernel_filtered_degree_le start stop a depth M W d hT hTB hθ hθv
      Ngrid k degree hb (hcontrol ω hω) origin (J ω) i
  · exact hsize

end
end Erdos.Problem1144
