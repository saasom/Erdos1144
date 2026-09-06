import Erdos.Problem1144.HarperCandidateCovariancePairedCellIntegrability

open MeasureTheory Finset Set
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The numerical reflected-cell bound, including all sign patterns,
permutations, Cauchy denominators, and the actual screened gap saving. -/
def candidateCovarianceReflectedCellBound (C D : ℝ) (start stop a k : ℕ)
    (W M η : ℝ) : ℝ :=
  let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
  let L := Real.log (Problem520.harperBlockEndpoint stop : ℝ)
  let δ := Problem520.invLog (Problem520.harperBlockEndpoint (a - 1))
  let U := A * M + 3 * Real.log (1 + L * M)
  ((2 : ℝ) ^ (2 * k) * (Nat.factorial (2 * k) : ℝ)) *
    (((4 : ℝ) ^ (2 * k) * candidateCovarianceGapMomentFactor C D start (2 * k) *
      L ^ (2 * k) / Real.log 3) *
      (W ^ (12 * (2 * k - 1)) * M *
        (U ^ (2 * k - 1) / W ^ (2012 * k) +
          2 * η * (2 * k - 1 : ℕ) * (A + 2 / δ) * U ^ (2 * k - 2))))

/-- Averaging the literal reflection/permutation reduction and inserting the
ordered arithmetic moment gives a numerical bound with exactly
`2^(2k) (2k)!` symmetry terms. Reflected signs need not be balanced. -/
theorem candidate_exists_screened_squaredDensity_resonance_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ k : ℕ, 1 ≤ k → ∀ start stop a : ℕ, J ≤ start → start < a → a ≤ stop →
    ∀ W : ℝ, 1 ≤ W → ∀ M : ℝ, 0 ≤ M →
      M ≤ candidateCovarianceHeightWindow start / 2 →
    ∀ η : ℝ, 0 ≤ η → ∀ m : ℤ,
    (∫ ω, (∫ x in {x | |candidateRowPowerFrequency id x - m| ≤ η},
      candidateRowProduct (candidateEulerBandSquaredWeight
        (Problem520.harperBlockEndpoint stop) ω) x
      ∂candidateRowPowerMeasure ((volume.restrict (Icc (-M) M)).restrict
        (candidateCovarianceScreenedHeightSet start (stop - start) W M
          (Finset.Icc (a - start) (stop - start)) ω)) k) ∂Problem520.μ) ≤
      candidateCovarianceReflectedCellBound C D start stop a k W M η := by
  classical
  obtain ⟨C, D, hC, hD, J, hordered⟩ :=
    candidate_exists_ordered_screened_euler_resonance_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro k hk start stop a hJ hsa has W hW M hM hwindow η hη m
  let Y := Problem520.harperBlockEndpoint stop
  let A := Real.log (Problem520.harperBlockEndpoint start : ℝ)
  let L := Real.log (Y : ℝ)
  let δ := Problem520.invLog (Problem520.harperBlockEndpoint (a - 1))
  let U := A * M + 3 * Real.log (1 + L * M)
  let Q := ((4 : ℝ) ^ (k + k) * candidateCovarianceGapMomentFactor C D start (k + k) *
      L ^ (k + k) / Real.log 3) *
      (W ^ (12 * (2 * k - 1)) * M *
        (U ^ (2 * k - 1) / W ^ (2012 * k) +
          2 * η * (2 * k - 1 : ℕ) * (A + 2 / δ) * U ^ (2 * k - 2)))
  let O (b : Fin (k + k) → Bool) (p : Equiv.Perm (Fin (k + k)))
      (ω : Problem520.Omega) : ℝ :=
    ∫ x in candidateCovarianceHeightCell start (stop - start) W M
        (Finset.Icc (a - start) (stop - start)) ω
        (fun i => candidateCovarianceReflectedSigns (candidateCovarianceInitialSigns k) b (p i))
        (m : ℝ) η ∩ candidateCovarianceOrderedPositiveHeights (k + k),
      ∏ i, candidateEulerBandSquaredWeight Y ω (x i)
  have hOi (b : Fin (k + k) → Bool) (p : Equiv.Perm (Fin (k + k))) :
      Integrable (O b p) Problem520.μ :=
    candidate_integrable_ordered_screened_euler_integral Y start (stop - start) W M
      (Finset.Icc (a - start) (stop - start)) _ (m : ℝ) η
  have hO (b : Fin (k + k) → Bool) (p : Equiv.Perm (Fin (k + k))) :
      (∫ ω, O b p ω ∂Problem520.μ) ≤ Q := by
    have hn : (2 * k - 1) + 1 = k + k := by omega
    have he : 2 * k - 1 - 1 = 2 * k - 2 := by omega
    let P (q : ℕ) : Prop := ∀ σ : Fin q → ℤ, (∀ i, σ i = 1 ∨ σ i = -1) →
      (∫ ω, (∫ x in candidateCovarianceHeightCell start (stop - start) W M
          (Finset.Icc (a - start) (stop - start)) ω σ (m : ℝ) η ∩
          candidateCovarianceOrderedPositiveHeights q,
        ∏ i, candidateEulerBandSquaredWeight Y ω (x i)) ∂Problem520.μ) ≤ Q
    have hP : P ((2 * k - 1) + 1) := by
      intro σ hσ
      have hb := hordered (2 * k - 1) start stop a hJ hsa has (by omega)
        W hW M hM hwindow σ hσ k (by omega) η hη m
      apply hb.trans_eq
      dsimp only [Q, U, δ, A, L, Y]
      rw [hn, he]
    have hP' : P (k + k) := hn ▸ hP
    exact hP'
      (fun i => candidateCovarianceReflectedSigns (candidateCovarianceInitialSigns k) b (p i))
      (candidate_covariance_effectiveRowSigns_unit k b p)
  have hsum : Integrable (fun ω =>
      ∑ b : Fin (k + k) → Bool, ∑ p : Equiv.Perm (Fin (k + k)), O b p ω)
      Problem520.μ := by
    exact integrable_finset_sum _ (fun b _ => integrable_finset_sum _ (fun p _ => hOi b p))
  have havg : (∫ ω, (∫ x in {x | |candidateRowPowerFrequency id x - m| ≤ η},
      candidateRowProduct (candidateEulerBandSquaredWeight Y ω) x
      ∂candidateRowPowerMeasure ((volume.restrict (Icc (-M) M)).restrict
        (candidateCovarianceScreenedHeightSet start (stop - start) W M
          (Finset.Icc (a - start) (stop - start)) ω)) k) ∂Problem520.μ) ≤
      ∫ ω, (∑ b : Fin (k + k) → Bool,
        ∑ p : Equiv.Perm (Fin (k + k)), O b p ω) ∂Problem520.μ := by
    apply integral_mono
      (candidate_integrable_screened_squaredDensity_cell start stop a (by omega) W M k m η)
      hsum
    intro ω
    exact candidate_integral_row_screenedSquaredDensity_le_reflected_ordered Y ω k
      start (stop - start) W M (Finset.Icc (a - start) (stop - start)) (m : ℝ) η
  apply havg.trans
  rw [integral_finset_sum _ (fun b _ =>
    integrable_finset_sum _ (fun p _ => hOi b p))]
  simp_rw [integral_finset_sum _ (fun p _ => hOi _ p)]
  calc
    _ ≤ ∑ _b : Fin (k + k) → Bool, ∑ _p : Equiv.Perm (Fin (k + k)), Q := by
      exact Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun p _ => hO b p
    _ = candidateCovarianceReflectedCellBound C D start stop a k W M η := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_perm,
        Nat.cast_pow, Nat.cast_ofNat]
      dsimp only [candidateCovarianceReflectedCellBound, Q, U, δ, A, L, Y]
      rw [show k + k = 2 * k by omega]
      ring

/-- The actual averaged paired Euler cell has a fully numerical bound. This
retains the exact logarithmic partner-contraction loss and enlarged width
`ε + 2 k d`, with the same inclusive D-star/strong screen through `B_stop`. -/
theorem candidate_exists_screened_pairedEuler_resonance_bound :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∃ J : ℕ,
    ∀ k : ℕ, 1 ≤ k → ∀ start stop a : ℕ, J ≤ start → start < a → a ≤ stop →
    ∀ W : ℝ, 1 ≤ W → ∀ M : ℝ, 0 ≤ M →
      M ≤ candidateCovarianceHeightWindow start / 2 →
    ∀ T B d : ℝ, 0 < T → T ≤ B → 0 ≤ d →
    ∀ ε : ℝ, 0 ≤ ε → ∀ m : ℤ,
    (∫ ω, (∫ z in {z | |candidateRowPowerFrequency Prod.snd z - m| ≤ ε},
      candidateRowProduct (candidateEulerBandRowWeight
        (Problem520.harperBlockEndpoint stop) ω T B) z
      ∂candidateRowPowerMeasure
        (((volume.restrict (Icc (-M) M)).prod (volume.restrict (Icc (-M) M))).restrict
          (candidateRowPairDomain
            (candidateCovarianceScreenedHeightSet start (stop - start) W M
              (Finset.Icc (a - start) (stop - start)) ω) d)) k) ∂Problem520.μ) ≤
      (2 * (Real.log (B / T) + 2) * Real.log (1 + T * d) / T) ^ (2 * k) *
        candidateCovarianceReflectedCellBound C D start stop a k W M (ε + 2 * k * d) := by
  obtain ⟨C, D, hC, hD, J, hbound⟩ :=
    candidate_exists_screened_squaredDensity_resonance_bound
  refine ⟨C, D, hC, hD, J, ?_⟩
  intro k hk start stop a hJ hsa has W hW M hM hwindow T B d hT hTB hd ε hε m
  let R := 2 * (Real.log (B / T) + 2) * Real.log (1 + T * d) / T
  have hR : 0 ≤ R := (candidateCovarianceLocalKernelMass_nonneg T B d).trans
    (candidate_local_whiteKernel_mass_le hT hTB hd)
  have hi := candidate_integrable_screened_squaredDensity_cell start stop a
    (by omega) W M k m (ε + 2 * k * d)
  have havg := integral_mono
    (candidate_integrable_screened_pairedEuler_cell start stop a (by omega) W M T B d k m ε)
    (hi.const_mul (R ^ (2 * k)))
    (fun ω => candidate_integral_resonant_paired_euler_contraction_log
      (Problem520.harperBlockEndpoint stop) ω M hT hTB hd
      (candidate_measurableSet_screenedHeightSet start (stop - start) W M
        (Finset.Icc (a - start) (stop - start)) ω) k m ε)
  rw [integral_const_mul] at havg
  exact havg.trans (mul_le_mul_of_nonneg_left
    (hbound k hk start stop a hJ hsa has W hW M hM hwindow
      (ε + 2 * k * d) (by positivity) m) (pow_nonneg hR _))

end
end Erdos.Problem1144
