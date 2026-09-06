import Erdos.Problem1144.HarperCandidateSpectralRegionMoments

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos.Problem1144
noncomputable section

/-- The frequency radii below the fixed high-frequency cutoff `1/8`. -/
def candidateSpectralDyadicRadius (j : ℕ) : ℝ := (1 / 8) * (1 / 2 : ℝ) ^ j

theorem candidateSpectralDyadicRadius_pos (j : ℕ) :
    0 < candidateSpectralDyadicRadius j := by unfold candidateSpectralDyadicRadius; positivity

theorem candidateSpectralDyadicRadius_succ (j : ℕ) :
    candidateSpectralDyadicRadius (j + 1) = candidateSpectralDyadicRadius j / 2 := by
  unfold candidateSpectralDyadicRadius
  rw [pow_succ]
  ring

theorem candidateSpectralDyadicRadius_antitone : Antitone candidateSpectralDyadicRadius := by
  apply antitone_nat_of_succ_le
  intro j
  rw [candidateSpectralDyadicRadius_succ]
  linarith [candidateSpectralDyadicRadius_pos j]

theorem candidateSpectralDyadicRadius_le (j : ℕ) :
    candidateSpectralDyadicRadius j ≤ 1 / 8 := by
  simpa [candidateSpectralDyadicRadius] using
    candidateSpectralDyadicRadius_antitone (Nat.zero_le j)

theorem candidate_exists_spectral_dyadic_radius {σ : ℝ}
    (hσ : σ ∈ Ioc (0 : ℝ) (1 / 8)) :
    ∃ n : ℕ, candidateSpectralDyadicRadius n / 2 < σ ∧
      σ ≤ candidateSpectralDyadicRadius n := by
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one
    (by linarith [hσ.1] : 0 < 8 * σ) (by linarith [hσ.2] : 8 * σ ≤ 1)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n, ?_, ?_⟩ <;> unfold candidateSpectralDyadicRadius
  · rw [pow_succ] at hnlo
    linarith
  · linarith

/-- The positive height saving from the actual Euler interval estimate is
summable over the entire dyadic frequency grid. -/
theorem candidate_summable_spectral_dyadic_radius :
    Summable fun j => candidateSpectralDyadicRadius j ^ (1 / 16 : ℝ) := by
  have h : Summable fun j : ℕ => ((1 / 2 : ℝ) ^ (1 / 16 : ℝ)) ^ j :=
    summable_geometric_of_lt_one (by positivity)
      (Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num))
  convert h.mul_left ((1 / 8 : ℝ) ^ (1 / 16 : ℝ)) using 1
  ext j
  rw [candidateSpectralDyadicRadius,
    Real.mul_rpow (by norm_num) (pow_nonneg (by norm_num) _),
    Real.rpow_pow_comm (by norm_num)]

private theorem integral_cover_le {f : ℝ → ℝ} (hi : Integrable f)
    (hf : ∀ t, 0 ≤ f t) {A B C : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hcover : A ⊆ B ∪ C) :
    (∫ t in A, f t) ≤ (∫ t in B, f t) + ∫ t in C, f t := by
  rw [← integral_indicator hA, ← integral_indicator hB, ← integral_indicator hC,
    ← integral_add (hi.indicator hB) (hi.indicator hC)]
  apply integral_mono (hi.indicator hA) ((hi.indicator hB).add (hi.indicator hC))
  intro t
  change A.indicator f t ≤ B.indicator f t + C.indicator f t
  have hb : 0 ≤ B.indicator f t := Set.indicator_nonneg (fun x _ => hf x) t
  have hc : 0 ≤ C.indicator f t := Set.indicator_nonneg (fun x _ => hf x) t
  by_cases ht : t ∈ A
  · rw [Set.indicator_of_mem ht]
    rcases hcover ht with htB | htC
    · rw [Set.indicator_of_mem htB]
      linarith
    · rw [Set.indicator_of_mem htC]
      linarith
  · rw [Set.indicator_of_notMem ht]
    linarith

private theorem integral_symmetric_split {f : ℝ → ℝ} (hi : Integrable f)
    (hf : ∀ t, 0 ≤ f t) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in Icc (-b) b, f t) ≤
      (∫ t in Icc (-a) a, f t) +
        ((∫ t in Icc a b, f t) + ∫ t in Icc (-b) (-a), f t) := by
  have h1 := integral_cover_le hi hf measurableSet_Icc measurableSet_Icc measurableSet_Icc
    (A := Icc (-b) b) (B := Icc (-b) (-a)) (C := Icc (-a) b) (by
      intro t ht
      by_cases ht' : t ≤ -a
      · exact Or.inl ⟨ht.1, ht'⟩
      · exact Or.inr ⟨le_of_lt (lt_of_not_ge ht'), ht.2⟩)
  have h2 := integral_cover_le hi hf measurableSet_Icc measurableSet_Icc measurableSet_Icc
    (A := Icc (-a) b) (B := Icc (-a) a) (C := Icc a b) (by
      intro t ht
      by_cases ht' : t ≤ a
      · exact Or.inl ⟨ht.1, ht'⟩
      · exact Or.inr ⟨le_of_lt (lt_of_not_ge ht'), ht.2⟩)
  linarith

/-- The literal whole-frequency energy is bounded by one high-frequency
region, one central interval, and the actual finite dyadic bands. -/
theorem candidate_finiteSpectralEnergy_le_dyadic_cover (y n : ℕ) {σ : ℝ}
    (hσ : σ ∈ Ioc (0 : ℝ) (1 / 2)) (ω : Problem520.Omega) :
    candidateFiniteSpectralEnergy y σ ω ≤
      candidateFiniteSpectralRegionEnergy y σ {t | (1 / 8 : ℝ) ≤ |t|} ω +
      candidateFiniteSpectralRegionEnergy y σ
        (Icc (-candidateSpectralDyadicRadius n) (candidateSpectralDyadicRadius n)) ω +
      ∑ j ∈ Finset.range n,
        (candidateFiniteSpectralRegionEnergy y σ
          (Icc (candidateSpectralDyadicRadius (j + 1)) (candidateSpectralDyadicRadius j)) ω +
         candidateFiniteSpectralRegionEnergy y σ
          (Icc (-candidateSpectralDyadicRadius j) (-candidateSpectralDyadicRadius (j + 1))) ω) := by
  let f : ℝ → ℝ := fun t => candidateCompleteZetaWeight σ t *
    harperRankinEulerDensity y (2 * σ) ω t
  have hi : Integrable f := candidate_integrable_weight_mul_euler y (2 * σ) ω
    (candidate_integrable_complete_zeta_weight hσ)
  have hf (t : ℝ) : 0 ≤ f t := mul_nonneg (candidateCompleteZetaWeight_nonneg σ t)
    (harperRankinEulerDensity_nonneg y (2 * σ) ω t)
  have hd : ∀ k : ℕ, (∫ t in Icc (-(1 / 8 : ℝ)) (1 / 8), f t) ≤
      (∫ t in Icc (-candidateSpectralDyadicRadius k) (candidateSpectralDyadicRadius k), f t) +
      ∑ j ∈ Finset.range k,
        ((∫ t in Icc (candidateSpectralDyadicRadius (j + 1)) (candidateSpectralDyadicRadius j), f t) +
         ∫ t in Icc (-candidateSpectralDyadicRadius j) (-candidateSpectralDyadicRadius (j + 1)), f t) := by
    intro k
    induction k with
    | zero => simp [candidateSpectralDyadicRadius]
    | succ k ih =>
      rw [Finset.sum_range_succ]
      have hs := integral_symmetric_split hi hf (candidateSpectralDyadicRadius_pos (k + 1)).le
        (candidateSpectralDyadicRadius_antitone (Nat.le_succ k))
      linarith
  have hh := integral_cover_le hi hf MeasurableSet.univ
    (measurableSet_le measurable_const (by fun_prop)) measurableSet_Icc
    (A := univ) (B := {t | (1 / 8 : ℝ) ≤ |t|}) (C := Icc (-(1 / 8 : ℝ)) (1 / 8)) (by
      intro t _
      by_cases ht : (1 / 8 : ℝ) ≤ |t|
      · exact Or.inl ht
      · exact Or.inr (abs_le.mp (le_of_lt (lt_of_not_ge ht))))
  rw [setIntegral_univ] at hh
  have h := mul_le_mul_of_nonneg_left (hh.trans (add_le_add le_rfl (hd n))) hσ.1.le
  simpa only [candidateFiniteSpectralEnergy, candidateFiniteSpectralRegionEnergy,
    mul_add, Finset.mul_sum, f, add_assoc] using h

end
end Erdos.Problem1144
