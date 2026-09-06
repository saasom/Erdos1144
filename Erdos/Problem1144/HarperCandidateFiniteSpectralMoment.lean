import Erdos.Problem1144.HarperCandidateSpectralDyadicCover

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144
noncomputable section

private theorem sum_eighth_le {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i) ^ (1 / 8 : ℝ) ≤ ∑ i ∈ s, a i ^ (1 / 8 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine (Real.rpow_add_le_add_rpow (ha i (by simp))
      (Finset.sum_nonneg fun j hj => ha j (by simp [hj])) (by norm_num) (by norm_num)).trans ?_
    exact add_le_add le_rfl (ih fun j hj => ha j (by simp [hj]))

private theorem split_eighth_le (A B : ℝ) (P N : ℕ → ℝ) (n : ℕ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : ∀ j, 0 ≤ P j) (hN : ∀ j, 0 ≤ N j) :
    (A + B + ∑ j ∈ Finset.range n, (P j + N j)) ^ (1 / 8 : ℝ) ≤
      A ^ (1 / 8 : ℝ) + B ^ (1 / 8 : ℝ) +
        ∑ j ∈ Finset.range n, (P j ^ (1 / 8 : ℝ) + N j ^ (1 / 8 : ℝ)) := by
  refine (Real.rpow_add_le_add_rpow (add_nonneg hA hB)
    (Finset.sum_nonneg fun j _ => add_nonneg (hP j) (hN j))
    (by norm_num) (by norm_num)).trans ?_
  apply add_le_add
  · exact Real.rpow_add_le_add_rpow hA hB (by norm_num) (by norm_num)
  · refine (sum_eighth_le _ _ (fun j _ => add_nonneg (hP j) (hN j))).trans ?_
    exact Finset.sum_le_sum fun j _ =>
      Real.rpow_add_le_add_rpow (hP j) (hN j) (by norm_num) (by norm_num)

/-- The actual full-frequency moment is controlled by the moments of the
finite cover, using subadditivity at exponent `1/8`. -/
theorem candidate_finiteSpectralEnergy_moment_le_dyadic (y n : ℕ) {σ : ℝ}
    (hσ : σ ∈ Ioc (0 : ℝ) (1 / 2)) :
    (∫ ω, candidateFiniteSpectralEnergy y σ ω ^ (1 / 8 : ℝ) ∂Problem520.μ) ≤
      (∫ ω, candidateFiniteSpectralRegionEnergy y σ {t | (1 / 8 : ℝ) ≤ |t|} ω ^
        (1 / 8 : ℝ) ∂Problem520.μ) +
      (∫ ω, candidateFiniteSpectralRegionEnergy y σ
        (Icc (-candidateSpectralDyadicRadius n) (candidateSpectralDyadicRadius n)) ω ^
        (1 / 8 : ℝ) ∂Problem520.μ) +
      ∑ j ∈ Finset.range n,
        ((∫ ω, candidateFiniteSpectralRegionEnergy y σ
          (Icc (candidateSpectralDyadicRadius (j + 1)) (candidateSpectralDyadicRadius j)) ω ^
          (1 / 8 : ℝ) ∂Problem520.μ) +
         ∫ ω, candidateFiniteSpectralRegionEnergy y σ
          (Icc (-candidateSpectralDyadicRadius j) (-candidateSpectralDyadicRadius (j + 1))) ω ^
          (1 / 8 : ℝ) ∂Problem520.μ) := by
  let H := candidateFiniteSpectralRegionEnergy y σ {t | (1 / 8 : ℝ) ≤ |t|}
  let A := candidateFiniteSpectralRegionEnergy y σ
    (Icc (-candidateSpectralDyadicRadius n) (candidateSpectralDyadicRadius n))
  let P (j : ℕ) := candidateFiniteSpectralRegionEnergy y σ
    (Icc (candidateSpectralDyadicRadius (j + 1)) (candidateSpectralDyadicRadius j))
  let N (j : ℕ) := candidateFiniteSpectralRegionEnergy y σ
    (Icc (-candidateSpectralDyadicRadius j) (-candidateSpectralDyadicRadius (j + 1)))
  have hH := candidate_integrable_finiteSpectralRegionEnergy_rpow y σ (1 / 8 : ℝ)
    {t | (1 / 8 : ℝ) ≤ |t|}
  have hA := candidate_integrable_finiteSpectralRegionEnergy_rpow y σ (1 / 8 : ℝ)
    (Icc (-candidateSpectralDyadicRadius n) (candidateSpectralDyadicRadius n))
  have hP (j : ℕ) : Integrable (fun ω => P j ω ^ (1 / 8 : ℝ)) Problem520.μ :=
    candidate_integrable_finiteSpectralRegionEnergy_rpow y σ (1 / 8 : ℝ) _
  have hN (j : ℕ) : Integrable (fun ω => N j ω ^ (1 / 8 : ℝ)) Problem520.μ :=
    candidate_integrable_finiteSpectralRegionEnergy_rpow y σ (1 / 8 : ℝ) _
  have hPN (j : ℕ) : Integrable
      (fun ω => P j ω ^ (1 / 8 : ℝ) + N j ω ^ (1 / 8 : ℝ)) Problem520.μ :=
    (hP j).add (hN j)
  have hS : Integrable (fun ω => ∑ j ∈ Finset.range n,
      (P j ω ^ (1 / 8 : ℝ) + N j ω ^ (1 / 8 : ℝ))) Problem520.μ :=
    integrable_finset_sum (Finset.range n) (fun j _ => hPN j)
  have hHA : Integrable (fun ω => H ω ^ (1 / 8 : ℝ) + A ω ^ (1 / 8 : ℝ))
      Problem520.μ := hH.add hA
  have hp (ω : Problem520.Omega) : candidateFiniteSpectralEnergy y σ ω ^ (1 / 8 : ℝ) ≤
      H ω ^ (1 / 8 : ℝ) + A ω ^ (1 / 8 : ℝ) +
        ∑ j ∈ Finset.range n, (P j ω ^ (1 / 8 : ℝ) + N j ω ^ (1 / 8 : ℝ)) := by
    refine (Real.rpow_le_rpow (candidateFiniteSpectralEnergy_nonneg y hσ.1.le ω)
      (candidate_finiteSpectralEnergy_le_dyadic_cover y n hσ ω) (by norm_num)).trans ?_
    exact split_eighth_le (H ω) (A ω) (fun j => P j ω) (fun j => N j ω) n
      (candidateFiniteSpectralRegionEnergy_nonneg y hσ.1.le _ ω)
      (candidateFiniteSpectralRegionEnergy_nonneg y hσ.1.le _ ω)
      (fun j => candidateFiniteSpectralRegionEnergy_nonneg y hσ.1.le _ ω)
      (fun j => candidateFiniteSpectralRegionEnergy_nonneg y hσ.1.le _ ω)
  have h := integral_mono (candidate_integrable_finiteSpectralEnergy_rpow y σ (1 / 8 : ℝ))
    (hHA.add hS) hp
  simp only [Pi.add_apply] at h
  rw [integral_add hHA hS, integral_add hH hA,
    integral_finset_sum _ (fun j _ => hPN j)] at h
  simp_rw [integral_add (hP _) (hN _)] at h
  exact h

/-- The finite Euler products multiplied by the full zeta weight have a
uniform eighth moment, eventually in the prime cutoff for each damping.
Every frequency-region and arithmetic input is discharged. -/
theorem candidate_exists_finiteSpectralEnergy_uniform_eighth_moment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Ioc (0 : ℝ) (1 / 8),
      ∀ᶠ y : ℕ in atTop,
        (∫ ω, candidateFiniteSpectralEnergy y σ ω ^ (1 / 8 : ℝ) ∂Problem520.μ) ≤ C := by
  obtain ⟨CH, hCH, hhigh⟩ := candidate_exists_finiteSpectralRegion_high_moment
    (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨CL, hCL, hlocal⟩ := candidate_exists_finiteSpectralRegion_small_moment
  let R := candidateSpectralDyadicRadius
  let S := ∑' j : ℕ, R j ^ (1 / 16 : ℝ)
  have hS0 : 0 ≤ S := tsum_nonneg fun j => Real.rpow_nonneg (candidateSpectralDyadicRadius_pos j).le _
  refine ⟨CH + CL + 2 * CL * S, by positivity, ?_⟩
  intro σ hσ
  obtain ⟨n, hnlo, hnhi⟩ := candidate_exists_spectral_dyadic_radius hσ
  have hσ' : σ ∈ Ioc (0 : ℝ) (1 / 2) := ⟨hσ.1, by linarith [hσ.2]⟩
  have hrn := candidateSpectralDyadicRadius_pos n
  have hsize := candidateSpectralDyadicRadius_le n
  filter_upwards [eventually_ge_atTop (⌊Real.exp (1 / (2 * R n))⌋₊)] with y hy
  have hcut {U : ℝ} (hU : R n ≤ U) : ⌊Real.exp (1 / (2 * U))⌋₊ ≤ y := by
    apply le_trans _ hy
    apply Nat.floor_le_floor
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left (by norm_num) (by dsimp [R]; positivity)
      (by linarith)
  have hcenter : (∫ ω, candidateFiniteSpectralRegionEnergy y σ
      (Icc (-R n) (R n)) ω ^ (1 / 8 : ℝ) ∂Problem520.μ) ≤ CL := by
    have h := hlocal σ hσ (2 * R n) ⟨by dsimp [R]; positivity, by dsimp [R]; linarith⟩
      (by dsimp [R]; linarith) (-R n) (R n) (by dsimp [R]; linarith)
      (by ring_nf; exact le_rfl)
      (fun t ht => (abs_le.mpr ht).trans (by dsimp [R]; linarith))
      (fun t _ => by dsimp [R]; linarith [abs_nonneg t]) y
      (hcut (by dsimp [R]; linarith))
    refine h.trans ?_
    have hp : (2 * R n) ^ (1 / 16 : ℝ) ≤ 1 :=
      Real.rpow_le_one (by dsimp [R]; positivity) (by dsimp [R]; linarith) (by norm_num)
    nlinarith
  have hband (j : ℕ) (hj : j ∈ Finset.range n) :
      (∫ ω, candidateFiniteSpectralRegionEnergy y σ (Icc (R (j + 1)) (R j)) ω ^
        (1 / 8 : ℝ) ∂Problem520.μ) +
      (∫ ω, candidateFiniteSpectralRegionEnergy y σ (Icc (-R j) (-R (j + 1))) ω ^
        (1 / 8 : ℝ) ∂Problem520.μ) ≤ 2 * CL * R j ^ (1 / 16 : ℝ) := by
    have hjn : j + 1 ≤ n := by simpa using (Finset.mem_range.mp hj)
    have hm : R n ≤ R (j + 1) := candidateSpectralDyadicRadius_antitone hjn
    have hp := candidateSpectralDyadicRadius_pos (j + 1)
    have hu := candidateSpectralDyadicRadius_le (j + 1)
    have hs : R j = 2 * R (j + 1) := by
      have he := candidateSpectralDyadicRadius_succ j
      dsimp [R]
      linarith
    have hs0 : 0 < R (j + 1) := hp
    have H := hlocal σ hσ (R (j + 1)) ⟨hp, by linarith⟩ (hnhi.trans hm)
    have hpos := H (R (j + 1)) (R j) (by rw [hs]; linarith) (by rw [hs]; linarith)
      (fun t ht => by rw [abs_of_nonneg (hs0.le.trans ht.1)]; linarith [ht.2])
      (fun t ht => by rw [abs_of_nonneg (hs0.le.trans ht.1)]; linarith [ht.1, hσ.1])
      y (hcut hm)
    have hneg := H (-R j) (-R (j + 1)) (by rw [hs]; linarith) (by rw [hs]; linarith)
      (fun t ht => by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.1])
      (fun t ht => by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2, hσ.1])
      y (hcut hm)
    have hpmon := Real.rpow_le_rpow hp.le
      (candidateSpectralDyadicRadius_antitone (Nat.le_succ j)) (by norm_num : (0 : ℝ) ≤ 1 / 16)
    nlinarith [mul_le_mul_of_nonneg_left hpmon hCL]
  have hsum : (∑ j ∈ Finset.range n, 2 * CL * R j ^ (1 / 16 : ℝ)) ≤ 2 * CL * S := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact candidate_summable_spectral_dyadic_radius.sum_le_tsum _
      (fun j _ => Real.rpow_nonneg (candidateSpectralDyadicRadius_pos j).le _)
  have h := candidate_finiteSpectralEnergy_moment_le_dyadic y n hσ'
  exact h.trans (add_le_add (add_le_add (hhigh σ hσ' y) hcenter)
    ((Finset.sum_le_sum hband).trans hsum))

end
end Erdos.Problem1144
