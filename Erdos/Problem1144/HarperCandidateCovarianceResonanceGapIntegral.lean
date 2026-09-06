import Erdos.Problem1144.HarperCandidateCovarianceResonanceGapIntegralCore

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

private theorem gap_profile_integrable {n : ℕ} {M : ℝ} {G : ℝ → ℝ}
    (hG : IntegrableOn G (Icc 0 M)) :
    Integrable (fun x : Fin (n + 1) → ℝ => ∏ i : Fin n, G (x i.castSucc))
      (Measure.pi (fun _ : Fin (n + 1) => volume.restrict (Icc (0 : ℝ) M))) := by
  let w : Fin (n + 1) → ℝ → ℝ := fun i x => if i = Fin.last n then 1 else G x
  have hi (i : Fin (n + 1)) : IntegrableOn (w i) (Icc 0 M) := by
    by_cases h : i = Fin.last n
    · simp only [w, if_pos h]; exact integrable_const 1
    · simpa only [w, if_neg h] using hG
  have he : (fun x => ∏ i, w i (x i)) =
      fun x : Fin (n + 1) → ℝ => ∏ i : Fin n, G (x i.castSucc) := by
    funext x
    rw [Fin.prod_univ_castSucc]
    simp [w]
  exact he ▸ Integrable.fintype_prod hi

private theorem gap_profile_integral {n : ℕ} {M : ℝ} (hM : 0 ≤ M) (G : ℝ → ℝ) :
    (∫ x : Fin (n + 1) → ℝ, (∏ i : Fin n, G (x i.castSucc))
      ∂Measure.pi (fun _ : Fin (n + 1) => volume.restrict (Icc (0 : ℝ) M))) =
        M * (∫ x in Icc (0 : ℝ) M, G x) ^ n := by
  let w : Fin (n + 1) → ℝ → ℝ := fun i x => if i = Fin.last n then 1 else G x
  have he : (fun x => ∏ i, w i (x i)) =
      fun x : Fin (n + 1) → ℝ => ∏ i : Fin n, G (x i.castSucc) := by
    funext x
    rw [Fin.prod_univ_castSucc]
    simp [w]
  rw [← he, integral_fintype_prod_eq_prod, Fin.prod_univ_castSucc]
  simp [w, Real.volume_real_Icc_of_le hM, mul_comm]

private theorem internal_small_count {n : ℕ} (g : Fin (n + 1) → ℝ) (δ : ℝ) :
    (Finset.univ.filter (fun i : Fin (n + 1) => i.val < n ∧ g i < δ)).card =
      (Finset.univ.filter (fun i : Fin n => g i.castSucc < δ)).card := by
  classical
  rw [Finset.card_filter, Fin.sum_univ_castSucc, Finset.card_filter]
  simp

/-- Weighted resonance volume from the actual signed-gap dichotomy. Short
gaps supply `W^(-2012k)`; otherwise a nonzero integer coefficient supplies
a resonance slice. All other gap masses and the endpoint length remain
explicit. No balance condition on the signs is required. -/
theorem candidate_integral_gapBox_resonance_le {n : ℕ} (hn : 1 ≤ n)
    (signs : Fin (n + 1) → ℤ) (hsigns : ∀ i, signs i = 1 ∨ signs i = -1)
    (k : ℕ) (hk : 2 * k ≤ n + 1)
    {M ε K δ U W : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hU : 0 ≤ U) (hW : 1 ≤ W) (m : ℤ)
    (G : ℝ → ℝ) (hG : Measurable G) (hGi : IntegrableOn G (Icc 0 M))
    (hGn : ∀ x, 0 ≤ G x)
    (hGK : ∀ x ∈ Icc (0 : ℝ) M, δ ≤ x → G x ≤ K)
    (hGU : (∫ x in Icc (0 : ℝ) M, G x) ≤ U) :
    (∫ x, {x : Fin (n + 1) → ℝ |
      |(∑ i, (candidateGapCoefficients n signs i : ℝ) * x i) - (m : ℝ)| ≤ ε}.indicator
        (fun x => ∏ i : Fin n, G (x i.castSucc) *
          (if x i.castSucc < δ then (W ^ 1000)⁻¹ else W ^ 6) ^ 2) x
      ∂Measure.pi (fun _ : Fin (n + 1) => volume.restrict (Icc (0 : ℝ) M))) ≤
      W ^ (12 * n) * M *
        (U ^ n / W ^ (2012 * k) + 2 * ε * n * K * U ^ (n - 1)) := by
  classical
  let μ : Measure (Fin (n + 1) → ℝ) :=
    Measure.pi (fun _ : Fin (n + 1) => volume.restrict (Icc (0 : ℝ) M))
  let c := candidateGapCoefficients n signs
  let E : Set (Fin (n + 1) → ℝ) :=
    {x | |(∑ i, (c i : ℝ) * x i) - (m : ℝ)| ≤ ε}
  let P : (Fin (n + 1) → ℝ) → ℝ := fun x => ∏ i : Fin n, G (x i.castSucc)
  let Q : (Fin (n + 1) → ℝ) → ℝ := fun x => ∏ i : Fin n, G (x i.castSucc) *
    (if x i.castSucc < δ then (W ^ 1000)⁻¹ else W ^ 6) ^ 2
  let H : Fin n → (Fin (n + 1) → ℝ) → ℝ := fun j =>
    if c j.castSucc = 0 then 0 else
      {x | |(∑ i, (c i : ℝ) * x i) - (m : ℝ)| ≤ ε ∧ δ ≤ x j.castSucc}.indicator P
  let C := W ^ (12 * n)
  let D := W ^ (2012 * k)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hPn (x) : 0 ≤ P x := Finset.prod_nonneg (fun i _ => hGn _)
  have hQn (x) : 0 ≤ Q x := Finset.prod_nonneg (fun i _ => mul_nonneg (hGn _) (sq_nonneg _))
  have hHn (j) (x) : 0 ≤ H j x := by
    dsimp only [H]
    split_ifs
    · exact le_rfl
    · exact Set.indicator_nonneg (fun x _ => hPn x) x
  have hPi : Integrable P μ := gap_profile_integrable hGi
  have hPm : Measurable P := by unfold P; fun_prop
  have hEm : MeasurableSet E := by
    exact measurableSet_le (by fun_prop) measurable_const
  have hHm (j : Fin n) : MeasurableSet
      {x : Fin (n + 1) → ℝ |
        |(∑ i, (c i : ℝ) * x i) - (m : ℝ)| ≤ ε ∧ δ ≤ x j.castSucc} := by
    exact hEm.inter (measurableSet_le measurable_const (measurable_pi_apply _))
  have hHi (j : Fin n) : Integrable (H j) μ := by
    dsimp only [H]
    split_ifs
    · exact integrable_zero _ _ _
    · exact hPi.indicator (hHm j)
  have hsumI : Integrable (fun x => ∑ j, H j x) μ := integrable_finset_sum _ (fun j _ => hHi j)
  have hQm : Measurable Q := by
    unfold Q
    apply Finset.measurable_prod
    intro i _
    apply Measurable.mul (hG.comp (measurable_pi_apply _))
    exact (Measurable.ite (measurableSet_lt (measurable_pi_apply _) measurable_const)
      measurable_const measurable_const).pow_const 2
  have hQbound (x) : Q x ≤ C * P x := by
    have hs := candidate_prod_squared_gapSaving_le W hW δ
      (fun i : Fin n => x i.castSucc) 0 (Nat.zero_le _)
    simp only [Fintype.card_fin, Nat.mul_zero, pow_zero, div_one] at hs
    dsimp only [Q, P, C]
    rw [Finset.prod_mul_distrib]
    exact (mul_le_mul_of_nonneg_left hs (hPn x)).trans_eq (mul_comm _ _)
  have hQi : Integrable Q μ := by
    apply (hPi.const_mul C).mono' hQm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hQn x)] using hQbound x)
  have hpoint (x : Fin (n + 1) → ℝ) :
      E.indicator Q x ≤ C * (P x / D + ∑ j, H j x) := by
    have hsum0 : 0 ≤ ∑ j, H j x := Finset.sum_nonneg (fun j _ => hHn j x)
    by_cases he : x ∈ E
    · rw [Set.indicator_of_mem he]
      rcases candidate_gapCoefficients_small_or_resonant_gap n signs hsigns k hk x δ with hs | hs
      · rw [internal_small_count] at hs
        have hsave := candidate_prod_squared_gapSaving_le W hW δ
          (fun i : Fin n => x i.castSucc) k hs
        simp only [Fintype.card_fin] at hsave
        have hsmall : Q x ≤ C * (P x / D) := by
          dsimp only [Q]
          rw [Finset.prod_mul_distrib]
          exact (mul_le_mul_of_nonneg_left hsave (hPn x)).trans_eq (by dsimp [C, D, P]; ring)
        exact hsmall.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hsum0) hC)
      · obtain ⟨i, hi, hlarge, hci⟩ := hs
        let j : Fin n := ⟨i.val, hi⟩
        have hj : j.castSucc = i := Fin.ext rfl
        have hc : c j.castSucc ≠ 0 := by
          rw [hj]
          intro hzero
          have : (1 : ℤ) ≤ |(0 : ℤ)| := hzero ▸ hci
          norm_num at this
        have hHeq : H j x = P x := by
          dsimp only [H]
          rw [if_neg hc]
          exact Set.indicator_of_mem (show x ∈ {x : Fin (n + 1) → ℝ |
            |(∑ i, (c i : ℝ) * x i) - (m : ℝ)| ≤ ε ∧ δ ≤ x j.castSucc} from
              ⟨he, hj ▸ hlarge⟩) _
        have hsum : P x ≤ ∑ j, H j x := hHeq ▸
          (Finset.single_le_sum (fun j _ => hHn j x) (Finset.mem_univ j))
        exact (hQbound x).trans (mul_le_mul_of_nonneg_left
          (hsum.trans (le_add_of_nonneg_left (div_nonneg (hPn x) hD.le))) hC)
    · rw [Set.indicator_of_notMem he]
      exact mul_nonneg hC (add_nonneg (div_nonneg (hPn x) hD.le) hsum0)
  have hlarge (j : Fin n) : (∫ x, H j x ∂μ) ≤ 2 * ε * K * M * U ^ (n - 1) := by
    by_cases hc : c j.castSucc = 0
    · simp only [H, if_pos hc, Pi.zero_apply, integral_zero]
      positivity
    · simpa only [H, if_neg hc] using
        candidate_integral_gapBox_large_resonance_le hn c j hc hM hε hK hU m G hG hGi
          (fun x _ => hGn x) hGK hGU
  have hI : 0 ≤ ∫ x in Icc (0 : ℝ) M, G x := integral_nonneg hGn
  have hmass : (∫ x, P x ∂μ) ≤ M * U ^ n := by
    rw [show (∫ x, P x ∂μ) = M * (∫ x in Icc (0 : ℝ) M, G x) ^ n from
      gap_profile_integral hM G]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hI hGU n) hM
  have hiR := (hPi.div_const D).add hsumI |>.const_mul C
  change (∫ x, E.indicator Q x ∂μ) ≤ _
  calc
    _ ≤ ∫ x, C * (P x / D + ∑ j, H j x) ∂μ :=
      integral_mono (hQi.indicator hEm) hiR hpoint
    _ = C * ((∫ x, P x ∂μ) / D + ∑ j, ∫ x, H j x ∂μ) := by
      rw [integral_const_mul, integral_add (hPi.div_const D) hsumI, integral_div,
        integral_finset_sum _ (fun j _ => hHi j)]
    _ ≤ C * (M * U ^ n / D + n * (2 * ε * K * M * U ^ (n - 1))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add (div_le_div_of_nonneg_right hmass hD.le)
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hlarge j)
    _ = _ := by dsimp only [C, D]; ring

end Erdos.Problem1144
