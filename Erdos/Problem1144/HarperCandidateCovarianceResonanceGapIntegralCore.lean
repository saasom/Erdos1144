import Erdos.Problem1144.HarperCandidateCovarianceGapResonance
import Erdos.Problem1144.HarperCandidateCovarianceGapProduct
import Erdos.Problem1144.HarperCandidateCovarianceResonanceSliceGapMass

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

private theorem squared_saving_factor {W : ℝ} (hW : 1 ≤ W) (δ x : ℝ) :
    (if x < δ then (W ^ 1000)⁻¹ else W ^ 6) ^ 2 =
      W ^ 12 * (if x < δ then (W ^ 2012)⁻¹ else 1) := by
  have hW0 : W ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hW)
  split_ifs
  · rw [show 2012 = 12 + 1000 * 2 by norm_num, pow_add, pow_mul, mul_inv,
      ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hW0), one_mul, inv_pow]
  · ring

/-- Exact saving from all short gaps. Each replaces the ordinary squared
cap `W^12` by `W^-2000`, hence the additional exponent `2012`. -/
theorem candidate_prod_squared_gapSaving_eq {ι : Type*} [Fintype ι]
    (W : ℝ) (hW : 1 ≤ W) (δ : ℝ) (g : ι → ℝ) :
    (∏ i, (if g i < δ then (W ^ 1000)⁻¹ else W ^ 6) ^ 2) =
      W ^ (12 * Fintype.card ι) /
        W ^ (2012 * (Finset.univ.filter (fun i => g i < δ)).card) := by
  classical
  simp_rw [squared_saving_factor hW δ, Finset.prod_mul_distrib]
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, Finset.card_univ, ← pow_mul, inv_pow, div_eq_mul_inv]

/-- Counting at least `k` short gaps yields the full quantitative saving. -/
theorem candidate_prod_squared_gapSaving_le {ι : Type*} [Fintype ι]
    (W : ℝ) (hW : 1 ≤ W) (δ : ℝ) (g : ι → ℝ) (k : ℕ)
    (hk : k ≤ (Finset.univ.filter (fun i => g i < δ)).card) :
    (∏ i, (if g i < δ then (W ^ 1000)⁻¹ else W ^ 6) ^ 2) ≤
      W ^ (12 * Fintype.card ι) / W ^ (2012 * k) := by
  rw [candidate_prod_squared_gapSaving_eq W hW δ g]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ hW (Nat.mul_le_mul_left _ hk))

private theorem box_product {n : ℕ} (G : ℝ → ℝ) (x : Fin (n + 1) → ℝ) :
    (∏ i : Fin (n + 1), if i = Fin.last n then (1 : ℝ) else G (x i)) =
      ∏ i : Fin n, G (x i.castSucc) := by
  rw [Fin.prod_univ_castSucc]
  simp

private theorem other_product {n : ℕ} (hn : 1 ≤ n) (j : Fin (n + 1))
    (hj : j ≠ Fin.last n) (I M : ℝ) :
    (∏ i : Fin n, if j.succAbove i = Fin.last n then M else I) = M * I ^ (n - 1) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.succAbove_ne_last_last hj, if_pos, Nat.add_sub_cancel]
    have he (i : Fin n) : j.succAbove i.castSucc ≠ Fin.last (n + 1) :=
      Fin.succAbove_ne_last hj (Fin.castSucc_ne_last i)
    simp only [he, if_false, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring

/-- A large internal gap gives a weighted affine slice, with the endpoint
coordinate contributing exactly its length and every other gap retaining
its one-dimensional mass. -/
theorem candidate_integral_gapBox_large_resonance_le {n : ℕ} (hn : 1 ≤ n)
    (c : Fin (n + 1) → ℤ) (j : Fin n) (hc : c j.castSucc ≠ 0)
    {M ε K δ U : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hU : 0 ≤ U)
    (m : ℤ) (G : ℝ → ℝ) (hG : Measurable G)
    (hGi : IntegrableOn G (Icc 0 M))
    (hGn : ∀ x ∈ Icc (0 : ℝ) M, 0 ≤ G x)
    (hGK : ∀ x ∈ Icc (0 : ℝ) M, δ ≤ x → G x ≤ K)
    (hGU : (∫ x in Icc (0 : ℝ) M, G x) ≤ U) :
    (∫ x, {x : Fin (n + 1) → ℝ |
      |(∑ i, (c i : ℝ) * x i) - (m : ℝ)| ≤ ε ∧ δ ≤ x j.castSucc}.indicator
        (fun x => ∏ i : Fin n, G (x i.castSucc)) x
      ∂Measure.pi (fun _ : Fin (n + 1) => volume.restrict (Icc (0 : ℝ) M))) ≤
        (2 * ε * K) * M * U ^ (n - 1) := by
  classical
  let w : Fin (n + 1) → ℝ → ℝ := fun i x =>
    if i = j.castSucc then (Ici δ).indicator G x
    else if i = Fin.last n then 1 else G x
  have hwj : w j.castSucc = (Ici δ).indicator G := by funext x; simp [w]
  have hwother (i : Fin n) : w (j.castSucc.succAbove i) =
      fun x => if j.castSucc.succAbove i = Fin.last n then 1 else G x := by
    funext x
    simp only [w, Fin.succAbove_ne, if_false]
  have hwi (i : Fin (n + 1)) : IntegrableOn (w i) (Icc 0 M) := by
    by_cases hi : i = j.castSucc
    · subst i; rw [hwj]; exact hGi.indicator measurableSet_Ici
    · by_cases hl : i = Fin.last n
      · simp only [w, if_neg hi, if_pos hl]; exact integrable_const 1
      · simpa only [w, if_neg hi, if_neg hl] using hGi
  have hwn (i : Fin (n + 1)) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) M) : 0 ≤ w i x := by
    dsimp only [w]
    split_ifs
    · by_cases hd : x ∈ Ici δ
      · rw [Set.indicator_of_mem hd]; exact hGn x hx
      · rw [Set.indicator_of_notMem hd]
    · positivity
    · exact hGn x hx
  have hwb (x : ℝ) (hx : x ∈ Icc (0 : ℝ) M) : w j.castSucc x ≤ K := by
    rw [hwj]
    by_cases hd : x ∈ Ici δ
    · rw [Set.indicator_of_mem hd]; exact hGK x hx hd
    · rw [Set.indicator_of_notMem hd]; exact hK
  have hs := candidate_integral_integerLinear_resonanceSlice_le c j.castSucc hc hε hK m
    (fun _ => 0) (fun _ => M) w (by rw [hwj]; exact hG.indicator measurableSet_Ici)
    hwi hwn hwb
  have heq (x : Fin (n + 1) → ℝ) :
      {x : Fin (n + 1) → ℝ | |(∑ i, (c i : ℝ) * x i) - (m : ℝ)| ≤ ε}.indicator
          (fun x => ∏ i, w i (x i)) x =
        {x : Fin (n + 1) → ℝ |
          |(∑ i, (c i : ℝ) * x i) - (m : ℝ)| ≤ ε ∧ δ ≤ x j.castSucc}.indicator
          (fun x => ∏ i : Fin n, G (x i.castSucc)) x := by
    have hp : (∏ i, w i (x i)) =
        {x : Fin (n + 1) → ℝ | δ ≤ x j.castSucc}.indicator
          (fun x => ∏ i : Fin n, G (x i.castSucc)) x := by
      by_cases hd : δ ≤ x j.castSucc
      · have hprod : (∏ i, w i (x i)) =
            ∏ i : Fin (n + 1), if i = Fin.last n then 1 else G (x i) := by
          apply Finset.prod_congr rfl
          intro i _
          by_cases hi : i = j.castSucc
          · subst i; simp [w, Set.indicator_apply, hd]
          · simp only [w, if_neg hi]
        rw [hprod, box_product]
        simp [Set.indicator_apply, hd]
      · have hz : w j.castSucc (x j.castSucc) = 0 := by
          rw [hwj]; simp [Set.indicator_apply, hd]
        rw [Finset.prod_eq_zero (Finset.mem_univ j.castSucc) hz]
        simp [Set.indicator_apply, hd]
    by_cases hr : |(∑ i, (c i : ℝ) * x i) - (m : ℝ)| ≤ ε
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, hr, if_true, true_and]
      simpa only [Set.indicator_apply, Set.mem_setOf_eq] using hp
    · simp only [Set.indicator_apply, Set.mem_setOf_eq, hr, if_false, false_and]
  simp_rw [heq] at hs
  have hI : 0 ≤ ∫ x in Icc (0 : ℝ) M, G x :=
    setIntegral_nonneg measurableSet_Icc hGn
  have hprod : (∏ i : Fin n, ∫ x in Icc (0 : ℝ) M, w (j.castSucc.succAbove i) x) =
      M * (∫ x in Icc (0 : ℝ) M, G x) ^ (n - 1) := by
    simp_rw [hwother]
    have hi (i : Fin n) :
        (∫ x in Icc (0 : ℝ) M, if j.castSucc.succAbove i = Fin.last n then (1 : ℝ) else G x) =
          if j.castSucc.succAbove i = Fin.last n then M else ∫ x in Icc (0 : ℝ) M, G x := by
      split_ifs <;> simp [setIntegral_const, Real.volume_real_Icc_of_le hM]
    simp_rw [hi]
    exact other_product hn j.castSucc (Fin.castSucc_ne_last j) _ M
  rw [hprod] at hs
  have hc1 : (1 : ℝ) ≤ |(c j.castSucc : ℝ)| := by exact_mod_cast Int.one_le_abs hc
  calc
    _ ≤ ((2 * ε / |(c j.castSucc : ℝ)|) * K) *
        (M * (∫ x in Icc (0 : ℝ) M, G x) ^ (n - 1)) := hs
    _ ≤ (2 * ε * K) * (M * U ^ (n - 1)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right (div_le_self (by positivity) hc1) hK
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hI hGU _) hM
      · positivity
      · positivity
    _ = _ := by ring

end Erdos.Problem1144
