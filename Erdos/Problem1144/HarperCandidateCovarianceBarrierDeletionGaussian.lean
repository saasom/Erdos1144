import Erdos.Problem1144.HarperCandidateCovarianceBarrierTailGaussian

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

noncomputable section

/-! Terminal-near estimates at every possible barrier violation location. -/

/-- The middle block may be longer than the outer blocks. -/
theorem candidate_gaussianWalkTerminalNear_probability_le_unequal_thirds
    (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n) (v : Fin (m + (n + m)) → ℝ≥0)
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hlo : ∀ i, (1 / 4 : ℝ≥0) ≤ v i) (hhi : ∀ i, v i ≤ (1 / 2 : ℝ≥0)) :
    (Measure.pi (fun i : Fin (m + (n + m)) => gaussianReal 0 (v i))).real
      (gaussianWalkTerminalNearSet (m + (n + m)) x r) ≤
        8192 * (x + 2) * (r + 2) * r / (Real.sqrt (m : ℝ)) ^ 3 := by
  let V : ℝ≥0 := ∑ i : Fin n, v (Fin.natAdd m (Fin.castAdd m i))
  have hVnn : (m : ℝ≥0) * (1 / 4) ≤ V := by
    calc
      _ ≤ (n : ℝ≥0) * (1 / 4) := by exact mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) (by positivity)
      _ = ∑ _i : Fin n, (1 / 4 : ℝ≥0) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hlo _
  have hVR : (m : ℝ) * (1 / 4) ≤ (V : ℝ) := by exact_mod_cast hVnn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hVpos : (0 : ℝ) < V := by linarith
  have hv : V ≠ 0 := by exact_mod_cast hVpos.ne'
  have hsM : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmR
  have hsV : 0 < Real.sqrt (V : ℝ) := Real.sqrt_pos.2 hVpos
  have hsqrt : Real.sqrt (m : ℝ) / 2 ≤ Real.sqrt (V : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt hmR.le]
    norm_num
    linarith
  have hquot : r / Real.sqrt (V : ℝ) ≤ 2 * r / Real.sqrt (m : ℝ) := by
    apply (div_le_div_iff₀ hsV hsM).2
    nlinarith [mul_le_mul_of_nonneg_left hsqrt hr]
  have h := candidate_gaussianWalkTerminalNear_probability_le_three_blocks
    m n m hm hm v hv x r hx hr hlo hhi
  calc
    _ ≤ (64 * (x + 2) / Real.sqrt (m : ℝ)) *
        (64 * (r + 2) / Real.sqrt (m : ℝ)) * (r / Real.sqrt (V : ℝ)) := h
    _ ≤ (64 * (x + 2) / Real.sqrt (m : ℝ)) *
        (64 * (r + 2) / Real.sqrt (m : ℝ)) * (2 * r / Real.sqrt (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hquot (by positivity)
    _ = _ := by ring


/-- Every length at least three has the sharp terminal-near bound. The
integer third in the denominator avoids a divisibility restriction on the
location where a strong barrier is violated. -/
theorem candidate_gaussianWalkTerminalNear_probability_le_all_lengths
    (n : ℕ) (hn : 3 ≤ n) (v : Fin n → ℝ≥0)
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (hlo : ∀ i, (1 / 4 : ℝ≥0) ≤ v i) (hhi : ∀ i, v i ≤ (1 / 2 : ℝ≥0)) :
    (Measure.pi (fun i : Fin n => gaussianReal 0 (v i))).real
      (gaussianWalkTerminalNearSet n x r) ≤
        8192 * (x + 2) * (r + 2) * r / (Real.sqrt ((n / 3 : ℕ) : ℝ)) ^ 3 := by
  let m := n / 3
  let k := n - (m + m)
  have hm : 0 < m := by dsimp [m]; omega
  have hmk : m ≤ k := by dsimp [m, k]; omega
  have heq : n = m + (k + m) := by dsimp [m, k]; omega
  have h : ∀ (N : ℕ) (hN : N = m + (k + m)) (w : Fin N → ℝ≥0),
      (∀ i, (1 / 4 : ℝ≥0) ≤ w i) → (∀ i, w i ≤ (1 / 2 : ℝ≥0)) →
      (Measure.pi (fun i : Fin N => gaussianReal 0 (w i))).real
        (gaussianWalkTerminalNearSet N x r) ≤
        8192 * (x + 2) * (r + 2) * r / (Real.sqrt (m : ℝ)) ^ 3 := by
    intro N hN w hwlo hwhi
    subst N
    exact candidate_gaussianWalkTerminalNear_probability_le_unequal_thirds
      m k hm hmk w x r hx hr hwlo hwhi
  exact h n heq v hlo hhi


private theorem partialSum_before_split (m q : ℕ) (hm : 0 < m)
    (ω : Fin (m + q) → ℝ) :
    Problem520.harperPathPartialSum ω ⟨m - 1, by omega⟩ =
      ∑ i, (harperFinSplit ω).1 i := by
  have heq : Finset.Iic (⟨m - 1, by omega⟩ : Fin (m + q)) =
      Finset.univ.map (Fin.castAddEmb q) := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro hi
      have hiv : i.val < m := by
        have hi' : i.val ≤ m - 1 := Fin.le_iff_val_le_val.mp hi
        omega
      exact ⟨⟨i.val, hiv⟩, Fin.ext rfl⟩
    · rintro ⟨j, rfl⟩
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.castAddEmb_apply, Fin.val_castAdd]
      omega
  unfold Problem520.harperPathPartialSum
  rw [heq, Finset.sum_map]
  rfl

/-- A violation at an internal prefix costs both the sharp terminal-near
prefix probability and the independent surviving suffix probability. This
is the factor needed when summing strong-barrier deletion locations. -/
theorem candidate_gaussian_internalBarrier_probability_le
    (m q : ℕ) (hm : 3 ≤ m) (hq : 0 < q) (v : Fin (m + q) → ℝ≥0)
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (lower upper : Fin (m + q) → ℝ)
    (hupper : ∀ i, upper i ≤ x)
    (hpinch : ∀ i, i.val + 1 = m → x - r ≤ lower i)
    (hlo : ∀ i, (1 / 4 : ℝ≥0) ≤ v i) (hhi : ∀ i, v i ≤ (1 / 2 : ℝ≥0)) :
    (Measure.pi (fun i : Fin (m + q) => gaussianReal 0 (v i))).real
      (Problem520.harperPartialSumBarrierSet lower upper) ≤
        (8192 * (x + 2) * (r + 2) * r /
          (Real.sqrt ((m / 3 : ℕ) : ℝ)) ^ 3) *
        (64 * (r + 2) / Real.sqrt (q : ℝ)) := by
  let A := gaussianWalkTerminalNearSet m x r
  let B := Problem520.gaussianWalkSurvivalSet q r
  have hA : MeasurableSet A := measurableSet_gaussianWalkTerminalNearSet m hx
  have hB : MeasurableSet B := Problem520.measurableSet_gaussianWalkSurvivalSet q hr
  have hsubset : Problem520.harperPartialSumBarrierSet lower upper ⊆
      harperFinSplit ⁻¹' (A ×ˢ B) := by
    intro ω hω
    have hu : Problem520.gaussianWalkSurvives (m + q) x ω := by
      apply (gaussianWalkSurvives_iff_harperPathPartialSum_le _ _ _).2
      intro i
      exact ((Problem520.mem_harperPartialSumBarrierSet.mp hω i).2).trans (hupper i)
    have hp := (Problem520.mem_harperPartialSumBarrierSet.mp hω
      (⟨m - 1, by omega⟩ : Fin (m + q))).1
    have hlow := hpinch (⟨m - 1, by omega⟩ : Fin (m + q)) (by simp; omega)
    rw [partialSum_before_split m q (by omega) ω] at hp
    have hnear : x - (∑ i, (harperFinSplit ω).1 i) ≤ r := by linarith
    refine ⟨⟨?_, hnear⟩, ?_⟩
    · apply (gaussianWalkSurvives_iff_harperPathPartialSum_le m x _).2
      intro k
      have hmap : (Finset.Iic k).map (Fin.castAddEmb q) =
          Finset.Iic (Fin.castAdd q k) := by
        ext i
        simp only [Finset.mem_map, Finset.mem_Iic, Fin.castAddEmb_apply]
        constructor
        · rintro ⟨j, hj, rfl⟩
          exact_mod_cast hj
        · intro hi
          have hiv : i.val < m := lt_of_le_of_lt (by exact_mod_cast hi) k.isLt
          exact ⟨⟨i.val, hiv⟩, by exact_mod_cast hi, Fin.ext rfl⟩
      have hfull := (gaussianWalkSurvives_iff_harperPathPartialSum_le _ _ _).1 hu
        (Fin.castAdd q k)
      unfold Problem520.harperPathPartialSum at hfull ⊢
      rw [← hmap, Finset.sum_map] at hfull
      exact hfull
    · apply (gaussianWalkSurvives_iff_harperPathPartialSum_le q r _).2
      intro k
      exact ((gaussianWalkSurvives_iff_harperPathPartialSum_le _ _ _).1
        (gaussianWalkSurvives_snd_of_harperFinSplit x ω hu) k).trans hnear
  have hsplit := measurePreserving_harperFinSplit m q v
  have hmap := map_measureReal_apply
    (μ := Measure.pi fun i : Fin (m + q) => gaussianReal 0 (v i))
    hsplit.measurable (hA.prod hB)
  rw [hsplit.map_eq] at hmap
  refine (measureReal_mono hsubset).trans ?_
  rw [← hmap, measureReal_prod_prod]
  exact mul_le_mul
    (candidate_gaussianWalkTerminalNear_probability_le_all_lengths m hm
      (fun i => v (Fin.castAdd q i)) x r hx hr (fun i => hlo _) (fun i => hhi _))
    (Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin q hq
      (fun i => v (Fin.natAdd m i)) hr (fun i => hlo _) (fun i => hhi _))
    (measureReal_nonneg) (by positivity)

end

end Erdos.Problem1144
