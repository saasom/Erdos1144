import Erdos.Problem1144.HarperCandidateSpectralCovariance

open MeasureTheory Set

namespace Erdos.Problem1144

/-- An explicit constant from the elementary exponential majorant. -/
def candidateStationaryTailConstant (c : ℝ) : ℝ := 2 * (c + 3) ^ 2 + 4

private theorem candidate_log_square_exponential_majorant
    {c T W t : ℝ} (hc : 0 ≤ c) (hT : 1 ≤ T)
    (hj : 1 ≤ Real.log T) (hW : 1 ≤ W) (ht : c * T ≤ t) :
    Real.log (t + 2) ^ 2 ≤ candidateStationaryTailConstant c * Real.log T ^ 2 *
      Real.exp (W * (t / T - c)) := by
  have hTpos : 0 < T := by linarith
  have hWpos : 0 < W := by linarith
  have ht0 : 0 ≤ t := (mul_nonneg hc hTpos.le).trans ht
  let v := W * (t / T - c)
  have hv : 0 ≤ v := mul_nonneg hWpos.le ((le_div_iff₀ hTpos).mpr ht |> sub_nonneg.mpr)
  have hvlarge : t / T - c ≤ v :=
    le_mul_of_one_le_left ((le_div_iff₀ hTpos).mpr ht |> sub_nonneg.mpr) hW
  have hratio : (t + 2) / T ≤ c + v + 2 := by
    have htwo : 2 / T ≤ 2 := (div_le_iff₀ hTpos).mpr (by linarith)
    rw [add_div]
    linarith
  have hlog : Real.log (t + 2) ≤ (c + 3 + v) * Real.log T := by
    have hsplit : Real.log (t + 2) = Real.log T + Real.log ((t + 2) / T) := by
      rw [Real.log_div (by positivity) hTpos.ne']
      ring
    rw [hsplit]
    have hratio0 : 0 ≤ (t + 2) / T := by positivity
    have hsmall := (Real.log_le_self hratio0).trans hratio
    have hfactor := mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ c + v + 2)
    nlinarith
  have hlog0 : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
  have hpoly : (c + 3 + v) ^ 2 ≤ candidateStationaryTailConstant c * Real.exp v := by
    have hexp := Real.sum_le_exp_of_nonneg hv 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
    have hv2 : v ^ 2 ≤ 2 * Real.exp v := by nlinarith
    have he : 1 ≤ Real.exp v := Real.one_le_exp_iff.mpr hv
    have hc2 := mul_le_mul_of_nonneg_left he (sq_nonneg (c + 3))
    unfold candidateStationaryTailConstant
    nlinarith [sq_nonneg (c + 3 - v)]
  calc
    Real.log (t + 2) ^ 2 ≤ ((c + 3 + v) * Real.log T) ^ 2 :=
      pow_le_pow_left₀ hlog0 hlog 2
    _ = (c + 3 + v) ^ 2 * Real.log T ^ 2 := mul_pow _ _ _
    _ ≤ (candidateStationaryTailConstant c * Real.exp v) * Real.log T ^ 2 :=
      mul_le_mul_of_nonneg_right hpoly (sq_nonneg _)
    _ = _ := by dsimp [v]; ring

/-- The elementary integral estimate in candidate equation (24), with
`γ = 1`. Its constant is explicit and the exponential tail rate is exact. -/
theorem candidate_stationary_log_square_tail_bound
    {c T W : ℝ} (hc : 0 ≤ c) (hT : 1 ≤ T)
    (hj : 1 ≤ Real.log T) (hW : 1 ≤ W) :
    IntegrableOn (fun t => Real.exp (-2 * W * t / T) * Real.log (t + 2) ^ 2)
      (Ioi (c * T)) ∧
    (1 / T) * (∫ t in Ioi (c * T),
      Real.exp (-2 * W * t / T) * Real.log (t + 2) ^ 2) ≤
      candidateStationaryTailConstant c * Real.log T ^ 2 * Real.exp (-2 * c * W) / W := by
  have hTpos : 0 < T := by linarith
  have hWpos : 0 < W := by linarith
  let B := candidateStationaryTailConstant c * Real.log T ^ 2 * Real.exp (-c * W)
  have hi : IntegrableOn (fun t => B * Real.exp ((-W / T) * t)) (Ioi (c * T)) :=
    (integrableOn_exp_mul_Ioi (div_neg_of_neg_of_pos (by linarith) hTpos) _).const_mul B
  have hb : ∀ t ∈ Ioi (c * T),
      Real.exp (-2 * W * t / T) * Real.log (t + 2) ^ 2 ≤
        B * Real.exp ((-W / T) * t) := by
    intro t ht
    have h := mul_le_mul_of_nonneg_left
      (candidate_log_square_exponential_majorant hc hT hj hW ht.le)
      (Real.exp_pos (-2 * W * t / T)).le
    convert h using 1
    dsimp [B]
    have he : Real.exp (-c * W) * Real.exp ((-W / T) * t) =
        Real.exp (-2 * W * t / T) * Real.exp (W * (t / T - c)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    linear_combination (candidateStationaryTailConstant c * Real.log T ^ 2) * he
  have ha : IntegrableOn (fun t => Real.exp (-2 * W * t / T) *
      Real.log (t + 2) ^ 2) (Ioi (c * T)) := by
    apply hi.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hb t ht
  refine ⟨ha, ?_⟩
  have hle := integral_mono_ae ha hi
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact hb t ht)
  apply (mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 1 / T)).trans_eq
  rw [integral_const_mul, integral_exp_mul_Ioi (div_neg_of_neg_of_pos (by linarith) hTpos)]
  have hphase : (-W / T) * (c * T) = -c * W := by field_simp
  rw [hphase]
  have he : Real.exp (-c * W) * Real.exp (-c * W) = Real.exp (-2 * c * W) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  dsimp [B]
  field_simp

end Erdos.Problem1144
