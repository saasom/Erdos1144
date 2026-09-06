import Erdos.Problem1144.HarperCandidateGaussianVariance
import Erdos.Problem1144.HarperCandidateEnergyLowerEvent
import Erdos.Problem1144.HarperCandidatePrimeBins

open MeasureTheory Set Filter
open scoped Topology

namespace Erdos.Problem1144

/-- A fixed proportional exponential prefix has its actual critical scale
bounded below by the common logarithmic-time scale. -/
theorem candidate_eventually_exponential_prefix_geometry
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    ∀ᶠ T : ℝ in atTop,
      let y := ⌊Real.exp (c * T)⌋₊
      4 ≤ y ∧ c * T / 2 ≤ Real.log (y : ℝ) ∧ Real.log (y : ℝ) ≤ c * T ∧
        (1 + Real.log T) ^ (-(1 : ℝ) / 2) ≤ harperInitialCriticalScale y := by
  have hexp := tendsto_nat_floor_atTop.comp
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc))
  filter_upwards [hexp.eventually_ge_atTop 4,
    (tendsto_id.const_mul_atTop hc).eventually_ge_atTop 2,
    eventually_ge_atTop (1 : ℝ)] with T hy hcT hT
  dsimp only
  dsimp only [Function.comp_def, id_eq] at hy hcT
  have hround := candidate_log_floor_exp_error (by linarith : 0 ≤ c * T)
  have hyR : (1 : ℝ) ≤ (⌊Real.exp (c * T)⌋₊ : ℝ) := by exact_mod_cast (by omega : 1 ≤ ⌊Real.exp (c * T)⌋₊)
  have hinv : (⌊Real.exp (c * T)⌋₊ : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using one_div_le_one_div_of_le zero_lt_one hyR
  have hlow : c * T / 2 ≤ Real.log (⌊Real.exp (c * T)⌋₊ : ℝ) := by linarith [hround.2]
  have hupp : Real.log (⌊Real.exp (c * T)⌋₊ : ℝ) ≤ c * T := by linarith [hround.1]
  refine ⟨hy, hlow, hupp, ?_⟩
  have hlogpos : 0 < Real.log (⌊Real.exp (c * T)⌋₊ : ℝ) := by linarith
  have hlogle : Real.log (Real.log (⌊Real.exp (c * T)⌋₊ : ℝ)) ≤ Real.log T := by
    exact Real.log_le_log hlogpos (hupp.trans (by nlinarith))
  unfold harperInitialCriticalScale Problem520.logLogNat
  exact Real.rpow_le_rpow_of_nonpos
    (Problem520.one_add_logLogNat_pos_of_four_le hy) (by linarith) (by norm_num)

/-- The literal common prefix supplies a variance floor for every coordinate
in the window. The deterministic constant is explicit, including the
finite-cylinder factor. -/
theorem candidate_squarefree_white_variance_ge_log_scale
    {N y : ℕ} (ω : Omega) (u : Fin N → ℝ) {T α β d : ℝ} (s : Finset ℕ)
    (hT1 : 1 ≤ T) (hα : 1 < α) (hαβ : α ≤ β) (hd : 0 ≤ d) (hy : 1 ≤ y)
    (hlow : (α - 1) * T / 2 ≤ Real.log (y : ℝ))
    (hupp : Real.log (y : ℝ) ≤ (α - 1) * T)
    (hscale : (1 + Real.log T) ^ (-(1 : ℝ) / 2) ≤ harperInitialCriticalScale y)
    (hpoints : ∀ i, u i ∈ Icc (α * T) (β * T))
    (henergy : d * Real.log (y : ℝ) * harperInitialCriticalScale y / (49 : ℝ) ^ s.card ≤
      harperSquarefreeCoefficientPrefixEnergy y ω) (i : Fin N) :
    (d * (α - 1) / (2 * β * (49 : ℝ) ^ s.card)) *
      (1 + Real.log T) ^ (-(1 : ℝ) / 2) ≤
        candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T i i := by
  have hβ : 0 < β := by linarith
  have hT : 0 < T := by linarith
  have hg : 0 ≤ (1 + Real.log T) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg
    (by linarith [Real.log_nonneg hT1]) _
  have hnum : (d * ((α - 1) * T / 2) *
      (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / (49 : ℝ) ^ s.card ≤
      harperSquarefreeCoefficientPrefixEnergy y ω := by
    apply le_trans _ henergy
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hlow hd) hscale hg
      (mul_nonneg hd (Real.log_nonneg (by exact_mod_cast hy)))
  have hv := candidate_squarefree_white_variance_ge_coefficient_energy ω u hT hy
    (fun j => by have := (hpoints j).1; linarith) (fun j => (hpoints j).2) i
  calc
    _ = ((d * ((α - 1) * T / 2) *
        (1 + Real.log T) ^ (-(1 : ℝ) / 2)) / (49 : ℝ) ^ s.card) / (β * T) := by
      field_simp
    _ ≤ _ := (div_le_div_of_nonneg_right hnum (mul_pos hβ hT).le).trans hv

/-- An absolute positive probability supports a simultaneous variance floor
on every finite grid in the window, under each fixed finite-cylinder law. -/
theorem candidate_exists_squarefree_white_variance_lower_probability :
    ∃ delta : ℝ, 0 < delta ∧ ∀ α β : ℝ, 1 < α → α ≤ 2 → α ≤ β →
      ∀ (s : Finset ℕ) (η : s → Bool), ∃ v > 0,
        ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, ∀ u : Fin N → ℝ,
          (∀ i, u i ∈ Icc (α * T) (β * T)) →
          delta ≤ (candidateCylinderLaw s η).real
            {ω | ∀ i, v * (1 + Real.log T) ^ (-(1 : ℝ) / 2) ≤
              candidateWhiteCovariance (harperCandidateSquarefreeLogProcess ω) u T i i} := by
  obtain ⟨delta, hdelta, d, hd, Y, hY4, henergy⟩ :=
    candidate_exists_squarefree_prefix_energy_lower_probability_cylinder
  refine ⟨delta, hdelta, ?_⟩
  intro α β hα hα2 hαβ s η
  have hβ : 0 < β := by linarith
  refine ⟨d * (α - 1) / (2 * β * (49 : ℝ) ^ s.card),
    div_pos (mul_pos hd (by linarith)) (by positivity), ?_⟩
  have hc : 0 < α - 1 := by linarith
  have hcut := tendsto_nat_floor_atTop.comp
    (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc))
  filter_upwards [hcut.eventually_ge_atTop Y,
    candidate_eventually_exponential_prefix_geometry hc (by linarith),
    eventually_ge_atTop (1 : ℝ)] with T hY hgeom hT
  dsimp only [Function.comp_def, id_eq] at hY
  rcases hgeom with ⟨hy, hlow, hupp, hscale⟩
  intro N u hpoints
  apply (henergy s η _ hY).trans
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω i
  exact candidate_squarefree_white_variance_ge_log_scale ω u s hT hα hαβ hd.le
    (by omega) hlow hupp hscale hpoints hω i

end Erdos.Problem1144
