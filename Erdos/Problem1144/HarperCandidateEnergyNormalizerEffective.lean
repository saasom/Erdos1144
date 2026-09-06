import Erdos.Problem1144.HarperCandidateEnergyNormalizer

open Filter
open scoped Topology

namespace Erdos.Problem1144

private theorem candidate_log_floor_exp_lower {L : ℝ} (hL : Real.log 4 ≤ L) :
    4 ≤ ⌊Real.exp L⌋₊ ∧ L / 2 ≤ Real.log (⌊Real.exp L⌋₊ : ℝ) ∧
      Real.log (⌊Real.exp L⌋₊ : ℝ) ≤ L := by
  have hexp : (4 : ℝ) ≤ Real.exp L := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 4)] using Real.exp_le_exp.mpr hL
  have hz : 4 ≤ ⌊Real.exp L⌋₊ := (Nat.le_floor_iff (Real.exp_pos L).le).mpr hexp
  have hzpos : (0 : ℝ) < (⌊Real.exp L⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊Real.exp L⌋₊)
  have hzR : (4 : ℝ) ≤ (⌊Real.exp L⌋₊ : ℝ) := by exact_mod_cast hz
  have hfloor := Nat.lt_floor_add_one (Real.exp L)
  have hhalf : Real.exp L / 2 ≤ (⌊Real.exp L⌋₊ : ℝ) := by linarith
  have hlog := Real.log_le_log (by positivity : 0 < Real.exp L / 2) hhalf
  rw [Real.log_div (Real.exp_pos L).ne' (by norm_num), Real.log_exp] at hlog
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Real.log_le_log hzpos (Nat.floor_le (Real.exp_pos L).le)
  rw [Real.log_exp] at hupper
  exact ⟨hz, by linarith, hupper⟩

/-- Keeping primes only up to the effective cutoff removes the exponential
Rankin loss. The visible size condition simply keeps that cutoff at least 4. -/
theorem candidate_rankinNormalizer_lower_effective_cutoff
    {y : ℕ} (hy : 4 ≤ y) {a : ℝ} (ha : 0 ≤ a)
    (hsize : Real.log 4 ≤ Real.log y / (1 + a * Real.log y)) :
    (candidateRankinNormalizerConstant / 2) *
      (Real.log y / (1 + a * Real.log y)) ≤ harperRankinPrimeEnergyNormalizer y a := by
  let L := Real.log (y : ℝ) / (1 + a * Real.log y)
  let z := ⌊Real.exp L⌋₊
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hden : 0 < 1 + a * Real.log (y : ℝ) := by positivity
  obtain ⟨hz, hzlower, hzupper⟩ := candidate_log_floor_exp_lower hsize
  change 4 ≤ z at hz
  change L / 2 ≤ Real.log (z : ℝ) at hzlower
  change Real.log (z : ℝ) ≤ L at hzupper
  have hL : L ≤ Real.log (y : ℝ) := by
    dsimp only [L]
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg ha hlog.le]
  have hzy : z ≤ y := by
    apply Nat.floor_le_of_le
    exact (Real.exp_le_exp.mpr hL).trans_eq (Real.exp_log (by positivity))
  have haz : a * Real.log (z : ℝ) ≤ 1 := by
    have haL : a * L ≤ 1 := by
      dsimp only [L]
      rw [← mul_div_assoc]
      exact (div_le_one hden).mpr (by linarith)
    exact (mul_le_mul_of_nonneg_left hzupper ha).trans haL
  have hsmall := candidate_rankinNormalizer_lower_small_shift hz ha haz
  calc
    (candidateRankinNormalizerConstant / 2) *
        (Real.log (y : ℝ) / (1 + a * Real.log y)) =
      candidateRankinNormalizerConstant * (L / 2) := by dsimp only [L]; ring
    _ ≤ candidateRankinNormalizerConstant * Real.log (z : ℝ) :=
      mul_le_mul_of_nonneg_left hzlower candidateRankinNormalizerConstant_pos.le
    _ ≤ harperRankinPrimeEnergyNormalizer z a := hsmall
    _ ≤ harperRankinPrimeEnergyNormalizer y a := candidate_rankinNormalizer_mono_cutoff hzy a

/-- Polynomial dependence on the actual Rankin parameter. The bound is
uniform in `V` and `y` under the explicit effective-cutoff size condition. -/
theorem candidate_rankinNormalizer_lower_polynomial
    {V : ℝ} (hV : 0 ≤ V) {y : ℕ} (hy : 4 ≤ y)
    (hsize : (1 + 4 * V) * Real.log 4 ≤ Real.log y) :
    candidateRankinNormalizerConstant * Real.log y / (2 * (1 + 4 * V)) ≤
      harperRankinPrimeEnergyNormalizer y (4 * V / Real.log y) := by
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < y))
  have hden : 0 < 1 + 4 * V := by positivity
  have ha : 0 ≤ 4 * V / Real.log (y : ℝ) := by positivity
  have he : 1 + (4 * V / Real.log (y : ℝ)) * Real.log y = 1 + 4 * V := by
    field_simp
  have hs : Real.log 4 ≤ Real.log (y : ℝ) / (1 + (4 * V / Real.log y) * Real.log y) := by
    rw [he]
    exact (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hsize)
  have h := candidate_rankinNormalizer_lower_effective_cutoff hy ha hs
  rw [he] at h
  convert h using 1 <;> field_simp <;> ring

/-- For each fixed nonnegative `V`, the polynomial normalizer lower bound
holds eventually, with one absolute numerator constant. -/
theorem candidate_rankinNormalizer_eventually_lower_polynomial
    {V : ℝ} (hV : 0 ≤ V) :
    ∀ᶠ y : ℕ in atTop,
      candidateRankinNormalizerConstant * Real.log y / (2 * (1 + 4 * V)) ≤
        harperRankinPrimeEnergyNormalizer y (4 * V / Real.log y) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (4 : ℕ),
    hlog.eventually_ge_atTop ((1 + 4 * V) * Real.log 4)] with y hy hsize
  exact candidate_rankinNormalizer_lower_polynomial hV hy hsize

end Erdos.Problem1144
