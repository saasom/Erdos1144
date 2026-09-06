import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Average

open MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Deterministic block and shift averaging

These lemmas select a deterministic arithmetic grid from an integrated
nonnegative function, such as an old-field negative-tail probability.  The
selection concerns that deterministic probability function, not any realized
sample of the random process.
-/

theorem candidate_intervalIntegrable_gridCell
    {F : ℝ → ℝ} {a h : ℝ} {n i : ℕ} (hh : 0 ≤ h) (hi : i < n)
    (hF : IntervalIntegrable F volume a (a + (n : ℝ) * h)) :
    IntervalIntegrable F volume (a + (i : ℝ) * h) (a + ((i + 1 : ℕ) : ℝ) * h) := by
  have hin : (i : ℝ) + 1 ≤ n := by exact_mod_cast hi
  apply hF.mono_set
  rw [Set.uIcc_of_le (by push_cast; nlinarith),
    Set.uIcc_of_le (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hh))]
  intro t ht
  rcases ht with ⟨htl, htr⟩
  push_cast at htr
  constructor <;> nlinarith [show (0 : ℝ) ≤ i from Nat.cast_nonneg i]

/-- Integrating a shifted arithmetic grid exactly partitions its containing
block; there is no loss depending on the number of grid points. -/
theorem candidate_integral_shifted_grid_sum
    {F : ℝ → ℝ} {a h : ℝ} {m : ℕ} (hh : 0 ≤ h)
    (hF : IntervalIntegrable F volume a (a + (m : ℝ) * h)) :
    (∫ s in (0 : ℝ)..h, ∑ i ∈ Finset.range m, F (a + (i : ℝ) * h + s)) =
      ∫ t in a..a + (m : ℝ) * h, F t := by
  have hi : ∀ i ∈ Finset.range m,
      IntervalIntegrable (fun s ↦ F (a + (i : ℝ) * h + s)) volume 0 h := by
    intro i hi
    have hc := candidate_intervalIntegrable_gridCell hh (Finset.mem_range.mp hi) hF
    have ht := hc.comp_add_left (a + (i : ℝ) * h)
    convert ht using 1 <;> push_cast <;> ring
  rw [intervalIntegral.integral_finset_sum hi]
  have heq : ∀ i : ℕ, (∫ s in (0 : ℝ)..h, F (a + (i : ℝ) * h + s)) =
      ∫ t in (a + (i : ℝ) * h)..(a + ((i + 1 : ℕ) : ℝ) * h), F t := by
    intro i
    rw [intervalIntegral.integral_comp_add_left]
    congr 1 <;> push_cast <;> ring
  simp_rw [heq]
  simpa using intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ ↦ a + (i : ℝ) * h) (n := m)
    (fun i hi ↦ candidate_intervalIntegrable_gridCell hh hi hF)

/-- A block contains a shift whose grid average is at most its spatial
average.  The selected shift lies in `(0,h]`; this avoids any assumptions at
individual exceptional points. -/
theorem candidate_exists_shift_grid_average_le
    {F : ℝ → ℝ} {a h : ℝ} {m : ℕ} (hh : 0 < h) (hm : 0 < m)
    (hF : IntervalIntegrable F volume a (a + (m : ℝ) * h)) :
    ∃ s ∈ Set.Ioc (0 : ℝ) h,
      (∑ i ∈ Finset.range m, F (a + (i : ℝ) * h + s)) / (m : ℝ) ≤
        (∫ t in a..a + (m : ℝ) * h, F t) / ((m : ℝ) * h) := by
  have hi : ∀ i ∈ Finset.range m,
      IntervalIntegrable (fun s ↦ F (a + (i : ℝ) * h + s)) volume 0 h := by
    intro i hi
    have hc := candidate_intervalIntegrable_gridCell hh.le (Finset.mem_range.mp hi) hF
    have ht := hc.comp_add_left (a + (i : ℝ) * h)
    convert ht using 1 <;> push_cast <;> ring
  have hsum : IntervalIntegrable
      (fun s ↦ ∑ i ∈ Finset.range m, F (a + (i : ℝ) * h + s)) volume 0 h := by
    convert IntervalIntegrable.sum (Finset.range m) hi using 1
    ext s
    simp
  obtain ⟨s, hs, hav⟩ := exists_le_setAverage
    (μ := volume) (s := Set.Ioc (0 : ℝ) h)
    (by simpa [Real.volume_Ioc] using hh) (by simp [Real.volume_Ioc]) hsum.1
  refine ⟨s, hs, ?_⟩
  rw [setAverage_eq, Real.volume_real_Ioc_of_le hh.le, sub_zero,
    ← intervalIntegral.integral_of_le hh.le,
    candidate_integral_shifted_grid_sum hh.le hF, smul_eq_mul] at hav
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  calc
    (∑ i ∈ Finset.range m, F (a + (i : ℝ) * h + s)) / (m : ℝ) ≤
        (h⁻¹ * ∫ t in a..a + (m : ℝ) * h, F t) / (m : ℝ) :=
      div_le_div_of_nonneg_right hav hmR.le
    _ = (∫ t in a..a + (m : ℝ) * h, F t) / ((m : ℝ) * h) := by field_simp

/-- A finite interval partition contains a block with at most the mean
integral.  This is ordinary finite averaging of deterministic numbers. -/
theorem candidate_exists_block_integral_le
    {F : ℝ → ℝ} {a ℓ : ℝ} {n : ℕ} (hℓ : 0 ≤ ℓ) (hn : 0 < n)
    (hF : IntervalIntegrable F volume a (a + (n : ℝ) * ℓ)) :
    ∃ k < n, (∫ t in (a + (k : ℝ) * ℓ)..(a + ((k + 1 : ℕ) : ℝ) * ℓ), F t) ≤
      (∫ t in a..a + (n : ℝ) * ℓ, F t) / (n : ℝ) := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ ↦ a + (k : ℝ) * ℓ) (n := n)
    (fun k hk ↦ candidate_intervalIntegrable_gridCell hℓ hk hF)
  have hle : (∑ k ∈ Finset.range n,
      ∫ t in (a + (k : ℝ) * ℓ)..(a + ((k + 1 : ℕ) : ℝ) * ℓ), F t) ≤
      ∑ _k ∈ Finset.range n, (∫ t in a..a + (n : ℝ) * ℓ, F t) / (n : ℝ) := by
    rw [hsum]
    simp only [Nat.cast_zero, zero_mul, add_zero, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    exact le_rfl
  obtain ⟨k, hk, hval⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr hn.ne') hle
  exact ⟨k, Finset.mem_range.mp hk, hval⟩

/-- Exact deterministic block-and-shift selection from an integrated
nonnegative function.  Any uncovered terminal interval is discarded by
nonnegativity.  The denominator is the total covered length `n*m*h`, so no
factor counting the blocks is lost. -/
theorem candidate_exists_block_shift_grid_average_le
    {F : ℝ → ℝ} {a b h : ℝ} {n m : ℕ}
    (hh : 0 < h) (hn : 0 < n) (hm : 0 < m)
    (hcover : a + (n : ℝ) * ((m : ℝ) * h) ≤ b)
    (hF : IntervalIntegrable F volume a b)
    (hnonneg : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), 0 ≤ F t) :
    ∃ k < n, ∃ s ∈ Set.Ioc (0 : ℝ) h,
      (∑ i ∈ Finset.range m, F (a + (k : ℝ) * ((m : ℝ) * h) + (i : ℝ) * h + s)) /
        (m : ℝ) ≤ (∫ t in a..b, F t) / ((n : ℝ) * (m : ℝ) * h) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hℓ : 0 < (m : ℝ) * h := mul_pos hmR hh
  have hacover : a ≤ a + (n : ℝ) * ((m : ℝ) * h) :=
    le_add_of_nonneg_right (mul_pos hnR hℓ).le
  have hcovered : IntervalIntegrable F volume a (a + (n : ℝ) * ((m : ℝ) * h)) := by
    apply hF.mono_set
    rw [Set.uIcc_of_le hacover, Set.uIcc_of_le (hacover.trans hcover)]
    exact Set.Icc_subset_Icc le_rfl hcover
  obtain ⟨k, hk, hkval⟩ := candidate_exists_block_integral_le hℓ.le hn hcovered
  have hkint := candidate_intervalIntegrable_gridCell hℓ.le hk hcovered
  have hkend : a + ((k + 1 : ℕ) : ℝ) * ((m : ℝ) * h) =
      (a + (k : ℝ) * ((m : ℝ) * h)) + (m : ℝ) * h := by push_cast; ring
  rw [hkend] at hkint hkval
  obtain ⟨s, hs, hsval⟩ := candidate_exists_shift_grid_average_le hh hm hkint
  refine ⟨k, hk, s, hs, hsval.trans ?_⟩
  calc
    (∫ t in (a + (k : ℝ) * ((m : ℝ) * h))..
        ((a + (k : ℝ) * ((m : ℝ) * h)) + (m : ℝ) * h), F t) / ((m : ℝ) * h) ≤
        ((∫ t in a..a + (n : ℝ) * ((m : ℝ) * h), F t) / (n : ℝ)) /
          ((m : ℝ) * h) := div_le_div_of_nonneg_right hkval hℓ.le
    _ = (∫ t in a..a + (n : ℝ) * ((m : ℝ) * h), F t) /
        ((n : ℝ) * (m : ℝ) * h) := by rw [div_div, mul_assoc]
    _ ≤ (∫ t in a..b, F t) / ((n : ℝ) * (m : ℝ) * h) :=
      div_le_div_of_nonneg_right
        (intervalIntegral.integral_mono_interval le_rfl hacover hcover hnonneg hF)
        (mul_pos (mul_pos hnR hmR) hh).le

/-- Every point on the selected grid belongs to the original observation
window, including when the shift equals the spacing. -/
theorem candidate_grid_point_mem_window
    {a b h s : ℝ} {n m k i : ℕ} (hh : 0 ≤ h)
    (hcover : a + (n : ℝ) * ((m : ℝ) * h) ≤ b)
    (hk : k < n) (hi : i < m) (hs : s ∈ Set.Ioc (0 : ℝ) h) :
    a + (k : ℝ) * ((m : ℝ) * h) + (i : ℝ) * h + s ∈ Set.Ioc a b := by
  have hkR : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have hiR : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
  have hmnonneg : 0 ≤ (m : ℝ) * h := mul_nonneg (Nat.cast_nonneg m) hh
  have hkpos : 0 ≤ (k : ℝ) * ((m : ℝ) * h) :=
    mul_nonneg (Nat.cast_nonneg k) hmnonneg
  have hipos : 0 ≤ (i : ℝ) * h := mul_nonneg (Nat.cast_nonneg i) hh
  have hkbound := mul_le_mul_of_nonneg_right hkR hmnonneg
  have hibound := mul_le_mul_of_nonneg_right hiR hh
  constructor
  · linarith [hs.1]
  · nlinarith [hs.2]

end Erdos.Problem1144
