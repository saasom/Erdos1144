import Erdos.Problem1144.HarperCandidateTranslationPrimeBins
import Erdos.Problem1144.HarperCandidateCovariance
import Mathlib.Order.Interval.Set.Union

open MeasureTheory Set Filter
open scoped BigOperators

namespace Erdos.Problem1144

/-!
# Exact whole-bin partitions for the prime/white construction

Half-open logarithmic bins are disjoint, cover the entire finite interval,
and induce exactly the matching finite prime partition. Rounding upward
retains the crossing bin and reaches the prescribed macroscopic endpoint.
-/

def candidateWholeLogBin (T h : ℝ) (j : ℕ) : Set ℝ :=
  Ioc (T + (j : ℝ) * h) (T + ((j + 1 : ℕ) : ℝ) * h)

theorem candidateWholeLogBin_eq (T h : ℝ) (j : ℕ) :
    candidateWholeLogBin T h j = Ioc (T + (j : ℝ) * h) (T + (j : ℝ) * h + h) := by
  unfold candidateWholeLogBin
  congr 1
  push_cast
  ring

theorem measurableSet_candidateWholeLogBin (T h : ℝ) (j : ℕ) :
    MeasurableSet (candidateWholeLogBin T h j) := measurableSet_Ioc

theorem candidateWholeLogBin_disjoint {T h : ℝ} (hh : 0 ≤ h) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (candidateWholeLogBin T h j) (candidateWholeLogBin T h k) := by
  rcases lt_or_gt_of_ne hjk with hjk | hkj
  · apply Ioc_disjoint_Ioc_of_le
    have hc : ((j + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hjk
    have hm := mul_le_mul_of_nonneg_right hc hh
    linarith
  · apply Disjoint.symm
    apply Ioc_disjoint_Ioc_of_le
    have hc : ((k + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hkj
    have hm := mul_le_mul_of_nonneg_right hc hh
    linarith

theorem candidateWholeLogBin_union {T h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    (⋃ j ∈ Finset.range n, candidateWholeLogBin T h j) = Ioc T (T + (n : ℝ) * h) := by
  apply Subset.antisymm
  · apply iUnion_subset
    intro j
    apply iUnion_subset
    intro hj
    have hjn : ((j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Finset.mem_range.mp hj
    apply Ioc_subset_Ioc
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hh)
    · have hm := mul_le_mul_of_nonneg_right hjn hh
      linarith
  · simpa only [candidateWholeLogBin, Nat.cast_zero, zero_mul, add_zero] using
      Ioc_subset_biUnion_Ioc n (fun j ↦ T + (j : ℝ) * h)

theorem candidateWholeLogBin_volume {T h : ℝ} (hh : 0 ≤ h) (j : ℕ) :
    volume.real (candidateWholeLogBin T h j) = h := by
  rw [candidateWholeLogBin_eq, Real.volume_real_Ioc_of_le (by linarith)]
  ring

/-- Exact upward-rounded coverage and its one-bin overshoot. -/
theorem candidate_ceil_bin_coverage {D h : ℝ} (hD : 0 ≤ D) (hh : 0 < h) :
    D ≤ (⌈D / h⌉₊ : ℝ) * h ∧ (⌈D / h⌉₊ : ℝ) * h < D + h := by
  constructor
  · exact (div_le_iff₀ hh).mp (Nat.le_ceil (D / h))
  · have he := Nat.ceil_lt_add_one (div_nonneg hD hh.le)
    have hm := mul_lt_mul_of_pos_right he hh
    simpa only [add_mul, div_mul_cancel₀ D hh.ne', one_mul] using hm

/-- The candidate's full-bin count reaches `β*T` and has a polynomially
bounded total width on every scale `T ≥ 1` with `h ≤ 1`. -/
theorem candidate_macroscopic_ceil_bin_coverage {β T h : ℝ}
    (hβ : 1 ≤ β) (hT : 1 ≤ T) (hh : 0 < h) (hh1 : h ≤ 1) :
    β * T ≤ T + (⌈((β - 1) * T) / h⌉₊ : ℝ) * h ∧
      (⌈((β - 1) * T) / h⌉₊ : ℝ) * h ≤ β * T := by
  have hD : 0 ≤ (β - 1) * T := mul_nonneg (sub_nonneg.mpr hβ) (by linarith)
  have hc := candidate_ceil_bin_coverage hD hh
  constructor <;> linarith [hc.1, hc.2]

/-- Natural cutoff membership and real logarithmic membership agree exactly. -/
theorem candidate_mem_logPrimeBin_iff {z h : ℝ} {p : ℕ} :
    p ∈ candidateLogPrimeBin z h ↔
      Nat.Prime p ∧ z < Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ z + h := by
  constructor
  · exact candidate_mem_logPrimeBin_log_bounds
  · rintro ⟨hp, hleft, hright⟩
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨?_, ?_⟩, hp⟩
    · exact (Nat.floor_lt (Real.exp_pos _).le).mpr ((Real.lt_log_iff_exp_lt hp0).mp hleft)
    · exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr ((Real.log_le_iff_le_exp hp0).mp hright)

theorem candidateLogPrimeBin_disjoint {T h : ℝ} (hh : 0 ≤ h) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (candidateLogPrimeBin (T + (j : ℝ) * h) h)
      (candidateLogPrimeBin (T + (k : ℝ) * h) h) := by
  apply Finset.disjoint_left.mpr
  intro p hpj hpk
  have hj := (candidate_mem_logPrimeBin_log_bounds hpj).2
  have hk := (candidate_mem_logPrimeBin_log_bounds hpk).2
  have hdis := candidateWholeLogBin_disjoint (T := T) hh hjk
  rw [candidateWholeLogBin_eq, candidateWholeLogBin_eq] at hdis
  exact Set.disjoint_left.mp hdis hj hk

/-- The union of the actual finite prime bins is precisely the one large
prime interval, with no missing or duplicated endpoint primes. -/
theorem candidateLogPrimeBin_union {T h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    (Finset.range n).biUnion (fun j ↦ candidateLogPrimeBin (T + (j : ℝ) * h) h) =
      (Finset.Ioc ⌊Real.exp T⌋₊ ⌊Real.exp (T + (n : ℝ) * h)⌋₊).filter Nat.Prime := by
  change _ = candidateLogPrimeBin T ((n : ℝ) * h)
  ext p
  rw [Finset.mem_biUnion, candidate_mem_logPrimeBin_iff]
  constructor
  · rintro ⟨j, hj, hp⟩
    have hp' := candidate_mem_logPrimeBin_log_bounds hp
    have hmem : Real.log (p : ℝ) ∈ ⋃ j ∈ Finset.range n, candidateWholeLogBin T h j := by
      exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj,
        by simpa only [candidateWholeLogBin_eq] using hp'.2⟩⟩
    rw [candidateWholeLogBin_union hh n] at hmem
    exact ⟨hp'.1, hmem⟩
  · rintro ⟨hpP, hpL, hpR⟩
    have hmem : Real.log (p : ℝ) ∈ ⋃ j ∈ Finset.range n, candidateWholeLogBin T h j := by
      rw [candidateWholeLogBin_union hh n]
      exact ⟨hpL, hpR⟩
    obtain ⟨j, hmem⟩ := mem_iUnion.mp hmem
    obtain ⟨hj, hpj⟩ := mem_iUnion.mp hmem
    rw [candidateWholeLogBin_eq] at hpj
    exact ⟨j, hj, candidate_mem_logPrimeBin_iff.mpr ⟨hpP, hpj⟩⟩

/-- Every left endpoint of the upward-rounded partition precedes the target. -/
theorem candidate_ceil_bin_left_lt {D h : ℝ} (hh : 0 < h) {j : ℕ}
    (hj : j < ⌈D / h⌉₊) : (j : ℝ) * h < D := by
  exact (lt_div_iff₀ hh).mp (Nat.lt_ceil.mp hj)

/-- A literal finite step kernel, extended by zero outside its bins. -/
noncomputable def candidateWholeBinStep (T h : ℝ) (n : ℕ) (b : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (candidateWholeLogBin T h j).indicator (fun _ ↦ b j) x

theorem measurable_candidateWholeBinStep (T h : ℝ) (n : ℕ) (b : ℕ → ℝ) :
    Measurable (candidateWholeBinStep T h n b) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.indicator (measurableSet_candidateWholeLogBin T h j)

theorem candidate_integrable_wholeBinStep (T h : ℝ) (n : ℕ) (b : ℕ → ℝ) :
    Integrable (candidateWholeBinStep T h n b) := by
  apply integrable_finset_sum
  intro j _
  apply (integrable_indicator_iff (measurableSet_candidateWholeLogBin T h j)).mpr
  exact integrableOn_const (by simp [candidateWholeLogBin])

theorem candidateWholeBinStep_eq_of_mem {T h : ℝ} {n j : ℕ} {x : ℝ}
    (hh : 0 ≤ h) (hj : j ∈ Finset.range n) (hx : x ∈ candidateWholeLogBin T h j)
    (b : ℕ → ℝ) : candidateWholeBinStep T h n b x = b j := by
  unfold candidateWholeBinStep
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hx _
  · intro k _ hkj
    have hnot : x ∉ candidateWholeLogBin T h k := fun hk ↦
      Set.disjoint_left.mp (candidateWholeLogBin_disjoint hh hkj) hk hx
    exact Set.indicator_of_notMem hnot _
  · exact fun hn ↦ (hn hj).elim

theorem candidateWholeBinStep_eq_zero_of_not_mem {T h : ℝ} {n : ℕ} {x : ℝ}
    (hx : x ∉ ⋃ j ∈ Finset.range n, candidateWholeLogBin T h j) (b : ℕ → ℝ) :
    candidateWholeBinStep T h n b x = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  exact Set.indicator_of_notMem (fun hxj ↦ hx (mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hxj⟩⟩)) _

theorem candidateWholeBinStep_mul {T h : ℝ} (hh : 0 ≤ h) (n : ℕ) (b c : ℕ → ℝ) (x : ℝ) :
    candidateWholeBinStep T h n b x * candidateWholeBinStep T h n c x =
      candidateWholeBinStep T h n (fun j ↦ b j * c j) x := by
  by_cases hx : x ∈ ⋃ j ∈ Finset.range n, candidateWholeLogBin T h j
  · obtain ⟨j, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hj, hxj⟩ := mem_iUnion.mp hx
    simp only [candidateWholeBinStep_eq_of_mem hh hj hxj]
  · simp only [candidateWholeBinStep_eq_zero_of_not_mem hx, mul_zero]

theorem candidate_integral_wholeBinStep {T h : ℝ} (hh : 0 ≤ h) (n : ℕ) (b : ℕ → ℝ) :
    (∫ x, candidateWholeBinStep T h n b x) = ∑ j ∈ Finset.range n, h * b j := by
  unfold candidateWholeBinStep
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_indicator_const _ (measurableSet_candidateWholeLogBin T h j),
      candidateWholeLogBin_volume hh, smul_eq_mul]
  · intro j _
    exact (integrable_indicator_iff (measurableSet_candidateWholeLogBin T h j)).mpr
      (integrableOn_const (by simp [candidateWholeLogBin]))

theorem candidate_integrable_wholeBinStep_mul {T h : ℝ} (hh : 0 ≤ h)
    (n : ℕ) (b c : ℕ → ℝ) :
    Integrable (fun x ↦ candidateWholeBinStep T h n b x * candidateWholeBinStep T h n c x) := by
  simp_rw [candidateWholeBinStep_mul hh]
  exact candidate_integrable_wholeBinStep T h n (fun j ↦ b j * c j)

/-- Exact white step covariance, with each full bin contributing precisely
its Lebesgue length times its two endpoint coefficients. -/
theorem candidate_integral_wholeBinStep_mul {T h : ℝ} (hh : 0 ≤ h)
    (n : ℕ) (b c : ℕ → ℝ) :
    (∫ x, candidateWholeBinStep T h n b x * candidateWholeBinStep T h n c x) =
      ∑ j ∈ Finset.range n, h * b j * c j := by
  simp_rw [candidateWholeBinStep_mul hh]
  simpa only [mul_assoc] using candidate_integral_wholeBinStep hh n (fun j ↦ b j * c j)

theorem candidate_memLp_wholeBinStep_two {T h : ℝ} (hh : 0 ≤ h) (n : ℕ) (b : ℕ → ℝ) :
    MemLp (candidateWholeBinStep T h n b) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (measurable_candidateWholeBinStep T h n b).aestronglyMeasurable).mpr
  simpa only [pow_two] using candidate_integrable_wholeBinStep_mul hh n b b

/-- Gram identification for any finite family of literal white step kernels.
The coefficient at index `j` is evaluated at that bin's right endpoint by
instantiating `b`; no independence or nondegeneracy assumptions are needed. -/
theorem candidate_wholeBinStep_gram_eq {ι : Type*} {T h : ℝ}
    (hh : 0 ≤ h) (n : ℕ) (b : ι → ℕ → ℝ) :
    candidateWeightedGram volume (fun i ↦ candidateWholeBinStep T h n (b i)) (fun _ ↦ 1) =
      fun i k ↦ ∑ j ∈ Finset.range n, h * b i j * b k j := by
  funext i k
  simp only [candidateWeightedGram, one_mul]
  exact candidate_integral_wholeBinStep_mul hh n (b i) (b k)

/-- A supported kernel's global squared step error is exactly the sum of its
errors over the disjoint whole bins. -/
theorem candidate_integral_sq_sub_wholeBinStep {T h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    (f : ℝ → ℝ) (c : ℕ → ℝ) (hf : MemLp f 2 volume)
    (hsupport : ∀ x, x ∉ Ioc T (T + (n : ℝ) * h) → f x = 0) :
    (∫ x, (f x - candidateWholeBinStep T h n c x) ^ 2) =
      ∑ j ∈ Finset.range n, ∫ x in candidateWholeLogBin T h j, (f x - c j) ^ 2 := by
  have hE : Integrable (fun x ↦ (f x - candidateWholeBinStep T h n c x) ^ 2) :=
    (hf.sub (candidate_memLp_wholeBinStep_two hh n c)).integrable_sq
  have hzero : ∀ x, x ∉ Ioc T (T + (n : ℝ) * h) →
      (f x - candidateWholeBinStep T h n c x) ^ 2 = 0 := by
    intro x hx
    have hx' : x ∉ ⋃ j ∈ Finset.range n, candidateWholeLogBin T h j := by
      rwa [candidateWholeLogBin_union hh n]
    rw [hsupport x hx, candidateWholeBinStep_eq_zero_of_not_mem hx' c]
    norm_num
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← candidateWholeLogBin_union hh n]
  rw [integral_biUnion_finset (Finset.range n)
    (fun j _ ↦ measurableSet_candidateWholeLogBin T h j)
    (fun _ _ _ _ hjk ↦ candidateWholeLogBin_disjoint hh hjk)
    (fun _ _ ↦ hE.integrableOn)]
  apply Finset.sum_congr rfl
  intro j hj
  apply setIntegral_congr_fun (measurableSet_candidateWholeLogBin T h j)
  intro x hx
  dsimp only
  rw [candidateWholeBinStep_eq_of_mem hh hj hx c]

end Erdos.Problem1144
