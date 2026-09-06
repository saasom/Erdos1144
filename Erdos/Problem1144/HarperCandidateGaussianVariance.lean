import Erdos.Problem1144.HarperCandidateCovariance
import Erdos.Problem1144.HarperCoefficientScaleEnergy
import Erdos.Problem1144.HarperCandidateSpectralConvolution
import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory Set

namespace Erdos.Problem1144

/-- The same prefix energy lower-bounds every white-noise variance whose
endpoint leaves room for that prefix above the prime cutoff. -/
theorem candidate_white_variance_ge_common_prefix
    {ι : Type*} (a : ℝ → ℝ) (u : ι → ℝ) (i : ι)
    {V B : ℝ} (hV : 0 < V) (hB : 0 ≤ B) (hu : V + B ≤ u i)
    (hprefix : IntegrableOn (fun s => a s ^ 2) (Ioc 0 B))
    (hwhite : IntegrableOn (fun v => (1 / v) * a (u i - v) * a (u i - v))
      (Ici V)) :
    (∫ s in Ioc 0 B, a s ^ 2) / u i ≤ candidateWhiteCovariance a u V i i := by
  have hu0 : 0 < u i := by linarith
  have hB' : u i - B ≤ u i := by linarith
  have hs : Ioc (u i - B) (u i) ⊆ Ici V := by
    intro v hv
    change V ≤ v
    linarith [hv.1]
  have href : IntegrableOn (fun v => a (u i - v) ^ 2)
      (Ioc (u i - B) (u i)) := by
    have h := ((intervalIntegrable_iff_integrableOn_Ioc_of_le hB).mpr hprefix).comp_sub_left
      (u i)
    have h' : IntervalIntegrable (fun v => a (u i - v) ^ 2) volume
        (u i - B) (u i) := by simpa only [sub_zero] using h.symm
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hB').mp h'
  have hchange : (∫ v in Ioc (u i - B) (u i), a (u i - v) ^ 2) =
      ∫ s in Ioc 0 B, a s ^ 2 := by
    rw [← intervalIntegral.integral_of_le hB',
      intervalIntegral.integral_comp_sub_left (fun s => a s ^ 2) (u i)]
    simp only [sub_self, sub_sub_cancel]
    exact intervalIntegral.integral_of_le hB
  calc
    _ = ∫ v in Ioc (u i - B) (u i), (1 / u i) * a (u i - v) ^ 2 := by
      rw [integral_const_mul, hchange]
      ring
    _ ≤ ∫ v in Ioc (u i - B) (u i), (1 / v) * a (u i - v) * a (u i - v) := by
      apply integral_mono_ae (href.const_mul _) (hwhite.mono_set hs)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      have hv0 : 0 < v := hV.trans_le (hs hv)
      have hrec := one_div_le_one_div_of_le hv0 hv.2
      simpa only [pow_two, mul_assoc] using
        mul_le_mul_of_nonneg_right hrec (sq_nonneg (a (u i - v)))
    _ ≤ candidateWhiteCovariance a u V i i := by
      apply setIntegral_mono_set hwhite
      · filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
        have hv0 : 0 ≤ v := hV.le.trans hv
        simpa only [pow_two, mul_assoc] using
          mul_nonneg (one_div_nonneg.mpr hv0) (sq_nonneg (a (u i - v)))
      · exact Filter.Eventually.of_forall fun v hv => hs hv

/-- Endpoint upper bounds make the preceding common lower bound independent
of the retained index. Selection may depend arbitrarily on the signs. -/
theorem candidate_white_variance_ge_common_prefix_uniform
    {ι : Type*} (a : ℝ → ℝ) (u : ι → ℝ)
    {V B U : ℝ} (hV : 0 < V) (hB : 0 ≤ B)
    (hu : ∀ i, V + B ≤ u i) (hU : ∀ i, u i ≤ U)
    (hprefix : IntegrableOn (fun s => a s ^ 2) (Ioc 0 B))
    (hwhite : ∀ i, IntegrableOn
      (fun v => (1 / v) * a (u i - v) * a (u i - v)) (Ici V)) (i : ι) :
    (∫ s in Ioc 0 B, a s ^ 2) / U ≤ candidateWhiteCovariance a u V i i := by
  have hui : 0 < u i := by linarith [hu i]
  exact (div_le_div_of_nonneg_left (integral_nonneg fun _ => sq_nonneg _) hui (hU i)).trans
    (candidate_white_variance_ge_common_prefix a u i hV hB (hu i) hprefix (hwhite i))

/-- The squarefree coefficient in the complete model is exactly the
squarefree model used by the established Harper energy theorems. -/
theorem candidate_gSquarefree_eq_problem520 (omega : Omega) (n : ℕ) :
    gSquarefree omega n = Problem520.f omega n := by
  classical
  by_cases hn : Squarefree n
  · have hker : sfKernel n = n.primeFactors := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      have hpf := Nat.mem_primeFactors.mp hp
      rw [Nat.factorization_eq_one_of_squarefree hn hpf.1 hpf.2.1]
    simp only [gSquarefree, Problem520.f, if_pos hn, f, hker]
    rfl
  · simp [gSquarefree, Problem520.f, hn]

/-- The two existing endpoint conventions for the squarefree partial sum
agree exactly, including cutoff zero. -/
theorem candidate_GSquarefree_eq_partialSum (omega : Omega) (N : ℕ) :
    GSquarefree omega N = Problem520.partialSum omega N := by
  classical
  have hset : Finset.Icc 1 N = (Finset.range N).image Nat.succ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hn
      exact ⟨n - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  simp only [GSquarefree, candidate_gSquarefree_eq_problem520, hset,
    Finset.sum_image Nat.succ_injective.injOn, Problem520.partialSum]

private theorem candidate_squarefree_log_eq_partialSum (omega : Omega) (t : ℝ) :
    harperCandidateSquarefreeLogProcess omega t =
      if 0 ≤ t then Problem520.partialSum omega ⌊Real.exp t⌋₊ / Real.exp (t / 2) else 0 := by
  simp only [harperCandidateSquarefreeLogProcess, candidate_GSquarefree_eq_partialSum]

private theorem candidate_exp_image_log_prefix {y : ℕ} (hy : 1 ≤ y) :
    Real.exp '' Ioc (0 : ℝ) (Real.log (y : ℝ)) = Ioc (1 : ℝ) (y : ℝ) := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hy
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor
    · simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr ht.1
    · simpa only [Real.exp_log hy0] using Real.exp_le_exp.mpr ht.2
  · intro hz
    have hz0 : 0 < z := lt_trans zero_lt_one hz.1
    exact ⟨Real.log z, ⟨Real.log_pos hz.1, Real.log_le_log hz0 hz.2⟩,
      Real.exp_log hz0⟩

private theorem candidate_squarefree_log_sq_change
    (omega : Problem520.Omega) {y : ℕ} {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) (Real.log (y : ℝ))) (hy : 1 ≤ y) :
    |Real.exp t| • (|Problem520.ΨReal omega (Real.exp t) y| ^ 2 / (Real.exp t) ^ 2) =
      harperCandidateSquarefreeLogProcess omega t ^ 2 := by
  have hy0 : (0 : ℝ) < y := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hy
  have he : Real.exp t ≤ (y : ℝ) := by
    simpa only [Real.exp_log hy0] using Real.exp_le_exp.mpr ht.2
  rw [ΨReal_eq_squarefreePartialSum_of_le omega he]
  have hsq : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  simp only [candidate_squarefree_log_eq_partialSum, if_pos ht.1.le,
    abs_of_pos (Real.exp_pos t),
    smul_eq_mul, sq_abs, div_pow, hsq]
  field_simp

/-- Exact exponential substitution identifies the common time energy with
the already formalized ordinary squarefree coefficient-prefix energy. -/
theorem candidate_squarefree_log_prefix_energy_eq
    (omega : Problem520.Omega) {y : ℕ} (hy : 1 ≤ y) :
    (∫ t in Ioc (0 : ℝ) (Real.log (y : ℝ)),
      harperCandidateSquarefreeLogProcess omega t ^ 2) =
      harperSquarefreeCoefficientPrefixEnergy y omega := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (s := Ioc (0 : ℝ) (Real.log (y : ℝ))) measurableSet_Ioc
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn
    (fun z : ℝ => |Problem520.ΨReal omega z y| ^ 2 / z ^ 2)
  rw [candidate_exp_image_log_prefix hy] at h
  rw [harperSquarefreeCoefficientPrefixEnergy, h]
  exact setIntegral_congr_fun measurableSet_Ioc fun t ht =>
    (candidate_squarefree_log_sq_change omega ht hy).symm

/-- Integrability of that literal common time energy is unconditional. -/
theorem candidate_squarefree_log_prefix_integrable
    (omega : Problem520.Omega) {y : ℕ} (hy : 1 ≤ y) :
    IntegrableOn (fun t => harperCandidateSquarefreeLogProcess omega t ^ 2)
      (Ioc (0 : ℝ) (Real.log (y : ℝ))) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioc (0 : ℝ) (Real.log (y : ℝ))) measurableSet_Ioc
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn
    (fun z : ℝ => |Problem520.ΨReal omega z y| ^ 2 / z ^ 2)
  rw [candidate_exp_image_log_prefix hy] at h
  exact (h.mp (integrableOn_harperSquarefreeCoefficientPrefixEnergy y omega)).congr_fun
    (fun t ht => candidate_squarefree_log_sq_change omega ht hy) measurableSet_Ioc

/-- The squarefree log process is bounded on every left half-line. -/
theorem candidate_squarefree_log_abs_le_exp_half
    (omega : Omega) {t b : ℝ} (htb : t ≤ b) :
    |harperCandidateSquarefreeLogProcess omega t| ≤ Real.exp (b / 2) := by
  have hG (N : ℕ) : |GSquarefree omega N| ≤ (N : ℝ) := by
    unfold GSquarefree
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 N, |gSquarefree omega n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Icc 1 N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        by_cases hn : Squarefree n <;> simp [gSquarefree, hn]
      _ = N := by simp
  by_cases ht : 0 ≤ t
  · rw [harperCandidateSquarefreeLogProcess, if_pos ht, abs_div,
      abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ (⌊Real.exp t⌋₊ : ℝ) / Real.exp (t / 2) :=
        div_le_div_of_nonneg_right (hG _) (Real.exp_pos _).le
      _ ≤ Real.exp t / Real.exp (t / 2) :=
        div_le_div_of_nonneg_right (Nat.floor_le (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = Real.exp (t / 2) := by rw [← Real.exp_sub]; congr 1; ring
      _ ≤ Real.exp (b / 2) := Real.exp_le_exp.mpr (by linarith)
  · simpa [harperCandidateSquarefreeLogProcess, ht] using (Real.exp_pos (b / 2)).le

/-- Every literal squarefree white-noise variance exists; the integrand has
bounded compact support above its positive prime cutoff. -/
theorem candidate_squarefree_white_variance_integrable
    (omega : Omega) {V : ℝ} (hV : 0 < V) (u : ℝ) :
    IntegrableOn (fun v => (1 / v) * harperCandidateSquarefreeLogProcess omega (u - v) *
      harperCandidateSquarefreeLogProcess omega (u - v)) (Ici V) := by
  let q : ℝ → ℝ := fun v => (1 / v) * harperCandidateSquarefreeLogProcess omega (u - v) *
    harperCandidateSquarefreeLogProcess omega (u - v)
  have hmeas : Measurable q := by
    have hm : Measurable fun v : ℝ => harperCandidateSquarefreeLogProcess omega (u - v) :=
      measurable_harperCandidateSquarefreeLogProcess.comp
        (measurable_const.prodMk (measurable_const.sub measurable_id))
    exact ((measurable_const.div measurable_id).mul hm).mul hm
  have hi : IntegrableOn q (Icc V u) := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable
      ((1 / V) * Real.exp (u / 2) ^ 2)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hv0 : 0 < v := hV.trans_le hv.1
    have hma := candidate_squarefree_log_abs_le_exp_half omega
      (show u - v ≤ u by linarith)
    have hrec : 1 / v ≤ 1 / V := one_div_le_one_div_of_le hV hv.1
    simp only [q, Real.norm_eq_abs, abs_mul, abs_div, abs_one, abs_of_pos hv0]
    have hs := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (abs_nonneg _) (Real.exp_pos _).le).mpr hma) (one_div_nonneg.mpr hv0.le)
    calc
      _ = (1 / v) * |harperCandidateSquarefreeLogProcess omega (u - v)| ^ 2 := by ring
      _ ≤ (1 / v) * Real.exp (u / 2) ^ 2 := hs
      _ ≤ (1 / V) * Real.exp (u / 2) ^ 2 := mul_le_mul_of_nonneg_right hrec (sq_nonneg _)
  have hi' : Integrable ((Icc V u).indicator q) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hi
  have hi'' : IntegrableOn ((Icc V u).indicator q) (Ici V) := hi'.integrableOn
  exact hi''.congr_fun (fun v hv => by
    by_cases hvu : v ≤ u
    · exact indicator_of_mem (show v ∈ Icc V u from ⟨hv, hvu⟩) q
    · have hneg : u - v < 0 := by linarith
      simp [q, harperCandidateSquarefreeLogProcess, not_le.mpr hneg, hvu]) measurableSet_Ici

/-- The genuine squarefree covariance has one common, unconditional prefix
energy lower bound, uniformly over all indices and therefore over every
sign-dependent retained subset. -/
theorem candidate_squarefree_white_variance_ge_coefficient_energy
    {ι : Type*} (omega : Omega) (u : ι → ℝ)
    {V U : ℝ} {y : ℕ} (hV : 0 < V) (hy : 1 ≤ y)
    (hu : ∀ i, V + Real.log (y : ℝ) ≤ u i) (hU : ∀ i, u i ≤ U) (i : ι) :
    harperSquarefreeCoefficientPrefixEnergy y omega / U ≤
      candidateWhiteCovariance (harperCandidateSquarefreeLogProcess omega) u V i i := by
  rw [← candidate_squarefree_log_prefix_energy_eq omega hy]
  apply candidate_white_variance_ge_common_prefix_uniform _ _ hV
    (Real.log_nonneg (by exact_mod_cast hy)) hu hU
    (candidate_squarefree_log_prefix_integrable omega hy)
  exact fun i => candidate_squarefree_white_variance_integrable omega hV (u i)

end Erdos.Problem1144
