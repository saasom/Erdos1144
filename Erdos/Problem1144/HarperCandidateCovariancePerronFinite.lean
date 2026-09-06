import Erdos.Problem1144.HarperCandidateCovariancePerronL2

open Finset MeasureTheory Set FourierTransform
open scoped BigOperators Topology

namespace Erdos.Problem1144
noncomputable section

/-- The literal squarefree partial-sum process with all integers supported on
primes at most `Y`. This has finite Euler support, not an integer truncation. -/
def candidateEulerLogProcess (Y : ℕ) (ω : Omega) (t : ℝ) : ℂ :=
  ∑ n ∈ candidateEulerSupport Y,
    candidateComplexLaplaceAtom (1 / 2) n t * (gSquarefree ω n : ℂ)

private theorem atom_memLp_two (n : ℕ) :
    MemLp (candidateComplexLaplaceAtom (1 / 2) n) 2 := by
  have h := candidate_integrable_complexLaplaceAtom (s := 1 / 2) (by norm_num) n
  apply (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mpr
  have hsq : (fun t => ‖candidateComplexLaplaceAtom (1 / 2) n t‖ ^ 2) =
      fun t => ‖candidateComplexLaplaceAtom 1 n t‖ := by
    funext t
    by_cases ht : Real.log (n : ℝ) ≤ t
    · simp only [candidateComplexLaplaceAtom, indicator_of_mem (show t ∈ Ici (Real.log (n : ℝ)) from ht), Complex.norm_exp]
      simp only [Complex.mul_re, Complex.neg_re, Complex.div_re, Complex.one_re,
        Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im]
      norm_num
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    · simp [candidateComplexLaplaceAtom, ht]
  rw [hsq]
  exact (candidate_integrable_complexLaplaceAtom (s := 1) (by norm_num) n).norm

theorem candidate_integrable_eulerLogProcess (Y : ℕ) (ω : Omega) :
    Integrable (candidateEulerLogProcess Y ω) := by
  apply integrable_finset_sum
  intro n hn
  exact (candidate_integrable_complexLaplaceAtom (s := 1 / 2) (by norm_num) n).mul_const _

theorem candidate_memLp_two_eulerLogProcess (Y : ℕ) (ω : Omega) :
    MemLp (candidateEulerLogProcess Y ω) 2 := by
  apply memLp_finset_sum
  intro n hn
  exact (atom_memLp_two n).mul_const _

/-- Below the Euler prime cutoff, the finite smooth process is exactly the
actual squarefree logarithmic partial sum, including its floor convention. -/
theorem candidate_eulerLogProcess_eq_squarefree (Y : ℕ) (ω : Omega) {t : ℝ}
    (ht : ⌊Real.exp t⌋₊ ≤ Y) :
    candidateEulerLogProcess Y ω t = (harperCandidateSquarefreeLogProcess ω t : ℂ) := by
  classical
  let F : ℕ → ℂ := fun n => candidateComplexLaplaceAtom (1 / 2) n t * (gSquarefree ω n : ℂ)
  let J := candidateEulerSupport Y ∩ Finset.Icc 1 Y
  have hleft : (∑ n ∈ J, F n) = ∑ n ∈ candidateEulerSupport Y, F n := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hn hn'
    have hpos := (candidateEulerSupport_mem hn).1
    have hlog : ¬Real.log (n : ℝ) ≤ t := by
      intro h
      have hnexp := (Nat.le_floor_iff (Real.exp_pos t).le).mpr
        ((Real.log_le_iff_le_exp (Nat.cast_pos.mpr hpos)).mp h)
      exact hn' (Finset.mem_inter.mpr ⟨hn, Finset.mem_Icc.mpr ⟨hpos, hnexp.trans ht⟩⟩)
    simp [F, candidateComplexLaplaceAtom, hlog]
  have hright : (∑ n ∈ J, F n) = ∑ n ∈ Finset.Icc 1 Y, F n := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro n hn hn'
    have hsq : ¬Squarefree n := by
      intro h
      exact hn' (Finset.mem_inter.mpr ⟨candidateEulerSupport_contains
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 h, hn⟩)
    simp [F, gSquarefree_of_not_squarefree ω hsq]
  have hsup := hleft.symm.trans hright
  rw [candidateEulerLogProcess, hsup]
  rw [harperCandidateSquarefreeLogProcess_eq_quotient]
  rw [← min_eq_right ht, candidate_GSquarefree_min_eq_log_indicators,
    Complex.ofReal_div, Complex.ofReal_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hlog : Real.log (n : ℝ) ≤ t
  · simp only [F, candidateComplexLaplaceAtom, indicator_of_mem (show t ∈ Ici (Real.log (n : ℝ)) from hlog), if_pos hlog]
    have he : Complex.exp (-(1 / 2 : ℂ) * t) = (Real.exp (t / 2) : ℂ)⁻¹ := by
      rw [Complex.ofReal_exp, ← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  · simp [F, candidateComplexLaplaceAtom, hlog]

/-- Fourier transform of the actual finite Euler-support process at critical
real part `1/2`, in the negative angular convention of the covariance kernel. -/
theorem candidate_eulerLogProcess_fourier_eq (Y : ℕ) (ω : Omega) (τ : ℝ) :
    (𝓕 (candidateEulerLogProcess Y ω)) (τ / (2 * Real.pi)) =
      candidateEulerAngularApprox Y 0 ω τ := by
  let s : ℂ := (1 / 2 : ℂ) + (τ : ℂ) * Complex.I
  have hs : 0 < s.re := by simp [s]
  rw [Real.fourier_real_eq, candidateEulerAngularApprox_eq_sum]
  have heq (t : ℝ) : Real.fourierChar (-(t * (τ / (2 * Real.pi)))) •
      candidateEulerLogProcess Y ω t =
      ∑ n ∈ candidateEulerSupport Y, candidateComplexLaplaceAtom s n t * (gSquarefree ω n : ℂ) := by
    rw [candidateEulerLogProcess, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases ht : Real.log (n : ℝ) ≤ t
    · simp only [candidateComplexLaplaceAtom, indicator_of_mem (show t ∈ Ici (Real.log (n : ℝ)) from ht), Circle.smul_def,
        smul_eq_mul]
      have hp := candidate_angular_phase_exp 0 τ t
      have hz : ((Real.exp (-0 * t) / Real.exp (t / 2) : ℝ) : ℂ) =
          Complex.exp (-(1 / 2 : ℂ) * t) := by
        simp only [neg_zero, zero_mul, Real.exp_zero, one_div, Complex.ofReal_inv,
          Complex.ofReal_exp, ← Complex.exp_neg]
        congr 1
        push_cast
        ring
      rw [hz] at hp
      simpa only [zero_add, Complex.ofReal_div, Complex.ofReal_one,
        Complex.ofReal_ofNat, s, mul_assoc] using congrArg (fun z : ℂ => z * (gSquarefree ω n : ℂ)) hp
    · simp [candidateComplexLaplaceAtom, ht]
  simp_rw [heq]
  rw [integral_finset_sum _ (fun n _ =>
    (candidate_integrable_complexLaplaceAtom hs n).mul_const _)]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    _ = (∫ t, candidateComplexLaplaceAtom s n t) * (gSquarefree ω n : ℂ) :=
      integral_mul_const _ _
    _ = _ := by
      rw [candidate_integral_complexLaplaceAtom hs]
      simp [candidateEulerDirichletCoefficient, s]

/-- The critical finite Euler transform has exactly the omitted frequency
energy as the `L²` truncation error for its literal arithmetic time process.
The frequency variable here is Fourier's standard frequency `ξ`; its Euler
angular frequency is explicitly `2πξ`. -/
theorem candidate_finiteEuler_hard_cutoff_error_eq (Y : ℕ) (ω : Omega) (H : ℝ) :
    (∫ x, ‖(𝓕⁻ ((Icc (-H) H).indicator
      (fun ξ => candidateEulerAngularApprox Y 0 ω (2 * Real.pi * ξ)))) x -
        candidateEulerLogProcess Y ω x‖ ^ 2) =
      ∫ ξ in (Icc (-H) H)ᶜ,
        ‖candidateEulerAngularApprox Y 0 ω (2 * Real.pi * ξ)‖ ^ 2 := by
  have he : (𝓕 (candidateEulerLogProcess Y ω)) =
      fun ξ => candidateEulerAngularApprox Y 0 ω (2 * Real.pi * ξ) := by
    funext ξ
    have h := candidate_eulerLogProcess_fourier_eq Y ω (2 * Real.pi * ξ)
    simpa only [mul_div_cancel_left₀ ξ (by positivity : 2 * Real.pi ≠ 0)] using h
  simpa only [he] using candidate_hard_fourier_cutoff_error_eq
    (candidate_integrable_eulerLogProcess Y ω) (candidate_memLp_two_eulerLogProcess Y ω) H

end
end Erdos.Problem1144
