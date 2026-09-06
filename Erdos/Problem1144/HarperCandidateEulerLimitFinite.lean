import Erdos.Problem1144.HarperCandidateGaussianVariance
import Erdos.Problem1144.HarperCandidateSpectralTail
import Erdos.Problem1144.HarperRankinParseval
import Mathlib.Analysis.Convex.Integral

open Finset MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Erdos.Problem1144
noncomputable section

/-- The integers represented by the literal finite squarefree Euler product. -/
def candidateEulerSupport (Y : ℕ) : Finset ℕ :=
  ((Y + 1).primesBelow.powerset).image Problem520.freshProduct

private theorem support_prime {Y : ℕ} {S : Finset ℕ}
    (hS : S ∈ (Y + 1).primesBelow.powerset) : ∀ p ∈ S, p.Prime :=
  fun p hp => Nat.prime_of_mem_primesBelow ((Finset.mem_powerset.mp hS) hp)

private theorem support_inj (Y : ℕ) :
    Set.InjOn Problem520.freshProduct (↑(Y + 1).primesBelow.powerset : Set (Finset ℕ)) := by
  intro S hS T hT he
  simpa only [Problem520.freshProduct_primeFactors (support_prime hS),
    Problem520.freshProduct_primeFactors (support_prime hT)] using congrArg Nat.primeFactors he

/-- Every Euler integer is positive and squarefree. -/
theorem candidateEulerSupport_mem {Y n : ℕ} (hn : n ∈ candidateEulerSupport Y) :
    0 < n ∧ Squarefree n := by
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hn
  exact ⟨Problem520.freshProduct_pos_of_primes (support_prime hS),
    Problem520.freshProduct_squarefree (support_prime hS)⟩

/-- All squarefree integers up to the prime cutoff occur in the Euler product. -/
theorem candidateEulerSupport_contains {Y n : ℕ} (hn : 0 < n)
    (hnY : n ≤ Y) (hsq : Squarefree n) : n ∈ candidateEulerSupport Y := by
  refine Finset.mem_image.mpr ⟨n.primeFactors, Finset.mem_powerset.mpr ?_, ?_⟩
  · intro p hp
    obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by have := Nat.le_of_dvd hn hpn; omega, hpp⟩
  · exact Nat.prod_primeFactors_of_squarefree hsq

/-- The finite prime Euler transform, in the actual negative angular convention. -/
def candidateEulerAngularApprox (Y : ℕ) (σ : ℝ) (ω : Omega) (τ : ℝ) : ℂ :=
  harperRankinDirichletPolynomial Y (2 * σ) ω (-τ) /
    (((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)

def candidateEulerDirichletCoefficient (σ τ : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (-(((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) * Real.log n) /
    (((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I)

private theorem coeff_phase (σ τ : ℝ) {n : ℕ} (hn : 0 < n) (c : ℝ) :
    ((c / Real.sqrt ((n : ℝ) ^ (1 + 2 * σ)) : ℝ) : ℂ) *
        Complex.exp (((-τ * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) /
        (((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) = candidateEulerDirichletCoefficient σ τ n * (c : ℂ) := by
  have hsqrt : Real.sqrt ((n : ℝ) ^ (1 + 2 * σ)) =
      Real.exp ((σ + 1 / 2) * Real.log (n : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg n),
      Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
    congr 1
    ring
  have hexp : Complex.exp (-(((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) *
      Real.log (n : ℝ)) =
      (Real.exp ((σ + 1 / 2) * Real.log (n : ℝ)) : ℂ)⁻¹ *
        Complex.exp (((-τ * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [show -(((σ + 1 / 2 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) * Real.log (n : ℝ) =
      -(((σ + 1 / 2) * Real.log (n : ℝ) : ℝ) : ℂ) +
        (((-τ * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp]
  rw [hsqrt, Complex.ofReal_div, candidateEulerDirichletCoefficient, hexp]
  ring

/-- The Euler transform is a squarefree Dirichlet polynomial on its exact
integer support, including smooth integers larger than the prime cutoff. -/
theorem candidateEulerAngularApprox_eq_sum (Y : ℕ) (σ : ℝ) (ω : Omega) (τ : ℝ) :
    candidateEulerAngularApprox Y σ ω τ =
      ∑ n ∈ candidateEulerSupport Y, candidateEulerDirichletCoefficient σ τ n * (gSquarefree ω n : ℂ) := by
  classical
  unfold candidateEulerAngularApprox harperRankinDirichletPolynomial
  rw [Finset.sum_div, candidateEulerSupport, Finset.sum_image (support_inj Y)]
  apply Finset.sum_congr rfl
  intro S hS
  rw [candidate_gSquarefree_eq_problem520,
    Problem520.f_freshProduct ω (support_prime hS)]
  exact coeff_phase σ τ (Problem520.freshProduct_pos_of_primes (support_prime hS)) _

theorem candidateEulerAngularApprox_sub_integer_eq_sum (Y : ℕ) (σ : ℝ) (ω : Omega) (τ : ℝ) :
    candidateEulerAngularApprox Y σ ω τ -
      (∑ n ∈ Finset.Icc 1 Y, candidateEulerDirichletCoefficient σ τ n * (gSquarefree ω n : ℂ)) =
      ∑ n ∈ candidateEulerSupport Y \ Finset.Icc 1 Y,
        candidateEulerDirichletCoefficient σ τ n * (gSquarefree ω n : ℂ) := by
  classical
  let S := candidateEulerSupport Y
  let J := S ∩ Finset.Icc 1 Y
  have hi : (∑ n ∈ Finset.Icc 1 Y, candidateEulerDirichletCoefficient σ τ n * (gSquarefree ω n : ℂ)) =
      ∑ n ∈ J, candidateEulerDirichletCoefficient σ τ n * (gSquarefree ω n : ℂ) := by
    symm
    apply Finset.sum_subset Finset.inter_subset_right
    intro n hn hnot
    have hsq : ¬Squarefree n := by
      intro h
      exact hnot (Finset.mem_inter.mpr ⟨candidateEulerSupport_contains
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 h, hn⟩)
    simp [gSquarefree_of_not_squarefree ω hsq]
  have hd : S \ J = S \ Finset.Icc 1 Y := by ext n; simp [J]
  rw [candidateEulerAngularApprox_eq_sum, hi]
  have h := Finset.sum_sdiff (f := fun n => candidateEulerDirichletCoefficient σ τ n * (gSquarefree ω n : ℂ))
    (show J ⊆ S from Finset.inter_subset_left)
  rw [hd] at h
  exact sub_eq_iff_eq_add.mpr h.symm

/-- The positive Dirichlet mass remaining above the integer cutoff. -/
def candidateEulerTailMass (Y : ℕ) (σ : ℝ) : ℝ :=
  (∑' n : ℕ, (n : ℝ) ^ (-(1 + 2 * σ))) -
    ∑ n ∈ Finset.range (Y + 1), (n : ℝ) ^ (-(1 + 2 * σ))

theorem candidateEulerTailMass_nonneg (Y : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ candidateEulerTailMass Y σ := by
  apply sub_nonneg.mpr
  exact (Real.summable_nat_rpow.mpr (by linarith : -(1 + 2 * σ) < -1)).sum_le_tsum _
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem candidateEulerTailMass_tendsto {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun Y => candidateEulerTailMass Y σ) atTop (𝓝 0) := by
  have h := (Real.summable_nat_rpow.mpr (by linarith : -(1 + 2 * σ) < -1)).hasSum.tendsto_sum_nat
  have hshift : Tendsto (fun Y : ℕ => Y + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) tendsto_id
  simpa only [candidateEulerTailMass, Function.comp_def, sub_self] using
    (tendsto_const_nhds (x := ∑' n : ℕ, (n : ℝ) ^ (-(1 + 2 * σ)))).sub (h.comp hshift)

/-- Orthogonality controls the prime-cutoff error by the ordinary Dirichlet
tail, uniformly in angular frequency. -/
theorem candidate_integral_euler_sub_integer_sq_le (Y : ℕ) {σ : ℝ}
    (hσ : 0 < σ) (τ : ℝ) :
    (∫ ω, ‖candidateEulerAngularApprox Y σ ω τ -
      (∑ n ∈ Finset.Icc 1 Y, candidateEulerDirichletCoefficient σ τ n * (gSquarefree ω n : ℂ))‖ ^ 2 ∂mu) ≤
      candidateEulerTailMass Y σ / ((σ + 1 / 2) ^ 2 + τ ^ 2) := by
  classical
  simp_rw [candidateEulerAngularApprox_sub_integer_eq_sum]
  let S := candidateEulerSupport Y \ Finset.Icc 1 Y
  have hpos (n : ℕ) (hn : n ∈ S) : 0 < n :=
    (candidateEulerSupport_mem (Finset.mem_sdiff.mp hn).1).1
  refine (candidate_integral_complex_squarefree_sum_norm_sq_le S (candidateEulerDirichletCoefficient σ τ) hpos).trans ?_
  have hd : Disjoint S (Finset.range (Y + 1)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hnR
    have hnS := Finset.mem_sdiff.mp hn
    exact hnS.2 (Finset.mem_Icc.mpr ⟨hpos n hn, by simpa using Finset.mem_range.mp hnR⟩)
  have hm : (∑ n ∈ S, (n : ℝ) ^ (-(1 + 2 * σ))) ≤ candidateEulerTailMass Y σ := by
    have hb := (Real.summable_nat_rpow.mpr (by linarith : -(1 + 2 * σ) < -1)).sum_le_tsum
      (S ∪ Finset.range (Y + 1)) (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    rw [Finset.sum_union hd] at hb
    exact (le_sub_iff_add_le).mpr hb
  calc
    (∑ n ∈ S, ‖candidateEulerDirichletCoefficient σ τ n‖ ^ 2) =
        (∑ n ∈ S, (n : ℝ) ^ (-(1 + 2 * σ))) / ((σ + 1 / 2) ^ 2 + τ ^ 2) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun n hn => candidate_squarefree_dirichletCoefficient_norm_sq σ τ (hpos n hn)
    _ ≤ _ := div_le_div_of_nonneg_right hm (by positivity)

/-- The finite prime transforms are jointly measurable in signs and frequency. -/
theorem measurable_candidateEulerAngularApprox (Y : ℕ) (σ : ℝ) :
    Measurable fun z : Omega × ℝ => candidateEulerAngularApprox Y σ z.1 z.2 := by
  simp_rw [candidateEulerAngularApprox_eq_sum]
  apply Finset.measurable_sum
  intro n hn
  have hg : Measurable (fun z : Omega × ℝ => gSquarefree z.1 n) :=
    (measurable_gSquarefree n).comp measurable_fst
  unfold candidateEulerDirichletCoefficient
  fun_prop

/-- Every finite prime transform has an integrable squared norm. -/
theorem candidate_integrable_eulerAngularApprox_sq (Y : ℕ) (σ τ : ℝ) :
    Integrable (fun ω => ‖candidateEulerAngularApprox Y σ ω τ‖ ^ 2) mu := by
  simp_rw [candidateEulerAngularApprox_eq_sum]
  exact candidate_integrable_complex_squarefree_sum_norm_sq _ _

/-- The square of the exact prime versus integer cutoff error is integrable. -/
theorem candidate_integrable_euler_sub_integer_sq (Y : ℕ) (σ τ : ℝ) :
    Integrable (fun ω => ‖candidateEulerAngularApprox Y σ ω τ -
      ∑ n ∈ Finset.Icc 1 Y, candidateEulerDirichletCoefficient σ τ n * (gSquarefree ω n : ℂ)‖ ^ 2) mu := by
  simp_rw [candidateEulerAngularApprox_sub_integer_eq_sum]
  exact candidate_integrable_complex_squarefree_sum_norm_sq _ _

end
end Erdos.Problem1144
