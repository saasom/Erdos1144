import Erdos.Problem1144.HarperCandidateCovarianceArithmeticMoments

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem1144

noncomputable section

/-!
# Strong-barrier prefix removal for literal Euler mixed moments

This is the deterministic removal of the small-prime factors followed by
the actual independent mixed-moment estimate.  The event in the integral
is defined by the displayed Euler-prefix inequalities, not by an opaque
good-event predicate or a moment certificate.  The probability that the
strong barrier can replace Harper's weaker barrier is a separate input
and is not claimed here.
-/

/-- On the displayed prefix barrier, the product of the full Euler energies
is bounded by the barrier heights times precisely the factors that remain
above each prefix. -/
theorem candidate_mixedEuler_le_barrier_residual
    {ι : Type*} [Fintype ι] (y : ℕ)
    (A : ι → Finset (Problem520.HarperPrimeIndex y)) (t B : ι → ℝ)
    (η : Problem520.HarperPrimeCube y)
    (hgood : ∀ i, (∏ p ∈ A i,
      Problem520.harperCoordinateFactor p.1 (t i) (η p)) ≤ B i) :
    (∏ i, ∏ p : Problem520.HarperPrimeIndex y,
      Problem520.harperCoordinateFactor p.1 (t i) (η p)) ≤
      (∏ i, B i) * (∏ p : Problem520.HarperPrimeIndex y,
        ∏ i ∈ Finset.univ.filter (fun i => p ∉ A i),
          Problem520.harperCoordinateFactor p.1 (t i) (η p)) := by
  classical
  let f : ι → Problem520.HarperPrimeIndex y → ℝ :=
    fun i p => Problem520.harperCoordinateFactor p.1 (t i) (η p)
  have hf i p : 0 ≤ f i p :=
    Problem520.harperCoordinateFactor_nonneg p.1 (t i) (η p)
  have hsplit i : (∏ p, f i p) = (∏ p ∈ A i, f i p) *
      ∏ p, if p ∈ A i then 1 else f i p := by
    rw [← show (∏ p : Problem520.HarperPrimeIndex y,
        if p ∈ A i then f i p else 1) = ∏ p ∈ A i, f i p by
      rw [Finset.prod_ite_mem, Finset.univ_inter]]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p _
    split_ifs <;> simp
  have hres : (∏ i, ∏ p : Problem520.HarperPrimeIndex y,
      if p ∈ A i then 1 else f i p) =
      ∏ p : Problem520.HarperPrimeIndex y,
        ∏ i ∈ Finset.univ.filter (fun i => p ∉ A i), f i p := by
    simp only [Finset.prod_filter, ite_not]
    exact Finset.prod_comm
  change (∏ i, ∏ p, f i p) ≤ _
  simp_rw [hsplit]
  rw [Finset.prod_mul_distrib, hres]
  exact mul_le_mul_of_nonneg_right
    (Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun p _ => hf i p)
      (fun i _ => hgood i))
    (Finset.prod_nonneg fun p _ => Finset.prod_nonneg fun i _ => hf i p)

/-- The barrier-truncated joint Euler moment is bounded by the explicit
mixed-prime exponent of the residual factors. -/
theorem candidate_integral_barrier_mixedEuler_cube_le
    {ι : Type*} [Fintype ι] (y : ℕ)
    (A : ι → Finset (Problem520.HarperPrimeIndex y)) (t B : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) :
    (∫ η, {η | ∀ i, (∏ p ∈ A i,
        Problem520.harperCoordinateFactor p.1 (t i) (η p)) ≤ B i}.indicator
      (fun η => ∏ i, ∏ p : Problem520.HarperPrimeIndex y,
        Problem520.harperCoordinateFactor p.1 (t i) (η p)) η
      ∂Problem520.harperFairCubeLaw y) ≤
      (∏ i, B i) * Real.exp (∑ p : Problem520.HarperPrimeIndex y,
        if 4 ≤ p.1 then candidateEulerMixedExponent p.1
          (Finset.univ.filter (fun i => p ∉ A i)) t
        else (Finset.univ.filter (fun i => p ∉ A i)).card * Real.log 4) := by
  classical
  let I : Problem520.HarperPrimeIndex y → Finset ι :=
    fun p => Finset.univ.filter (fun i => p ∉ A i)
  let R : Problem520.HarperPrimeCube y → ℝ := fun η =>
    ∏ p : Problem520.HarperPrimeIndex y,
      ∏ i ∈ I p, Problem520.harperCoordinateFactor p.1 (t i) (η p)
  have hprodB : 0 ≤ ∏ i, B i := Finset.prod_nonneg fun i _ => hB i
  have hR η : 0 ≤ R η := Finset.prod_nonneg fun p _ =>
    Finset.prod_nonneg fun i _ => Problem520.harperCoordinateFactor_nonneg p.1 (t i) (η p)
  calc
    _ ≤ ∫ η, (∏ i, B i) * R η ∂Problem520.harperFairCubeLaw y := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro η
      simp only [Set.indicator, Set.mem_setOf_eq]
      by_cases hgood : ∀ i, (∏ p ∈ A i,
          Problem520.harperCoordinateFactor p.1 (t i) (η p)) ≤ B i
      · rw [if_pos hgood]
        exact candidate_mixedEuler_le_barrier_residual y A t B η hgood
      · rw [if_neg hgood]
        exact mul_nonneg hprodB (hR η)
    _ = (∏ i, B i) * ∫ η, R η ∂Problem520.harperFairCubeLaw y :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (candidate_integral_mixedEuler_cube_le_all_primes y I t) hprodB

/-- The same prefix-removal bound for the literal infinite Rademacher
space, with arbitrary finite sets of primes removed at each height. -/
theorem candidate_integral_barrier_mixedEuler_le
    {ι : Type*} [Fintype ι] (y : ℕ)
    (A : ι → Finset (Problem520.HarperPrimeIndex y)) (t B : ι → ℝ)
    (hB : ∀ i, 0 ≤ B i) :
    (∫ ω, {ω | ∀ i, (∏ p ∈ A i,
        Problem520.harperEulerFactor ω p.1 (t i)) ≤ B i}.indicator
      (fun ω => ∏ i, Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      (∏ i, B i) * Real.exp (∑ p : Problem520.HarperPrimeIndex y,
        if 4 ≤ p.1 then candidateEulerMixedExponent p.1
          (Finset.univ.filter (fun i => p ∉ A i)) t
        else (Finset.univ.filter (fun i => p ∉ A i)).card * Real.log 4) := by
  classical
  have h := candidate_integral_barrier_mixedEuler_cube_le y A t B hB
  rw [Problem520.harperFairCubeLaw,
    ← Problem520.integral_comp_harperPrimeRestriction_mu] at h
  have hfull (ω : Problem520.Omega) :
      (∏ i, Problem520.harperEulerDensity y ω (t i)) =
        ∏ i, ∏ p : Problem520.HarperPrimeIndex y,
          Problem520.harperEulerFactor ω p.1 (t i) := by
    apply Finset.prod_congr rfl
    intro i _
    exact (Finset.prod_coe_sort ((y + 1).primesBelow)
      (fun p => Problem520.harperEulerFactor ω p (t i))).symm
  simpa only [Problem520.harperCoordinateFactor,
    Problem520.harperPrimeRestriction_apply, Problem520.harperEulerFactor,
    Problem520.ε, hfull] using h

/-- A natural Euler-product cutoff is exactly the corresponding prefix in
the common prime cube. -/
theorem candidate_eulerDensity_eq_primeCube_prefix
    (y c : ℕ) (hc : c ≤ y) (ω : Problem520.Omega) (t : ℝ) :
    Problem520.harperEulerDensity c ω t =
      ∏ p ∈ Finset.univ.filter (fun p : Problem520.HarperPrimeIndex y => p.1 ≤ c),
        Problem520.harperEulerFactor ω p.1 t := by
  classical
  symm
  calc
    _ = ∏ p ∈ (y + 1).primesBelow,
        if p ≤ c then Problem520.harperEulerFactor ω p t else 1 := by
      rw [Finset.prod_filter]
      exact Finset.prod_coe_sort ((y + 1).primesBelow)
        (fun p => if p ≤ c then Problem520.harperEulerFactor ω p t else 1)
    _ = ∏ p ∈ ((y + 1).primesBelow).filter (fun p => p ≤ c),
        Problem520.harperEulerFactor ω p t := (Finset.prod_filter _ _).symm
    _ = Problem520.harperEulerDensity c ω t := by
      unfold Problem520.harperEulerDensity
      congr 1
      ext p
      simp only [Finset.mem_filter, Nat.mem_primesBelow]
      constructor
      · rintro ⟨⟨_, hp⟩, hpc⟩
        exact ⟨by omega, hp⟩
      · rintro ⟨hpc, hp⟩
        exact ⟨⟨by omega, hp⟩, by omega⟩

/-- Literal cutoff version of the barrier-truncated mixed moment.  It
applies directly to the prime prefixes selected from the ordered height
gaps in Harper's resonant covariance calculation. -/
theorem candidate_integral_prefixBarrier_mixedEuler_le
    {ι : Type*} [Fintype ι] (y : ℕ) (c : ι → ℕ) (hc : ∀ i, c i ≤ y)
    (t B : ι → ℝ) (hB : ∀ i, 0 ≤ B i) :
    (∫ ω, {ω | ∀ i, Problem520.harperEulerDensity (c i) ω (t i) ≤ B i}.indicator
      (fun ω => ∏ i, Problem520.harperEulerDensity y ω (t i)) ω ∂Problem520.μ) ≤
      (∏ i, B i) * Real.exp (∑ p : Problem520.HarperPrimeIndex y,
        if 4 ≤ p.1 then candidateEulerMixedExponent p.1
          (Finset.univ.filter (fun i => c i < p.1)) t
        else (Finset.univ.filter (fun i => c i < p.1)).card * Real.log 4) := by
  classical
  have hpref (ω : Problem520.Omega) (i : ι) :=
    (candidate_eulerDensity_eq_primeCube_prefix y (c i) (hc i) ω (t i)).symm
  have h := candidate_integral_barrier_mixedEuler_le y
    (fun i => Finset.univ.filter (fun p : Problem520.HarperPrimeIndex y => p.1 ≤ c i))
    t B hB
  simpa only [hpref, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using h

end

end Erdos.Problem1144
