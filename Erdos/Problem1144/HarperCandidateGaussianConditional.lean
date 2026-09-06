import Erdos.Problem1144.HarperCandidateGaussianFiber

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos.Problem1144

private theorem candidate_measurable_selected_linear_crossing {n m : ℕ}
    (a : Omega → Fin n → Fin m → ℝ) (J : Omega → Finset (Fin m))
    (ha : ∀ p i, Measurable fun omega => a omega p i)
    (hJ : ∀ i, MeasurableSet {omega | i ∈ J omega}) (K : ℝ) :
    MeasurableSet {z : Omega × (Fin n → ℝ) |
      ∃ i ∈ J z.1, K ≤ |∑ p, a z.1 p i * z.2 p|} ∧
    MeasurableSet {z : Omega × (Fin n → ℝ) |
      ∃ i ∈ J z.1, K < |∑ p, a z.1 p i * z.2 p|} := by
  have hf (i : Fin m) : Measurable fun z : Omega × (Fin n → ℝ) =>
      |∑ p, a z.1 p i * z.2 p| := by
    apply Measurable.abs
    apply Finset.measurable_sum
    intro p _
    exact ((ha p i).comp measurable_fst).mul ((measurable_pi_apply p).comp measurable_snd)
  constructor <;> simp only [Set.setOf_exists] <;> apply MeasurableSet.iUnion <;> intro i
  · exact ((hJ i).preimage measurable_fst).inter (measurableSet_le measurable_const (hf i))
  · exact ((hJ i).preimage measurable_fst).inter (measurableSet_lt measurable_const (hf i))

/-- The actual fixed-cylinder Rademacher-to-Gaussian replacement. The old
selector is allowed to use the entire old field. Its dependence is handled
by exact fresh-flip fibers before averaging the uniform exponential error. -/
theorem candidate_conditional_selected_fresh_max_comparison
    {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (s : Finset ℕ) (eta : s → Bool)
      (u : Fin m → ℝ) (q : Fin n → ℕ) (T β b ρ : ℝ),
      Function.Injective q → Real.log 2 ≤ T →
      (∀ p ∈ s, p ≤ ⌊Real.exp T⌋₊) → (∀ p, ⌊Real.exp T⌋₊ < q p) →
      (∀ i, ⌊Real.exp (u i)⌋₊ < ⌊Real.exp T⌋₊ ^ 2) →
      (∀ i, u i ≤ β * T) →
      let J := candidateRetainedIndices
        (fun omega i => harperCandidateLogOld omega ⌊Real.exp T⌋₊ (u i)) b ρ
      let a : Omega → Fin n → Fin m → ℝ := fun omega p i =>
        S omega (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2)
      (∫ omega, (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
        {v | ∃ i ∈ J omega, K + δ ≤ |∑ p, a omega p i * v p|}
          ∂candidateCylinderLaw s eta) ≤
        (candidateCylinderLaw s eta).real
          {omega | ∃ i ∈ J omega, K < |∑ p, a omega p i * eps omega (q p)|} +
        C * (m : ℝ) ^ 3 * Real.exp ((3 * β / 2 - 2) * T) := by
  classical
  obtain ⟨C, hC, hcomp⟩ := candidate_selected_fresh_max_rademacher_comparison hK hδ
  refine ⟨C, hC, ?_⟩
  intro n m s eta u q T β b ρ hq hT hs hqT hcut hu
  dsimp only
  let P := candidateCylinderLaw s eta
  let G := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let R := Measure.pi (fun _ : Fin n => candidateRademacherLaw)
  let J := candidateRetainedIndices
    (fun omega i => harperCandidateLogOld omega ⌊Real.exp T⌋₊ (u i)) b ρ
  let a : Omega → Fin n → Fin m → ℝ := fun omega p i =>
    S omega (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2)
  have ha (p : Fin n) (i : Fin m) : Measurable fun omega => a omega p i :=
    (measurable_S _).div_const _
  have hJ (i : Fin m) : MeasurableSet {omega | i ∈ J omega} :=
    measurableSet_mem_candidateRetainedIndices _
      (fun i => measurable_harperCandidateLogOld _ (u i)) b ρ i
  have hGint : Integrable (fun omega => G.real
      {v | ∃ i ∈ J omega, K + δ ≤ |∑ p, a omega p i * v p|}) P := by
    exact Measure.integrable_measure_prodMk_left
      (candidate_measurable_selected_linear_crossing a J ha hJ (K + δ)).1 (by finiteness)
  have hRint : Integrable (fun omega => R.real
      {v | ∃ i ∈ J omega, K < |∑ p, a omega p i * v p|}) P := by
    exact Measure.integrable_measure_prodMk_left
      (candidate_measurable_selected_linear_crossing a J ha hJ K).2 (by finiteness)
  have hE : MeasurableSet {omega | ∃ i ∈ J omega,
      K < |∑ p, a omega p i * eps omega (q p)|} := by
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    exact (hJ i).inter (measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun p _ => (ha p i).mul (measurable_eps (q p))).abs)
  have hR : (∫ omega, R.real
      {v | ∃ i ∈ J omega, K < |∑ p, a omega p i * v p|} ∂P) =
      P.real {omega | ∃ i ∈ J omega, K < |∑ p, a omega p i * eps omega (q p)|} := by
    apply candidate_selected_fresh_sign_fiber_average q hq a J _ _ P _ K hE
    · intro omega v
      funext p i
      exact candidate_log_fresh_coefficient_freshFlipSet q u _ hqT hcut omega v p i
    · intro omega v
      exact candidate_log_retained_freshFlipSet q u _ hqT b ρ omega v
    · intro v
      apply candidateCylinderLaw_freshFlipSet
      intro p hp
      exact (not_lt_of_ge (hs _ hp)) (hqT p)
  have hi := integral_mono hGint (hRint.add
    (integrable_const (C * (m : ℝ) ^ 3 * Real.exp ((3 * β / 2 - 2) * T))))
    (fun omega => hcomp n m omega u q hq (J omega) T β hT hqT hu)
  simp only [Pi.add_apply] at hi
  rw [integral_add hRint (integrable_const _), hR] at hi
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hi

/-- Enumerating the common fresh-prime union gives the literal log-time
fresh process at each grid point. Extra primes have quotient cutoff zero. -/
theorem candidate_fresh_linear_sum_eq_logFresh {n m : ℕ}
    (q : Fin n → ℕ) (hq : Function.Injective q) (u : Fin m → ℝ) (X : ℕ)
    (himage : Finset.univ.image q =
      candidateGridFreshPrimes X (fun i => ⌊Real.exp (u i)⌋₊))
    (omega : Omega) (i : Fin m) (hui : 0 ≤ u i) :
    (∑ p, (S omega (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2)) *
      eps omega (q p)) = harperCandidateLogFresh omega X (u i) := by
  classical
  let P := candidateGridFreshPrimes X (fun i => ⌊Real.exp (u i)⌋₊)
  have hsum : (∑ p ∈ P, eps omega p * S omega (⌊Real.exp (u i)⌋₊ / p)) =
      largePrimeContribution omega X ⌊Real.exp (u i)⌋₊ := by
    symm
    apply Finset.sum_subset (largePrimeInterval_subset_candidateGridFreshPrimes X _ i)
    intro p hp hpi
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    have hprime := (mem_largePrimeInterval.mp hj).1
    have hXp := (mem_largePrimeInterval.mp hj).2.1
    have hNp : ⌊Real.exp (u i)⌋₊ < p := by
      by_contra h
      exact hpi (mem_largePrimeInterval.mpr ⟨hprime, hXp, Nat.le_of_not_gt h⟩)
    simp [Nat.div_eq_of_lt hNp, S]
  have hN : 0 < ⌊Real.exp (u i)⌋₊ := by
    apply Nat.floor_pos.mpr
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hui
  have hsqrt : Real.sqrt (⌊Real.exp (u i)⌋₊ : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))
  calc
    _ = (∑ p ∈ P, eps omega p * S omega (⌊Real.exp (u i)⌋₊ / p)) /
        Real.exp (u i / 2) := by
      dsimp only [P]
      rw [Finset.sum_div, ← himage, Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro p _
        ring
      · exact fun _ _ _ _ h => hq h
    _ = largePrimeContribution omega X ⌊Real.exp (u i)⌋₊ / Real.exp (u i / 2) := by
      rw [hsum]
    _ = _ := by
      unfold harperCandidateLogFresh largePrimeProcess harperCandidateLogNormalization
      field_simp

/-- The final replacement inequality on the candidate's literal log-fresh
process, conditioned on any fixed old assignment. -/
theorem candidate_conditional_logFresh_max_comparison
    {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (s : Finset ℕ) (eta : s → Bool)
      (u : Fin m → ℝ) (q : Fin n → ℕ) (T β b ρ : ℝ),
      Function.Injective q → Real.log 2 ≤ T →
      (∀ p ∈ s, p ≤ ⌊Real.exp T⌋₊) →
      Finset.univ.image q = candidateGridFreshPrimes ⌊Real.exp T⌋₊
        (fun i => ⌊Real.exp (u i)⌋₊) →
      (∀ i, 0 ≤ u i ∧ ⌊Real.exp (u i)⌋₊ < ⌊Real.exp T⌋₊ ^ 2) →
      (∀ i, u i ≤ β * T) →
      let J := candidateRetainedIndices
        (fun omega i => harperCandidateLogOld omega ⌊Real.exp T⌋₊ (u i)) b ρ
      (∫ omega, (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
        {v | ∃ i ∈ J omega, K + δ ≤ |∑ p,
          (S omega (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2)) * v p|}
          ∂candidateCylinderLaw s eta) ≤
        (candidateCylinderLaw s eta).real {omega | ∃ i ∈ J omega,
          K < |harperCandidateLogFresh omega ⌊Real.exp T⌋₊ (u i)|} +
        C * (m : ℝ) ^ 3 * Real.exp ((3 * β / 2 - 2) * T) := by
  obtain ⟨C, hC, hcomp⟩ := candidate_conditional_selected_fresh_max_comparison hK hδ
  refine ⟨C, hC, ?_⟩
  intro n m s eta u q T β b ρ hq hT hs himage hcut hu
  have hqT (p : Fin n) : ⌊Real.exp T⌋₊ < q p := by
    apply candidateGridFreshPrimes_above _ (fun i => ⌊Real.exp (u i)⌋₊)
    rw [← himage]
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
  have h := hcomp n m s eta u q T β b ρ hq hT hs hqT (fun i => (hcut i).2) hu
  have hsum (omega : Omega) (i : Fin m) :=
    candidate_fresh_linear_sum_eq_logFresh q hq u _ himage omega i (hcut i).1
  dsimp only at h ⊢
  simpa only [hsum] using h

end Erdos.Problem1144
