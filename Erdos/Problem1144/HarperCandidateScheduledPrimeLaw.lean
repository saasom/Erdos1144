import Erdos.Problem1144.HarperCandidatePrimeWhiteComparisonRates
import Erdos.Problem1144.HarperCandidateGaussianAssembly

open MeasureTheory ProbabilityTheory Set Matrix WithLp
open scoped BigOperators

namespace Erdos.Problem1144

/-- A complete comparison coefficient is exactly the scheduled coefficient,
including its natural-number quotient cutoff and exponential normalization. -/
theorem candidate_complete_comparison_coefficient (ω : Omega) (t : ℝ)
    {p : ℕ} (hp : 0 < p) :
    candidateComparisonProcess false ω (t - Real.log p) / Real.sqrt p =
      S ω (⌊Real.exp t⌋₊ / p) / Real.exp (t / 2) := by
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hcut : ⌊Real.exp (t - Real.log p)⌋₊ = ⌊Real.exp t⌋₊ / p := by
    rw [Real.exp_sub, Real.exp_log hpR, Nat.floor_div_natCast]
  change harperCandidateLogProcess ω (t - Real.log p) / Real.sqrt p = _
  rw [harperCandidateLogProcess_eq_quotient, hcut,
    show (t - Real.log (p : ℝ)) / 2 = t / 2 - Real.log p / 2 by ring,
    Real.exp_sub, Real.exp_half (Real.log p), Real.exp_log hpR]
  field_simp

/-- The whole-bin comparison covariance agrees with the literal common
fresh-prime union. The extra primes in the final whole bin contribute zero. -/
theorem candidate_complete_comparison_prime_covariance_eq_fresh
    {m n : ℕ} (ω : Omega) (u : Fin m → ℝ) (q : Fin n → ℕ)
    (hq : Function.Injective q) (T : ℝ) {h : ℝ} (hh : 0 ≤ h) (b : ℕ)
    (hcover : ∀ i, u i ≤ T + (b : ℝ) * h)
    (himage : Finset.univ.image q =
      candidateGridFreshPrimes ⌊Real.exp T⌋₊ (fun i => ⌊Real.exp (u i)⌋₊)) :
    let c : Matrix (Fin m) (Fin n) ℝ :=
      fun i p => S ω (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2)
    candidateWeightedGram Measure.count
      (fun i => candidateComparisonPrime false ω (u i) T h b) (fun _ => 1) =
      c * cᴴ := by
  classical
  dsimp only
  let P := candidateGridFreshPrimes ⌊Real.exp T⌋₊ (fun i => ⌊Real.exp (u i)⌋₊)
  let R := (Finset.Ioc ⌊Real.exp T⌋₊ ⌊Real.exp (T + (b : ℝ) * h)⌋₊).filter Nat.Prime
  have hPR : P ⊆ R := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hprime, hlow, hu⟩ := mem_largePrimeInterval.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨hlow, hu.trans (Nat.floor_mono (Real.exp_le_exp.mpr (hcover i)))⟩, hprime⟩
  rw [candidate_comparison_prime_covariance_eq false ω u T hh b]
  ext i j
  change (∑ p ∈ R, _) = _
  calc
    _ = ∑ p ∈ P,
        (candidateComparisonProcess false ω (u i - Real.log (p : ℝ)) / Real.sqrt p) *
        (candidateComparisonProcess false ω (u j - Real.log (p : ℝ)) / Real.sqrt p) := by
      symm
      apply Finset.sum_subset hPR
      intro p hp hpP
      obtain ⟨hpR, hpPrime⟩ := Finset.mem_filter.mp hp
      have hlow := (Finset.mem_Ioc.mp hpR).1
      have hi : ⌊Real.exp (u i)⌋₊ < p := by
        by_contra hn
        exact hpP (largePrimeInterval_subset_candidateGridFreshPrimes _ _ i
          (mem_largePrimeInterval.mpr ⟨hpPrime, hlow, Nat.le_of_not_gt hn⟩))
      rw [candidate_complete_comparison_coefficient ω (u i) hpPrime.pos]
      simp [Nat.div_eq_of_lt hi, S]
    _ = ∑ p ∈ P,
        (S ω (⌊Real.exp (u i)⌋₊ / p) / Real.exp (u i / 2)) *
        (S ω (⌊Real.exp (u j)⌋₊ / p) / Real.exp (u j / 2)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpPrime := (Finset.mem_filter.mp (hPR hp)).2
      rw [candidate_complete_comparison_coefficient ω (u i) hpPrime.pos,
        candidate_complete_comparison_coefficient ω (u j) hpPrime.pos]
    _ = _ := by
      rw [show P = Finset.univ.image q from himage.symm, Finset.sum_image]
      · simp [Matrix.mul_apply]
      · exact fun _ _ _ _ he => hq he

/-- The comparison-prime Gaussian crossing is literally the fresh Gaussian
crossing, with its original enumeration and no independent unused noises. -/
theorem candidate_complete_comparison_prime_crossing_eq_fresh
    {m n : ℕ} (ω : Omega) (u : Fin m → ℝ) (q : Fin n → ℕ)
    (hq : Function.Injective q) (T : ℝ) {h : ℝ} (hh : 0 ≤ h) (b : ℕ)
    (hcover : ∀ i, u i ≤ T + (b : ℝ) * h)
    (himage : Finset.univ.image q =
      candidateGridFreshPrimes ⌊Real.exp T⌋₊ (fun i => ⌊Real.exp (u i)⌋₊))
    (J : Omega → Finset (Fin m)) (K : ℝ) :
    candidateComparisonPrimeCrossing false u T h b J K ω =
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).real
        {g | ∃ i ∈ J ω, K < |∑ p,
          (S ω (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2)) * g p|} := by
  have hs : MeasurableSet {x : EuclideanSpace ℝ (Fin m) | ∃ i ∈ J ω, K < |x i|} := by
    simp only [setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    exact (if hi : i ∈ J ω then by
      simpa only [hi, true_and] using
        (measurableSet_lt (measurable_const : Measurable (fun _ : EuclideanSpace ℝ (Fin m) => K))
          (show Measurable (fun x : EuclideanSpace ℝ (Fin m) => |x i|) by fun_prop))
      else by simp only [hi, false_and, setOf_false, MeasurableSet.empty])
  unfold candidateComparisonPrimeCrossing
  rw [candidate_complete_comparison_prime_covariance_eq_fresh ω u q hq T hh b hcover himage]
  exact ((candidate_measurePreserving_pi_gaussian_linear
    (fun i p => S ω (⌊Real.exp (u i)⌋₊ / q p) / Real.exp (u i / 2))).measureReal_preimage
      hs.nullMeasurableSet).symm

end Erdos.Problem1144
