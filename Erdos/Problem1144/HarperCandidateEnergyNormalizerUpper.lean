import Erdos.Problem1144.HarperCandidateEnergyNormalizer
import Erdos.Problem1144.HarperCandidateSpectralTail

open Finset
open scoped BigOperators

namespace Erdos.Problem1144

private theorem candidate_prod_rankinRadius_sq (S : Finset ℕ) (a : ℝ) :
    (∏ p ∈ S, harperRankinEulerRadius p a ^ 2) =
      (Problem520.freshProduct S : ℝ) ^ (-(1 + a)) := by
  unfold harperRankinEulerRadius Problem520.freshProduct
  have hlocal (p : ℕ) : ((p : ℝ) ^ (-(1 + a) / 2)) ^ 2 =
      (p : ℝ) ^ (-(1 + a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1
    norm_num
  simp_rw [hlocal]
  rw [Real.finset_prod_rpow]
  · rw [Nat.cast_prod]
  · intro p hp
    positivity

/-- The literal finite shifted Euler normalizer is bounded by the full
positive Dirichlet series. The proof expands over distinct squarefree integers. -/
theorem candidate_rankinNormalizer_le_dirichletMass (y : ℕ) {a : ℝ} (ha : 0 < a) :
    harperRankinPrimeEnergyNormalizer y a ≤
      ∑' n : ℕ, (n : ℝ) ^ (-(1 + a)) := by
  let P : Finset ℕ := (y + 1).primesBelow
  have hinj : Set.InjOn Problem520.freshProduct (↑P.powerset : Set (Finset ℕ)) := by
    intro S hS T hT heq
    have hSp : ∀ p ∈ S, p.Prime := fun p hp =>
      Nat.prime_of_mem_primesBelow ((Finset.mem_powerset.mp hS) hp)
    have hTp : ∀ p ∈ T, p.Prime := fun p hp =>
      Nat.prime_of_mem_primesBelow ((Finset.mem_powerset.mp hT) hp)
    have h := congrArg Nat.primeFactors heq
    simpa only [Problem520.freshProduct_primeFactors hSp,
      Problem520.freshProduct_primeFactors hTp] using h
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ (-(1 + a)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  calc
    harperRankinPrimeEnergyNormalizer y a =
        ∑ S ∈ P.powerset, (Problem520.freshProduct S : ℝ) ^ (-(1 + a)) := by
      unfold harperRankinPrimeEnergyNormalizer harperRankinEulerNormalizer
      rw [Finset.prod_one_add]
      exact Finset.sum_congr rfl fun S hS => candidate_prod_rankinRadius_sq S a
    _ = ∑ n ∈ P.powerset.image Problem520.freshProduct,
        (n : ℝ) ^ (-(1 + a)) :=
      (Finset.sum_image (f := fun n : ℕ => (n : ℝ) ^ (-(1 + a))) hinj).symm
    _ ≤ _ := hsum.sum_le_tsum _ (fun n hn => Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Uniform upper bound for every finite cutoff and positive shift. -/
theorem candidate_rankinNormalizer_upper (y : ℕ) {a : ℝ} (ha : 0 < a) :
    harperRankinPrimeEnergyNormalizer y a ≤ 1 + 1 / a := by
  have hmass := candidate_squarefree_dirichletMass_le (σ := a / 2) (by positivity)
  have heq : 2 * (a / 2) = a := by ring
  rw [heq] at hmass
  exact (candidate_rankinNormalizer_le_dirichletMass y ha).trans hmass

/-- The large-prime Euler factor has the inverse effective-window bound
needed when conditioning on all primes below the smaller cutoff. -/
theorem candidate_largePrime_rankinNormalizer_upper
    {y Y : ℕ} (hy : 4 ≤ y) (hyY : y ≤ Y)
    {a : ℝ} (ha : 0 < a) (hay : a * Real.log y ≤ 1) :
    (∏ p ∈ (Y + 1).primesBelow \ (y + 1).primesBelow,
      (1 + harperRankinEulerRadius p a ^ 2)) ≤
        (1 + 1 / a) / (candidateRankinNormalizerConstant * Real.log y) := by
  have hsub : (y + 1).primesBelow ⊆ (Y + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hden : 0 < candidateRankinNormalizerConstant * Real.log y :=
    mul_pos candidateRankinNormalizerConstant_pos hlog
  let R : ℝ := ∏ p ∈ (Y + 1).primesBelow \ (y + 1).primesBelow,
    (1 + harperRankinEulerRadius p a ^ 2)
  have hR : 0 ≤ R := Finset.prod_nonneg fun p hp => by positivity
  have hfactor : R * harperRankinPrimeEnergyNormalizer y a =
      harperRankinPrimeEnergyNormalizer Y a := by
    exact Finset.prod_sdiff hsub
  rw [le_div_iff₀ hden]
  calc
    R * (candidateRankinNormalizerConstant * Real.log y) ≤
        R * harperRankinPrimeEnergyNormalizer y a :=
      mul_le_mul_of_nonneg_left
        (candidate_rankinNormalizer_lower_small_shift hy ha.le hay) hR
    _ = harperRankinPrimeEnergyNormalizer Y a := hfactor
    _ ≤ _ := candidate_rankinNormalizer_upper Y ha

end Erdos.Problem1144
