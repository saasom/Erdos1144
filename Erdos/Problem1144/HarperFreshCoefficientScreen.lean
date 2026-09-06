import Erdos.Problem1144.HarperProcess
import Erdos.Problem1144.RademacherConcentration

open scoped BigOperators

namespace Erdos
namespace Problem1144

/-!
# An independent middle-prime screen for the Harper fresh walk

If `N < X * Y`, then every coefficient of the fresh-prime process cut at `X`
has quotient cutoff below `Y`.  This file turns that arithmetic observation
into pointwise invariance under flipping any finite set of prime coordinates
in the middle range `(Y, X]`.

The statements are deliberately pointwise.  Together with
`measurePreserving_freshSignFlip`, they are the exact finite-coordinate input
for conditioning or reflection arguments which expose the middle-prime screen
after the fresh coefficient cloud has been selected.
-/

/-- Flipping coordinates disjoint from the squarefree kernel of `n` leaves
`f(n)` unchanged. -/
theorem f_freshSignFlip_eq_of_disjoint_sfKernel
    (s : Finset ℕ) (omega : Omega) (n : ℕ)
    (hdisj : Disjoint s (sfKernel n)) :
    f (freshSignFlip s omega) n = f omega n := by
  classical
  unfold f
  apply Finset.prod_congr rfl
  intro q hq
  apply eps_freshSignFlip_of_notMem
  intro hqs
  exact Finset.disjoint_left.mp hdisj hqs hq

/-- Every coordinate in the squarefree kernel is a prime factor. -/
theorem sfKernel_subset_primeFactors (n : ℕ) :
    sfKernel n ⊆ n.primeFactors := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

/-- A `Y`-smooth integer has squarefree kernel disjoint from coordinates
strictly above `Y`. -/
theorem disjoint_sfKernel_of_isXSmooth_of_above
    {Y n : ℕ} (hn : IsXSmooth Y n) (s : Finset ℕ)
    (hs : ∀ q ∈ s, Y < q) :
    Disjoint s (sfKernel n) := by
  rw [Finset.disjoint_left]
  intro q hqs hqker
  have hqY : q ≤ Y := hn q (sfKernel_subset_primeFactors n hqker)
  exact (not_lt_of_ge hqY) (hs q hqs)

/-- A finite flip supported strictly above `Y` leaves the whole `Y`-smooth
partial sum unchanged. -/
theorem smoothSum_freshSignFlip_eq_of_above
    (s : Finset ℕ) (omega : Omega) (Y N : ℕ)
    (hs : ∀ q ∈ s, Y < q) :
    smoothSum (freshSignFlip s omega) Y N = smoothSum omega Y N := by
  classical
  unfold smoothSum
  apply Finset.sum_congr rfl
  intro n hn
  have hsmooth : IsXSmooth Y n := (Finset.mem_filter.mp hn).2
  exact f_freshSignFlip_eq_of_disjoint_sfKernel s omega n
    (disjoint_sfKernel_of_isXSmooth_of_above hsmooth s hs)

/-- Every fresh coefficient is invariant under a finite screen flip supported
above the smaller coefficient cutoff `Y`. -/
theorem largePrimeCoeff_freshSignFlip_eq_of_above
    (s : Finset ℕ) (omega : Omega) {X Y N p : ℕ}
    (hN : N < X * Y) (hp : p ∈ largePrimeInterval X N)
    (hs : ∀ q ∈ s, Y < q) :
    largePrimeCoeff (freshSignFlip s omega) X N p =
      largePrimeCoeff omega X N p := by
  rw [largePrimeCoeff_eq_smallerSmoothSum
      (freshSignFlip s omega) hN hp,
    largePrimeCoeff_eq_smallerSmoothSum omega hN hp,
    smoothSum_freshSignFlip_eq_of_above s omega Y (N / p) hs]

/-- The complete conditional variance geometry of one fresh walk is invariant
under the independent middle-prime screen. -/
theorem largePrimeVariance_freshSignFlip_eq_of_above
    (s : Finset ℕ) (omega : Omega) {X Y N : ℕ}
    (hN : N < X * Y) (hs : ∀ q ∈ s, Y < q) :
    largePrimeVariance (freshSignFlip s omega) X N =
      largePrimeVariance omega X N := by
  classical
  unfold largePrimeVariance
  apply Finset.sum_congr rfl
  intro p hp
  rw [largePrimeCoeff_freshSignFlip_eq_of_above s omega hN hp hs]

/-- The pairwise covariance geometry of two fresh walks is likewise invariant
under the screen. -/
theorem largePrimeCovariance_freshSignFlip_eq_of_above
    (s : Finset ℕ) (omega : Omega) {X Y M N : ℕ}
    (hM : M < X * Y) (hN : N < X * Y)
    (hs : ∀ q ∈ s, Y < q) :
    largePrimeCovariance (freshSignFlip s omega) X M N =
      largePrimeCovariance omega X M N := by
  classical
  unfold largePrimeCovariance
  apply Finset.sum_congr rfl
  intro p hp
  have hpM : p ∈ largePrimeInterval X M := (Finset.mem_inter.mp hp).1
  have hpN : p ∈ largePrimeInterval X N := (Finset.mem_inter.mp hp).2
  rw [largePrimeCoeff_freshSignFlip_eq_of_above s omega hM hpM hs,
    largePrimeCoeff_freshSignFlip_eq_of_above s omega hN hpN hs]

/-- If the screen also lies at or below `X`, then it leaves the entire fresh
large-prime process unchanged: it changes neither a fresh sign nor any fresh
coefficient. -/
theorem largePrimeProcess_freshSignFlip_eq_of_screen
    (s : Finset ℕ) (omega : Omega) {X Y N : ℕ}
    (hN : N < X * Y)
    (hsLo : ∀ q ∈ s, Y < q) (hsHi : ∀ q ∈ s, q ≤ X) :
    largePrimeProcess (freshSignFlip s omega) X N =
      largePrimeProcess omega X N := by
  classical
  rw [largePrimeProcess_eq_sum_coeff, largePrimeProcess_eq_sum_coeff]
  apply Finset.sum_congr rfl
  intro p hp
  have hXp : X < p :=
    (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp |>.2.1
  have hpNot : p ∉ s := by
    intro hps
    exact (not_lt_of_ge (hsHi p hps)) hXp
  rw [eps_freshSignFlip_of_notMem s omega hpNot,
    largePrimeCoeff_freshSignFlip_eq_of_above s omega hN hp hsLo]

/-! ## The exact `X^(1/3)` split on the power-of-two schedule -/

/-- With outer cutoff `X = 2^(21m)` and endpoints below `2^(28m)`, every
fresh coefficient lives below `2^(7m) = X^(1/3)`.  Hence all coordinates
strictly above `2^(7m)` are invisible to the coefficient. -/
theorem largePrimeCoeff_freshSignFlip_eq_powerTwo_oneThirdScreen
    (s : Finset ℕ) (omega : Omega) {m N p : ℕ}
    (hN : N < 2 ^ (28 * m))
    (hp : p ∈ largePrimeInterval (2 ^ (21 * m)) N)
    (hsLo : ∀ q ∈ s, 2 ^ (7 * m) < q) :
    largePrimeCoeff (freshSignFlip s omega) (2 ^ (21 * m)) N p =
      largePrimeCoeff omega (2 ^ (21 * m)) N p := by
  have hN' : N < 2 ^ (21 * m) * 2 ^ (7 * m) := by
    have hexp : 21 * m + 7 * m = 28 * m := by omega
    simpa only [← pow_add, hexp] using hN
  exact largePrimeCoeff_freshSignFlip_eq_of_above s omega hN' hp hsLo

/-- The conditional variance is measurable with respect to the prime signs
at most `2^(7m)` on the same endpoint window. -/
theorem largePrimeVariance_freshSignFlip_eq_powerTwo_oneThirdScreen
    (s : Finset ℕ) (omega : Omega) {m N : ℕ}
    (hN : N < 2 ^ (28 * m))
    (hsLo : ∀ q ∈ s, 2 ^ (7 * m) < q) :
    largePrimeVariance (freshSignFlip s omega) (2 ^ (21 * m)) N =
      largePrimeVariance omega (2 ^ (21 * m)) N := by
  have hN' : N < 2 ^ (21 * m) * 2 ^ (7 * m) := by
    have hexp : 21 * m + 7 * m = 28 * m := by omega
    simpa only [← pow_add, hexp] using hN
  apply largePrimeVariance_freshSignFlip_eq_of_above s omega
    (X := 2 ^ (21 * m)) (Y := 2 ^ (7 * m))
  · exact hN'
  · exact hsLo

/-- The same `X^(1/3)` independence holds simultaneously for every pair of
fresh coefficient vectors used in covariance pruning. -/
theorem largePrimeCovariance_freshSignFlip_eq_powerTwo_oneThirdScreen
    (s : Finset ℕ) (omega : Omega) {m M N : ℕ}
    (hM : M < 2 ^ (28 * m)) (hN : N < 2 ^ (28 * m))
    (hsLo : ∀ q ∈ s, 2 ^ (7 * m) < q) :
    largePrimeCovariance (freshSignFlip s omega) (2 ^ (21 * m)) M N =
      largePrimeCovariance omega (2 ^ (21 * m)) M N := by
  have hexp : 21 * m + 7 * m = 28 * m := by omega
  have hM' : M < 2 ^ (21 * m) * 2 ^ (7 * m) := by
    simpa only [← pow_add, hexp] using hM
  have hN' : N < 2 ^ (21 * m) * 2 ^ (7 * m) := by
    simpa only [← pow_add, hexp] using hN
  exact largePrimeCovariance_freshSignFlip_eq_of_above
    s omega hM' hN' hsLo

/-- If the flipped coordinates also lie below the outer cutoff, then the
entire fresh process is fixed.  Thus `(2^(7m),2^(21m)]` is a genuine
post-selection screen independent of both coefficients and fresh signs. -/
theorem largePrimeProcess_freshSignFlip_eq_powerTwo_oneThirdScreen
    (s : Finset ℕ) (omega : Omega) {m N : ℕ}
    (hN : N < 2 ^ (28 * m))
    (hsLo : ∀ q ∈ s, 2 ^ (7 * m) < q)
    (hsHi : ∀ q ∈ s, q ≤ 2 ^ (21 * m)) :
    largePrimeProcess (freshSignFlip s omega) (2 ^ (21 * m)) N =
      largePrimeProcess omega (2 ^ (21 * m)) N := by
  have hN' : N < 2 ^ (21 * m) * 2 ^ (7 * m) := by
    have hexp : 21 * m + 7 * m = 28 * m := by omega
    simpa only [← pow_add, hexp] using hN
  apply largePrimeProcess_freshSignFlip_eq_of_screen s omega
    (X := 2 ^ (21 * m)) (Y := 2 ^ (7 * m))
  · exact hN'
  · exact hsLo
  · exact hsHi

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.largePrimeCoeff_freshSignFlip_eq_powerTwo_oneThirdScreen
#print axioms Erdos.Problem1144.largePrimeVariance_freshSignFlip_eq_powerTwo_oneThirdScreen
#print axioms Erdos.Problem1144.largePrimeCovariance_freshSignFlip_eq_powerTwo_oneThirdScreen
#print axioms Erdos.Problem1144.largePrimeProcess_freshSignFlip_eq_powerTwo_oneThirdScreen
