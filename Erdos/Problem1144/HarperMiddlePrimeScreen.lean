import Erdos.Problem1144.AbsoluteTail
import Erdos.Problem1144.HarperTrackBLinearPrimeScreen

open scoped BigOperators

namespace Erdos
namespace Problem1144

/-!
# Finite middle-prime screen averaging

The coefficient-localization theorem makes the middle-prime coordinates a
finite post-selection cube.  This file records the deterministic convexity
fact needed to use that cube: averaging the maximum over a finite cloud is at
least the maximum of the coordinatewise averages.

It also supplies exact coordinate-overwrite and cancellation lemmas for the
squarefree-supported model.  These distinguish the valid squarefree screen
average from the false analogous claim for the complete model, where even
prime powers survive averaging.
-/

/-- A complete assignment of the coordinates in a finite screen. -/
abbrev MiddleScreenWorld (s : Finset ℕ) := (q : {q // q ∈ s}) → Bool

/-- Replace exactly the coordinates in `s` by a prescribed finite-screen
assignment, leaving the outside world fixed. -/
def middleScreenOverwrite
    (s : Finset ℕ) (eta : MiddleScreenWorld s) (omega : Omega) : Omega :=
  fun p ↦ if hp : p ∈ s then eta ⟨p, hp⟩ else omega p

/-- Flip one coordinate of a finite-screen assignment. -/
def middleScreenWorldFlip
    {s : Finset ℕ} (q : {q // q ∈ s}) (eta : MiddleScreenWorld s) :
    MiddleScreenWorld s :=
  Function.update eta q (!eta q)

@[simp] theorem middleScreenWorldFlip_apply_self
    {s : Finset ℕ} (q : {q // q ∈ s}) (eta : MiddleScreenWorld s) :
    middleScreenWorldFlip q eta q = !eta q := by
  simp [middleScreenWorldFlip]

theorem middleScreenWorldFlip_involutive
    {s : Finset ℕ} (q : {q // q ∈ s}) :
    Function.Involutive (middleScreenWorldFlip q) := by
  intro eta
  funext r
  by_cases hrq : r = q
  · subst r
    simp [middleScreenWorldFlip]
  · simp [middleScreenWorldFlip, hrq]

/-- Flipping an assignment coordinate and then overwriting is the same as
overwriting first and flipping that coordinate in the ambient sign world. -/
theorem middleScreenOverwrite_worldFlip
    (s : Finset ℕ) (q : {q // q ∈ s})
    (eta : MiddleScreenWorld s) (omega : Omega) :
    middleScreenOverwrite s (middleScreenWorldFlip q eta) omega =
      freshSignFlip {q.1} (middleScreenOverwrite s eta omega) := by
  funext p
  by_cases hpq : p = q.1
  · subst p
    simp [middleScreenOverwrite, middleScreenWorldFlip, freshSignFlip,
      q.property]
  · by_cases hps : p ∈ s
    · have hsub : (⟨p, hps⟩ : {q // q ∈ s}) ≠ q := by
        intro h
        exact hpq (congrArg Subtype.val h)
      simp [middleScreenOverwrite, middleScreenWorldFlip, freshSignFlip,
        hps, hpq, hsub]
    · simp [middleScreenOverwrite, freshSignFlip, hps, hpq]

/-- Flipping one screen coordinate is a permutation of the finite cube. -/
def middleScreenWorldFlipEquiv
    {s : Finset ℕ} (q : {q // q ∈ s}) :
    MiddleScreenWorld s ≃ MiddleScreenWorld s where
  toFun := middleScreenWorldFlip q
  invFun := middleScreenWorldFlip q
  left_inv := middleScreenWorldFlip_involutive q
  right_inv := middleScreenWorldFlip_involutive q

/-- A squarefree-supported monomial whose kernel meets the screen has exact
zero sum over the finite screen fiber. -/
theorem sum_middleScreenWorld_gSquarefree_eq_zero_of_not_disjoint
    (s : Finset ℕ) (omega : Omega) {n : ℕ}
    (hn : Squarefree n) (hmeet : ¬ Disjoint s (sfKernel n)) :
    (∑ eta : MiddleScreenWorld s,
      gSquarefree (middleScreenOverwrite s eta omega) n) = 0 := by
  classical
  obtain ⟨q, hqs, hqker⟩ := Finset.not_disjoint_iff.mp hmeet
  let qsub : {q // q ∈ s} := ⟨q, hqs⟩
  let F : MiddleScreenWorld s → ℝ := fun eta ↦
    gSquarefree (middleScreenOverwrite s eta omega) n
  have hneg (eta : MiddleScreenWorld s) :
      F (middleScreenWorldFlip qsub eta) = -F eta := by
    simp only [F, gSquarefree_of_squarefree _ hn]
    rw [middleScreenOverwrite_worldFlip,
      f_freshSignFlip_singleton q (middleScreenOverwrite s eta omega) n,
      if_pos hqker]
  have hperm := (middleScreenWorldFlipEquiv qsub).sum_comp F
  have hsumNeg :
      (∑ eta : MiddleScreenWorld s,
          F ((middleScreenWorldFlipEquiv qsub) eta)) =
        -(∑ eta : MiddleScreenWorld s, F eta) := by
    calc
      (∑ eta : MiddleScreenWorld s,
          F ((middleScreenWorldFlipEquiv qsub) eta)) =
          ∑ eta : MiddleScreenWorld s, -F eta := by
            apply Finset.sum_congr rfl
            intro eta _heta
            exact hneg eta
      _ = -(∑ eta : MiddleScreenWorld s, F eta) :=
        by simp only [Finset.sum_neg_distrib]
  rw [hsumNeg] at hperm
  have : (∑ eta : MiddleScreenWorld s, F eta) = 0 := by linarith
  exact this

/-- If the kernel misses the screen, overwriting the screen leaves the
squarefree-supported monomial unchanged. -/
theorem gSquarefree_middleScreenOverwrite_eq_of_disjoint
    (s : Finset ℕ) (eta : MiddleScreenWorld s) (omega : Omega) {n : ℕ}
    (hdisj : Disjoint s (sfKernel n)) :
    gSquarefree (middleScreenOverwrite s eta omega) n =
      gSquarefree omega n := by
  classical
  by_cases hn : Squarefree n
  · simp only [gSquarefree_of_squarefree _ hn]
    unfold f
    apply Finset.prod_congr rfl
    intro q hq
    have hqNot : q ∉ s := by
      intro hqs
      exact (Finset.disjoint_left.mp hdisj hqs) hq
    simp [eps, middleScreenOverwrite, hqNot]
  · simp [gSquarefree_of_not_squarefree _ hn]

/-- Exact finite-fiber average of one squarefree-supported monomial. -/
theorem sum_middleScreenWorld_gSquarefree
    (s : Finset ℕ) (omega : Omega) (n : ℕ) :
    (∑ eta : MiddleScreenWorld s,
      gSquarefree (middleScreenOverwrite s eta omega) n) =
      if Disjoint s (sfKernel n) then
        (2 ^ s.card : ℕ) * gSquarefree omega n
      else 0 := by
  classical
  by_cases hdisj : Disjoint s (sfKernel n)
  · rw [if_pos hdisj]
    simp_rw [gSquarefree_middleScreenOverwrite_eq_of_disjoint
      s _ omega hdisj]
    simp
  · rw [if_neg hdisj]
    by_cases hn : Squarefree n
    · exact sum_middleScreenWorld_gSquarefree_eq_zero_of_not_disjoint
        s omega hn hdisj
    · simp [gSquarefree_of_not_squarefree _ hn]

/-- Prime coordinates in the arithmetic middle interval `(Y, X]`. -/
noncomputable def middlePrimeCoordinates (Y X : ℕ) : Finset ℕ :=
  (Finset.Ioc Y X).filter Nat.Prime

theorem mem_middlePrimeCoordinates {Y X p : ℕ} :
    p ∈ middlePrimeCoordinates Y X ↔ Y < p ∧ p ≤ X ∧ Nat.Prime p := by
  simp [middlePrimeCoordinates, and_assoc]

/-- The `X`-smooth part of the squarefree critical sum. -/
noncomputable def squarefreeSmoothCriticalSum
    (omega : Omega) (X N : ℕ) : ℝ := by
  classical
  exact
    ∑ n ∈ Finset.Icc 1 N,
      if IsXSmooth X n then
        gSquarefree omega n / Real.sqrt (n : ℝ)
      else 0

/-- On a squarefree `X`-smooth integer, missing every middle coordinate is
equivalent to already being `Y`-smooth. -/
theorem disjoint_middlePrimeCoordinates_sfKernel_iff
    {Y X n : ℕ} (hn : Squarefree n) (hX : IsXSmooth X n) :
    Disjoint (middlePrimeCoordinates Y X) (sfKernel n) ↔
      IsXSmooth Y n := by
  constructor
  · intro hdisj p hpFactors
    have hpPrime : Nat.Prime p := Nat.prime_of_mem_primeFactors hpFactors
    have hpX : p ≤ X := hX p hpFactors
    by_contra hpY
    have hYp : Y < p := lt_of_not_ge hpY
    have hpMiddle : p ∈ middlePrimeCoordinates Y X :=
      mem_middlePrimeCoordinates.mpr ⟨hYp, hpX, hpPrime⟩
    have hpKernel : p ∈ sfKernel n :=
      (mem_sfKernel_iff_dvd_of_squarefree hn hpPrime).mpr
        (Nat.dvd_of_mem_primeFactors hpFactors)
    exact (Finset.disjoint_left.mp hdisj hpMiddle) hpKernel
  · intro hY
    rw [Finset.disjoint_left]
    intro p hpMiddle hpKernel
    have hpFactors : p ∈ n.primeFactors :=
      sfKernel_subset_primeFactors n hpKernel
    have hpLeY : p ≤ Y := hY p hpFactors
    exact (not_lt_of_ge hpLeY) (mem_middlePrimeCoordinates.mp hpMiddle).1

/-- A prime divisor larger than the square-root range occurs to the first
power and hence belongs to the odd-exponent kernel. -/
theorem mem_sfKernel_of_prime_dvd_of_lt_sq
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hpn : p ∣ n)
    (hnlt : n < p ^ 2) :
    p ∈ sfKernel n := by
  have hfacPos : 0 < n.factorization p :=
    hp.factorization_pos_of_dvd hn.ne' hpn
  have hfacLe : n.factorization p ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ n.factorization p := by omega
    have hpSqDvd : p ^ 2 ∣ n :=
      (hp.pow_dvd_iff_le_factorization hn.ne').2 htwo
    have hpSqLe : p ^ 2 ≤ n := Nat.le_of_dvd hn hpSqDvd
    omega
  have hfac : n.factorization p = 1 := by omega
  rw [mem_sfKernel_iff_odd_factorization, hfac]
  simp

/-- For complete multiplicativity the squarefree screen criterion becomes
exact again below `Y^2`: no prime in `(Y,X]` can occur with a surviving even
positive exponent. -/
theorem disjoint_middlePrimeCoordinates_sfKernel_iff_of_lt_square
    {Y X N n : ℕ} (hN : N < Y ^ 2)
    (hnIcc : n ∈ Finset.Icc 1 N) (hnX : IsXSmooth X n) :
    Disjoint (middlePrimeCoordinates Y X) (sfKernel n) ↔
      IsXSmooth Y n := by
  constructor
  · intro hdisj p hpFactors
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hpFactors
    have hpX : p ≤ X := hnX p hpFactors
    by_contra hpY
    have hYp : Y < p := lt_of_not_ge hpY
    have hpMiddle : p ∈ middlePrimeCoordinates Y X :=
      mem_middlePrimeCoordinates.mpr ⟨hYp, hpX, hpPrime⟩
    have hnPos : 0 < n :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hnIcc).1
    have hnLe : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
    have hYSqPSq : Y ^ 2 < p ^ 2 :=
      Nat.pow_lt_pow_left hYp (by norm_num)
    have hnPSq : n < p ^ 2 := hnLe.trans_lt (hN.trans hYSqPSq)
    have hpKernel : p ∈ sfKernel n :=
      mem_sfKernel_of_prime_dvd_of_lt_sq hpPrime hnPos
        (Nat.dvd_of_mem_primeFactors hpFactors) hnPSq
    exact (Finset.disjoint_left.mp hdisj hpMiddle) hpKernel
  · intro hnY
    exact disjoint_sfKernel_of_isXSmooth_of_above hnY
      (middlePrimeCoordinates Y X) fun q hq ↦
        (mem_middlePrimeCoordinates.mp hq).1

/-- Below `L^2`, every squarefree `X`-smooth but non-`L`-smooth monomial
contains exactly one prime from `(L, X]`; flipping the whole band therefore
negates that monomial. -/
theorem f_freshSignFlip_middlePrimeCoordinates_eq_neg
    (omega : Omega) {L X N n : ℕ} (hN : N < L ^ 2)
    (hnIcc : n ∈ Finset.Icc 1 N) (hnSq : Squarefree n)
    (hnX : IsXSmooth X n) (hnL : ¬ IsXSmooth L n) :
    f (freshSignFlip (middlePrimeCoordinates L X) omega) n =
      -f omega n := by
  classical
  have hn0 : n ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hnIcc).1)
  obtain ⟨p, hpPrime, hLp, hpn⟩ :=
    (not_isXSmooth_iff_exists_large_prime_of_ne_zero L n hn0).mp hnL
  have hpFactors : p ∈ n.primeFactors := hpPrime.mem_primeFactors hpn hn0
  have hpX : p ≤ X := hnX p hpFactors
  have hpMiddle : p ∈ middlePrimeCoordinates L X :=
    mem_middlePrimeCoordinates.mpr ⟨hLp, hpX, hpPrime⟩
  have hpKernel : p ∈ sfKernel n :=
    (mem_sfKernel_iff_dvd_of_squarefree hnSq hpPrime).mpr hpn
  unfold f
  rw [← Finset.mul_prod_erase (sfKernel n)
      (fun q ↦ eps (freshSignFlip (middlePrimeCoordinates L X) omega) q)
      hpKernel,
    eps_freshSignFlip_of_mem _ omega hpMiddle]
  have hrest :
      ∏ q ∈ (sfKernel n).erase p,
          eps (freshSignFlip (middlePrimeCoordinates L X) omega) q =
        ∏ q ∈ (sfKernel n).erase p, eps omega q := by
    apply Finset.prod_congr rfl
    intro q hq
    have hqNe : q ≠ p := Finset.ne_of_mem_erase hq
    have hqNot : q ∉ middlePrimeCoordinates L X := by
      intro hqMiddle
      have hqData := mem_middlePrimeCoordinates.mp hqMiddle
      have hqKernel : q ∈ sfKernel n := Finset.mem_of_mem_erase hq
      have hqDvd : q ∣ n :=
        (mem_sfKernel_iff_dvd_of_squarefree hnSq hqData.2.2).mp hqKernel
      have hpq : p = q :=
        large_prime_unique_of_lt_square hN hnIcc hpPrime hLp hpn
          hqData.2.2 hqData.1 hqDvd
      exact hqNe hpq.symm
    exact eps_freshSignFlip_of_notMem _ omega hqNot
  rw [hrest, ← Finset.mul_prod_erase (sfKernel n) (eps omega) hpKernel]
  ring

/-- The genuinely linear top-prime band, represented as the difference
between the `X`-smooth and `L`-smooth squarefree critical sums. -/
noncomputable def squarefreeCriticalPrimeBand
    (omega : Omega) (L X N : ℕ) : ℝ :=
  squarefreeSmoothCriticalSum omega X N -
    squarefreeSmoothCriticalSum omega L N

/-- The exact arithmetic support of the squarefree critical top-prime band. -/
noncomputable def squarefreeCriticalPrimeBandSet
    (L X N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    Squarefree n ∧ IsXSmooth X n ∧ ¬ IsXSmooth L n

/-- Below `L^2`, the product support generated by the fresh coordinates
`p ∈ (L, X]` is literally the squarefree `X`-smooth, non-`L`-smooth band.

This is the exact arithmetic identification behind the screen split: after
writing `n = p*m`, the quotient `m` is automatically below `L`, so the
coefficient of `eps_p` depends only on coordinates below `L`. -/
theorem trackBSquarefreeFreshProductSet_middlePrimeCoordinates
    {L X N : ℕ} (hN : N < L ^ 2) :
    trackBSquarefreeFreshProductSet (middlePrimeCoordinates L X) N =
      squarefreeCriticalPrimeBandSet L X N := by
  classical
  ext n
  constructor
  · intro hn
    rcases mem_trackBSquarefreeFreshProductSet.mp hn with ⟨a, ha, rfl⟩
    rcases a with ⟨p, m⟩
    rcases mem_trackBSquarefreeFreshPairs.mp ha with ⟨hpFresh, hm⟩
    have hpData := mem_middlePrimeCoordinates.mp hpFresh
    have hpPrime : Nat.Prime p := hpData.2.2
    have hmData := mem_trackBSquarefreeFreshCoeffSupport.mp hm
    have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hmData.1
    have hpmPos : 0 < p * m := Nat.mul_pos hpPrime.pos hmPos
    have hpmIcc : p * m ∈ Finset.Icc 1 N :=
      Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hpmPos, hmData.2.2.2.2.2⟩
    have hpmSq : Squarefree (p * m) :=
      trackBSquarefreeFreshProductSet_squarefree
        (fun q hq => (mem_middlePrimeCoordinates.mp hq).2.2) hn
    have hmSmooth : IsXSmooth L m :=
      isXSmooth_of_le_div_large hN hpData.1 hmData.2.1
    have hpmSmooth : IsXSmooth X (p * m) := by
      intro q hqFactors
      have hqPrime : Nat.Prime q := Nat.prime_of_mem_primeFactors hqFactors
      have hqDvd : q ∣ p * m := Nat.dvd_of_mem_primeFactors hqFactors
      rcases hqPrime.dvd_mul.mp hqDvd with hqp | hqm
      · have hqpEq : q = p :=
          ((hpPrime.dvd_iff_eq hqPrime.ne_one).mp hqp).symm
        simpa [hqpEq] using hpData.2.1
      · have hmNe : m ≠ 0 := hmPos.ne'
        have hqmFactors : q ∈ m.primeFactors :=
          hqPrime.mem_primeFactors hqm hmNe
        exact (hmSmooth q hqmFactors).trans
          (hpData.1.le.trans hpData.2.1)
    have hpmNotSmooth : ¬ IsXSmooth L (p * m) := by
      rw [not_isXSmooth_iff_exists_large_prime_of_ne_zero L (p * m)
        hpmPos.ne']
      exact ⟨p, hpPrime, hpData.1, dvd_mul_right p m⟩
    exact Finset.mem_filter.mpr
      ⟨hpmIcc, hpmSq, hpmSmooth, hpmNotSmooth⟩
  · intro hn
    rcases Finset.mem_filter.mp hn with
      ⟨hnIcc, hnSq, hnSmooth, hnNotSmooth⟩
    have hnPos : 0 < n :=
      lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hnIcc).1
    obtain ⟨p, hpPrime, hLp, hpn⟩ :=
      (not_isXSmooth_iff_exists_large_prime_of_ne_zero L n hnPos.ne').mp
        hnNotSmooth
    have hpFactors : p ∈ n.primeFactors :=
      hpPrime.mem_primeFactors hpn hnPos.ne'
    have hpX : p ≤ X := hnSmooth p hpFactors
    let m : ℕ := n / p
    have hpFresh : p ∈ middlePrimeCoordinates L X :=
      mem_middlePrimeCoordinates.mpr ⟨hLp, hpX, hpPrime⟩
    have hpLeN : p ≤ n := Nat.le_of_dvd hnPos hpn
    have hmPos : 0 < m := Nat.div_pos hpLeN hpPrime.pos
    have hmLe : m ≤ N / p :=
      Nat.div_le_div_right (Finset.mem_Icc.mp hnIcc).2
    have hmDvd : m ∣ n := Nat.div_dvd_of_dvd hpn
    have hmSq : Squarefree m := hnSq.squarefree_of_dvd hmDvd
    have hpmEq : p * m = n := by
      dsimp [m]
      exact Nat.mul_div_cancel' hpn
    have hpNotDvdM : ¬ p ∣ m := by
      intro hpDvdM
      have hppDvd : p * p ∣ n := by
        rw [← hpmEq]
        exact Nat.mul_dvd_mul_left p hpDvdM
      exact (Nat.squarefree_iff_prime_squarefree.mp hnSq p hpPrime) hppDvd
    have hmNoFresh :
        trackBNoFreshFactor (middlePrimeCoordinates L X) m := by
      rw [trackBNoFreshFactor, Finset.disjoint_left]
      intro q hqKernel hqFresh
      have hqFactors : q ∈ m.primeFactors :=
        sfKernel_subset_primeFactors m hqKernel
      have hqLeM : q ≤ m := Nat.le_of_mem_primeFactors hqFactors
      have hmLtL : m < L := quotient_lt_X_of_le_div_large hN hLp hmLe
      exact (not_lt_of_ge hqLeM)
        (hmLtL.trans (mem_middlePrimeCoordinates.mp hqFresh).1)
    have hpmLe : p * m ≤ N := by
      simpa [hpmEq] using (Finset.mem_Icc.mp hnIcc).2
    have hmSupport :
        m ∈ trackBSquarefreeFreshCoeffSupport
          (middlePrimeCoordinates L X) N p :=
      mem_trackBSquarefreeFreshCoeffSupport.mpr
        ⟨Nat.succ_le_of_lt hmPos, hmLe, hmSq, hpNotDvdM,
          hmNoFresh, hpmLe⟩
    rw [mem_trackBSquarefreeFreshProductSet]
    exact ⟨⟨p, m⟩,
      mem_trackBSquarefreeFreshPairs.mpr ⟨hpFresh, hmSupport⟩, hpmEq⟩

/-- Weighted-sum form of the top-prime band. -/
theorem squarefreeCriticalPrimeBand_eq_squarefreeWeightedSum
    (omega : Omega) {L X N : ℕ} (hLX : L ≤ X) :
    squarefreeCriticalPrimeBand omega L X N =
      squarefreeWeightedSum (squarefreeCriticalPrimeBandSet L X N)
        (fun n => (Real.sqrt (n : ℝ))⁻¹) omega := by
  classical
  unfold squarefreeCriticalPrimeBand squarefreeSmoothCriticalSum
    squarefreeWeightedSum squarefreeCriticalPrimeBandSet
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hnIcc
  by_cases hnSq : Squarefree n
  · by_cases hnX : IsXSmooth X n
    · by_cases hnL : IsXSmooth L n
      · simp [hnSq, hnX, hnL, div_eq_mul_inv]
      · simp [hnSq, hnX, hnL, div_eq_mul_inv, mul_comm]
    · have hnL : ¬ IsXSmooth L n := by
        intro h
        exact hnX (fun p hp => (h p hp).trans hLX)
      simp [hnSq, hnX, hnL]
  · simp [hnSq, gSquarefree_of_not_squarefree]

/-- Exact identification of the top-prime screen with the concrete raw
fresh-prime linear core already used by the active Track B certificate. -/
theorem squarefreeCriticalPrimeBand_eq_trackBLinearPrimeCoreRaw
    (omega : Omega) {L X N : ℕ} (hLX : L ≤ X) (hN : N < L ^ 2) :
    squarefreeCriticalPrimeBand omega L X N =
      trackBLinearPrimeCoreRaw
        (fun _j _N => middlePrimeCoordinates L X)
        (trackBSquarefreeFreshLinearCoeff
          (fun _j _N => middlePrimeCoordinates L X)) omega 0 N := by
  rw [trackBLinearPrimeCoreRaw_sqfreeFreshCoeff_eq_squarefreeWeightedSum]
  · rw [trackBSquarefreeFreshProductSet_middlePrimeCoordinates hN]
    exact squarefreeCriticalPrimeBand_eq_squarefreeWeightedSum omega hLX
  · intro p hp
    exact (mem_middlePrimeCoordinates.mp hp).2.2

/-- The finite-orbit conditional Rademacher bound specialized to the literal
top-prime band.  A positive-probability lower bound for its conditional
variance event yields a large-band event with only the universal factor
`1/12`; no old-world negative-tail estimate appears. -/
theorem measureReal_squarefreeCriticalPrimeBand_large_lower_of_varianceThreshold
    {L X N : ℕ} (hLX : L ≤ X) (hN : N < L ^ 2)
    (U delta : ℝ)
    (hdelta : delta ≤
      mu.real
        (trackBSquarefreeFreshVarianceThresholdEvent
          (middlePrimeCoordinates L X) N U)) :
    delta / 12 ≤
      mu.real {omega | U ≤ |squarefreeCriticalPrimeBand omega L X N|} := by
  have hcore :=
    measureReal_trackBSquarefreeFreshCoreLarge_lower_of_varianceThreshold
      (middlePrimeCoordinates L X) N U delta hdelta
  have hevent :
      trackBSquarefreeFreshCoreLargeEvent
          (middlePrimeCoordinates L X) N U =
        {omega | U ≤ |squarefreeCriticalPrimeBand omega L X N|} := by
    ext omega
    simp only [trackBSquarefreeFreshCoreLargeEvent, Set.mem_setOf_eq]
    rw [squarefreeCriticalPrimeBand_eq_trackBLinearPrimeCoreRaw omega hLX hN]
  rwa [hevent] at hcore

/-- When `N < L^2`, the whole top-prime band is exactly odd under the global
flip of `(L, X]`.  This is the reflection input suggested by the finite audit. -/
theorem squarefreeCriticalPrimeBand_freshSignFlip_eq_neg
    (omega : Omega) {L X N : ℕ} (hLX : L ≤ X) (hN : N < L ^ 2) :
    squarefreeCriticalPrimeBand
        (freshSignFlip (middlePrimeCoordinates L X) omega) L X N =
      -squarefreeCriticalPrimeBand omega L X N := by
  classical
  unfold squarefreeCriticalPrimeBand squarefreeSmoothCriticalSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hnIcc
  by_cases hnL : IsXSmooth L n
  · have hnX : IsXSmooth X n := by
      intro p hp
      exact (hnL p hp).trans hLX
    simp [hnL, hnX]
  · by_cases hnX : IsXSmooth X n
    · simp only [hnL, hnX, if_false, if_true, sub_zero]
      by_cases hnSq : Squarefree n
      · rw [gSquarefree_of_squarefree _ hnSq,
          gSquarefree_of_squarefree _ hnSq,
          f_freshSignFlip_middlePrimeCoordinates_eq_neg
            omega hN hnIcc hnSq hnX hnL]
        ring
      · simp [gSquarefree_of_not_squarefree _ hnSq]
    · simp [hnL, hnX]

/-- The lower `L`-smooth background is fixed by flipping the disjoint top
prime band `(L, X]`. -/
theorem squarefreeSmoothCriticalSum_freshSignFlip_middlePrimeCoordinates
    (omega : Omega) (L X N : ℕ) :
    squarefreeSmoothCriticalSum
        (freshSignFlip (middlePrimeCoordinates L X) omega) L N =
      squarefreeSmoothCriticalSum omega L N := by
  classical
  unfold squarefreeSmoothCriticalSum
  apply Finset.sum_congr rfl
  intro n _hnIcc
  by_cases hnL : IsXSmooth L n
  · simp only [hnL, if_true]
    by_cases hnSq : Squarefree n
    · rw [gSquarefree_of_squarefree _ hnSq,
        gSquarefree_of_squarefree _ hnSq]
      apply congrArg (fun z : ℝ ↦ z / Real.sqrt (n : ℝ))
      apply f_freshSignFlip_eq_of_disjoint_sfKernel
      rw [Finset.disjoint_left]
      intro p hpMiddle hpKernel
      have hpFactors : p ∈ n.primeFactors :=
        sfKernel_subset_primeFactors n hpKernel
      exact (not_lt_of_ge (hnL p hpFactors))
        (mem_middlePrimeCoordinates.mp hpMiddle).1
    · simp [gSquarefree_of_not_squarefree _ hnSq]
  · simp [hnL]

/-- Exact reflection identity for the top-prime screen. -/
theorem measureReal_squarefreeCriticalPrimeBand_reflection
    {L X N : ℕ} (hLX : L ≤ X) (hN : N < L ^ 2) (U : ℝ) :
    mu.real
        (shiftedFreshLargeEvent
          (fun omega ↦ squarefreeSmoothCriticalSum omega L N)
          (fun omega ↦ squarefreeCriticalPrimeBand omega L X N) U) =
      mu.real
        (shiftedFreshReflectedLargeEvent
          (fun omega ↦ squarefreeSmoothCriticalSum omega L N)
          (fun omega ↦ squarefreeCriticalPrimeBand omega L X N) U) := by
  apply measureReal_shiftedFreshLarge_eq_reflected_of_measurePreserving
    (fun omega ↦ squarefreeSmoothCriticalSum omega L N)
    (fun omega ↦ squarefreeCriticalPrimeBand omega L X N)
    U (freshSignFlip (middlePrimeCoordinates L X))
    (measurePreserving_freshSignFlip (middlePrimeCoordinates L X))
  · intro omega
    exact squarefreeSmoothCriticalSum_freshSignFlip_middlePrimeCoordinates
      omega L X N
  · intro omega
    exact squarefreeCriticalPrimeBand_freshSignFlip_eq_neg omega hLX hN

/-- A large genuinely linear top-prime band cannot be hidden by an arbitrary
`L`-smooth background: it yields a large full squarefree smooth sum with only
the universal reflection loss `1/2`, and no negative-tail estimate. -/
theorem measureReal_squarefreeSmoothCriticalSum_large_lower_of_primeBand
    {L X N : ℕ} (hLX : L ≤ X) (hN : N < L ^ 2) (U p : ℝ)
    (hband : p ≤ mu.real
      {omega | U ≤ |squarefreeCriticalPrimeBand omega L X N|}) :
    p / 2 ≤ mu.real
      {omega | U ≤ |squarefreeSmoothCriticalSum omega X N|} := by
  let A : Omega → ℝ := fun omega ↦ squarefreeSmoothCriticalSum omega L N
  let Z : Omega → ℝ := fun omega ↦ squarefreeCriticalPrimeBand omega L X N
  have hreflect :
      mu.real (shiftedFreshLargeEvent A Z U) =
        mu.real (shiftedFreshReflectedLargeEvent A Z U) := by
    simpa only [A, Z] using
      measureReal_squarefreeCriticalPrimeBand_reflection hLX hN U
  have hlower := measureReal_shiftedFreshLarge_lower_of_freshLarge
    A Z U p hreflect (by simpa [freshLargeEvent, Z] using hband)
  simpa [shiftedFreshLargeEvent, A, Z, squarefreeCriticalPrimeBand,
    sub_eq_add_neg, add_sub_cancel_left] using hlower

/-- Exact post-selection screen average for the squarefree old contribution:
averaging `(Y, X]` deletes precisely the non-`Y`-smooth squarefree terms. -/
theorem sum_middleScreenWorld_squarefreeSmoothCriticalSum
    (omega : Omega) {Y X N : ℕ} (hYX : Y ≤ X) :
    (∑ eta : MiddleScreenWorld (middlePrimeCoordinates Y X),
      squarefreeSmoothCriticalSum
        (middleScreenOverwrite (middlePrimeCoordinates Y X) eta omega) X N) =
      (2 ^ (middlePrimeCoordinates Y X).card : ℕ) *
        squarefreeSmoothCriticalSum omega Y N := by
  classical
  let s := middlePrimeCoordinates Y X
  let scale : ℝ := (2 ^ s.card : ℕ)
  unfold squarefreeSmoothCriticalSum
  calc
    (∑ eta : MiddleScreenWorld s,
        ∑ n ∈ Finset.Icc 1 N,
          if IsXSmooth X n then
            gSquarefree (middleScreenOverwrite s eta omega) n /
              Real.sqrt (n : ℝ)
          else 0) =
        ∑ n ∈ Finset.Icc 1 N,
          ∑ eta : MiddleScreenWorld s,
            if IsXSmooth X n then
              gSquarefree (middleScreenOverwrite s eta omega) n /
                Real.sqrt (n : ℝ)
            else 0 := by
              rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.Icc 1 N,
          scale *
            (if IsXSmooth Y n then
              gSquarefree omega n / Real.sqrt (n : ℝ)
            else 0) := by
      apply Finset.sum_congr rfl
      intro n _hnIcc
      by_cases hnX : IsXSmooth X n
      · simp only [hnX, if_true]
        rw [← Finset.sum_div,
          sum_middleScreenWorld_gSquarefree]
        by_cases hnsq : Squarefree n
        · have hiff : Disjoint s (sfKernel n) ↔ IsXSmooth Y n := by
            simpa only [s] using
              disjoint_middlePrimeCoordinates_sfKernel_iff hnsq hnX
          by_cases hnY : IsXSmooth Y n
          · have hdisj : Disjoint s (sfKernel n) := hiff.mpr hnY
            simp only [hdisj, if_true, hnY, scale]
            ring
          · have hmeet : ¬ Disjoint s (sfKernel n) := by
              exact fun hdisj => hnY (hiff.mp hdisj)
            simp [hmeet, hnY]
        · simp [gSquarefree_of_not_squarefree _ hnsq]
      · have hnY : ¬ IsXSmooth Y n := by
          intro hY
          apply hnX
          intro p hp
          exact (hY p hp).trans hYX
        simp [hnX, hnY]
    _ = (2 ^ s.card : ℕ) *
          ∑ n ∈ Finset.Icc 1 N,
            if IsXSmooth Y n then
              gSquarefree omega n / Real.sqrt (n : ℝ)
            else 0 := by
      rw [Finset.mul_sum]

/-- Finite-cube Jensen for a maximum, in its denominator-free form.  No
probability or measurability infrastructure is needed. -/
theorem sup_sum_le_sum_sup_middleScreen
    {I : Type*} (cloud : Finset I) (hcloud : cloud.Nonempty)
    (s : Finset ℕ) (F : I → MiddleScreenWorld s → ℝ) :
    cloud.sup' hcloud (fun i ↦ ∑ eta, F i eta) ≤
      ∑ eta, cloud.sup' hcloud (fun i ↦ F i eta) := by
  apply Finset.sup'_le hcloud
  intro i hi
  exact Finset.sum_le_sum fun eta _heta ↦ Finset.le_sup' (fun j ↦ F j eta) hi

/-- Screen convexity specialized to the squarefree smooth critical endpoint
cloud.  The average screen maximum dominates the maximum of the exact
`Y`-smooth residual. -/
theorem squarefreeSmoothCriticalSum_sup_le_sum_screenSup
    (cloud : Finset ℕ) (hcloud : cloud.Nonempty)
    (omega : Omega) {Y X : ℕ} (hYX : Y ≤ X) :
    cloud.sup' hcloud (fun N ↦
        (2 ^ (middlePrimeCoordinates Y X).card : ℕ) *
          squarefreeSmoothCriticalSum omega Y N) ≤
      ∑ eta : MiddleScreenWorld (middlePrimeCoordinates Y X),
        cloud.sup' hcloud (fun N ↦
          squarefreeSmoothCriticalSum
            (middleScreenOverwrite (middlePrimeCoordinates Y X) eta omega) X N) := by
  let s := middlePrimeCoordinates Y X
  have hconvex := sup_sum_le_sum_sup_middleScreen cloud hcloud s
    (fun N eta ↦ squarefreeSmoothCriticalSum
      (middleScreenOverwrite s eta omega) X N)
  have hfiber (N : ℕ) :
      (∑ eta : MiddleScreenWorld s,
        squarefreeSmoothCriticalSum (middleScreenOverwrite s eta omega) X N) =
        (2 ^ s.card : ℕ) * squarefreeSmoothCriticalSum omega Y N := by
    simpa only [s] using
      sum_middleScreenWorld_squarefreeSmoothCriticalSum omega hYX
  simpa only [hfiber] using hconvex

/-! ## The exact complete-model middle-screen residual -/

/-- If the odd-exponent kernel misses the screen, overwriting the screen
leaves the complete multiplicative coefficient unchanged.  Unlike the
squarefree-supported statement above, this applies to every positive integer,
including numbers containing prime squares. -/
theorem f_middleScreenOverwrite_eq_of_disjoint
    (s : Finset ℕ) (eta : MiddleScreenWorld s) (omega : Omega) (n : ℕ)
    (hdisj : Disjoint s (sfKernel n)) :
    f (middleScreenOverwrite s eta omega) n = f omega n := by
  classical
  unfold f
  apply Finset.prod_congr rfl
  intro q hq
  have hqNot : q ∉ s := by
    intro hqs
    exact (Finset.disjoint_left.mp hdisj hqs) hq
  simp [eps, middleScreenOverwrite, hqNot]

/-- A complete multiplicative monomial whose odd-exponent kernel meets the
screen has exact zero sum over the finite screen cube. -/
theorem sum_middleScreenWorld_f_eq_zero_of_not_disjoint
    (s : Finset ℕ) (omega : Omega) {n : ℕ}
    (hmeet : ¬ Disjoint s (sfKernel n)) :
    (∑ eta : MiddleScreenWorld s,
      f (middleScreenOverwrite s eta omega) n) = 0 := by
  classical
  obtain ⟨q, hqs, hqker⟩ := Finset.not_disjoint_iff.mp hmeet
  let qsub : {q // q ∈ s} := ⟨q, hqs⟩
  let F : MiddleScreenWorld s → ℝ := fun eta ↦
    f (middleScreenOverwrite s eta omega) n
  have hneg (eta : MiddleScreenWorld s) :
      F (middleScreenWorldFlip qsub eta) = -F eta := by
    unfold F f
    rw [middleScreenOverwrite_worldFlip,
      ← Finset.mul_prod_erase (sfKernel n)
        (fun p ↦ eps (freshSignFlip {q} (middleScreenOverwrite s eta omega)) p)
        hqker,
      eps_freshSignFlip_of_mem {q} (middleScreenOverwrite s eta omega) (by simp)]
    have hrest :
        ∏ p ∈ (sfKernel n).erase q,
            eps (freshSignFlip {q} (middleScreenOverwrite s eta omega)) p =
          ∏ p ∈ (sfKernel n).erase q,
            eps (middleScreenOverwrite s eta omega) p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact eps_freshSignFlip_of_notMem {q}
        (middleScreenOverwrite s eta omega)
        (by simpa using Finset.ne_of_mem_erase hp)
    rw [hrest,
      ← Finset.mul_prod_erase (sfKernel n)
        (fun p ↦ eps (middleScreenOverwrite s eta omega) p) hqker]
    ring
  have hperm := (middleScreenWorldFlipEquiv qsub).sum_comp F
  have hsumNeg :
      (∑ eta : MiddleScreenWorld s,
          F ((middleScreenWorldFlipEquiv qsub) eta)) =
        -(∑ eta : MiddleScreenWorld s, F eta) := by
    calc
      (∑ eta : MiddleScreenWorld s,
          F ((middleScreenWorldFlipEquiv qsub) eta)) =
          ∑ eta : MiddleScreenWorld s, -F eta := by
            apply Finset.sum_congr rfl
            intro eta _heta
            exact hneg eta
      _ = -(∑ eta : MiddleScreenWorld s, F eta) := by
        simp only [Finset.sum_neg_distrib]
  rw [hsumNeg] at hperm
  change (∑ eta : MiddleScreenWorld s,
    f (middleScreenOverwrite s eta omega) n) = 0
  change (∑ eta : MiddleScreenWorld s, F eta) = 0
  linarith

/-- Exact finite-fiber average of one complete multiplicative coefficient.
Only the parity kernel matters: even powers of screen primes survive, while
every monomial with an odd screen exponent cancels. -/
theorem sum_middleScreenWorld_f
    (s : Finset ℕ) (omega : Omega) (n : ℕ) :
    (∑ eta : MiddleScreenWorld s,
      f (middleScreenOverwrite s eta omega) n) =
      if Disjoint s (sfKernel n) then
        (2 ^ s.card : ℕ) * f omega n
      else 0 := by
  classical
  by_cases hdisj : Disjoint s (sfKernel n)
  · rw [if_pos hdisj]
    simp_rw [f_middleScreenOverwrite_eq_of_disjoint s _ omega n hdisj]
    simp
  · rw [if_neg hdisj]
    exact sum_middleScreenWorld_f_eq_zero_of_not_disjoint s omega hdisj

/-- The exact complete-model residual after averaging the middle prime screen.
It retains the `X`-smooth integers whose odd-exponent kernel avoids `(Y,X]`;
in particular, even powers of middle primes remain. -/
noncomputable def completeMiddleScreenResidualSum
    (omega : Omega) (Y X N : ℕ) : ℝ := by
  classical
  exact
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsXSmooth X n),
      if Disjoint (middlePrimeCoordinates Y X) (sfKernel n) then
        f omega n
      else 0

/-- The complete residual is normalized on the original endpoint scale. -/
noncomputable def completeMiddleScreenResidualProcess
    (omega : Omega) (Y X N : ℕ) : ℝ :=
  completeMiddleScreenResidualSum omega Y X N / Real.sqrt (N : ℝ)

/-- Exact finite-screen average of the complete `X`-smooth old contribution.
This is the correct replacement for the false assertion that averaging leaves
only the `Y`-smooth complete sum. -/
theorem sum_middleScreenWorld_smoothSum
    (omega : Omega) (Y X N : ℕ) :
    (∑ eta : MiddleScreenWorld (middlePrimeCoordinates Y X),
      smoothSum
        (middleScreenOverwrite (middlePrimeCoordinates Y X) eta omega) X N) =
      (2 ^ (middlePrimeCoordinates Y X).card : ℕ) *
        completeMiddleScreenResidualSum omega Y X N := by
  classical
  let s := middlePrimeCoordinates Y X
  unfold smoothSum completeMiddleScreenResidualSum
  calc
    (∑ eta : MiddleScreenWorld s,
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsXSmooth X n),
          f (middleScreenOverwrite s eta omega) n) =
      ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsXSmooth X n),
        ∑ eta : MiddleScreenWorld s,
          f (middleScreenOverwrite s eta omega) n := by
            rw [Finset.sum_comm]
    _ = ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsXSmooth X n),
          (2 ^ s.card : ℕ) *
            (if Disjoint s (sfKernel n) then f omega n else 0) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [sum_middleScreenWorld_f]
      split <;> simp_all
    _ = (2 ^ s.card : ℕ) *
        ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsXSmooth X n),
          if Disjoint s (sfKernel n) then f omega n else 0 := by
      rw [Finset.mul_sum]

/-- In the sub-square range the complete residual simplifies literally to the
smaller smooth sum.  This is the precise range in which finite-screen
averaging has no surviving even-prime-power correction. -/
theorem completeMiddleScreenResidualSum_eq_smoothSum_of_lt_square
    (omega : Omega) {Y X N : ℕ} (hYX : Y ≤ X) (hN : N < Y ^ 2) :
    completeMiddleScreenResidualSum omega Y X N =
      smoothSum omega Y N := by
  classical
  unfold completeMiddleScreenResidualSum smoothSum
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hnIcc
  by_cases hnX : IsXSmooth X n
  · have hiff :=
      disjoint_middlePrimeCoordinates_sfKernel_iff_of_lt_square
        hN hnIcc hnX
    by_cases hnY : IsXSmooth Y n
    · have hdisj := hiff.mpr hnY
      simp [hnX, hnY, hdisj]
    · have hmeet : ¬ Disjoint (middlePrimeCoordinates Y X) (sfKernel n) :=
        fun hdisj ↦ hnY (hiff.mp hdisj)
      simp [hnX, hnY, hmeet]
  · have hnY : ¬ IsXSmooth Y n := by
      intro hY
      apply hnX
      intro p hp
      exact (hY p hp).trans hYX
    simp [hnX, hnY]

/-- Exact complete-model screen average in the sub-square range. -/
theorem sum_middleScreenWorld_smoothSum_eq_smaller_of_lt_square
    (omega : Omega) {Y X N : ℕ} (hYX : Y ≤ X) (hN : N < Y ^ 2) :
    (∑ eta : MiddleScreenWorld (middlePrimeCoordinates Y X),
      smoothSum
        (middleScreenOverwrite (middlePrimeCoordinates Y X) eta omega) X N) =
      (2 ^ (middlePrimeCoordinates Y X).card : ℕ) *
        smoothSum omega Y N := by
  rw [sum_middleScreenWorld_smoothSum,
    completeMiddleScreenResidualSum_eq_smoothSum_of_lt_square omega hYX hN]

/-- Finite-screen Parseval/Jensen in the same sub-square range.  The average
square of the enlarged smooth sum dominates the square of the smaller smooth
sum, so the independent screen can lift energy without any one-sided
lower-tail estimate. -/
theorem card_mul_smoothSum_sq_le_sum_middleScreenWorld_smoothSum_sq
    (omega : Omega) {Y X N : ℕ} (hYX : Y ≤ X) (hN : N < Y ^ 2) :
    ((2 ^ (middlePrimeCoordinates Y X).card : ℕ) : ℝ) *
        smoothSum omega Y N ^ 2 ≤
      ∑ eta : MiddleScreenWorld (middlePrimeCoordinates Y X),
        smoothSum
          (middleScreenOverwrite (middlePrimeCoordinates Y X) eta omega) X N ^ 2 := by
  classical
  let s := middlePrimeCoordinates Y X
  let scale : ℝ := (2 ^ s.card : ℕ)
  let F : MiddleScreenWorld s → ℝ := fun eta ↦
    smoothSum (middleScreenOverwrite s eta omega) X N
  have hsum : (∑ eta : MiddleScreenWorld s, F eta) =
      scale * smoothSum omega Y N := by
    simpa only [s, scale, F] using
      sum_middleScreenWorld_smoothSum_eq_smaller_of_lt_square
        omega hYX hN
  have hcard : (((Finset.univ : Finset (MiddleScreenWorld s)).card : ℕ) : ℝ) =
      scale := by
    simp [scale, s]
  have hcauchyRaw :=
    sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (MiddleScreenWorld s))) (f := F)
  have hcauchy :
      (scale * smoothSum omega Y N) ^ 2 ≤
        scale * ∑ eta : MiddleScreenWorld s, F eta ^ 2 := by
    simpa only [hsum, hcard] using hcauchyRaw
  have hscale : 0 < scale := by dsimp [scale]; positivity
  have hmul :
      scale * (scale * smoothSum omega Y N ^ 2) ≤
        scale * ∑ eta : MiddleScreenWorld s, F eta ^ 2 := by
    calc
      scale * (scale * smoothSum omega Y N ^ 2) =
          (scale * smoothSum omega Y N) ^ 2 := by ring
      _ ≤ scale * ∑ eta : MiddleScreenWorld s, F eta ^ 2 := hcauchy
  have hcancel := le_of_mul_le_mul_left hmul hscale
  simpa only [s, scale, F] using hcancel

/-- Weighted finite-cloud form of the sub-square screen-energy lift.  Any
nonnegative endpoint weights may be used, so a later finite
Harman--Parseval localization can be inserted without revisiting the screen
argument. -/
theorem card_mul_sum_weight_mul_smoothSum_sq_le_sum_middleScreenWorld
    (omega : Omega) {Y X : ℕ} (hYX : Y ≤ X)
    (T : Finset ℕ) (weight : ℕ → ℝ)
    (hweight : ∀ N ∈ T, 0 ≤ weight N)
    (hsubsquare : ∀ N ∈ T, N < Y ^ 2) :
    ((2 ^ (middlePrimeCoordinates Y X).card : ℕ) : ℝ) *
        (∑ N ∈ T, weight N * smoothSum omega Y N ^ 2) ≤
      ∑ eta : MiddleScreenWorld (middlePrimeCoordinates Y X),
        ∑ N ∈ T, weight N *
          smoothSum
            (middleScreenOverwrite
              (middlePrimeCoordinates Y X) eta omega) X N ^ 2 := by
  classical
  let s := middlePrimeCoordinates Y X
  let scale : ℝ := (2 ^ s.card : ℕ)
  let F : MiddleScreenWorld s → ℕ → ℝ := fun eta N ↦
    smoothSum (middleScreenOverwrite s eta omega) X N
  calc
    scale * (∑ N ∈ T, weight N * smoothSum omega Y N ^ 2) =
        ∑ N ∈ T, weight N * (scale * smoothSum omega Y N ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      ring
    _ ≤ ∑ N ∈ T, weight N * ∑ eta : MiddleScreenWorld s, F eta N ^ 2 := by
      apply Finset.sum_le_sum
      intro N hN
      apply mul_le_mul_of_nonneg_left _ (hweight N hN)
      simpa only [s, scale, F] using
        card_mul_smoothSum_sq_le_sum_middleScreenWorld_smoothSum_sq
          omega hYX (hsubsquare N hN)
    _ = ∑ eta : MiddleScreenWorld s,
          ∑ N ∈ T, weight N * F eta N ^ 2 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ eta : MiddleScreenWorld (middlePrimeCoordinates Y X),
          ∑ N ∈ T, weight N *
            smoothSum
              (middleScreenOverwrite
                (middlePrimeCoordinates Y X) eta omega) X N ^ 2 := by
      rfl

/-- A `Y`-smooth complete sum is unchanged by overwriting coordinates
strictly above `Y`. -/
theorem smoothSum_middleScreenOverwrite_eq
    (Y X N : ℕ)
    (eta : MiddleScreenWorld (middlePrimeCoordinates Y X))
    (omega : Omega) :
    smoothSum (middleScreenOverwrite (middlePrimeCoordinates Y X) eta omega) Y N =
      smoothSum omega Y N := by
  classical
  unfold smoothSum
  apply Finset.sum_congr rfl
  intro n hn
  have hnSmooth : IsXSmooth Y n := (Finset.mem_filter.mp hn).2
  apply f_middleScreenOverwrite_eq_of_disjoint
  rw [Finset.disjoint_left]
  intro p hpMiddle hpKernel
  have hpFactors : p ∈ n.primeFactors := sfKernel_subset_primeFactors n hpKernel
  exact (not_lt_of_ge (hnSmooth p hpFactors))
    (mem_middlePrimeCoordinates.mp hpMiddle).1

/-- The complete large-prime process is pointwise fixed by every assignment
of the independent middle screen whenever all of its coefficients live below
`Y`. -/
theorem largePrimeProcess_middleScreenOverwrite_eq
    {Y X N : ℕ}
    (eta : MiddleScreenWorld (middlePrimeCoordinates Y X))
    (omega : Omega) (hN : N < X * Y) :
    largePrimeProcess
        (middleScreenOverwrite (middlePrimeCoordinates Y X) eta omega) X N =
      largePrimeProcess omega X N := by
  classical
  rw [largePrimeProcess_eq_sum_coeff, largePrimeProcess_eq_sum_coeff]
  apply Finset.sum_congr rfl
  intro p hp
  have hpData := mem_largePrimeInterval.mp hp
  have hpNotMiddle : p ∉ middlePrimeCoordinates Y X := by
    intro hpMiddle
    exact (not_lt_of_ge (mem_middlePrimeCoordinates.mp hpMiddle).2.1)
      hpData.2.1
  have hcoeffOverwrite :=
    largePrimeCoeff_eq_smallerSmoothSum
      (middleScreenOverwrite (middlePrimeCoordinates Y X) eta omega) hN hp
  have hcoeff := largePrimeCoeff_eq_smallerSmoothSum omega hN hp
  rw [hcoeffOverwrite, hcoeff,
    smoothSum_middleScreenOverwrite_eq Y X (N / p) eta omega]
  simp [eps, middleScreenOverwrite, hpNotMiddle]

/-- Averaging the complete normalized endpoint over `(Y,X]` leaves exactly
the parity-kernel residual plus the unchanged fresh process above `X`.
This is the rigorous three-way split suggested by the `X^(1/3)` observation.
-/
theorem sum_middleScreenWorld_cutoffNormSum
    (omega : Omega) {Y X N : ℕ} (hYX : Y ≤ X) (hN : N < X * Y) :
    (∑ eta : MiddleScreenWorld (middlePrimeCoordinates Y X),
      cutoffNormSum
        (middleScreenOverwrite (middlePrimeCoordinates Y X) eta omega) N) =
      (2 ^ (middlePrimeCoordinates Y X).card : ℕ) *
        (completeMiddleScreenResidualProcess omega Y X N +
          largePrimeProcess omega X N) := by
  classical
  let s := middlePrimeCoordinates Y X
  have hN2 : N < X ^ 2 := by
    exact lt_of_lt_of_le hN (by
      simpa [pow_two] using Nat.mul_le_mul_left X hYX)
  simp_rw [cutoffNormSum_eq_smoothProcess_add_largePrimeProcess _ hN2]
  rw [Finset.sum_add_distrib]
  have hold :
      (∑ eta : MiddleScreenWorld s,
          smoothProcess (middleScreenOverwrite s eta omega) X N) =
        (2 ^ s.card : ℕ) * completeMiddleScreenResidualProcess omega Y X N := by
    unfold smoothProcess completeMiddleScreenResidualProcess
    rw [← Finset.sum_div]
    rw [show
      (∑ eta : MiddleScreenWorld s,
        smoothSum (middleScreenOverwrite s eta omega) X N) =
          (2 ^ s.card : ℕ) * completeMiddleScreenResidualSum omega Y X N by
      simpa only [s] using sum_middleScreenWorld_smoothSum omega Y X N]
    ring
  have hfresh :
      (∑ eta : MiddleScreenWorld s,
          largePrimeProcess (middleScreenOverwrite s eta omega) X N) =
        (2 ^ s.card : ℕ) * largePrimeProcess omega X N := by
    calc
      (∑ eta : MiddleScreenWorld s,
          largePrimeProcess (middleScreenOverwrite s eta omega) X N) =
          ∑ _eta : MiddleScreenWorld s, largePrimeProcess omega X N := by
            apply Finset.sum_congr rfl
            intro eta _heta
            simpa only [s] using
              largePrimeProcess_middleScreenOverwrite_eq eta omega hN
      _ = (2 ^ s.card : ℕ) * largePrimeProcess omega X N := by simp
  rw [hold, hfresh]
  ring

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.sum_middleScreenWorld_gSquarefree
#print axioms Erdos.Problem1144.trackBSquarefreeFreshProductSet_middlePrimeCoordinates
#print axioms Erdos.Problem1144.squarefreeCriticalPrimeBand_eq_trackBLinearPrimeCoreRaw
#print axioms Erdos.Problem1144.measureReal_squarefreeCriticalPrimeBand_large_lower_of_varianceThreshold
#print axioms Erdos.Problem1144.f_freshSignFlip_middlePrimeCoordinates_eq_neg
#print axioms Erdos.Problem1144.squarefreeCriticalPrimeBand_freshSignFlip_eq_neg
#print axioms Erdos.Problem1144.measureReal_squarefreeCriticalPrimeBand_reflection
#print axioms Erdos.Problem1144.measureReal_squarefreeSmoothCriticalSum_large_lower_of_primeBand
#print axioms Erdos.Problem1144.sum_middleScreenWorld_squarefreeSmoothCriticalSum
#print axioms Erdos.Problem1144.sup_sum_le_sum_sup_middleScreen
#print axioms Erdos.Problem1144.squarefreeSmoothCriticalSum_sup_le_sum_screenSup
#print axioms Erdos.Problem1144.sum_middleScreenWorld_f
#print axioms Erdos.Problem1144.sum_middleScreenWorld_smoothSum
#print axioms Erdos.Problem1144.completeMiddleScreenResidualSum_eq_smoothSum_of_lt_square
#print axioms Erdos.Problem1144.sum_middleScreenWorld_smoothSum_eq_smaller_of_lt_square
#print axioms Erdos.Problem1144.card_mul_smoothSum_sq_le_sum_middleScreenWorld_smoothSum_sq
#print axioms Erdos.Problem1144.card_mul_sum_weight_mul_smoothSum_sq_le_sum_middleScreenWorld
#print axioms Erdos.Problem1144.largePrimeProcess_middleScreenOverwrite_eq
#print axioms Erdos.Problem1144.sum_middleScreenWorld_cutoffNormSum
