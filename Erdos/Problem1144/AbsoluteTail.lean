import Erdos.Problem1144.EndpointSeparationBridge
import Erdos.Problem1144.Multiplicativity
import Erdos.Problem1144.PositiveProbabilityLimsup

open MeasureTheory Filter
open scoped ENNReal

namespace Erdos
namespace Problem1144

/-!
# Tail infrastructure for the absolute target

The active positive-probability route needs only one model-specific fact:
absolute unboundedness is unchanged after modifying finitely many prime
coordinates.  This file closes the measure-theoretic consequences and leaves
that arithmetic invariance as an explicit pointwise input.
-/

/-- Replace the first `n` Boolean coordinates by `false`. -/
def clearCoordinatePrefix (n : ℕ) (omega : Omega) : Omega :=
  fun i => if i < n then false else omega i

/-- The finite set of `true` coordinates in the first `n` positions.  Flipping
exactly these coordinates clears the prefix. -/
def truePrefixCoordinates (n : ℕ) (omega : Omega) : Finset ℕ :=
  (Finset.range n).filter fun i => omega i

/-- Clearing a coordinate prefix is a finite coordinate flip. -/
theorem freshSignFlip_truePrefixCoordinates
    (n : ℕ) (omega : Omega) :
    freshSignFlip (truePrefixCoordinates n omega) omega =
      clearCoordinatePrefix n omega := by
  funext i
  by_cases hi : i < n
  · cases homega : omega i <;>
      simp [freshSignFlip, truePrefixCoordinates, clearCoordinatePrefix,
        hi, homega]
  · simp [freshSignFlip, truePrefixCoordinates, clearCoordinatePrefix, hi]

/-- A one-coordinate flip changes `f(m)` precisely when that coordinate
belongs to the squarefree kernel of `m`. -/
theorem f_freshSignFlip_singleton (p : ℕ) (omega : Omega) (m : ℕ) :
    f (freshSignFlip {p} omega) m =
      if p ∈ sfKernel m then -f omega m else f omega m := by
  classical
  rw [f, f]
  by_cases hp : p ∈ sfKernel m
  · rw [if_pos hp, ← Finset.mul_prod_erase (sfKernel m)
      (fun q => eps (freshSignFlip {p} omega) q) hp,
      eps_freshSignFlip_of_mem {p} omega (by simp)]
    have hrest :
        ∏ q ∈ (sfKernel m).erase p, eps (freshSignFlip {p} omega) q =
          ∏ q ∈ (sfKernel m).erase p, eps omega q := by
      apply Finset.prod_congr rfl
      intro q hq
      exact eps_freshSignFlip_of_notMem {p} omega
        (by simpa using Finset.ne_of_mem_erase hq)
    rw [hrest, ← Finset.mul_prod_erase (sfKernel m) (eps omega) hp]
    ring
  · rw [if_neg hp]
    apply Finset.prod_congr rfl
    intro q hq
    have hqp : q ≠ p := by
      intro h
      subst q
      exact hp hq
    exact eps_freshSignFlip_of_notMem {p} omega
      (by simpa using hqp)

/-- Reindex a sum supported on multiples of `p` by division by `p`. -/
theorem sum_dvd_div_eq_sum_Icc_div
    (g : ℕ → ℝ) (N p : ℕ) (hp : 0 < p) :
    (∑ n ∈ Finset.Icc 1 N,
      if p ∣ n then g (n / p) else 0) =
        ∑ m ∈ Finset.Icc 1 (N / p), g m := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_bij
    (fun n _hn => n / p)
    (fun n hn => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      rw [Finset.mem_Icc]
      have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn.1.1
      have hp_le_n : p ≤ n := Nat.le_of_dvd hn_pos hn.2
      exact ⟨Nat.succ_le_of_lt (Nat.div_pos hp_le_n hp),
        Nat.div_le_div_right hn.1.2⟩)
    (fun n₁ hn₁ n₂ hn₂ heq => by
      rw [Finset.mem_filter] at hn₁ hn₂
      have hmul₁ : p * (n₁ / p) = n₁ := Nat.mul_div_cancel' hn₁.2
      have hmul₂ : p * (n₂ / p) = n₂ := Nat.mul_div_cancel' hn₂.2
      calc
        n₁ = p * (n₁ / p) := hmul₁.symm
        _ = p * (n₂ / p) := congrArg (p * ·) heq
        _ = n₂ := hmul₂)
    (fun m hm => by
      rw [Finset.mem_Icc] at hm
      let n := p * m
      have hn_le : n ≤ N := by
        dsimp [n]
        simpa [mul_comm] using (Nat.le_div_iff_mul_le hp).mp hm.2
      have hn_pos : 0 < n := mul_pos hp (lt_of_lt_of_le zero_lt_one hm.1)
      refine ⟨n, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨Nat.succ_le_of_lt hn_pos, hn_le⟩, dvd_mul_right p m⟩
      · dsimp [n]
        exact Nat.mul_div_cancel_left m hp)
    (fun _n _hn => rfl)

/-- At a positive integer, the original and one-coordinate-flipped
coefficients satisfy the local Euler-factor recurrence. -/
theorem oneCoordinateFlip_coefficient_recurrence
    (p : ℕ) (hp : p.Prime) (omega : Omega) {n : ℕ} (hn : 0 < n) :
    f (freshSignFlip {p} omega) n + eps omega p *
        (if p ∣ n then f (freshSignFlip {p} omega) (n / p) else 0) =
      f omega n - eps omega p *
        (if p ∣ n then f omega (n / p) else 0) := by
  classical
  by_cases hpn : p ∣ n
  · have hp_le_n : p ≤ n := Nat.le_of_dvd hn hpn
    have hq_pos : 0 < n / p := Nat.div_pos hp_le_n hp.pos
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
    have hflip :
        f (freshSignFlip {p} omega) n =
          eps (freshSignFlip {p} omega) p *
            f (freshSignFlip {p} omega) (n / p) := by
      calc
        f (freshSignFlip {p} omega) n =
            f (freshSignFlip {p} omega) (p * (n / p)) :=
          congrArg (f (freshSignFlip {p} omega)) hmul.symm
        _ = _ := f_prime_mul (freshSignFlip {p} omega) hp hq_pos
    have horiginal :
        f omega n = eps omega p * f omega (n / p) := by
      calc
        f omega n = f omega (p * (n / p)) :=
          congrArg (f omega) hmul.symm
        _ = _ := f_prime_mul omega hp hq_pos
    have heps :
        eps (freshSignFlip {p} omega) p = -eps omega p :=
      eps_freshSignFlip_of_mem {p} omega (by simp)
    simp only [hpn, ↓reduceIte]
    rw [hflip, horiginal, heps]
    ring
  · have hpnotmem : p ∉ sfKernel n := not_mem_sfKernel_of_not_dvd hpn
    simp [hpn, f_freshSignFlip_singleton, hpnotmem]

/-- Exact summatory recurrence obtained by replacing one Euler factor. -/
theorem S_oneCoordinateFlip_add
    (p : ℕ) (hp : p.Prime) (omega : Omega) (N : ℕ) :
    S (freshSignFlip {p} omega) N +
        eps omega p * S (freshSignFlip {p} omega) (N / p) =
      S omega N - eps omega p * S omega (N / p) := by
  classical
  unfold S
  rw [← sum_dvd_div_eq_sum_Icc_div
      (fun m => f (freshSignFlip {p} omega) m) N p hp.pos,
    ← sum_dvd_div_eq_sum_Icc_div (fun m => f omega m) N p hp.pos,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact oneCoordinateFlip_coefficient_recurrence p hp omega
    (lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hn).1)

/-- Division by any prime contracts the square-root scale by at least `3/4`.
The rational constant avoids introducing a prime-dependent denominator. -/
theorem four_mul_sqrt_natDiv_le_three_mul_sqrt
    (p N : ℕ) (hp : p.Prime) :
    4 * Real.sqrt (((N / p : ℕ) : ℝ)) ≤
      3 * Real.sqrt ((N : ℝ)) := by
  have hmul : (N / p) * p ≤ N := Nat.div_mul_le_self N p
  have htwo : 2 * (N / p) ≤ N := by
    have h := Nat.mul_le_mul_left (N / p) hp.two_le
    exact le_trans (by simpa [mul_comm] using h) hmul
  have htwoReal :
      2 * (((N / p : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast htwo
  have hscale :
      16 * (((N / p : ℕ) : ℝ)) ≤ 9 * (N : ℝ) := by
    have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith
  have hqnonneg : (0 : ℝ) ≤ ((N / p : ℕ) : ℝ) := by positivity
  have hNnonneg : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hsqrtq := Real.sqrt_nonneg (((N / p : ℕ) : ℝ))
  have hsqrtN := Real.sqrt_nonneg (N : ℝ)
  have hsqq := Real.sq_sqrt hqnonneg
  have hsqN := Real.sq_sqrt hNnonneg
  nlinarith

/-- Pointwise `O(sqrt N)` boundedness of the unnormalized summatory
function. -/
def SqrtBoundedPartialSums (omega : Omega) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    |S omega N| ≤ C * Real.sqrt (N : ℝ)

/-- A one-coordinate flip preserves `O(sqrt N)` boundedness.  The output
constant `8C` is deliberately coarse; only finiteness matters. -/
theorem sqrtBoundedPartialSums_freshSignFlip_singleton
    (p : ℕ) (hp : p.Prime) (omega : Omega)
    (hbounded : SqrtBoundedPartialSums omega) :
    SqrtBoundedPartialSums (freshSignFlip {p} omega) := by
  rcases hbounded with ⟨C, hC, hbound⟩
  refine ⟨8 * C, by positivity, ?_⟩
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      by_cases hNzero : N = 0
      · subst N
        simp [S]
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hNzero
        have hq_lt : N / p < N := Nat.div_lt_self hNpos hp.one_lt
        have hiq := ih (N / p) hq_lt
        have hrec := S_oneCoordinateFlip_add p hp omega N
        have heq :
            S (freshSignFlip {p} omega) N =
              S omega N - eps omega p * S omega (N / p) -
                eps omega p * S (freshSignFlip {p} omega) (N / p) := by
          linarith
        rw [heq]
        calc
          |S omega N - eps omega p * S omega (N / p) -
              eps omega p * S (freshSignFlip {p} omega) (N / p)|
              = |S omega N + (-(eps omega p * S omega (N / p))) +
                  (-(eps omega p *
                    S (freshSignFlip {p} omega) (N / p)))| := by
                congr 1
          _ ≤ |S omega N + (-(eps omega p * S omega (N / p)))| +
                |-(eps omega p *
                  S (freshSignFlip {p} omega) (N / p))| := abs_add_le _ _
          _ ≤ (|S omega N| + |-(eps omega p * S omega (N / p))|) +
                |-(eps omega p *
                  S (freshSignFlip {p} omega) (N / p))| := by
              gcongr
              exact abs_add_le _ _
          _ = |S omega N| + |S omega (N / p)| +
                |S (freshSignFlip {p} omega) (N / p)| := by
              simp [abs_mul]
          _ ≤ C * Real.sqrt (N : ℝ) +
                C * Real.sqrt (((N / p : ℕ) : ℝ)) +
                8 * C * Real.sqrt (((N / p : ℕ) : ℝ)) := by
              exact add_le_add
                (add_le_add (hbound N) (hbound (N / p))) hiq
          _ ≤ 8 * C * Real.sqrt (N : ℝ) := by
              have hcontract := four_mul_sqrt_natDiv_le_three_mul_sqrt p N hp
              have hsqrtN : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
              have hgap :
                  0 ≤ C *
                    (3 * Real.sqrt (N : ℝ) -
                      4 * Real.sqrt (((N / p : ℕ) : ℝ))) :=
                mul_nonneg hC (sub_nonneg.mpr hcontract)
              have hCN : 0 ≤ C * Real.sqrt (N : ℝ) := mul_nonneg hC hsqrtN
              nlinarith

/-- A global square-root bound rules out absolute normalized unboundedness. -/
theorem not_absErdos1144Point_of_sqrtBoundedPartialSums
    (omega : Omega) (hbounded : SqrtBoundedPartialSums omega) :
    ¬ absErdos1144Point omega := by
  rcases hbounded with ⟨C, hC, hbound⟩
  intro habs
  rcases (frequently_atTop.mp (habs (C + 1))) 0 with ⟨N, _hN, hlarge⟩
  have hsqrt : 0 < Real.sqrt (((N + 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos_of_pos (by positivity)
  have hnorm : |normSum omega N| ≤ C := by
    rw [normSum, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [div_le_iff₀ hsqrt]
    simpa [mul_comm] using hbound (N + 1)
  linarith

/-- Failure of absolute normalized unboundedness produces a global
`O(sqrt N)` bound.  The finitely many terms before the eventual bound are
absorbed using the elementary estimate `|S(N)| ≤ N`. -/
theorem sqrtBoundedPartialSums_of_not_absErdos1144Point
    (omega : Omega) (hnot : ¬ absErdos1144Point omega) :
    SqrtBoundedPartialSums omega := by
  rw [absErdos1144Point, not_forall] at hnot
  rcases hnot with ⟨A, hA⟩
  have hevent : ∀ᶠ N : ℕ in atTop, |normSum omega N| < A :=
    (not_frequently.mp hA).mono fun N hN => lt_of_not_ge hN
  rw [eventually_atTop] at hevent
  rcases hevent with ⟨N₀, hN₀⟩
  let C : ℝ := max A (N₀ + 1 : ℕ)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact le_trans (by positivity : (0 : ℝ) ≤ (N₀ + 1 : ℕ)) (le_max_right _ _)
  refine ⟨C, hC, fun N => ?_⟩
  by_cases hNzero : N = 0
  · subst N
    simp [S]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hNzero
    by_cases hlargeIndex : N₀ ≤ N - 1
    · have hlarge := hN₀ (N - 1) hlargeIndex
      have hsucc : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
      have hsqrt : 0 < Real.sqrt (N : ℝ) :=
        Real.sqrt_pos_of_pos (by exact_mod_cast hNpos)
      have hdiv : |S omega N| / Real.sqrt (N : ℝ) < A := by
        simpa [normSum, hsucc, abs_div,
          abs_of_nonneg (Real.sqrt_nonneg _)] using hlarge
      have hSA : |S omega N| < A * Real.sqrt (N : ℝ) :=
        (div_lt_iff₀ hsqrt).mp hdiv
      have hAC : A ≤ C := le_max_left _ _
      exact hSA.le.trans (mul_le_mul_of_nonneg_right hAC (Real.sqrt_nonneg _))
    · have hNle : N ≤ N₀ := by omega
      have hSN : |S omega N| ≤ (N : ℝ) := abs_S_le omega N
      have hNC : (N : ℝ) ≤ C := by
        have hcast : (N : ℝ) ≤ ((N₀ + 1 : ℕ) : ℝ) := by
          exact_mod_cast hNle.trans (Nat.le_add_right N₀ 1)
        exact hcast.trans (by exact le_max_right A ((N₀ + 1 : ℕ) : ℝ))
      have honeSqrt : (1 : ℝ) ≤ Real.sqrt (N : ℝ) := by
        rw [Real.one_le_sqrt]
        exact_mod_cast hNpos
      calc
        |S omega N| ≤ (N : ℝ) := hSN
        _ ≤ C := hNC
        _ = C * 1 := by ring
        _ ≤ C * Real.sqrt (N : ℝ) :=
          mul_le_mul_of_nonneg_left honeSqrt hC

/-- Absolute normalized unboundedness is exactly the negation of a global
square-root bound. -/
theorem absErdos1144Point_iff_not_sqrtBoundedPartialSums
    (omega : Omega) :
    absErdos1144Point omega ↔ ¬ SqrtBoundedPartialSums omega := by
  constructor
  · intro habs hbounded
    exact not_absErdos1144Point_of_sqrtBoundedPartialSums omega hbounded habs
  · intro hnot
    by_contra habs
    exact hnot (sqrtBoundedPartialSums_of_not_absErdos1144Point omega habs)

/-- Flipping the same finite coordinate set twice is the identity. -/
@[simp] theorem freshSignFlip_freshSignFlip
    (s : Finset ℕ) (omega : Omega) :
    freshSignFlip s (freshSignFlip s omega) = omega := by
  funext p
  by_cases hp : p ∈ s <;> cases homega : omega p <;>
    simp [freshSignFlip, hp, homega]

/-- One-coordinate flips preserve square-root boundedness in both directions. -/
theorem sqrtBoundedPartialSums_freshSignFlip_singleton_iff
    (p : ℕ) (hp : p.Prime) (omega : Omega) :
    SqrtBoundedPartialSums (freshSignFlip {p} omega) ↔
      SqrtBoundedPartialSums omega := by
  constructor
  · intro h
    have htwice :=
      sqrtBoundedPartialSums_freshSignFlip_singleton
        p hp (freshSignFlip {p} omega) h
    simpa using htwice
  · exact sqrtBoundedPartialSums_freshSignFlip_singleton p hp omega

/-- One prime-coordinate flip preserves absolute unboundedness. -/
theorem absErdos1144Point_freshSignFlip_singleton_iff
    (p : ℕ) (hp : p.Prime) (omega : Omega) :
    absErdos1144Point (freshSignFlip {p} omega) ↔
      absErdos1144Point omega := by
  simp only [absErdos1144Point_iff_not_sqrtBoundedPartialSums]
  exact not_congr (sqrtBoundedPartialSums_freshSignFlip_singleton_iff p hp omega)

/-- Every coordinate occurring in a squarefree kernel is prime. -/
theorem prime_of_mem_sfKernel {m p : ℕ} (hp : p ∈ sfKernel m) :
    p.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

/-- Flipping a non-prime coordinate does not change the model at all. -/
theorem f_freshSignFlip_singleton_of_not_prime
    (p : ℕ) (hp : ¬ p.Prime) (omega : Omega) (m : ℕ) :
    f (freshSignFlip {p} omega) m = f omega m := by
  rw [f_freshSignFlip_singleton, if_neg]
  exact fun hmem => hp (prime_of_mem_sfKernel hmem)

/-- The absolute event is invariant under a flip at any coordinate.  Prime
coordinates use the Euler recurrence; non-prime coordinates are noise. -/
theorem absErdos1144Point_freshSignFlip_singleton_iff_all
    (p : ℕ) (omega : Omega) :
    absErdos1144Point (freshSignFlip {p} omega) ↔
      absErdos1144Point omega := by
  by_cases hp : p.Prime
  · exact absErdos1144Point_freshSignFlip_singleton_iff p hp omega
  · have hS : ∀ N,
        S (freshSignFlip {p} omega) N = S omega N := by
      intro N
      unfold S
      apply Finset.sum_congr rfl
      intro m _hm
      exact f_freshSignFlip_singleton_of_not_prime p hp omega m
    constructor <;> intro h A
    · simpa [normSum, hS] using h A
    · simpa [normSum, hS] using h A

/-- Adding a new coordinate to a finite flip set is the same as applying its
singleton flip after the old flip. -/
theorem freshSignFlip_insert_of_notMem
    (p : ℕ) (s : Finset ℕ) (hp : p ∉ s) (omega : Omega) :
    freshSignFlip (insert p s) omega =
      freshSignFlip {p} (freshSignFlip s omega) := by
  funext q
  by_cases hqp : q = p
  · subst q
    cases homega : omega p <;> simp [freshSignFlip, hp, homega]
  · by_cases hqs : q ∈ s <;>
      cases homega : omega q <;>
      simp [freshSignFlip, hqp, hqs, homega]

/-- Absolute normalized unboundedness is invariant under every finite set of
coordinate changes. -/
theorem absErdos1144Point_freshSignFlip_iff
    (s : Finset ℕ) (omega : Omega) :
    absErdos1144Point (freshSignFlip s omega) ↔
      absErdos1144Point omega := by
  induction s using Finset.induction_on with
  | empty =>
      have hempty : freshSignFlip ∅ omega = omega := by
        funext p
        simp [freshSignFlip]
      rw [hempty]
  | @insert p s hp ih =>
      rw [freshSignFlip_insert_of_notMem p s hp omega]
      exact
        (absErdos1144Point_freshSignFlip_singleton_iff_all
          p (freshSignFlip s omega)).trans ih

/-- Clearing any finite coordinate prefix preserves absolute normalized
unboundedness. -/
theorem absErdos1144Point_clearCoordinatePrefix_iff
    (n : ℕ) (omega : Omega) :
    absErdos1144Point (clearCoordinatePrefix n omega) ↔
      absErdos1144Point omega := by
  rw [← freshSignFlip_truePrefixCoordinates]
  exact absErdos1144Point_freshSignFlip_iff _ _

/-- Clearing a finite prefix uses only coordinates from `n` onward. -/
theorem measurable_clearCoordinatePrefix_tailFrom (n : ℕ) :
    Measurable[coordinateTailFromMeasurableSpace n]
      (clearCoordinatePrefix n) := by
  refine @measurable_pi_lambda Omega ℕ (fun _ ↦ Bool)
    (coordinateTailFromMeasurableSpace n) (fun _ ↦ inferInstance)
    (clearCoordinatePrefix n) (fun i ↦ ?_)
  by_cases hi : i < n
  · simp [clearCoordinatePrefix, hi]
  · have hni : n ≤ i := Nat.le_of_not_gt hi
    simpa [clearCoordinatePrefix, hi] using
      measurable_coordinateTailFrom_eval_of_ge n i hni

/-- A measurable event invariant under clearing the first `n` coordinates is
measurable with respect to the coordinates from `n` onward. -/
theorem measurableSet_coordinateTailFrom_of_clearPrefix_invariant
    {E : Set Omega} (hE : MeasurableSet E) (n : ℕ)
    (hinvariant : ∀ omega,
      clearCoordinatePrefix n omega ∈ E ↔ omega ∈ E) :
    MeasurableSet[coordinateTailFromMeasurableSpace n] E := by
  have heq : E = clearCoordinatePrefix n ⁻¹' E := by
    ext omega
    exact (hinvariant omega).symm
  rw [heq]
  exact hE.preimage (measurable_clearCoordinatePrefix_tailFrom n)

/-- Event form of absolute normalized unboundedness. -/
def absErdos1144Event : Set Omega :=
  {omega | absErdos1144Point omega}

theorem measurableSet_absErdos1144Event :
    MeasurableSet absErdos1144Event := by
  rw [show absErdos1144Event =
      ⋂ k : ℕ, ⋂ n0 : ℕ,
        ⋃ N : ℕ, {omega : Omega |
          n0 ≤ N ∧ (k : ℝ) ≤ |normSum omega N|} by
    ext omega
    simp only [absErdos1144Event, Set.mem_setOf_eq, Set.mem_iInter,
      Set.mem_iUnion]
    constructor
    · intro h k n0
      rcases (frequently_atTop.mp (h k)) n0 with ⟨N, hNge, hN⟩
      exact ⟨N, hNge, hN⟩
    · intro h A
      rcases exists_nat_ge A with ⟨k, hAk⟩
      rw [frequently_atTop]
      intro n0
      rcases h k n0 with ⟨N, hNge, hN⟩
      exact ⟨N, hNge, hAk.trans hN⟩]
  refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun n0 =>
    MeasurableSet.iUnion fun N => ?_
  by_cases hN : n0 ≤ N
  · simpa [hN] using measurableSet_le measurable_const (measurable_normSum N).abs
  · simp [hN]

/-- Clearing every finite coordinate prefix without changing absolute
unboundedness makes the absolute event coordinate-tail measurable. -/
theorem measurableSet_absErdos1144Event_coordinateTail_of_clearPrefix_invariant
    (hinvariant : ∀ n omega,
      absErdos1144Point (clearCoordinatePrefix n omega) ↔
        absErdos1144Point omega) :
    MeasurableSet[coordinateTailMeasurableSpace] absErdos1144Event := by
  rw [coordinateTailMeasurableSpace, Filter.limsup_eq_iInf_iSup_of_nat]
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  exact measurableSet_coordinateTailFrom_of_clearPrefix_invariant
    measurableSet_absErdos1144Event n (hinvariant n)

/-- Absolute normalized unboundedness is an unconditional coordinate-tail
event for the completely multiplicative Rademacher model. -/
theorem measurableSet_absErdos1144Event_coordinateTail :
    MeasurableSet[coordinateTailMeasurableSpace] absErdos1144Event :=
  measurableSet_absErdos1144Event_coordinateTail_of_clearPrefix_invariant
    absErdos1144Point_clearCoordinatePrefix_iff

/-- Zero-one certificate for the absolute point event. -/
structure AbsErdos1144MeasureZeroOne where
  measure_zero_or_one :
    mu absErdos1144Event = 0 ∨ mu absErdos1144Event = 1

theorem absErdos1144MeasureZeroOne_of_measurableSet_coordinateTail
    (htail :
      MeasurableSet[coordinateTailMeasurableSpace] absErdos1144Event) :
    AbsErdos1144MeasureZeroOne := by
  refine ⟨?_⟩
  refine ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop
    (μ := mu) ?_ ?_ htail
  · intro n
    exact (measurable_pi_apply n).comap_le
  · simpa [ProbabilityTheory.iIndepFun] using iIndepFun_coordinates

/-- The absolute Erdős #1144 event has probability zero or one, with no
model-specific premise left. -/
theorem absErdos1144MeasureZeroOne : AbsErdos1144MeasureZeroOne :=
  absErdos1144MeasureZeroOne_of_measurableSet_coordinateTail
    measurableSet_absErdos1144Event_coordinateTail

/-- Positive probability of absolute unboundedness upgrades to the almost-sure
absolute target once the tail zero-one input is available. -/
theorem absErdos1144_of_measureZeroOne_of_measure_pos
    (hzero : AbsErdos1144MeasureZeroOne)
    (hpos : 0 < mu absErdos1144Event) :
    AbsErdos1144 := by
  rcases hzero.measure_zero_or_one with hzeroMeasure | hone
  · rw [hzeroMeasure] at hpos
    exact (lt_irrefl (0 : ℝ≥0∞) hpos).elim
  · have hmem : absErdos1144Event ∈ ae mu :=
      (MeasureTheory.mem_ae_iff_prob_eq_one
        measurableSet_absErdos1144Event).mpr hone
    simpa [AbsErdos1144, absErdos1144Event, absErdos1144Point] using hmem

/-- Any positive probability of absolute normalized unboundedness is already
enough for the almost-sure absolute target. -/
theorem absErdos1144_of_measure_pos
    (hpos : 0 < mu absErdos1144Event) :
    AbsErdos1144 :=
  absErdos1144_of_measureZeroOne_of_measure_pos
    absErdos1144MeasureZeroOne hpos

/-! ## Positive-probability block shortcut -/

/-- The event that a given block contains a large absolute normalized sum is
measurable. -/
theorem measurableSet_absBlockSuccess
    (X Y : ℕ → ℕ) (M : ℕ → ℝ) (j : ℕ) :
    MeasurableSet {omega : Omega | absBlockSuccess X Y M omega j} := by
  rw [show {omega : Omega | absBlockSuccess X Y M omega j} =
      ⋃ N ∈ Finset.Icc (X j) (Y j),
        {omega : Omega | M j ≤ |normSum omega N|} by
    ext omega
    simp [absBlockSuccess]]
  exact Finset.measurableSet_biUnion _ fun N _hN =>
    measurableSet_le measurable_const (measurable_normSum N).abs

/-- Infinitely many successful blocks with thresholds and left endpoints
tending to infinity imply pointwise absolute normalized unboundedness. -/
theorem absErdos1144Point_of_frequently_absBlockSuccess
    (X Y : ℕ → ℕ) (M : ℕ → ℝ)
    (hX : Tendsto X atTop atTop) (hM : Tendsto M atTop atTop)
    (omega : Omega)
    (hsuccess : ∃ᶠ j : ℕ in atTop, absBlockSuccess X Y M omega j) :
    absErdos1144Point omega := by
  intro A
  rw [Filter.Frequently]
  intro hbad
  rw [eventually_atTop] at hbad
  rcases hbad with ⟨N₀, hN₀⟩
  have hMevent : ∀ᶠ j : ℕ in atTop, A ≤ M j :=
    hM.eventually_ge_atTop A
  have hXevent : ∀ᶠ j : ℕ in atTop, N₀ ≤ X j :=
    hX.eventually_ge_atTop N₀
  rcases (hsuccess.and_eventually (hMevent.and hXevent)).exists with
    ⟨j, hblock, hAj, hXj⟩
  rcases hblock with ⟨N, hNmem, hlarge⟩
  have hN₀N : N₀ ≤ N :=
    hXj.trans (Finset.mem_Icc.mp hNmem).1
  exact hN₀ N hN₀N (hAj.trans hlarge)

/-- A positive-probability replacement for the old summable-failure block
certificate.  No independence between scales is required. -/
structure PositiveProbabilityAbsBlockOmega where
  X : ℕ → ℕ
  Y : ℕ → ℕ
  M : ℕ → ℝ
  lower : ℝ≥0∞
  lower_ne_zero : lower ≠ 0
  X_tendsto : Tendsto X atTop atTop
  M_tendsto : Tendsto M atTop atTop
  prob_success :
    ∀ j, lower ≤ mu {omega : Omega | absBlockSuccess X Y M omega j}

/-- Uniform positive success probability on every scale already proves the
almost-sure absolute target. -/
theorem absErdos1144_of_positiveProbabilityAbsBlockOmega
    (h : PositiveProbabilityAbsBlockOmega) :
    AbsErdos1144 := by
  let E : ℕ → Set Omega :=
    fun j => {omega : Omega | absBlockSuccess h.X h.Y h.M omega j}
  have hmeas : ∀ j, MeasurableSet (E j) :=
    fun j => measurableSet_absBlockSuccess h.X h.Y h.M j
  have hlower : h.lower ≤ mu (limsup E atTop) :=
    measure_limsup_atTop_ge_of_uniform_lower E hmeas h.prob_success
  have hsubset : limsup E atTop ⊆ absErdos1144Event := by
    intro omega homega
    rw [Filter.mem_limsup_iff_frequently_mem] at homega
    exact absErdos1144Point_of_frequently_absBlockSuccess
      h.X h.Y h.M h.X_tendsto h.M_tendsto omega homega
  have hpositive : 0 < mu absErdos1144Event := by
    have hcpos : 0 < h.lower := bot_lt_iff_ne_bot.mpr h.lower_ne_zero
    exact lt_of_lt_of_le hcpos (hlower.trans (measure_mono hsubset))
  exact absErdos1144_of_measure_pos hpositive

/-- Piercing at least one absolute endpoint screen produces a successful
absolute block when all candidate endpoints lie inside that block. -/
theorem endpointAbsScreenFailureEvent_compl_subset_absBlockSuccess
    (lo hi : ℕ → ℕ) (M : ℕ → ℝ)
    (indexSet : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℕ) (j : ℕ)
    (hendpoints :
      ∀ r, r ∈ indexSet j →
        a j r ∈ Finset.Icc (lo j) (hi j) ∧
          b j r ∈ Finset.Icc (lo j) (hi j)) :
    (endpointAbsScreenFailureEvent indexSet a b M j)ᶜ ⊆
      {omega : Omega | absBlockSuccess lo hi M omega j} := by
  rw [endpointAbsScreenFailureEvent_compl_eq_exists_pairSuccess]
  intro omega homega
  rcases homega with ⟨r, hr, hpair⟩
  rcases hendpoints r hr with ⟨ha, hb⟩
  exact endpointAbsPairSuccess_subset_absBlockSuccess
    lo hi M (a j r) (b j r) j ha hb hpair

/-- Endpoint-screen version of the positive-probability shortcut.  This is
the natural target for a one-scale second-moment or Paley--Zygmund argument:
the screen only needs a fixed nonzero chance of being pierced. -/
structure PositiveProbabilityEndpointSeparationAbsScreenCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  indexSet : ℕ → Finset ℕ
  a : ℕ → ℕ → ℕ
  b : ℕ → ℕ → ℕ
  lower : ℝ≥0∞
  lower_ne_zero : lower ≠ 0
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  endpoints_in_block :
    ∀ j r, r ∈ indexSet j →
      a j r ∈ Finset.Icc (lo j) (hi j) ∧
        b j r ∈ Finset.Icc (lo j) (hi j)
  prob_screen_success :
    ∀ j, lower ≤
      mu ((endpointAbsScreenFailureEvent indexSet a b M j)ᶜ)

/-- Endpoint-screen positive probability induces block positive probability. -/
noncomputable def positiveProbabilityAbsBlockOmega_of_endpointScreen
    (h : PositiveProbabilityEndpointSeparationAbsScreenCertificate) :
    PositiveProbabilityAbsBlockOmega where
  X := h.lo
  Y := h.hi
  M := h.M
  lower := h.lower
  lower_ne_zero := h.lower_ne_zero
  X_tendsto := h.lo_tendsto_atTop
  M_tendsto := h.M_tendsto_atTop
  prob_success := by
    intro j
    exact (h.prob_screen_success j).trans (measure_mono
      (endpointAbsScreenFailureEvent_compl_subset_absBlockSuccess
        h.lo h.hi h.M h.indexSet h.a h.b j
        (fun r hr => h.endpoints_in_block j r hr)))

/-- Fixed positive endpoint-screen success at every scale proves the
almost-sure absolute Erdős #1144 target. -/
theorem absErdos1144_of_positiveProbabilityEndpointScreen
    (h : PositiveProbabilityEndpointSeparationAbsScreenCertificate) :
    AbsErdos1144 :=
  absErdos1144_of_positiveProbabilityAbsBlockOmega
    (positiveProbabilityAbsBlockOmega_of_endpointScreen h)

end Problem1144
end Erdos
