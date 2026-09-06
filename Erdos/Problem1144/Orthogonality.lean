import Erdos.Problem1144.Statistics
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.MeasureTheory.Integral.Pi

open MeasureTheory
open scoped BigOperators

namespace Erdos
namespace Problem1144

/-- Real-valued indicator of the square condition. -/
noncomputable def squareIndicator (n : ℕ) : ℝ := by
  classical
  exact if IsSquare n then 1 else 0

@[simp] theorem squareIndicator_nonneg (n : ℕ) :
    0 ≤ squareIndicator n := by
  unfold squareIndicator
  by_cases hsq : IsSquare n <;> simp [hsq]

@[simp] theorem squareIndicator_le_one (n : ℕ) :
    squareIndicator n ≤ 1 := by
  unfold squareIndicator
  by_cases hsq : IsSquare n <;> simp [hsq]

/-- A finite Walsh character on the coin-flip product space.

The exponent function is intentionally not reduced modulo two: the integral
lemma below is the place where parity is used.
-/
noncomputable def coordChar (P : Finset ℕ) (k : ℕ → ℕ) (omega : Omega) : ℝ :=
  ∏ p ∈ P, eps omega p ^ k p

/-- Finite coordinate characters are measurable. -/
theorem measurable_coordChar (P : Finset ℕ) (k : ℕ → ℕ) :
    Measurable fun omega : Omega => coordChar P k omega := by
  unfold coordChar
  exact Finset.measurable_prod _ fun p _ => (measurable_eps p).pow_const _

/-- The finite product integral over a restricted Boolean cube factors into
one-coordinate expectations. -/
theorem integral_boolSign_pi_char (P : Finset ℕ) (k : ℕ → ℕ) :
    ∫ x : (p : P) → Bool, (∏ p : P, boolSign (x p) ^ k p)
        ∂Measure.pi (fun _ : P => coin)
      =
    ∏ p : P, (if Even (k p) then (1 : ℝ) else 0) := by
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (f := fun (p : P) (b : Bool) => boolSign b ^ k p)
    (μ := fun _ : P => coin)]
  exact Finset.prod_congr rfl fun p _ => by
    simpa using integral_boolSign_pow (k p)

/-- Finite Walsh-character orthogonality under the infinite fair-coin product. -/
theorem integral_coordChar (P : Finset ℕ) (k : ℕ → ℕ) :
    ∫ omega, coordChar P k omega ∂mu
      =
    ∏ p : P, (if Even (k p) then (1 : ℝ) else 0) := by
  let F : ((p : P) → Bool) → ℝ :=
    fun x => ∏ p : P, boolSign (x p) ^ k p
  have hF :
      AEStronglyMeasurable F (Measure.pi (fun _ : P => coin)) := by
    exact (measurable_of_finite F).aestronglyMeasurable
  have hrestrict :=
    integral_restrict_infinitePi
      (μ := fun _ : ℕ => coin)
      (s := P)
      (f := F)
      hF
  have hleft :
      (fun omega : Omega => F (P.restrict omega))
        =
      (fun omega : Omega => coordChar P k omega) := by
    funext omega
    change
      (∏ x ∈ P.attach, boolSign (omega ↑x) ^ k ↑x)
        =
      (∏ x ∈ P, boolSign (omega x) ^ k x)
    exact Finset.prod_attach P fun p => boolSign (omega p) ^ k p
  rw [← hleft]
  simpa [mu, F] using hrestrict.trans (integral_boolSign_pi_char P k)

/-- A finite Walsh character has mean zero as soon as one exponent is odd. -/
theorem integral_coordChar_of_exists_odd
    (P : Finset ℕ) (k : ℕ → ℕ)
    (hodd : ∃ p, p ∈ P ∧ Odd (k p)) :
    ∫ omega, coordChar P k omega ∂mu = 0 := by
  rw [integral_coordChar]
  rcases hodd with ⟨p, hp, hkp⟩
  have hknot : ¬ Even (k p) := Nat.not_even_iff_odd.mpr hkp
  exact
    Finset.prod_eq_zero
      (s := Finset.univ)
      (i := ⟨p, hp⟩)
      (by simp)
      (by simp [hknot])

/-- A finite Walsh character has mean one when every exponent is even. -/
theorem integral_coordChar_of_forall_even
    (P : Finset ℕ) (k : ℕ → ℕ)
    (heven : ∀ p, p ∈ P → Even (k p)) :
    ∫ omega, coordChar P k omega ∂mu = 1 := by
  rw [integral_coordChar]
  exact Finset.prod_eq_one fun p _ => by
    simp [heven p p.property]

/-- The multiset of prime-coordinate appearances in a finite product
`∏ i, f (n i)`. Repeated appearances are retained, as they encode parity. -/
noncomputable def prodFPrimeMultiset {α : Type*}
    (I : Finset α) (n : α → ℕ) : Multiset ℕ :=
  I.val.bind fun i => (sfKernel (n i)).val

/-- The finite prime support of a finite product of `f` values. -/
noncomputable def prodFSupport {α : Type*}
    (I : Finset α) (n : α → ℕ) : Finset ℕ :=
  (prodFPrimeMultiset I n).toFinset

/-- The exponent count of a coordinate in a finite product of `f` values. -/
noncomputable def prodFExponent {α : Type*}
    (I : Finset α) (n : α → ℕ) (p : ℕ) : ℕ :=
  (prodFPrimeMultiset I n).count p

/-- Coordinate exponent counts are cardinalities of the indices where that
prime lies in the individual squarefree kernels. -/
theorem prodFExponent_eq_card_filter
    {α : Type*} (I : Finset α) (n : α → ℕ) (p : ℕ) :
    prodFExponent I n p
      =
    (I.filter fun i => p ∈ sfKernel (n i)).card := by
  classical
  have hcount :
      ∀ i, Multiset.count p (sfKernel (n i)).val =
        if p ∈ sfKernel (n i) then 1 else 0 := fun i =>
    Multiset.count_eq_of_nodup (sfKernel (n i)).nodup
  simp [prodFExponent, prodFPrimeMultiset, Multiset.count_bind, hcount]

/-- A prime coordinate lies in the collected support exactly when its collected
exponent count is positive. -/
theorem mem_prodFSupport_iff
    {α : Type*} (I : Finset α) (n : α → ℕ) (p : ℕ) :
    p ∈ prodFSupport I n ↔ 0 < prodFExponent I n p := by
  classical
  rw [prodFSupport, prodFExponent, Multiset.mem_toFinset]
  exact (Multiset.count_pos (a := p) (s := prodFPrimeMultiset I n)).symm

/-- Factorization of a finite product, pointwise at a prime coordinate. -/
theorem factorization_prod_apply
    {α : Type*} (I : Finset α) (n : α → ℕ)
    (hpos : ∀ i, i ∈ I → 0 < n i) (p : ℕ) :
    (∏ i ∈ I, n i).factorization p
      =
    ∑ i ∈ I, (n i).factorization p := by
  classical
  have hne : ∀ i ∈ I, n i ≠ 0 := fun i hi => (hpos i hi).ne'
  have h := congrArg (fun q : ℕ →₀ ℕ => q p)
    (Nat.factorization_prod (S := I) (g := n) hne)
  simpa using h

/-- A positive square has even valuation at every prime coordinate. -/
theorem factorization_even_of_isSquare
    {n : ℕ} (hn : n ≠ 0) (hsq : IsSquare n) (p : ℕ) :
    Even (n.factorization p) := by
  rcases hsq with ⟨r, hr⟩
  have hr_ne : r ≠ 0 := by
    intro h0
    apply hn
    rw [hr, h0, zero_mul]
  rw [hr]
  have hfac : (r * r).factorization p = (r.factorization + r.factorization) p := by
    simpa using
      (congrArg (fun q : ℕ →₀ ℕ => q p)
        (Nat.factorization_mul hr_ne hr_ne))
  rw [hfac]
  simp [Finsupp.add_apply]

/-- If all valuations of a positive natural are even, then the natural is a
square. -/
theorem isSquare_of_forall_factorization_even
    {n : ℕ} (hn : n ≠ 0) (heven : ∀ p, Even (n.factorization p)) :
    IsSquare n := by
  let half : ℕ →₀ ℕ := n.factorization.mapRange (fun k => k / 2) (by simp)
  let r : ℕ := half.prod fun p e => p ^ e
  have hhalf_support : ∀ p ∈ half.support, Nat.Prime p := by
    intro p hp
    have hp' : p ∈ n.factorization.support := by
      exact Finsupp.support_mapRange hp
    rw [Nat.support_factorization] at hp'
    exact Nat.prime_of_mem_primeFactors hp'
  have hrfac : r.factorization = half := by
    simpa [r] using Nat.prod_pow_factorization_eq_self hhalf_support
  have hr_ne : r ≠ 0 := by
    dsimp [r]
    exact half.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (hhalf_support p hp).ne_zero
  have hrrfac : (r * r).factorization = n.factorization := by
    rw [Nat.factorization_mul hr_ne hr_ne, hrfac]
    ext p
    simp [half, Finsupp.mapRange_apply]
    simpa [two_mul] using Nat.two_mul_div_two_of_even (heven p)
  have hEq : r * r = n :=
    Nat.eq_of_factorization_eq (mul_ne_zero hr_ne hr_ne) hn fun p => by
      exact congrFun (congrArg DFunLike.coe hrrfac) p
  exact ⟨r, hEq.symm⟩

/-- A coordinate belongs to the squarefree kernel exactly when its valuation is
odd. -/
theorem mem_sfKernel_iff_odd_factorization (n p : ℕ) :
    p ∈ sfKernel n ↔ Odd (n.factorization p) := by
  constructor
  · intro hp
    rw [sfKernel, Finset.mem_filter] at hp
    exact Nat.not_even_iff_odd.mp (Nat.not_even_iff.mpr hp.2)
  · intro hp
    have hne : n.factorization p ≠ 0 := by
      intro hzero
      rw [hzero] at hp
      exact Nat.not_odd_zero hp
    have hmem : p ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hne
    rw [Nat.support_factorization] at hmem
    rw [sfKernel, Finset.mem_filter]
    exact ⟨hmem, Nat.not_even_iff.mp (Nat.not_even_iff_odd.mpr hp)⟩

/-- On a prime input, the completely multiplicative model is the corresponding
coordinate sign. -/
theorem f_prime (omega : Omega) {p : ℕ} (hp : p.Prime) :
    f omega p = eps omega p := by
  rw [f]
  have hsf : sfKernel p = {p} := by
    ext q
    rw [Finset.mem_singleton, mem_sfKernel_iff_odd_factorization, hp.factorization]
    by_cases hq : q = p
    · subst hq
      simp
    · simpa [Finsupp.single_eq_of_ne hq] using hq
  simp [hsf]

/-- The collected squarefree-coordinate exponent has the same parity as the
sum of the corresponding prime valuations. -/
theorem even_prodFExponent_iff_even_factorization_sum
    {α : Type*} (I : Finset α) (n : α → ℕ) (p : ℕ) :
    Even (prodFExponent I n p)
      ↔
    Even (∑ i ∈ I, (n i).factorization p) := by
  classical
  rw [prodFExponent_eq_card_filter]
  have hfilter :
      (I.filter fun i => p ∈ sfKernel (n i))
        =
      (I.filter fun i => Odd ((n i).factorization p)) := by
    ext i
    simp [mem_sfKernel_iff_odd_factorization]
  rw [hfilter]
  exact (Finset.even_sum_iff_even_card_odd
    (s := I) (f := fun i => (n i).factorization p)).symm

/-- A finite product of model values is exactly the coordinate character
obtained by collecting the prime-coordinate appearances with multiplicity. -/
theorem prod_f_eq_coordChar
    {α : Type*} (I : Finset α) (n : α → ℕ) (omega : Omega) :
    (∏ i ∈ I, f omega (n i))
      =
    coordChar (prodFSupport I n) (prodFExponent I n) omega := by
  classical
  let m : Multiset ℕ := prodFPrimeMultiset I n
  calc
    (∏ i ∈ I, f omega (n i))
        = (m.map fun p => eps omega p).prod := by
          simp [m, prodFPrimeMultiset, f, Multiset.map_bind, Multiset.prod_bind]
    _ = ∏ p ∈ m.toFinset, eps omega p ^ m.count p := by
          rw [Finset.prod_multiset_map_count]
    _ = coordChar (prodFSupport I n) (prodFExponent I n) omega := by
          simp [coordChar, prodFSupport, prodFExponent, m]

/-- Product form of the finite parity indicator. -/
theorem prod_parity_indicator (P : Finset ℕ) (k : ℕ → ℕ) :
    (∏ p : P, (if Even (k p) then (1 : ℝ) else 0))
      =
    if (∀ p, p ∈ P → Even (k p)) then 1 else 0 := by
  by_cases hpar : ∀ p, p ∈ P → Even (k p)
  · rw [if_pos hpar]
    exact Finset.prod_eq_one fun p _ => by
      simp [hpar p p.property]
  · rw [if_neg hpar]
    push Not at hpar
    rcases hpar with ⟨p, hp, hp_odd_exp⟩
    exact
      Finset.prod_eq_zero
        (s := Finset.univ)
        (i := ⟨p, hp⟩)
        (by simp)
        (by simp [hp_odd_exp])

/-- The square condition for the integer product is exactly even parity of all
collected squarefree-kernel coordinates.

The positivity hypothesis excludes the artificial `0` case, where every
integer is not represented by a nonzero prime factorization.
-/
theorem isSquare_prod_iff_prodFParity
  {α : Type*}
  (I : Finset α)
  (n : α → ℕ)
  (hpos : ∀ i, i ∈ I → 0 < n i) :
  IsSquare (∏ i ∈ I, n i)
    ↔
  ∀ p, p ∈ prodFSupport I n → Even (prodFExponent I n p) := by
  classical
  have hprod_ne : (∏ i ∈ I, n i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi => (hpos i hi).ne'
  constructor
  · intro hsq p _hp
    have hval := factorization_even_of_isSquare hprod_ne hsq p
    rw [factorization_prod_apply I n hpos p] at hval
    exact (even_prodFExponent_iff_even_factorization_sum I n p).mpr hval
  · intro hpar
    refine isSquare_of_forall_factorization_even hprod_ne fun p => ?_
    rw [factorization_prod_apply I n hpos p]
    refine (even_prodFExponent_iff_even_factorization_sum I n p).mp ?_
    by_cases hp : p ∈ prodFSupport I n
    · exact hpar p hp
    · have hnot_pos : ¬ 0 < prodFExponent I n p := by
        intro hpos_exp
        exact hp ((mem_prodFSupport_iff I n p).mpr hpos_exp)
      have hzero : prodFExponent I n p = 0 := Nat.eq_zero_of_not_pos hnot_pos
      rw [hzero]
      exact Even.zero

/-- Algebraic square criterion for the collected prime-coordinate parities,
in the real indicator form needed by finite moment expansions. -/
theorem squareIndicator_eq_prodFParity
  {α : Type*}
  (I : Finset α)
  (n : α → ℕ)
  (hpos : ∀ i, i ∈ I → 0 < n i) :
  squareIndicator (∏ i ∈ I, n i)
    =
  if (∀ p, p ∈ prodFSupport I n → Even (prodFExponent I n p)) then 1 else 0
    := by
  classical
  have hiff := isSquare_prod_iff_prodFParity I n hpos
  by_cases hsq : IsSquare (∏ i ∈ I, n i)
  · rw [squareIndicator, if_pos hsq, if_pos (hiff.mp hsq)]
  · have hnot :
        ¬ ∀ p, p ∈ prodFSupport I n → Even (prodFExponent I n p) := by
      intro hpar
      exact hsq (hiff.mpr hpar)
    rw [squareIndicator, if_neg hsq, if_neg hnot]

/-- Orthogonality of the Rademacher multiplicative characters, indexed by an
arbitrary finite family. -/
theorem integral_prod_f_indexed
  {α : Type*}
  (I : Finset α)
  (n : α → ℕ)
  (hpos : ∀ i, i ∈ I → 0 < n i) :
  ∫ omega, (∏ i ∈ I, f omega (n i)) ∂mu =
    squareIndicator (∏ i ∈ I, n i) := by
  have hfun :
      (fun omega : Omega => ∏ i ∈ I, f omega (n i))
        =
      fun omega : Omega => coordChar (prodFSupport I n) (prodFExponent I n) omega := by
    funext omega
    exact prod_f_eq_coordChar I n omega
  rw [hfun, integral_coordChar, squareIndicator_eq_prodFParity I n hpos,
    prod_parity_indicator]

/-- Compatibility wrapper for the older set-of-integers form. -/
theorem integral_prod_f
  (ns : Finset ℕ)
  (hpos : ∀ n, n ∈ ns → 0 < n) :
  ∫ omega, (∏ n ∈ ns, f omega n) ∂mu =
    squareIndicator (∏ n ∈ ns, n) :=
  integral_prod_f_indexed ns id hpos

end Problem1144
end Erdos
