import Erdos.Problem1144.Orthogonality

open scoped BigOperators

namespace Erdos
namespace Problem1144

/-- Multiplying by a prime not already dividing `m` inserts that prime into
the squarefree kernel.

This is the focused complete-multiplicativity lemma needed for Harper's
large-prime decomposition: in the range `n < X^2`, the large prime occurs
exactly once, so the quotient is not divisible by that prime.
-/
theorem sfKernel_prime_mul_of_not_dvd
    {p m : ℕ} (hp : p.Prime) (hm : 0 < m) (hpm : ¬ p ∣ m) :
    sfKernel (p * m) = insert p (sfKernel m) := by
  ext q
  by_cases hq : q = p
  · subst q
    have hodd : Odd ((p * m).factorization p) := by
      rw [Nat.factorization_mul hp.ne_zero hm.ne']
      simp [hp.factorization, Nat.factorization_eq_zero_of_not_dvd hpm]
    rw [Finset.mem_insert, mem_sfKernel_iff_odd_factorization]
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      exact hodd
  · have hfac : (p * m).factorization q = m.factorization q := by
      rw [Nat.factorization_mul hp.ne_zero hm.ne', hp.factorization]
      simp [hq]
    rw [Finset.mem_insert, mem_sfKernel_iff_odd_factorization,
      mem_sfKernel_iff_odd_factorization, hfac]
    simp [hq]

/-- If `p` does not divide `m`, then `p` is absent from the squarefree kernel
of `m`. -/
theorem not_mem_sfKernel_of_not_dvd
    {p m : ℕ} (hpm : ¬ p ∣ m) :
    p ∉ sfKernel m := by
  intro hp_mem
  have hodd : Odd (m.factorization p) :=
    (mem_sfKernel_iff_odd_factorization m p).mp hp_mem
  have hzero : m.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpm
  rw [hzero] at hodd
  exact Nat.not_odd_zero hodd

/-- Prime-step multiplicativity for the complete Rademacher model.

This is the form used to turn a rough summand `f(p*m)` into the fresh large
prime sign `eps p` times the already-conditioned coefficient `f(m)`.
-/
theorem f_prime_mul_of_not_dvd
    (omega : Omega) {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hpm : ¬ p ∣ m) :
    f omega (p * m) = eps omega p * f omega m := by
  have hnotmem : p ∉ sfKernel m := not_mem_sfKernel_of_not_dvd hpm
  rw [f, sfKernel_prime_mul_of_not_dvd hp hm hpm]
  rw [Finset.prod_insert hnotmem]
  rfl

/-- Swapped prime-step multiplicativity. -/
theorem f_mul_prime_of_not_dvd
    (omega : Omega) {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hpm : ¬ p ∣ m) :
    f omega (m * p) = f omega m * eps omega p := by
  rw [mul_comm m p, f_prime_mul_of_not_dvd omega hp hm hpm, mul_comm]

/-- Multiplication by a prime toggles that prime in the squarefree kernel,
whether or not the prime already divides the other factor. -/
theorem sfKernel_prime_mul
    {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    sfKernel (p * m) =
      if p ∈ sfKernel m then (sfKernel m).erase p
      else insert p (sfKernel m) := by
  classical
  by_cases hpmem : p ∈ sfKernel m
  · rw [if_pos hpmem]
    have hpodd : Odd (m.factorization p) :=
      (mem_sfKernel_iff_odd_factorization m p).mp hpmem
    ext q
    have hfac :
        (p * m).factorization q = p.factorization q + m.factorization q := by
      simpa [Finsupp.add_apply] using congrFun
        (congrArg DFunLike.coe
          (Nat.factorization_mul hp.ne_zero hm.ne')) q
    rw [Finset.mem_erase, mem_sfKernel_iff_odd_factorization,
      mem_sfKernel_iff_odd_factorization, hfac, hp.factorization]
    by_cases hqp : q = p
    · subst q
      simp [hpodd]
    · simp [hqp]
  · rw [if_neg hpmem]
    have hpnotodd : ¬ Odd (m.factorization p) := by
      simpa [mem_sfKernel_iff_odd_factorization] using hpmem
    ext q
    have hfac :
        (p * m).factorization q = p.factorization q + m.factorization q := by
      simpa [Finsupp.add_apply] using congrFun
        (congrArg DFunLike.coe
          (Nat.factorization_mul hp.ne_zero hm.ne')) q
    rw [Finset.mem_insert, mem_sfKernel_iff_odd_factorization,
      mem_sfKernel_iff_odd_factorization, hfac, hp.factorization]
    by_cases hqp : q = p
    · subst q
      have heven : Even (m.factorization p) :=
        Nat.not_odd_iff_even.mp hpnotodd
      have hodd : Odd (1 + m.factorization p) := by
        simpa [add_comm] using heven.add_one
      simp [hodd]
    · simp [hqp]

/-- Prime-step multiplicativity without a coprimality hypothesis.  This is the
single-prime form of complete multiplicativity. -/
theorem f_prime_mul
    (omega : Omega) {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    f omega (p * m) = eps omega p * f omega m := by
  classical
  rw [f, sfKernel_prime_mul hp hm]
  by_cases hpmem : p ∈ sfKernel m
  · rw [if_pos hpmem]
    change (∏ q ∈ (sfKernel m).erase p, eps omega q) =
      eps omega p * ∏ q ∈ sfKernel m, eps omega q
    rw [← Finset.mul_prod_erase (sfKernel m) (eps omega) hpmem]
    rw [← mul_assoc, eps_mul_self, one_mul]
  · rw [if_neg hpmem, Finset.prod_insert hpmem]
    rfl

/-- Swapped prime-step complete multiplicativity. -/
theorem f_mul_prime
    (omega : Omega) {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    f omega (m * p) = f omega m * eps omega p := by
  rw [mul_comm m p, f_prime_mul omega hp hm, mul_comm]

/-- Full complete multiplicativity on positive integers.  The model assigns
`f(0)=1`, so positivity is essential when packaging it as an arithmetic
coefficient rather than a map-with-zero. -/
theorem f_mul_of_pos
    (omega : Omega) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    f omega (m * n) = f omega m * f omega n := by
  let motive : ℕ → Prop := fun a ↦
    a = 0 ∨ ∀ b : ℕ, 0 < b → f omega (a * b) = f omega a * f omega b
  have hall : ∀ a : ℕ, motive a := by
    apply induction_on_primes
    · exact Or.inl rfl
    · exact Or.inr (by intro b hb; simp)
    · intro p a hp ih
      by_cases ha : a = 0
      · exact Or.inl (by simp [ha])
      · have haPos : 0 < a := Nat.pos_of_ne_zero ha
        have ihMul : ∀ b : ℕ, 0 < b →
            f omega (a * b) = f omega a * f omega b :=
          ih.resolve_left ha
        refine Or.inr ?_
        intro b hb
        calc
          f omega ((p * a) * b) = f omega (p * (a * b)) := by
            rw [mul_assoc]
          _ = eps omega p * f omega (a * b) :=
            f_prime_mul omega hp (Nat.mul_pos haPos hb)
          _ = eps omega p * (f omega a * f omega b) := by
            rw [ihMul b hb]
          _ = (eps omega p * f omega a) * f omega b := by ring
          _ = f omega (p * a) * f omega b := by
            rw [f_prime_mul omega hp haPos]
  exact (hall m).resolve_left hm.ne' n hn

theorem f_mul_of_ne_zero
    (omega : Omega) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    f omega (m * n) = f omega m * f omega n :=
  f_mul_of_pos omega (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

/-- The completely multiplicative signs packaged as a map with zero.  This
is the form consumed by general Euler-product lemmas; on positive integers it
is definitionally the original model. -/
noncomputable def fMonoidWithZeroHom (omega : Omega) : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else f omega n
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    simp only [hm, hn, mul_eq_zero, or_false, if_false]
    exact f_mul_of_ne_zero omega hm hn

@[simp] theorem fMonoidWithZeroHom_apply_of_pos
    (omega : Omega) {n : ℕ} (hn : 0 < n) :
    fMonoidWithZeroHom omega n = f omega n := by
  simp [fMonoidWithZeroHom, hn.ne']

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.f_mul_of_pos
#print axioms Erdos.Problem1144.fMonoidWithZeroHom
