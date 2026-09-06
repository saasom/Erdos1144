import Erdos.Problem1144.HarperBlock
import Erdos.Problem1144.Multiplicativity

open scoped BigOperators

namespace Erdos
namespace Problem1144

/-- `n` is `X`-smooth if all prime divisors of `n` are at most `X`. -/
def IsXSmooth (X n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, p ≤ X

/-- For positive `n`, failing `X`-smoothness is exactly having a prime divisor
above `X`. -/
theorem not_isXSmooth_iff_exists_large_prime_of_ne_zero
    (X n : ℕ) (hn : n ≠ 0) :
    ¬ IsXSmooth X n ↔
      ∃ p : ℕ, p.Prime ∧ X < p ∧ p ∣ n := by
  constructor
  · intro h
    unfold IsXSmooth at h
    push Not at h
    rcases h with ⟨p, hp_mem, hXp⟩
    exact
      ⟨p, Nat.prime_of_mem_primeFactors hp_mem, hXp,
        Nat.dvd_of_mem_primeFactors hp_mem⟩
  · rintro ⟨p, hp, hXp, hpn⟩ hsmooth
    have hp_mem : p ∈ n.primeFactors := hp.mem_primeFactors hpn hn
    exact not_lt_of_ge (hsmooth p hp_mem) hXp

/-- The `X`-smooth part of the summatory function. -/
noncomputable def smoothSum (omega : Omega) (X N : ℕ) : ℝ :=
  by
    classical
    exact ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsXSmooth X n), f omega n

/-- The complementary, non-`X`-smooth part of the summatory function. -/
noncomputable def roughSum (omega : Omega) (X N : ℕ) : ℝ :=
  by
    classical
    exact ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ IsXSmooth X n), f omega n

/-- The finite set of rough summands up to `N`. -/
noncomputable def roughSet (X N : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 N).filter (fun n => ¬ IsXSmooth X n)

/-- Membership in the rough summand set. -/
theorem mem_roughSet {X N n : ℕ} :
    n ∈ roughSet X N ↔ n ∈ Finset.Icc 1 N ∧ ¬ IsXSmooth X n := by
  classical
  rw [roughSet, Finset.mem_filter]

/-- Deterministic smooth/rough split of the summatory function. -/
theorem S_eq_smoothSum_add_roughSum
    (omega : Omega) (X N : ℕ) :
    S omega N = smoothSum omega X N + roughSum omega X N := by
  classical
  unfold S smoothSum roughSum
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 N)
    (p := fun n => IsXSmooth X n)
    (f := fun n => f omega n)]

/-- `roughSum` is the sum over `roughSet`. -/
theorem roughSum_eq_sum_roughSet
    (omega : Omega) (X N : ℕ) :
    roughSum omega X N = ∑ n ∈ roughSet X N, f omega n := by
  classical
  rfl

/-- Prime divisors of numbers in `[1, N]` are themselves at most `N`. -/
theorem prime_dvd_le_of_mem_Icc
    {p n N : ℕ}
    (hn : n ∈ Finset.Icc 1 N) (hpn : p ∣ n) :
    p ≤ N := by
  have hn_pos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  exact (Nat.le_of_dvd hn_pos hpn).trans hnN

/-- Large prime divisors of a block summand lie in the finite prime interval
`(X, N]`. -/
theorem large_prime_mem_interval_of_dvd
    {X N p n : ℕ} (hp : p.Prime)
    (hXp : X < p) (hn : n ∈ Finset.Icc 1 N) (hpn : p ∣ n) :
    p ∈ (Finset.Icc (X + 1) N).filter (fun q => q.Prime) := by
  rw [Finset.mem_filter]
  refine ⟨?_, hp⟩
  rw [Finset.mem_Icc]
  exact ⟨Nat.succ_le_of_lt hXp, prime_dvd_le_of_mem_Icc hn hpn⟩

/-- The finite set of primes in `(X, N]`, the large-prime coordinates visible
to the block cutoff `N`. -/
noncomputable def largePrimeInterval (X N : ℕ) : Finset ℕ :=
  (Finset.Icc (X + 1) N).filter (fun p => p.Prime)

/-- Membership in the finite large-prime interval. -/
theorem mem_largePrimeInterval {X N p : ℕ} :
    p ∈ largePrimeInterval X N ↔ p.Prime ∧ X < p ∧ p ≤ N := by
  rw [largePrimeInterval, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hXp, hpN⟩, hp⟩
    exact ⟨hp, Nat.lt_of_succ_le hXp, hpN⟩
  · rintro ⟨hp, hXp, hpN⟩
    exact ⟨⟨Nat.succ_le_of_lt hXp, hpN⟩, hp⟩

/-- Pair index set for Harper's large-prime contribution. A pair is a large
prime `p` and a quotient `m <= N/p`. -/
noncomputable def largePrimePairs (X N : ℕ) :
    Finset (Sigma fun _p : ℕ => ℕ) :=
  (largePrimeInterval X N).sigma fun p => Finset.Icc 1 (N / p)

/-- Membership in the large-prime pair index set. -/
theorem mem_largePrimePairs {X N : ℕ} {a : Sigma fun _p : ℕ => ℕ} :
    a ∈ largePrimePairs X N ↔
      a.1 ∈ largePrimeInterval X N ∧ a.2 ∈ Finset.Icc 1 (N / a.1) := by
  rw [largePrimePairs, Finset.mem_sigma]

/-- Every nonsmooth summand has at least one visible large prime coordinate. -/
theorem exists_largePrimeInterval_of_not_isXSmooth
    {X N n : ℕ}
    (hn : n ∈ Finset.Icc 1 N) (hrough : ¬ IsXSmooth X n) :
    ∃ p ∈ largePrimeInterval X N, p ∣ n := by
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hn).1
  have hn_ne : n ≠ 0 := hn_pos.ne'
  rcases (not_isXSmooth_iff_exists_large_prime_of_ne_zero X n hn_ne).mp hrough with
    ⟨p, hp, hXp, hpn⟩
  exact
    ⟨p,
      (mem_largePrimeInterval (X := X) (N := N) (p := p)).mpr
        ⟨hp, hXp, prime_dvd_le_of_mem_Icc hn hpn⟩,
      hpn⟩

/-- Under `N < X^2`, a number `n <= N` cannot have two prime divisors above
`X`.

This is the uniqueness fact behind Harper's large-prime decomposition: the
rough part can be reindexed by the unique large prime `p` and the quotient
`m = n / p`.
-/
theorem large_prime_unique_of_lt_square
    {X N n p q : ℕ}
    (hN : N < X ^ 2)
    (hn : n ∈ Finset.Icc 1 N)
    (hp : p.Prime) (hXp : X < p) (hpn : p ∣ n)
    (hq : q.Prime) (hXq : X < q) (hqn : q ∣ n) :
    p = q := by
  by_contra hpq_ne
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr hpq_ne
  have hpq_dvd : p * q ∣ n :=
    hcop.mul_dvd_of_dvd_of_dvd hpn hqn
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hn).1
  have hpq_le_n : p * q ≤ n := Nat.le_of_dvd hn_pos hpq_dvd
  have hn_le_N : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hpq_le_N : p * q ≤ N := hpq_le_n.trans hn_le_N
  have hXsq_lt_pq : X ^ 2 < p * q := by
    simpa [pow_two] using Nat.mul_lt_mul_of_lt_of_lt hXp hXq
  have hN_lt_pq : N < p * q := hN.trans hXsq_lt_pq
  exact not_lt_of_ge hpq_le_N hN_lt_pq

/-- In the Harper range `N < X^2`, each rough summand has a unique visible
large-prime coordinate. -/
theorem existsUnique_largePrimeInterval_of_not_isXSmooth
    {X N n : ℕ}
    (hN : N < X ^ 2)
    (hn : n ∈ Finset.Icc 1 N) (hrough : ¬ IsXSmooth X n) :
    ∃! p, p ∈ largePrimeInterval X N ∧ p ∣ n := by
  rcases exists_largePrimeInterval_of_not_isXSmooth hn hrough with
    ⟨p, hp_mem, hpn⟩
  refine ⟨p, ⟨hp_mem, hpn⟩, ?_⟩
  intro q hq_data
  rcases hq_data with ⟨hq_mem, hqn⟩
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp_mem with
    ⟨hp_prime, hXp, _⟩
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := q)).mp hq_mem with
    ⟨hq_prime, hXq, _⟩
  exact
    (large_prime_unique_of_lt_square
      (X := X) (N := N) (n := n) (p := p) (q := q) hN hn
      hp_prime hXp hpn hq_prime hXq hqn).symm

/-- Numbers below `X` are automatically `X`-smooth. -/
theorem isXSmooth_of_lt
    {X m : ℕ} (hmX : m < X) :
    IsXSmooth X m := by
  intro q hq
  exact (Nat.le_of_mem_primeFactors hq).trans hmX.le

/-- In the Harper range `N < X^2`, quotients by primes above `X` are below
`X`. -/
theorem quotient_lt_X_of_le_div_large
    {X N p m : ℕ}
    (hN : N < X ^ 2) (hXp : X < p) (hm_le : m ≤ N / p) :
    m < X := by
  have hXpos : 0 < X := by
    by_contra hXnot
    have hXzero : X = 0 := Nat.eq_zero_of_not_pos hXnot
    simp [hXzero] at hN
  by_contra hm_not
  have hXm : X ≤ m := le_of_not_gt hm_not
  have hm_pos : 0 < m := lt_of_lt_of_le hXpos hXm
  have hmp_le_N : m * p ≤ N := Nat.mul_le_of_le_div p m N hm_le
  have hXsq_lt_mp : X ^ 2 < m * p := by
    simpa [pow_two] using Nat.mul_lt_mul_of_le_of_lt hXm hXp hm_pos
  exact not_lt_of_ge hmp_le_N (hN.trans hXsq_lt_mp)

/-- A quotient `m <= N/p` is not divisible by the large prime `p` in the
Harper range. -/
theorem not_dvd_of_le_div_large
    {X N p m : ℕ}
    (hN : N < X ^ 2) (hXp : X < p) (hm_pos : 0 < m)
    (hm_le : m ≤ N / p) :
    ¬ p ∣ m := by
  have hmX : m < X := quotient_lt_X_of_le_div_large hN hXp hm_le
  exact Nat.not_dvd_of_pos_of_lt hm_pos (hmX.trans hXp)

/-- A quotient `m <= N/p` is `X`-smooth in the Harper range. -/
theorem isXSmooth_of_le_div_large
    {X N p m : ℕ}
    (hN : N < X ^ 2) (hXp : X < p) (hm_le : m ≤ N / p) :
    IsXSmooth X m :=
  isXSmooth_of_lt (quotient_lt_X_of_le_div_large hN hXp hm_le)

/-- Harper's large-prime contribution, before conditioning on the large prime
signs. -/
noncomputable def largePrimeContribution
    (omega : Omega) (X N : ℕ) : ℝ :=
  ∑ p ∈ largePrimeInterval X N, eps omega p * S omega (N / p)

/-- In the Harper range, the large-prime contribution expands as a finite sum
over products `p*m`.

The key point is that `m <= N/p` implies `m < X < p`, so `p` does not divide
`m` and the focused prime-step multiplicativity lemma applies.
-/
theorem largePrimeContribution_eq_pairSum
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2) :
    largePrimeContribution omega X N =
      ∑ p ∈ largePrimeInterval X N,
        ∑ m ∈ Finset.Icc 1 (N / p), f omega (p * m) := by
  unfold largePrimeContribution S
  refine Finset.sum_congr rfl fun p hp_mem => ?_
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp_mem with
    ⟨hp_prime, hXp, _⟩
  calc
    eps omega p * (∑ m ∈ Finset.Icc 1 (N / p), f omega m)
        = ∑ m ∈ Finset.Icc 1 (N / p), eps omega p * f omega m := by
          rw [Finset.mul_sum]
    _ = ∑ m ∈ Finset.Icc 1 (N / p), f omega (p * m) := by
          refine Finset.sum_congr rfl fun m hm_mem => ?_
          have hm_pos : 0 < m :=
            lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hm_mem).1
          have hm_le : m ≤ N / p := (Finset.mem_Icc.mp hm_mem).2
          have hpm : ¬ p ∣ m :=
            not_dvd_of_le_div_large hN hXp hm_pos hm_le
          exact (f_prime_mul_of_not_dvd omega hp_prime hm_pos hpm).symm

/-- Multiplication maps every large-prime pair to a rough summand. -/
theorem largePrimePair_product_mem_roughSet
    {X N : ℕ}
    {a : Sigma fun _p : ℕ => ℕ}
    (ha : a ∈ largePrimePairs X N) :
    a.1 * a.2 ∈ roughSet X N := by
  rcases (mem_largePrimePairs (X := X) (N := N) (a := a)).mp ha with
    ⟨hp_mem, hm_mem⟩
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := a.1)).mp hp_mem with
    ⟨hp_prime, hXp, _⟩
  have hm_pos : 0 < a.2 :=
    lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hm_mem).1
  have hm_le : a.2 ≤ N / a.1 := (Finset.mem_Icc.mp hm_mem).2
  have hmul_pos : 0 < a.1 * a.2 :=
    Nat.mul_pos hp_prime.pos hm_pos
  have hmul_le_N : a.1 * a.2 ≤ N := by
    simpa [mul_comm] using Nat.mul_le_of_le_div a.1 a.2 N hm_le
  have hnot_smooth : ¬ IsXSmooth X (a.1 * a.2) := by
    rw [not_isXSmooth_iff_exists_large_prime_of_ne_zero X (a.1 * a.2)
      hmul_pos.ne']
    exact ⟨a.1, hp_prime, hXp, dvd_mul_right a.1 a.2⟩
  rw [mem_roughSet]
  exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hmul_pos, hmul_le_N⟩, hnot_smooth⟩

/-- In the Harper range, multiplication is injective on the large-prime pair
index set.

This is the injectivity half of the eventual `largePrimePairs`/`roughSet`
bijection.
-/
theorem largePrimePair_product_injective
    {X N : ℕ} (hN : N < X ^ 2)
    {a b : Sigma fun _p : ℕ => ℕ}
    (ha : a ∈ largePrimePairs X N)
    (hb : b ∈ largePrimePairs X N)
    (hab : a.1 * a.2 = b.1 * b.2) :
    a = b := by
  rcases a with ⟨p, m⟩
  rcases b with ⟨q, k⟩
  simp only at ha hb hab ⊢
  rcases (mem_largePrimePairs (X := X) (N := N)
      (a := (⟨p, m⟩ : Sigma fun _p : ℕ => ℕ))).mp ha with
    ⟨hp_mem, hm_mem⟩
  rcases (mem_largePrimePairs (X := X) (N := N)
      (a := (⟨q, k⟩ : Sigma fun _p : ℕ => ℕ))).mp hb with
    ⟨hq_mem, hk_mem⟩
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp_mem with
    ⟨hp_prime, hXp, _⟩
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := q)).mp hq_mem with
    ⟨hq_prime, hXq, _⟩
  have hn_mem : p * m ∈ Finset.Icc 1 N :=
    (mem_roughSet.mp
      (largePrimePair_product_mem_roughSet
        (a := (⟨p, m⟩ : Sigma fun _p : ℕ => ℕ)) ha)).1
  have hpq : p = q := by
    exact large_prime_unique_of_lt_square
      (X := X) (N := N) (n := p * m) (p := p) (q := q)
      hN hn_mem
      hp_prime hXp (dvd_mul_right p m)
      hq_prime hXq ⟨k, hab⟩
  subst q
  have hmk : m = k := Nat.mul_left_cancel hp_prime.pos hab
  subst k
  rfl

/-- Every rough summand comes from at least one large-prime pair. Combined
with `largePrimePair_product_injective`, this gives the finite bijection needed
to reindex the rough sum. -/
theorem exists_largePrimePair_product_eq_of_mem_roughSet
    {X N n : ℕ}
    (hn : n ∈ roughSet X N) :
    ∃ a ∈ largePrimePairs X N, a.1 * a.2 = n := by
  rcases (mem_roughSet.mp hn) with ⟨hnIcc, hrough⟩
  rcases exists_largePrimeInterval_of_not_isXSmooth hnIcc hrough with
    ⟨p, hp_mem, hpn⟩
  let m : ℕ := n / p
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hnIcc).1
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp_mem with
    ⟨hp_prime, _, _⟩
  have hp_le_n : p ≤ n := Nat.le_of_dvd hn_pos hpn
  have hm_pos : 0 < m := Nat.div_pos hp_le_n hp_prime.pos
  have hm_le : m ≤ N / p :=
    Nat.div_le_div_right (Finset.mem_Icc.mp hnIcc).2
  refine
    ⟨⟨p, m⟩,
      (mem_largePrimePairs (X := X) (N := N)
        (a := (⟨p, m⟩ : Sigma fun _p : ℕ => ℕ))).mpr
        ⟨hp_mem, Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hm_pos, hm_le⟩⟩,
      ?_⟩
  dsimp [m]
  simpa [mul_comm] using (Nat.div_mul_cancel hpn)

/-- The pair-indexed product sum is exactly the rough sum. -/
theorem largePrimePair_sum_eq_roughSum
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2) :
    (∑ a ∈ largePrimePairs X N, f omega (a.1 * a.2)) =
      roughSum omega X N := by
  rw [roughSum_eq_sum_roughSet]
  exact Finset.sum_bij
    (fun a _ha => a.1 * a.2)
    (fun a ha => largePrimePair_product_mem_roughSet ha)
    (fun a₁ ha₁ a₂ ha₂ hEq =>
      largePrimePair_product_injective hN ha₁ ha₂ hEq)
    (fun n hn => by
      rcases exists_largePrimePair_product_eq_of_mem_roughSet hn with
        ⟨a, ha, hprod⟩
      exact ⟨a, ha, hprod⟩)
    (fun _ _ => rfl)

/-- Harper's deterministic large-prime decomposition for the complete model,
in the range where each summand has at most one prime factor above `X`.

The analytic proof will condition on primes up to `X`; this theorem isolates
the fresh large-prime process as a finite sum over `p > X`.
-/
theorem roughSum_eq_largePrimeContribution
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2) :
    roughSum omega X N = largePrimeContribution omega X N := by
  rw [← largePrimePair_sum_eq_roughSum omega hN]
  rw [largePrimeContribution_eq_pairSum omega hN]
  rw [largePrimePairs, Finset.sum_sigma']

/-- Complete-model Harper decomposition:

`S(N)` is the `X`-smooth remainder plus the contribution from the unique prime
factor above `X`, valid whenever `N < X^2`.
-/
theorem S_eq_smoothSum_add_largePrimeContribution
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2) :
    S omega N = smoothSum omega X N + largePrimeContribution omega X N := by
  rw [S_eq_smoothSum_add_roughSum omega X N,
    roughSum_eq_largePrimeContribution omega hN]

end Problem1144
end Erdos
