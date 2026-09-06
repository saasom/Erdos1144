import Erdos.Problem1144.HarperDecomposition
import Mathlib.Algebra.BigOperators.Field

open MeasureTheory
open scoped BigOperators

namespace Erdos
namespace Problem1144

/-- Paper-normalized partial sums, without the `N + 1` shift used in the
final Lean statement. This is the normalization that naturally appears in
Harper-style block decompositions. -/
noncomputable def cutoffNormSum (omega : Omega) (N : ℕ) : ℝ :=
  S omega N / Real.sqrt (N : ℝ)

/-- The shifted final normalization is the unshifted paper normalization at
the successor cutoff. -/
theorem normSum_eq_cutoffNormSum_succ (omega : Omega) (N : ℕ) :
    normSum omega N = cutoffNormSum omega (N + 1) := by
  rfl

/-- Normalized `X`-smooth remainder. -/
noncomputable def smoothProcess (omega : Omega) (X N : ℕ) : ℝ :=
  smoothSum omega X N / Real.sqrt (N : ℝ)

/-- Square-product pair count restricted to the `X`-smooth summands up to `N`. -/
noncomputable def smoothPairCount (X N : ℕ) : ℝ :=
  by
    classical
    exact
      ∑ a ∈ (Finset.Icc 1 N).filter (fun n => IsXSmooth X n),
        ∑ b ∈ (Finset.Icc 1 N).filter (fun n => IsXSmooth X n),
          squareIndicator (a * b)

/-- The finite set of smooth pairs whose product is a square, represented as
a sigma finset so its cardinal unfolds directly to an iterated sum. -/
noncomputable def smoothSquarePairSet (X N : ℕ) :
    Finset (Sigma fun _a : ℕ => ℕ) :=
  by
    classical
    let S := (Finset.Icc 1 N).filter (fun n => IsXSmooth X n)
    exact S.sigma fun a => S.filter fun b => IsSquare (a * b)

/-- Finite squarefree `X`-smooth kernels up to a cutoff. These are the `d`
in the elementary parametrisation `a = d u^2`, `b = d v^2`. -/
noncomputable def smoothSquareKernelSet (X B : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 B).filter fun d => Squarefree d ∧ IsXSmooth X d

/-- Finite reciprocal square-kernel weight. This is the truncated version of
`prod_{p <= X} (1 + 1 / p)` that is enough for any fixed finite block. -/
noncomputable def smoothSquareKernelWeight (X B : ℕ) : ℝ :=
  ∑ d ∈ smoothSquareKernelSet X B, (d : ℝ)⁻¹

/-- Overcounting triples for smooth square pairs:
`a = u^2 d`, `b = v^2 d`, with the common squarefree kernel `d`. -/
noncomputable def smoothKernelTripleSet (X N : ℕ) :
    Finset (Sigma fun _d : ℕ => ℕ × ℕ) :=
  by
    classical
    exact
      (smoothSquareKernelSet X N).sigma fun d =>
        (Finset.Icc 1 (Nat.sqrt (N / d))).product
          (Finset.Icc 1 (Nat.sqrt (N / d)))

/-- The pair associated to a square-kernel triple. -/
def smoothKernelTripleToPair (t : Sigma fun _d : ℕ => ℕ × ℕ) :
    Sigma fun _a : ℕ => ℕ :=
  ⟨t.2.1 ^ 2 * t.1, t.2.2 ^ 2 * t.1⟩

/-- Smooth square-pair counts are nonnegative. -/
theorem smoothPairCount_nonneg (X N : ℕ) :
    0 ≤ smoothPairCount X N := by
  classical
  unfold smoothPairCount
  refine Finset.sum_nonneg fun a _ha => ?_
  exact Finset.sum_nonneg fun b _hb => squareIndicator_nonneg (a * b)

/-- The smooth pair count is the cardinality of the corresponding square-pair
set. -/
theorem smoothPairCount_eq_card_smoothSquarePairSet (X N : ℕ) :
    smoothPairCount X N = (smoothSquarePairSet X N).card := by
  classical
  unfold smoothPairCount smoothSquarePairSet squareIndicator
  simp

/-- The finite square-kernel weight is nonnegative. -/
theorem smoothSquareKernelWeight_nonneg (X B : ℕ) :
    0 ≤ smoothSquareKernelWeight X B := by
  classical
  unfold smoothSquareKernelWeight smoothSquareKernelSet
  refine Finset.sum_nonneg fun d _hd => ?_
  exact inv_nonneg.mpr (by positivity : 0 ≤ (d : ℝ))

/-- In a decomposition `n = u^2 d` with `d` squarefree, the odd prime
coordinates of `n` are exactly the prime divisors of `d`. -/
theorem odd_factorization_sq_mul_squarefree_iff_dvd
    {n d u p : ℕ} (hu : u ≠ 0) (hd : Squarefree d)
    (h : u ^ 2 * d = n) (hp : p.Prime) :
    Odd (n.factorization p) ↔ p ∣ d := by
  have hd_ne : d ≠ 0 := hd.ne_zero
  have hfac :
      n.factorization p = 2 * u.factorization p + d.factorization p := by
    rw [← h]
    have hmul :=
      congrArg (fun q : ℕ →₀ ℕ => q p)
        (Nat.factorization_mul (pow_ne_zero 2 hu) hd_ne)
    simpa [Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
      two_mul] using hmul
  constructor
  · intro hodd
    by_contra hnot
    have hd0 : d.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnot
    rw [hfac, hd0, add_zero] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨u.factorization p, by ring⟩
  · intro hpd
    have hd1 : d.factorization p = 1 :=
      Nat.factorization_eq_one_of_squarefree hd hp hpd
    rw [hfac, hd1]
    exact ⟨u.factorization p, by ring⟩

/-- If `a*b` is a square, then the squarefree parts in decompositions
`a = u^2 d_a` and `b = v^2 d_b` are equal. -/
theorem squarefree_parts_eq_of_mul_square
    {a b da db ua ub : ℕ}
    (hua : ua ≠ 0) (hub : ub ≠ 0)
    (hda : Squarefree da) (hdb : Squarefree db)
    (ha : ua ^ 2 * da = a) (hb : ub ^ 2 * db = b)
    (hsq : IsSquare (a * b)) :
    da = db := by
  have ha_ne : a ≠ 0 := by
    rw [← ha]
    exact mul_ne_zero (pow_ne_zero 2 hua) hda.ne_zero
  have hb_ne : b ≠ 0 := by
    rw [← hb]
    exact mul_ne_zero (pow_ne_zero 2 hub) hdb.ne_zero
  rw [Nat.Squarefree.ext_iff hda hdb]
  intro p hp
  have hfac_mul :
      (a * b).factorization p =
        a.factorization p + b.factorization p := by
    have h :=
      congrArg (fun q : ℕ →₀ ℕ => q p)
        (Nat.factorization_mul ha_ne hb_ne)
    simpa [Finsupp.add_apply] using h
  have heven_sum : Even (a.factorization p + b.factorization p) := by
    have heven := factorization_even_of_isSquare
      (mul_ne_zero ha_ne hb_ne) hsq p
    simpa [hfac_mul] using heven
  have hodd_iff : Odd (a.factorization p) ↔ Odd (b.factorization p) :=
    Nat.even_add'.mp heven_sum
  constructor
  · intro hpda
    have haodd : Odd (a.factorization p) :=
      (odd_factorization_sq_mul_squarefree_iff_dvd hua hda ha hp).mpr hpda
    exact
      (odd_factorization_sq_mul_squarefree_iff_dvd hub hdb hb hp).mp
        (hodd_iff.mp haodd)
  · intro hpdb
    have hbodd : Odd (b.factorization p) :=
      (odd_factorization_sq_mul_squarefree_iff_dvd hub hdb hb hp).mpr hpdb
    exact
      (odd_factorization_sq_mul_squarefree_iff_dvd hua hda ha hp).mp
        (hodd_iff.mpr hbodd)

/-- Square pairs have the standard common-squarefree-kernel parametrisation:
`a = u^2 d`, `b = v^2 d`. -/
theorem exists_common_squarefree_kernel_of_mul_square
    {a b : ℕ} (ha_pos : 0 < a) (hb_pos : 0 < b)
    (hsq : IsSquare (a * b)) :
    ∃ d u v : ℕ, Squarefree d ∧ 0 < u ∧ 0 < v ∧
      u ^ 2 * d = a ∧ v ^ 2 * d = b := by
  rcases Nat.sq_mul_squarefree_of_pos ha_pos with
    ⟨da, ua, hda_pos, hua_pos, ha, hda⟩
  rcases Nat.sq_mul_squarefree_of_pos hb_pos with
    ⟨db, ub, _hdb_pos, hub_pos, hb, hdb⟩
  have hdeq : da = db :=
    squarefree_parts_eq_of_mul_square
      hua_pos.ne' hub_pos.ne' hda hdb ha hb hsq
  exact ⟨db, ua, ub, hdb, hua_pos, hub_pos, by simpa [hdeq] using ha, hb⟩

/-- Smooth square pairs have the same parametrisation with an `X`-smooth
squarefree kernel bounded by the original cutoff. -/
theorem exists_smoothSquareKernel_param_of_smooth_pair_square
    {X N a b : ℕ}
    (haIcc : a ∈ Finset.Icc 1 N) (ha_smooth : IsXSmooth X a)
    (hbIcc : b ∈ Finset.Icc 1 N) (_hb_smooth : IsXSmooth X b)
    (hsq : IsSquare (a * b)) :
    ∃ d ∈ smoothSquareKernelSet X N, ∃ u v : ℕ,
      u ^ 2 * d = a ∧ v ^ 2 * d = b := by
  classical
  have ha_pos : 0 < a := (Finset.mem_Icc.mp haIcc).1
  have ha_le : a ≤ N := (Finset.mem_Icc.mp haIcc).2
  have hb_pos : 0 < b := (Finset.mem_Icc.mp hbIcc).1
  rcases exists_common_squarefree_kernel_of_mul_square
      ha_pos hb_pos hsq with
    ⟨d, u, v, hd_sqfree, _hu_pos, _hv_pos, hdu, hdv⟩
  have hd_dvd_a : d ∣ a := ⟨u ^ 2, by rw [mul_comm, hdu]⟩
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_sqfree.ne_zero
  have hd_le_N : d ≤ N :=
    (Nat.le_of_dvd ha_pos hd_dvd_a).trans ha_le
  have hd_smooth : IsXSmooth X d := by
    intro p hp_mem
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp_mem
    have hpa : p ∣ a := hpd.trans hd_dvd_a
    have hp_mem_a : p ∈ a.primeFactors :=
      hp_prime.mem_primeFactors hpa ha_pos.ne'
    exact ha_smooth p hp_mem_a
  refine ⟨d, ?_, u, v, hdu, hdv⟩
  unfold smoothSquareKernelSet
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hd_pos, hd_le_N⟩, hd_sqfree, hd_smooth⟩

/-- Every smooth square pair is hit by the square-kernel triple map. -/
theorem smoothKernelTripleToPair_surjOn_smoothSquarePairSet (X N : ℕ) :
    Set.SurjOn smoothKernelTripleToPair
      (smoothKernelTripleSet X N : Set (Sigma fun _d : ℕ => ℕ × ℕ))
      (smoothSquarePairSet X N : Set (Sigma fun _a : ℕ => ℕ)) := by
  classical
  intro y hy
  rcases y with ⟨a, b⟩
  unfold smoothSquarePairSet at hy
  simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_filter] at hy
  rcases hy with ⟨haS, hbS, hsq⟩
  rcases haS with ⟨haIcc, ha_smooth⟩
  rcases hbS with ⟨hbIcc, hb_smooth⟩
  rcases exists_smoothSquareKernel_param_of_smooth_pair_square
      haIcc ha_smooth hbIcc hb_smooth hsq with
    ⟨d, hdKernel, u, v, hdu, hdv⟩
  have ha_le : a ≤ N := (Finset.mem_Icc.mp haIcc).2
  have hb_le : b ≤ N := (Finset.mem_Icc.mp hbIcc).2
  have hd_pos : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hdKernel).1).1
  have hu2_le_div : u ^ 2 ≤ N / d := by
    rw [Nat.le_div_iff_mul_le hd_pos]
    exact hdu ▸ ha_le
  have hv2_le_div : v ^ 2 ≤ N / d := by
    rw [Nat.le_div_iff_mul_le hd_pos]
    exact hdv ▸ hb_le
  have hu_mem : u ∈ Finset.Icc 1 (Nat.sqrt (N / d)) := by
    rw [Finset.mem_Icc]
    constructor
    · have hu_pos : 0 < u := by
        by_contra hu0
        have : a = 0 := by
          rw [← hdu, Nat.eq_zero_of_not_pos hu0]
          simp
        have ha_pos : 0 < a :=
          lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp haIcc).1
        exact (ne_of_gt ha_pos) this
      exact Nat.succ_le_of_lt hu_pos
    · exact Nat.le_sqrt'.mpr hu2_le_div
  have hv_mem : v ∈ Finset.Icc 1 (Nat.sqrt (N / d)) := by
    rw [Finset.mem_Icc]
    constructor
    · have hv_pos : 0 < v := by
        by_contra hv0
        have : b = 0 := by
          rw [← hdv, Nat.eq_zero_of_not_pos hv0]
          simp
        have hb_pos : 0 < b :=
          lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hbIcc).1
        exact (ne_of_gt hb_pos) this
      exact Nat.succ_le_of_lt hv_pos
    · exact Nat.le_sqrt'.mpr hv2_le_div
  refine ⟨⟨d, (u, v)⟩, ?_, ?_⟩
  · unfold smoothKernelTripleSet
    simp only [Finset.mem_coe, Finset.mem_sigma]
    exact ⟨hdKernel, Finset.mem_product.mpr ⟨hu_mem, hv_mem⟩⟩
  · ext <;> simp [smoothKernelTripleToPair, hdu, hdv]

/-- The smooth square-pair count is bounded by the number of square-kernel
triples. -/
theorem smoothPairCount_le_card_smoothKernelTripleSet (X N : ℕ) :
    smoothPairCount X N ≤ (smoothKernelTripleSet X N).card := by
  rw [smoothPairCount_eq_card_smoothSquarePairSet]
  exact_mod_cast
    Finset.card_le_card_of_surjOn smoothKernelTripleToPair
      (smoothKernelTripleToPair_surjOn_smoothSquarePairSet X N)

/-- The overcounting triple set has size at most the reciprocal square-kernel
weight times `N`. -/
theorem card_smoothKernelTripleSet_le_mul_smoothSquareKernelWeight
    (X N : ℕ) :
    ((smoothKernelTripleSet X N).card : ℝ) ≤
      (N : ℝ) * smoothSquareKernelWeight X N := by
  classical
  unfold smoothKernelTripleSet smoothSquareKernelWeight
  rw [Finset.card_sigma]
  calc
    ((∑ x ∈ smoothSquareKernelSet X N,
        ((Finset.Icc 1 (N / x).sqrt).product
          (Finset.Icc 1 (N / x).sqrt)).card : ℕ) : ℝ)
        =
        ∑ x ∈ smoothSquareKernelSet X N,
          (((Finset.Icc 1 (N / x).sqrt).product
            (Finset.Icc 1 (N / x).sqrt)).card : ℝ) := by
          simp
    _ ≤
        ∑ x ∈ smoothSquareKernelSet X N,
          (N : ℝ) / (x : ℝ) := by
          refine Finset.sum_le_sum fun x hx => ?_
          calc
            (((Finset.Icc 1 (N / x).sqrt).product
              (Finset.Icc 1 (N / x).sqrt)).card : ℝ)
                =
                ((Nat.sqrt (N / x)) ^ 2 : ℕ) := by
                  simp [Finset.card_product, pow_two]
            _ ≤ ((N / x : ℕ) : ℝ) := by
                  exact_mod_cast Nat.sqrt_le' (N / x)
            _ ≤ (N : ℝ) / (x : ℝ) := by
                  exact Nat.cast_div_le
    _ =
        (N : ℝ) *
          ∑ x ∈ smoothSquareKernelSet X N, (x : ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [div_eq_mul_inv]

/-- Elementary smooth square-pair estimate in finite-kernel form. -/
theorem smoothPairCount_le_mul_smoothSquareKernelWeight
    (X N : ℕ) :
    smoothPairCount X N ≤ (N : ℝ) * smoothSquareKernelWeight X N :=
  (smoothPairCount_le_card_smoothKernelTripleSet X N).trans
    (card_smoothKernelTripleSet_le_mul_smoothSquareKernelWeight X N)

/-- Normalized large-prime contribution. -/
noncomputable def largePrimeProcess (omega : Omega) (X N : ℕ) : ℝ :=
  largePrimeContribution omega X N / Real.sqrt (N : ℝ)

/-- The coefficient of the fresh sign `eps p` in the normalized large-prime
process. After conditioning on coordinates up to `X`, these coefficients are
fixed for `p > X`. -/
noncomputable def largePrimeCoeff
    (omega : Omega) (_X N p : ℕ) : ℝ :=
  S omega (N / p) / Real.sqrt (N : ℝ)

/-- Conditional variance proxy for the normalized large-prime process. -/
noncomputable def largePrimeVariance
    (omega : Omega) (X N : ℕ) : ℝ :=
  ∑ p ∈ largePrimeInterval X N, (largePrimeCoeff omega X N p) ^ 2

/-- Conditional covariance proxy for two normalized large-prime processes. -/
noncomputable def largePrimeCovariance
    (omega : Omega) (X M N : ℕ) : ℝ :=
  ∑ p ∈ largePrimeInterval X M ∩ largePrimeInterval X N,
    largePrimeCoeff omega X M p * largePrimeCoeff omega X N p

/-- The unshifted normalized partial sum splits into smooth and large-prime
processes in the Harper range. -/
theorem cutoffNormSum_eq_smoothProcess_add_largePrimeProcess
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2) :
    cutoffNormSum omega N =
      smoothProcess omega X N + largePrimeProcess omega X N := by
  unfold cutoffNormSum smoothProcess largePrimeProcess
  rw [S_eq_smoothSum_add_largePrimeContribution omega hN]
  ring

/-- The large-prime process as a finite signed sum with explicit coefficients. -/
theorem largePrimeProcess_eq_sum_coeff
    (omega : Omega) (X N : ℕ) :
    largePrimeProcess omega X N =
      ∑ p ∈ largePrimeInterval X N,
        eps omega p * largePrimeCoeff omega X N p := by
  unfold largePrimeProcess largePrimeContribution largePrimeCoeff
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun p _hp => ?_
  ring

/-- The covariance proxy agrees with the variance proxy on the diagonal. -/
theorem largePrimeCovariance_self
    (omega : Omega) (X N : ℕ) :
    largePrimeCovariance omega X N N =
      largePrimeVariance omega X N := by
  unfold largePrimeCovariance largePrimeVariance
  simp [pow_two]

/-- The variance proxy is nonnegative. -/
theorem largePrimeVariance_nonneg
    (omega : Omega) (X N : ℕ) :
    0 ≤ largePrimeVariance omega X N := by
  unfold largePrimeVariance
  exact Finset.sum_nonneg fun p _hp => sq_nonneg _

/-- Coordinate signs have absolute value one. -/
@[simp] theorem abs_eps (omega : Omega) (p : ℕ) :
    |eps omega p| = 1 := by
  unfold eps
  by_cases h : omega p <;> simp [h]

/-- If every summand up to `N` is `X`-smooth, the smooth sum is the full
summatory function. -/
theorem smoothSum_eq_S_of_forall_smooth
    (omega : Omega) {X N : ℕ}
    (h : ∀ n ∈ Finset.Icc 1 N, IsXSmooth X n) :
    smoothSum omega X N = S omega N := by
  classical
  unfold smoothSum S
  rw [Finset.filter_true_of_mem h]

/-- For a visible large prime `p` in the Harper range, the quotient cutoff
`N / p` is below `X`. -/
theorem quotient_cutoff_lt_X_of_largePrimeInterval
    {X N p : ℕ} (hN : N < X ^ 2)
    (hp : p ∈ largePrimeInterval X N) :
    N / p < X := by
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp with
    ⟨_hp_prime, hXp, _hpN⟩
  exact quotient_lt_X_of_le_div_large hN hXp le_rfl

/-- A two-scale version of the quotient localization.  If the endpoint lies
below `X * Y`, then every coefficient attached to a prime above `X` has cutoff
strictly below `Y`.

In the Harper cloud one takes `N < X^(4/3)` and `Y = X^(1/3)`.  This records
the useful fact that the fresh-prime coefficient vector only sees the small
prime coordinates, leaving the whole middle range `(Y, X]` as independent
screen randomness. -/
theorem quotient_cutoff_lt_of_lt_mul_of_largePrimeInterval
    {X Y N p : ℕ} (hN : N < X * Y)
    (hp : p ∈ largePrimeInterval X N) :
    N / p < Y := by
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp with
    ⟨_hp_prime, hXp, _hpN⟩
  have hYpos : 0 < Y := by
    by_contra hY
    have hYzero : Y = 0 := Nat.eq_zero_of_not_pos hY
    simp [hYzero] at hN
  by_contra hquot
  have hYle : Y ≤ N / p := le_of_not_gt hquot
  have hYp_le : Y * p ≤ N := Nat.mul_le_of_le_div p Y N hYle
  have hXY_lt : X * Y < p * Y := Nat.mul_lt_mul_of_pos_right hXp hYpos
  have hpY_le : p * Y ≤ N := by simpa [Nat.mul_comm] using hYp_le
  omega

/-- Under the two-scale product bound, a fresh coefficient is already the
`Y`-smooth quotient sum.  Thus it is determined by prime signs at most `Y`,
even though the fresh-prime decomposition itself is made at the larger cutoff
`X`. -/
theorem S_div_eq_smoothSum_of_lt_mul_of_largePrimeInterval
    (omega : Omega) {X Y N p : ℕ} (hN : N < X * Y)
    (hp : p ∈ largePrimeInterval X N) :
    S omega (N / p) = smoothSum omega Y (N / p) := by
  have hquot : N / p < Y :=
    quotient_cutoff_lt_of_lt_mul_of_largePrimeInterval hN hp
  exact
    (smoothSum_eq_S_of_forall_smooth
      (omega := omega) (X := Y) (N := N / p) (by
        intro m hm
        exact isXSmooth_of_lt
          ((Finset.mem_Icc.mp hm).2.trans_lt hquot))).symm

/-- The normalized fresh coefficient inherits the same sharper small-prime
localization. -/
theorem largePrimeCoeff_eq_smallerSmoothSum
    (omega : Omega) {X Y N p : ℕ} (hN : N < X * Y)
    (hp : p ∈ largePrimeInterval X N) :
    largePrimeCoeff omega X N p =
      smoothSum omega Y (N / p) / Real.sqrt (N : ℝ) := by
  unfold largePrimeCoeff
  rw [S_div_eq_smoothSum_of_lt_mul_of_largePrimeInterval omega hN hp]

/-- For a visible large prime `p` in the Harper range, every summand in
`S(N / p)` is `X`-smooth. This is the conditioning boundary: the coefficient
of `eps_p` only uses small-prime coordinates. -/
theorem S_div_eq_smoothSum_of_largePrimeInterval
    (omega : Omega) {X N p : ℕ} (hN : N < X ^ 2)
    (hp : p ∈ largePrimeInterval X N) :
    S omega (N / p) = smoothSum omega X (N / p) := by
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp with
    ⟨_hp_prime, hXp, _hpN⟩
  exact
    (smoothSum_eq_S_of_forall_smooth
      (omega := omega) (X := X) (N := N / p) (by
        intro m hm
        exact isXSmooth_of_le_div_large hN hXp (Finset.mem_Icc.mp hm).2)).symm

/-- Large-prime coefficients can be written using only the `X`-smooth quotient
sum in the Harper range. -/
theorem largePrimeCoeff_eq_smoothSum
    (omega : Omega) {X N p : ℕ} (hN : N < X ^ 2)
    (hp : p ∈ largePrimeInterval X N) :
    largePrimeCoeff omega X N p =
      smoothSum omega X (N / p) / Real.sqrt (N : ℝ) := by
  unfold largePrimeCoeff
  rw [S_div_eq_smoothSum_of_largePrimeInterval omega hN hp]

/-- The large-prime process with coefficients written as smooth quotient sums. -/
theorem largePrimeProcess_eq_sum_smoothCoeff
    (omega : Omega) {X N : ℕ} (hN : N < X ^ 2) :
    largePrimeProcess omega X N =
      ∑ p ∈ largePrimeInterval X N,
        eps omega p * (smoothSum omega X (N / p) / Real.sqrt (N : ℝ)) := by
  rw [largePrimeProcess_eq_sum_coeff]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [largePrimeCoeff_eq_smoothSum omega hN hp]

/-- Local prime-step expansion of one large-prime summand.

For a visible large prime `p`, the term `eps_p * S(N/p)` is exactly the sum of
`f(p*m)` over the corresponding quotient range. -/
theorem eps_mul_S_div_eq_sum_prime_mul
    (omega : Omega) {X N p : ℕ} (hN : N < X ^ 2)
    (hp_mem : p ∈ largePrimeInterval X N) :
    eps omega p * S omega (N / p) =
      ∑ m ∈ Finset.Icc 1 (N / p), f omega (p * m) := by
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp_mem with
    ⟨hp_prime, hXp, _hpN⟩
  unfold S
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

/-- Distinct large-prime coordinates cannot both be hidden inside quotient
factors in the Harper range.

If `p` and `q` are distinct primes above `X`, and `m <= N / p`,
`k <= N / q`, then `p * m * (q * k)` is not a square. This is the finite
arithmetic obstruction that kills cross terms in the large-prime process
second moment. -/
theorem not_isSquare_largePrime_cross
    {X N p q m k : ℕ}
    (hN : N < X ^ 2)
    (hp_mem : p ∈ largePrimeInterval X N)
    (hq_mem : q ∈ largePrimeInterval X N)
    (hpq : p ≠ q)
    (hm_mem : m ∈ Finset.Icc 1 (N / p))
    (hk_mem : k ∈ Finset.Icc 1 (N / q)) :
    ¬ IsSquare (p * m * (q * k)) := by
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp_mem with
    ⟨hp_prime, hXp, _hpN⟩
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := q)).mp hq_mem with
    ⟨hq_prime, hXq, _hqN⟩
  have hm_pos : 0 < m :=
    lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hm_mem).1
  have hk_pos : 0 < k :=
    lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hk_mem).1
  have hm_le : m ≤ N / p := (Finset.mem_Icc.mp hm_mem).2
  have hk_le : k ≤ N / q := (Finset.mem_Icc.mp hk_mem).2
  have hpm : ¬ p ∣ m :=
    not_dvd_of_le_div_large hN hXp hm_pos hm_le
  have hk_lt_X : k < X :=
    quotient_lt_X_of_le_div_large hN hXq hk_le
  have hpk : ¬ p ∣ k :=
    Nat.not_dvd_of_pos_of_lt hk_pos (hk_lt_X.trans hXp)
  have hpq_dvd_not : ¬ p ∣ q := by
    intro hdiv
    have hqp : q = p := (hq_prime.dvd_iff_eq hp_prime.ne_one).mp hdiv
    exact hpq hqp.symm
  intro hsq
  have hprod_ne : p * m * (q * k) ≠ 0 := by
    exact
      mul_ne_zero
        (mul_ne_zero hp_prime.ne_zero hm_pos.ne')
        (mul_ne_zero hq_prime.ne_zero hk_pos.ne')
  have heven := factorization_even_of_isSquare hprod_ne hsq p
  have hpmfac : m.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpm
  have hpkfac : k.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpk
  have hqpfac : q.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpq_dvd_not
  have hfac : (p * m * (q * k)).factorization p = 1 := by
    rw [Nat.factorization_mul
      (mul_ne_zero hp_prime.ne_zero hm_pos.ne')
      (mul_ne_zero hq_prime.ne_zero hk_pos.ne')]
    rw [Nat.factorization_mul hp_prime.ne_zero hm_pos.ne']
    rw [Nat.factorization_mul hq_prime.ne_zero hk_pos.ne']
    simp [hp_prime.factorization, hpmfac, hpkfac, hqpfac]
  rw [hfac] at heven
  exact Nat.not_even_one heven

/-- Two-cutoff version of `not_isSquare_largePrime_cross`.

This is the arithmetic input for covariance computations. The quotient paired
with `p` may come from cutoff `M`, while the quotient paired with `q` may come
from cutoff `N`. -/
theorem not_isSquare_largePrime_cross_twoCutoffs
    {X M N p q m k : ℕ}
    (hM : M < X ^ 2)
    (hN : N < X ^ 2)
    (hp_mem : p ∈ largePrimeInterval X M)
    (hq_mem : q ∈ largePrimeInterval X N)
    (hpq : p ≠ q)
    (hm_mem : m ∈ Finset.Icc 1 (M / p))
    (hk_mem : k ∈ Finset.Icc 1 (N / q)) :
    ¬ IsSquare (p * m * (q * k)) := by
  rcases (mem_largePrimeInterval (X := X) (N := M) (p := p)).mp hp_mem with
    ⟨hp_prime, hXp, _hpM⟩
  rcases (mem_largePrimeInterval (X := X) (N := N) (p := q)).mp hq_mem with
    ⟨hq_prime, hXq, _hqN⟩
  have hm_pos : 0 < m :=
    lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hm_mem).1
  have hk_pos : 0 < k :=
    lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hk_mem).1
  have hm_le : m ≤ M / p := (Finset.mem_Icc.mp hm_mem).2
  have hk_le : k ≤ N / q := (Finset.mem_Icc.mp hk_mem).2
  have hpm : ¬ p ∣ m :=
    not_dvd_of_le_div_large hM hXp hm_pos hm_le
  have hk_lt_X : k < X :=
    quotient_lt_X_of_le_div_large hN hXq hk_le
  have hpk : ¬ p ∣ k :=
    Nat.not_dvd_of_pos_of_lt hk_pos (hk_lt_X.trans hXp)
  have hpq_dvd_not : ¬ p ∣ q := by
    intro hdiv
    have hqp : q = p := (hq_prime.dvd_iff_eq hp_prime.ne_one).mp hdiv
    exact hpq hqp.symm
  intro hsq
  have hprod_ne : p * m * (q * k) ≠ 0 := by
    exact
      mul_ne_zero
        (mul_ne_zero hp_prime.ne_zero hm_pos.ne')
        (mul_ne_zero hq_prime.ne_zero hk_pos.ne')
  have heven := factorization_even_of_isSquare hprod_ne hsq p
  have hpmfac : m.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpm
  have hpkfac : k.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpk
  have hqpfac : q.factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hpq_dvd_not
  have hfac : (p * m * (q * k)).factorization p = 1 := by
    rw [Nat.factorization_mul
      (mul_ne_zero hp_prime.ne_zero hm_pos.ne')
      (mul_ne_zero hq_prime.ne_zero hk_pos.ne')]
    rw [Nat.factorization_mul hp_prime.ne_zero hm_pos.ne']
    rw [Nat.factorization_mul hq_prime.ne_zero hk_pos.ne']
    simp [hp_prime.factorization, hpmfac, hpkfac, hqpfac]
  rw [hfac] at heven
  exact Nat.not_even_one heven

/-- Orthogonality kills one expanded cross term coming from two distinct
large-prime coordinates. -/
theorem integral_largePrime_cross_term_eq_zero
    {X N p q m k : ℕ}
    (hN : N < X ^ 2)
    (hp_mem : p ∈ largePrimeInterval X N)
    (hq_mem : q ∈ largePrimeInterval X N)
    (hpq : p ≠ q)
    (hm_mem : m ∈ Finset.Icc 1 (N / p))
    (hk_mem : k ∈ Finset.Icc 1 (N / q)) :
    ∫ omega, f omega (p * m) * f omega (q * k) ∂mu = 0 := by
  let idx : Bool → ℕ := fun b => if b then p * m else q * k
  have hpos : ∀ b, b ∈ (Finset.univ : Finset Bool) → 0 < idx b := by
    intro b _hb
    cases b
    · change 0 < q * k
      rcases (mem_largePrimeInterval (X := X) (N := N) (p := q)).mp hq_mem with
        ⟨hq_prime, _hXq, _hqN⟩
      have hk_pos : 0 < k :=
        lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hk_mem).1
      exact Nat.mul_pos hq_prime.pos hk_pos
    · change 0 < p * m
      rcases (mem_largePrimeInterval (X := X) (N := N) (p := p)).mp hp_mem with
        ⟨hp_prime, _hXp, _hpN⟩
      have hm_pos : 0 < m :=
        lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hm_mem).1
      exact Nat.mul_pos hp_prime.pos hm_pos
  have h := integral_prod_f_indexed
    (I := (Finset.univ : Finset Bool)) (n := idx) hpos
  have hfun :
      (fun omega : Omega => f omega (p * m) * f omega (q * k))
        =
      (fun omega : Omega => ∏ b, f omega (idx b)) := by
    funext omega
    simp [idx]
  have hprod : (∏ b ∈ (Finset.univ : Finset Bool), idx b) = p * m * (q * k) := by
    simp [idx]
  rw [hfun, h, hprod, squareIndicator]
  exact
    if_neg
      (not_isSquare_largePrime_cross hN hp_mem hq_mem hpq hm_mem hk_mem)

/-- Two-cutoff version of the expanded cross-term cancellation. -/
theorem integral_largePrime_cross_term_twoCutoffs_eq_zero
    {X M N p q m k : ℕ}
    (hM : M < X ^ 2)
    (hN : N < X ^ 2)
    (hp_mem : p ∈ largePrimeInterval X M)
    (hq_mem : q ∈ largePrimeInterval X N)
    (hpq : p ≠ q)
    (hm_mem : m ∈ Finset.Icc 1 (M / p))
    (hk_mem : k ∈ Finset.Icc 1 (N / q)) :
    ∫ omega, f omega (p * m) * f omega (q * k) ∂mu = 0 := by
  let idx : Bool → ℕ := fun b => if b then p * m else q * k
  have hpos : ∀ b, b ∈ (Finset.univ : Finset Bool) → 0 < idx b := by
    intro b _hb
    cases b
    · change 0 < q * k
      rcases (mem_largePrimeInterval (X := X) (N := N) (p := q)).mp hq_mem with
        ⟨hq_prime, _hXq, _hqN⟩
      have hk_pos : 0 < k :=
        lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hk_mem).1
      exact Nat.mul_pos hq_prime.pos hk_pos
    · change 0 < p * m
      rcases (mem_largePrimeInterval (X := X) (N := M) (p := p)).mp hp_mem with
        ⟨hp_prime, _hXp, _hpM⟩
      have hm_pos : 0 < m :=
        lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hm_mem).1
      exact Nat.mul_pos hp_prime.pos hm_pos
  have h := integral_prod_f_indexed
    (I := (Finset.univ : Finset Bool)) (n := idx) hpos
  have hfun :
      (fun omega : Omega => f omega (p * m) * f omega (q * k))
        =
      (fun omega : Omega => ∏ b, f omega (idx b)) := by
    funext omega
    simp [idx]
  have hprod : (∏ b ∈ (Finset.univ : Finset Bool), idx b) = p * m * (q * k) := by
    simp [idx]
  rw [hfun, h, hprod, squareIndicator]
  exact
    if_neg
      (not_isSquare_largePrime_cross_twoCutoffs
        hM hN hp_mem hq_mem hpq hm_mem hk_mem)

/-- Products of two model values are integrable. -/
theorem integrable_f_mul_f (a b : ℕ) :
    Integrable (fun omega : Omega => f omega a * f omega b) mu := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact ((measurable_f a).mul (measurable_f b)).aestronglyMeasurable
  · exact ae_of_all _ fun omega => by
      simp [abs_f]

/-- Orthogonality for a product of two model values. -/
theorem integral_f_mul_f_eq_squareIndicator
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ∫ omega, f omega a * f omega b ∂mu =
      squareIndicator (a * b) := by
  let idx : Bool → ℕ := fun t => if t then a else b
  have hpos : ∀ t, t ∈ (Finset.univ : Finset Bool) → 0 < idx t := by
    intro t _ht
    cases t
    · exact hb
    · exact ha
  have h := integral_prod_f_indexed
    (I := (Finset.univ : Finset Bool)) (n := idx) hpos
  have hfun :
      (fun omega : Omega => f omega a * f omega b)
        =
      (fun omega : Omega => ∏ t, f omega (idx t)) := by
    funext omega
    simp [idx]
  have hprod : (∏ t ∈ (Finset.univ : Finset Bool), idx t) = a * b := by
    simp [idx]
  rw [hfun, h, hprod]

/-- Squared summatory functions are integrable. -/
theorem integrable_S_sq (N : ℕ) :
    Integrable (fun omega : Omega => (S omega N) ^ 2) mu := by
  refine
    Integrable.of_bound
      ((measurable_S N).pow_const 2).aestronglyMeasurable
      ((N : ℝ) ^ 2) ?_
  exact ae_of_all _ fun omega => by
    have hS := abs_S_le omega N
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg (S omega N))]
    have hSsq : (S omega N) ^ 2 = |S omega N| ^ 2 := by
      rw [sq_abs]
    rw [hSsq]
    exact pow_le_pow_left₀ (abs_nonneg _) hS 2

/-- Products of two summatory functions are integrable. -/
theorem integrable_S_mul_S (M N : ℕ) :
    Integrable (fun omega : Omega => S omega M * S omega N) mu := by
  refine
    Integrable.of_bound
      ((measurable_S M).mul (measurable_S N)).aestronglyMeasurable
      ((M : ℝ) * (N : ℝ)) ?_
  exact ae_of_all _ fun omega => by
    have hM := abs_S_le omega M
    have hN := abs_S_le omega N
    rw [Real.norm_eq_abs, abs_mul]
    exact
      mul_le_mul hM hN (abs_nonneg _) (by exact_mod_cast Nat.zero_le M)

/-- Smooth-remainder second moment as an explicit finite square-pair count. -/
theorem integral_smoothSum_sq_eq_smoothPairCount (X N : ℕ) :
    ∫ omega, (smoothSum omega X N) ^ 2 ∂mu =
      smoothPairCount X N := by
  classical
  unfold smoothSum smoothPairCount
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro b hb
      have ha_pos : 0 < a := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      have hb_pos : 0 < b := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1
      exact integral_f_mul_f_eq_squareIndicator ha_pos hb_pos
    · intro b _hb
      exact integrable_f_mul_f a b
  · intro a _ha
    exact
      integrable_finset_sum
        ((Finset.Icc 1 N).filter (fun n => IsXSmooth X n))
        fun b _hb => integrable_f_mul_f a b

/-- Squared smooth remainders are integrable. -/
theorem integrable_smoothSum_sq (X N : ℕ) :
    Integrable (fun omega : Omega => (smoothSum omega X N) ^ 2) mu := by
  classical
  unfold smoothSum
  simp_rw [pow_two, Finset.sum_mul_sum]
  exact
    integrable_finset_sum
      ((Finset.Icc 1 N).filter (fun n => IsXSmooth X n))
      fun a _ha =>
        integrable_finset_sum
          ((Finset.Icc 1 N).filter (fun n => IsXSmooth X n))
          fun b _hb => integrable_f_mul_f a b

/-- Squared normalized smooth remainders are integrable. -/
theorem integrable_smoothProcess_sq (X N : ℕ) :
    Integrable (fun omega : Omega => (smoothProcess omega X N) ^ 2) mu := by
  refine
    ((integrable_smoothSum_sq X N).div_const
      ((Real.sqrt (N : ℝ)) ^ 2)).congr ?_
  exact ae_of_all _ fun omega => by
    change
      (smoothSum omega X N) ^ 2 / (Real.sqrt (N : ℝ)) ^ 2 =
        (smoothProcess omega X N) ^ 2
    unfold smoothProcess
    ring

/-- Normalized smooth-remainder second moment as a finite square-pair count. -/
theorem integral_smoothProcess_sq_eq_smoothPairCount_div (X N : ℕ) :
    ∫ omega, (smoothProcess omega X N) ^ 2 ∂mu =
      smoothPairCount X N / (Real.sqrt (N : ℝ)) ^ 2 := by
  calc
    ∫ omega, (smoothProcess omega X N) ^ 2 ∂mu
        =
        ∫ omega,
          (smoothSum omega X N) ^ 2 / (Real.sqrt (N : ℝ)) ^ 2 ∂mu := by
          apply integral_congr_ae
          exact ae_of_all _ fun omega => by
            unfold smoothProcess
            ring
    _ =
        (∫ omega, (smoothSum omega X N) ^ 2 ∂mu) /
          (Real.sqrt (N : ℝ)) ^ 2 := by
          rw [integral_div]
    _ = smoothPairCount X N / (Real.sqrt (N : ℝ)) ^ 2 := by
          rw [integral_smoothSum_sq_eq_smoothPairCount]

/-- One-point lower-tail bound for the normalized smooth remainder, using only
its second moment. -/
theorem measure_smoothProcess_lt_neg_le_second
    {X N : ℕ} {B : ℝ} (hB : 0 < B) :
    mu {omega | smoothProcess omega X N < -B} ≤
      ENNReal.ofReal
        ((smoothPairCount X N / (Real.sqrt (N : ℝ)) ^ 2) / B ^ 2) := by
  let E : Set Omega := {omega | smoothProcess omega X N < -B}
  let T : Set Omega := {omega | B ^ 2 ≤ (smoothProcess omega X N) ^ 2}
  have hsubset : E ⊆ T := by
    intro omega hlt
    have hlt' : smoothProcess omega X N < -B := by
      simpa [E] using hlt
    have hleabs : B ≤ |smoothProcess omega X N| := by
      rw [le_abs]
      right
      linarith
    have hpow : B ^ 2 ≤ |smoothProcess omega X N| ^ 2 :=
      pow_le_pow_left₀ hB.le hleabs 2
    rw [← abs_pow] at hpow
    simpa [T,
      abs_of_nonneg
        (by positivity : 0 ≤ (smoothProcess omega X N) ^ 2)] using hpow
  have hnonneg :
      0 ≤ᵐ[mu] fun omega => (smoothProcess omega X N) ^ 2 :=
    ae_of_all _ fun omega => by positivity
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (μ := mu)
      (f := fun omega => (smoothProcess omega X N) ^ 2)
      hnonneg (integrable_smoothProcess_sq X N) (B ^ 2)
  have hTreal :
      mu.real T ≤
        (smoothPairCount X N / (Real.sqrt (N : ℝ)) ^ 2) / B ^ 2 := by
    have hmul :
        B ^ 2 * mu.real T ≤
          smoothPairCount X N / (Real.sqrt (N : ℝ)) ^ 2 := by
      calc
        B ^ 2 * mu.real T
            ≤ ∫ omega, (smoothProcess omega X N) ^ 2 ∂mu := by
              simpa [T] using hmarkov
        _ = smoothPairCount X N / (Real.sqrt (N : ℝ)) ^ 2 := by
              rw [integral_smoothProcess_sq_eq_smoothPairCount_div]
    rw [le_div_iff₀ (pow_pos hB 2)]
    exact by simpa [mul_comm] using hmul
  have hEreal :
      mu.real E ≤
        (smoothPairCount X N / (Real.sqrt (N : ℝ)) ^ 2) / B ^ 2 :=
    (measureReal_mono hsubset).trans hTreal
  rw [← ofReal_measureReal (μ := mu) (s := E)]
  exact ENNReal.ofReal_le_ofReal hEreal

/-- The square of one unnormalized large-prime summand is the square of its
coefficient sum; the fresh sign disappears. -/
theorem largePrime_summand_sq
    (omega : Omega) (p N : ℕ) :
    (eps omega p * S omega (N / p)) ^ 2 =
      (S omega (N / p)) ^ 2 := by
  calc
    (eps omega p * S omega (N / p)) ^ 2
        = (eps omega p) ^ 2 * (S omega (N / p)) ^ 2 := by ring
    _ = (S omega (N / p)) ^ 2 := by simp

/-- Integral form of `largePrime_summand_sq`. -/
theorem integral_largePrime_summand_sq
    (p N : ℕ) :
    ∫ omega, (eps omega p * S omega (N / p)) ^ 2 ∂mu =
      ∫ omega, (S omega (N / p)) ^ 2 ∂mu := by
  simp_rw [largePrime_summand_sq]

/-- The normalized diagonal summand square is the square of its coefficient. -/
theorem largePrime_coeff_summand_sq
    (omega : Omega) (X N p : ℕ) :
    (eps omega p * largePrimeCoeff omega X N p) ^ 2 =
      (largePrimeCoeff omega X N p) ^ 2 := by
  calc
    (eps omega p * largePrimeCoeff omega X N p) ^ 2
        = (eps omega p) ^ 2 * (largePrimeCoeff omega X N p) ^ 2 := by ring
    _ = (largePrimeCoeff omega X N p) ^ 2 := by simp

/-- Integral form of `largePrime_coeff_summand_sq`. -/
theorem integral_largePrime_coeff_summand_sq
    (X N p : ℕ) :
    ∫ omega, (eps omega p * largePrimeCoeff omega X N p) ^ 2 ∂mu =
      ∫ omega, (largePrimeCoeff omega X N p) ^ 2 ∂mu := by
  simp_rw [largePrime_coeff_summand_sq]

/-- Squared normalized coefficients are just squared quotient sums divided by
the squared normalizing factor. -/
theorem largePrimeCoeff_sq
    (omega : Omega) (X N p : ℕ) :
    (largePrimeCoeff omega X N p) ^ 2 =
      (S omega (N / p)) ^ 2 / (Real.sqrt (N : ℝ)) ^ 2 := by
  unfold largePrimeCoeff
  ring

/-- Product form of the normalized large-prime coefficients for two cutoffs. -/
theorem largePrimeCoeff_mul
    (omega : Omega) (X M N p : ℕ) :
    largePrimeCoeff omega X M p * largePrimeCoeff omega X N p =
      (S omega (M / p) * S omega (N / p)) /
        (Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ)) := by
  unfold largePrimeCoeff
  ring

/-- Squared normalized coefficients are integrable. -/
theorem integrable_largePrimeCoeff_sq (X N p : ℕ) :
    Integrable
      (fun omega : Omega => (largePrimeCoeff omega X N p) ^ 2) mu := by
  refine
    ((integrable_S_sq (N / p)).div_const
      ((Real.sqrt (N : ℝ)) ^ 2)).congr ?_
  exact ae_of_all _ fun omega => by
    change
      (S omega (N / p)) ^ 2 / (Real.sqrt (N : ℝ)) ^ 2 =
        (largePrimeCoeff omega X N p) ^ 2
    rw [largePrimeCoeff_sq]

/-- Products of normalized coefficients for two cutoffs are integrable. -/
theorem integrable_largePrimeCoeff_mul (X M N p : ℕ) :
    Integrable
      (fun omega : Omega =>
        largePrimeCoeff omega X M p * largePrimeCoeff omega X N p) mu := by
  refine
    ((integrable_S_mul_S (M / p) (N / p)).div_const
      (Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ))).congr ?_
  exact ae_of_all _ fun omega => by
    change
      (S omega (M / p) * S omega (N / p)) /
          (Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ)) =
        largePrimeCoeff omega X M p * largePrimeCoeff omega X N p
    rw [largePrimeCoeff_mul]

/-- Products of two unnormalized large-prime summands are integrable. -/
theorem integrable_largePrime_summand_pair (N p q : ℕ) :
    Integrable
      (fun omega : Omega =>
        (eps omega p * S omega (N / p)) *
          (eps omega q * S omega (N / q))) mu := by
  refine Integrable.of_bound ?_ ((N : ℝ) ^ 2) ?_
  · exact
      (((measurable_eps p).mul (measurable_S (N / p))).mul
        ((measurable_eps q).mul (measurable_S (N / q)))).aestronglyMeasurable
  · exact ae_of_all _ fun omega => by
      have hpS := abs_S_le omega (N / p)
      have hqS := abs_S_le omega (N / q)
      have hpN : (((N / p : ℕ) : ℝ)) ≤ (N : ℝ) := by
        exact_mod_cast Nat.div_le_self N p
      have hqN : (((N / q : ℕ) : ℝ)) ≤ (N : ℝ) := by
        exact_mod_cast Nat.div_le_self N q
      have hSp_nonneg : 0 ≤ |S omega (N / p)| := abs_nonneg _
      have hSq_nonneg : 0 ≤ |S omega (N / q)| := abs_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_eps, abs_eps]
      nlinarith

/-- Products of two large-prime summands from possibly different cutoffs are
integrable. -/
theorem integrable_largePrime_summand_pair_twoCutoffs (M N p q : ℕ) :
    Integrable
      (fun omega : Omega =>
        (eps omega p * S omega (M / p)) *
          (eps omega q * S omega (N / q))) mu := by
  refine Integrable.of_bound ?_ ((M : ℝ) * (N : ℝ)) ?_
  · exact
      (((measurable_eps p).mul (measurable_S (M / p))).mul
        ((measurable_eps q).mul (measurable_S (N / q)))).aestronglyMeasurable
  · exact ae_of_all _ fun omega => by
      have hpS := abs_S_le omega (M / p)
      have hqS := abs_S_le omega (N / q)
      have hpM : (((M / p : ℕ) : ℝ)) ≤ (M : ℝ) := by
        exact_mod_cast Nat.div_le_self M p
      have hqN : (((N / q : ℕ) : ℝ)) ≤ (N : ℝ) := by
        exact_mod_cast Nat.div_le_self N q
      have hSp_nonneg : 0 ≤ |S omega (M / p)| := abs_nonneg _
      have hSq_nonneg : 0 ≤ |S omega (N / q)| := abs_nonneg _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_eps, abs_eps]
      nlinarith

/-- Same-prime diagonal identity for two cutoffs. -/
theorem largePrime_summand_samePrime_mul
    (omega : Omega) (M N p : ℕ) :
    (eps omega p * S omega (M / p)) *
        (eps omega p * S omega (N / p)) =
      S omega (M / p) * S omega (N / p) := by
  calc
    (eps omega p * S omega (M / p)) *
        (eps omega p * S omega (N / p))
        = (eps omega p * eps omega p) *
            (S omega (M / p) * S omega (N / p)) := by ring
    _ = S omega (M / p) * S omega (N / p) := by simp

/-- Integral form of the same-prime diagonal identity for two cutoffs. -/
theorem integral_largePrime_summand_samePrime_mul
    (M N p : ℕ) :
    ∫ omega,
        (eps omega p * S omega (M / p)) *
          (eps omega p * S omega (N / p)) ∂mu =
      ∫ omega, S omega (M / p) * S omega (N / p) ∂mu := by
  apply integral_congr_ae
  exact ae_of_all _ fun omega =>
    largePrime_summand_samePrime_mul omega M N p

/-- Orthogonality kills the whole cross term between two distinct large-prime
summands. -/
theorem integral_largePrime_summand_cross_eq_zero
    {X N p q : ℕ}
    (hN : N < X ^ 2)
    (hp_mem : p ∈ largePrimeInterval X N)
    (hq_mem : q ∈ largePrimeInterval X N)
    (hpq : p ≠ q) :
    ∫ omega,
        (eps omega p * S omega (N / p)) *
          (eps omega q * S omega (N / q)) ∂mu = 0 := by
  have hfun :
      (fun omega : Omega =>
        (eps omega p * S omega (N / p)) *
          (eps omega q * S omega (N / q)))
        =
      (fun omega : Omega =>
        (∑ m ∈ Finset.Icc 1 (N / p), f omega (p * m)) *
          (∑ k ∈ Finset.Icc 1 (N / q), f omega (q * k))) := by
    funext omega
    rw [eps_mul_S_div_eq_sum_prime_mul omega hN hp_mem,
      eps_mul_S_div_eq_sum_prime_mul omega hN hq_mem]
  rw [hfun]
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro m hm
    rw [integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro k hk
      exact integral_largePrime_cross_term_eq_zero hN hp_mem hq_mem hpq hm hk
    · intro k _hk
      exact integrable_f_mul_f (p * m) (q * k)
  · intro m _hm
    exact integrable_finset_sum (Finset.Icc 1 (N / q)) fun k _hk =>
      integrable_f_mul_f (p * m) (q * k)

/-- Two-cutoff version of the large-prime summand cross cancellation. -/
theorem integral_largePrime_summand_cross_twoCutoffs_eq_zero
    {X M N p q : ℕ}
    (hM : M < X ^ 2)
    (hN : N < X ^ 2)
    (hp_mem : p ∈ largePrimeInterval X M)
    (hq_mem : q ∈ largePrimeInterval X N)
    (hpq : p ≠ q) :
    ∫ omega,
        (eps omega p * S omega (M / p)) *
          (eps omega q * S omega (N / q)) ∂mu = 0 := by
  have hfun :
      (fun omega : Omega =>
        (eps omega p * S omega (M / p)) *
          (eps omega q * S omega (N / q)))
        =
      (fun omega : Omega =>
        (∑ m ∈ Finset.Icc 1 (M / p), f omega (p * m)) *
          (∑ k ∈ Finset.Icc 1 (N / q), f omega (q * k))) := by
    funext omega
    rw [eps_mul_S_div_eq_sum_prime_mul omega hM hp_mem,
      eps_mul_S_div_eq_sum_prime_mul omega hN hq_mem]
  rw [hfun]
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro m hm
    rw [integral_finset_sum]
    · apply Finset.sum_eq_zero
      intro k hk
      exact
        integral_largePrime_cross_term_twoCutoffs_eq_zero
          hM hN hp_mem hq_mem hpq hm hk
    · intro k _hk
      exact integrable_f_mul_f (p * m) (q * k)
  · intro m _hm
    exact integrable_finset_sum (Finset.Icc 1 (N / q)) fun k _hk =>
      integrable_f_mul_f (p * m) (q * k)

/-- Diagonal/off-diagonal second moment identity for the unnormalized
large-prime contribution. -/
theorem integral_largePrimeContribution_sq_eq_sum
    {X N : ℕ} (hN : N < X ^ 2) :
    ∫ omega, (largePrimeContribution omega X N) ^ 2 ∂mu =
      ∑ p ∈ largePrimeInterval X N,
        ∫ omega, (S omega (N / p)) ^ 2 ∂mu := by
  unfold largePrimeContribution
  simp_rw [pow_two]
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [integral_finset_sum]
    · rw [Finset.sum_eq_single p]
      · apply integral_congr_ae
        exact ae_of_all _ fun omega => by
          calc
            eps omega p * S omega (N / p) *
                (eps omega p * S omega (N / p))
                = (eps omega p * S omega (N / p)) ^ 2 := by ring
            _ = (S omega (N / p)) ^ 2 :=
                largePrime_summand_sq omega p N
            _ = S omega (N / p) * S omega (N / p) := by ring
      · intro q hq hqp
        exact integral_largePrime_summand_cross_eq_zero hN hp hq hqp.symm
      · intro hpnot
        exact (hpnot hp).elim
    · intro q _hq
      exact integrable_largePrime_summand_pair N p q
  · intro p _hp
    exact integrable_finset_sum (largePrimeInterval X N) fun q _hq =>
      integrable_largePrime_summand_pair N p q

/-- A finite-sum restriction identity used to write diagonal covariance sums
over the intersection of the visible prime sets. -/
theorem sum_ite_mem_eq_sum_inter (s t : Finset ℕ) (A : ℕ → ℝ) :
    (∑ p ∈ s, if p ∈ t then A p else 0) =
      ∑ p ∈ s ∩ t, A p := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun p _hp => rfl
  ext p
  simp

/-- Diagonal/off-diagonal covariance identity for two unnormalized large-prime
contributions. -/
theorem integral_largePrimeContribution_mul_eq_sum_inter
    {X M N : ℕ} (hM : M < X ^ 2) (hN : N < X ^ 2) :
    ∫ omega,
        largePrimeContribution omega X M *
          largePrimeContribution omega X N ∂mu =
      ∑ p ∈ largePrimeInterval X M ∩ largePrimeInterval X N,
        ∫ omega, S omega (M / p) * S omega (N / p) ∂mu := by
  classical
  let PM := largePrimeInterval X M
  let PN := largePrimeInterval X N
  let A : ℕ → ℝ :=
    fun p => ∫ omega, S omega (M / p) * S omega (N / p) ∂mu
  unfold largePrimeContribution
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finset_sum]
  · calc
      (∑ p ∈ PM,
          ∫ omega,
            ∑ q ∈ PN,
              (eps omega p * S omega (M / p)) *
                (eps omega q * S omega (N / q)) ∂mu)
          = ∑ p ∈ PM, if p ∈ PN then A p else 0 := by
            refine Finset.sum_congr rfl fun p hp => ?_
            rw [integral_finset_sum]
            · by_cases hpN : p ∈ PN
              · rw [if_pos hpN]
                rw [Finset.sum_eq_single p]
                · exact integral_largePrime_summand_samePrime_mul M N p
                · intro q hq hqp
                  exact
                    integral_largePrime_summand_cross_twoCutoffs_eq_zero
                      hM hN (by simpa [PM] using hp)
                      (by simpa [PN] using hq) hqp.symm
                · intro hpnot
                  exact (hpnot hpN).elim
              · rw [if_neg hpN]
                apply Finset.sum_eq_zero
                intro q hq
                have hpq : p ≠ q := by
                  intro hpq_eq
                  subst hpq_eq
                  exact hpN hq
                exact
                  integral_largePrime_summand_cross_twoCutoffs_eq_zero
                    hM hN (by simpa [PM] using hp)
                    (by simpa [PN] using hq) hpq
            · intro q _hq
              exact integrable_largePrime_summand_pair_twoCutoffs M N p q
      _ = ∑ p ∈ PM ∩ PN, A p := by
            exact sum_ite_mem_eq_sum_inter PM PN A
      _ =
          ∑ p ∈ largePrimeInterval X M ∩ largePrimeInterval X N,
            ∫ omega, S omega (M / p) * S omega (N / p) ∂mu := by
            simp [PM, PN, A]
  · intro p _hp
    exact integrable_finset_sum (largePrimeInterval X N) fun q _hq =>
      integrable_largePrime_summand_pair_twoCutoffs M N p q

/-- Normalized second-moment identity for the large-prime process. -/
theorem integral_largePrimeProcess_sq_eq_integral_variance
    {X N : ℕ} (hN : N < X ^ 2) :
    ∫ omega, (largePrimeProcess omega X N) ^ 2 ∂mu =
      ∫ omega, largePrimeVariance omega X N ∂mu := by
  calc
    ∫ omega, (largePrimeProcess omega X N) ^ 2 ∂mu
        =
        ∫ omega,
          (largePrimeContribution omega X N) ^ 2 /
            (Real.sqrt (N : ℝ)) ^ 2 ∂mu := by
          apply integral_congr_ae
          exact ae_of_all _ fun omega => by
            unfold largePrimeProcess
            ring
    _ =
        (∫ omega, (largePrimeContribution omega X N) ^ 2 ∂mu) /
          (Real.sqrt (N : ℝ)) ^ 2 := by
          rw [integral_div]
    _ =
        (∑ p ∈ largePrimeInterval X N,
          ∫ omega, (S omega (N / p)) ^ 2 ∂mu) /
          (Real.sqrt (N : ℝ)) ^ 2 := by
          rw [integral_largePrimeContribution_sq_eq_sum hN]
    _ =
        ∑ p ∈ largePrimeInterval X N,
          (∫ omega, (S omega (N / p)) ^ 2 ∂mu) /
          (Real.sqrt (N : ℝ)) ^ 2 := by
          rw [Finset.sum_div]
    _ =
        ∑ p ∈ largePrimeInterval X N,
          ∫ omega, (largePrimeCoeff omega X N p) ^ 2 ∂mu := by
          refine Finset.sum_congr rfl fun p _hp => ?_
          rw [← integral_div]
          apply integral_congr_ae
          exact ae_of_all _ fun omega => by
            change
              (S omega (N / p)) ^ 2 / (Real.sqrt (N : ℝ)) ^ 2 =
                (largePrimeCoeff omega X N p) ^ 2
            rw [largePrimeCoeff_sq]
    _ =
        ∫ omega, largePrimeVariance omega X N ∂mu := by
          unfold largePrimeVariance
          rw [integral_finset_sum]
          intro p _hp
          exact integrable_largePrimeCoeff_sq X N p

/-- Normalized covariance identity for the large-prime process. -/
theorem integral_largePrimeProcess_mul_eq_integral_covariance
    {X M N : ℕ} (hM : M < X ^ 2) (hN : N < X ^ 2) :
    ∫ omega,
        largePrimeProcess omega X M *
          largePrimeProcess omega X N ∂mu =
      ∫ omega, largePrimeCovariance omega X M N ∂mu := by
  calc
    ∫ omega,
        largePrimeProcess omega X M *
          largePrimeProcess omega X N ∂mu
        =
        ∫ omega,
          (largePrimeContribution omega X M *
            largePrimeContribution omega X N) /
            (Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ)) ∂mu := by
          apply integral_congr_ae
          exact ae_of_all _ fun omega => by
            unfold largePrimeProcess
            ring
    _ =
        (∫ omega,
          largePrimeContribution omega X M *
            largePrimeContribution omega X N ∂mu) /
          (Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ)) := by
          rw [integral_div]
    _ =
        (∑ p ∈ largePrimeInterval X M ∩ largePrimeInterval X N,
          ∫ omega, S omega (M / p) * S omega (N / p) ∂mu) /
          (Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ)) := by
          rw [integral_largePrimeContribution_mul_eq_sum_inter hM hN]
    _ =
        ∑ p ∈ largePrimeInterval X M ∩ largePrimeInterval X N,
          (∫ omega, S omega (M / p) * S omega (N / p) ∂mu) /
            (Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ)) := by
          rw [Finset.sum_div]
    _ =
        ∑ p ∈ largePrimeInterval X M ∩ largePrimeInterval X N,
          ∫ omega,
            largePrimeCoeff omega X M p *
              largePrimeCoeff omega X N p ∂mu := by
          refine Finset.sum_congr rfl fun p _hp => ?_
          rw [← integral_div]
          apply integral_congr_ae
          exact ae_of_all _ fun omega => by
            change
              (S omega (M / p) * S omega (N / p)) /
                  (Real.sqrt (M : ℝ) * Real.sqrt (N : ℝ)) =
                largePrimeCoeff omega X M p *
                  largePrimeCoeff omega X N p
            rw [largePrimeCoeff_mul]
    _ =
        ∫ omega, largePrimeCovariance omega X M N ∂mu := by
          unfold largePrimeCovariance
          rw [integral_finset_sum]
          intro p _hp
          exact integrable_largePrimeCoeff_mul X M N p

/-- A crude deterministic coefficient bound. -/
theorem abs_largePrimeCoeff_le
    (omega : Omega) (X N p : ℕ) :
    |largePrimeCoeff omega X N p| ≤
      (((N / p : ℕ) : ℝ)) / Real.sqrt (N : ℝ) := by
  unfold largePrimeCoeff
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_le_div_of_nonneg_right (abs_S_le omega (N / p)) (Real.sqrt_nonneg _)

/-- Pointwise absorption of the smooth remainder.

If the large-prime process beats the target by a buffer and the smooth
remainder is no worse than the negative of that buffer, then the actual
normalized partial sum beats the target. -/
theorem normSum_ge_of_largePrimeProcess_ge_of_smoothProcess_ge
    (omega : Omega) {X N : ℕ} {M buffer : ℝ}
    (hN : N + 1 < X ^ 2)
    (hLarge : M + buffer ≤ largePrimeProcess omega X (N + 1))
    (hSmooth : -buffer ≤ smoothProcess omega X (N + 1)) :
    M ≤ normSum omega N := by
  rw [normSum_eq_cutoffNormSum_succ,
    cutoffNormSum_eq_smoothProcess_add_largePrimeProcess omega hN]
  linarith

/-- Pointwise absorption, packaged as block success. -/
theorem blockSuccess_of_largePrimeProcess_ge_of_smoothProcess_ge
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j N : ℕ)
    (hmem : N ∈ Finset.Icc (lo j) (hi j))
    (hN : N + 1 < (cut j) ^ 2)
    (hLarge :
      M j + buffer j ≤ largePrimeProcess omega (cut j) (N + 1))
    (hSmooth :
      -buffer j ≤ smoothProcess omega (cut j) (N + 1)) :
    blockSuccess lo hi M omega j := by
  exact
    ⟨N, hmem,
      normSum_ge_of_largePrimeProcess_ge_of_smoothProcess_ge
        (omega := omega) (X := cut j) (N := N)
        (M := M j) (buffer := buffer j) hN hLarge hSmooth⟩

/-- The coefficient functions are measurable. -/
theorem measurable_largePrimeCoeff (X N p : ℕ) :
    Measurable fun omega : Omega => largePrimeCoeff omega X N p := by
  unfold largePrimeCoeff
  exact (measurable_S (N / p)).div_const _

/-- The paper-normalized partial sums are measurable for each cutoff. -/
theorem measurable_cutoffNormSum (N : ℕ) :
    Measurable fun omega : Omega => cutoffNormSum omega N := by
  unfold cutoffNormSum
  exact (measurable_S N).div_const _

/-- The normalized smooth process is measurable for each pair of cutoffs. -/
theorem measurable_smoothProcess (X N : ℕ) :
    Measurable fun omega : Omega => smoothProcess omega X N := by
  classical
  unfold smoothProcess smoothSum
  exact
    (Finset.measurable_sum _ fun n _hn => measurable_f n).div_const _

/-- The large-prime contribution is measurable for each pair of cutoffs. -/
theorem measurable_largePrimeContribution (X N : ℕ) :
    Measurable fun omega : Omega => largePrimeContribution omega X N := by
  unfold largePrimeContribution
  exact
    Finset.measurable_sum _ fun p _hp =>
      (measurable_eps p).mul (measurable_S (N / p))

/-- The normalized large-prime process is measurable for each pair of cutoffs. -/
theorem measurable_largePrimeProcess (X N : ℕ) :
    Measurable fun omega : Omega => largePrimeProcess omega X N := by
  unfold largePrimeProcess
  exact (measurable_largePrimeContribution X N).div_const _

/-- The variance proxy is measurable. -/
theorem measurable_largePrimeVariance (X N : ℕ) :
    Measurable fun omega : Omega => largePrimeVariance omega X N := by
  unfold largePrimeVariance
  exact
    Finset.measurable_sum _ fun p _hp =>
      (measurable_largePrimeCoeff X N p).pow_const 2

/-- The covariance proxy is measurable. -/
theorem measurable_largePrimeCovariance (X M N : ℕ) :
    Measurable fun omega : Omega => largePrimeCovariance omega X M N := by
  unfold largePrimeCovariance
  exact
    Finset.measurable_sum _ fun p _hp =>
      (measurable_largePrimeCoeff X M p).mul
        (measurable_largePrimeCoeff X N p)

end Problem1144
end Erdos
