import Erdos.Problem1144.PositiveBlockCertificate
import Erdos.Problem1144.Orthogonality
import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.Order.Lattice

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-- Product of the primes in a finite set. -/
noncomputable def primeSetProduct (P : Finset ℕ) : ℕ :=
  ∏ p ∈ P, p

/-- A product of primes is positive. -/
theorem primeSetProduct_pos (P : Finset ℕ) (hP : ∀ p, p ∈ P → p.Prime) :
    0 < primeSetProduct P := by
  rw [primeSetProduct]
  exact Finset.prod_pos fun p hp => (hP p hp).pos

/-- Valuation of a product of distinct primes. -/
theorem factorization_primeSetProduct
    (P : Finset ℕ) (hP : ∀ q, q ∈ P → q.Prime) (p : ℕ) :
    (primeSetProduct P).factorization p = if p ∈ P then 1 else 0 := by
  classical
  rw [primeSetProduct]
  rw [factorization_prod_apply P (fun q => q)]
  · by_cases hpP : p ∈ P
    · rw [if_pos hpP]
      rw [Finset.sum_eq_single p]
      · rw [(hP p hpP).factorization]
        simp
      · intro q hq hqp
        rw [(hP q hq).factorization]
        simp [hqp.symm]
      · intro hpnot
        exact (hpnot hpP).elim
    · rw [if_neg hpP]
      apply Finset.sum_eq_zero
      intro q hq
      rw [(hP q hq).factorization]
      simp [show p ≠ q by intro hpq; subst hpq; exact hpP hq]
  · intro q hq
    exact (hP q hq).pos

/-- For subsets of the same prime set, the product of the two squarefree prime
products is square exactly on the diagonal. -/
theorem isSquare_primeSetProduct_mul_iff_eq
    (P A B : Finset ℕ)
    (hP : ∀ p, p ∈ P → p.Prime)
    (hA : A ∈ P.powerset) (hB : B ∈ P.powerset) :
    IsSquare (primeSetProduct A * primeSetProduct B) ↔ A = B := by
  classical
  have hAprime : ∀ p, p ∈ A → p.Prime :=
    fun p hp => hP p ((Finset.mem_powerset.mp hA) hp)
  have hBprime : ∀ p, p ∈ B → p.Prime :=
    fun p hp => hP p ((Finset.mem_powerset.mp hB) hp)
  constructor
  · intro hsq
    ext p
    constructor
    · intro hpA
      by_contra hpBnot
      have hne : primeSetProduct A * primeSetProduct B ≠ 0 :=
        mul_ne_zero (primeSetProduct_pos A hAprime).ne'
          (primeSetProduct_pos B hBprime).ne'
      have heven := factorization_even_of_isSquare hne hsq p
      have hfac : (primeSetProduct A * primeSetProduct B).factorization p = 1 := by
        rw [Nat.factorization_mul (primeSetProduct_pos A hAprime).ne'
          (primeSetProduct_pos B hBprime).ne']
        simp [factorization_primeSetProduct A hAprime p,
          factorization_primeSetProduct B hBprime p, hpA, hpBnot]
      rw [hfac] at heven
      exact Nat.not_even_one heven
    · intro hpB
      by_contra hpAnot
      have hne : primeSetProduct A * primeSetProduct B ≠ 0 :=
        mul_ne_zero (primeSetProduct_pos A hAprime).ne'
          (primeSetProduct_pos B hBprime).ne'
      have heven := factorization_even_of_isSquare hne hsq p
      have hfac : (primeSetProduct A * primeSetProduct B).factorization p = 1 := by
        rw [Nat.factorization_mul (primeSetProduct_pos A hAprime).ne'
          (primeSetProduct_pos B hBprime).ne']
        simp [factorization_primeSetProduct A hAprime p,
          factorization_primeSetProduct B hBprime p, hpAnot, hpB]
      rw [hfac] at heven
      exact Nat.not_even_one heven
  · intro hEq
    subst hEq
    exact ⟨primeSetProduct A, rfl⟩

/-- Real square indicator for the diagonal square condition on two prime
subsets. -/
theorem squareIndicator_primeSetProduct_mul
    (P A B : Finset ℕ)
    (hP : ∀ p, p ∈ P → p.Prime)
    (hA : A ∈ P.powerset) (hB : B ∈ P.powerset) :
    squareIndicator (primeSetProduct A * primeSetProduct B) =
      if A = B then 1 else 0 := by
  classical
  rw [squareIndicator]
  by_cases hsq : IsSquare (primeSetProduct A * primeSetProduct B)
  · rw [if_pos hsq,
      if_pos ((isSquare_primeSetProduct_mul_iff_eq P A B hP hA hB).mp hsq)]
  · have hne : A ≠ B := by
      intro hAB
      exact hsq ((isSquare_primeSetProduct_mul_iff_eq P A B hP hA hB).mpr hAB)
    rw [if_neg hsq, if_neg hne]

/-- Coefficient attached to one selected subset in the resonator expansion. -/
noncomputable def resonatorSubsetCoeff (A : Finset ℕ) : ℝ :=
  ∏ p ∈ A, (1 / Real.sqrt (p : ℝ))

/-- Positive resonator `prod_{p in P} (1 + eps_p / sqrt p)`. -/
noncomputable def resonator (P : Finset ℕ) (omega : Omega) : ℝ :=
  ∏ p ∈ P, (1 + eps omega p / Real.sqrt (p : ℝ))

/-- Powerset expansion of the positive resonator. -/
theorem resonator_eq_sum_powerset (P : Finset ℕ) (omega : Omega) :
    resonator P omega =
      ∑ A ∈ P.powerset, ∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ) := by
  classical
  rw [resonator, Finset.prod_one_add]

/-- Density used for the resonator-tilted measure. -/
noncomputable def resonatorWeight (P : Finset ℕ) (omega : Omega) : ℝ :=
  resonator P omega ^ 2

/-- The resonator density is nonnegative pointwise. -/
theorem resonatorWeight_nonneg (P : Finset ℕ) (omega : Omega) :
    0 ≤ resonatorWeight P omega := by
  rw [resonatorWeight]
  exact sq_nonneg _

/-- The resonator density equals its absolute value. -/
theorem abs_resonatorWeight (P : Finset ℕ) (omega : Omega) :
    |resonatorWeight P omega| = resonatorWeight P omega :=
  abs_of_nonneg (resonatorWeight_nonneg P omega)

/-- Double-powerset expansion of the resonator density. -/
theorem resonatorWeight_eq_sum_powerset (P : Finset ℕ) (omega : Omega) :
    resonatorWeight P omega =
      ∑ A ∈ P.powerset,
        ∑ B ∈ P.powerset,
          (∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ)) := by
  rw [resonatorWeight, pow_two, resonator_eq_sum_powerset]
  rw [Finset.sum_mul_sum]

/-- A resonator subset term is its deterministic coefficient times the product
of the corresponding prime values of `f`. -/
theorem resonator_subset_term_eq_coeff_mul_f
    (P A : Finset ℕ) (omega : Omega)
    (hP : ∀ p, p ∈ P → p.Prime)
    (hA : A ∈ P.powerset) :
    (∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ))
      =
    resonatorSubsetCoeff A * ∏ p ∈ A, f omega p := by
  rw [resonatorSubsetCoeff, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpP : p ∈ P := (Finset.mem_powerset.mp hA) hp
  rw [f_prime omega (hP p hpP)]
  ring

/-- Index family used to keep the two resonator subsets as separate
multiplicities when applying multiplicative-character orthogonality. -/
private def resonatorIndexValue (n : ℕ) (A B : Finset ℕ) :
    Option (Sum A B) → ℕ
  | none => n
  | some (Sum.inl p) => (p : ℕ)
  | some (Sum.inr p) => (p : ℕ)

/-- Index family for the four prime products in `R_P^4`. -/
private def resonatorFourthIndexValue (A B C D : Finset ℕ) :
    Sum (Sum A B) (Sum C D) → ℕ
  | Sum.inl (Sum.inl p) => (p : ℕ)
  | Sum.inl (Sum.inr p) => (p : ℕ)
  | Sum.inr (Sum.inl p) => (p : ℕ)
  | Sum.inr (Sum.inr p) => (p : ℕ)

/-- Orthogonality evaluation for one summatory term against two prime products. -/
theorem integral_f_mul_prime_products
    (n : ℕ) (A B : Finset ℕ)
    (hn : 0 < n)
    (hA : ∀ p, p ∈ A → p.Prime)
    (hB : ∀ p, p ∈ B → p.Prime) :
    ∫ omega,
        f omega n *
          ((∏ p : A, f omega (p : ℕ)) *
            (∏ p : B, f omega (p : ℕ))) ∂mu
      =
    squareIndicator (n * primeSetProduct A * primeSetProduct B) := by
  let m : Option (Sum A B) → ℕ := resonatorIndexValue n A B
  have hpos :
      ∀ i, i ∈ (Finset.univ : Finset (Option (Sum A B))) → 0 < m i := by
    intro i _hi
    cases i with
    | none => exact hn
    | some s =>
      cases s with
      | inl p => exact (hA p p.property).pos
      | inr p => exact (hB p p.property).pos
  have h := integral_prod_f_indexed
    (I := (Finset.univ : Finset (Option (Sum A B)))) (n := m) hpos
  have hfun :
      (fun omega : Omega =>
        f omega n *
          ((∏ p : A, f omega (p : ℕ)) *
            (∏ p : B, f omega (p : ℕ))))
        =
      (fun omega : Omega => ∏ i, f omega (m i)) := by
    funext omega
    simp [m, resonatorIndexValue]
  rw [hfun, h]
  congr 1
  simp only [m, resonatorIndexValue, Fintype.prod_option, Fintype.prod_sum_type,
    Finset.univ_eq_attach, primeSetProduct]
  rw [Finset.prod_attach A (fun p => p), Finset.prod_attach B (fun p => p)]
  ring_nf

/-- Orthogonality evaluation for four prime products. -/
theorem integral_four_prime_products
    (A B C D : Finset ℕ)
    (hA : ∀ p, p ∈ A → p.Prime)
    (hB : ∀ p, p ∈ B → p.Prime)
    (hC : ∀ p, p ∈ C → p.Prime)
    (hD : ∀ p, p ∈ D → p.Prime) :
    ∫ omega,
        (((∏ p : A, f omega (p : ℕ)) *
            (∏ p : B, f omega (p : ℕ))) *
          ((∏ p : C, f omega (p : ℕ)) *
            (∏ p : D, f omega (p : ℕ)))) ∂mu
      =
    squareIndicator
      (((primeSetProduct A * primeSetProduct B) * primeSetProduct C) *
        primeSetProduct D) := by
  let m : Sum (Sum A B) (Sum C D) → ℕ :=
    resonatorFourthIndexValue A B C D
  have hpos :
      ∀ i, i ∈ (Finset.univ : Finset (Sum (Sum A B) (Sum C D))) → 0 < m i := by
    intro i _hi
    cases i with
    | inl s =>
      cases s with
      | inl p => exact (hA p p.property).pos
      | inr p => exact (hB p p.property).pos
    | inr s =>
      cases s with
      | inl p => exact (hC p p.property).pos
      | inr p => exact (hD p p.property).pos
  have h := integral_prod_f_indexed
    (I := (Finset.univ : Finset (Sum (Sum A B) (Sum C D)))) (n := m) hpos
  have hfun :
      (fun omega : Omega =>
        (((∏ p : A, f omega (p : ℕ)) *
            (∏ p : B, f omega (p : ℕ))) *
          ((∏ p : C, f omega (p : ℕ)) *
            (∏ p : D, f omega (p : ℕ)))))
        =
      (fun omega : Omega => ∏ i, f omega (m i)) := by
    funext omega
    simp [m, resonatorFourthIndexValue]
  rw [hfun, h]
  congr 1
  simp only [m, resonatorFourthIndexValue, Fintype.prod_sum_type,
    Finset.univ_eq_attach, primeSetProduct]
  rw [Finset.prod_attach A (fun p => p), Finset.prod_attach B (fun p => p),
    Finset.prod_attach C (fun p => p), Finset.prod_attach D (fun p => p)]
  ring_nf

/-- The finite products appearing in the summatory expansion are integrable. -/
theorem integrable_f_mul_prime_products (n : ℕ) (A B : Finset ℕ) :
    Integrable
      (fun omega : Omega =>
        f omega n *
          ((∏ p : A, f omega (p : ℕ)) *
            (∏ p : B, f omega (p : ℕ)))) mu := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact
      ((measurable_f n).mul
        ((Finset.measurable_prod (Finset.univ : Finset A)
          fun p _ => measurable_f (p : ℕ)).mul
        (Finset.measurable_prod (Finset.univ : Finset B)
          fun p _ => measurable_f (p : ℕ)))).aestronglyMeasurable
  · exact ae_of_all _ fun omega => by
      simp [abs_f]

/-- The four finite prime products in the resonator fourth moment are
integrable. -/
theorem integrable_four_prime_products (A B C D : Finset ℕ) :
    Integrable
      (fun omega : Omega =>
        (((∏ p : A, f omega (p : ℕ)) *
            (∏ p : B, f omega (p : ℕ))) *
          ((∏ p : C, f omega (p : ℕ)) *
            (∏ p : D, f omega (p : ℕ))))) mu := by
  refine Integrable.of_bound ?_ 1 ?_
  · exact
      (((Finset.measurable_prod (Finset.univ : Finset A)
          fun p _ => measurable_f (p : ℕ)).mul
        (Finset.measurable_prod (Finset.univ : Finset B)
          fun p _ => measurable_f (p : ℕ))).mul
        ((Finset.measurable_prod (Finset.univ : Finset C)
          fun p _ => measurable_f (p : ℕ)).mul
        (Finset.measurable_prod (Finset.univ : Finset D)
          fun p _ => measurable_f (p : ℕ)))).aestronglyMeasurable
  · exact ae_of_all _ fun omega => by
      simp [abs_f]

/-- Expansion of the summatory function against two prime-product factors. -/
theorem integral_S_mul_prime_products
    (N : ℕ) (A B : Finset ℕ)
    (hA : ∀ p, p ∈ A → p.Prime)
    (hB : ∀ p, p ∈ B → p.Prime) :
    ∫ omega,
        S omega (N + 1) *
          ((∏ p : A, f omega (p : ℕ)) *
            (∏ p : B, f omega (p : ℕ))) ∂mu
      =
    ∑ n ∈ Finset.Icc 1 (N + 1),
      squareIndicator (n * primeSetProduct A * primeSetProduct B) := by
  unfold S
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [integral_f_mul_prime_products n A B]
    · exact (Finset.mem_Icc.mp hn).1
    · exact hA
    · exact hB
  · intro n _hn
    exact integrable_f_mul_prime_products n A B

/-- Integrability companion for `integral_S_mul_prime_products`. -/
theorem integrable_S_mul_prime_products
    (N : ℕ) (A B : Finset ℕ) :
    Integrable
      (fun omega : Omega =>
        S omega (N + 1) *
          ((∏ p : A, f omega (p : ℕ)) *
            (∏ p : B, f omega (p : ℕ)))) mu := by
  unfold S
  simp_rw [Finset.sum_mul]
  exact integrable_finset_sum (Finset.Icc 1 (N + 1)) fun n _hn =>
    integrable_f_mul_prime_products n A B

/-- One double-powerset term in the tilted first moment. -/
theorem integral_normSum_resonator_subset_terms
    (P A B : Finset ℕ) (N : ℕ)
    (hP : ∀ p, p ∈ P → p.Prime)
    (hA : A ∈ P.powerset) (hB : B ∈ P.powerset) :
    ∫ omega,
        normSum omega N *
          ((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))) ∂mu
      =
    ((resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
      (∑ n ∈ Finset.Icc 1 (N + 1),
        squareIndicator (n * primeSetProduct A * primeSetProduct B))) /
      Real.sqrt (((N + 1 : ℕ) : ℝ)) := by
  have hAprime : ∀ p, p ∈ A → p.Prime :=
    fun p hp => hP p ((Finset.mem_powerset.mp hA) hp)
  have hBprime : ∀ p, p ∈ B → p.Prime :=
    fun p hp => hP p ((Finset.mem_powerset.mp hB) hp)
  have hfun :
      (fun omega : Omega =>
        normSum omega N *
          ((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))))
      =
      (fun omega : Omega =>
        ((resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
          (S omega (N + 1) *
            ((∏ p : A, f omega (p : ℕ)) *
              (∏ p : B, f omega (p : ℕ))))) /
          Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
    funext omega
    rw [normSum]
    rw [resonator_subset_term_eq_coeff_mul_f P A omega hP hA]
    rw [resonator_subset_term_eq_coeff_mul_f P B omega hP hB]
    rw [Finset.prod_coe_sort A (fun p => f omega p),
      Finset.prod_coe_sort B (fun p => f omega p)]
    ring
  rw [hfun]
  rw [integral_div]
  rw [integral_const_mul]
  rw [integral_S_mul_prime_products N A B hAprime hBprime]

/-- Integrability companion for one double-powerset term in the tilted first
moment. -/
theorem integrable_normSum_resonator_subset_terms
    (P A B : Finset ℕ) (N : ℕ)
    (hP : ∀ p, p ∈ P → p.Prime)
    (hA : A ∈ P.powerset) (hB : B ∈ P.powerset) :
    Integrable
      (fun omega : Omega =>
        normSum omega N *
          ((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ)))) mu := by
  have hfun :
      (fun omega : Omega =>
        normSum omega N *
          ((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))))
      =
      (fun omega : Omega =>
        ((resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
          (S omega (N + 1) *
            ((∏ p : A, f omega (p : ℕ)) *
              (∏ p : B, f omega (p : ℕ))))) /
          Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
    funext omega
    rw [normSum]
    rw [resonator_subset_term_eq_coeff_mul_f P A omega hP hA]
    rw [resonator_subset_term_eq_coeff_mul_f P B omega hP hB]
    rw [Finset.prod_coe_sort A (fun p => f omega p),
      Finset.prod_coe_sort B (fun p => f omega p)]
    ring
  have hbase :=
    ((integrable_S_mul_prime_products N A B).const_mul
      (resonatorSubsetCoeff A * resonatorSubsetCoeff B)).div_const
        (Real.sqrt (((N + 1 : ℕ) : ℝ)))
  exact hbase.congr (ae_of_all _ fun omega => (congrFun hfun omega).symm)

/-- Resonator mass `E R_P^2`. -/
noncomputable def resonatorMass (P : Finset ℕ) : ℝ :=
  ∫ omega, resonatorWeight P omega ∂mu

/-- Tilted mean of one normalized partial sum. -/
noncomputable def resonatorTiltedMean (P : Finset ℕ) (N : ℕ) : ℝ :=
  ∫ omega, normSum omega N * resonatorWeight P omega ∂mu

/-- Fourth moment of the resonator density, used to transfer tilted probability
back to the original measure by Cauchy-Schwarz. -/
noncomputable def resonatorFourthMoment (P : Finset ℕ) : ℝ :=
  ∫ omega, resonatorWeight P omega ^ 2 ∂mu

/-- Finite square-product count predicted by expanding `E R_P^4`.

The four subsets correspond to the four copies of the resonator in
`R_P^4 = (R_P^2)^2`.
-/
noncomputable def resonatorFourthMomentCount (P : Finset ℕ) : ℝ :=
  ∑ A ∈ P.powerset,
    ∑ B ∈ P.powerset,
      ∑ C ∈ P.powerset,
        ∑ D ∈ P.powerset,
          (((resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
              resonatorSubsetCoeff C) *
            resonatorSubsetCoeff D) *
            squareIndicator
              (((primeSetProduct A * primeSetProduct B) *
                  primeSetProduct C) *
                primeSetProduct D)

/-- Finite square-product count predicted by expanding `E R_P^2`. -/
noncomputable def resonatorMassCount (P : Finset ℕ) : ℝ :=
  ∑ A ∈ P.powerset,
    ∑ B ∈ P.powerset,
      (resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
        squareIndicator (primeSetProduct A * primeSetProduct B)

/-- Euler product form of the resonator mass. The factor is kept as
`(1 / sqrt p)^2` here so the finite powerset identity matches by definitional
algebra; it can later be rewritten to `1 / p` under positivity. -/
noncomputable def resonatorMassEulerProduct (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 + (1 / Real.sqrt (p : ℝ)) ^ 2)

/-- Sqrt-free Euler product form of the resonator mass. -/
noncomputable def resonatorMassPrimeProduct (P : Finset ℕ) : ℝ :=
  ∏ p ∈ P, (1 + 1 / (p : ℝ))

/-- The square of the reciprocal square-root factor is the reciprocal prime
factor. -/
theorem inv_sqrt_sq_eq_inv_nat (p : ℕ) (hp : 0 < p) :
    (1 / Real.sqrt (p : ℝ)) ^ 2 = 1 / (p : ℝ) := by
  have hnonneg : 0 ≤ (p : ℝ) := by exact_mod_cast hp.le
  have hsqrt_ne : Real.sqrt (p : ℝ) ≠ 0 := by
    exact (Real.sqrt_pos_of_pos (by exact_mod_cast hp)).ne'
  field_simp [pow_two, hsqrt_ne]
  rw [Real.sq_sqrt hnonneg]

/-- On prime sets, the square-root Euler product is the usual
`prod_p (1 + 1 / p)`. -/
theorem resonatorMassEulerProduct_eq_primeProduct
    (P : Finset ℕ) (hP : ∀ p, p ∈ P → p.Prime) :
    resonatorMassEulerProduct P = resonatorMassPrimeProduct P := by
  rw [resonatorMassEulerProduct, resonatorMassPrimeProduct]
  apply Finset.prod_congr rfl
  intro p hp
  rw [inv_sqrt_sq_eq_inv_nat p (hP p hp).pos]

/-- Resonator subset coefficients are nonnegative. -/
theorem resonatorSubsetCoeff_nonneg (A : Finset ℕ) :
    0 ≤ resonatorSubsetCoeff A := by
  rw [resonatorSubsetCoeff]
  exact Finset.prod_nonneg fun p _hp => by positivity

/-- Resonator subset coefficients are positive when the selected coordinates
are positive integers. -/
theorem resonatorSubsetCoeff_pos
    (A : Finset ℕ) (hA : ∀ p, p ∈ A → 0 < p) :
    0 < resonatorSubsetCoeff A := by
  rw [resonatorSubsetCoeff]
  exact Finset.prod_pos fun p hp => by
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hA p hp
    positivity

/-- The square-root Euler product is positive. -/
theorem resonatorMassEulerProduct_pos (P : Finset ℕ) :
    0 < resonatorMassEulerProduct P := by
  rw [resonatorMassEulerProduct]
  exact Finset.prod_pos fun p _hp => by positivity

/-- The prime Euler product is positive on prime sets. -/
theorem resonatorMassPrimeProduct_pos
    (P : Finset ℕ) (hP : ∀ p, p ∈ P → p.Prime) :
    0 < resonatorMassPrimeProduct P := by
  rw [← resonatorMassEulerProduct_eq_primeProduct P hP]
  exact resonatorMassEulerProduct_pos P

/-- Finite square-product count predicted by expanding `E[S_N R_P^2]`.

The subsets `A` and `B` encode squarefree divisors selected from the two copies
of the resonator.
-/
noncomputable def resonatorFirstMomentCount (P : Finset ℕ) (N : ℕ) : ℝ :=
  ∑ A ∈ P.powerset,
    ∑ B ∈ P.powerset,
      (resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
        (∑ n ∈ Finset.Icc 1 (N + 1),
          squareIndicator (n * primeSetProduct A * primeSetProduct B))

/-- Euler-product amplification predicted by the diagonal square condition. -/
noncomputable def resonatorLocalAmplification (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, 2 / ((p : ℝ) + 1)

/-- Strict lower-tail form of block failure.

This is the event most analytic estimates naturally bound:
every normalized partial sum in the block is strictly below the threshold.
-/
def blockStrictLowerTail (X Y : ℕ → ℕ) (M : ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | ∀ N, N ∈ Finset.Icc (X j) (Y j) → normSum omega N < M j}

/-- Maximum normalized partial sum over one finite block.

The fallback value is used only for empty blocks. Certificates record
`X j ≤ Y j`, so the transfer lemmas always use the nonempty branch.
-/
noncomputable def blockMax (X Y : ℕ → ℕ) (omega : Omega) (j : ℕ) : ℝ :=
  let block := Finset.Icc (X j) (Y j)
  if h : block.Nonempty then block.sup' h fun N => normSum omega N else 0

/-- On nonempty blocks, the strict lower-tail event is the event that the
finite block maximum is below the threshold. -/
theorem blockMax_lt_iff_strictLowerTail
    (X Y : ℕ → ℕ) (M : ℕ → ℝ) (omega : Omega) (j : ℕ)
    (hXY : X j ≤ Y j) :
    blockMax X Y omega j < M j ↔ omega ∈ blockStrictLowerTail X Y M j := by
  classical
  unfold blockMax blockStrictLowerTail
  have hI : (Finset.Icc (X j) (Y j)).Nonempty :=
    Finset.nonempty_Icc.mpr hXY
  rw [dif_pos hI, Finset.sup'_lt_iff]
  rfl

/-- Every normalized partial sum in a nonempty block is bounded by the finite
block maximum. -/
theorem normSum_le_blockMax
    (X Y : ℕ → ℕ) (omega : Omega) (j N : ℕ)
    (hXY : X j ≤ Y j) (hN : N ∈ Finset.Icc (X j) (Y j)) :
    normSum omega N ≤ blockMax X Y omega j := by
  classical
  unfold blockMax
  have hI : (Finset.Icc (X j) (Y j)).Nonempty :=
    Finset.nonempty_Icc.mpr hXY
  rw [dif_pos hI]
  exact Finset.le_sup' (fun N => normSum omega N) hN

/-- On nonempty blocks, success is equivalent to the threshold being below the
finite block maximum. -/
theorem blockSuccess_iff_le_blockMax
    (X Y : ℕ → ℕ) (M : ℕ → ℝ) (omega : Omega) (j : ℕ)
    (hXY : X j ≤ Y j) :
    blockSuccess X Y M omega j ↔ M j ≤ blockMax X Y omega j := by
  classical
  constructor
  · intro hsucc
    rcases hsucc with ⟨N, hN, hle⟩
    exact le_trans hle (normSum_le_blockMax X Y omega j N hXY hN)
  · intro hle
    unfold blockMax at hle
    have hI : (Finset.Icc (X j) (Y j)).Nonempty :=
      Finset.nonempty_Icc.mpr hXY
    rw [dif_pos hI, Finset.le_sup'_iff] at hle
    exact hle

/-- The finite block maximum is measurable as a function of the random
environment. -/
theorem measurable_blockMax (X Y : ℕ → ℕ) (j : ℕ) :
    Measurable fun omega : Omega => blockMax X Y omega j := by
  classical
  unfold blockMax
  let s := Finset.Icc (X j) (Y j)
  change Measurable fun omega : Omega =>
    if h : s.Nonempty then
      s.sup' h fun N => normSum omega N
    else 0
  by_cases hI : s.Nonempty
  · have hEq :
        (fun omega : Omega =>
          if h : s.Nonempty then s.sup' h fun N => normSum omega N else 0)
        =
        (fun omega : Omega => s.sup' hI fun N => normSum omega N) := by
      funext omega
      simp [hI]
    rw [hEq]
    have hEqApply :
        (fun omega : Omega => s.sup' hI fun N => normSum omega N)
        =
        s.sup' hI (fun N (omega : Omega) => normSum omega N) := by
      funext omega
      exact (Finset.sup'_apply hI (fun N (omega : Omega) => normSum omega N) omega).symm
    rw [hEqApply]
    exact
      Finset.measurable_sup'
        (s := s)
        (f := fun N (omega : Omega) => normSum omega N)
        hI
        (fun N _hN => measurable_normSum N)
  · have hEq :
        (fun omega : Omega =>
          if h : s.Nonempty then s.sup' h fun N => normSum omega N else 0)
        =
        (fun _omega : Omega => 0) := by
      funext omega
      simp [hI]
    rw [hEq]
    exact measurable_const

/-- On nonempty blocks, the strict lower-tail event is measurable. -/
theorem measurableSet_blockStrictLowerTail
    (X Y : ℕ → ℕ) (M : ℕ → ℝ) (j : ℕ)
    (hXY : X j ≤ Y j) :
    MeasurableSet (blockStrictLowerTail X Y M j) := by
  have hset :
      blockStrictLowerTail X Y M j =
        {omega : Omega | blockMax X Y omega j < M j} := by
    ext omega
    exact (blockMax_lt_iff_strictLowerTail X Y M omega j hXY).symm
  rw [hset]
  exact measurableSet_lt (measurable_blockMax X Y j) measurable_const

/-- On nonempty blocks, non-strict block failure equals the strict lower-tail
event. -/
theorem blockFailure_eq_blockStrictLowerTail
    (X Y : ℕ → ℕ) (M : ℕ → ℝ) (j : ℕ)
    (hXY : X j ≤ Y j) :
    blockFailure X Y M j = blockStrictLowerTail X Y M j := by
  ext omega
  constructor
  · intro hfail N hN
    exact lt_of_not_ge fun hle => hfail ⟨N, hN, hle⟩
  · intro htail hsucc
    have hle :
        M j ≤ blockMax X Y omega j :=
      (blockSuccess_iff_le_blockMax X Y M omega j hXY).mp hsucc
    have hlt :
        blockMax X Y omega j < M j :=
      (blockMax_lt_iff_strictLowerTail X Y M omega j hXY).mpr htail
    exact not_lt_of_ge hle hlt

/-- On nonempty blocks, the original block-failure event is measurable. -/
theorem measurableSet_blockFailure
    (X Y : ℕ → ℕ) (M : ℕ → ℝ) (j : ℕ)
    (hXY : X j ≤ Y j) :
    MeasurableSet (blockFailure X Y M j) := by
  rw [blockFailure_eq_blockStrictLowerTail X Y M j hXY]
  exact measurableSet_blockStrictLowerTail X Y M j hXY

/-- The existing non-strict failure event is contained in the strict lower-tail
event, by linearity of the order on `ℝ`. -/
theorem blockFailure_subset_blockStrictLowerTail
    (X Y : ℕ → ℕ) (M : ℕ → ℝ) (j : ℕ) :
    blockFailure X Y M j ⊆ blockStrictLowerTail X Y M j := by
  intro omega hfail N hN
  exact lt_of_not_ge fun hle => hfail ⟨N, hN, hle⟩

/-- Resonator-shaped finite block estimates.

The field `P` records the prime set used in each block. The hard analytic work
is compressed into `lower_tail`, a summable bound for the strict lower-tail
event. The theorem below turns this into the general positive-block certificate.
-/
structure ResonatorBlockEstimates where
  X : ℕ → ℕ
  Y : ℕ → ℕ
  M : ℕ → ℝ
  fail : ℕ → ℝ≥0∞
  P : ℕ → Finset ℕ
  gap : ℕ → ℝ
  fourth : ℕ → ℝ
  P_prime : ∀ j p, p ∈ P j → p.Prime
  block_nonempty : ∀ j, X j ≤ Y j
  X_tendsto : Tendsto X atTop atTop
  M_tendsto : Tendsto M atTop atTop
  fail_summable : (∑' j, fail j) ≠ ⊤
  gap_pos : ∀ j, 0 < gap j
  first_moment_count_lower :
    ∀ j, ∃ N ∈ Finset.Icc (X j) (Y j),
      (M j + gap j) * resonatorMassPrimeProduct (P j) ≤
        resonatorFirstMomentCount (P j) N /
          Real.sqrt (((N + 1 : ℕ) : ℝ))
  fourth_moment_count_upper :
    ∀ j, resonatorFourthMomentCount (P j) ≤ fourth j
  lower_tail :
    ∀ j, mu (blockStrictLowerTail X Y M j) ≤ fail j

/-- A sharper resonator certificate that derives the strict lower-tail estimate
from the finite first/fourth resonator inequalities.

The field `tail_transfer` is the remaining probabilistic transfer theorem:
for each block, the finite first-moment lower bound and fourth-moment upper
bound must imply the summable lower-tail estimate. Keeping it as a separate
interface prevents the final path from assuming the lower-tail bound as an
opaque primitive.
-/
structure ResonatorBlockTransferCertificate where
  X : ℕ → ℕ
  Y : ℕ → ℕ
  M : ℕ → ℝ
  fail : ℕ → ℝ≥0∞
  P : ℕ → Finset ℕ
  gap : ℕ → ℝ
  fourth : ℕ → ℝ
  P_prime : ∀ j p, p ∈ P j → p.Prime
  block_nonempty : ∀ j, X j ≤ Y j
  X_tendsto : Tendsto X atTop atTop
  M_tendsto : Tendsto M atTop atTop
  fail_summable : (∑' j, fail j) ≠ ⊤
  gap_pos : ∀ j, 0 < gap j
  first_moment_count_lower :
    ∀ j, ∃ N ∈ Finset.Icc (X j) (Y j),
      (M j + gap j) * resonatorMassPrimeProduct (P j) ≤
        resonatorFirstMomentCount (P j) N /
          Real.sqrt (((N + 1 : ℕ) : ℝ))
  fourth_moment_count_upper :
    ∀ j, resonatorFourthMomentCount (P j) ≤ fourth j
  tail_transfer :
    ∀ j,
      (∃ N ∈ Finset.Icc (X j) (Y j),
        (M j + gap j) * resonatorMassPrimeProduct (P j) ≤
          resonatorFirstMomentCount (P j) N /
            Real.sqrt (((N + 1 : ℕ) : ℝ))) →
      resonatorFourthMomentCount (P j) ≤ fourth j →
      mu (blockStrictLowerTail X Y M j) ≤ fail j

/-- The transfer certificate recovers the older resonator block estimate
interface by applying `tail_transfer` block by block. -/
def resonatorBlockEstimates_of_transferCertificate
    (h : ResonatorBlockTransferCertificate) :
    ResonatorBlockEstimates where
  X := h.X
  Y := h.Y
  M := h.M
  fail := h.fail
  P := h.P
  gap := h.gap
  fourth := h.fourth
  P_prime := h.P_prime
  block_nonempty := h.block_nonempty
  X_tendsto := h.X_tendsto
  M_tendsto := h.M_tendsto
  fail_summable := h.fail_summable
  gap_pos := h.gap_pos
  first_moment_count_lower := h.first_moment_count_lower
  fourth_moment_count_upper := h.fourth_moment_count_upper
  lower_tail := fun j =>
    h.tail_transfer j
      (h.first_moment_count_lower j)
      (h.fourth_moment_count_upper j)

/-- Resonator block estimates imply the active positive-block certificate. -/
def positiveBlockOmega_of_resonatorBlockEstimates
    (h : ResonatorBlockEstimates) :
    PositiveBlockOmega where
  X := h.X
  Y := h.Y
  M := h.M
  fail := h.fail
  X_tendsto := h.X_tendsto
  M_tendsto := h.M_tendsto
  fail_summable := h.fail_summable
  prob_fail := fun j =>
    le_trans
      (measure_mono (blockFailure_subset_blockStrictLowerTail h.X h.Y h.M j))
      (h.lower_tail j)

/-- Certificate-local form of the block maximum/lower-tail equivalence. -/
theorem ResonatorBlockEstimates.blockMax_lt_iff
    (h : ResonatorBlockEstimates) (omega : Omega) (j : ℕ) :
    blockMax h.X h.Y omega j < h.M j ↔
      omega ∈ blockStrictLowerTail h.X h.Y h.M j :=
  blockMax_lt_iff_strictLowerTail h.X h.Y h.M omega j (h.block_nonempty j)

/-- Certificate-local form of the block success/block maximum equivalence. -/
theorem ResonatorBlockEstimates.blockSuccess_iff_le_blockMax
    (h : ResonatorBlockEstimates) (omega : Omega) (j : ℕ) :
    blockSuccess h.X h.Y h.M omega j ↔ h.M j ≤ blockMax h.X h.Y omega j :=
  Problem1144.blockSuccess_iff_le_blockMax h.X h.Y h.M omega j (h.block_nonempty j)

/-- Certificate-local bound of a block value by the block maximum. -/
theorem ResonatorBlockEstimates.normSum_le_blockMax
    (h : ResonatorBlockEstimates) (omega : Omega) {j N : ℕ}
    (hN : N ∈ Finset.Icc (h.X j) (h.Y j)) :
    normSum omega N ≤ blockMax h.X h.Y omega j :=
  Problem1144.normSum_le_blockMax h.X h.Y omega j N (h.block_nonempty j) hN

/-- Certificate-local measurability of the strict lower-tail event. -/
theorem ResonatorBlockEstimates.measurableSet_blockStrictLowerTail
    (h : ResonatorBlockEstimates) (j : ℕ) :
    MeasurableSet (blockStrictLowerTail h.X h.Y h.M j) :=
  Problem1144.measurableSet_blockStrictLowerTail h.X h.Y h.M j
    (h.block_nonempty j)

/-- Certificate-local measurability of the non-strict block-failure event. -/
theorem ResonatorBlockEstimates.measurableSet_blockFailure
    (h : ResonatorBlockEstimates) (j : ℕ) :
    MeasurableSet (blockFailure h.X h.Y h.M j) :=
  Problem1144.measurableSet_blockFailure h.X h.Y h.M j
    (h.block_nonempty j)

/-- Transfer-certificate-local measurability of the strict lower-tail event. -/
theorem ResonatorBlockTransferCertificate.measurableSet_blockStrictLowerTail
    (h : ResonatorBlockTransferCertificate) (j : ℕ) :
    MeasurableSet (blockStrictLowerTail h.X h.Y h.M j) :=
  Problem1144.measurableSet_blockStrictLowerTail h.X h.Y h.M j
    (h.block_nonempty j)

/-- Transfer-certificate-local measurability of the non-strict block-failure
event. -/
theorem ResonatorBlockTransferCertificate.measurableSet_blockFailure
    (h : ResonatorBlockTransferCertificate) (j : ℕ) :
    MeasurableSet (blockFailure h.X h.Y h.M j) :=
  Problem1144.measurableSet_blockFailure h.X h.Y h.M j
    (h.block_nonempty j)

/-- One double-powerset term in the resonator mass. -/
theorem integral_resonator_subset_terms
    (P A B : Finset ℕ)
    (hP : ∀ p, p ∈ P → p.Prime)
    (hA : A ∈ P.powerset) (hB : B ∈ P.powerset) :
    ∫ omega,
        ((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
          (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))) ∂mu
      =
    (resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
      squareIndicator (primeSetProduct A * primeSetProduct B) := by
  have hAprime : ∀ p, p ∈ A → p.Prime :=
    fun p hp => hP p ((Finset.mem_powerset.mp hA) hp)
  have hBprime : ∀ p, p ∈ B → p.Prime :=
    fun p hp => hP p ((Finset.mem_powerset.mp hB) hp)
  have hfun :
      (fun omega : Omega =>
        ((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
          (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))))
      =
      (fun omega : Omega =>
        (resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
          (f omega 1 *
            ((∏ p : A, f omega (p : ℕ)) *
              (∏ p : B, f omega (p : ℕ))))) := by
    funext omega
    rw [resonator_subset_term_eq_coeff_mul_f P A omega hP hA]
    rw [resonator_subset_term_eq_coeff_mul_f P B omega hP hB]
    rw [Finset.prod_coe_sort A (fun p => f omega p),
      Finset.prod_coe_sort B (fun p => f omega p)]
    simp
    ring
  rw [hfun]
  rw [integral_const_mul]
  rw [integral_f_mul_prime_products 1 A B (by norm_num) hAprime hBprime]
  ring_nf

/-- Integrability companion for one double-powerset term in the resonator mass. -/
theorem integrable_resonator_subset_terms
    (P A B : Finset ℕ)
    (hP : ∀ p, p ∈ P → p.Prime)
    (hA : A ∈ P.powerset) (hB : B ∈ P.powerset) :
    Integrable
      (fun omega : Omega =>
        ((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
          (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ)))) mu := by
  have hfun :
      (fun omega : Omega =>
        ((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
          (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))))
      =
      (fun omega : Omega =>
        (resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
          (f omega 1 *
            ((∏ p : A, f omega (p : ℕ)) *
              (∏ p : B, f omega (p : ℕ))))) := by
    funext omega
    rw [resonator_subset_term_eq_coeff_mul_f P A omega hP hA]
    rw [resonator_subset_term_eq_coeff_mul_f P B omega hP hB]
    rw [Finset.prod_coe_sort A (fun p => f omega p),
      Finset.prod_coe_sort B (fun p => f omega p)]
    simp
    ring
  exact
    ((integrable_f_mul_prime_products 1 A B).const_mul
      (resonatorSubsetCoeff A * resonatorSubsetCoeff B)).congr
      (ae_of_all _ fun omega => (congrFun hfun omega).symm)

/-- The resonator density is integrable for finite prime sets. -/
theorem integrable_resonatorWeight
    (P : Finset ℕ) (hP : ∀ p, p ∈ P → p.Prime) :
    Integrable (fun omega : Omega => resonatorWeight P omega) mu := by
  have hfun :
      (fun omega : Omega => resonatorWeight P omega)
      =
      (fun omega : Omega =>
        ∑ A ∈ P.powerset,
          ∑ B ∈ P.powerset,
            (∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
              (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))) := by
    funext omega
    rw [resonatorWeight_eq_sum_powerset]
  exact
    (integrable_finset_sum P.powerset fun A hA =>
      integrable_finset_sum P.powerset fun B hB =>
        integrable_resonator_subset_terms P A B hP hA hB).congr
      (ae_of_all _ fun omega => (congrFun hfun omega).symm)

/-- One quadruple-powerset term in the resonator fourth moment. -/
theorem integral_resonator_four_subset_terms
    (P A B C D : Finset ℕ)
    (hP : ∀ p, p ∈ P → p.Prime)
    (hA : A ∈ P.powerset) (hB : B ∈ P.powerset)
    (hC : C ∈ P.powerset) (hD : D ∈ P.powerset) :
    ∫ omega,
        (((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))) *
          ((∏ p ∈ C, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ D, eps omega p / Real.sqrt (p : ℝ)))) ∂mu
      =
    ((((resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
          resonatorSubsetCoeff C) * resonatorSubsetCoeff D) *
      squareIndicator
        (((primeSetProduct A * primeSetProduct B) * primeSetProduct C) *
          primeSetProduct D)) := by
  have hAprime : ∀ p, p ∈ A → p.Prime :=
    fun p hp => hP p ((Finset.mem_powerset.mp hA) hp)
  have hBprime : ∀ p, p ∈ B → p.Prime :=
    fun p hp => hP p ((Finset.mem_powerset.mp hB) hp)
  have hCprime : ∀ p, p ∈ C → p.Prime :=
    fun p hp => hP p ((Finset.mem_powerset.mp hC) hp)
  have hDprime : ∀ p, p ∈ D → p.Prime :=
    fun p hp => hP p ((Finset.mem_powerset.mp hD) hp)
  have hfun :
      (fun omega : Omega =>
        (((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))) *
          ((∏ p ∈ C, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ D, eps omega p / Real.sqrt (p : ℝ)))))
      =
      (fun omega : Omega =>
        (((resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
            resonatorSubsetCoeff C) * resonatorSubsetCoeff D) *
          (((∏ p : A, f omega (p : ℕ)) *
              (∏ p : B, f omega (p : ℕ))) *
            ((∏ p : C, f omega (p : ℕ)) *
              (∏ p : D, f omega (p : ℕ))))) := by
    funext omega
    rw [resonator_subset_term_eq_coeff_mul_f P A omega hP hA]
    rw [resonator_subset_term_eq_coeff_mul_f P B omega hP hB]
    rw [resonator_subset_term_eq_coeff_mul_f P C omega hP hC]
    rw [resonator_subset_term_eq_coeff_mul_f P D omega hP hD]
    rw [Finset.prod_coe_sort A (fun p => f omega p),
      Finset.prod_coe_sort B (fun p => f omega p),
      Finset.prod_coe_sort C (fun p => f omega p),
      Finset.prod_coe_sort D (fun p => f omega p)]
    ring
  rw [hfun]
  rw [integral_const_mul]
  rw [integral_four_prime_products A B C D hAprime hBprime hCprime hDprime]

/-- Integrability companion for one quadruple-powerset term in the resonator
fourth moment. -/
theorem integrable_resonator_four_subset_terms
    (P A B C D : Finset ℕ)
    (hP : ∀ p, p ∈ P → p.Prime)
    (hA : A ∈ P.powerset) (hB : B ∈ P.powerset)
    (hC : C ∈ P.powerset) (hD : D ∈ P.powerset) :
    Integrable
      (fun omega : Omega =>
        (((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))) *
          ((∏ p ∈ C, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ D, eps omega p / Real.sqrt (p : ℝ))))) mu := by
  have hfun :
      (fun omega : Omega =>
        (((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))) *
          ((∏ p ∈ C, eps omega p / Real.sqrt (p : ℝ)) *
            (∏ p ∈ D, eps omega p / Real.sqrt (p : ℝ)))))
      =
      (fun omega : Omega =>
        (((resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
            resonatorSubsetCoeff C) * resonatorSubsetCoeff D) *
          (((∏ p : A, f omega (p : ℕ)) *
              (∏ p : B, f omega (p : ℕ))) *
            ((∏ p : C, f omega (p : ℕ)) *
              (∏ p : D, f omega (p : ℕ))))) := by
    funext omega
    rw [resonator_subset_term_eq_coeff_mul_f P A omega hP hA]
    rw [resonator_subset_term_eq_coeff_mul_f P B omega hP hB]
    rw [resonator_subset_term_eq_coeff_mul_f P C omega hP hC]
    rw [resonator_subset_term_eq_coeff_mul_f P D omega hP hD]
    rw [Finset.prod_coe_sort A (fun p => f omega p),
      Finset.prod_coe_sort B (fun p => f omega p),
      Finset.prod_coe_sort C (fun p => f omega p),
      Finset.prod_coe_sort D (fun p => f omega p)]
    ring
  exact
    ((integrable_four_prime_products A B C D).const_mul
      (((resonatorSubsetCoeff A * resonatorSubsetCoeff B) *
          resonatorSubsetCoeff C) * resonatorSubsetCoeff D)).congr
      (ae_of_all _ fun omega => (congrFun hfun omega).symm)

/-- Quadruple-powerset expansion of the square of the resonator density. -/
theorem resonatorWeight_sq_eq_sum_powerset
    (P : Finset ℕ) (omega : Omega) :
    resonatorWeight P omega ^ 2 =
      ∑ A ∈ P.powerset,
        ∑ B ∈ P.powerset,
          ∑ C ∈ P.powerset,
            ∑ D ∈ P.powerset,
              (((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
                  (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))) *
                ((∏ p ∈ C, eps omega p / Real.sqrt (p : ℝ)) *
                  (∏ p ∈ D, eps omega p / Real.sqrt (p : ℝ)))) := by
  rw [pow_two, resonatorWeight_eq_sum_powerset]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]

/-- The square of the resonator density is integrable for finite prime sets. -/
theorem integrable_resonatorWeight_sq
    (P : Finset ℕ) (hP : ∀ p, p ∈ P → p.Prime) :
    Integrable (fun omega : Omega => resonatorWeight P omega ^ 2) mu := by
  have hfun :
      (fun omega : Omega => resonatorWeight P omega ^ 2)
      =
      (fun omega : Omega =>
        ∑ A ∈ P.powerset,
          ∑ B ∈ P.powerset,
            ∑ C ∈ P.powerset,
              ∑ D ∈ P.powerset,
                (((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
                    (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))) *
                  ((∏ p ∈ C, eps omega p / Real.sqrt (p : ℝ)) *
                    (∏ p ∈ D, eps omega p / Real.sqrt (p : ℝ))))) := by
    funext omega
    rw [resonatorWeight_sq_eq_sum_powerset]
  exact
    (integrable_finset_sum P.powerset fun A hA =>
      integrable_finset_sum P.powerset fun B hB =>
        integrable_finset_sum P.powerset fun C hC =>
          integrable_finset_sum P.powerset fun D hD =>
            integrable_resonator_four_subset_terms P A B C D hP hA hB hC hD).congr
      (ae_of_all _ fun omega => (congrFun hfun omega).symm)

/-- The mass expansion for the positive resonator. -/
theorem resonator_mass_count
  (P : Finset ℕ)
  (hP : ∀ p, p ∈ P → p.Prime) :
  resonatorMass P = resonatorMassCount P := by
  rw [resonatorMass, resonatorMassCount]
  simp_rw [resonatorWeight_eq_sum_powerset]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro B hB
      rw [integral_resonator_subset_terms P A B hP hA hB]
    · intro B hB
      exact integrable_resonator_subset_terms P A B hP hA hB
  · intro A hA
    exact integrable_finset_sum P.powerset fun B hB =>
      integrable_resonator_subset_terms P A B hP hA hB

/-- The fourth-moment expansion for the positive resonator. -/
theorem resonator_fourth_moment_count
    (P : Finset ℕ)
    (hP : ∀ p, p ∈ P → p.Prime) :
    resonatorFourthMoment P = resonatorFourthMomentCount P := by
  rw [resonatorFourthMoment, resonatorFourthMomentCount]
  have hfun :
      (fun omega : Omega => resonatorWeight P omega ^ 2)
      =
      (fun omega : Omega =>
        ∑ A ∈ P.powerset,
          ∑ B ∈ P.powerset,
            ∑ C ∈ P.powerset,
              ∑ D ∈ P.powerset,
                (((∏ p ∈ A, eps omega p / Real.sqrt (p : ℝ)) *
                    (∏ p ∈ B, eps omega p / Real.sqrt (p : ℝ))) *
                  ((∏ p ∈ C, eps omega p / Real.sqrt (p : ℝ)) *
                    (∏ p ∈ D, eps omega p / Real.sqrt (p : ℝ))))) := by
    funext omega
    rw [pow_two, resonatorWeight_eq_sum_powerset]
    simp_rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  rw [hfun]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro B hB
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro C hC
        rw [integral_finset_sum]
        · apply Finset.sum_congr rfl
          intro D hD
          rw [integral_resonator_four_subset_terms P A B C D hP hA hB hC hD]
        · intro D hD
          exact integrable_resonator_four_subset_terms P A B C D hP hA hB hC hD
      · intro C hC
        exact integrable_finset_sum P.powerset fun D hD =>
          integrable_resonator_four_subset_terms P A B C D hP hA hB hC hD
    · intro B hB
      exact integrable_finset_sum P.powerset fun C hC =>
        integrable_finset_sum P.powerset fun D hD =>
          integrable_resonator_four_subset_terms P A B C D hP hA hB hC hD
  · intro A hA
    exact integrable_finset_sum P.powerset fun B hB =>
      integrable_finset_sum P.powerset fun C hC =>
        integrable_finset_sum P.powerset fun D hD =>
          integrable_resonator_four_subset_terms P A B C D hP hA hB hC hD

/-- The square condition in the mass count restricts the double powerset sum to
the diagonal. -/
theorem resonatorMassCount_eq_diag_sum
    (P : Finset ℕ) (hP : ∀ p, p ∈ P → p.Prime) :
    resonatorMassCount P =
      ∑ A ∈ P.powerset, resonatorSubsetCoeff A * resonatorSubsetCoeff A := by
  classical
  rw [resonatorMassCount]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_eq_single_of_mem A hA]
  · simp [squareIndicator_primeSetProduct_mul P A A hP hA hA]
  · intro B hB hBA
    rw [squareIndicator_primeSetProduct_mul P A B hP hA hB]
    have hAB : A ≠ B := fun h => hBA h.symm
    simp [hAB]

/-- The finite Euler-product form of the resonator mass count. -/
theorem resonatorMassCount_eq_eulerProduct
    (P : Finset ℕ) (hP : ∀ p, p ∈ P → p.Prime) :
    resonatorMassCount P = resonatorMassEulerProduct P := by
  classical
  rw [resonatorMassCount_eq_diag_sum P hP, resonatorMassEulerProduct]
  rw [Finset.prod_one_add]
  apply Finset.sum_congr rfl
  intro A _hA
  rw [resonatorSubsetCoeff, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  ring

/-- The probabilistic mass itself has the finite Euler-product form. -/
theorem resonator_mass_eulerProduct
    (P : Finset ℕ) (hP : ∀ p, p ∈ P → p.Prime) :
    resonatorMass P = resonatorMassEulerProduct P := by
  rw [resonator_mass_count P hP, resonatorMassCount_eq_eulerProduct P hP]

/-- The resonator mass in the usual `prod_p (1 + 1 / p)` normalization. -/
theorem resonator_mass_primeProduct
    (P : Finset ℕ) (hP : ∀ p, p ∈ P → p.Prime) :
    resonatorMass P = resonatorMassPrimeProduct P := by
  rw [resonator_mass_eulerProduct P hP,
    resonatorMassEulerProduct_eq_primeProduct P hP]

/-- The first-moment expansion for the positive resonator.

This is deliberately stated as a finite identity. Proving it should use
`integral_prod_f` plus the expansion of `R_P^2`.
-/
theorem resonator_first_moment_count
  (P : Finset ℕ)
  (hP : ∀ p, p ∈ P → p.Prime)
  (N : ℕ) :
  resonatorTiltedMean P N =
    resonatorFirstMomentCount P N / Real.sqrt (((N + 1 : ℕ) : ℝ)) := by
  rw [resonatorTiltedMean, resonatorFirstMomentCount]
  simp_rw [Finset.sum_div]
  simp_rw [resonatorWeight_eq_sum_powerset]
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro A hA
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro B hB
      rw [integral_normSum_resonator_subset_terms P A B N hP hA hB]
      rw [← Finset.mul_sum]
    · intro B hB
      exact integrable_normSum_resonator_subset_terms P A B N hP hA hB
  · intro A hA
    exact integrable_finset_sum P.powerset fun B hB =>
      integrable_normSum_resonator_subset_terms P A B N hP hA hB

/-- The finite first-moment count lower bound in `ResonatorBlockEstimates`
translates into the corresponding tilted integral lower bound. -/
theorem ResonatorBlockEstimates.firstMomentIntegral_lower
    (h : ResonatorBlockEstimates) :
    ∀ j, ∃ N ∈ Finset.Icc (h.X j) (h.Y j),
      (h.M j + h.gap j) * resonatorMass (h.P j) ≤
        resonatorTiltedMean (h.P j) N := by
  intro j
  rcases h.first_moment_count_lower j with ⟨N, hN, hle⟩
  refine ⟨N, hN, ?_⟩
  rw [resonator_mass_primeProduct (h.P j) (h.P_prime j)]
  rw [resonator_first_moment_count (h.P j) (h.P_prime j) N]
  exact hle

/-- The finite fourth-moment count upper bound in `ResonatorBlockEstimates`
translates into the corresponding integral upper bound. -/
theorem ResonatorBlockEstimates.fourthMomentIntegral_upper
    (h : ResonatorBlockEstimates) :
    ∀ j, resonatorFourthMoment (h.P j) ≤ h.fourth j := by
  intro j
  rw [resonator_fourth_moment_count (h.P j) (h.P_prime j)]
  exact h.fourth_moment_count_upper j

end Problem1144
end Erdos
