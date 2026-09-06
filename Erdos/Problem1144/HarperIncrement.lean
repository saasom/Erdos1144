import Erdos.Problem1144.HarperProcess

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-- Large-prime coefficient, extended by zero outside its natural prime
support. This lets different values use a common finite support. -/
noncomputable def largePrimeCoeffOn
    (omega : Omega) (X N p : ℕ) : ℝ :=
  if p ∈ largePrimeInterval X N then
    largePrimeCoeff omega X N p
  else
    0

@[simp] theorem largePrimeCoeffOn_of_mem
    (omega : Omega) {X N p : ℕ}
    (hp : p ∈ largePrimeInterval X N) :
    largePrimeCoeffOn omega X N p = largePrimeCoeff omega X N p := by
  simp [largePrimeCoeffOn, hp]

@[simp] theorem largePrimeCoeffOn_of_not_mem
    (omega : Omega) {X N p : ℕ}
    (hp : p ∉ largePrimeInterval X N) :
    largePrimeCoeffOn omega X N p = 0 := by
  simp [largePrimeCoeffOn, hp]

/-- A common support for two large-prime coefficient vectors. -/
noncomputable def largePrimeIncrementSupport (X M N : ℕ) : Finset ℕ :=
  largePrimeInterval X M ∪ largePrimeInterval X N

/-- A common support for two increment vectors. -/
noncomputable def largePrimeIncrementPairSupport (X M N P Q : ℕ) : Finset ℕ :=
  largePrimeIncrementSupport X M N ∪ largePrimeIncrementSupport X P Q

/-- Log-increment coefficient `v_N - v_M`, represented on a zero-extended
support. -/
noncomputable def largePrimeIncrementCoeff
    (omega : Omega) (X M N p : ℕ) : ℝ :=
  largePrimeCoeffOn omega X N p - largePrimeCoeffOn omega X M p

/-- Large-prime increment process. -/
noncomputable def largePrimeIncrementProcess
    (omega : Omega) (X M N : ℕ) : ℝ :=
  largePrimeProcess omega X N - largePrimeProcess omega X M

/-- Conditional variance proxy for an increment vector. -/
noncomputable def largePrimeIncrementVariance
    (omega : Omega) (X M N : ℕ) : ℝ :=
  ∑ p ∈ largePrimeIncrementSupport X M N,
    (largePrimeIncrementCoeff omega X M N p) ^ 2

/-- Conditional covariance proxy for two increment vectors. -/
noncomputable def largePrimeIncrementCovariance
    (omega : Omega) (X M N P Q : ℕ) : ℝ :=
  ∑ p ∈ largePrimeIncrementPairSupport X M N P Q,
    largePrimeIncrementCoeff omega X M N p *
      largePrimeIncrementCoeff omega X P Q p

theorem sum_largePrimeCoeffOn_sq_eq_variance_of_subset
    (omega : Omega) {X N : ℕ} {s : Finset ℕ}
    (hsub : largePrimeInterval X N ⊆ s) :
    (∑ p ∈ s, (largePrimeCoeffOn omega X N p) ^ 2) =
      largePrimeVariance omega X N := by
  classical
  unfold largePrimeVariance
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun p hp => ?_
    simp [largePrimeCoeffOn, hp]
  · intro p _hp hpnot
    simp [largePrimeCoeffOn, hpnot]

theorem sum_largePrimeCoeffOn_mul_eq_covariance_of_subsets
    (omega : Omega) {X M N : ℕ} {s : Finset ℕ}
    (hM : largePrimeInterval X M ⊆ s) :
    (∑ p ∈ s,
      largePrimeCoeffOn omega X M p *
        largePrimeCoeffOn omega X N p) =
      largePrimeCovariance omega X M N := by
  classical
  unfold largePrimeCovariance
  have hinter : largePrimeInterval X M ∩ largePrimeInterval X N ⊆ s := by
    intro p hp
    exact hM (Finset.mem_of_mem_inter_left hp)
  rw [← Finset.sum_subset hinter]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hpM : p ∈ largePrimeInterval X M := Finset.mem_of_mem_inter_left hp
    have hpN : p ∈ largePrimeInterval X N := Finset.mem_of_mem_inter_right hp
    simp [largePrimeCoeffOn, hpM, hpN]
  · intro p _hp hpnot
    have hpnot' :
        ¬ (p ∈ largePrimeInterval X M ∧ p ∈ largePrimeInterval X N) := by
      simpa [Finset.mem_inter] using hpnot
    by_cases hpM : p ∈ largePrimeInterval X M
    · have hpN : p ∉ largePrimeInterval X N := by
        intro hpN
        exact hpnot' ⟨hpM, hpN⟩
      simp [largePrimeCoeffOn, hpM, hpN]
    · simp [largePrimeCoeffOn, hpM]

/-- A large-prime process may be summed over any finite support containing its
natural interval, using zero-extended coefficients. -/
theorem largePrimeProcess_eq_sum_coeffOn_of_subset
    (omega : Omega) {X N : ℕ} {s : Finset ℕ}
    (hsub : largePrimeInterval X N ⊆ s) :
    largePrimeProcess omega X N =
      ∑ p ∈ s, eps omega p * largePrimeCoeffOn omega X N p := by
  classical
  calc
    largePrimeProcess omega X N
        = ∑ p ∈ largePrimeInterval X N,
            eps omega p * largePrimeCoeff omega X N p := by
          rw [largePrimeProcess_eq_sum_coeff omega X N]
    _ = ∑ p ∈ largePrimeInterval X N,
          eps omega p * largePrimeCoeffOn omega X N p := by
          refine Finset.sum_congr rfl fun p hp => ?_
          simp [largePrimeCoeffOn, hp]
    _ = ∑ p ∈ s, eps omega p * largePrimeCoeffOn omega X N p := by
          exact Finset.sum_subset hsub (by
            intro p _hp hpnot
            simp [largePrimeCoeffOn, hpnot])

/-- Increment process as a signed sum of increment coefficients. -/
theorem largePrimeIncrementProcess_eq_sum_coeff
    (omega : Omega) (X M N : ℕ) :
    largePrimeIncrementProcess omega X M N =
      ∑ p ∈ largePrimeIncrementSupport X M N,
        eps omega p * largePrimeIncrementCoeff omega X M N p := by
  classical
  unfold largePrimeIncrementProcess largePrimeIncrementCoeff
  rw [largePrimeProcess_eq_sum_coeffOn_of_subset
      (omega := omega) (X := X) (N := N)
      (s := largePrimeIncrementSupport X M N) Finset.subset_union_right]
  rw [largePrimeProcess_eq_sum_coeffOn_of_subset
      (omega := omega) (X := X) (N := M)
      (s := largePrimeIncrementSupport X M N) Finset.subset_union_left]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _hp => ?_
  ring

/-- Increment variance is the first-difference variance identity
`||v_N-v_M||^2 = ||v_N||^2 + ||v_M||^2 - 2 <v_M,v_N>`. -/
theorem largePrimeIncrementVariance_eq
    (omega : Omega) (X M N : ℕ) :
    largePrimeIncrementVariance omega X M N =
      largePrimeVariance omega X N +
        largePrimeVariance omega X M -
          2 * largePrimeCovariance omega X M N := by
  classical
  let s := largePrimeIncrementSupport X M N
  let a : ℕ → ℝ := fun p => largePrimeCoeffOn omega X M p
  let b : ℕ → ℝ := fun p => largePrimeCoeffOn omega X N p
  have hsM : largePrimeInterval X M ⊆ s := Finset.subset_union_left
  have hsN : largePrimeInterval X N ⊆ s := Finset.subset_union_right
  unfold largePrimeIncrementVariance largePrimeIncrementCoeff
  change
    (∑ p ∈ s, (b p - a p) ^ 2) =
      largePrimeVariance omega X N +
        largePrimeVariance omega X M -
          2 * largePrimeCovariance omega X M N
  calc
    (∑ p ∈ s, (b p - a p) ^ 2)
        = ∑ p ∈ s, (b p ^ 2 + a p ^ 2 - 2 * (a p * b p)) := by
          refine Finset.sum_congr rfl fun p _hp => ?_
          ring
    _ =
        (∑ p ∈ s, b p ^ 2) +
          (∑ p ∈ s, a p ^ 2) -
            2 * (∑ p ∈ s, a p * b p) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.mul_sum]
    _ =
        largePrimeVariance omega X N +
          largePrimeVariance omega X M -
            2 * largePrimeCovariance omega X M N := by
          rw [sum_largePrimeCoeffOn_sq_eq_variance_of_subset
              (omega := omega) (X := X) (N := N) (s := s) hsN]
          rw [sum_largePrimeCoeffOn_sq_eq_variance_of_subset
              (omega := omega) (X := X) (N := M) (s := s) hsM]
          rw [sum_largePrimeCoeffOn_mul_eq_covariance_of_subsets
              (omega := omega) (X := X) (M := M) (N := N) (s := s) hsM]

/-- Increment covariance is the second-difference identity
`<v_N-v_M,v_Q-v_P> = K(N,Q)-K(N,P)-K(M,Q)+K(M,P)`. -/
theorem largePrimeIncrementCovariance_eq
    (omega : Omega) (X M N P Q : ℕ) :
    largePrimeIncrementCovariance omega X M N P Q =
      largePrimeCovariance omega X N Q -
        largePrimeCovariance omega X N P -
          largePrimeCovariance omega X M Q +
            largePrimeCovariance omega X M P := by
  classical
  let s := largePrimeIncrementPairSupport X M N P Q
  let m : ℕ → ℝ := fun p => largePrimeCoeffOn omega X M p
  let n : ℕ → ℝ := fun p => largePrimeCoeffOn omega X N p
  let pcoeff : ℕ → ℝ := fun p => largePrimeCoeffOn omega X P p
  let q : ℕ → ℝ := fun p => largePrimeCoeffOn omega X Q p
  have hsM : largePrimeInterval X M ⊆ s := by
    exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hsN : largePrimeInterval X N ⊆ s := by
    exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hsP : largePrimeInterval X P ⊆ s := by
    exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_right
  have hsQ : largePrimeInterval X Q ⊆ s := by
    exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_right
  unfold largePrimeIncrementCovariance largePrimeIncrementCoeff
  change
    (∑ r ∈ s, (n r - m r) * (q r - pcoeff r)) =
      largePrimeCovariance omega X N Q -
        largePrimeCovariance omega X N P -
          largePrimeCovariance omega X M Q +
            largePrimeCovariance omega X M P
  calc
    (∑ r ∈ s, (n r - m r) * (q r - pcoeff r))
        =
        ∑ r ∈ s,
          (n r * q r - n r * pcoeff r - m r * q r + m r * pcoeff r) := by
          refine Finset.sum_congr rfl fun r _hr => ?_
          ring
    _ =
        (∑ r ∈ s, n r * q r) -
          (∑ r ∈ s, n r * pcoeff r) -
            (∑ r ∈ s, m r * q r) +
              (∑ r ∈ s, m r * pcoeff r) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ =
        largePrimeCovariance omega X N Q -
          largePrimeCovariance omega X N P -
            largePrimeCovariance omega X M Q +
              largePrimeCovariance omega X M P := by
          rw [sum_largePrimeCoeffOn_mul_eq_covariance_of_subsets
              (omega := omega) (X := X) (M := N) (N := Q) (s := s) hsN]
          rw [sum_largePrimeCoeffOn_mul_eq_covariance_of_subsets
              (omega := omega) (X := X) (M := N) (N := P) (s := s) hsN]
          rw [sum_largePrimeCoeffOn_mul_eq_covariance_of_subsets
              (omega := omega) (X := X) (M := M) (N := Q) (s := s) hsM]
          rw [sum_largePrimeCoeffOn_mul_eq_covariance_of_subsets
              (omega := omega) (X := X) (M := M) (N := P) (s := s) hsM]

theorem measurable_largePrimeCoeffOn (X N p : ℕ) :
    Measurable fun omega : Omega => largePrimeCoeffOn omega X N p := by
  classical
  unfold largePrimeCoeffOn
  by_cases hp : p ∈ largePrimeInterval X N
  · simp [hp, measurable_largePrimeCoeff X N p]
  · simp [hp, measurable_const]

theorem measurable_largePrimeIncrementCoeff (X M N p : ℕ) :
    Measurable fun omega : Omega => largePrimeIncrementCoeff omega X M N p := by
  unfold largePrimeIncrementCoeff
  exact (measurable_largePrimeCoeffOn X N p).sub
    (measurable_largePrimeCoeffOn X M p)

theorem measurable_largePrimeIncrementVariance (X M N : ℕ) :
    Measurable fun omega : Omega =>
      largePrimeIncrementVariance omega X M N := by
  unfold largePrimeIncrementVariance
  exact
    Finset.measurable_sum _ fun p _hp =>
      (measurable_largePrimeIncrementCoeff X M N p).pow_const 2

theorem measurable_largePrimeIncrementCovariance (X M N P Q : ℕ) :
    Measurable fun omega : Omega =>
      largePrimeIncrementCovariance omega X M N P Q := by
  unfold largePrimeIncrementCovariance
  exact
    Finset.measurable_sum _ fun r _hr =>
      (measurable_largePrimeIncrementCoeff X M N r).mul
        (measurable_largePrimeIncrementCoeff X P Q r)

end Problem1144
end Erdos
