import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators

namespace Erdos
namespace Problem1144

/-!
# Deterministic dyadic-transfer inequalities

This file contains route-neutral finite `L^2` estimates for the Harperized
endpoint-screen direction.  The analytic dyadic recurrence is expected to
reduce, after discretization, to a nonnegative kernel with bounded row and
column mass.  The finite Schur estimate below is the formal deterministic
core of the claim that dyadic-increment energy controls endpoint energy.
-/

/-- Weighted finite Cauchy--Schwarz in a form suited for nonnegative kernels. -/
theorem sq_sum_mul_le_sum_mul_sq_of_nonneg {ι : Type*}
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i, i ∈ s → 0 ≤ w i) :
    (∑ i ∈ s, w i * x i) ^ 2 ≤
      (∑ i ∈ s, w i) * (∑ i ∈ s, w i * x i ^ 2) := by
  let f : ι → ℝ := fun i => Real.sqrt (w i)
  let g : ι → ℝ := fun i => Real.sqrt (w i) * x i
  have hfg :
      (∑ i ∈ s, f i * g i) = ∑ i ∈ s, w i * x i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hwi : 0 ≤ w i := hw i hi
    calc
      f i * g i = (Real.sqrt (w i) * Real.sqrt (w i)) * x i := by
        simp [f, g, mul_assoc]
      _ = w i * x i := by rw [← sq, Real.sq_sqrt hwi]
  have hf_sq :
      (∑ i ∈ s, f i ^ 2) = ∑ i ∈ s, w i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hwi : 0 ≤ w i := hw i hi
    simp [f, Real.sq_sqrt hwi]
  have hg_sq :
      (∑ i ∈ s, g i ^ 2) = ∑ i ∈ s, w i * x i ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hwi : 0 ≤ w i := hw i hi
    calc
      g i ^ 2 = (Real.sqrt (w i)) ^ 2 * x i ^ 2 := by
        simp [g, mul_pow]
      _ = w i * x i ^ 2 := by rw [Real.sq_sqrt hwi]
  let B : ℝ :=
    Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2)
  have hsum_le : (∑ i ∈ s, f i * g i) ≤ B :=
    Real.sum_mul_le_sqrt_mul_sqrt s f g
  have hneg_le : -(∑ i ∈ s, f i * g i) ≤ B := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt s f (fun i => -g i)
    simpa [B, Finset.sum_neg_distrib] using h
  have habs_le : |∑ i ∈ s, f i * g i| ≤ B := by
    exact abs_le.mpr ⟨by linarith, hsum_le⟩
  have hB_nonneg : 0 ≤ B := by positivity
  have hsquare :
      (∑ i ∈ s, f i * g i) ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hB_nonneg] using habs_le)
  have hB_sq :
      B ^ 2 =
        (∑ i ∈ s, w i) * (∑ i ∈ s, w i * x i ^ 2) := by
    have hf_nonneg : 0 ≤ ∑ i ∈ s, f i ^ 2 :=
      Finset.sum_nonneg fun i hi => sq_nonneg (f i)
    have hg_nonneg : 0 ≤ ∑ i ∈ s, g i ^ 2 :=
      Finset.sum_nonneg fun i hi => sq_nonneg (g i)
    calc
      B ^ 2 =
          (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) := by
            simp [B, mul_pow, Real.sq_sqrt hf_nonneg, Real.sq_sqrt hg_nonneg]
      _ = (∑ i ∈ s, w i) * (∑ i ∈ s, w i * x i ^ 2) := by
            rw [hf_sq, hg_sq]
  simpa [hfg, hB_sq] using hsquare

/-- Finite Schur test for nonnegative kernels.

If every row has mass at most `A` and every column has mass at most `B`, then
the kernel operator has squared `L^2` norm at most `A * B`. -/
theorem finite_schur_l2_bound {α β : Type*}
    (I : Finset α) (J : Finset β) (K : α → β → ℝ) (x : β → ℝ)
    (A B : ℝ)
    (hK_nonneg : ∀ i, i ∈ I → ∀ j, j ∈ J → 0 ≤ K i j)
    (hrow : ∀ i, i ∈ I → (∑ j ∈ J, K i j) ≤ A)
    (hcol : ∀ j, j ∈ J → (∑ i ∈ I, K i j) ≤ B)
    (hA : 0 ≤ A) :
    (∑ i ∈ I, (∑ j ∈ J, K i j * x j) ^ 2) ≤
      A * B * (∑ j ∈ J, x j ^ 2) := by
  have hpoint :
      ∀ i, i ∈ I →
        (∑ j ∈ J, K i j * x j) ^ 2 ≤
          A * (∑ j ∈ J, K i j * x j ^ 2) := by
    intro i hi
    have hcs :=
      sq_sum_mul_le_sum_mul_sq_of_nonneg J (fun j => K i j) x
        (fun j hj => hK_nonneg i hi j hj)
    have henergy_nonneg : 0 ≤ ∑ j ∈ J, K i j * x j ^ 2 := by
      refine Finset.sum_nonneg ?_
      intro j hj
      exact mul_nonneg (hK_nonneg i hi j hj) (sq_nonneg (x j))
    calc
      (∑ j ∈ J, K i j * x j) ^ 2
          ≤ (∑ j ∈ J, K i j) * (∑ j ∈ J, K i j * x j ^ 2) := hcs
      _ ≤ A * (∑ j ∈ J, K i j * x j ^ 2) :=
          mul_le_mul_of_nonneg_right (hrow i hi) henergy_nonneg
  calc
    (∑ i ∈ I, (∑ j ∈ J, K i j * x j) ^ 2)
        ≤ ∑ i ∈ I, A * (∑ j ∈ J, K i j * x j ^ 2) := by
          exact Finset.sum_le_sum fun i hi => hpoint i hi
    _ = A * (∑ i ∈ I, ∑ j ∈ J, K i j * x j ^ 2) := by
          rw [Finset.mul_sum]
    _ = A * (∑ j ∈ J, ∑ i ∈ I, K i j * x j ^ 2) := by
          rw [Finset.sum_comm]
    _ = A * (∑ j ∈ J, (∑ i ∈ I, K i j) * x j ^ 2) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Finset.sum_mul]
    _ ≤ A * (∑ j ∈ J, B * x j ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hA
          exact Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg (x j))
    _ = A * (B * ∑ j ∈ J, x j ^ 2) := by
          rw [← Finset.mul_sum]
    _ = A * B * (∑ j ∈ J, x j ^ 2) := by ring

/-- Elementary square bound for splitting a main term and an error term. -/
theorem sq_add_le_two_sq_add_two_sq (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

/-- Finite Schur test with an additive error vector.

If `h_i = sum_j K_ij x_j + e_i`, then the output energy is bounded by twice
the Schur energy plus twice the error energy. -/
theorem finite_schur_l2_bound_add_error {α β : Type*}
    (I : Finset α) (J : Finset β) (K : α → β → ℝ) (x : β → ℝ)
    (e : α → ℝ) (A B : ℝ)
    (hK_nonneg : ∀ i, i ∈ I → ∀ j, j ∈ J → 0 ≤ K i j)
    (hrow : ∀ i, i ∈ I → (∑ j ∈ J, K i j) ≤ A)
    (hcol : ∀ j, j ∈ J → (∑ i ∈ I, K i j) ≤ B)
    (hA : 0 ≤ A) :
    (∑ i ∈ I, ((∑ j ∈ J, K i j * x j) + e i) ^ 2) ≤
      2 * (A * B * (∑ j ∈ J, x j ^ 2)) +
        2 * (∑ i ∈ I, e i ^ 2) := by
  have hpoint :
      ∀ i ∈ I,
        ((∑ j ∈ J, K i j * x j) + e i) ^ 2 ≤
          2 * (∑ j ∈ J, K i j * x j) ^ 2 + 2 * e i ^ 2 := by
    intro i _hi
    exact sq_add_le_two_sq_add_two_sq _ _
  calc
    (∑ i ∈ I, ((∑ j ∈ J, K i j * x j) + e i) ^ 2)
        ≤ ∑ i ∈ I,
            (2 * (∑ j ∈ J, K i j * x j) ^ 2 + 2 * e i ^ 2) := by
          exact Finset.sum_le_sum fun i hi => hpoint i hi
    _ =
        2 * (∑ i ∈ I, (∑ j ∈ J, K i j * x j) ^ 2) +
          2 * (∑ i ∈ I, e i ^ 2) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤
        2 * (A * B * (∑ j ∈ J, x j ^ 2)) +
          2 * (∑ i ∈ I, e i ^ 2) := by
          gcongr
          exact finite_schur_l2_bound I J K x A B hK_nonneg hrow hcol hA

/-- Symmetric finite Schur test when the same mass bound controls rows and
columns. -/
theorem finite_schur_l2_bound_uniform {α β : Type*}
    (I : Finset α) (J : Finset β) (K : α → β → ℝ) (x : β → ℝ)
    (C : ℝ)
    (hK_nonneg : ∀ i, i ∈ I → ∀ j, j ∈ J → 0 ≤ K i j)
    (hrow : ∀ i, i ∈ I → (∑ j ∈ J, K i j) ≤ C)
    (hcol : ∀ j, j ∈ J → (∑ i ∈ I, K i j) ≤ C)
    (hC : 0 ≤ C) :
    (∑ i ∈ I, (∑ j ∈ J, K i j * x j) ^ 2) ≤
      C ^ 2 * (∑ j ∈ J, x j ^ 2) := by
  have h :=
    finite_schur_l2_bound I J K x C C hK_nonneg hrow hcol hC
  simpa [pow_two, mul_assoc] using h

/-- Any finite sub-sum of a nonnegative geometric series is bounded by its
infinite sum. -/
theorem finite_geometric_sum_le_inv_one_sub
    (rho : ℝ) (s : Finset ℕ)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) :
    (∑ k ∈ s, rho ^ k) ≤ (1 - rho)⁻¹ := by
  calc
    (∑ k ∈ s, rho ^ k) ≤ ∑' k : ℕ, rho ^ k :=
      (summable_geometric_of_lt_one hrho_nonneg hrho_lt_one).sum_le_tsum s
        (fun k _hk => pow_nonneg hrho_nonneg k)
    _ = (1 - rho)⁻¹ := tsum_geometric_of_lt_one hrho_nonneg hrho_lt_one

/-- Schur bound with the row and column masses bounded by the full geometric
series with ratio `rho`.  This is the finite operator estimate expected after
discretizing the backward dyadic recurrence. -/
theorem finite_schur_l2_bound_geometric_mass {α β : Type*}
    (I : Finset α) (J : Finset β) (K : α → β → ℝ) (x : β → ℝ)
    (rho : ℝ)
    (hK_nonneg : ∀ i, i ∈ I → ∀ j, j ∈ J → 0 ≤ K i j)
    (hrow : ∀ i, i ∈ I → (∑ j ∈ J, K i j) ≤ (1 - rho)⁻¹)
    (hcol : ∀ j, j ∈ J → (∑ i ∈ I, K i j) ≤ (1 - rho)⁻¹)
    (hrho_lt_one : rho < 1) :
    (∑ i ∈ I, (∑ j ∈ J, K i j * x j) ^ 2) ≤
      ((1 - rho)⁻¹) ^ 2 * (∑ j ∈ J, x j ^ 2) := by
  have hmass_nonneg : 0 ≤ (1 - rho)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hrho_lt_one.le)
  exact
    finite_schur_l2_bound_uniform I J K x ((1 - rho)⁻¹)
      hK_nonneg hrow hcol hmass_nonneg

/-- The dyadic backward recurrence has geometric ratio `1 / sqrt(2)`. -/
theorem dyadicTransferRatio_nonneg :
    0 ≤ (Real.sqrt 2)⁻¹ := by
  positivity

/-- The dyadic backward recurrence ratio is strictly below one. -/
theorem dyadicTransferRatio_lt_one :
    (Real.sqrt 2)⁻¹ < 1 := by
  have hsqrt_gt : 1 < Real.sqrt (2 : ℝ) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (2 : ℝ) := Real.sqrt_lt_sqrt zero_le_one (by norm_num)
  exact inv_lt_one_of_one_lt₀ hsqrt_gt

/-- Schur bound specialized to the dyadic backward-recurrence ratio
`2^(-1/2)`. -/
theorem finite_schur_l2_bound_dyadic_mass {α β : Type*}
    (I : Finset α) (J : Finset β) (K : α → β → ℝ) (x : β → ℝ)
    (hK_nonneg : ∀ i, i ∈ I → ∀ j, j ∈ J → 0 ≤ K i j)
    (hrow : ∀ i, i ∈ I → (∑ j ∈ J, K i j) ≤ (1 - (Real.sqrt 2)⁻¹)⁻¹)
    (hcol : ∀ j, j ∈ J → (∑ i ∈ I, K i j) ≤ (1 - (Real.sqrt 2)⁻¹)⁻¹) :
    (∑ i ∈ I, (∑ j ∈ J, K i j * x j) ^ 2) ≤
      ((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2 * (∑ j ∈ J, x j ^ 2) :=
  finite_schur_l2_bound_geometric_mass I J K x (Real.sqrt 2)⁻¹
    hK_nonneg hrow hcol dyadicTransferRatio_lt_one

/-- Row mass bound for the finite backward geometric kernel
`1_{i <= j} rho^(j-i)` on a finite range. -/
theorem finite_backward_geometric_row_mass_le
    (rho : ℝ) (n i : ℕ)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) :
    (∑ j ∈ Finset.range n, if i ≤ j then rho ^ (j - i) else 0) ≤
      (1 - rho)⁻¹ := by
  by_cases hin : i ≤ n
  · have hfirst :
        (∑ j ∈ Finset.range i, if i ≤ j then rho ^ (j - i) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hji : j < i := by simpa using hj
      simp [Nat.not_le_of_lt hji]
    calc
      (∑ j ∈ Finset.range n, if i ≤ j then rho ^ (j - i) else 0)
          = ∑ j ∈ Finset.range (i + (n - i)), if i ≤ j then rho ^ (j - i) else 0 := by
            rw [Nat.add_sub_of_le hin]
      _ = (∑ j ∈ Finset.range i, if i ≤ j then rho ^ (j - i) else 0) +
            ∑ k ∈ Finset.range (n - i),
              (if i ≤ i + k then rho ^ (i + k - i) else 0) := by
            rw [Finset.sum_range_add]
      _ = ∑ k ∈ Finset.range (n - i), rho ^ k := by
            rw [hfirst]
            simp
      _ ≤ (1 - rho)⁻¹ :=
            finite_geometric_sum_le_inv_one_sub rho (Finset.range (n - i))
              hrho_nonneg hrho_lt_one
  · have hnle : n ≤ i := le_of_not_ge hin
    have hsum :
        (∑ j ∈ Finset.range n, if i ≤ j then rho ^ (j - i) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hjn : j < n := by simpa using hj
      have hji : j < i := lt_of_lt_of_le hjn hnle
      simp [Nat.not_le_of_lt hji]
    have hmass_nonneg : 0 ≤ (1 - rho)⁻¹ := by
      exact inv_nonneg.mpr (sub_nonneg.mpr hrho_lt_one.le)
    simpa [hsum] using hmass_nonneg

/-- Column mass bound for the finite backward geometric kernel
`1_{i <= j} rho^(j-i)` on a finite range. -/
theorem finite_backward_geometric_col_mass_le
    (rho : ℝ) (n j : ℕ)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) :
    (∑ i ∈ Finset.range n, if i ≤ j then rho ^ (j - i) else 0) ≤
      (1 - rho)⁻¹ := by
  by_cases hle : j + 1 ≤ n
  · have htail :
        (∑ k ∈ Finset.range (n - (j + 1)),
          (if (j + 1) + k ≤ j then rho ^ (j - ((j + 1) + k)) else 0)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k _hk
      have hnot : ¬ (j + 1) + k ≤ j := by omega
      simp [hnot]
    have hhead :
        (∑ i ∈ Finset.range (j + 1), if i ≤ j then rho ^ (j - i) else 0) =
          ∑ i ∈ Finset.range (j + 1), rho ^ (j - i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hij : i ≤ j := Nat.le_of_lt_succ (by simpa using hi)
      simp [hij]
    calc
      (∑ i ∈ Finset.range n, if i ≤ j then rho ^ (j - i) else 0)
          = (∑ i ∈ Finset.range (j + 1), if i ≤ j then rho ^ (j - i) else 0) +
            ∑ k ∈ Finset.range (n - (j + 1)),
              (if (j + 1) + k ≤ j then rho ^ (j - ((j + 1) + k)) else 0) := by
            conv_lhs => rw [← Nat.add_sub_of_le hle]
            rw [Finset.sum_range_add]
      _ = ∑ i ∈ Finset.range (j + 1), rho ^ (j - i) := by
            rw [htail, hhead]
            simp
      _ = ∑ k ∈ Finset.range (j + 1), rho ^ k := by
            simpa using (Finset.sum_range_reflect (fun k => rho ^ k) (j + 1))
      _ ≤ (1 - rho)⁻¹ :=
            finite_geometric_sum_le_inv_one_sub rho (Finset.range (j + 1))
              hrho_nonneg hrho_lt_one
  · have hnle : n ≤ j + 1 := le_of_not_ge hle
    have hterms : ∀ i ∈ Finset.range n, i ≤ j := by
      intro i hi
      have hin : i < n := by simpa using hi
      omega
    calc
      (∑ i ∈ Finset.range n, if i ≤ j then rho ^ (j - i) else 0)
          = ∑ i ∈ Finset.range n, rho ^ (j - i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [hterms i hi]
      _ ≤ ∑ i ∈ Finset.range (j + 1), rho ^ (j - i) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?subset ?nonneg
            · intro i hi
              have hin : i < n := by simpa using hi
              simp [lt_of_lt_of_le hin hnle]
            · intro i _hi_big _hi_not
              exact pow_nonneg hrho_nonneg (j - i)
      _ = ∑ k ∈ Finset.range (j + 1), rho ^ k := by
            simpa using (Finset.sum_range_reflect (fun k => rho ^ k) (j + 1))
      _ ≤ (1 - rho)⁻¹ :=
            finite_geometric_sum_le_inv_one_sub rho (Finset.range (j + 1))
              hrho_nonneg hrho_lt_one

/-- Finite Schur estimate for the explicit backward geometric kernel
`1_{i <= j} rho^(j-i)` on `range n`. -/
theorem finite_backward_geometric_schur_l2_bound_range
    (rho : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) :
    (∑ i ∈ Finset.range n,
        (∑ j ∈ Finset.range n,
          (if i ≤ j then rho ^ (j - i) else 0) * x j) ^ 2) ≤
      ((1 - rho)⁻¹) ^ 2 * (∑ j ∈ Finset.range n, x j ^ 2) := by
  refine
    finite_schur_l2_bound_geometric_mass (Finset.range n) (Finset.range n)
      (fun i j => if i ≤ j then rho ^ (j - i) else 0) x rho ?hK ?hrow
      ?hcol hrho_lt_one
  · intro i _hi j _hj
    by_cases hij : i ≤ j
    · simp [hij, pow_nonneg hrho_nonneg]
    · simp [hij]
  · intro i _hi
    exact finite_backward_geometric_row_mass_le rho n i hrho_nonneg hrho_lt_one
  · intro j _hj
    exact finite_backward_geometric_col_mass_le rho n j hrho_nonneg hrho_lt_one

/-- Finite Schur estimate with additive error for the explicit backward
geometric kernel on `range n`. -/
theorem finite_backward_geometric_schur_l2_bound_range_add_error
    (rho : ℝ) (n : ℕ) (x e : ℕ → ℝ)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) :
    (∑ i ∈ Finset.range n,
        ((∑ j ∈ Finset.range n,
          (if i ≤ j then rho ^ (j - i) else 0) * x j) + e i) ^ 2) ≤
      2 * (((1 - rho)⁻¹) ^ 2 * (∑ j ∈ Finset.range n, x j ^ 2)) +
        2 * (∑ i ∈ Finset.range n, e i ^ 2) := by
  have hK :
      ∀ i, i ∈ Finset.range n → ∀ j, j ∈ Finset.range n →
        0 ≤ (fun i j => if i ≤ j then rho ^ (j - i) else 0) i j := by
    intro i _hi j _hj
    by_cases hij : i ≤ j
    · simp [hij, pow_nonneg hrho_nonneg]
    · simp [hij]
  have hrow :
      ∀ i, i ∈ Finset.range n →
        (∑ j ∈ Finset.range n,
          (fun i j => if i ≤ j then rho ^ (j - i) else 0) i j) ≤
          (1 - rho)⁻¹ := by
    intro i _hi
    exact finite_backward_geometric_row_mass_le rho n i hrho_nonneg hrho_lt_one
  have hcol :
      ∀ j, j ∈ Finset.range n →
        (∑ i ∈ Finset.range n,
          (fun i j => if i ≤ j then rho ^ (j - i) else 0) i j) ≤
          (1 - rho)⁻¹ := by
    intro j _hj
    exact finite_backward_geometric_col_mass_le rho n j hrho_nonneg hrho_lt_one
  have hA : 0 ≤ (1 - rho)⁻¹ := by
    exact inv_nonneg.mpr (sub_nonneg.mpr hrho_lt_one.le)
  have h :=
    finite_schur_l2_bound_add_error (Finset.range n) (Finset.range n)
      (fun i j => if i ≤ j then rho ^ (j - i) else 0) x e
      ((1 - rho)⁻¹) ((1 - rho)⁻¹) hK hrow hcol hA
  simpa [pow_two, mul_assoc] using h

/-- Finite Schur estimate for the explicit backward dyadic kernel on
`range n`. -/
theorem finite_backward_dyadic_schur_l2_bound_range
    (n : ℕ) (x : ℕ → ℝ) :
    (∑ i ∈ Finset.range n,
        (∑ j ∈ Finset.range n,
          (if i ≤ j then (Real.sqrt 2)⁻¹ ^ (j - i) else 0) * x j) ^ 2) ≤
      ((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2 *
        (∑ j ∈ Finset.range n, x j ^ 2) :=
  finite_backward_geometric_schur_l2_bound_range (Real.sqrt 2)⁻¹ n x
    dyadicTransferRatio_nonneg dyadicTransferRatio_lt_one

/-- Finite Schur estimate with additive error for the explicit backward dyadic
kernel on `range n`. -/
theorem finite_backward_dyadic_schur_l2_bound_range_add_error
    (n : ℕ) (x e : ℕ → ℝ) :
    (∑ i ∈ Finset.range n,
        ((∑ j ∈ Finset.range n,
          (if i ≤ j then (Real.sqrt 2)⁻¹ ^ (j - i) else 0) * x j) +
            e i) ^ 2) ≤
      2 * (((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2 *
          (∑ j ∈ Finset.range n, x j ^ 2)) +
        2 * (∑ i ∈ Finset.range n, e i ^ 2) :=
  finite_backward_geometric_schur_l2_bound_range_add_error (Real.sqrt 2)⁻¹ n
    x e dyadicTransferRatio_nonneg dyadicTransferRatio_lt_one

/-- Scalar energy-transfer conclusion after a finite Schur estimate.

If endpoint energy `H` is at most `C^2 * D + boundary`, while Harper-style
inputs give `H >= endpointFloor` and the boundary costs at most half of that
floor, then the dyadic energy `D` inherits the lower bound
`endpointFloor / (2*C^2)`. -/
theorem dyadicEnergy_lower_of_endpointEnergy_upper
    (H D boundary C endpointFloor : ℝ)
    (hC_pos : 0 < C)
    (hupper : H ≤ C ^ 2 * D + boundary)
    (hlower : endpointFloor ≤ H)
    (hboundary : boundary ≤ endpointFloor / 2) :
    endpointFloor / (2 * C ^ 2) ≤ D := by
  have hC_sq_pos : 0 < C ^ 2 := sq_pos_of_pos hC_pos
  have hhalf : endpointFloor / 2 ≤ C ^ 2 * D := by
    linarith
  calc
    endpointFloor / (2 * C ^ 2) = (endpointFloor / 2) / C ^ 2 := by ring
    _ ≤ D := by
      rw [div_le_iff₀ hC_sq_pos]
      rwa [mul_comm]

/-- Scalar energy-transfer conclusion after a Schur estimate with an additive
error vector.

If endpoint energy `H` is at most `2*C^2*D + 2*errorEnergy`, while
`H >= endpointFloor` and the error energy costs at most a quarter of that
floor, then the dyadic energy `D` inherits the lower bound
`endpointFloor / (4*C^2)`. -/
theorem dyadicEnergy_lower_of_endpointEnergy_add_error_upper
    (H D errorEnergy C endpointFloor : ℝ)
    (hC_pos : 0 < C)
    (hupper : H ≤ 2 * (C ^ 2 * D) + 2 * errorEnergy)
    (hlower : endpointFloor ≤ H)
    (herror : errorEnergy ≤ endpointFloor / 4) :
    endpointFloor / (4 * C ^ 2) ≤ D := by
  have hC_sq_pos : 0 < C ^ 2 := sq_pos_of_pos hC_pos
  have hquarter : endpointFloor / 4 ≤ C ^ 2 * D := by
    linarith
  calc
    endpointFloor / (4 * C ^ 2) = (endpointFloor / 4) / C ^ 2 := by ring
    _ ≤ D := by
      rw [div_le_iff₀ hC_sq_pos]
      rwa [mul_comm]

/-- Scalar energy-transfer conclusion when the Schur mass is the full
geometric mass `(1-rho)^-1`. -/
theorem dyadicEnergy_lower_of_geometric_endpointEnergy_upper
    (H D boundary rho endpointFloor : ℝ)
    (hrho_lt_one : rho < 1)
    (hupper : H ≤ ((1 - rho)⁻¹) ^ 2 * D + boundary)
    (hlower : endpointFloor ≤ H)
    (hboundary : boundary ≤ endpointFloor / 2) :
    endpointFloor / (2 * ((1 - rho)⁻¹) ^ 2) ≤ D := by
  have hC_pos : 0 < (1 - rho)⁻¹ := by
    exact inv_pos.mpr (sub_pos.mpr hrho_lt_one)
  exact
    dyadicEnergy_lower_of_endpointEnergy_upper H D boundary ((1 - rho)⁻¹)
      endpointFloor hC_pos hupper hlower hboundary

/-- Scalar energy-transfer conclusion with additive error when the Schur mass
is the full geometric mass `(1-rho)^-1`. -/
theorem dyadicEnergy_lower_of_geometric_endpointEnergy_add_error_upper
    (H D errorEnergy rho endpointFloor : ℝ)
    (hrho_lt_one : rho < 1)
    (hupper : H ≤
      2 * (((1 - rho)⁻¹) ^ 2 * D) + 2 * errorEnergy)
    (hlower : endpointFloor ≤ H)
    (herror : errorEnergy ≤ endpointFloor / 4) :
    endpointFloor / (4 * ((1 - rho)⁻¹) ^ 2) ≤ D := by
  have hC_pos : 0 < (1 - rho)⁻¹ := by
    exact inv_pos.mpr (sub_pos.mpr hrho_lt_one)
  exact
    dyadicEnergy_lower_of_endpointEnergy_add_error_upper H D errorEnergy
      ((1 - rho)⁻¹) endpointFloor hC_pos hupper hlower herror

/-- Scalar energy-transfer conclusion for the actual backward dyadic ratio
`rho = 1/sqrt(2)`. -/
theorem dyadicEnergy_lower_of_dyadic_endpointEnergy_upper
    (H D boundary endpointFloor : ℝ)
    (hupper : H ≤ ((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2 * D + boundary)
    (hlower : endpointFloor ≤ H)
    (hboundary : boundary ≤ endpointFloor / 2) :
    endpointFloor / (2 * ((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2) ≤ D :=
  dyadicEnergy_lower_of_geometric_endpointEnergy_upper H D boundary
    (Real.sqrt 2)⁻¹ endpointFloor dyadicTransferRatio_lt_one
    hupper hlower hboundary

/-- Scalar energy-transfer conclusion with additive error for the actual
backward dyadic ratio `rho = 1/sqrt(2)`. -/
theorem dyadicEnergy_lower_of_dyadic_endpointEnergy_add_error_upper
    (H D errorEnergy endpointFloor : ℝ)
    (hupper : H ≤
      2 * (((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2 * D) + 2 * errorEnergy)
    (hlower : endpointFloor ≤ H)
    (herror : errorEnergy ≤ endpointFloor / 4) :
    endpointFloor / (4 * ((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2) ≤ D :=
  dyadicEnergy_lower_of_geometric_endpointEnergy_add_error_upper H D errorEnergy
    (Real.sqrt 2)⁻¹ endpointFloor dyadicTransferRatio_lt_one hupper hlower
    herror

/-- Paper-facing geometric dyadic-transfer wrapper.

If a finite endpoint-energy vector `h` satisfies the backward geometric
recurrence `h_i = sum_{j >= i} rho^(j-i) x_j + e_i` on `range n`, and the
endpoint energy has a floor while the error energy costs at most a quarter of
that floor, then the dyadic-increment energy `sum x_j^2` inherits the
corresponding lower bound. -/
theorem dyadicEnergy_lower_of_backward_geometric_recurrence_add_error
    (rho : ℝ) (n : ℕ) (h x e : ℕ → ℝ) (endpointFloor : ℝ)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1)
    (hrec : ∀ i, i ∈ Finset.range n →
      h i = (∑ j ∈ Finset.range n,
        (if i ≤ j then rho ^ (j - i) else 0) * x j) + e i)
    (hlower : endpointFloor ≤ ∑ i ∈ Finset.range n, h i ^ 2)
    (herror : (∑ i ∈ Finset.range n, e i ^ 2) ≤ endpointFloor / 4) :
    endpointFloor / (4 * ((1 - rho)⁻¹) ^ 2) ≤
      ∑ j ∈ Finset.range n, x j ^ 2 := by
  have hupper_expr :=
    finite_backward_geometric_schur_l2_bound_range_add_error rho n x e
      hrho_nonneg hrho_lt_one
  have hrewrite :
      (∑ i ∈ Finset.range n, h i ^ 2) =
        ∑ i ∈ Finset.range n,
          ((∑ j ∈ Finset.range n,
            (if i ≤ j then rho ^ (j - i) else 0) * x j) + e i) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hrec i hi]
  have hupper :
      (∑ i ∈ Finset.range n, h i ^ 2) ≤
        2 * (((1 - rho)⁻¹) ^ 2 * (∑ j ∈ Finset.range n, x j ^ 2)) +
          2 * (∑ i ∈ Finset.range n, e i ^ 2) := by
    simpa [hrewrite] using hupper_expr
  exact
    dyadicEnergy_lower_of_geometric_endpointEnergy_add_error_upper
      (∑ i ∈ Finset.range n, h i ^ 2)
      (∑ j ∈ Finset.range n, x j ^ 2)
      (∑ i ∈ Finset.range n, e i ^ 2)
      rho endpointFloor hrho_lt_one hupper hlower herror

/-- Paper-facing dyadic-transfer wrapper for the actual backward dyadic ratio
`rho = 1/sqrt(2)`. -/
theorem dyadicEnergy_lower_of_backward_dyadic_recurrence_add_error
    (n : ℕ) (h x e : ℕ → ℝ) (endpointFloor : ℝ)
    (hrec : ∀ i, i ∈ Finset.range n →
      h i = (∑ j ∈ Finset.range n,
        (if i ≤ j then (Real.sqrt 2)⁻¹ ^ (j - i) else 0) * x j) + e i)
    (hlower : endpointFloor ≤ ∑ i ∈ Finset.range n, h i ^ 2)
    (herror : (∑ i ∈ Finset.range n, e i ^ 2) ≤ endpointFloor / 4) :
    endpointFloor / (4 * ((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2) ≤
      ∑ j ∈ Finset.range n, x j ^ 2 :=
  dyadicEnergy_lower_of_backward_geometric_recurrence_add_error
    (Real.sqrt 2)⁻¹ n h x e endpointFloor dyadicTransferRatio_nonneg
    dyadicTransferRatio_lt_one hrec hlower herror

/-- Paper-facing geometric dyadic-transfer wrapper for an exact finite
backward recurrence with no additive error. -/
theorem dyadicEnergy_lower_of_backward_geometric_recurrence
    (rho : ℝ) (n : ℕ) (h x : ℕ → ℝ) (endpointFloor : ℝ)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1)
    (hfloor_nonneg : 0 ≤ endpointFloor)
    (hrec : ∀ i, i ∈ Finset.range n →
      h i = ∑ j ∈ Finset.range n,
        (if i ≤ j then rho ^ (j - i) else 0) * x j)
    (hlower : endpointFloor ≤ ∑ i ∈ Finset.range n, h i ^ 2) :
    endpointFloor / (2 * ((1 - rho)⁻¹) ^ 2) ≤
      ∑ j ∈ Finset.range n, x j ^ 2 := by
  have hupper_expr :=
    finite_backward_geometric_schur_l2_bound_range rho n x hrho_nonneg
      hrho_lt_one
  have hrewrite :
      (∑ i ∈ Finset.range n, h i ^ 2) =
        ∑ i ∈ Finset.range n,
          (∑ j ∈ Finset.range n,
            (if i ≤ j then rho ^ (j - i) else 0) * x j) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hrec i hi]
  have hupper :
      (∑ i ∈ Finset.range n, h i ^ 2) ≤
        ((1 - rho)⁻¹) ^ 2 * (∑ j ∈ Finset.range n, x j ^ 2) := by
    simpa [hrewrite] using hupper_expr
  exact
    dyadicEnergy_lower_of_geometric_endpointEnergy_upper
      (∑ i ∈ Finset.range n, h i ^ 2)
      (∑ j ∈ Finset.range n, x j ^ 2)
      0 rho endpointFloor hrho_lt_one (by simpa using hupper) hlower
      (by linarith)

/-- Paper-facing dyadic-transfer wrapper for the exact backward recurrence
with ratio `rho = 1/sqrt(2)` and no additive error. -/
theorem dyadicEnergy_lower_of_backward_dyadic_recurrence
    (n : ℕ) (h x : ℕ → ℝ) (endpointFloor : ℝ)
    (hfloor_nonneg : 0 ≤ endpointFloor)
    (hrec : ∀ i, i ∈ Finset.range n →
      h i = ∑ j ∈ Finset.range n,
        (if i ≤ j then (Real.sqrt 2)⁻¹ ^ (j - i) else 0) * x j)
    (hlower : endpointFloor ≤ ∑ i ∈ Finset.range n, h i ^ 2) :
    endpointFloor / (2 * ((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2) ≤
      ∑ j ∈ Finset.range n, x j ^ 2 :=
  dyadicEnergy_lower_of_backward_geometric_recurrence (Real.sqrt 2)⁻¹ n h x
    endpointFloor dyadicTransferRatio_nonneg dyadicTransferRatio_lt_one
    hfloor_nonneg hrec hlower

/-- Packaged analytic handoff for a finite backward-geometric dyadic-energy
transfer with an additive error vector.

The paper-side input is deliberately minimal: a finite recurrence, an endpoint
energy floor, and an error-energy budget.  The conclusion is the inherited
dyadic-increment energy floor. -/
structure BackwardGeometricEnergyTransferCertificate where
  rho : ℝ
  n : ℕ
  h : ℕ → ℝ
  x : ℕ → ℝ
  e : ℕ → ℝ
  endpointFloor : ℝ
  rho_nonneg : 0 ≤ rho
  rho_lt_one : rho < 1
  recurrence :
    ∀ i, i ∈ Finset.range n →
      h i = (∑ j ∈ Finset.range n,
        (if i ≤ j then rho ^ (j - i) else 0) * x j) + e i
  endpoint_floor : endpointFloor ≤ ∑ i ∈ Finset.range n, h i ^ 2
  error_budget : (∑ i ∈ Finset.range n, e i ^ 2) ≤ endpointFloor / 4

/-- Certificate-local conclusion for finite backward-geometric dyadic-energy
transfer with additive error. -/
theorem BackwardGeometricEnergyTransferCertificate.dyadicEnergy_lower
    (c : BackwardGeometricEnergyTransferCertificate) :
    c.endpointFloor / (4 * ((1 - c.rho)⁻¹) ^ 2) ≤
      ∑ j ∈ Finset.range c.n, c.x j ^ 2 :=
  dyadicEnergy_lower_of_backward_geometric_recurrence_add_error
    c.rho c.n c.h c.x c.e c.endpointFloor c.rho_nonneg c.rho_lt_one
    c.recurrence c.endpoint_floor c.error_budget

/-- Packaged analytic handoff for the actual finite backward-dyadic recurrence
with ratio `1 / sqrt(2)` and an additive error vector. -/
structure BackwardDyadicEnergyTransferCertificate where
  n : ℕ
  h : ℕ → ℝ
  x : ℕ → ℝ
  e : ℕ → ℝ
  endpointFloor : ℝ
  recurrence :
    ∀ i, i ∈ Finset.range n →
      h i = (∑ j ∈ Finset.range n,
        (if i ≤ j then (Real.sqrt 2)⁻¹ ^ (j - i) else 0) * x j) + e i
  endpoint_floor : endpointFloor ≤ ∑ i ∈ Finset.range n, h i ^ 2
  error_budget : (∑ i ∈ Finset.range n, e i ^ 2) ≤ endpointFloor / 4

/-- Certificate-local conclusion for the actual finite backward-dyadic
energy-transfer handoff with additive error. -/
theorem BackwardDyadicEnergyTransferCertificate.dyadicEnergy_lower
    (c : BackwardDyadicEnergyTransferCertificate) :
    c.endpointFloor / (4 * ((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2) ≤
      ∑ j ∈ Finset.range c.n, c.x j ^ 2 :=
  dyadicEnergy_lower_of_backward_dyadic_recurrence_add_error
    c.n c.h c.x c.e c.endpointFloor c.recurrence c.endpoint_floor c.error_budget

/-- Packaged analytic handoff for an exact finite backward-geometric
dyadic-energy transfer, with no additive error vector. -/
structure ExactBackwardGeometricEnergyTransferCertificate where
  rho : ℝ
  n : ℕ
  h : ℕ → ℝ
  x : ℕ → ℝ
  endpointFloor : ℝ
  rho_nonneg : 0 ≤ rho
  rho_lt_one : rho < 1
  endpointFloor_nonneg : 0 ≤ endpointFloor
  recurrence :
    ∀ i, i ∈ Finset.range n →
      h i = ∑ j ∈ Finset.range n,
        (if i ≤ j then rho ^ (j - i) else 0) * x j
  endpoint_floor : endpointFloor ≤ ∑ i ∈ Finset.range n, h i ^ 2

/-- Certificate-local conclusion for exact finite backward-geometric
dyadic-energy transfer. -/
theorem ExactBackwardGeometricEnergyTransferCertificate.dyadicEnergy_lower
    (c : ExactBackwardGeometricEnergyTransferCertificate) :
    c.endpointFloor / (2 * ((1 - c.rho)⁻¹) ^ 2) ≤
      ∑ j ∈ Finset.range c.n, c.x j ^ 2 :=
  dyadicEnergy_lower_of_backward_geometric_recurrence c.rho c.n c.h c.x
    c.endpointFloor c.rho_nonneg c.rho_lt_one c.endpointFloor_nonneg
    c.recurrence c.endpoint_floor

/-- Packaged analytic handoff for the exact finite backward-dyadic recurrence
with ratio `1 / sqrt(2)`. -/
structure ExactBackwardDyadicEnergyTransferCertificate where
  n : ℕ
  h : ℕ → ℝ
  x : ℕ → ℝ
  endpointFloor : ℝ
  endpointFloor_nonneg : 0 ≤ endpointFloor
  recurrence :
    ∀ i, i ∈ Finset.range n →
      h i = ∑ j ∈ Finset.range n,
        (if i ≤ j then (Real.sqrt 2)⁻¹ ^ (j - i) else 0) * x j
  endpoint_floor : endpointFloor ≤ ∑ i ∈ Finset.range n, h i ^ 2

/-- Certificate-local conclusion for exact finite backward-dyadic
energy-transfer. -/
theorem ExactBackwardDyadicEnergyTransferCertificate.dyadicEnergy_lower
    (c : ExactBackwardDyadicEnergyTransferCertificate) :
    c.endpointFloor / (2 * ((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2) ≤
      ∑ j ∈ Finset.range c.n, c.x j ^ 2 :=
  dyadicEnergy_lower_of_backward_dyadic_recurrence c.n c.h c.x c.endpointFloor
    c.endpointFloor_nonneg c.recurrence c.endpoint_floor

end Problem1144
end Erdos
