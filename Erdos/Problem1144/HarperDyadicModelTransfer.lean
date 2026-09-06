import Erdos.Problem1144.HarperDyadicTransfer
import Erdos.Problem1144.Statistics

open scoped BigOperators

namespace Erdos
namespace Problem1144

/-!
# Exact dyadic recurrence for the Problem 1144 summatory function

This file instantiates the deterministic dyadic-transfer workbench on the
actual completely multiplicative model.  On the exact mesh `N_i = base * 2^i`,
the normalized endpoint and normalized dyadic increment satisfy the stable
one-step recurrence with ratio `1 / sqrt 2`; there is no discretization or
rounding error.
-/

/-- The normalized endpoint on the exact dyadic mesh `base * 2^i`. -/
noncomputable def dyadicNormalizedEndpoint
    (omega : Omega) (base i : ℕ) : ℝ :=
  S omega (base * 2 ^ i) / Real.sqrt (((base * 2 ^ i : ℕ) : ℝ))

/-- The increment from `base * 2^i` to `base * 2^(i+1)`, normalized at the
left endpoint. -/
noncomputable def dyadicNormalizedIncrement
    (omega : Omega) (base i : ℕ) : ℝ :=
  (S omega (base * 2 ^ (i + 1)) - S omega (base * 2 ^ i)) /
    Real.sqrt (((base * 2 ^ i : ℕ) : ℝ))

theorem sqrt_dyadicEndpoint_succ (base i : ℕ) :
    Real.sqrt (((base * 2 ^ (i + 1) : ℕ) : ℝ)) =
      Real.sqrt 2 * Real.sqrt (((base * 2 ^ i : ℕ) : ℝ)) := by
  push_cast
  rw [pow_succ]
  rw [show (base : ℝ) * ((2 : ℝ) ^ i * 2) =
      2 * ((base : ℝ) * (2 : ℝ) ^ i) by ring]
  exact Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _

/-- Exact stable dyadic recurrence for the actual summatory function. -/
theorem dyadicNormalizedEndpoint_succ
    (omega : Omega) {base : ℕ} (hbase : 0 < base) (i : ℕ) :
    dyadicNormalizedEndpoint omega base (i + 1) =
      (Real.sqrt 2)⁻¹ *
        (dyadicNormalizedEndpoint omega base i +
          dyadicNormalizedIncrement omega base i) := by
  unfold dyadicNormalizedEndpoint dyadicNormalizedIncrement
  rw [sqrt_dyadicEndpoint_succ]
  have hsqrt2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hmesh : 0 < (base * 2 ^ i : ℕ) := Nat.mul_pos hbase (by positivity)
  have hsqrtMesh : Real.sqrt (((base * 2 ^ i : ℕ) : ℝ)) ≠ 0 := by
    positivity
  field_simp [pow_succ]
  ring

/-- Iterating a stable one-step recurrence gives its exact geometric
convolution formula. -/
theorem forward_geometric_recurrence_closed_form
    (rho : ℝ) (h d : ℕ → ℝ)
    (hstep : ∀ i, h (i + 1) = rho * (h i + d i)) :
    ∀ i,
      h i = (∑ j ∈ Finset.range i, rho ^ (i - j) * d j) + rho ^ i * h 0 := by
  intro i
  induction i with
  | zero => simp
  | succ i ih =>
      rw [hstep i, ih, Finset.sum_range_succ]
      have hpow (j : ℕ) (hj : j ∈ Finset.range i) :
          rho ^ (i + 1 - j) = rho * rho ^ (i - j) := by
        have hji : j ≤ i := Nat.le_of_lt (by simpa using hj)
        rw [Nat.succ_sub hji, pow_succ]
        ring
      have hsum :
          rho * (∑ j ∈ Finset.range i, rho ^ (i - j) * d j) =
            ∑ j ∈ Finset.range i, rho ^ (i + 1 - j) * d j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [hpow j hj]
        ring
      calc
        rho *
            ((∑ j ∈ Finset.range i, rho ^ (i - j) * d j) +
              rho ^ i * h 0 + d i) =
            (∑ j ∈ Finset.range i, rho ^ (i + 1 - j) * d j) +
              rho * d i + rho ^ (i + 1) * h 0 := by
                rw [mul_add, mul_add, hsum, pow_succ]
                ring
        _ =
            ((∑ j ∈ Finset.range i, rho ^ (i + 1 - j) * d j) +
              rho ^ (i + 1 - i) * d i) +
                rho ^ (i + 1) * h 0 := by simp

/-- Closed geometric formula for the actual dyadic endpoint sequence. -/
theorem dyadicNormalizedEndpoint_closed_form
    (omega : Omega) {base : ℕ} (hbase : 0 < base) (i : ℕ) :
    dyadicNormalizedEndpoint omega base i =
      (∑ j ∈ Finset.range i,
          (Real.sqrt 2)⁻¹ ^ (i - j) *
            dyadicNormalizedIncrement omega base j) +
        (Real.sqrt 2)⁻¹ ^ i * dyadicNormalizedEndpoint omega base 0 := by
  exact forward_geometric_recurrence_closed_form
    (Real.sqrt 2)⁻¹
    (dyadicNormalizedEndpoint omega base)
    (dyadicNormalizedIncrement omega base)
    (dyadicNormalizedEndpoint_succ omega hbase) i

/-- Schur estimate for the forward geometric kernel produced directly by the
one-step recurrence.  It is the transpose, with the diagonal omitted, of the
backward kernel in `HarperDyadicTransfer`. -/
theorem finite_forward_geometric_schur_l2_bound_range
    (rho : ℝ) (n : ℕ) (x : ℕ → ℝ)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) :
    (∑ i ∈ Finset.range n,
        (∑ j ∈ Finset.range n,
          (if j < i then rho ^ (i - j) else 0) * x j) ^ 2) ≤
      ((1 - rho)⁻¹) ^ 2 * (∑ j ∈ Finset.range n, x j ^ 2) := by
  refine finite_schur_l2_bound_geometric_mass
    (Finset.range n) (Finset.range n)
    (fun i j => if j < i then rho ^ (i - j) else 0) x rho ?_ ?_ ?_
    hrho_lt_one
  · intro i _hi j _hj
    by_cases hji : j < i
    · simp [hji, pow_nonneg hrho_nonneg]
    · simp [hji]
  · intro i _hi
    calc
      (∑ j ∈ Finset.range n, if j < i then rho ^ (i - j) else 0) ≤
          ∑ j ∈ Finset.range n, if j ≤ i then rho ^ (i - j) else 0 := by
            refine Finset.sum_le_sum fun j _hj => ?_
            by_cases hji : j < i
            · simp [hji, hji.le]
            · by_cases hle : j ≤ i
              · simp [hji, hle, pow_nonneg hrho_nonneg]
              · simp [hji, hle]
      _ ≤ (1 - rho)⁻¹ :=
        finite_backward_geometric_col_mass_le rho n i hrho_nonneg hrho_lt_one
  · intro j _hj
    calc
      (∑ i ∈ Finset.range n, if j < i then rho ^ (i - j) else 0) ≤
          ∑ i ∈ Finset.range n, if j ≤ i then rho ^ (i - j) else 0 := by
            refine Finset.sum_le_sum fun i _hi => ?_
            by_cases hji : j < i
            · simp [hji, hji.le]
            · by_cases hle : j ≤ i
              · simp [hji, hle, pow_nonneg hrho_nonneg]
              · simp [hji, hle]
      _ ≤ (1 - rho)⁻¹ :=
        finite_backward_geometric_row_mass_le rho n j hrho_nonneg hrho_lt_one

/-- Forward geometric Schur estimate with an additive boundary vector. -/
theorem finite_forward_geometric_schur_l2_bound_range_add_error
    (rho : ℝ) (n : ℕ) (x e : ℕ → ℝ)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) :
    (∑ i ∈ Finset.range n,
        ((∑ j ∈ Finset.range n,
          (if j < i then rho ^ (i - j) else 0) * x j) + e i) ^ 2) ≤
      2 * (((1 - rho)⁻¹) ^ 2 * (∑ j ∈ Finset.range n, x j ^ 2)) +
        2 * (∑ i ∈ Finset.range n, e i ^ 2) := by
  have hpoint (i : ℕ) :
      ((∑ j ∈ Finset.range n,
          (if j < i then rho ^ (i - j) else 0) * x j) + e i) ^ 2 ≤
        2 * (∑ j ∈ Finset.range n,
          (if j < i then rho ^ (i - j) else 0) * x j) ^ 2 +
          2 * e i ^ 2 :=
    sq_add_le_two_sq_add_two_sq _ _
  calc
    (∑ i ∈ Finset.range n,
        ((∑ j ∈ Finset.range n,
          (if j < i then rho ^ (i - j) else 0) * x j) + e i) ^ 2) ≤
      ∑ i ∈ Finset.range n,
        (2 * (∑ j ∈ Finset.range n,
          (if j < i then rho ^ (i - j) else 0) * x j) ^ 2 +
            2 * e i ^ 2) :=
        Finset.sum_le_sum fun i _hi => hpoint i
    _ = 2 * (∑ i ∈ Finset.range n,
          (∑ j ∈ Finset.range n,
            (if j < i then rho ^ (i - j) else 0) * x j) ^ 2) +
        2 * (∑ i ∈ Finset.range n, e i ^ 2) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 2 * (((1 - rho)⁻¹) ^ 2 *
          (∑ j ∈ Finset.range n, x j ^ 2)) +
        2 * (∑ i ∈ Finset.range n, e i ^ 2) := by
          gcongr
          exact finite_forward_geometric_schur_l2_bound_range rho n x
            hrho_nonneg hrho_lt_one

/-- The exact endpoint energy on any finite dyadic mesh is controlled by the
increment energy and the geometrically decaying left-boundary value. -/
theorem dyadicNormalizedEndpoint_energy_le
    (omega : Omega) {base : ℕ} (hbase : 0 < base) (n : ℕ) :
    (∑ i ∈ Finset.range n,
        dyadicNormalizedEndpoint omega base i ^ 2) ≤
      2 * (((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2 *
        (∑ j ∈ Finset.range n,
          dyadicNormalizedIncrement omega base j ^ 2)) +
      2 * (∑ i ∈ Finset.range n,
        (((Real.sqrt 2)⁻¹ ^ i) *
          dyadicNormalizedEndpoint omega base 0) ^ 2) := by
  let rho : ℝ := (Real.sqrt 2)⁻¹
  let endpoint : ℕ → ℝ := dyadicNormalizedEndpoint omega base
  let increment : ℕ → ℝ := dyadicNormalizedIncrement omega base
  let boundary : ℕ → ℝ := fun i => rho ^ i * endpoint 0
  have hformula (i : ℕ) (hi : i ∈ Finset.range n) :
      endpoint i =
        (∑ j ∈ Finset.range n,
          (if j < i then rho ^ (i - j) else 0) * increment j) + boundary i := by
    have hin : i ≤ n := (Finset.mem_range.mp hi).le
    have hsub : Finset.range i ⊆ Finset.range n := Finset.range_mono hin
    have hsum :
        (∑ j ∈ Finset.range n,
          (if j < i then rho ^ (i - j) else 0) * increment j) =
          ∑ j ∈ Finset.range i, rho ^ (i - j) * increment j := by
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl ?_
        intro j hj
        simp [Finset.mem_range.mp hj]
      · intro j _hjn hjnot
        have hnot : ¬j < i := by simpa using hjnot
        simp [hnot]
    rw [hsum]
    exact dyadicNormalizedEndpoint_closed_form omega hbase i
  have hrewrite :
      (∑ i ∈ Finset.range n, endpoint i ^ 2) =
        ∑ i ∈ Finset.range n,
          ((∑ j ∈ Finset.range n,
            (if j < i then rho ^ (i - j) else 0) * increment j) +
              boundary i) ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hformula i hi]
  have hbound := finite_forward_geometric_schur_l2_bound_range_add_error
    rho n increment boundary dyadicTransferRatio_nonneg dyadicTransferRatio_lt_one
  simpa only [rho, endpoint, increment, boundary, hrewrite] using hbound

theorem dyadicTransferRatio_sq :
    ((Real.sqrt 2)⁻¹) ^ 2 = (1 / 2 : ℝ) := by
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The left-boundary contribution has an absolute geometric energy bound. -/
theorem dyadicBoundary_energy_le_two (n : ℕ) (a : ℝ) :
    (∑ i ∈ Finset.range n, (((Real.sqrt 2)⁻¹ ^ i) * a) ^ 2) ≤
      2 * a ^ 2 := by
  have hsum :
      (∑ i ∈ Finset.range n, (((Real.sqrt 2)⁻¹ ^ i) * a) ^ 2) =
        a ^ 2 * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    rw [mul_pow]
    have hpow : (((Real.sqrt 2)⁻¹ ^ i) ^ 2) =
        (((Real.sqrt 2)⁻¹) ^ 2) ^ i := by
      simp only [← pow_mul]
      rw [Nat.mul_comm]
    rw [hpow, dyadicTransferRatio_sq]
    ring
  rw [hsum]
  have hgeom := finite_geometric_sum_le_inv_one_sub
    (1 / 2 : ℝ) (Finset.range n) (by norm_num) (by norm_num)
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  calc
    a ^ 2 * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i ≤
        a ^ 2 * (1 - (1 / 2 : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hgeom ha
    _ = 2 * a ^ 2 := by ring

/-- Clean model-level transfer: endpoint energy on an exact dyadic mesh is
bounded by the increment energy plus four times the first endpoint. -/
theorem dyadicNormalizedEndpoint_energy_le_increment_add_boundary
    (omega : Omega) {base : ℕ} (hbase : 0 < base) (n : ℕ) :
    (∑ i ∈ Finset.range n,
        dyadicNormalizedEndpoint omega base i ^ 2) ≤
      2 * (((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2 *
        (∑ j ∈ Finset.range n,
          dyadicNormalizedIncrement omega base j ^ 2)) +
      4 * dyadicNormalizedEndpoint omega base 0 ^ 2 := by
  calc
    (∑ i ∈ Finset.range n,
        dyadicNormalizedEndpoint omega base i ^ 2) ≤
        2 * (((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2 *
          (∑ j ∈ Finset.range n,
            dyadicNormalizedIncrement omega base j ^ 2)) +
        2 * (∑ i ∈ Finset.range n,
          (((Real.sqrt 2)⁻¹ ^ i) *
            dyadicNormalizedEndpoint omega base 0) ^ 2) :=
      dyadicNormalizedEndpoint_energy_le omega hbase n
    _ ≤ 2 * (((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2 *
          (∑ j ∈ Finset.range n,
            dyadicNormalizedIncrement omega base j ^ 2)) +
        2 * (2 * dyadicNormalizedEndpoint omega base 0 ^ 2) := by
      gcongr
      exact dyadicBoundary_energy_le_two n
        (dyadicNormalizedEndpoint omega base 0)
    _ = 2 * (((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2 *
          (∑ j ∈ Finset.range n,
            dyadicNormalizedIncrement omega base j ^ 2)) +
        4 * dyadicNormalizedEndpoint omega base 0 ^ 2 := by ring

/-- A growing endpoint-energy floor transfers directly to the actual dyadic
increment energy once it dominates the single left-boundary value. -/
theorem dyadicNormalizedIncrement_energy_lower
    (omega : Omega) {base : ℕ} (hbase : 0 < base) (n : ℕ)
    (endpointFloor : ℝ)
    (hfloor : endpointFloor ≤
      ∑ i ∈ Finset.range n, dyadicNormalizedEndpoint omega base i ^ 2)
    (hboundary :
      8 * dyadicNormalizedEndpoint omega base 0 ^ 2 ≤ endpointFloor) :
    endpointFloor / (4 * ((1 - (Real.sqrt 2)⁻¹)⁻¹) ^ 2) ≤
      ∑ j ∈ Finset.range n,
        dyadicNormalizedIncrement omega base j ^ 2 := by
  have hupper :=
    dyadicNormalizedEndpoint_energy_le_increment_add_boundary omega hbase n
  have herror :
      2 * dyadicNormalizedEndpoint omega base 0 ^ 2 ≤ endpointFloor / 4 := by
    linarith
  apply dyadicEnergy_lower_of_dyadic_endpointEnergy_add_error_upper
    (∑ i ∈ Finset.range n,
      dyadicNormalizedEndpoint omega base i ^ 2)
    (∑ j ∈ Finset.range n,
      dyadicNormalizedIncrement omega base j ^ 2)
    (2 * dyadicNormalizedEndpoint omega base 0 ^ 2)
    endpointFloor
  · convert hupper using 1
    ring
  · exact hfloor
  · exact herror

end Problem1144
end Erdos
