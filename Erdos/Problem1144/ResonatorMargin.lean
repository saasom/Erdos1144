import Erdos.Problem1144.Resonator
import Mathlib.Analysis.Convex.Integral

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-- A one-block resonator margin.

If all test points in the block are below the target `M j`, and both the
test weights and resonator weight are nonnegative, then this finite weighted
sum is nonpositive. A positive margin therefore certifies block success.
-/
noncomputable def resonatorMargin
    (testSet : ℕ → Finset ℕ)
    (weight : ℕ → ℕ → ℝ)
    (resWeight : ℕ → ℕ → Omega → ℝ)
    (M : ℕ → ℝ)
    (j : ℕ)
    (omega : Omega) : ℝ :=
  (testSet j).sum fun N =>
    weight j N * resWeight j N omega * (normSum omega N - M j)

/-- Block failure forces the resonator margin to be nonpositive.

This is the deterministic reason the margin is the right transfer object:
with nonnegative weights, every summand is nonpositive on a failed block.
-/
theorem blockFailure_subset_margin_nonpos
    (X Y : ℕ → ℕ) (M : ℕ → ℝ)
    (testSet : ℕ → Finset ℕ)
    (weight : ℕ → ℕ → ℝ)
    (resWeight : ℕ → ℕ → Omega → ℝ)
    (j : ℕ)
    (testSet_in_block :
      ∀ j N, N ∈ testSet j → X j ≤ N ∧ N ≤ Y j)
    (weight_nonneg :
      ∀ j N, N ∈ testSet j → 0 ≤ weight j N)
    (resWeight_nonneg :
      ∀ j N, N ∈ testSet j → ∀ omega, 0 ≤ resWeight j N omega) :
    blockFailure X Y M j ⊆
      {omega | resonatorMargin testSet weight resWeight M j omega ≤ 0} := by
  intro omega hfail
  change
    (testSet j).sum
      (fun N =>
        weight j N * resWeight j N omega * (normSum omega N - M j))
      ≤ 0
  apply Finset.sum_nonpos
  intro N hN
  have hblock := testSet_in_block j N hN
  have hNblock : N ∈ Finset.Icc (X j) (Y j) :=
    Finset.mem_Icc.mpr hblock
  have hlt : normSum omega N < M j :=
    lt_of_not_ge fun hle => hfail ⟨N, hNblock, hle⟩
  have hdiff : normSum omega N - M j ≤ 0 := by
    linarith
  have hwr : 0 ≤ weight j N * resWeight j N omega :=
    mul_nonneg (weight_nonneg j N hN) (resWeight_nonneg j N hN omega)
  exact mul_nonpos_of_nonneg_of_nonpos hwr hdiff

/-- A fourth-moment one-sided lower-tail bound for any real random variable.

If `E D` is at least `A > 0`, then the event `D ≤ 0` is contained in the
fourth-moment deviation event. Markov's inequality gives the stated bound.
-/
theorem measure_nonpos_le_centered_fourth
    (D : Omega → ℝ) (A B : ℝ)
    (hA : 0 < A)
    (hfourth_int :
      Integrable (fun omega => (D omega - ∫ omega, D omega ∂mu) ^ 4) mu)
    (hmean : A ≤ ∫ omega, D omega ∂mu)
    (hfourth :
      (∫ omega, (D omega - ∫ omega, D omega ∂mu) ^ 4 ∂mu) ≤ B) :
    mu {omega | D omega ≤ 0} ≤ ENNReal.ofReal (B / A ^ 4) := by
  let E : Set Omega := {omega | D omega ≤ 0}
  let T : Set Omega :=
    {omega | A ^ 4 ≤ (D omega - ∫ omega, D omega ∂mu) ^ 4}
  have hsubset : E ⊆ T := by
    intro omega hD
    have hD0 : D omega ≤ 0 := hD
    have hleabs : A ≤ |D omega - ∫ omega, D omega ∂mu| := by
      rw [le_abs]
      right
      linarith
    have hpowabs : A ^ 4 ≤ |D omega - ∫ omega, D omega ∂mu| ^ 4 :=
      pow_le_pow_left₀ hA.le hleabs 4
    rw [← abs_pow] at hpowabs
    simpa [T,
      abs_of_nonneg
        (by positivity :
          0 ≤ (D omega - ∫ omega, D omega ∂mu) ^ 4)] using hpowabs
  have hnonneg :
      0 ≤ᵐ[mu] fun omega => (D omega - ∫ omega, D omega ∂mu) ^ 4 :=
    ae_of_all _ fun omega => by positivity
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (μ := mu)
      (f := fun omega => (D omega - ∫ omega, D omega ∂mu) ^ 4)
      hnonneg hfourth_int (A ^ 4)
  have hTreal : mu.real T ≤ B / A ^ 4 := by
    have hmul : A ^ 4 * mu.real T ≤ B :=
      le_trans hmarkov hfourth
    rw [le_div_iff₀ (pow_pos hA 4)]
    exact by simpa [mul_comm] using hmul
  have hEreal : mu.real E ≤ B / A ^ 4 :=
    (measureReal_mono hsubset).trans hTreal
  rw [← ofReal_measureReal (μ := mu) (s := E)]
  exact ENNReal.ofReal_le_ofReal hEreal

/-- The centered fourth moment is controlled by the raw fourth moment, up to a
constant, on the probability space `mu`.

This is the only analytic normalization hidden by the raw fourth-moment
certificate: Jensen bounds `(E D)^4` by `E D^4`, while
`(x - m)^4 ≤ 8 (x^4 + m^4)` gives the harmless constant.
-/
theorem centered_fourth_le_raw_fourth
    (D : Omega → ℝ)
    (hD_int : Integrable D mu)
    (hD4_int : Integrable (fun omega => D omega ^ 4) mu) :
    (∫ omega, (D omega - ∫ omega, D omega ∂mu) ^ 4 ∂mu)
      ≤ 16 * ∫ omega, D omega ^ 4 ∂mu := by
  let m : ℝ := ∫ omega, D omega ∂mu
  have hpoly : ∀ x : ℝ, (x - m) ^ 4 ≤ 8 * (x ^ 4 + m ^ 4) := by
    intro x
    nlinarith [sq_nonneg (x - m), sq_nonneg (x + m),
      sq_nonneg (x ^ 2 - m ^ 2)]
  have hbound_ae :
      (fun omega => (D omega - m) ^ 4) ≤ᵐ[mu]
        (fun omega => 8 * (D omega ^ 4 + m ^ 4)) :=
    ae_of_all _ fun omega => hpoly (D omega)
  have hmajor_int :
      Integrable (fun omega => 8 * (D omega ^ 4 + m ^ 4)) mu := by
    exact (hD4_int.add (integrable_const (m ^ 4))).const_mul 8
  have hcenter_int : Integrable (fun omega => (D omega - m) ^ 4) mu := by
    refine Integrable.mono' hmajor_int ?_ ?_
    · fun_prop
    · filter_upwards [hbound_ae] with omega homega
      rw [Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (D omega - m) ^ 4)]
      exact homega
  have hle_int :
      (∫ omega, (D omega - m) ^ 4 ∂mu) ≤
        ∫ omega, 8 * (D omega ^ 4 + m ^ 4) ∂mu :=
    integral_mono_ae hcenter_int hmajor_int hbound_ae
  have hc : ConvexOn ℝ (Set.univ : Set ℝ) (fun x : ℝ => x ^ 4) := by
    simpa using ((by norm_num : Even 4).convexOn_pow (𝕜 := ℝ))
  have hcont : ContinuousOn (fun x : ℝ => x ^ 4) (Set.univ : Set ℝ) := by
    fun_prop
  have hmap : (∀ᵐ omega ∂mu, D omega ∈ (Set.univ : Set ℝ)) := by
    simp
  have hmean4 : m ^ 4 ≤ ∫ omega, D omega ^ 4 ∂mu := by
    simpa [m] using
      ConvexOn.map_integral_le (μ := mu) hc hcont isClosed_univ hmap
        hD_int hD4_int
  have hmajor_eval :
      (∫ omega, 8 * (D omega ^ 4 + m ^ 4) ∂mu)
        = 8 * (∫ omega, D omega ^ 4 ∂mu) + 8 * m ^ 4 := by
    calc
      (∫ omega, 8 * (D omega ^ 4 + m ^ 4) ∂mu)
          = ∫ omega, (8 * D omega ^ 4 + 8 * m ^ 4) ∂mu := by
            congr 1
            ext omega
            ring
      _ = (∫ omega, 8 * D omega ^ 4 ∂mu) +
            ∫ omega, 8 * m ^ 4 ∂mu := by
            rw [integral_add]
            · exact (hD4_int.const_mul 8)
            · exact integrable_const (8 * m ^ 4)
      _ = 8 * (∫ omega, D omega ^ 4 ∂mu) + 8 * m ^ 4 := by
            rw [integral_const_mul 8 (fun omega => D omega ^ 4)]
            simp [integral_const]
  rw [show
      (∫ omega, (D omega - ∫ omega, D omega ∂mu) ^ 4 ∂mu)
        = ∫ omega, (D omega - m) ^ 4 ∂mu by rfl]
  calc
    (∫ omega, (D omega - m) ^ 4 ∂mu)
        ≤ ∫ omega, 8 * (D omega ^ 4 + m ^ 4) ∂mu := hle_int
    _ = 8 * (∫ omega, D omega ^ 4 ∂mu) + 8 * m ^ 4 := hmajor_eval
    _ ≤ 16 * ∫ omega, D omega ^ 4 ∂mu := by
      nlinarith

/-- Raw fourth-moment lower-tail bound for a positive-margin random variable. -/
theorem measure_margin_nonpos_le_raw_fourth
    (D : Omega → ℝ) (A C : ℝ)
    (hA : 0 < A)
    (hD_int : Integrable D mu)
    (hD4_int : Integrable (fun omega => D omega ^ 4) mu)
    (hmean : A ≤ ∫ omega, D omega ∂mu)
    (hraw : (∫ omega, D omega ^ 4 ∂mu) ≤ C) :
    mu {omega | D omega ≤ 0} ≤ ENNReal.ofReal (16 * C / A ^ 4) := by
  have hcenter_int :
      Integrable
        (fun omega => (D omega - ∫ omega, D omega ∂mu) ^ 4) mu := by
    let m : ℝ := ∫ omega, D omega ∂mu
    have hpoly : ∀ x : ℝ, (x - m) ^ 4 ≤ 8 * (x ^ 4 + m ^ 4) := by
      intro x
      nlinarith [sq_nonneg (x - m), sq_nonneg (x + m),
        sq_nonneg (x ^ 2 - m ^ 2)]
    have hbound_ae :
        (fun omega => (D omega - m) ^ 4) ≤ᵐ[mu]
          (fun omega => 8 * (D omega ^ 4 + m ^ 4)) :=
      ae_of_all _ fun omega => hpoly (D omega)
    have hmajor_int :
        Integrable (fun omega => 8 * (D omega ^ 4 + m ^ 4)) mu := by
      exact (hD4_int.add (integrable_const (m ^ 4))).const_mul 8
    have hcenter_int_m : Integrable (fun omega => (D omega - m) ^ 4) mu := by
      refine Integrable.mono' hmajor_int ?_ ?_
      · fun_prop
      · filter_upwards [hbound_ae] with omega homega
        rw [Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ (D omega - m) ^ 4)]
        exact homega
    simpa [m] using hcenter_int_m
  exact measure_nonpos_le_centered_fourth
    (D := D) (A := A) (B := 16 * C) hA hcenter_int hmean
    (le_trans (centered_fourth_le_raw_fourth D hD_int hD4_int)
      (mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 16)))

/-- A per-test-point resonator transfer certificate for the positive-block
theorem.

The analytic burden is concentrated in raw first/fourth estimates for the
explicit margins `D_j`. The failure budget is
`ofReal (16 * C_j / A_j^4)`.
-/
structure ResonatorTransferCertificate where
  X : ℕ → ℕ
  Y : ℕ → ℕ
  M : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  weight : ℕ → ℕ → ℝ
  resWeight : ℕ → ℕ → Omega → ℝ
  A : ℕ → ℝ
  C : ℕ → ℝ
  X_tendsto : Tendsto X atTop atTop
  M_tendsto : Tendsto M atTop atTop
  testSet_in_block :
    ∀ j N, N ∈ testSet j → X j ≤ N ∧ N ≤ Y j
  weight_nonneg :
    ∀ j N, N ∈ testSet j → 0 ≤ weight j N
  resWeight_nonneg :
    ∀ j N, N ∈ testSet j → ∀ omega, 0 ≤ resWeight j N omega
  A_pos : ∀ j, 0 < A j
  margin_integrable :
    ∀ j,
      Integrable (fun omega => resonatorMargin testSet weight resWeight M j omega) mu
  raw_fourth_integrable :
    ∀ j,
      Integrable
        (fun omega => (resonatorMargin testSet weight resWeight M j omega) ^ 4) mu
  mean_lower :
    ∀ j,
      A j ≤
        ∫ omega,
          resonatorMargin testSet weight resWeight M j omega ∂mu
  raw_fourth_upper :
    ∀ j,
      (∫ omega,
        (resonatorMargin testSet weight resWeight M j omega) ^ 4 ∂mu)
      ≤ C j
  error_summable :
    (∑' j, ENNReal.ofReal (16 * C j / A j ^ 4)) ≠ ⊤

/-- A per-test resonator transfer certificate gives the positive-block omega
certificate. -/
noncomputable def positiveBlockOmega_of_resonatorTransferCertificate
    (h : ResonatorTransferCertificate) :
    PositiveBlockOmega where
  X := h.X
  Y := h.Y
  M := h.M
  fail := fun j => ENNReal.ofReal (16 * h.C j / h.A j ^ 4)
  X_tendsto := h.X_tendsto
  M_tendsto := h.M_tendsto
  fail_summable := h.error_summable
  prob_fail := by
    intro j
    have hsubset :
        blockFailure h.X h.Y h.M j ⊆
          {omega |
            resonatorMargin h.testSet h.weight h.resWeight h.M j omega ≤ 0} :=
      blockFailure_subset_margin_nonpos h.X h.Y h.M h.testSet h.weight
        h.resWeight j h.testSet_in_block h.weight_nonneg h.resWeight_nonneg
    exact le_trans
      (measure_mono hsubset)
      (measure_margin_nonpos_le_raw_fourth
        (D := fun omega =>
          resonatorMargin h.testSet h.weight h.resWeight h.M j omega)
        (A := h.A j)
        (C := h.C j)
        (h.A_pos j)
        (h.margin_integrable j)
        (h.raw_fourth_integrable j)
        (h.mean_lower j)
        (h.raw_fourth_upper j))

/-- Direct route from a per-test resonator transfer certificate to Erdős #1144. -/
theorem erdos1144_of_resonatorTransferCertificate
    (h : ResonatorTransferCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_resonatorTransferCertificate h)

end Problem1144
end Erdos
