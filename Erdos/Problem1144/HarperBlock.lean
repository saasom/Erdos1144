import Erdos.Problem1144.PositiveBlockCertificate

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Erdos
namespace Problem1144

/-- Interval-form block success, matching the way Harper-style block theorems
are normally stated on paper.

This is propositionally equivalent to `blockSuccess`; it avoids exposing
`Finset.Icc` in analytic theorem statements.
-/
def intervalBlockSuccess
    (lo hi : ℕ → ℕ) (M : ℕ → ℝ) (omega : Omega) (j : ℕ) : Prop :=
  ∃ N, lo j ≤ N ∧ N ≤ hi j ∧ M j ≤ normSum omega N

/-- Interval-form block failure. -/
def intervalBlockFailure
    (lo hi : ℕ → ℕ) (M : ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | ¬ intervalBlockSuccess lo hi M omega j}

/-- The interval and finite-interval formulations of block success agree. -/
theorem blockSuccess_iff_intervalBlockSuccess
    (lo hi : ℕ → ℕ) (M : ℕ → ℝ) (omega : Omega) (j : ℕ) :
    blockSuccess lo hi M omega j ↔
      intervalBlockSuccess lo hi M omega j := by
  constructor
  · rintro ⟨N, hN, hM⟩
    exact ⟨N, (Finset.mem_Icc.mp hN).1, (Finset.mem_Icc.mp hN).2, hM⟩
  · rintro ⟨N, hlo, hhi, hM⟩
    exact ⟨N, Finset.mem_Icc.mpr ⟨hlo, hhi⟩, hM⟩

/-- The interval and finite-interval formulations of block failure agree. -/
theorem blockFailure_eq_intervalBlockFailure
    (lo hi : ℕ → ℕ) (M : ℕ → ℝ) (j : ℕ) :
    blockFailure lo hi M j =
      intervalBlockFailure lo hi M j := by
  ext omega
  simp [blockFailure, intervalBlockFailure,
    blockSuccess_iff_intervalBlockSuccess lo hi M omega j]

/-- A direct one-sided Harper-style block certificate.

The hard analytic input is exactly the high-probability positive block theorem:
each block fails with probability at most `delta j`, the thresholds tend to
infinity, and the failure budget is summable.
-/
structure OneSidedHarperBlockCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  delta : ℕ → ℝ
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  delta_nonneg : ∀ j, 0 ≤ delta j
  delta_summable : Summable delta
  block_failure_bound :
    ∀ j,
      mu (intervalBlockFailure lo hi M j) ≤ ENNReal.ofReal (delta j)

/-- A one-sided Harper block certificate is already a `PositiveBlockOmega`
certificate. -/
noncomputable def positiveBlockOmega_of_oneSidedHarperBlockCertificate
    (h : OneSidedHarperBlockCertificate) :
    PositiveBlockOmega where
  X := h.lo
  Y := h.hi
  M := h.M
  fail := fun j => ENNReal.ofReal (h.delta j)
  X_tendsto := h.lo_tendsto_atTop
  M_tendsto := h.M_tendsto_atTop
  fail_summable := h.delta_summable.tsum_ofReal_ne_top
  prob_fail := by
    intro j
    rw [blockFailure_eq_intervalBlockFailure h.lo h.hi h.M j]
    exact h.block_failure_bound j

/-- Direct closure route from a one-sided Harper block theorem to Erdős #1144. -/
theorem erdos1144_of_oneSidedHarperBlockCertificate
    (h : OneSidedHarperBlockCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_oneSidedHarperBlockCertificate h)

/-- Analytic target for the Harper route.

This is intentionally stated at the certificate boundary: proving this theorem
amounts to porting Harper's one-sided local block theorem to the complete
Rademacher model used in #1144.
-/
axiom completeOneSidedHarperBlock : OneSidedHarperBlockCertificate

/-- The Harper route's positive-block certificate. -/
noncomputable def positiveBlockOmega_of_completeOneSidedHarperBlock :
    PositiveBlockOmega :=
  positiveBlockOmega_of_oneSidedHarperBlockCertificate
    completeOneSidedHarperBlock

/-- Erdős #1144 from the complete-model one-sided Harper block theorem. -/
theorem erdos1144_of_completeOneSidedHarperBlock : Erdos1144 :=
  erdos1144_of_oneSidedHarperBlockCertificate completeOneSidedHarperBlock

end Problem1144
end Erdos
