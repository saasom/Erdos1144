import Erdos.Problem1144.HarperTrackB

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-!
## Projected-observable block certificates

This file gives a route-neutral adapter from projected-observable success
events to the raw `normSum` block-success boundary used by `Erdos1144`.

The final theorem still requires raw partial sums.  A projected observable is
admissible only after proving that projected success, outside a summably small
bridge-bad event, forces a genuine raw block success.
-/

/-- Atomic projected success at threshold `M j + B j`.  This is the event
`C_{j,r} >= M_j + B_j` in the informal bridge argument. -/
def projectedAtomSuccessEvent
    (C : ℕ → ℕ → Omega → ℝ) (M B : ℕ → ℝ) (j r : ℕ) : Set Omega :=
  {omega | M j + B j ≤ C j r omega}

/-- Atomic raw success at threshold `M j`. -/
def projectedAtomRawSuccessEvent
    (X : ℕ → ℕ → Omega → ℝ) (M : ℕ → ℝ) (j r : ℕ) : Set Omega :=
  {omega | M j ≤ X j r omega}

/-- Atomic bridge-bad event: the raw observable falls below its projected core
by more than the buffer `B j`. -/
def projectedAtomRemainderBadEvent
    (X C : ℕ → ℕ → Omega → ℝ) (B : ℕ → ℝ) (j r : ℕ) : Set Omega :=
  {omega | X j r omega - C j r omega < -B j}

/-- Atomic deterministic bridge implication in contrapositive form.  If the
projected core reaches `M_j + B_j` and the raw observable does not reach
`M_j`, then the remainder is below `-B_j`. -/
theorem projectedAtomSuccess_inter_rawFailure_subset_remainderBad
    (X C : ℕ → ℕ → Omega → ℝ) (M B : ℕ → ℝ) (j r : ℕ) :
    projectedAtomSuccessEvent C M B j r ∩
        (projectedAtomRawSuccessEvent X M j r)ᶜ ⊆
      projectedAtomRemainderBadEvent X C B j r := by
  intro omega homega
  rcases homega with ⟨hprojected, hnotRaw⟩
  change M j + B j ≤ C j r omega at hprojected
  change ¬ M j ≤ X j r omega at hnotRaw
  have hraw_lt : X j r omega < M j := lt_of_not_ge hnotRaw
  change X j r omega - C j r omega < -B j
  linarith

/-- Atomic bridge implication in forward form.  A projected success and a
non-bad remainder force raw success. -/
theorem projectedAtomSuccess_inter_remainderGood_subset_raw
    (X C : ℕ → ℕ → Omega → ℝ) (M B : ℕ → ℝ) (j r : ℕ) :
    projectedAtomSuccessEvent C M B j r ∩
        (projectedAtomRemainderBadEvent X C B j r)ᶜ ⊆
      projectedAtomRawSuccessEvent X M j r := by
  intro omega homega
  rcases homega with ⟨hprojected, hnotBad⟩
  change M j + B j ≤ C j r omega at hprojected
  change ¬ X j r omega - C j r omega < -B j at hnotBad
  have hrem_ge : -B j ≤ X j r omega - C j r omega := le_of_not_gt hnotBad
  change M j ≤ X j r omega
  linarith

/-- If projected block success guarantees at least one atomic projected success,
and each atomic raw success is a raw block success, then bridge failure is
contained in the union of the atomic remainder-bad events. -/
theorem projectedBridgeBad_subset_biUnion_remainderBad
    (indexSet : Finset ℕ)
    (X C : ℕ → ℕ → Omega → ℝ) (M B : ℕ → ℝ) (j : ℕ)
    (projectedSuccess rawSuccess : Set Omega)
    (hprojected :
      projectedSuccess ⊆
        ⋃ r ∈ indexSet, projectedAtomSuccessEvent C M B j r)
    (hraw :
      ∀ r, r ∈ indexSet →
        projectedAtomRawSuccessEvent X M j r ⊆ rawSuccess) :
    projectedSuccess ∩ rawSuccessᶜ ⊆
      ⋃ r ∈ indexSet, projectedAtomRemainderBadEvent X C B j r := by
  intro omega homega
  rcases homega with ⟨hproj, hnotRawSuccess⟩
  rcases Set.mem_iUnion₂.mp (hprojected hproj) with ⟨r, hr, hAtomProjected⟩
  have hnotAtomRaw :
      omega ∈ (projectedAtomRawSuccessEvent X M j r)ᶜ := by
    intro hAtomRaw
    exact hnotRawSuccess (hraw r hr hAtomRaw)
  have hbad :
      omega ∈ projectedAtomRemainderBadEvent X C B j r :=
    projectedAtomSuccess_inter_rawFailure_subset_remainderBad X C M B j r
      ⟨hAtomProjected, hnotAtomRaw⟩
  exact Set.mem_iUnion₂.mpr ⟨r, hr, hbad⟩

/-- If `bridgeBad` contains every projected-success/raw-failure outcome, then
projected success outside `bridgeBad` implies raw success.  This is the
set-level adapter for the `projected_success_subset_raw_success` field. -/
theorem projectedSuccess_diff_bridgeBad_subset_rawSuccess
    (projectedSuccess rawSuccess bridgeBad : Set Omega)
    (hbridge : projectedSuccess ∩ rawSuccessᶜ ⊆ bridgeBad) :
    projectedSuccess \ bridgeBad ⊆ rawSuccess := by
  intro omega homega
  rcases homega with ⟨hproj, hnotBridge⟩
  by_contra hnotRaw
  exact hnotBridge (hbridge ⟨hproj, hnotRaw⟩)

/-- Specialization of the bridge adapter when `bridgeBad` is chosen to be the
finite union of atomic remainder-bad events. -/
theorem projectedSuccess_diff_biUnion_remainderBad_subset_rawSuccess
    (indexSet : Finset ℕ)
    (X C : ℕ → ℕ → Omega → ℝ) (M B : ℕ → ℝ) (j : ℕ)
    (projectedSuccess rawSuccess : Set Omega)
    (hprojected :
      projectedSuccess ⊆
        ⋃ r ∈ indexSet, projectedAtomSuccessEvent C M B j r)
    (hraw :
      ∀ r, r ∈ indexSet →
        projectedAtomRawSuccessEvent X M j r ⊆ rawSuccess) :
    projectedSuccess \
        (⋃ r ∈ indexSet, projectedAtomRemainderBadEvent X C B j r) ⊆
      rawSuccess := by
  exact
    projectedSuccess_diff_bridgeBad_subset_rawSuccess projectedSuccess rawSuccess
      (⋃ r ∈ indexSet, projectedAtomRemainderBadEvent X C B j r)
      (projectedBridgeBad_subset_biUnion_remainderBad
        indexSet X C M B j projectedSuccess rawSuccess hprojected hraw)

/-- Finite union bound for the projected-to-raw bridge bad event. -/
theorem measure_projectedBridgeBad_le_sum_remainderBad
    (indexSet : Finset ℕ)
    (X C : ℕ → ℕ → Omega → ℝ) (M B : ℕ → ℝ) (j : ℕ)
    (projectedSuccess rawSuccess : Set Omega)
    (hprojected :
      projectedSuccess ⊆
        ⋃ r ∈ indexSet, projectedAtomSuccessEvent C M B j r)
    (hraw :
      ∀ r, r ∈ indexSet →
        projectedAtomRawSuccessEvent X M j r ⊆ rawSuccess) :
    mu (projectedSuccess ∩ rawSuccessᶜ) ≤
      ∑ r ∈ indexSet, mu (projectedAtomRemainderBadEvent X C B j r) := by
  calc
    mu (projectedSuccess ∩ rawSuccessᶜ)
        ≤ mu (⋃ r ∈ indexSet, projectedAtomRemainderBadEvent X C B j r) := by
          exact
            measure_mono
              (projectedBridgeBad_subset_biUnion_remainderBad
                indexSet X C M B j projectedSuccess rawSuccess hprojected hraw)
    _ ≤ ∑ r ∈ indexSet, mu (projectedAtomRemainderBadEvent X C B j r) :=
          MeasureTheory.measure_biUnion_finset_le indexSet
            (fun r => projectedAtomRemainderBadEvent X C B j r)

/-- One-point second-moment bound for an atomic negative bridge remainder. -/
theorem measure_projectedAtomRemainderBadEvent_le_second
    (X C : ℕ → ℕ → Omega → ℝ) (B : ℕ → ℝ) (second : ℕ → ℕ → ℝ) (j r : ℕ)
    (hB : 0 < B j)
    (hint : Integrable (fun omega => (X j r omega - C j r omega) ^ 2) mu)
    (hsecond :
      (∫ omega, (X j r omega - C j r omega) ^ 2 ∂mu) ≤ second j r) :
    mu (projectedAtomRemainderBadEvent X C B j r) ≤
      ENNReal.ofReal (second j r / (B j) ^ 2) := by
  have hsubset :
      projectedAtomRemainderBadEvent X C B j r ⊆
        {omega | B j < |X j r omega - C j r omega|} := by
    intro omega hbad
    change X j r omega - C j r omega < -B j at hbad
    have hlt_neg : B j < -(X j r omega - C j r omega) := by linarith
    exact lt_of_lt_of_le hlt_neg (neg_le_abs _)
  calc
    mu (projectedAtomRemainderBadEvent X C B j r)
        ≤ mu {omega | B j < |X j r omega - C j r omega|} :=
          measure_mono hsubset
    _ ≤ ENNReal.ofReal (second j r / (B j) ^ 2) := by
          exact
            measure_abs_error_gt_le_second
              (E := fun omega => X j r omega - C j r omega)
              (A := B j)
              (V := second j r)
              hB hint hsecond

/-- Finite second-moment budget for the projected-to-raw bridge. -/
noncomputable def projectedBridgeSecondMomentBudget
    (indexSet : ℕ → Finset ℕ) (B : ℕ → ℝ) (second : ℕ → ℕ → ℝ)
    (j : ℕ) : ℝ≥0∞ :=
  ∑ r ∈ indexSet j, ENNReal.ofReal (second j r / (B j) ^ 2)

/-- The projected-to-raw bridge bad event is controlled by the finite
second-moment budget of the remainders `X_{j,r} - C_{j,r}`. -/
theorem measure_projectedBridgeBad_le_secondMomentBudget
    (indexSet : ℕ → Finset ℕ)
    (X C : ℕ → ℕ → Omega → ℝ) (M B : ℕ → ℝ) (second : ℕ → ℕ → ℝ) (j : ℕ)
    (projectedSuccess rawSuccess : Set Omega)
    (hprojected :
      projectedSuccess ⊆
        ⋃ r ∈ indexSet j, projectedAtomSuccessEvent C M B j r)
    (hraw :
      ∀ r, r ∈ indexSet j →
        projectedAtomRawSuccessEvent X M j r ⊆ rawSuccess)
    (hB : 0 < B j)
    (hint :
      ∀ r, r ∈ indexSet j →
        Integrable (fun omega => (X j r omega - C j r omega) ^ 2) mu)
    (hsecond :
      ∀ r, r ∈ indexSet j →
        (∫ omega, (X j r omega - C j r omega) ^ 2 ∂mu) ≤ second j r) :
    mu (projectedSuccess ∩ rawSuccessᶜ) ≤
      projectedBridgeSecondMomentBudget indexSet B second j := by
  calc
    mu (projectedSuccess ∩ rawSuccessᶜ)
        ≤ ∑ r ∈ indexSet j, mu (projectedAtomRemainderBadEvent X C B j r) :=
          measure_projectedBridgeBad_le_sum_remainderBad
            (indexSet j) X C M B j projectedSuccess rawSuccess hprojected hraw
    _ ≤ ∑ r ∈ indexSet j, ENNReal.ofReal (second j r / (B j) ^ 2) := by
          exact Finset.sum_le_sum fun r hr =>
            measure_projectedAtomRemainderBadEvent_le_second
              X C B second j r hB (hint r hr) (hsecond r hr)

/-- Summability wrapper for bridge-bad events paid by an `ENNReal` budget. -/
theorem projectedBridgeBad_tsum_ne_top_of_budget
    (bridgeBad : ℕ → Set Omega) (budget : ℕ → ℝ≥0∞)
    (hprob : ∀ j, mu (bridgeBad j) ≤ budget j)
    (hbudget : (∑' j, budget j) ≠ ⊤) :
    (∑' j, mu (bridgeBad j)) ≠ ⊤ := by
  exact ne_top_of_le_ne_top hbudget (ENNReal.tsum_le_tsum hprob)

/-- A certificate that allows an auxiliary projected observable internally,
while preserving the raw `normSum` block-success boundary.

The event `projectedSuccess j` can be any event produced by a Walsh projection,
endpoint-shell observable, filtered large-prime process, or other auxiliary
process.  The field `projected_success_subset_raw_success` is the necessary
bridge back to the original partial sums: outside `bridgeBad j`, projected
success must imply `blockSuccess lo hi M`.
-/
structure ProjectedBlockCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  M : ℕ → ℝ
  projectedSuccess : ℕ → Set Omega
  bridgeBad : ℕ → Set Omega
  failProjected : ℕ → ℝ≥0∞
  failBridge : ℕ → ℝ≥0∞
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  fail_summable :
    (∑' j, (failProjected j + failBridge j)) ≠ ⊤
  prob_projected_fail :
    ∀ j, mu ((projectedSuccess j)ᶜ) ≤ failProjected j
  prob_bridge_bad :
    ∀ j, mu (bridgeBad j) ≤ failBridge j
  projected_success_subset_raw_success :
    ∀ j, projectedSuccess j \ bridgeBad j ⊆
      {omega | blockSuccess lo hi M omega j}

/-- If raw block success fails, then either projected success failed or the
bridge back to raw partial sums is in its bad event. -/
theorem blockFailure_subset_projectedFailure_union_bridgeBad
    (h : ProjectedBlockCertificate) (j : ℕ) :
    blockFailure h.lo h.hi h.M j ⊆
      (h.projectedSuccess j)ᶜ ∪ h.bridgeBad j := by
  intro omega hfail
  by_cases hproj : omega ∈ h.projectedSuccess j
  · by_cases hbridge : omega ∈ h.bridgeBad j
    · exact Or.inr hbridge
    · have hraw :
          omega ∈ {omega | blockSuccess h.lo h.hi h.M omega j} := by
        exact h.projected_success_subset_raw_success j ⟨hproj, hbridge⟩
      exact False.elim (hfail hraw)
  · exact Or.inl hproj

/-- Projected-observable certificates produce ordinary positive-block
certificates once the projected-to-raw bridge has a summable bad event. -/
noncomputable def positiveBlockOmega_of_projectedBlockCertificate
    (h : ProjectedBlockCertificate) :
    PositiveBlockOmega where
  X := h.lo
  Y := h.hi
  M := h.M
  fail := fun j => h.failProjected j + h.failBridge j
  X_tendsto := h.lo_tendsto_atTop
  M_tendsto := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_fail := by
    intro j
    calc
      mu (blockFailure h.lo h.hi h.M j)
          ≤ mu ((h.projectedSuccess j)ᶜ ∪ h.bridgeBad j) := by
            exact
              measure_mono
                (blockFailure_subset_projectedFailure_union_bridgeBad h j)
      _ ≤ mu ((h.projectedSuccess j)ᶜ) + mu (h.bridgeBad j) :=
            measure_union_le _ _
      _ ≤ h.failProjected j + h.failBridge j :=
            add_le_add (h.prob_projected_fail j) (h.prob_bridge_bad j)

/-- Direct closure from a projected-observable block certificate. -/
theorem erdos1144_of_projectedBlockCertificate
    (h : ProjectedBlockCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_projectedBlockCertificate h)

end Problem1144
end Erdos
