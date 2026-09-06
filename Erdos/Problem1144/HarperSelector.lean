import Erdos.Problem1144.HarperProcessBlock

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-- A selected test point has a large-prime win. The selector may depend on
the whole sample point; the analytic proof is responsible for constructing a
useful selector and bounding the failure probability. -/
def selectedLargeSuccess
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (M buffer : ℕ → ℝ) (selector : ℕ → Omega → ℕ)
    (omega : Omega) (j : ℕ) : Prop :=
  selector j omega ∈ testSet j ∧
    M j + buffer j ≤
      largePrimeProcess omega (cut j) (selector j omega + 1)

/-- Failure of selected large-prime success. -/
def selectedLargeFailure
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (M buffer : ℕ → ℝ) (selector : ℕ → Omega → ℕ)
    (j : ℕ) : Set Omega :=
  {omega | ¬ selectedLargeSuccess testSet cut M buffer selector omega j}

/-- Smooth badness at the selected point only. This avoids the all-mesh smooth
budget that is incompatible with a high-probability large-prime maximum in the
true Harper range. -/
def selectedSmoothBad
    (cut : ℕ → ℕ) (buffer : ℕ → ℝ)
    (selector : ℕ → Omega → ℕ) (j : ℕ) : Set Omega :=
  {omega |
    smoothProcess omega (cut j) (selector j omega + 1) < -buffer j}

/-- A concrete selector: choose a point attaining the finite large-prime
maximum on the test mesh. The fallback value for empty meshes is irrelevant
for certificates, which require nonempty test sets. -/
noncomputable def largePrimeMaxSelector
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) : ℕ :=
  if h : (testSet j).Nonempty then
    Classical.choose
      (Finset.exists_mem_eq_sup'
        (s := testSet j) h
        (f := fun N => largePrimeProcess omega (cut j) (N + 1)))
  else 0

/-- The max selector belongs to the test mesh when the mesh is nonempty. -/
theorem largePrimeMaxSelector_mem
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) (htest : (testSet j).Nonempty) :
    largePrimeMaxSelector testSet cut j omega ∈ testSet j := by
  classical
  unfold largePrimeMaxSelector
  rw [dif_pos htest]
  exact
    (Classical.choose_spec
      (Finset.exists_mem_eq_sup'
        (s := testSet j) htest
        (f := fun N => largePrimeProcess omega (cut j) (N + 1)))).1

/-- The max selector attains the finite large-prime maximum. -/
theorem largePrimeMaxSelector_attains
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) (htest : (testSet j).Nonempty) :
    largePrimeTestMax testSet cut omega j =
      largePrimeProcess omega (cut j)
        (largePrimeMaxSelector testSet cut j omega + 1) := by
  classical
  unfold largePrimeTestMax largePrimeMaxSelector
  rw [dif_pos htest, dif_pos htest]
  exact
    (Classical.choose_spec
      (Finset.exists_mem_eq_sup'
        (s := testSet j) htest
        (f := fun N => largePrimeProcess omega (cut j) (N + 1)))).2

/-- On nonempty meshes, selected large-prime success for the max selector is
equivalent to ordinary test-mesh large-prime success. -/
theorem selectedLargeSuccess_maxSelector_iff_largePrimeTestSuccess
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) (htest : (testSet j).Nonempty) :
    selectedLargeSuccess testSet cut M buffer
        (largePrimeMaxSelector testSet cut) omega j ↔
      largePrimeTestSuccess testSet cut M buffer omega j := by
  classical
  constructor
  · intro hsel
    exact ⟨largePrimeMaxSelector testSet cut j omega, hsel.1, hsel.2⟩
  · rintro ⟨N, hN, hle⟩
    refine
      ⟨largePrimeMaxSelector_mem testSet cut j omega htest, ?_⟩
    calc
      M j + buffer j
          ≤ largePrimeProcess omega (cut j) (N + 1) := hle
      _ ≤ largePrimeTestMax testSet cut omega j := by
            have hmax :
                largePrimeTestMax testSet cut omega j =
                  (testSet j).sup' htest fun N =>
                    largePrimeProcess omega (cut j) (N + 1) := by
              unfold largePrimeTestMax
              simp [htest]
            calc
              largePrimeProcess omega (cut j) (N + 1)
                  ≤
                  (testSet j).sup' htest fun N =>
                    largePrimeProcess omega (cut j) (N + 1) := by
                    exact
                      Finset.le_sup'
                        (fun N => largePrimeProcess omega (cut j) (N + 1))
                        hN
              _ = largePrimeTestMax testSet cut omega j := hmax.symm
      _ =
          largePrimeProcess omega (cut j)
            (largePrimeMaxSelector testSet cut j omega + 1) := by
            rw [largePrimeMaxSelector_attains testSet cut j omega htest]

/-- On nonempty meshes, selected large-prime failure for the max selector is
the ordinary test-mesh large-prime failure. -/
theorem selectedLargeFailure_maxSelector_eq_largePrimeTestFailure
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (j : ℕ) (htest : (testSet j).Nonempty) :
    selectedLargeFailure testSet cut M buffer
        (largePrimeMaxSelector testSet cut) j =
      largePrimeTestFailure testSet cut M buffer j := by
  ext omega
  simp [selectedLargeFailure, largePrimeTestFailure,
    selectedLargeSuccess_maxSelector_iff_largePrimeTestSuccess
      testSet cut M buffer omega j htest]

/-- The set of test points attaining the finite large-prime maximum. -/
noncomputable def largePrimeMaximizerSet
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) : Finset ℕ :=
  (testSet j).filter fun N =>
    largePrimeTestMax testSet cut omega j =
      largePrimeProcess omega (cut j) (N + 1)

/-- The finite argmax set is nonempty when the test mesh is nonempty. -/
theorem largePrimeMaximizerSet_nonempty
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) (htest : (testSet j).Nonempty) :
    (largePrimeMaximizerSet testSet cut j omega).Nonempty := by
  classical
  rcases
    Finset.exists_mem_eq_sup'
      (s := testSet j) htest
      (f := fun N => largePrimeProcess omega (cut j) (N + 1))
    with ⟨N, hN, hmax⟩
  refine ⟨N, ?_⟩
  unfold largePrimeMaximizerSet largePrimeTestMax
  simp [hN, htest, hmax]

/-- A deterministic selector: the least test point attaining the finite
large-prime maximum. The fallback value for empty meshes is irrelevant for
certificates, which require nonempty test sets. -/
noncomputable def largePrimeFirstMaxSelector
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) : ℕ :=
  if h : (largePrimeMaximizerSet testSet cut j omega).Nonempty then
    (largePrimeMaximizerSet testSet cut j omega).min' h
  else 0

/-- The deterministic first-max selector belongs to the argmax set. -/
theorem largePrimeFirstMaxSelector_mem_maximizerSet
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) (htest : (testSet j).Nonempty) :
    largePrimeFirstMaxSelector testSet cut j omega ∈
      largePrimeMaximizerSet testSet cut j omega := by
  classical
  unfold largePrimeFirstMaxSelector
  rw [dif_pos (largePrimeMaximizerSet_nonempty testSet cut j omega htest)]
  exact
    Finset.min'_mem
      (largePrimeMaximizerSet testSet cut j omega)
      (largePrimeMaximizerSet_nonempty testSet cut j omega htest)

/-- The deterministic first-max selector belongs to the test mesh when the
mesh is nonempty. -/
theorem largePrimeFirstMaxSelector_mem
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) (htest : (testSet j).Nonempty) :
    largePrimeFirstMaxSelector testSet cut j omega ∈ testSet j := by
  classical
  have hmem :=
    largePrimeFirstMaxSelector_mem_maximizerSet
      testSet cut j omega htest
  unfold largePrimeMaximizerSet at hmem
  exact (Finset.mem_filter.mp hmem).1

/-- The deterministic first-max selector attains the finite large-prime
maximum. -/
theorem largePrimeFirstMaxSelector_attains
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) (htest : (testSet j).Nonempty) :
    largePrimeTestMax testSet cut omega j =
      largePrimeProcess omega (cut j)
        (largePrimeFirstMaxSelector testSet cut j omega + 1) := by
  classical
  have hmem :=
    largePrimeFirstMaxSelector_mem_maximizerSet
      testSet cut j omega htest
  unfold largePrimeMaximizerSet at hmem
  exact (Finset.mem_filter.mp hmem).2

/-- On nonempty meshes, selected large-prime success for the deterministic
first-max selector is equivalent to ordinary test-mesh large-prime success. -/
theorem selectedLargeSuccess_firstMaxSelector_iff_largePrimeTestSuccess
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (omega : Omega) (j : ℕ) (htest : (testSet j).Nonempty) :
    selectedLargeSuccess testSet cut M buffer
        (largePrimeFirstMaxSelector testSet cut) omega j ↔
      largePrimeTestSuccess testSet cut M buffer omega j := by
  classical
  constructor
  · intro hsel
    exact ⟨largePrimeFirstMaxSelector testSet cut j omega, hsel.1, hsel.2⟩
  · rintro ⟨N, hN, hle⟩
    refine
      ⟨largePrimeFirstMaxSelector_mem testSet cut j omega htest, ?_⟩
    calc
      M j + buffer j
          ≤ largePrimeProcess omega (cut j) (N + 1) := hle
      _ ≤ largePrimeTestMax testSet cut omega j := by
            have hmax :
                largePrimeTestMax testSet cut omega j =
                  (testSet j).sup' htest fun N =>
                    largePrimeProcess omega (cut j) (N + 1) := by
              unfold largePrimeTestMax
              simp [htest]
            calc
              largePrimeProcess omega (cut j) (N + 1)
                  ≤
                  (testSet j).sup' htest fun N =>
                    largePrimeProcess omega (cut j) (N + 1) := by
                    exact
                      Finset.le_sup'
                        (fun N => largePrimeProcess omega (cut j) (N + 1))
                        hN
              _ = largePrimeTestMax testSet cut omega j := hmax.symm
      _ =
          largePrimeProcess omega (cut j)
            (largePrimeFirstMaxSelector testSet cut j omega + 1) := by
            rw [largePrimeFirstMaxSelector_attains testSet cut j omega htest]

/-- On nonempty meshes, selected large-prime failure for the deterministic
first-max selector is the ordinary test-mesh large-prime failure. -/
theorem selectedLargeFailure_firstMaxSelector_eq_largePrimeTestFailure
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (j : ℕ) (htest : (testSet j).Nonempty) :
    selectedLargeFailure testSet cut M buffer
        (largePrimeFirstMaxSelector testSet cut) j =
      largePrimeTestFailure testSet cut M buffer j := by
  ext omega
  simp [selectedLargeFailure, largePrimeTestFailure,
    selectedLargeSuccess_firstMaxSelector_iff_largePrimeTestSuccess
      testSet cut M buffer omega j htest]

/-- Any point in the maximizer set is at least the deterministic first
maximizer. -/
theorem largePrimeFirstMaxSelector_le_of_mem_maximizerSet
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) {N : ℕ}
    (hN : N ∈ largePrimeMaximizerSet testSet cut j omega) :
    largePrimeFirstMaxSelector testSet cut j omega ≤ N := by
  classical
  unfold largePrimeFirstMaxSelector
  rw [dif_pos ⟨N, hN⟩]
  exact
    Finset.min'_le
      (largePrimeMaximizerSet testSet cut j omega) N hN

/-- Characterization of the deterministic first maximizer: it is exactly the
least point in the finite argmax set. -/
theorem largePrimeFirstMaxSelector_eq_iff
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j : ℕ) (omega : Omega) (htest : (testSet j).Nonempty)
    {N : ℕ} :
    largePrimeFirstMaxSelector testSet cut j omega = N ↔
      N ∈ largePrimeMaximizerSet testSet cut j omega ∧
        ∀ M,
          M ∈ largePrimeMaximizerSet testSet cut j omega →
            N ≤ M := by
  classical
  constructor
  · intro hN
    constructor
    · simpa [hN] using
        largePrimeFirstMaxSelector_mem_maximizerSet
          testSet cut j omega htest
    · intro M hM
      simpa [hN] using
        largePrimeFirstMaxSelector_le_of_mem_maximizerSet
          testSet cut j omega hM
  · rintro ⟨hNmem, hNleast⟩
    have hsel_mem :
        largePrimeFirstMaxSelector testSet cut j omega ∈
          largePrimeMaximizerSet testSet cut j omega :=
      largePrimeFirstMaxSelector_mem_maximizerSet
        testSet cut j omega htest
    have hsel_le_N :
        largePrimeFirstMaxSelector testSet cut j omega ≤ N :=
      largePrimeFirstMaxSelector_le_of_mem_maximizerSet
        testSet cut j omega hNmem
    have hN_le_sel :
        N ≤ largePrimeFirstMaxSelector testSet cut j omega :=
      hNleast
        (largePrimeFirstMaxSelector testSet cut j omega) hsel_mem
    exact le_antisymm hsel_le_N hN_le_sel

/-- The event that a fixed test point is the deterministic first argmax. -/
def largePrimeFirstMaxEvent
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j N : ℕ) : Set Omega :=
  {omega |
    N ∈ largePrimeMaximizerSet testSet cut j omega ∧
      ∀ M,
        M ∈ largePrimeMaximizerSet testSet cut j omega →
          N ≤ M}

/-- Membership in the first-argmax event is the same as being selected by the
deterministic first-max selector. -/
theorem mem_largePrimeFirstMaxEvent_iff_selector_eq
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ)
    (j N : ℕ) (omega : Omega) (htest : (testSet j).Nonempty) :
    omega ∈ largePrimeFirstMaxEvent testSet cut j N ↔
      largePrimeFirstMaxSelector testSet cut j omega = N := by
  classical
  simpa [largePrimeFirstMaxEvent] using
    (largePrimeFirstMaxSelector_eq_iff
      testSet cut j omega htest (N := N)).symm

/-- Smooth badness at a fixed first-argmax candidate. -/
def firstMaxSmoothBadAt
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (buffer : ℕ → ℝ)
    (j N : ℕ) : Set Omega :=
  {omega |
    omega ∈ largePrimeFirstMaxEvent testSet cut j N ∧
      smoothProcess omega (cut j) (N + 1) < -buffer j}

/-- Smooth badness at the deterministic first argmax decomposes over the finite
test mesh. This is the exact event the remaining analytic smooth estimate must
control. -/
theorem selectedSmoothBad_firstMaxSelector_iff_exists_firstMaxSmoothBadAt
    (testSet : ℕ → Finset ℕ) (cut : ℕ → ℕ) (buffer : ℕ → ℝ)
    (j : ℕ) (omega : Omega) (htest : (testSet j).Nonempty) :
    omega ∈ selectedSmoothBad cut buffer
        (largePrimeFirstMaxSelector testSet cut) j ↔
      ∃ N ∈ testSet j,
        omega ∈ firstMaxSmoothBadAt testSet cut buffer j N := by
  classical
  constructor
  · intro hbad
    refine
      ⟨largePrimeFirstMaxSelector testSet cut j omega,
        largePrimeFirstMaxSelector_mem testSet cut j omega htest, ?_⟩
    constructor
    · exact
        (mem_largePrimeFirstMaxEvent_iff_selector_eq
          testSet cut j
          (largePrimeFirstMaxSelector testSet cut j omega)
          omega htest).2 rfl
    · simpa [selectedSmoothBad] using hbad
  · rintro ⟨N, _hNtest, hbadAt⟩
    rcases hbadAt with ⟨hfirst, hsmooth⟩
    have hsel :
        largePrimeFirstMaxSelector testSet cut j omega = N :=
      (mem_largePrimeFirstMaxEvent_iff_selector_eq
        testSet cut j N omega htest).1 hfirst
    simpa [selectedSmoothBad, hsel] using hsmooth

/-- If the selected point has the large-prime win and its smooth remainder is
not too negative, then block failure is impossible. -/
theorem blockFailure_subset_selectedLargeFailure_union_selectedSmoothBad
    (lo hi cut : ℕ → ℕ) (M buffer : ℕ → ℝ)
    (testSet : ℕ → Finset ℕ) (selector : ℕ → Omega → ℕ) (j : ℕ)
    (selector_in_block :
      ∀ omega,
        selector j omega ∈ testSet j →
          selector j omega ∈ Finset.Icc (lo j) (hi j))
    (selector_in_range :
      ∀ omega,
        selector j omega ∈ testSet j →
          selector j omega + 1 < (cut j) ^ 2) :
    blockFailure lo hi M j ⊆
      selectedLargeFailure testSet cut M buffer selector j ∪
        selectedSmoothBad cut buffer selector j := by
  intro omega hfail
  by_cases hLarge :
      selectedLargeSuccess testSet cut M buffer selector omega j
  · by_cases hSmoothBad :
        omega ∈ selectedSmoothBad cut buffer selector j
    · exact Or.inr hSmoothBad
    · exfalso
      rcases hLarge with ⟨hsel, hlarge⟩
      have hsmooth :
          -buffer j ≤
            smoothProcess omega (cut j) (selector j omega + 1) := by
        exact not_lt.mp hSmoothBad
      have hsucc :
          blockSuccess lo hi M omega j :=
        blockSuccess_of_largePrimeProcess_ge_of_smoothProcess_ge
          lo hi cut M buffer omega j (selector j omega)
          (selector_in_block omega hsel)
          (selector_in_range omega hsel)
          hlarge
          hsmooth
      exact hfail hsucc
  · exact Or.inl hLarge

/-- Selector-based Harper block certificate.

This is the viable replacement for the all-mesh smooth-budget certificate. The
large-prime proof may use a mesh, but the smooth remainder is charged only at a
selected point, typically a winner or near-winner of the large-prime process. -/
structure HarperSelectorBlockCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  selector : ℕ → Omega → ℕ
  failLarge : ℕ → ℝ≥0∞
  failSmooth : ℕ → ℝ≥0∞
  selector_in_block :
    ∀ j omega,
      selector j omega ∈ testSet j →
        selector j omega ∈ Finset.Icc (lo j) (hi j)
  selector_in_range :
    ∀ j omega,
      selector j omega ∈ testSet j →
        selector j omega + 1 < (cut j) ^ 2
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  fail_summable :
    (∑' j, (failLarge j + failSmooth j)) ≠ ⊤
  prob_selected_large_fail :
    ∀ j,
      mu (selectedLargeFailure testSet cut M buffer selector j) ≤ failLarge j
  prob_selected_smooth_bad :
    ∀ j,
      mu (selectedSmoothBad cut buffer selector j) ≤ failSmooth j

/-- Selector-based Harper certificates imply the active positive block
certificate. -/
noncomputable def positiveBlockOmega_of_harperSelectorBlockCertificate
    (h : HarperSelectorBlockCertificate) :
    PositiveBlockOmega where
  X := h.lo
  Y := h.hi
  M := h.M
  fail := fun j => h.failLarge j + h.failSmooth j
  X_tendsto := h.lo_tendsto_atTop
  M_tendsto := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_fail := by
    intro j
    calc
      mu (blockFailure h.lo h.hi h.M j)
          ≤
          mu
            (selectedLargeFailure h.testSet h.cut h.M h.buffer
                h.selector j ∪
              selectedSmoothBad h.cut h.buffer h.selector j) := by
            exact
              measure_mono
                (blockFailure_subset_selectedLargeFailure_union_selectedSmoothBad
                  h.lo h.hi h.cut h.M h.buffer h.testSet h.selector j
                  (h.selector_in_block j)
                  (h.selector_in_range j))
      _ ≤
          mu
            (selectedLargeFailure h.testSet h.cut h.M h.buffer
              h.selector j) +
          mu (selectedSmoothBad h.cut h.buffer h.selector j) :=
            measure_union_le _ _
      _ ≤ h.failLarge j + h.failSmooth j :=
            add_le_add
              (h.prob_selected_large_fail j)
              (h.prob_selected_smooth_bad j)

/-- Direct closure from the selector-based Harper certificate. -/
theorem erdos1144_of_harperSelectorBlockCertificate
    (h : HarperSelectorBlockCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_harperSelectorBlockCertificate h)

/-- Concrete first-argmax selector certificate. The hard smooth estimate is now
only for the least selected maximizer, while the large-prime estimate can be
stated as the ordinary test-mesh maximum failure. -/
structure HarperMaxSelectorBlockCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  failLarge : ℕ → ℝ≥0∞
  failSmooth : ℕ → ℝ≥0∞
  testSet_nonempty : ∀ j, (testSet j).Nonempty
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  testSet_in_range :
    ∀ j N, N ∈ testSet j → N + 1 < (cut j) ^ 2
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  fail_summable :
    (∑' j, (failLarge j + failSmooth j)) ≠ ⊤
  prob_large_test_fail :
    ∀ j,
      mu (largePrimeTestFailure testSet cut M buffer j) ≤ failLarge j
  prob_selected_smooth_bad :
    ∀ j,
      mu
        (selectedSmoothBad cut buffer
          (largePrimeFirstMaxSelector testSet cut) j) ≤ failSmooth j

/-- The concrete first-argmax selector certificate supplies the general
selector certificate. -/
noncomputable def harperSelectorBlockCertificate_of_maxSelector
    (h : HarperMaxSelectorBlockCertificate) :
    HarperSelectorBlockCertificate where
  lo := h.lo
  hi := h.hi
  cut := h.cut
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  selector := largePrimeFirstMaxSelector h.testSet h.cut
  failLarge := h.failLarge
  failSmooth := h.failSmooth
  selector_in_block := by
    intro j omega hsel
    exact
      h.testSet_in_block j
        (largePrimeFirstMaxSelector h.testSet h.cut j omega) hsel
  selector_in_range := by
    intro j omega hsel
    exact
      h.testSet_in_range j
        (largePrimeFirstMaxSelector h.testSet h.cut j omega) hsel
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_selected_large_fail := by
    intro j
    rw [selectedLargeFailure_firstMaxSelector_eq_largePrimeTestFailure
      h.testSet h.cut h.M h.buffer j (h.testSet_nonempty j)]
    exact h.prob_large_test_fail j
  prob_selected_smooth_bad := h.prob_selected_smooth_bad

/-- Max-selector certificates imply the active positive block certificate. -/
noncomputable def positiveBlockOmega_of_harperMaxSelectorBlockCertificate
    (h : HarperMaxSelectorBlockCertificate) :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperSelectorBlockCertificate
    (harperSelectorBlockCertificate_of_maxSelector h)

/-- Direct closure from the concrete first-argmax certificate. -/
theorem erdos1144_of_harperMaxSelectorBlockCertificate
    (h : HarperMaxSelectorBlockCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_harperMaxSelectorBlockCertificate h)

/-- First-argmax event certificate.

This exposes the remaining smooth estimate as fixed-candidate bounds: for each
test point `N`, bound the probability that `N` is the deterministic first
large-prime maximizer and that the smooth remainder is too negative there. Lean
then performs only the finite union bound over the test mesh. -/
structure HarperFirstMaxEventBlockCertificate where
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  cut : ℕ → ℕ
  M : ℕ → ℝ
  buffer : ℕ → ℝ
  testSet : ℕ → Finset ℕ
  failLarge : ℕ → ℝ≥0∞
  failSmoothAt : ℕ → ℕ → ℝ≥0∞
  testSet_nonempty : ∀ j, (testSet j).Nonempty
  testSet_in_block :
    ∀ j N, N ∈ testSet j → N ∈ Finset.Icc (lo j) (hi j)
  testSet_in_range :
    ∀ j N, N ∈ testSet j → N + 1 < (cut j) ^ 2
  lo_tendsto_atTop : Tendsto lo atTop atTop
  M_tendsto_atTop : Tendsto M atTop atTop
  fail_summable :
    (∑' j,
      (failLarge j + Finset.sum (testSet j) (fun N => failSmoothAt j N))) ≠ ⊤
  prob_large_test_fail :
    ∀ j,
      mu (largePrimeTestFailure testSet cut M buffer j) ≤ failLarge j
  prob_firstMax_smooth_bad :
    ∀ j N,
      N ∈ testSet j →
        mu (firstMaxSmoothBadAt testSet cut buffer j N) ≤
          failSmoothAt j N

/-- Fixed-candidate first-argmax smooth estimates imply the concrete
first-argmax selector certificate. -/
noncomputable def harperMaxSelectorBlockCertificate_of_firstMaxEvent
    (h : HarperFirstMaxEventBlockCertificate) :
    HarperMaxSelectorBlockCertificate where
  lo := h.lo
  hi := h.hi
  cut := h.cut
  M := h.M
  buffer := h.buffer
  testSet := h.testSet
  failLarge := h.failLarge
  failSmooth := fun j =>
    Finset.sum (h.testSet j) (fun N => h.failSmoothAt j N)
  testSet_nonempty := h.testSet_nonempty
  testSet_in_block := h.testSet_in_block
  testSet_in_range := h.testSet_in_range
  lo_tendsto_atTop := h.lo_tendsto_atTop
  M_tendsto_atTop := h.M_tendsto_atTop
  fail_summable := h.fail_summable
  prob_large_test_fail := h.prob_large_test_fail
  prob_selected_smooth_bad := by
    intro j
    calc
      mu
          (selectedSmoothBad h.cut h.buffer
            (largePrimeFirstMaxSelector h.testSet h.cut) j)
          ≤
          mu
            (⋃ N ∈ h.testSet j,
              firstMaxSmoothBadAt h.testSet h.cut h.buffer j N) := by
            refine measure_mono ?_
            intro omega hbad
            rw [selectedSmoothBad_firstMaxSelector_iff_exists_firstMaxSmoothBadAt
              h.testSet h.cut h.buffer j omega (h.testSet_nonempty j)] at hbad
            rcases hbad with ⟨N, hN, hbadAt⟩
            exact Set.mem_iUnion.2 ⟨N, Set.mem_iUnion.2 ⟨hN, hbadAt⟩⟩
      _ ≤
          Finset.sum (h.testSet j) (fun N =>
            mu (firstMaxSmoothBadAt h.testSet h.cut h.buffer j N)) :=
            MeasureTheory.measure_biUnion_finset_le
              (h.testSet j)
              (fun N => firstMaxSmoothBadAt h.testSet h.cut h.buffer j N)
      _ ≤ Finset.sum (h.testSet j) (fun N => h.failSmoothAt j N) :=
            Finset.sum_le_sum fun N hN =>
              h.prob_firstMax_smooth_bad j N hN

/-- First-argmax event certificates imply the active positive block
certificate. -/
noncomputable def positiveBlockOmega_of_harperFirstMaxEventBlockCertificate
    (h : HarperFirstMaxEventBlockCertificate) :
    PositiveBlockOmega :=
  positiveBlockOmega_of_harperMaxSelectorBlockCertificate
    (harperMaxSelectorBlockCertificate_of_firstMaxEvent h)

/-- Direct closure from the fixed-candidate first-argmax event certificate. -/
theorem erdos1144_of_harperFirstMaxEventBlockCertificate
    (h : HarperFirstMaxEventBlockCertificate) :
    Erdos1144 :=
  erdos1144_of_positiveBlockOmega
    (positiveBlockOmega_of_harperFirstMaxEventBlockCertificate h)

end Problem1144
end Erdos
