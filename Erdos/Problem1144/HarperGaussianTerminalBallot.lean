import Erdos.Problem1144.HarperTerminalCappedBallot
import Erdos.Problem520.HarperScheduledOffDiagonalBarrier
import Erdos.Problem520.HarperBlockPath

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# The Gaussian terminal-cap estimate

A surviving walk which nevertheless misses the negative terminal cap is
controlled by two independent half-ballots.  The first half stays below the
original upper barrier.  Read backwards with signs reversed, the second half
stays below the terminal distance.  Sharp one-sided ballot upper bounds then
make the exceptional slice `O(log n / n)`.
-/

/-- Survival below a flat barrier is equivalent to the corresponding family
of partial-sum inequalities. -/
theorem gaussianWalkSurvives_iff_harperPathPartialSum_le
    (n : Nat) (x : Real) (omega : Fin n -> Real) :
    Problem520.gaussianWalkSurvives n x omega ↔
      ∀ k, Problem520.harperPathPartialSum omega k <= x := by
  constructor
  · intro h k
    exact harperPathPartialSum_le_of_gaussianWalkSurvives n x omega h k
  · intro h
    induction n generalizing x with
    | zero => trivial
    | succ n ih =>
        constructor
        · simpa only [Problem520.harperPathPartialSum_zero] using h 0
        · apply ih (x - omega 0) (fun i => omega i.succ)
          intro k
          have hk := h k.succ
          rw [Problem520.harperPathPartialSum_succ] at hk
          linarith

/-- Reverse the order of a finite increment vector and negate every
coordinate. -/
def harperReverseNegate {n : Nat} (omega : Fin n -> Real) : Fin n -> Real :=
  fun i => -omega i.rev

/-- A prefix of the reverse-negated vector is the negative of the
corresponding terminal suffix of the original vector. -/
theorem harperPathPartialSum_reverseNegate
    {n : Nat} (omega : Fin n -> Real) (k : Fin n) :
    Problem520.harperPathPartialSum (harperReverseNegate omega) k =
      -∑ i ∈ Finset.Ici k.rev, omega i := by
  unfold Problem520.harperPathPartialSum harperReverseNegate
  rw [Finset.sum_neg_distrib]
  congr 1
  calc
    (∑ i ∈ Finset.Iic k, omega i.rev) =
        ∑ i ∈ (Finset.Iic k).map Fin.revPerm.toEmbedding, omega i := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [show Fin.revPerm.toEmbedding i = i.rev by
        exact Fin.revPerm_apply i]
    _ = ∑ i ∈ Finset.Ici k.rev, omega i := by
      rw [Fin.map_revPerm_Iic]

/-- Split a vector of length `m+n` into its consecutive pieces. -/
def harperFinSplit {m n : Nat} (omega : Fin (m + n) -> Real) :
    (Fin m -> Real) × (Fin n -> Real) :=
  (fun i => omega (Fin.castAdd n i), fun j => omega (Fin.natAdd m j))

/-- Reassembling the two pieces selected by `harperFinSplit` recovers the
original vector. -/
theorem harperFinSplit_addCases
    {m n : Nat} (omega : Fin (m + n) -> Real) :
    Fin.addCases (harperFinSplit omega).1 (harperFinSplit omega).2 = omega := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [harperFinSplit]
  · intro j
    simp [harperFinSplit]

/-- Exact decomposition of the terminal sum at the midpoint. -/
theorem sum_harperFinSplit
    {m n : Nat} (omega : Fin (m + n) -> Real) :
    (∑ i, omega i) =
      (∑ i, (harperFinSplit omega).1 i) +
        ∑ j, (harperFinSplit omega).2 j := by
  simpa only [harperFinSplit] using Fin.sum_univ_add omega

private theorem map_Iic_castAdd {m : Nat} (k : Fin m) :
    (Finset.Iic k).map (Fin.castAddEmb m) =
      Finset.Iic (Fin.castAdd m k) := by
  ext i
  simp only [Finset.mem_map, Finset.mem_Iic, Fin.castAddEmb_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact_mod_cast hj
  · intro hi
    have hiv : i.val < m := lt_of_le_of_lt (by exact_mod_cast hi) k.isLt
    let j : Fin m := ⟨i.val, hiv⟩
    refine ⟨j, ?_, Fin.ext ?_⟩
    · exact_mod_cast hi
    · rfl

private theorem map_split_prefix {m : Nat} (k : Fin m) (hk : 0 < k.val) :
    (Finset.univ.map (Fin.castAddEmb m)) ∪
        ((Finset.Iio k).map (Fin.natAddEmb m)) =
      Finset.Iic (⟨m + (k.val - 1), by omega⟩ : Fin (m + m)) := by
  ext q
  refine Fin.addCases ?_ ?_ q
  · intro i
    have hleft : Fin.castAdd m i ∈
        Finset.univ.map (Fin.castAddEmb m) :=
      Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hright : Fin.castAdd m i ∈
        Finset.Iic
          (⟨m + (k.val - 1), by omega⟩ : Fin (m + m)) := by
      simp only [Finset.mem_Iic]
      change i.val ≤ m + (k.val - 1)
      omega
    simp only [Finset.mem_union]
    exact iff_of_true (Or.inl hleft) hright
  · intro i
    have hnotleft : Fin.natAdd m i ∉
        Finset.univ.map (Fin.castAddEmb m) := by
      intro h
      obtain ⟨j, _hj, heq⟩ := Finset.mem_map.mp h
      have hval := congrArg Fin.val heq
      simp only [Fin.castAddEmb_apply, Fin.val_castAdd,
        Fin.val_natAdd] at hval
      omega
    have hsecond : Fin.natAdd m i ∈
          (Finset.Iio k).map (Fin.natAddEmb m) ↔ i < k := by
      constructor
      · intro h
        obtain ⟨j, hj, heq⟩ := Finset.mem_map.mp h
        have hji : j = i := by
          apply Fin.ext
          have hval := congrArg Fin.val heq
          simpa only [Fin.natAddEmb_apply, Fin.val_natAdd] using
            Nat.add_left_cancel hval
        simpa only [Finset.mem_Iio, hji] using hj
      · intro hi
        exact Finset.mem_map.mpr
          ⟨i, Finset.mem_Iio.mpr hi, rfl⟩
    have htarget : Fin.natAdd m i ∈
          Finset.Iic
            (⟨m + (k.val - 1), by omega⟩ : Fin (m + m)) ↔ i < k := by
      simp only [Finset.mem_Iic]
      change m + i.val ≤ m + (k.val - 1) ↔ i.val < k.val
      omega
    simp only [Finset.mem_union, hnotleft, false_or, hsecond, htarget]

/-- The key deterministic two-half implication.  If a full even-length walk
survives below `x` and has terminal distance at most `r`, then its first half
survives below `x`, while its reversed and negated second half survives below
`r`. -/
theorem gaussianWalkSurvives_halves_of_terminalDistance_le
    (m : Nat) (x r : Real) (omega : Fin (m + m) -> Real)
    (hsurv : Problem520.gaussianWalkSurvives (m + m) x omega)
    (hterminal : Problem520.gaussianWalkTerminalDistance (m + m) x omega <= r) :
    Problem520.gaussianWalkSurvives m x (harperFinSplit omega).1 ∧
      Problem520.gaussianWalkSurvives m r
        (harperReverseNegate (harperFinSplit omega).2) := by
  let u : Fin m -> Real := (harperFinSplit omega).1
  let v : Fin m -> Real := (harperFinSplit omega).2
  have hall : ∀ k, Problem520.harperPathPartialSum omega k <= x :=
    (gaussianWalkSurvives_iff_harperPathPartialSum_le
      (m + m) x omega).mp hsurv
  have hfirst : Problem520.gaussianWalkSurvives m x u := by
    apply (gaussianWalkSurvives_iff_harperPathPartialSum_le m x u).mpr
    intro k
    let j : Fin (m + m) := Fin.castAdd m k
    have hj := hall j
    unfold Problem520.harperPathPartialSum at hj ⊢
    calc
      (∑ i ∈ Finset.Iic k, u i) =
          ∑ i ∈ (Finset.Iic k).map (Fin.castAddEmb m), omega i := by
        rw [Finset.sum_map]
        rfl
      _ = ∑ i ∈ Finset.Iic j, omega i := by
        rw [show j = Fin.castAdd m k by rfl, map_Iic_castAdd]
      _ ≤ x := hj
  refine ⟨hfirst, ?_⟩
  apply (gaussianWalkSurvives_iff_harperPathPartialSum_le m r
    (harperReverseNegate v)).mpr
  intro k
  rw [harperPathPartialSum_reverseNegate]
  have htotal : x - ((∑ i, u i) + ∑ i, v i) <= r := by
    simpa only [Problem520.gaussianWalkTerminalDistance,
      sum_harperFinSplit, u, v] using hterminal
  by_cases hkzero : k.rev.val = 0
  · have hIci : Finset.Ici k.rev = Finset.univ := by
      ext i
      simp only [Finset.mem_Ici, Finset.mem_univ, iff_true]
      exact Fin.le_iff_val_le_val.mpr (by omega)
    rw [hIci]
    have hmpos : 0 < m := Nat.zero_lt_of_lt k.isLt
    let last : Fin m := ⟨m - 1, by omega⟩
    have hlast := harperPathPartialSum_le_of_gaussianWalkSurvives
      m x u hfirst last
    have hIicLast : Finset.Iic last = Finset.univ := by
      ext i
      simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
      apply Fin.le_iff_val_le_val.mpr
      dsimp [last]
      omega
    unfold Problem520.harperPathPartialSum at hlast
    rw [hIicLast] at hlast
    linarith
  · let j0 : Nat := k.rev.val - 1
    have hj0lt : j0 < m := by
      dsimp [j0]
      omega
    let j : Fin (m + m) :=
      ⟨m + j0, by dsimp [j0]; omega⟩
    have hj := hall j
    have hAB : Disjoint
        (Finset.univ.map (Fin.castAddEmb m))
        ((Finset.Iio k.rev).map (Fin.natAddEmb m)) := by
      rw [Finset.disjoint_left]
      intro q hqA hqB
      obtain ⟨a, _ha, haeq⟩ := Finset.mem_map.mp hqA
      obtain ⟨b, _hb, hbeq⟩ := Finset.mem_map.mp hqB
      have hval := congrArg Fin.val (haeq.trans hbeq.symm)
      simp only [Fin.castAddEmb_apply, Fin.natAddEmb_apply,
        Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
    have hdecomp :
        (∑ i ∈ Finset.Iic j, omega i) =
          (∑ i, u i) + ∑ i ∈ Finset.Iio k.rev, v i := by
      calc
        (∑ i ∈ Finset.Iic j, omega i) =
            ∑ i ∈
              (Finset.univ.map (Fin.castAddEmb m)) ∪
                ((Finset.Iio k.rev).map (Fin.natAddEmb m)), omega i := by
          rw [map_split_prefix k.rev (by omega)]
        _ = (∑ i ∈ Finset.univ.map (Fin.castAddEmb m), omega i) +
            ∑ i ∈ (Finset.Iio k.rev).map (Fin.natAddEmb m), omega i := by
          rw [Finset.sum_union hAB]
        _ = (∑ i, u i) + ∑ i ∈ Finset.Iio k.rev, v i := by
          rw [Finset.sum_map, Finset.sum_map]
          rfl
    have hdisj : Disjoint (Finset.Iio k.rev) (Finset.Ici k.rev) := by
      rw [Finset.disjoint_left]
      intro i hi hci
      exact (not_le_of_gt (Finset.mem_Iio.mp hi))
        (Finset.mem_Ici.mp hci)
    have hunion : Finset.Iio k.rev ∪ Finset.Ici k.rev = Finset.univ := by
      ext i
      simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici,
        Finset.mem_univ, iff_true]
      exact lt_or_ge i k.rev
    have hvSplit :
        (∑ i, v i) =
          (∑ i ∈ Finset.Iio k.rev, v i) +
            ∑ i ∈ Finset.Ici k.rev, v i := by
      rw [← Finset.sum_union hdisj, hunion]
    unfold Problem520.harperPathPartialSum at hj
    rw [hdecomp] at hj
    linarith

/-- Splitting a finite Gaussian vector into consecutive coordinate blocks is
measure preserving from the full product law to the product of the two block
laws. -/
theorem measurePreserving_harperFinSplit
    (m n : Nat) (variance : Fin (m + n) -> NNReal) :
    MeasurePreserving (harperFinSplit (m := m) (n := n))
      (Measure.pi (fun i : Fin (m + n) => gaussianReal 0 (variance i)))
      ((Measure.pi (fun i : Fin m =>
          gaussianReal 0 (variance (Fin.castAdd n i)))).prod
        (Measure.pi (fun j : Fin n =>
          gaussianReal 0 (variance (Fin.natAdd m j))))) := by
  let laws : Fin (m + n) -> Measure Real :=
    fun i => gaussianReal 0 (variance i)
  let E : (Fin m ⊕ Fin n -> Real) ≃ᵐ (Fin (m + n) -> Real) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) => Real)
      (finSumFinEquiv (m := m) (n := n))
  have hcongr := measurePreserving_piCongrLeft laws
    (finSumFinEquiv (m := m) (n := n))
  have hsum := measurePreserving_sumPiEquivProdPi
    (fun sigma : Fin m ⊕ Fin n => laws (finSumFinEquiv sigma))
  exact hsum.comp (hcongr.symm E)

/-- Reversal followed by coordinatewise negation preserves a centered
Gaussian product law, up to reversing its variance vector. -/
theorem measurePreserving_harperReverseNegate
    (n : Nat) (variance : Fin n -> NNReal) :
    MeasurePreserving (harperReverseNegate (n := n))
      (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i)))
      (Measure.pi (fun j : Fin n => gaussianReal 0 (variance j.rev))) := by
  have hcoordinate : ∀ i : Fin n,
      MeasurePreserving (MeasurableEquiv.neg Real)
        (gaussianReal 0 (variance i))
        (gaussianReal 0 (variance (Fin.revPerm i).rev)) := by
    intro i
    constructor
    · exact (MeasurableEquiv.neg Real).measurable
    · simpa only [Fin.revPerm_apply, Fin.rev_rev, neg_zero] using
        (gaussianReal_map_neg (μ := (0 : Real)) (v := variance i))
  exact measurePreserving_arrowCongr'
    (fun i : Fin n => gaussianReal 0 (variance i))
    (fun j : Fin n => gaussianReal 0 (variance j.rev))
    Fin.revPerm (MeasurableEquiv.neg Real) hcoordinate

/-- Walks which survive below `x` but finish within terminal distance `r` of
that upper barrier.  This is the exceptional slice removed by the negative
terminal cap. -/
def gaussianWalkTerminalNearSet (n : Nat) (x r : Real) :
    Set (Fin n -> Real) :=
  Problem520.gaussianWalkSurvivalSet n x ∩
    {omega | Problem520.gaussianWalkTerminalDistance n x omega <= r}

theorem measurableSet_gaussianWalkTerminalNearSet
    (n : Nat) {x r : Real} (hx : 0 <= x) :
    MeasurableSet (gaussianWalkTerminalNearSet n x r) := by
  apply (Problem520.measurableSet_gaussianWalkSurvivalSet n hx).inter
  unfold Problem520.gaussianWalkTerminalDistance
  exact measurableSet_le
    (measurable_const.sub
      (Finset.measurable_sum _ fun i _hi => measurable_pi_apply i))
    measurable_const

/-- A surviving even-length walk which finishes within distance `r` of its
barrier has probability at most the product of two sharp half-walk ballot
bounds.  At `x = 1` and `r = O(log m)` this is `O(log m / m)`. -/
theorem gaussianWalkTerminalNear_probability_le_two_half_ballots
    (m : Nat) (hm : 0 < m) (variance : Fin (m + m) -> NNReal)
    {x r : Real} (hx : 0 <= x) (hr : 0 <= r)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    (Measure.pi (fun i : Fin (m + m) =>
        gaussianReal 0 (variance i))).real
          (gaussianWalkTerminalNearSet (m + m) x r) <=
      (64 * (x + 2) / Real.sqrt (m : Real)) *
        (64 * (r + 2) / Real.sqrt (m : Real)) := by
  let P : Measure (Fin (m + m) -> Real) :=
    Measure.pi (fun i : Fin (m + m) => gaussianReal 0 (variance i))
  let P1 : Measure (Fin m -> Real) :=
    Measure.pi (fun i : Fin m =>
      gaussianReal 0 (variance (Fin.castAdd m i)))
  let P2 : Measure (Fin m -> Real) :=
    Measure.pi (fun j : Fin m =>
      gaussianReal 0 (variance (Fin.natAdd m j)))
  let P2rev : Measure (Fin m -> Real) :=
    Measure.pi (fun j : Fin m =>
      gaussianReal 0 (variance (Fin.natAdd m j.rev)))
  let A : Set (Fin m -> Real) :=
    Problem520.gaussianWalkSurvivalSet m x
  let B : Set (Fin m -> Real) :=
    {v | Problem520.gaussianWalkSurvives m r (harperReverseNegate v)}
  have hA : MeasurableSet A :=
    Problem520.measurableSet_gaussianWalkSurvivalSet m hx
  have hrev := measurePreserving_harperReverseNegate m
    (fun j : Fin m => variance (Fin.natAdd m j))
  have hB : MeasurableSet B := by
    exact (Problem520.measurableSet_gaussianWalkSurvivalSet m hr).preimage
      hrev.measurable
  have hsplit := measurePreserving_harperFinSplit m m variance
  have hsubset : gaussianWalkTerminalNearSet (m + m) x r <=
      harperFinSplit ⁻¹' (A ×ˢ B) := by
    intro omega homega
    exact gaussianWalkSurvives_halves_of_terminalDistance_le m x r omega
      homega.1 homega.2
  have htransport :
      P.real (harperFinSplit ⁻¹' (A ×ˢ B)) =
        (P1.prod P2).real (A ×ˢ B) := by
    symm
    rw [← hsplit.map_eq]
    exact map_measureReal_apply hsplit.measurable (hA.prod hB)
  have hprod :
      (P1.prod P2).real (A ×ˢ B) = P1.real A * P2.real B := by
    simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  have hreverse : P2.real B =
      P2rev.real (Problem520.gaussianWalkSurvivalSet m r) := by
    change (Measure.pi (fun j : Fin m =>
        gaussianReal 0 (variance (Fin.natAdd m j)))).real B =
      (Measure.pi (fun j : Fin m =>
        gaussianReal 0 (variance (Fin.natAdd m j.rev)))).real
          (Problem520.gaussianWalkSurvivalSet m r)
    rw [← hrev.map_eq]
    exact (map_measureReal_apply hrev.measurable
      (Problem520.measurableSet_gaussianWalkSurvivalSet m hr)).symm
  have hfirst : P1.real A <=
      64 * (x + 2) / Real.sqrt (m : Real) := by
    exact Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
      m hm (fun i => variance (Fin.castAdd m i)) hx
        (fun i => hlower _) (fun i => hupper _)
  have hsecond : P2.real B <=
      64 * (r + 2) / Real.sqrt (m : Real) := by
    rw [hreverse]
    exact Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
      m hm (fun j => variance (Fin.natAdd m j.rev)) hr
        (fun j => hlower _) (fun j => hupper _)
  calc
    P.real (gaussianWalkTerminalNearSet (m + m) x r) <=
        P.real (harperFinSplit ⁻¹' (A ×ˢ B)) := measureReal_mono hsubset
    _ = (P1.prod P2).real (A ×ˢ B) := htransport
    _ = P1.real A * P2.real B := hprod
    _ <= (64 * (x + 2) / Real.sqrt (m : Real)) *
        (64 * (r + 2) / Real.sqrt (m : Real)) := by
      exact mul_le_mul hfirst hsecond measureReal_nonneg (by positivity)

/-- The Gaussian ballot event with an additional upper cap on its terminal
centered sum. -/
def gaussianWalkTerminalCappedSurvivalSet
    (n : Nat) (x cap : Real) : Set (Fin n -> Real) :=
  Problem520.gaussianWalkSurvivalSet n x ∩
    {omega | (∑ i, omega i) <= cap}

theorem measurableSet_gaussianWalkTerminalCappedSurvivalSet
    (n : Nat) {x cap : Real} (hx : 0 <= x) :
    MeasurableSet (gaussianWalkTerminalCappedSurvivalSet n x cap) := by
  apply (Problem520.measurableSet_gaussianWalkSurvivalSet n hx).inter
  exact measurableSet_le
    (Finset.measurable_sum _ fun i _hi => measurable_pi_apply i)
    measurable_const

/-- If the explicit two-half exceptional-slice bound costs at most half of
the ordinary Gaussian ballot mass, the terminal-capped ballot retains the
other half.  This separates the probability argument from the elementary
eventual numerical comparison. -/
theorem half_exp_neg_two_div_sqrt_le_gaussianTerminalCapped_probability
    (m : Nat) (hm : 0 < m) (variance : Fin (m + m) -> NNReal)
    {cap : Real} (hcap : cap <= 1)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal))
    (hbudget :
      (64 * ((1 : Real) + 2) / Real.sqrt (m : Real)) *
          (64 * ((1 - cap) + 2) / Real.sqrt (m : Real)) <=
        (1 / 2 : Real) *
          (Real.exp (-2) / Real.sqrt ((m + m : Nat) : Real))) :
    (1 / 2 : Real) *
        (Real.exp (-2) / Real.sqrt ((m + m : Nat) : Real)) <=
      (Measure.pi (fun i : Fin (m + m) =>
        gaussianReal 0 (variance i))).real
          (gaussianWalkTerminalCappedSurvivalSet (m + m) 1 cap) := by
  let P : Measure (Fin (m + m) -> Real) :=
    Measure.pi (fun i : Fin (m + m) => gaussianReal 0 (variance i))
  let S : Set (Fin (m + m) -> Real) :=
    Problem520.gaussianWalkSurvivalSet (m + m) 1
  let C : Set (Fin (m + m) -> Real) :=
    gaussianWalkTerminalCappedSurvivalSet (m + m) 1 cap
  let R : Set (Fin (m + m) -> Real) :=
    gaussianWalkTerminalNearSet (m + m) 1 (1 - cap)
  have hcover : S <= C ∪ R := by
    intro omega homega
    by_cases hsum : (∑ i, omega i) <= cap
    · exact Or.inl ⟨homega, hsum⟩
    · exact Or.inr ⟨homega, by
        change (1 : Real) - (∑ i, omega i) <= 1 - cap
        have hsum' : cap < ∑ i, omega i := lt_of_not_ge hsum
        linarith⟩
  have hsurvLower :
      Real.exp (-2) / Real.sqrt ((m + m : Nat) : Real) <= P.real S := by
    exact exp_neg_two_div_sqrt_le_gaussianVarianceWalk_probability_fin
      (m + m) (by omega) variance hlower hupper
  have hnear : P.real R <=
      (1 / 2 : Real) *
        (Real.exp (-2) / Real.sqrt ((m + m : Nat) : Real)) := by
    exact (gaussianWalkTerminalNear_probability_le_two_half_ballots
      m hm variance (x := (1 : Real)) (r := 1 - cap)
      (by norm_num) (sub_nonneg.2 hcap) hlower hupper).trans hbudget
  have hupperCover : P.real S <= P.real C + P.real R :=
    (measureReal_mono hcover).trans (measureReal_union_le C R)
  linarith

/-- The logarithmic terminal distance is negligible compared with the square
root walk scale. -/
theorem tendsto_harperTerminalBallot_ratio :
    Tendsto (fun x : Real =>
      (3 + 2 * Real.log (2 * x)) / Real.sqrt x)
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun x : Real => Real.sqrt x) atTop atTop :=
    Real.tendsto_sqrt_atTop
  have hlog : Tendsto (fun x : Real =>
      Real.log x / Real.sqrt x) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop
        (by norm_num : (0 : Real) < 1 / 2)).tendsto_div_nhds_zero
  have hconst : Tendsto (fun x : Real =>
      (3 + 2 * Real.log 2) / Real.sqrt x)
      atTop (nhds 0) := by
    simpa only [zero_div] using
      (tendsto_const_nhds.div_atTop hsqrt :
        Tendsto (fun x : Real =>
          (3 + 2 * Real.log 2) / Real.sqrt x)
          atTop (nhds 0))
  have hlogTwo : Tendsto (fun x : Real =>
      2 * (Real.log x / Real.sqrt x)) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlog
  have hmain := hconst.add hlogTwo
  have heq : (fun x : Real =>
      (3 + 2 * Real.log (2 * x)) / Real.sqrt x) =ᶠ[atTop]
      (fun x : Real =>
        (3 + 2 * Real.log 2) / Real.sqrt x +
          2 * (Real.log x / Real.sqrt x)) := by
    filter_upwards [eventually_gt_atTop (0 : Real)] with x hx
    rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hx.ne']
    ring
  simpa only [add_zero] using hmain.congr' heq.symm

/-- The explicit two-half error is eventually at most half of the uncapped
Gaussian ballot lower bound for the logarithmic terminal cap. -/
theorem eventually_harperTerminalBallot_budget :
    ∀ᶠ m : Nat in atTop,
      (64 * ((1 : Real) + 2) / Real.sqrt (m : Real)) *
          (64 *
              ((1 - harperTerminalCenteredCap (m + m)) + 2) /
            Real.sqrt (m : Real)) <=
        (1 / 2 : Real) *
          (Real.exp (-2) / Real.sqrt ((m + m : Nat) : Real)) := by
  have htNat := tendsto_harperTerminalBallot_ratio.comp
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun m : Nat => (m : Real)) atTop atTop)
  have hc : 0 < Real.exp (-2) / (49152 : Real) := by positivity
  have hsmall := htNat.eventually (eventually_lt_nhds hc)
  filter_upwards [hsmall, eventually_ge_atTop 1] with m hratio hm
  have hmpos : 0 < m := by omega
  have ha : 0 < Real.sqrt (m : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast hmpos)
  have hq : 0 < Real.sqrt ((m + m : Nat) : Real) :=
    Real.sqrt_pos.2 (by exact_mod_cast (show 0 < m + m by omega))
  change (3 + 2 * Real.log (2 * (m : Real))) /
      Real.sqrt (m : Real) < Real.exp (-2) / 49152 at hratio
  have harg : 2 * (m : Real) = ((m + m : Nat) : Real) := by
    push_cast
    ring
  rw [harg] at hratio
  have hsqrtBound : Real.sqrt ((m + m : Nat) : Real) <=
      2 * Real.sqrt (m : Real) := by
    rw [show ((m + m : Nat) : Real) = 2 * (m : Real) by
        push_cast; ring,
      Real.sqrt_mul (by norm_num : (0 : Real) <= 2)]
    have hsqrtTwo : Real.sqrt (2 : Real) <= 2 := by
      rw [Real.sqrt_le_iff]
      norm_num
    exact mul_le_mul_of_nonneg_right hsqrtTwo (Real.sqrt_nonneg _)
  have hleft :
      (64 * ((1 : Real) + 2) / Real.sqrt (m : Real)) *
          (64 *
              ((1 - harperTerminalCenteredCap (m + m)) + 2) /
            Real.sqrt (m : Real)) <=
        Real.exp (-2) / (4 * Real.sqrt (m : Real)) := by
    unfold harperTerminalCenteredCap
    rw [show ((1 - (-2 * Real.log ((m + m : Nat) : Real))) + 2) =
        3 + 2 * Real.log ((m + m : Nat) : Real) by ring]
    calc
      (64 * ((1 : Real) + 2) / Real.sqrt (m : Real)) *
          (64 * (3 + 2 * Real.log ((m + m : Nat) : Real)) /
            Real.sqrt (m : Real)) =
          (192 / Real.sqrt (m : Real)) *
            (64 * ((3 + 2 * Real.log ((m + m : Nat) : Real)) /
                Real.sqrt (m : Real))) := by ring
      _ <= (192 / Real.sqrt (m : Real)) *
          (64 * (Real.exp (-2) / 49152)) := by
        gcongr
      _ = Real.exp (-2) / (4 * Real.sqrt (m : Real)) := by
        field_simp
        ring
  calc
    (64 * ((1 : Real) + 2) / Real.sqrt (m : Real)) *
        (64 * ((1 - harperTerminalCenteredCap (m + m)) + 2) /
          Real.sqrt (m : Real)) <=
      Real.exp (-2) / (4 * Real.sqrt (m : Real)) := hleft
    _ <= (1 / 2 : Real) *
        (Real.exp (-2) / Real.sqrt ((m + m : Nat) : Real)) := by
      rw [show (1 / 2 : Real) *
          (Real.exp (-2) / Real.sqrt ((m + m : Nat) : Real)) =
        Real.exp (-2) / (2 * Real.sqrt ((m + m : Nat) : Real)) by ring]
      apply (div_le_div_iff₀ (by positivity :
        0 < 4 * Real.sqrt (m : Real)) (by positivity :
        0 < 2 * Real.sqrt ((m + m : Nat) : Real))).2
      nlinarith [Real.exp_pos (-2)]

/-- For all sufficiently long even walks, the logarithmic terminal-capped
Gaussian ballot has the same `1 / sqrt n` order as the uncapped ballot,
uniformly over variance vectors in `[1/4,1/2]`. -/
theorem eventually_half_exp_neg_two_div_sqrt_le_gaussianTerminalCapped_probability :
    ∀ᶠ m : Nat in atTop, ∀ variance : Fin (m + m) -> NNReal,
      (∀ i, (1 / 4 : NNReal) <= variance i) ->
      (∀ i, variance i <= (1 / 2 : NNReal)) ->
      (1 / 2 : Real) *
          (Real.exp (-2) / Real.sqrt ((m + m : Nat) : Real)) <=
        (Measure.pi (fun i : Fin (m + m) =>
          gaussianReal 0 (variance i))).real
            (gaussianWalkTerminalCappedSurvivalSet (m + m) 1
              (harperTerminalCenteredCap (m + m))) := by
  filter_upwards [eventually_harperTerminalBallot_budget,
    eventually_ge_atTop 1] with m hbudget hm
  intro variance hlower hupper
  have hmpos : 0 < m := by omega
  have hcap : harperTerminalCenteredCap (m + m) <= (1 : Real) := by
    unfold harperTerminalCenteredCap
    have hlog : 0 <= Real.log ((m + m : Nat) : Real) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 <= m + m by omega)
    nlinarith
  exact half_exp_neg_two_div_sqrt_le_gaussianTerminalCapped_probability
    m hmpos variance hcap hlower hupper hbudget

/-- From length eight onward, the safety-margin terminal level is below the
ordinary flat upper barrier `1`. -/
theorem harperTerminalCappedEventLevel_le_one
    {n : Nat} (hn : 8 <= n) :
    harperTerminalCappedEventLevel n <= (1 : Real) := by
  have hnpos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogmono : Real.log (8 : Real) <= Real.log (n : Real) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlog8 : (2 : Real) <= Real.log 8 := by
    rw [show (8 : Real) = 2 ^ (3 : Nat) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith [Real.log_two_gt_d9]
  unfold harperTerminalCappedEventLevel harperTerminalCenteredCap
  nlinarith

/-- A prefix indexed by the last coordinate is the full terminal sum. -/
theorem harperPathPartialSum_eq_terminal_sum
    {n : Nat} (omega : Fin n -> Real) (k : Fin n)
    (hk : k.val + 1 = n) :
    Problem520.harperPathPartialSum omega k = ∑ i, omega i := by
  unfold Problem520.harperPathPartialSum
  have hIic : Finset.Iic k = Finset.univ := by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_univ, iff_true]
    apply Fin.le_iff_val_le_val.mpr
    omega
  rw [hIic]

/-- The reverse-slicing target upper barrier.  It is ordinary and flat away
from the last time, where it imposes the safety-margin terminal cap. -/
noncomputable def harperScheduledTerminalCappedUpperBarrier
    (start n : Nat) (k : Fin n) : Real :=
  if k.val + 1 = n then harperTerminalCappedEventLevel n
  else harperScheduledAutomaticUpperBarrier start n k

/-- The exact Gaussian terminal-capped ballot, inside the moderate box, lies
inside the cumulatively contracted terminal barrier used by reverse finite
slicing.  The fixed safety margin `2` exactly pays for the universal mesh
width bound. -/
theorem gaussianTerminalCapped_inter_box_subset_contractedTerminalBarrier
    (start n : Nat) :
    gaussianWalkTerminalCappedSurvivalSet n 1
          (harperTerminalCenteredCap n) ∩
        Problem520.harperCoordinateBox
          (Problem520.harperScheduledModerateRadius start n) <=
      Problem520.harperPartialSumBarrierSet
          (fun k => harperScheduledAutomaticLowerBarrier start n k +
            Problem520.harperCumulativeCellWidth
              (Problem520.harperScheduledRelativeCellWidth start n) k)
          (fun k => harperScheduledTerminalCappedUpperBarrier start n k -
            Problem520.harperCumulativeCellWidth
              (Problem520.harperScheduledRelativeCellWidth start n) k) ∩
        Problem520.harperCoordinateBox
          (Problem520.harperScheduledModerateRadius start n) := by
  rintro omega ⟨⟨hsurv, hterminal⟩, hbox⟩
  refine ⟨?_, hbox⟩
  intro k
  let R := Problem520.harperScheduledModerateRadius start n
  let delta := Problem520.harperScheduledRelativeCellWidth start n
  have hlowerPath :
      -(∑ i ∈ Finset.Iic k, R i) <=
        Problem520.harperPathPartialSum omega k := by
    unfold Problem520.harperPathPartialSum
    have hcoord : ∀ i ∈ Finset.Iic k, -R i <= omega i := by
      intro i _hi
      exact (abs_le.mp ((Problem520.mem_harperCoordinateBox.mp hbox) i)).1
    have hsum := Finset.sum_le_sum hcoord
    simpa only [Finset.sum_neg_distrib] using hsum
  constructor
  · dsimp only [harperScheduledAutomaticLowerBarrier, delta, R]
    linarith
  · by_cases hk : k.val + 1 = n
    · have hsum : Problem520.harperPathPartialSum omega k <=
          harperTerminalCenteredCap n := by
        rw [harperPathPartialSum_eq_terminal_sum omega k hk]
        exact hterminal
      have hwidth :=
        Problem520.harperCumulativeScheduledRelativeCellWidth_le_two
          start n k
      dsimp only [harperScheduledTerminalCappedUpperBarrier]
      rw [if_pos hk]
      unfold harperTerminalCappedEventLevel
      linarith
    · have hupperPath : Problem520.harperPathPartialSum omega k <= 1 :=
        harperPathPartialSum_le_of_gaussianWalkSurvives n 1 omega hsurv k
      dsimp only [harperScheduledTerminalCappedUpperBarrier,
        harperScheduledAutomaticUpperBarrier]
      rw [if_neg hk]
      linarith

/-- The terminal barrier is a literal subset of the terminal-capped Harper
ballot event.  Length eight ensures its last upper level is also below the
ordinary flat barrier. -/
theorem harperTerminalBarrier_preimage_subset_cappedBallotEvent
    (y start n : Nat) (hn : 8 <= n) (t : Real) :
    (Problem520.harperScheduledCenteredBlockVectorVarying
        y start n t (fun _i : Fin n => t)) ⁻¹'
      Problem520.harperPartialSumBarrierSet
        (harperScheduledAutomaticLowerBarrier start n)
        (harperScheduledTerminalCappedUpperBarrier start n) <=
      harperTerminalCappedCentralLowerBallotCubeEvent y start n t := by
  intro eta heta
  have hlevel := harperTerminalCappedEventLevel_le_one hn
  have hcentral : eta ∈ harperCentralLowerBallotCubeEvent y start n t := by
    change Problem520.harperScheduledCenteredBlockVectorVarying
        y start n t (fun _i : Fin n => t) eta ∈
      Problem520.harperPartialSumBarrierSet
        (harperScheduledAutomaticLowerBarrier start n)
        (harperScheduledAutomaticUpperBarrier start n)
    intro k
    have hkbar := heta k
    refine ⟨hkbar.1, ?_⟩
    by_cases hk : k.val + 1 = n
    · have hwidth : 0 <= Problem520.harperCumulativeCellWidth
          (Problem520.harperScheduledRelativeCellWidth start n) k := by
        exact Problem520.harperCumulativeCellWidth_nonneg
          (fun i => (Problem520.harperScheduledRelativeCellWidth_pos
            start n i).le) k
      have hkupper : Problem520.harperPathPartialSum
          (Problem520.harperScheduledCenteredBlockVectorVarying
            y start n t (fun _i : Fin n => t) eta) k <=
          harperTerminalCappedEventLevel n := by
        simpa only [harperScheduledTerminalCappedUpperBarrier,
          if_pos hk] using hkbar.2
      unfold harperScheduledAutomaticUpperBarrier
      linarith
    · simpa only [harperScheduledTerminalCappedUpperBarrier,
        if_neg hk] using hkbar.2
  refine ⟨hcentral, ?_⟩
  let k : Fin n := ⟨n - 1, by omega⟩
  have hk : k.val + 1 = n := by dsimp [k]; omega
  have hkbar := heta k
  have hterminalPath : Problem520.harperPathPartialSum
      (Problem520.harperScheduledCenteredBlockVectorVarying
        y start n t (fun _i : Fin n => t) eta) k <=
      harperTerminalCappedEventLevel n := by
    simpa only [harperScheduledTerminalCappedUpperBarrier,
      if_pos hk] using hkbar.2
  rw [harperPathPartialSum_eq_terminal_sum _ k hk] at hterminalPath
  change Problem520.harperCenteredLinearPrimeBlockSum y
      (Problem520.harperScheduledPrimeRangeFrom y start n) t t eta <=
    harperTerminalCappedEventLevel n
  rw [← Problem520.sum_harperScheduledCenteredBlockVector_eq_rangeFrom
    y start n t t eta]
  simpa only [Problem520.harperScheduledCenteredBlockVector,
    Problem520.harperScheduledCenteredBlockVectorVarying] using hterminalPath

/-- Reverse local-limit transfer for the terminal-capped ballot.  Apart from
the standard moderate-box complement, it loses only the fixed cellwise factor
`3/4`. -/
theorem
    exists_three_fourths_mul_terminalGaussianBallot_sub_boxTail_le_harperTerminalCappedBallot :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start ->
      ∀ n : Nat, 8 <= n ->
      ∀ y : Nat, Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
          (1 / 2 : Real) *
              (Real.exp (-2) / Real.sqrt (n : Real)) <=
            (Measure.pi (fun i : Fin n =>
              Problem520.harperGaussianBlockLaw y
                (Problem520.harperScheduledPrimeBlock y
                  (start + (i : Nat))) t t)).real
              (gaussianWalkTerminalCappedSurvivalSet n 1
                (harperTerminalCenteredCap n)) ->
          (3 / 4 : Real) *
              ((1 / 2 : Real) *
                  (Real.exp (-2) / Real.sqrt (n : Real)) -
                (Measure.pi (fun i : Fin n =>
                  Problem520.harperGaussianBlockLaw y
                    (Problem520.harperScheduledPrimeBlock y
                      (start + (i : Nat))) t t)).real
                  (Problem520.harperCoordinateBox
                    (Problem520.harperScheduledModerateRadius start n))ᶜ) <=
            (Problem520.harperTiltedCubeLaw y t).real
              (harperTerminalCappedCentralLowerBallotCubeEvent
                y start n t) := by
  obtain ⟨J, hreverse⟩ :=
    exists_three_fourths_mul_gaussian_contractedBarrier_le_harperScheduledCentralBandBarrier
  refine ⟨J, ?_⟩
  intro d start hstart n hn y hy t htLower htUpper hgaussian
  let Q : Measure (Fin n -> Real) := Measure.pi (fun i : Fin n =>
    Problem520.harperGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t)
  let P : Measure (Fin n -> Real) := Measure.pi (fun i : Fin n =>
    Problem520.harperCenteredLinearBlockLaw y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t)
  let A := gaussianWalkTerminalCappedSurvivalSet n 1
    (harperTerminalCenteredCap n)
  let B := Problem520.harperCoordinateBox
    (Problem520.harperScheduledModerateRadius start n)
  let lower := harperScheduledAutomaticLowerBarrier start n
  let upper := harperScheduledTerminalCappedUpperBarrier start n
  let contracted := Problem520.harperPartialSumBarrierSet
      (fun k => lower k + Problem520.harperCumulativeCellWidth
        (Problem520.harperScheduledRelativeCellWidth start n) k)
      (fun k => upper k - Problem520.harperCumulativeCellWidth
        (Problem520.harperScheduledRelativeCellWidth start n) k) ∩ B
  let barrier := Problem520.harperPartialSumBarrierSet lower upper
  have hcover : A <= (A ∩ B) ∪ Bᶜ := by
    intro omega homega
    by_cases hbox : omega ∈ B
    · exact Or.inl ⟨homega, hbox⟩
    · exact Or.inr hbox
  have hsplit : Q.real A <= Q.real (A ∩ B) + Q.real Bᶜ :=
    (measureReal_mono hcover).trans (measureReal_union_le _ _)
  have hinterLower :
      (1 / 2 : Real) *
          (Real.exp (-2) / Real.sqrt (n : Real)) - Q.real Bᶜ <=
        Q.real (A ∩ B) := by
    change (1 / 2 : Real) *
        (Real.exp (-2) / Real.sqrt (n : Real)) <= Q.real A at hgaussian
    linarith
  have hinside : A ∩ B <= contracted := by
    simpa only [A, B, contracted, lower, upper] using
      gaussianTerminalCapped_inter_box_subset_contractedTerminalBarrier
        start n
  have hcontracted : Q.real (A ∩ B) <= Q.real contracted :=
    measureReal_mono hinside
  have hreverseMain := hreverse d start hstart n y hy t
    htLower htUpper lower upper
  have hbarrier : (3 / 4 : Real) * Q.real contracted <=
      P.real barrier := by
    simpa only [Q, P, B, contracted, barrier, lower, upper] using hreverseMain
  have hmap : P.real barrier =
      (Problem520.harperTiltedCubeLaw y t).real
        ((Problem520.harperScheduledCenteredBlockVectorVarying
          y start n t (fun _i : Fin n => t)) ⁻¹' barrier) := by
    rw [Problem520.harperTiltedCubeLaw_real_preimage_centeredBlockVectorVarying_eq_pi
      y start n t (fun _i : Fin n => t) barrier
      (Problem520.measurableSet_harperPartialSumBarrierSet lower upper)]
  have hevent :
      (Problem520.harperTiltedCubeLaw y t).real
          ((Problem520.harperScheduledCenteredBlockVectorVarying
            y start n t (fun _i : Fin n => t)) ⁻¹' barrier) <=
        (Problem520.harperTiltedCubeLaw y t).real
          (harperTerminalCappedCentralLowerBallotCubeEvent
            y start n t) := by
    exact measureReal_mono (by
      simpa only [barrier, lower, upper] using
        harperTerminalBarrier_preimage_subset_cappedBallotEvent
          y start n hn t)
  change (3 / 4 : Real) *
      ((1 / 2 : Real) *
          (Real.exp (-2) / Real.sqrt (n : Real)) - Q.real Bᶜ) <=
    (Problem520.harperTiltedCubeLaw y t).real
      (harperTerminalCappedCentralLowerBallotCubeEvent y start n t)
  calc
    (3 / 4 : Real) *
        ((1 / 2 : Real) *
            (Real.exp (-2) / Real.sqrt (n : Real)) - Q.real Bᶜ) <=
      (3 / 4 : Real) * Q.real (A ∩ B) := by gcongr
    _ <= (3 / 4 : Real) * Q.real contracted := by gcongr
    _ <= P.real barrier := hbarrier
    _ = (Problem520.harperTiltedCubeLaw y t).real
        ((Problem520.harperScheduledCenteredBlockVectorVarying
          y start n t (fun _i : Fin n => t)) ⁻¹' barrier) := hmap
    _ <= (Problem520.harperTiltedCubeLaw y t).real
        (harperTerminalCappedCentralLowerBallotCubeEvent
          y start n t) := hevent

/-- The completed one-height theorem: on every sufficiently long even
scheduled path, the actual tilted Harper cube assigns the terminal-capped
ballot probability of order `1 / sqrt n`, uniformly across a central vertical
band. -/
theorem
    exists_eventually_three_sixteenths_mul_exp_neg_two_div_sqrt_le_harperTiltedCubeLaw_terminalCappedBallot :
    ∃ J m0 : Nat, ∀ d start : Nat, J + d <= start ->
      ∀ m : Nat, m0 <= m ->
      ∀ y : Nat, Problem520.harperBlockEndpoint (start + (m + m)) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
          64 * (1 / 2 : Real) ^ start <=
            (1 / 4 : Real) *
              (Real.exp (-2) /
                Real.sqrt ((m + m : Nat) : Real)) ->
          (3 / 16 : Real) *
              (Real.exp (-2) /
                Real.sqrt ((m + m : Nat) : Real)) <=
            (Problem520.harperTiltedCubeLaw y t).real
              (harperTerminalCappedCentralLowerBallotCubeEvent
                y start (m + m) t) := by
  obtain ⟨Jtransfer, htransfer⟩ :=
    exists_three_fourths_mul_terminalGaussianBallot_sub_boxTail_le_harperTerminalCappedBallot
  obtain ⟨Jvar, hvar⟩ :=
    Problem520.exists_harperScheduledCentralBandVarianceVector_quarter_half
  obtain ⟨m0, hm0⟩ := eventually_atTop.1
    eventually_half_exp_neg_two_div_sqrt_le_gaussianTerminalCapped_probability
  refine ⟨max 8 (max Jtransfer Jvar), max 4 m0, ?_⟩
  intro d start hstart m hm y hy t htLower htUpper hbudget
  have hstart8 : 8 <= start := by omega
  have hstartTransfer : Jtransfer + d <= start := by omega
  have hstartVar : Jvar + d <= start := by omega
  have hm0' : m0 <= m := by omega
  let n : Nat := m + m
  have hn8 : 8 <= n := by dsimp [n]; omega
  let variance : Fin n -> NNReal := fun i =>
    Problem520.harperLinearBlockVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t
  let Q : Measure (Fin n -> Real) := Measure.pi (fun i : Fin n =>
    Problem520.harperGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t)
  let box := Problem520.harperCoordinateBox
    (Problem520.harperScheduledModerateRadius start n)
  let ballotMass := Real.exp (-2) / Real.sqrt (n : Real)
  have hvarianceVector := hvar d start hstartVar n y
    (by simpa only [n] using hy) t htLower htUpper
    (fun _i : Fin n => t) (by intro i; simp)
  have hlower : ∀ i, (1 / 4 : NNReal) <= variance i := by
    intro i
    exact_mod_cast (hvarianceVector i).1.le
  have hupper : ∀ i, variance i <= (1 / 2 : NNReal) := by
    intro i
    exact_mod_cast (hvarianceVector i).2.le
  have hgaussian : (1 / 2 : Real) * ballotMass <=
      Q.real (gaussianWalkTerminalCappedSurvivalSet n 1
        (harperTerminalCenteredCap n)) := by
    have h := hm0 m hm0' variance hlower hupper
    simpa only [n, variance, Q, ballotMass,
      Problem520.harperGaussianBlockLaw] using h
  have hvarianceUpper : ∀ i : Fin n,
      Problem520.harperLinearBlockVariance y
          (Problem520.harperScheduledPrimeBlock y
            (start + (i : Nat))) t t <= (1 / 2 : Real) := by
    intro i
    exact (hvarianceVector i).2.le
  have hbox : Q.real boxᶜ <= 64 * (1 / 2 : Real) ^ start := by
    simpa only [Q, box] using
      harperScheduledGaussianProductMeasure_box_compl_le
        t hstart8 hvarianceUpper
  have hboxBudget : Q.real boxᶜ <= (1 / 4 : Real) * ballotMass :=
    hbox.trans (by simpa only [n, ballotMass] using hbudget)
  have hmain := htransfer d start hstartTransfer n hn8 y
    (by simpa only [n] using hy) t htLower htUpper hgaussian
  change (3 / 16 : Real) * ballotMass <=
    (Problem520.harperTiltedCubeLaw y t).real
      (harperTerminalCappedCentralLowerBallotCubeEvent y start n t)
  have hremaining : (1 / 4 : Real) * ballotMass <=
      (1 / 2 : Real) * ballotMass - Q.real boxᶜ := by
    linarith
  calc
    (3 / 16 : Real) * ballotMass =
        (3 / 4 : Real) * ((1 / 4 : Real) * ballotMass) := by ring
    _ <= (3 / 4 : Real) *
        ((1 / 2 : Real) * ballotMass - Q.real boxᶜ) := by gcongr
    _ <= (Problem520.harperTiltedCubeLaw y t).real
        (harperTerminalCappedCentralLowerBallotCubeEvent
          y start n t) := by
      simpa only [Q, box, ballotMass] using hmain

end
end Problem1144
end Erdos

#print axioms Erdos.Problem1144.gaussianWalkSurvives_iff_harperPathPartialSum_le
#print axioms Erdos.Problem1144.gaussianWalkSurvives_halves_of_terminalDistance_le
#print axioms Erdos.Problem1144.gaussianWalkTerminalNear_probability_le_two_half_ballots
#print axioms Erdos.Problem1144.half_exp_neg_two_div_sqrt_le_gaussianTerminalCapped_probability
#print axioms Erdos.Problem1144.eventually_half_exp_neg_two_div_sqrt_le_gaussianTerminalCapped_probability
#print axioms Erdos.Problem1144.gaussianTerminalCapped_inter_box_subset_contractedTerminalBarrier
#print axioms Erdos.Problem1144.harperTerminalBarrier_preimage_subset_cappedBallotEvent
#print axioms Erdos.Problem1144.exists_eventually_three_sixteenths_mul_exp_neg_two_div_sqrt_le_harperTiltedCubeLaw_terminalCappedBallot
