import Erdos.Problem1144.HarperGaussianLogBallotFence
import Erdos.Problem1144.HarperGaussianTerminalBallot

open Finset MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# Exponentially small affine Gaussian tails

The auxiliary lower fence used by the one-height logarithmic ballot can fail
at time `m` only when the Gaussian prefix sum lies far in its lower tail.  The
untouched suffix ballot costs an affine function of the distance from its
upper barrier.  This file records a Chernoff-style bound for exactly that
weighted tail.  It avoids an exact Mills-ratio calculation and is uniform in
the (possibly varying) prefix variance.
-/

/-- On a lower tail, an affine weight is absorbed by an exponential weight.
The spare `1 / t` pays for the unbounded overshoot. -/
theorem affine_le_exp_of_le_neg
    {a c t z : Real} (ha : 0 <= a) (hc : 0 <= c) (ht : 0 < t)
    (hz : z <= -a) :
    c - z <= (c + a + 1 / t) * Real.exp (-t * (z + a)) := by
  let y : Real := -z - a
  have hy : 0 <= y := by
    dsimp only [y]
    linarith
  have hty : 0 <= t * y := mul_nonneg ht.le hy
  have hone : 1 <= Real.exp (t * y) := Real.one_le_exp hty
  have hlinear : y <= (1 / t) * Real.exp (t * y) := by
    have hbasic : t * y <= Real.exp (t * y) := by
      calc
        t * y <= t * y + 1 := by norm_num
        _ <= Real.exp (t * y) := Real.add_one_le_exp (t * y)
    rw [one_div, mul_comm]
    exact (le_mul_inv_iff₀ ht).mpr (by simpa only [mul_comm] using hbasic)
  have hconst : c + a <= (c + a) * Real.exp (t * y) := by
    nlinarith [add_nonneg hc ha]
  have hsum : c + a + y <=
      (c + a + 1 / t) * Real.exp (t * y) := by
    calc
      c + a + y <=
          (c + a) * Real.exp (t * y) +
            (1 / t) * Real.exp (t * y) := add_le_add hconst hlinear
      _ = (c + a + 1 / t) * Real.exp (t * y) := by ring
  have hleft : c - z = c + a + y := by
    dsimp only [y]
    ring
  have hexp : -t * (z + a) = t * y := by
    dsimp only [y]
    ring
  simpa only [hleft, hexp] using hsum

/-- A centered Gaussian lower tail with the affine terminal-distance weight
needed by the suffix ballot estimate. -/
theorem integral_Iic_gaussianReal_affine_lowerTail_le
    (v : NNReal) {a c t : Real} (ha : 0 <= a) (hc : 0 <= c) (ht : 0 < t) :
    (∫ z in Set.Iic (-a), (c - z) ∂gaussianReal 0 v) <=
      (c + a + 1 / t) * Real.exp (-t * a + (v : Real) * t ^ 2 / 2) := by
  let C : Real := c + a + 1 / t
  have hC : 0 <= C := by
    dsimp only [C]
    positivity
  have hleft : IntegrableOn (fun z : Real => c - z)
      (Set.Iic (-a)) (gaussianReal 0 v) :=
    ((integrable_const c).sub
      (memLp_one_iff_integrable.mp
        (by simpa only [id_eq] using
          (memLp_id_gaussianReal' (μ := (0 : Real)) (v := v) 1
            (by norm_num))))).integrableOn
  have hexpInt : Integrable (fun z : Real => Real.exp (-t * z))
      (gaussianReal 0 v) := by
    simpa only [neg_mul] using
      (integrable_exp_mul_gaussianReal (μ := (0 : Real)) (v := v) (-t))
  have hright : IntegrableOn
      (fun z : Real => C * Real.exp (-t * a) * Real.exp (-t * z))
      (Set.Iic (-a)) (gaussianReal 0 v) :=
    (hexpInt.const_mul (C * Real.exp (-t * a))).integrableOn
  have hpoint : ∀ z ∈ Set.Iic (-a),
      c - z <= C * Real.exp (-t * a) * Real.exp (-t * z) := by
    intro z hz
    have hbase := affine_le_exp_of_le_neg ha hc ht hz
    rw [show Real.exp (-t * (z + a)) =
        Real.exp (-t * a) * Real.exp (-t * z) by
      rw [← Real.exp_add]
      congr 1
      ring] at hbase
    simpa only [C, mul_assoc] using hbase
  calc
    (∫ z in Set.Iic (-a), (c - z) ∂gaussianReal 0 v) <=
        ∫ z in Set.Iic (-a),
          C * Real.exp (-t * a) * Real.exp (-t * z)
          ∂gaussianReal 0 v := by
      exact setIntegral_mono_on hleft hright measurableSet_Iic hpoint
    _ <= ∫ z,
          C * Real.exp (-t * a) * Real.exp (-t * z)
          ∂gaussianReal 0 v := by
      exact setIntegral_le_integral
        (hexpInt.const_mul (C * Real.exp (-t * a)))
        (Filter.Eventually.of_forall fun z => by positivity)
    _ = C * Real.exp (-t * a) *
          Real.exp ((v : Real) * t ^ 2 / 2) := by
      rw [integral_const_mul]
      have hmgf := congrFun
        (mgf_fun_id_gaussianReal (μ := (0 : Real)) (v := v)) (-t)
      rw [mgf] at hmgf
      have hmgf' : (∫ z, Real.exp (-t * z) ∂gaussianReal 0 v) =
          Real.exp ((v : Real) * t ^ 2 / 2) := by
        simpa only [zero_mul, zero_add, neg_sq, neg_mul] using hmgf
      rw [hmgf']
    _ = (c + a + 1 / t) *
          Real.exp (-t * a + (v : Real) * t ^ 2 / 2) := by
      rw [Real.exp_add]
      dsimp only [C]
      ring

/-- Plain Chernoff bound for a centered Gaussian lower tail.  This is the
terminal-time companion to the weighted estimate above, where there is no
untouched suffix ballot to pay for. -/
theorem gaussianReal_Iic_neg_le_exp
    (v : NNReal) {a t : Real} (ht : 0 < t) :
    (gaussianReal 0 v).real (Set.Iic (-a)) <=
      Real.exp (-t * a + (v : Real) * t ^ 2 / 2) := by
  have hint : Integrable (fun z : Real => Real.exp ((-t) * z))
      (gaussianReal 0 v) :=
    integrable_exp_mul_gaussianReal (μ := (0 : Real)) (v := v) (-t)
  have hchernoff := ProbabilityTheory.measure_le_le_exp_mul_mgf
    (μ := gaussianReal 0 v) (X := fun z : Real => z)
    (-a) (t := -t) (by linarith) hint
  rw [mgf_fun_id_gaussianReal] at hchernoff
  simpa only [id_eq] using hchernoff.trans_eq (by
    rw [← Real.exp_add]
    congr 1
    ring)

/-! ## A deep-prefix/surviving-suffix split -/

private theorem map_split_prefix_general
    {m q : Nat} (k : Fin q) :
    (Finset.univ.map (Fin.castAddEmb q)) ∪
        ((Finset.Iic k).map (Fin.natAddEmb m)) =
      Finset.Iic (Fin.natAdd m k) := by
  ext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    have hleft : Fin.castAdd q j ∈
        Finset.univ.map (Fin.castAddEmb q) :=
      Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩
    have htarget : Fin.castAdd q j ∈
        Finset.Iic (Fin.natAdd m k) := by
      simp only [Finset.mem_Iic]
      exact Fin.le_iff_val_le_val.mpr (by simp; omega)
    simp only [Finset.mem_union]
    exact iff_of_true (Or.inl hleft) htarget
  · intro j
    have hnotleft : Fin.natAdd m j ∉
        Finset.univ.map (Fin.castAddEmb q) := by
      intro h
      obtain ⟨i, _hi, heq⟩ := Finset.mem_map.mp h
      have hval := congrArg Fin.val heq
      simp only [Fin.castAddEmb_apply, Fin.val_castAdd,
        Fin.val_natAdd] at hval
      omega
    have hsecond : Fin.natAdd m j ∈
          (Finset.Iic k).map (Fin.natAddEmb m) ↔ j <= k := by
      constructor
      · intro h
        obtain ⟨i, hi, heq⟩ := Finset.mem_map.mp h
        have hij : i = j := by
          apply Fin.ext
          have hval := congrArg Fin.val heq
          simpa only [Fin.natAddEmb_apply, Fin.val_natAdd] using
            Nat.add_left_cancel hval
        simpa only [Finset.mem_Iic, hij] using hi
      · intro hj
        exact Finset.mem_map.mpr
          ⟨j, Finset.mem_Iic.mpr hj, rfl⟩
    have htarget : Fin.natAdd m j ∈
          Finset.Iic (Fin.natAdd m k) ↔ j <= k := by
      simp only [Finset.mem_Iic]
      exact Fin.le_iff_val_le_val.trans (by simp)
    simp only [Finset.mem_union, hnotleft, false_or, hsecond, htarget]

private theorem disjoint_split_prefix_general
    {m q : Nat} (k : Fin q) :
    Disjoint (Finset.univ.map (Fin.castAddEmb q))
      ((Finset.Iic k).map (Fin.natAddEmb m)) := by
  rw [Finset.disjoint_left]
  intro z hz1 hz2
  obtain ⟨i, _hi, hi⟩ := Finset.mem_map.mp hz1
  obtain ⟨j, _hj, hj⟩ := Finset.mem_map.mp hz2
  have hval := congrArg Fin.val (hi.trans hj.symm)
  simp only [Fin.castAddEmb_apply, Fin.natAddEmb_apply,
    Fin.val_castAdd, Fin.val_natAdd] at hval
  omega

/-- The complete first-block sum plus a suffix partial sum is the
corresponding partial sum of the unsplit vector. -/
theorem sum_harperFinSplit_fst_add_partialSum_snd
    {m q : Nat} (omega : Fin (m + q) -> Real) (k : Fin q) :
    (∑ i, (harperFinSplit omega).1 i) +
        Problem520.harperPathPartialSum (harperFinSplit omega).2 k =
      Problem520.harperPathPartialSum omega (Fin.natAdd m k) := by
  unfold Problem520.harperPathPartialSum harperFinSplit
  calc
    (∑ i : Fin m, omega (Fin.castAdd q i)) +
        ∑ j ∈ Finset.Iic k, omega (Fin.natAdd m j) =
      (∑ z ∈ Finset.univ.map (Fin.castAddEmb q), omega z) +
        ∑ z ∈ (Finset.Iic k).map (Fin.natAddEmb m), omega z := by
          rw [Finset.sum_map, Finset.sum_map]
          simp only [Fin.castAddEmb_apply, Fin.natAddEmb_apply]
    _ = ∑ z ∈
        (Finset.univ.map (Fin.castAddEmb q)) ∪
          ((Finset.Iic k).map (Fin.natAddEmb m)), omega z := by
      rw [Finset.sum_union (disjoint_split_prefix_general k)]
    _ = ∑ z ∈ Finset.Iic (Fin.natAdd m k), omega z := by
      rw [map_split_prefix_general k]

/-- After splitting off any prefix, survival of the full flat walk forces
the untouched suffix to survive from the remaining terminal distance. -/
theorem gaussianWalkSurvives_snd_of_harperFinSplit
    {m q : Nat} (x : Real) (omega : Fin (m + q) -> Real)
    (hsurv : Problem520.gaussianWalkSurvives (m + q) x omega) :
    Problem520.gaussianWalkSurvives q
      (x - ∑ i, (harperFinSplit omega).1 i)
      (harperFinSplit omega).2 := by
  apply (gaussianWalkSurvives_iff_harperPathPartialSum_le q
    (x - ∑ i, (harperFinSplit omega).1 i)
    (harperFinSplit omega).2).mpr
  intro k
  have hfull :=
    (gaussianWalkSurvives_iff_harperPathPartialSum_le
      (m + q) x omega).mp hsurv (Fin.natAdd m k)
  rw [← sum_harperFinSplit_fst_add_partialSum_snd omega k] at hfull
  linarith

/-- Flat survival together with a lower-tail condition on the first block. -/
def gaussianWalkDeepAtSplitSet
    (m q : Nat) (x a : Real) : Set (Fin (m + q) -> Real) :=
  Problem520.gaussianWalkSurvivalSet (m + q) x ∩
    {omega | (∑ i, (harperFinSplit omega).1 i) <= -a}

theorem measurableSet_gaussianWalkDeepAtSplitSet
    (m q : Nat) {x a : Real} (hx : 0 <= x) :
    MeasurableSet (gaussianWalkDeepAtSplitSet m q x a) := by
  apply (Problem520.measurableSet_gaussianWalkSurvivalSet (m + q) hx).inter
  exact measurableSet_le
    (Finset.measurable_sum _ fun i _hi =>
      measurable_pi_apply (Fin.castAdd q i)) measurable_const

/-- The product-space event obtained after dropping all constraints on the
first block except its terminal lower tail. -/
def gaussianWalkDeepSuffixSet
    (m q : Nat) (x a : Real) :
    Set ((Fin m -> Real) × (Fin q -> Real)) :=
  {p | (∑ i, p.1 i) <= -a ∧
    Problem520.gaussianWalkSurvives q
      (x - ∑ i, p.1 i) p.2}

theorem measurableSet_gaussianWalkDeepSuffixSet
    (m q : Nat) (x a : Real) :
    MeasurableSet (gaussianWalkDeepSuffixSet m q x a) := by
  rw [show gaussianWalkDeepSuffixSet m q x a =
      {p : (Fin m -> Real) × (Fin q -> Real) |
        (∑ i, p.1 i) <= -a} ∩
      ⋂ k : Fin q,
        {p : (Fin m -> Real) × (Fin q -> Real) |
          Problem520.harperPathPartialSum p.2 k <=
            x - ∑ i, p.1 i} by
    ext p
    simp only [gaussianWalkDeepSuffixSet, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_iInter]
    rw [gaussianWalkSurvives_iff_harperPathPartialSum_le]]
  apply MeasurableSet.inter
  · exact measurableSet_le
      (Finset.measurable_sum _ fun i _hi =>
        (measurable_pi_apply i).comp measurable_fst)
      measurable_const
  · apply MeasurableSet.iInter
    intro k
    exact measurableSet_le
      ((Finset.measurable_sum _ fun i _hi =>
        (measurable_pi_apply i).comp measurable_snd))
      (measurable_const.sub
        (Finset.measurable_sum _ fun i _hi =>
          (measurable_pi_apply i).comp measurable_fst))

/-- The deep-prefix slice of the original walk is contained in the split
product event. -/
theorem gaussianWalkDeepAtSplitSet_subset_preimage
    (m q : Nat) (x a : Real) :
    gaussianWalkDeepAtSplitSet m q x a <=
      harperFinSplit ⁻¹'
        gaussianWalkDeepSuffixSet m q x a := by
  intro omega homega
  refine ⟨homega.2, ?_⟩
  exact gaussianWalkSurvives_snd_of_harperFinSplit x omega homega.1

/-- Splitting the independent Gaussian coordinates converts the deep-prefix
slice to a product-space upper bound. -/
theorem gaussianWalkDeepAtSplit_probability_le_product
    (m q : Nat) (variance : Fin (m + q) -> NNReal)
    {x a : Real} :
    (Measure.pi (fun i : Fin (m + q) =>
      gaussianReal 0 (variance i))).real
        (gaussianWalkDeepAtSplitSet m q x a) <=
      ((Measure.pi (fun i : Fin m =>
          gaussianReal 0 (variance (Fin.castAdd q i)))).prod
        (Measure.pi (fun j : Fin q =>
          gaussianReal 0 (variance (Fin.natAdd m j))))).real
        (gaussianWalkDeepSuffixSet m q x a) := by
  let P : Measure (Fin (m + q) -> Real) :=
    Measure.pi (fun i : Fin (m + q) => gaussianReal 0 (variance i))
  let Psplit : Measure ((Fin m -> Real) × (Fin q -> Real)) :=
    (Measure.pi (fun i : Fin m =>
      gaussianReal 0 (variance (Fin.castAdd q i)))).prod
    (Measure.pi (fun j : Fin q =>
      gaussianReal 0 (variance (Fin.natAdd m j))))
  have hsplit := measurePreserving_harperFinSplit m q variance
  have hH := measurableSet_gaussianWalkDeepSuffixSet m q x a
  calc
    P.real (gaussianWalkDeepAtSplitSet m q x a) <=
        P.real (harperFinSplit ⁻¹'
          gaussianWalkDeepSuffixSet m q x a) :=
      measureReal_mono (gaussianWalkDeepAtSplitSet_subset_preimage m q x a)
    _ = Psplit.real (gaussianWalkDeepSuffixSet m q x a) := by
      have hmap := map_measureReal_apply (μ := P) hsplit.measurable hH
      rw [hsplit.map_eq] at hmap
      exact hmap.symm

/-- The sum of a finite product of centered one-dimensional Gaussians is
centered Gaussian with variance equal to the sum of the coordinate
variances.  This is the function-indexed wrapper around the list theorem. -/
theorem map_pi_gaussianReal_sum_eq
    (n : Nat) (variance : Fin n -> NNReal) :
    (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).map
        (fun omega => ∑ i, omega i) =
      gaussianReal 0 (List.ofFn variance).sum := by
  let vs : List NNReal := List.ofFn variance
  have hvlen : vs.length = n := by simp only [vs, List.length_ofFn]
  let e : Fin vs.length ≃ Fin n := finCongr hvlen
  let E : (Fin vs.length -> Real) ≃ᵐ (Fin n -> Real) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Real) e
  let Q : Measure (Fin vs.length -> Real) :=
    Problem520.gaussianVarianceWalkMeasure vs
  let P : Measure (Fin n -> Real) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  have hcoord (i : Fin vs.length) : vs.get i = variance (e i) := by
    dsimp only [vs, e]
    rw [List.get_ofFn]
    congr 1
  have hsource : Q = Measure.pi (fun i : Fin vs.length =>
      gaussianReal 0 (variance (e i))) := by
    dsimp only [Q, Problem520.gaussianVarianceWalkMeasure]
    congr 1
    funext i
    rw [hcoord]
  have hmp := measurePreserving_piCongrLeft
    (μ := fun i : Fin n => gaussianReal 0 (variance i)) e
  have hmpQ : Q.map E = P := by
    rw [hsource]
    exact hmp.map_eq
  have hE (omega : Fin vs.length -> Real) :
      E omega = fun j => omega (e.symm j) := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Real) e)
      omega (e i) = omega i
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin n => Real) e omega i
  have hsumE (omega : Fin vs.length -> Real) :
      (∑ j, E omega j) = ∑ i, omega i := by
    rw [hE]
    exact e.symm.sum_comp omega
  have hlist := Problem520.map_gaussianVarianceWalk_sum_eq vs
  calc
    P.map (fun omega => ∑ i, omega i) =
        (Q.map E).map (fun omega => ∑ i, omega i) := by rw [hmpQ]
    _ = Q.map ((fun omega => ∑ i, omega i) ∘ E) := by
      rw [Measure.map_map (by fun_prop) E.measurable]
    _ = Q.map (fun omega => ∑ i, omega i) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun omega => hsumE omega
    _ = gaussianReal 0 (List.ofFn variance).sum := by
      simpa only [Q, vs] using hlist

/-- The product-space deep-prefix event is bounded by a one-dimensional
weighted Gaussian tail.  The factor `64 / sqrt q` is the untouched suffix
ballot cost. -/
theorem gaussianWalkDeepSuffix_probability_le_affineTail
    (m q : Nat) (hq : 0 < q) (variance : Fin (m + q) -> NNReal)
    {x a : Real} (hx : 0 <= x) (ha : 0 <= a)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    ((Measure.pi (fun i : Fin m =>
        gaussianReal 0 (variance (Fin.castAdd q i)))).prod
      (Measure.pi (fun j : Fin q =>
        gaussianReal 0 (variance (Fin.natAdd m j))))).real
        (gaussianWalkDeepSuffixSet m q x a) <=
      (64 / Real.sqrt (q : Real)) *
        (∫ z in Set.Iic (-a), (x + 2 - z)
          ∂gaussianReal 0
            (List.ofFn (fun i : Fin m =>
              variance (Fin.castAdd q i))).sum) := by
  let P1 : Measure (Fin m -> Real) :=
    Measure.pi (fun i : Fin m =>
      gaussianReal 0 (variance (Fin.castAdd q i)))
  let P2 : Measure (Fin q -> Real) :=
    Measure.pi (fun j : Fin q =>
      gaussianReal 0 (variance (Fin.natAdd m j)))
  let H : Set ((Fin m -> Real) × (Fin q -> Real)) :=
    gaussianWalkDeepSuffixSet m q x a
  let S : (Fin m -> Real) -> Real := fun u => ∑ i, u i
  let F : ((Fin m -> Real) × (Fin q -> Real)) -> Real :=
    fun p => H.indicator (fun _ => (1 : Real)) p
  let c : Real := 64 / Real.sqrt (q : Real)
  have hH : MeasurableSet H :=
    measurableSet_gaussianWalkDeepSuffixSet m q x a
  have hFint : Integrable F (P1.prod P2) := by
    dsimp only [F]
    exact (integrable_const (1 : Real)).indicator hH
  have hSmeas : Measurable S := by
    dsimp only [S]
    exact Finset.measurable_sum _ fun i _hi => measurable_pi_apply i
  have hSid (i : Fin m) :
      Integrable (fun u : Fin m -> Real => u i) P1 := by
    dsimp only [P1]
    exact integrable_eval
      (memLp_one_iff_integrable.mp
        (by simpa only [id_eq] using
          (memLp_id_gaussianReal' (μ := (0 : Real))
            (v := variance (Fin.castAdd q i)) 1 (by norm_num))))
  have hSint : Integrable S P1 := by
    dsimp only [S]
    exact integrable_finset_sum Finset.univ (fun i _hi => hSid i)
  have hweightedInt : Integrable
      (fun u => (Set.Iic (-a)).indicator
        (fun z : Real => x + 2 - z) (S u)) P1 := by
    have hpre : MeasurableSet (S ⁻¹' Set.Iic (-a)) :=
      measurableSet_Iic.preimage hSmeas
    have hbase : Integrable
        ((S ⁻¹' Set.Iic (-a)).indicator
          (fun u => x + 2 - S u)) P1 :=
      ((integrable_const (x + 2)).sub hSint).indicator hpre
    simpa only [Set.indicator, Set.mem_preimage] using hbase
  have hc : 0 <= c := by
    dsimp only [c]
    positivity
  have hinner (u : Fin m -> Real) :
      (∫ v, F (u, v) ∂P2) =
        if hu : S u <= -a then
          P2.real (Problem520.gaussianWalkSurvivalSet q (x - S u))
        else 0 := by
    split_ifs with hu
    · have hd : 0 <= x - S u := by linarith
      have hset := Problem520.measurableSet_gaussianWalkSurvivalSet q hd
      have hfun : (fun v => F (u, v)) =
          (Problem520.gaussianWalkSurvivalSet q (x - S u)).indicator
            (fun _ => (1 : Real)) := by
        funext v
        dsimp only [S] at hu ⊢
        by_cases hv : Problem520.gaussianWalkSurvives q
            (x - ∑ i, u i) v
        · simp [F, H, gaussianWalkDeepSuffixSet,
            Problem520.gaussianWalkSurvivalSet, Set.indicator, hu, hv]
        · simp [F, H, gaussianWalkDeepSuffixSet,
            Problem520.gaussianWalkSurvivalSet, Set.indicator, hu, hv]
      rw [hfun]
      exact integral_indicator_one (μ := P2) hset
    · have hfun : (fun v => F (u, v)) = 0 := by
        funext v
        dsimp only [S] at hu ⊢
        by_cases hv : Problem520.gaussianWalkSurvives q
            (x - ∑ i, u i) v
        · simp [F, H, gaussianWalkDeepSuffixSet,
            Set.indicator, hu, hv]
        · simp [F, H, gaussianWalkDeepSuffixSet,
            Set.indicator, hu, hv]
      rw [hfun]
      simp
  have hinnerBound (u : Fin m -> Real) :
      (∫ v, F (u, v) ∂P2) <=
        c * (Set.Iic (-a)).indicator (fun z => x + 2 - z) (S u) := by
    by_cases hu : S u <= -a
    · have hu' : S u ∈ Set.Iic (-a) := hu
      rw [hinner, dif_pos hu, Set.indicator_of_mem hu']
      have hd : 0 <= x - S u := by linarith
      have hballot :=
        Problem520.gaussianVarianceWalk_quarter_half_probability_le_fin
          q hq (fun j : Fin q => variance (Fin.natAdd m j)) hd
          (fun j => hlower _) (fun j => hupper _)
      dsimp only [P2, c] at hballot ⊢
      convert hballot using 1 <;> ring
    · have hu' : S u ∉ Set.Iic (-a) := hu
      rw [hinner, dif_neg hu, Set.indicator_of_notMem hu']
      positivity
  have hinnerInt : Integrable (fun u => ∫ v, F (u, v) ∂P2) P1 :=
    hFint.integral_prod_left
  have hrightInt : Integrable
      (fun u => c * (Set.Iic (-a)).indicator
        (fun z => x + 2 - z) (S u)) P1 :=
    hweightedInt.const_mul c
  have hmapS : P1.map S =
      gaussianReal 0
        (List.ofFn (fun i : Fin m =>
          variance (Fin.castAdd q i))).sum := by
    simpa only [P1, S] using
      map_pi_gaussianReal_sum_eq m
        (fun i : Fin m => variance (Fin.castAdd q i))
  have htailMap :
      (∫ u, (Set.Iic (-a)).indicator
          (fun z => x + 2 - z) (S u) ∂P1) =
        ∫ z in Set.Iic (-a), (x + 2 - z)
          ∂gaussianReal 0
            (List.ofFn (fun i : Fin m =>
              variance (Fin.castAdd q i))).sum := by
    let g : Real -> Real :=
      fun z => (Set.Iic (-a)).indicator (fun z => x + 2 - z) z
    have hgmeas : Measurable g := by
      dsimp only [g]
      exact (measurable_const.sub measurable_id).indicator measurableSet_Iic
    have hmap := integral_map hSmeas.aemeasurable
      hgmeas.aestronglyMeasurable (μ := P1)
    rw [hmapS] at hmap
    rw [← integral_indicator measurableSet_Iic]
    simpa only [g] using hmap.symm
  calc
    (P1.prod P2).real H = ∫ p, F p ∂(P1.prod P2) := by
      simpa only [F] using (integral_indicator_one (μ := P1.prod P2) hH).symm
    _ = ∫ u, ∫ v, F (u, v) ∂P2 ∂P1 := integral_prod F hFint
    _ <= ∫ u, c * (Set.Iic (-a)).indicator
          (fun z => x + 2 - z) (S u) ∂P1 := by
      exact integral_mono hinnerInt hrightInt hinnerBound
    _ = c * ∫ u, (Set.Iic (-a)).indicator
          (fun z => x + 2 - z) (S u) ∂P1 := by
      rw [integral_const_mul]
    _ = c * (∫ z in Set.Iic (-a), (x + 2 - z)
          ∂gaussianReal 0
            (List.ofFn (fun i : Fin m =>
              variance (Fin.castAdd q i))).sum) := by rw [htailMap]

/-- Fully explicit deep-prefix estimate.  A Chernoff parameter `t` may be
chosen separately at every split time. -/
theorem gaussianWalkDeepAtSplit_probability_le_exp
    (m q : Nat) (hq : 0 < q) (variance : Fin (m + q) -> NNReal)
    {x a t : Real} (hx : 0 <= x) (ha : 0 <= a) (ht : 0 < t)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    (Measure.pi (fun i : Fin (m + q) =>
      gaussianReal 0 (variance i))).real
        (gaussianWalkDeepAtSplitSet m q x a) <=
      (64 / Real.sqrt (q : Real)) *
        (x + 2 + a + 1 / t) *
          Real.exp (-t * a +
            ((List.ofFn (fun i : Fin m =>
              variance (Fin.castAdd q i))).sum : Real) * t ^ 2 / 2) := by
  have hsplit := gaussianWalkDeepAtSplit_probability_le_product
    m q variance (x := x) (a := a)
  have hsuffix := gaussianWalkDeepSuffix_probability_le_affineTail
    m q hq variance hx ha hlower hupper
  have htail := integral_Iic_gaussianReal_affine_lowerTail_le
    (List.ofFn (fun i : Fin m => variance (Fin.castAdd q i))).sum
    (a := a) (c := x + 2) (t := t) ha (by linarith) ht
  have hc : 0 <= 64 / Real.sqrt (q : Real) := by positivity
  calc
    (Measure.pi (fun i : Fin (m + q) =>
      gaussianReal 0 (variance i))).real
        (gaussianWalkDeepAtSplitSet m q x a) <=
      ((Measure.pi (fun i : Fin m =>
          gaussianReal 0 (variance (Fin.castAdd q i)))).prod
        (Measure.pi (fun j : Fin q =>
          gaussianReal 0 (variance (Fin.natAdd m j))))).real
        (gaussianWalkDeepSuffixSet m q x a) := hsplit
    _ <= (64 / Real.sqrt (q : Real)) *
        (∫ z in Set.Iic (-a), (x + 2 - z)
          ∂gaussianReal 0
            (List.ofFn (fun i : Fin m =>
              variance (Fin.castAdd q i))).sum) := hsuffix
    _ <= (64 / Real.sqrt (q : Real)) *
        ((x + 2 + a + 1 / t) *
          Real.exp (-t * a +
            ((List.ofFn (fun i : Fin m =>
              variance (Fin.castAdd q i))).sum : Real) * t ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_left htail hc
    _ = (64 / Real.sqrt (q : Real)) *
        (x + 2 + a + 1 / t) *
          Real.exp (-t * a +
            ((List.ofFn (fun i : Fin m =>
              variance (Fin.castAdd q i))).sum : Real) * t ^ 2 / 2) := by
      ring

#print axioms Erdos.Problem1144.affine_le_exp_of_le_neg
#print axioms Erdos.Problem1144.integral_Iic_gaussianReal_affine_lowerTail_le
#print axioms Erdos.Problem1144.gaussianWalkSurvives_snd_of_harperFinSplit
#print axioms Erdos.Problem1144.gaussianWalkDeepAtSplit_probability_le_product
#print axioms Erdos.Problem1144.map_pi_gaussianReal_sum_eq
#print axioms Erdos.Problem1144.gaussianWalkDeepSuffix_probability_le_affineTail
#print axioms Erdos.Problem1144.gaussianWalkDeepAtSplit_probability_le_exp

end

end Problem1144
end Erdos
