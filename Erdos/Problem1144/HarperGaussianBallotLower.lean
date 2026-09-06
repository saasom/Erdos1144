import Erdos.Problem520.HarperGaussianVaryingWalk
import Erdos.Problem520.HarperCentralBandBarrier
import Erdos.Problem520.HarperTiltedModerateTail
import Erdos.Problem520.HarperBlockAvailability
import Erdos.Problem1144.HarperBallotLowerComparison
import Erdos.Problem1144.HarperRestrictedGraphEnergy

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# A lower Gaussian ballot estimate

The short route is Levy's maximal inequality.  For independent centered
symmetric increments it bounds the chance of ever crossing `x` by twice the
terminal upper tail.  For a Gaussian terminal value this leaves the central
interval mass, which is of order `1 / sqrt n`.
-/

/-- Every nondegenerate centered Gaussian puts exactly half of its mass on
the positive half-line. -/
theorem gaussianReal_zero_real_Ioi_zero_eq_half
    {v : NNReal} (hv : v ≠ 0) :
    (gaussianReal 0 v).real (Set.Ioi 0) = (1 / 2 : Real) := by
  let mu : Measure Real := gaussianReal 0 v
  have hmap : mu.map (fun x : Real => -x) = mu := by
    simpa only [mu, neg_zero] using (gaussianReal_map_neg (μ := (0 : Real)) (v := v))
  have hsymm : mu.real (Set.Ioi 0) = mu.real (Set.Iio 0) := by
    apply congrArg ENNReal.toReal
    calc
      mu (Set.Ioi 0) = (mu.map (fun x : Real => -x)) (Set.Ioi 0) := by rw [hmap]
      _ = mu ((fun x : Real => -x) ⁻¹' Set.Ioi 0) := by
        rw [Measure.map_apply (by fun_prop) measurableSet_Ioi]
      _ = mu (Set.Iio 0) := by
        congr 1
        ext x
        simp
  have hsingleton : mu.real ({0} : Set Real) = 0 := by
    rw [Measure.real, (noAtoms_gaussianReal hv).measure_singleton, ENNReal.toReal_zero]
  have hIic : mu.real (Set.Iic 0) = mu.real (Set.Iio 0) := by
    rw [show Set.Iic (0 : Real) = Set.Iio 0 ∪ {0} by
      ext x
      simp [le_iff_lt_or_eq]]
    rw [measureReal_union]
    · simp only [hsingleton, add_zero]
    · exact Set.disjoint_singleton_right.mpr (by simp)
    · exact measurableSet_singleton 0
  have hcompl := measureReal_add_measureReal_compl
    (μ := mu) (s := Set.Ioi (0 : Real)) measurableSet_Ioi
  have huniv : mu.real Set.univ = 1 := by simp [mu]
  have hsum : mu.real (Set.Ioi 0) + mu.real (Set.Iio 0) = 1 := by
    rw [← hIic]
    simpa only [compl_Ioi, huniv] using hcompl
  rw [← hsymm] at hsum
  linarith

/-- Upper-tail probability of the unrestricted varying-variance Gaussian
walk. -/
noncomputable def gaussianVarianceWalkUpperTail
    (vs : List NNReal) (x : Real) : Real :=
  (gaussianReal 0 vs.sum).real (Set.Ioi x)

theorem gaussianVarianceWalkUpperTail_nonneg_le_one
    (vs : List NNReal) (x : Real) :
    0 <= gaussianVarianceWalkUpperTail vs x ∧
      gaussianVarianceWalkUpperTail vs x <= 1 := by
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

theorem measurable_gaussianVarianceWalkUpperTail (vs : List NNReal) :
    Measurable (gaussianVarianceWalkUpperTail vs) := by
  let mu : Measure Real := gaussianReal 0 vs.sum
  have hfun : gaussianVarianceWalkUpperTail vs =
      fun x => 1 - cdf mu x := by
    funext x
    rw [show gaussianVarianceWalkUpperTail vs x = mu.real (Set.Ioi x) by rfl,
      ← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ,
      cdf_eq_real]
  rw [hfun]
  exact measurable_const.sub (monotone_cdf mu).measurable

theorem integrable_gaussianVarianceWalkUpperTail_comp_sub
    (v : NNReal) (vs : List NNReal) (x : Real) :
    Integrable (fun z => gaussianVarianceWalkUpperTail vs (x - z))
      (gaussianReal 0 v) := by
  apply (integrable_const (μ := gaussianReal 0 v) (1 : Real)).mono'
  · exact (measurable_gaussianVarianceWalkUpperTail vs).comp
      (measurable_const.sub measurable_id) |>.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        (gaussianVarianceWalkUpperTail_nonneg_le_one vs (x - z)).1]
      exact (gaussianVarianceWalkUpperTail_nonneg_le_one vs (x - z)).2

theorem half_le_gaussianVarianceWalkUpperTail_of_nonpos
    (vs : List NNReal) (hsum : vs.sum ≠ 0) {x : Real} (hx : x <= 0) :
    (1 / 2 : Real) <= gaussianVarianceWalkUpperTail vs x := by
  calc
    (1 / 2 : Real) = (gaussianReal 0 vs.sum).real (Set.Ioi 0) :=
      (gaussianReal_zero_real_Ioi_zero_eq_half hsum).symm
    _ <= (gaussianReal 0 vs.sum).real (Set.Ioi x) := by
      exact measureReal_mono (by intro z hz; exact lt_of_le_of_lt hx hz)
    _ = gaussianVarianceWalkUpperTail vs x := rfl

theorem gaussianVarianceWalkUpperTail_le_half_of_nonneg
    (vs : List NNReal) (hsum : vs.sum ≠ 0) {x : Real} (hx : 0 <= x) :
    gaussianVarianceWalkUpperTail vs x <= (1 / 2 : Real) := by
  calc
    gaussianVarianceWalkUpperTail vs x =
        (gaussianReal 0 vs.sum).real (Set.Ioi x) := rfl
    _ <= (gaussianReal 0 vs.sum).real (Set.Ioi 0) := by
      exact measureReal_mono (by intro z hz; exact hx.trans_lt hz)
    _ = (1 / 2 : Real) := gaussianReal_zero_real_Ioi_zero_eq_half hsum

/-- Convolution recursion for the terminal upper tail. -/
theorem gaussianVarianceWalkUpperTail_cons
    (v : NNReal) (vs : List NNReal) (x : Real) :
    gaussianVarianceWalkUpperTail (v :: vs) x =
      ∫ z, gaussianVarianceWalkUpperTail vs (x - z) ∂gaussianReal 0 v := by
  let mu : Measure Real := gaussianReal 0 v
  let nu : Measure Real := gaussianReal 0 vs.sum
  let f : Real -> Real := (Set.Ioi x).indicator (fun _ => 1)
  have hf : Integrable f (mu ∗ nu) := by
    exact (integrable_indicator_iff measurableSet_Ioi).2 integrableOn_const
  have hconv : mu ∗ nu = gaussianReal 0 (v + vs.sum) := by
    simpa only [mu, nu, zero_add] using
      (gaussianReal_conv_gaussianReal
        (m₁ := (0 : Real)) (m₂ := (0 : Real)) (v₁ := v) (v₂ := vs.sum))
  calc
    gaussianVarianceWalkUpperTail (v :: vs) x =
        (mu ∗ nu).real (Set.Ioi x) := by
      simp only [gaussianVarianceWalkUpperTail, List.sum_cons, hconv]
    _ = ∫ w, f w ∂(mu ∗ nu) := by
      simpa only [f] using
        (integral_indicator_one (μ := mu ∗ nu) measurableSet_Ioi).symm
    _ = ∫ z, ∫ y, f (z + y) ∂nu ∂mu :=
      MeasureTheory.integral_conv hf
    _ = ∫ z, gaussianVarianceWalkUpperTail vs (x - z) ∂mu := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (∫ y, f (z + y) ∂nu) = nu.real (Set.Ioi (x - z))
        rw [← integral_indicator_one (μ := nu) measurableSet_Ioi]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by
          by_cases hzy : x < z + y
          · have hy : x - z < y := by linarith
            simp [f, Set.indicator, hzy, hy]
          · have hy : ¬ x - z < y := by linarith
            simp [f, Set.indicator, hzy, hy]
    _ = ∫ z, gaussianVarianceWalkUpperTail vs (x - z)
        ∂gaussianReal 0 v := rfl

private theorem list_sum_ne_zero_of_ne_nil_of_mem_ne_zero
    {vs : List NNReal} (hne : vs ≠ [])
    (hpos : ∀ v ∈ vs, v ≠ 0) : vs.sum ≠ 0 := by
  cases vs with
  | nil => exact (hne rfl).elim
  | cons v vs =>
      have hv : 0 < v := pos_iff_ne_zero.mpr (hpos v (by simp))
      exact ne_of_gt (lt_of_lt_of_le hv (by simp))

/-- On the first increment's crossing half-line, the remaining centered
Gaussian tail has conditional probability at least one half.  This is the
one-line symmetry input in Levy's maximal inequality. -/
theorem half_mul_gaussian_Ioi_le_integral_upperTail
    (v : NNReal) (vs : List NNReal)
    (hpos : ∀ w ∈ vs, w ≠ 0) (x : Real) :
    (1 / 2 : Real) * (gaussianReal 0 v).real (Set.Ioi x) <=
      ∫ z in Set.Ioi x,
        gaussianVarianceWalkUpperTail vs (x - z) ∂gaussianReal 0 v := by
  have hint := integrable_gaussianVarianceWalkUpperTail_comp_sub v vs x
  calc
    (1 / 2 : Real) * (gaussianReal 0 v).real (Set.Ioi x) =
        ∫ _z in Set.Ioi x, (1 / 2 : Real) ∂gaussianReal 0 v := by
      rw [setIntegral_const]
      simp only [smul_eq_mul]
      ring
    _ <= ∫ z in Set.Ioi x,
        gaussianVarianceWalkUpperTail vs (x - z) ∂gaussianReal 0 v := by
      apply setIntegral_mono_on integrableOn_const hint.integrableOn
        measurableSet_Ioi
      intro z hz
      have hz' : x < z := hz
      have hxz : x - z < 0 := by linarith
      by_cases hnil : vs = []
      · subst vs
        rw [gaussianVarianceWalkUpperTail, List.sum_nil, gaussianReal_zero_var]
        rw [Measure.real, Measure.dirac_apply' 0 measurableSet_Ioi]
        simp [Set.indicator, hxz]
        norm_num
      · exact half_le_gaussianVarianceWalkUpperTail_of_nonpos vs
          (list_sum_ne_zero_of_ne_nil_of_mem_ne_zero hnil hpos) hxz.le

/-- Levy's maximal inequality, expressed in the direction needed here: the
finite Gaussian walk's survival probability is at least one minus twice its
terminal upper tail.  The proof is an induction on the increments; symmetry
of the untouched tail supplies the factor `2`. -/
theorem one_sub_two_mul_upperTail_le_gaussianVarianceWalkSurvivalProbability
    (vs : List NNReal) (hpos : ∀ v ∈ vs, v ≠ 0)
    {x : Real} (hx : 0 <= x) :
    1 - 2 * gaussianVarianceWalkUpperTail vs x <=
      Problem520.gaussianVarianceWalkSurvivalProbability vs x := by
  induction vs generalizing x with
  | nil =>
      simp [gaussianVarianceWalkUpperTail,
        Problem520.gaussianVarianceWalkSurvivalProbability,
        Problem520.gaussianVarianceKilledExpectation]
  | cons v vs ih =>
      have hv : v ≠ 0 := hpos v (by simp)
      have hvTail : ∀ w ∈ vs, w ≠ 0 := by
        intro w hw
        exact hpos w (by simp [hw])
      let mu : Measure Real := gaussianReal 0 v
      let T : Real -> Real := fun z =>
        gaussianVarianceWalkUpperTail vs (x - z)
      let P : Real -> Real := fun z =>
        Problem520.gaussianVarianceWalkSurvivalProbability vs (x - z)
      have hTint : Integrable T mu := by
        simpa only [T, mu] using
          integrable_gaussianVarianceWalkUpperTail_comp_sub v vs x
      have hPint : IntegrableOn P (Set.Iic x) mu := by
        apply (integrableOn_const (C := (1 : Real))).mono'
        · exact (Problem520.measurable_gaussianVarianceWalkSurvivalProbability vs).comp
            (measurable_const.sub measurable_id) |>.aestronglyMeasurable
        · exact (ae_restrict_mem measurableSet_Iic).mono fun z _hz => by
            rw [Real.norm_eq_abs, abs_of_nonneg
              (Problem520.gaussianVarianceWalkSurvivalProbability_nonneg_le_one
                vs (x - z)).1]
            exact
              (Problem520.gaussianVarianceWalkSurvivalProbability_nonneg_le_one
                vs (x - z)).2
      have hcompare :
          (∫ z in Set.Iic x, (1 - 2 * T z) ∂mu) <=
            ∫ z in Set.Iic x, P z ∂mu := by
        apply setIntegral_mono_on
        · exact (integrableOn_const : IntegrableOn
            (fun _ : Real => (1 : Real)) (Set.Iic x) mu).sub
              (hTint.const_mul 2).integrableOn
        · exact hPint
        · exact measurableSet_Iic
        · intro z hz
          exact ih hvTail (sub_nonneg.mpr hz)
      have hcross :
          (1 / 2 : Real) * mu.real (Set.Ioi x) <=
            ∫ z in Set.Ioi x, T z ∂mu := by
        simpa only [mu, T] using
          half_mul_gaussian_Ioi_le_integral_upperTail v vs hvTail x
      have hpartition :
          mu.real (Set.Iic x) + mu.real (Set.Ioi x) = 1 := by
        have h := measureReal_add_measureReal_compl
          (μ := mu) (s := Set.Iic x) measurableSet_Iic
        simpa only [compl_Iic, probReal_univ] using h
      have htailSplit :
          gaussianVarianceWalkUpperTail (v :: vs) x =
            (∫ z in Set.Iic x, T z ∂mu) +
              ∫ z in Set.Ioi x, T z ∂mu := by
        rw [gaussianVarianceWalkUpperTail_cons]
        rw [← integral_add_compl measurableSet_Iic hTint, compl_Iic]
      have hrestricted :
          (∫ z in Set.Iic x, (1 - 2 * T z) ∂mu) =
            mu.real (Set.Iic x) -
              2 * ∫ z in Set.Iic x, T z ∂mu := by
        have hOne : IntegrableOn (fun _ : Real => (1 : Real))
            (Set.Iic x) mu := integrableOn_const
        have hTwo : IntegrableOn (fun z => 2 * T z)
            (Set.Iic x) mu := (hTint.const_mul 2).integrableOn
        calc
          (∫ z in Set.Iic x, (1 - 2 * T z) ∂mu) =
              (∫ _z in Set.Iic x, (1 : Real) ∂mu) -
                ∫ z in Set.Iic x, 2 * T z ∂mu :=
            integral_sub hOne hTwo
          _ = mu.real (Set.Iic x) -
                2 * ∫ z in Set.Iic x, T z ∂mu := by
            rw [setIntegral_const, integral_const_mul]
            simp only [smul_eq_mul, mul_one]
      rw [Problem520.gaussianVarianceWalkSurvivalProbability,
        Problem520.gaussianVarianceKilledExpectation_cons]
      change 1 - 2 * gaussianVarianceWalkUpperTail (v :: vs) x <=
        ∫ z in Set.Iic x, P z ∂mu
      calc
        1 - 2 * gaussianVarianceWalkUpperTail (v :: vs) x =
            1 - 2 * ((∫ z in Set.Iic x, T z ∂mu) +
              ∫ z in Set.Ioi x, T z ∂mu) := by rw [htailSplit]
        _ <= mu.real (Set.Iic x) -
              2 * ∫ z in Set.Iic x, T z ∂mu := by
          nlinarith
        _ = ∫ z in Set.Iic x, (1 - 2 * T z) ∂mu := hrestricted.symm
        _ <= ∫ z in Set.Iic x, P z ∂mu := hcompare

/-- Symmetry identifies the remainder in Levy's inequality with a centered
Gaussian interval. -/
theorem one_sub_two_mul_gaussianUpperTail_eq_Icc
    {v : NNReal} {x : Real} (hx : 0 <= x) :
    1 - 2 * (gaussianReal 0 v).real (Set.Ioi x) =
      (gaussianReal 0 v).real (Set.Icc (-x) x) := by
  let mu : Measure Real := gaussianReal 0 v
  have hmap : mu.map (fun z : Real => -z) = mu := by
    simpa only [mu, neg_zero] using
      (gaussianReal_map_neg (μ := (0 : Real)) (v := v))
  have hsymm : mu.real (Set.Iio (-x)) = mu.real (Set.Ioi x) := by
    apply congrArg ENNReal.toReal
    calc
      mu (Set.Iio (-x)) =
          (mu.map (fun z : Real => -z)) (Set.Iio (-x)) := by rw [hmap]
      _ = mu ((fun z : Real => -z) ⁻¹' Set.Iio (-x)) := by
        rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
      _ = mu (Set.Ioi x) := by
        congr 1
        ext z
        simp
  have hdisj : Disjoint (Set.Iio (-x)) (Set.Ioi x) := by
    exact Set.disjoint_left.2 fun z hzLower hzUpper => by
      have hzLower' : z < -x := hzLower
      have hzUpper' : x < z := hzUpper
      linarith
  have houtside :
      mu.real ((Set.Icc (-x) x)ᶜ) =
        2 * mu.real (Set.Ioi x) := by
    rw [show (Set.Icc (-x) x)ᶜ = Set.Iio (-x) ∪ Set.Ioi x by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_union,
        Set.mem_Iio, Set.mem_Ioi]
      constructor <;> intro h
      · by_cases hz : z < -x
        · exact Or.inl hz
        · exact Or.inr (lt_of_not_ge fun hzx => h ⟨le_of_not_gt hz, hzx⟩)
      · rintro ⟨hzLower, hzUpper⟩
        rcases h with h | h <;> linarith]
    rw [measureReal_union hdisj measurableSet_Ioi, hsymm]
    ring
  have hcompl := measureReal_compl
    (μ := mu) (s := Set.Icc (-x) x) measurableSet_Icc
  rw [houtside, probReal_univ] at hcompl
  change 1 - 2 * mu.real (Set.Ioi x) = mu.real (Set.Icc (-x) x)
  linarith

/-- Elementary density lower bound on a fixed centered interval. -/
theorem two_mul_invSqrt_mul_exp_le_gaussianReal_Icc_neg_one_one
    {v : NNReal} (hv : v ≠ 0) :
    2 * (Real.sqrt (2 * Real.pi * (v : Real)))⁻¹ *
        Real.exp (-(1 : Real) / (2 * (v : Real))) <=
      (gaussianReal 0 v).real (Set.Icc (-1) 1) := by
  have hvReal : 0 < (v : Real) := by positivity
  rw [Measure.real, gaussianReal_apply_eq_integral 0 hv]
  rw [ENNReal.toReal_ofReal]
  · calc
      2 * (Real.sqrt (2 * Real.pi * (v : Real)))⁻¹ *
          Real.exp (-(1 : Real) / (2 * (v : Real))) =
          ∫ _z in Set.Icc (-1 : Real) 1,
            (Real.sqrt (2 * Real.pi * (v : Real)))⁻¹ *
              Real.exp (-(1 : Real) / (2 * (v : Real))) := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Icc]
        norm_num
        ring
      _ <= ∫ z in Set.Icc (-1 : Real) 1,
          gaussianPDFReal 0 v z := by
        apply setIntegral_mono_on
        · exact integrableOn_const (by simp)
        · exact (integrable_gaussianPDFReal 0 v).integrableOn
        · exact measurableSet_Icc
        · intro z hz
          have hzsq : z ^ 2 <= 1 := by
            have hzleft : 0 <= z + 1 := by linarith [hz.1]
            have hzright : 0 <= 1 - z := by linarith [hz.2]
            nlinarith [mul_nonneg hzleft hzright]
          have hquot : z ^ 2 / (2 * (v : Real)) <=
              1 / (2 * (v : Real)) := by
            exact div_le_div_of_nonneg_right hzsq (by positivity)
          have hexp : Real.exp (-(1 : Real) / (2 * (v : Real))) <=
              Real.exp (-z ^ 2 / (2 * (v : Real))) := by
            apply Real.exp_le_exp.mpr
            calc
              -(1 : Real) / (2 * (v : Real)) =
                  -(1 / (2 * (v : Real))) := by ring
              _ <= -(z ^ 2 / (2 * (v : Real))) := neg_le_neg hquot
              _ = -z ^ 2 / (2 * (v : Real)) := by ring
          unfold gaussianPDFReal
          simp only [sub_zero]
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
  · exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun z => gaussianPDFReal_nonneg 0 v z)

/-- If total variance is comparable to the number of steps, the centered
terminal interval has the required inverse-square-root mass. -/
theorem exp_neg_two_div_sqrt_le_gaussianReal_Icc_neg_one_one
    {v : NNReal} {n : Nat} (hn : 0 < n)
    (hlower : (n : Real) / 4 <= (v : Real))
    (hupper : (v : Real) <= (n : Real) / 2) :
    Real.exp (-2) / Real.sqrt (n : Real) <=
      (gaussianReal 0 v).real (Set.Icc (-1) 1) := by
  have hvReal : 0 < (v : Real) := by
    have hnReal : 0 < (n : Real) := by exact_mod_cast hn
    linarith
  have hv : v ≠ 0 := by
    intro hzero
    simp [hzero] at hvReal
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hsqrtN : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.2 hnReal
  have hden : 0 < Real.sqrt (2 * Real.pi * (v : Real)) := by positivity
  have hinside : 2 * Real.pi * (v : Real) <= 4 * (n : Real) := by
    calc
      2 * Real.pi * (v : Real) <=
          2 * Real.pi * ((n : Real) / 2) := by gcongr
      _ <= 4 * (n : Real) := by
        nlinarith [Real.pi_lt_four]
  have hdenle : Real.sqrt (2 * Real.pi * (v : Real)) <=
      2 * Real.sqrt (n : Real) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hsquare := Real.sq_sqrt hnReal.le
      nlinarith
  have hcoef : 1 / (2 * Real.sqrt (n : Real)) <=
      (Real.sqrt (2 * Real.pi * (v : Real)))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hden hdenle
  have hquot : 1 / (2 * (v : Real)) <= 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (v : Real))).2
    have hnOne : (1 : Real) <= n := by exact_mod_cast hn
    nlinarith
  have hexp : Real.exp (-2) <=
      Real.exp (-(1 : Real) / (2 * (v : Real))) := by
    apply Real.exp_le_exp.mpr
    calc
      (-2 : Real) <= -(1 / (2 * (v : Real))) := neg_le_neg hquot
      _ = -(1 : Real) / (2 * (v : Real)) := by ring
  calc
    Real.exp (-2) / Real.sqrt (n : Real) =
        2 * (1 / (2 * Real.sqrt (n : Real))) * Real.exp (-2) := by
      field_simp
    _ <= 2 * (Real.sqrt (2 * Real.pi * (v : Real)))⁻¹ *
        Real.exp (-(1 : Real) / (2 * (v : Real))) := by
      gcongr
    _ <= (gaussianReal 0 v).real (Set.Icc (-1) 1) :=
      two_mul_invSqrt_mul_exp_le_gaussianReal_Icc_neg_one_one hv

/-- Elementary density lower bound on the centered interval of radius
`1 / 2`.  The deliberately weak exponent leaves a simple numerical budget
for the auxiliary-fence subtraction. -/
theorem invSqrt_mul_exp_eighth_le_gaussianReal_Icc_neg_half_half
    {v : NNReal} (hv : v ≠ 0) :
    (Real.sqrt (2 * Real.pi * (v : Real)))⁻¹ *
        Real.exp (-(1 : Real) / (8 * (v : Real))) <=
      (gaussianReal 0 v).real (Set.Icc (-(1 / 2 : Real)) (1 / 2)) := by
  have hvReal : 0 < (v : Real) := by positivity
  rw [Measure.real, gaussianReal_apply_eq_integral 0 hv]
  rw [ENNReal.toReal_ofReal]
  · calc
      (Real.sqrt (2 * Real.pi * (v : Real)))⁻¹ *
          Real.exp (-(1 : Real) / (8 * (v : Real))) =
          ∫ _z in Set.Icc (-(1 / 2 : Real)) (1 / 2),
            (Real.sqrt (2 * Real.pi * (v : Real)))⁻¹ *
              Real.exp (-(1 : Real) / (8 * (v : Real))) := by
        rw [setIntegral_const, Measure.real_def, Real.volume_Icc]
        norm_num
      _ <= ∫ z in Set.Icc (-(1 / 2 : Real)) (1 / 2),
          gaussianPDFReal 0 v z := by
        apply setIntegral_mono_on
        · exact integrableOn_const (by simp)
        · exact (integrable_gaussianPDFReal 0 v).integrableOn
        · exact measurableSet_Icc
        · intro z hz
          have hzsq : z ^ 2 <= (1 / 4 : Real) := by
            have hzleft : 0 <= z + 1 / 2 := by linarith [hz.1]
            have hzright : 0 <= 1 / 2 - z := by linarith [hz.2]
            nlinarith [mul_nonneg hzleft hzright]
          have hquot : z ^ 2 / (2 * (v : Real)) <=
              1 / (8 * (v : Real)) := by
            calc
              z ^ 2 / (2 * (v : Real)) <=
                  (1 / 4 : Real) / (2 * (v : Real)) :=
                div_le_div_of_nonneg_right hzsq (by positivity)
              _ = 1 / (8 * (v : Real)) := by ring
          have hexp : Real.exp (-(1 : Real) / (8 * (v : Real))) <=
              Real.exp (-z ^ 2 / (2 * (v : Real))) := by
            apply Real.exp_le_exp.mpr
            calc
              -(1 : Real) / (8 * (v : Real)) =
                  -(1 / (8 * (v : Real))) := by ring
              _ <= -(z ^ 2 / (2 * (v : Real))) := neg_le_neg hquot
              _ = -z ^ 2 / (2 * (v : Real)) := by ring
          unfold gaussianPDFReal
          simp only [sub_zero]
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
  · exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun z => gaussianPDFReal_nonneg 0 v z)

/-- The half-height centered terminal interval still has a fixed
inverse-square-root mass. -/
theorem half_exp_neg_two_div_sqrt_le_gaussianReal_Icc_neg_half_half
    {v : NNReal} {n : Nat} (hn : 0 < n)
    (hlower : (n : Real) / 4 <= (v : Real))
    (hupper : (v : Real) <= (n : Real) / 2) :
    Real.exp (-2) / (2 * Real.sqrt (n : Real)) <=
      (gaussianReal 0 v).real (Set.Icc (-(1 / 2 : Real)) (1 / 2)) := by
  have hvReal : 0 < (v : Real) := by
    have hnReal : 0 < (n : Real) := by exact_mod_cast hn
    linarith
  have hv : v ≠ 0 := by
    intro hzero
    simp [hzero] at hvReal
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hsqrtN : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.2 hnReal
  have hden : 0 < Real.sqrt (2 * Real.pi * (v : Real)) := by positivity
  have hinside : 2 * Real.pi * (v : Real) <= 4 * (n : Real) := by
    calc
      2 * Real.pi * (v : Real) <=
          2 * Real.pi * ((n : Real) / 2) := by gcongr
      _ <= 4 * (n : Real) := by
        nlinarith [Real.pi_lt_four]
  have hdenle : Real.sqrt (2 * Real.pi * (v : Real)) <=
      2 * Real.sqrt (n : Real) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hsquare := Real.sq_sqrt hnReal.le
      nlinarith
  have hcoef : 1 / (2 * Real.sqrt (n : Real)) <=
      (Real.sqrt (2 * Real.pi * (v : Real)))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hden hdenle
  have hquot : 1 / (8 * (v : Real)) <= 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * (v : Real))).2
    have hnOne : (1 : Real) <= n := by exact_mod_cast hn
    nlinarith
  have hexp : Real.exp (-2) <=
      Real.exp (-(1 : Real) / (8 * (v : Real))) := by
    apply Real.exp_le_exp.mpr
    calc
      (-2 : Real) <= -(1 / (8 * (v : Real))) := neg_le_neg hquot
      _ = -(1 : Real) / (8 * (v : Real)) := by ring
  calc
    Real.exp (-2) / (2 * Real.sqrt (n : Real)) =
        (1 / (2 * Real.sqrt (n : Real))) * Real.exp (-2) := by ring
    _ <= (Real.sqrt (2 * Real.pi * (v : Real)))⁻¹ *
        Real.exp (-(1 : Real) / (8 * (v : Real))) := by
      gcongr
    _ <= (gaussianReal 0 v).real
        (Set.Icc (-(1 / 2 : Real)) (1 / 2)) :=
      invSqrt_mul_exp_eighth_le_gaussianReal_Icc_neg_half_half hv

private theorem list_sum_coe_between_length_mul
    (vs : List NNReal) {lo hi : Real}
    (hlower : ∀ v ∈ vs, lo <= (v : Real))
    (hupper : ∀ v ∈ vs, (v : Real) <= hi) :
    lo * vs.length <= (vs.sum : Real) ∧
      (vs.sum : Real) <= hi * vs.length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
      have hvLower := hlower v (by simp)
      have hvUpper := hupper v (by simp)
      have htailLower : ∀ w ∈ vs, lo <= (w : Real) := by
        intro w hw
        exact hlower w (by simp [hw])
      have htailUpper : ∀ w ∈ vs, (w : Real) <= hi := by
        intro w hw
        exact hupper w (by simp [hw])
      have htail := ih htailLower htailUpper
      simp only [List.sum_cons, NNReal.coe_add, List.length_cons, Nat.cast_add,
        Nat.cast_one]
      constructor <;> nlinarith

/-- Explicit lower ballot estimate for a varying Gaussian walk with all
coordinate variances in `[1/4,1/2]`. -/
theorem exp_neg_two_div_sqrt_le_gaussianVarianceWalkSurvivalProbability
    (vs : List NNReal) (hne : vs ≠ [])
    (hlower : ∀ v ∈ vs, (1 / 4 : NNReal) <= v)
    (hupper : ∀ v ∈ vs, v <= (1 / 2 : NNReal)) :
    Real.exp (-2) / Real.sqrt (vs.length : Real) <=
      Problem520.gaussianVarianceWalkSurvivalProbability vs 1 := by
  have hn : 0 < vs.length := List.length_pos_of_ne_nil hne
  have hpos : ∀ v ∈ vs, v ≠ 0 := by
    intro v hv hzero
    have := hlower v hv
    simp [hzero] at this
  have hbounds := list_sum_coe_between_length_mul vs
    (lo := (1 / 4 : Real)) (hi := (1 / 2 : Real))
    (fun v hv => by exact_mod_cast hlower v hv)
    (fun v hv => by exact_mod_cast hupper v hv)
  have hmass := exp_neg_two_div_sqrt_le_gaussianReal_Icc_neg_one_one
    (v := vs.sum) (n := vs.length) hn (by nlinarith [hbounds.1])
      (by nlinarith [hbounds.2])
  have hsymm := one_sub_two_mul_gaussianUpperTail_eq_Icc
    (v := vs.sum) (x := (1 : Real)) (by norm_num)
  have hlevy :=
    one_sub_two_mul_upperTail_le_gaussianVarianceWalkSurvivalProbability
      vs hpos (x := (1 : Real)) (by norm_num)
  calc
    Real.exp (-2) / Real.sqrt (vs.length : Real) <=
        (gaussianReal 0 vs.sum).real (Set.Icc (-1) 1) := hmass
    _ = 1 - 2 * gaussianVarianceWalkUpperTail vs 1 := by
      simpa only [gaussianVarianceWalkUpperTail] using hsymm.symm
    _ <= Problem520.gaussianVarianceWalkSurvivalProbability vs 1 := hlevy

/-- The same Lévy lower ballot estimate at flat height `1 / 2`. -/
theorem half_exp_neg_two_div_sqrt_le_gaussianVarianceWalkSurvivalProbability
    (vs : List NNReal) (hne : vs ≠ [])
    (hlower : ∀ v ∈ vs, (1 / 4 : NNReal) <= v)
    (hupper : ∀ v ∈ vs, v <= (1 / 2 : NNReal)) :
    Real.exp (-2) / (2 * Real.sqrt (vs.length : Real)) <=
      Problem520.gaussianVarianceWalkSurvivalProbability vs (1 / 2) := by
  have hn : 0 < vs.length := List.length_pos_of_ne_nil hne
  have hpos : ∀ v ∈ vs, v ≠ 0 := by
    intro v hv hzero
    have := hlower v hv
    simp [hzero] at this
  have hbounds := list_sum_coe_between_length_mul vs
    (lo := (1 / 4 : Real)) (hi := (1 / 2 : Real))
    (fun v hv => by exact_mod_cast hlower v hv)
    (fun v hv => by exact_mod_cast hupper v hv)
  have hmass :=
    half_exp_neg_two_div_sqrt_le_gaussianReal_Icc_neg_half_half
      (v := vs.sum) (n := vs.length) hn (by nlinarith [hbounds.1])
        (by nlinarith [hbounds.2])
  have hsymm := one_sub_two_mul_gaussianUpperTail_eq_Icc
    (v := vs.sum) (x := (1 / 2 : Real)) (by norm_num)
  have hlevy :=
    one_sub_two_mul_upperTail_le_gaussianVarianceWalkSurvivalProbability
      vs hpos (x := (1 / 2 : Real)) (by norm_num)
  calc
    Real.exp (-2) / (2 * Real.sqrt (vs.length : Real)) <=
        (gaussianReal 0 vs.sum).real
          (Set.Icc (-(1 / 2 : Real)) (1 / 2)) := hmass
    _ = 1 - 2 * gaussianVarianceWalkUpperTail vs (1 / 2) := by
      simpa only [gaussianVarianceWalkUpperTail] using hsymm.symm
    _ <= Problem520.gaussianVarianceWalkSurvivalProbability vs (1 / 2) :=
      hlevy

/-- Reindex the list model built from a finite variance vector back to the
original finite coordinates. -/
theorem gaussianVarianceWalkSurvivalProbability_ofFn_eq_probability_fin
    (n : Nat) (variance : Fin n -> NNReal) (x : Real) (hx : 0 <= x) :
    Problem520.gaussianVarianceWalkSurvivalProbability
        (List.ofFn variance) x =
      (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (Problem520.gaussianWalkSurvivalSet n x) := by
  let vs : List NNReal := List.ofFn variance
  rw [Problem520.gaussianVarianceWalkSurvivalProbability_eq_measureReal
    vs hx]
  have hvlen : vs.length = n := by simp [vs]
  let e : Fin vs.length ≃ Fin n := finCongr hvlen
  let E : (Fin vs.length -> Real) ≃ᵐ (Fin n -> Real) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Real) e
  have hcoord (i : Fin vs.length) : vs.get i = variance (e i) := by
    dsimp only [vs, e]
    rw [List.get_ofFn]
    congr 1
  have hsource : Problem520.gaussianVarianceWalkMeasure vs =
      Measure.pi (fun i : Fin vs.length =>
        gaussianReal 0 (variance (e i))) := by
    unfold Problem520.gaussianVarianceWalkMeasure
    congr 1
    funext i
    rw [hcoord]
  have hmp := measurePreserving_piCongrLeft
    (μ := fun i : Fin n => gaussianReal 0 (variance i)) e
  have hE (omega : Fin vs.length -> Real) :
      E omega = fun j => omega (e.symm j) := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Real) e)
      omega (e i) = omega i
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin n => Real) e omega i
  have hpre : E ⁻¹' Problem520.gaussianWalkSurvivalSet n x =
      Problem520.gaussianWalkSurvivalSet vs.length x := by
    ext omega
    simp only [Set.mem_preimage, Problem520.gaussianWalkSurvivalSet,
      Set.mem_setOf_eq]
    rw [hE]
    exact Problem520.gaussianWalkSurvives_reindex_finCongr hvlen x omega
  calc
    (Problem520.gaussianVarianceWalkMeasure vs).real
        (Problem520.gaussianWalkSurvivalSet vs.length x) =
      (Measure.pi (fun i : Fin vs.length =>
        gaussianReal 0 (variance (e i)))).real
        (Problem520.gaussianWalkSurvivalSet vs.length x) := by rw [hsource]
    _ = (Measure.pi (fun i : Fin n =>
        gaussianReal 0 (variance i))).real
        (Problem520.gaussianWalkSurvivalSet n x) := by
      rw [← hpre, ← map_measureReal_apply E.measurable
        (Problem520.measurableSet_gaussianWalkSurvivalSet n hx)]
      rw [hmp.map_eq]

/-- Finite-vector form of the lower Gaussian ballot estimate at height
`1 / 2`. -/
theorem half_exp_neg_two_div_sqrt_le_gaussianVarianceWalk_probability_fin
    (n : Nat) (hn : 0 < n) (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    Real.exp (-2) / (2 * Real.sqrt (n : Real)) <=
      (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (Problem520.gaussianWalkSurvivalSet n (1 / 2)) := by
  let vs : List NNReal := List.ofFn variance
  have hne : vs ≠ [] := by
    intro hnil
    have : vs.length = 0 := by simp [hnil]
    simp only [vs, List.length_ofFn] at this
    omega
  have hlower' : ∀ v ∈ vs, (1 / 4 : NNReal) <= v :=
    (List.forall_mem_ofFn_iff).2 hlower
  have hupper' : ∀ v ∈ vs, v <= (1 / 2 : NNReal) :=
    (List.forall_mem_ofFn_iff).2 hupper
  have hmain :=
    half_exp_neg_two_div_sqrt_le_gaussianVarianceWalkSurvivalProbability
      vs hne hlower' hupper'
  have htransport :=
    gaussianVarianceWalkSurvivalProbability_ofFn_eq_probability_fin
      n variance (1 / 2 : Real) (by norm_num)
  simpa only [vs, List.length_ofFn, htransport] using hmain

/-- Finite-vector form of the lower Gaussian ballot estimate. -/
theorem exp_neg_two_div_sqrt_le_gaussianVarianceWalk_probability_fin
    (n : Nat) (hn : 0 < n) (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    Real.exp (-2) / Real.sqrt (n : Real) <=
      (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
        (Problem520.gaussianWalkSurvivalSet n 1) := by
  let vs : List NNReal := List.ofFn variance
  have hne : vs ≠ [] := by
    intro hnil
    have : vs.length = 0 := by simp [hnil]
    simp only [vs, List.length_ofFn] at this
    omega
  have hlower' : ∀ v ∈ vs, (1 / 4 : NNReal) <= v :=
    (List.forall_mem_ofFn_iff).2 hlower
  have hupper' : ∀ v ∈ vs, v <= (1 / 2 : NNReal) :=
    (List.forall_mem_ofFn_iff).2 hupper
  have hmain := exp_neg_two_div_sqrt_le_gaussianVarianceWalkSurvivalProbability
    vs hne hlower' hupper'
  rw [Problem520.gaussianVarianceWalkSurvivalProbability_eq_measureReal
    vs (by norm_num : (0 : Real) <= 1)] at hmain
  have hvlen : vs.length = n := by simp [vs]
  let e : Fin vs.length ≃ Fin n := finCongr hvlen
  let E : (Fin vs.length -> Real) ≃ᵐ (Fin n -> Real) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n => Real) e
  have hcoord (i : Fin vs.length) : vs.get i = variance (e i) := by
    dsimp only [vs, e]
    rw [List.get_ofFn]
    congr 1
  have hsource : Problem520.gaussianVarianceWalkMeasure vs =
      Measure.pi (fun i : Fin vs.length =>
        gaussianReal 0 (variance (e i))) := by
    unfold Problem520.gaussianVarianceWalkMeasure
    congr 1
    funext i
    rw [hcoord]
  have hmp := measurePreserving_piCongrLeft
    (μ := fun i : Fin n => gaussianReal 0 (variance i)) e
  have hE (omega : Fin vs.length -> Real) :
      E omega = fun j => omega (e.symm j) := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Real) e)
      omega (e i) = omega i
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin n => Real) e omega i
  have hpre : E ⁻¹' Problem520.gaussianWalkSurvivalSet n 1 =
      Problem520.gaussianWalkSurvivalSet vs.length 1 := by
    ext omega
    simp only [Set.mem_preimage, Problem520.gaussianWalkSurvivalSet,
      Set.mem_setOf_eq]
    rw [hE]
    exact Problem520.gaussianWalkSurvives_reindex_finCongr hvlen 1 omega
  have htransport :
      (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).real
          (Problem520.gaussianWalkSurvivalSet n 1) =
        (Problem520.gaussianVarianceWalkMeasure vs).real
          (Problem520.gaussianWalkSurvivalSet vs.length 1) := by
    rw [← hmp.map_eq]
    rw [map_measureReal_apply E.measurable
      (Problem520.measurableSet_gaussianWalkSurvivalSet n
        (by norm_num : (0 : Real) <= 1))]
    rw [hpre, hsource]
  rw [htransport]
  simpa only [vs, List.length_ofFn] using hmain

/-- Unconditional scheduled central-band lower ballot estimate under the
variance-matched Gaussian product law. -/
theorem exists_exp_neg_two_div_sqrt_le_harperScheduledCentralBandGaussian_survival :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start -> ∀ n : Nat, 0 < n ->
      ∀ y : Nat, Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
            Real.exp (-2) / Real.sqrt (n : Real) <=
              (Measure.pi (fun i : Fin n =>
                Problem520.harperGaussianBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y
                    (start + (i : Nat))) t t)).real
                (Problem520.gaussianWalkSurvivalSet n 1) := by
  obtain ⟨J, hJ⟩ :=
    Problem520.exists_harperScheduledCentralBandVarianceVector_quarter_half
  refine ⟨J, ?_⟩
  intro d start hstart n hn y hy t htLower htUpper
  let variance : Fin n -> NNReal := fun i =>
    Problem520.harperLinearBlockVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t
  have hvar := hJ d start hstart n y hy t htLower htUpper
    (fun _i : Fin n => t) (by intro i; simp)
  have hlower : ∀ i, (1 / 4 : NNReal) <= variance i := by
    intro i
    exact_mod_cast (hvar i).1.le
  have hupper : ∀ i, variance i <= (1 / 2 : NNReal) := by
    intro i
    exact_mod_cast (hvar i).2.le
  have hmain := exp_neg_two_div_sqrt_le_gaussianVarianceWalk_probability_fin
    n hn variance hlower hupper
  simpa only [variance, Problem520.harperGaussianBlockLaw] using hmain

/-- Chebyshev for a single centered Gaussian coordinate. -/
theorem gaussianReal_real_abs_gt_le
    (v : NNReal) {R : Real} (hR : 0 < R) :
    (gaussianReal 0 v).real {z | R < |z|} <= (v : Real) / R ^ 2 := by
  have hsecond : (∫ z, z ^ 2 ∂gaussianReal 0 v) = (v : Real) := by
    simpa only [variance_eq_integral measurable_id'.aemeasurable,
      integral_id_gaussianReal, sub_zero] using
        (variance_fun_id_gaussianReal (μ := (0 : Real)) (v := v))
  have hsquareIntegrable :
      Integrable (fun z : Real => z ^ 2) (gaussianReal 0 v) := by
    have hid : MemLp (fun z : Real => z) 2 (gaussianReal 0 v) := by
      simpa only [id_eq] using
        (memLp_id_gaussianReal' (μ := (0 : Real)) (v := v) 2 (by norm_num))
    exact hid.integrable_sq
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := gaussianReal 0 v) (ae_of_all _ fun z => sq_nonneg z)
    hsquareIntegrable
    (R ^ 2)
  have hsubset : {z : Real | R < |z|} ⊆ {z | R ^ 2 <= z ^ 2} := by
    intro z hz
    change R ^ 2 <= z ^ 2
    rw [← sq_abs z]
    exact le_of_lt ((sq_lt_sq₀ hR.le (abs_nonneg z)).2 hz)
  have hmul : R ^ 2 * (gaussianReal 0 v).real {z : Real | R < |z|} <=
      (v : Real) := by
    calc
      R ^ 2 * (gaussianReal 0 v).real {z : Real | R < |z|} <=
          R ^ 2 * (gaussianReal 0 v).real {z | R ^ 2 <= z ^ 2} :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsubset) (sq_nonneg R)
      _ <= ∫ z, z ^ 2 ∂gaussianReal 0 v := hmarkov
      _ = (v : Real) := hsecond
  exact (le_div_iff₀ (sq_pos_of_pos hR)).2 (by
    simpa only [mul_comm] using hmul)

/-- The variance-matched scheduled Gaussian product leaves the standard
moderate box with the same geometric bound as the actual tilted path. -/
theorem harperScheduledGaussianProductMeasure_box_compl_le
    {y start n : Nat} (t : Real) (hstart : 8 <= start)
    (hvar : ∀ i : Fin n,
      Problem520.harperLinearBlockVariance y
          (Problem520.harperScheduledPrimeBlock y
            (start + (i : Nat))) t t <= (1 / 2 : Real)) :
    (Measure.pi (fun i : Fin n =>
      Problem520.harperGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y
          (start + (i : Nat))) t t)).real
      (Problem520.harperCoordinateBox
        (Problem520.harperScheduledModerateRadius start n))ᶜ <=
      64 * (1 / 2 : Real) ^ start := by
  classical
  let variance : Fin n -> NNReal := fun i =>
    Problem520.harperLinearBlockVarianceNNReal y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t
  let Q : Measure (Fin n -> Real) :=
    Measure.pi fun i => gaussianReal 0 (variance i)
  let bad : Fin n -> Set Real := fun i =>
    {z | Problem520.harperScheduledModerateRadius start n i < |z|}
  have hevent :
      (Problem520.harperCoordinateBox
        (Problem520.harperScheduledModerateRadius start n))ᶜ =
        ⋃ i : Fin n, (fun omega : Fin n -> Real => omega i) ⁻¹' bad i := by
    ext omega
    simp only [Set.mem_compl_iff, Problem520.mem_harperCoordinateBox,
      Set.mem_iUnion, Set.mem_preimage, bad, Set.mem_setOf_eq,
      not_forall, not_le]
  have hcoord (i : Fin n) : Q.real
      ((fun omega : Fin n -> Real => omega i) ⁻¹' bad i) =
        (gaussianReal 0 (variance i)).real (bad i) := by
    have hmap := Measure.pi_map_eval
      (μ := fun j : Fin n => gaussianReal 0 (variance j)) i
    have hmap' : Q.map (Function.eval i) = gaussianReal 0 (variance i) := by
      simpa only [Q, measure_univ, Finset.prod_const_one,
        one_smul] using hmap
    have hbad : MeasurableSet (bad i) := by
      dsimp only [bad]
      exact measurableSet_lt measurable_const
        (measurable_abs.comp measurable_id)
    have happ := map_measureReal_apply
      (μ := Q) (measurable_pi_apply i) hbad
    rw [hmap'] at happ
    exact happ.symm
  change Q.real
      (Problem520.harperCoordinateBox
        (Problem520.harperScheduledModerateRadius start n))ᶜ <= _
  rw [hevent]
  calc
    Q.real (⋃ i : Fin n,
        (fun omega : Fin n -> Real => omega i) ⁻¹' bad i) <=
        ∑ i : Fin n, Q.real
          ((fun omega : Fin n -> Real => omega i) ⁻¹' bad i) :=
      measureReal_iUnion_fintype_le _
    _ = ∑ i : Fin n, (gaussianReal 0 (variance i)).real (bad i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact hcoord i
    _ <= ∑ i : Fin n, 32 * (1 / 2 : Real) ^ (start + (i : Nat)) := by
      apply Finset.sum_le_sum
      intro i _hi
      let R := Problem520.harperScheduledModerateRadius start n i
      have hR : 0 < R :=
        Problem520.harperScheduledModerateRadius_pos_of_eight_le i
          (hstart.trans (Nat.le_add_right start i))
      have hR2 : (1 / 64 : Real) *
          (((2 ^ (start + (i : Nat)) : Nat) : Real)) <= R ^ 2 :=
        Problem520.one_sixtyFourth_two_pow_le_harperScheduledModerateRadius_sq
          i (hstart.trans (Nat.le_add_right start i))
      have htail := gaussianReal_real_abs_gt_le (variance i) hR
      have hvariance : (variance i : Real) <= (1 / 2 : Real) := by
        simpa only [variance,
          Problem520.coe_harperLinearBlockVarianceNNReal] using hvar i
      have hpow : (0 : Real) <
          ((2 ^ (start + (i : Nat)) : Nat) : Real) := by positivity
      calc
        (gaussianReal 0 (variance i)).real (bad i) <=
            (variance i : Real) / R ^ 2 := by simpa only [bad, R] using htail
        _ <= (1 / 2 : Real) / R ^ 2 :=
          div_le_div_of_nonneg_right hvariance (sq_nonneg R)
        _ <= (1 / 2 : Real) /
            ((1 / 64 : Real) *
              (((2 ^ (start + (i : Nat)) : Nat) : Real))) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hR2
        _ = 32 * (1 / 2 : Real) ^ (start + (i : Nat)) := by
          rw [div_eq_mul_inv]
          norm_num [Nat.cast_pow]
          rw [← inv_pow]
          norm_num
          ring
    _ = 32 * (1 / 2 : Real) ^ start *
        ∑ k ∈ Finset.range n, (1 / 2 : Real) ^ k := by
      rw [Fin.sum_univ_eq_sum_range
        (fun k : Nat => 32 * (1 / 2 : Real) ^ (start + k)) n]
      calc
        (∑ k ∈ Finset.range n,
            32 * (1 / 2 : Real) ^ (start + k)) =
            ∑ k ∈ Finset.range n,
              (32 * (1 / 2 : Real) ^ start) * (1 / 2 : Real) ^ k := by
          apply Finset.sum_congr rfl
          intro k _hk
          rw [pow_add]
          ring
        _ = _ := by rw [Finset.mul_sum]
    _ <= 32 * (1 / 2 : Real) ^ start * 2 := by
      gcongr
      exact sum_geometric_two_le n
    _ = 64 * (1 / 2 : Real) ^ start := by ring

/-- A deliberately coarse elementary exponential-over-linear estimate. -/
theorem two_thousand_forty_eight_mul_le_two_pow
    {n : Nat} (hn : 16 <= n) : 2048 * n <= 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      omega

/-- A rational lower bound sufficient for absorbing the Gaussian box tail. -/
theorem one_ninth_le_exp_neg_two : (1 / 9 : Real) <= Real.exp (-2) := by
  have hone : Real.exp 1 <= 3 := Real.exp_one_lt_three.le
  have htwo : Real.exp 2 <= 9 := by
    rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1]
  rw [Real.exp_neg]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (Real.exp_pos 2) htwo)

/-- Starting a path at its own length makes the geometric moderate-box tail
smaller than half of the elementary Gaussian ballot mass as soon as the path
has sixteen coordinates. -/
theorem harperGaussian_box_budget_self
    (n : Nat) (hn : 16 <= n) :
    64 * (1 / 2 : Real) ^ n <=
      (1 / 2 : Real) * (Real.exp (-2) / Real.sqrt (n : Real)) := by
  have hnpos : 0 < n := by omega
  have hsqrtPos : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.2 (by positivity)
  have hsqrtLe : Real.sqrt (n : Real) <= (n : Real) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hnOne : (1 : Real) <= n := by exact_mod_cast (show 1 <= n by omega)
      nlinarith
  have hpowNat := two_thousand_forty_eight_mul_le_two_pow hn
  have hpowReal : 1152 * Real.sqrt (n : Real) <= (2 : Real) ^ n := by
    have hcast : (2048 : Real) * n <= (2 : Real) ^ n := by
      exact_mod_cast hpowNat
    nlinarith
  have hsmall : 64 * (1 / 2 : Real) ^ n <=
      (1 / 18 : Real) / Real.sqrt (n : Real) := by
    have hfrac : 64 * Real.sqrt (n : Real) / (2 : Real) ^ n <=
        (1 / 18 : Real) := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    apply (le_div_iff₀ hsqrtPos).2
    calc
      64 * (1 / 2 : Real) ^ n * Real.sqrt (n : Real) =
          64 * Real.sqrt (n : Real) / (2 : Real) ^ n := by
        rw [one_div, inv_pow, div_eq_mul_inv]
        ring
      _ <= (1 / 18 : Real) := hfrac
  calc
    64 * (1 / 2 : Real) ^ n <=
        (1 / 18 : Real) / Real.sqrt (n : Real) := hsmall
    _ = (1 / 2 : Real) *
        ((1 / 9 : Real) / Real.sqrt (n : Real)) := by ring
    _ <= (1 / 2 : Real) *
        (Real.exp (-2) / Real.sqrt (n : Real)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right one_ninth_le_exp_neg_two hsqrtPos.le)
        (by norm_num)

/-! ## Composition with the reverse local-limit comparison -/

theorem harperPathPartialSum_le_of_gaussianWalkSurvives
    (n : Nat) (x : Real) (omega : Fin n -> Real)
    (h : Problem520.gaussianWalkSurvives n x omega) (k : Fin n) :
    Problem520.harperPathPartialSum omega k <= x := by
  induction n generalizing x with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) k
      · simpa only [Problem520.harperPathPartialSum_zero] using h.1
      · rw [Problem520.harperPathPartialSum_succ]
        have htail := ih (x - omega 0) (fun i => omega i.succ) h.2 j
        linarith

/-- Lower boundary which is automatic inside the scheduled coordinate box,
with one extra cumulative mesh width reserved for reverse slicing. -/
noncomputable def harperScheduledAutomaticLowerBarrier
    (start n : Nat) (k : Fin n) : Real :=
  -(∑ i ∈ Finset.Iic k,
      Problem520.harperScheduledModerateRadius start n i) -
    Problem520.harperCumulativeCellWidth
      (Problem520.harperScheduledRelativeCellWidth start n) k

/-- Upper boundary whose contracted version is the flat level `1`. -/
noncomputable def harperScheduledAutomaticUpperBarrier
    (start n : Nat) (k : Fin n) : Real :=
  1 + Problem520.harperCumulativeCellWidth
    (Problem520.harperScheduledRelativeCellWidth start n) k

/-- After discarding only the Gaussian moderate-box complement, the reverse
local-limit comparison transfers the Levy lower ballot bound to the actual
centered Harper block product law. -/
theorem
    exists_three_fourths_mul_gaussianBallot_sub_boxTail_le_harperScheduledCentralBandBarrier :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start -> ∀ n : Nat, 0 < n ->
      ∀ y : Nat, Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
            (3 / 4 : Real) *
                (Real.exp (-2) / Real.sqrt (n : Real) -
                  (Measure.pi (fun i : Fin n =>
                    Problem520.harperGaussianBlockLaw y
                      (Problem520.harperScheduledPrimeBlock y
                        (start + (i : Nat))) t t)).real
                    (Problem520.harperCoordinateBox
                      (Problem520.harperScheduledModerateRadius start n))ᶜ) <=
              (Measure.pi (fun i : Fin n =>
                Problem520.harperCenteredLinearBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y
                    (start + (i : Nat))) t t)).real
                (Problem520.harperPartialSumBarrierSet
                  (harperScheduledAutomaticLowerBarrier start n)
                  (harperScheduledAutomaticUpperBarrier start n)) := by
  obtain ⟨Jreverse, hreverse⟩ :=
    exists_three_fourths_mul_gaussian_contractedBarrier_le_harperScheduledCentralBandBarrier
  obtain ⟨Jballot, hballot⟩ :=
    exists_exp_neg_two_div_sqrt_le_harperScheduledCentralBandGaussian_survival
  refine ⟨max Jreverse Jballot, ?_⟩
  intro d start hstart n hn y hy t htLower htUpper
  have hstartReverse : Jreverse + d <= start := by omega
  have hstartBallot : Jballot + d <= start := by omega
  let Q : Measure (Fin n -> Real) := Measure.pi (fun i : Fin n =>
    Problem520.harperGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t)
  let P : Measure (Fin n -> Real) := Measure.pi (fun i : Fin n =>
    Problem520.harperCenteredLinearBlockLaw y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t)
  let R := Problem520.harperScheduledModerateRadius start n
  let delta := Problem520.harperScheduledRelativeCellWidth start n
  let A := Problem520.gaussianWalkSurvivalSet n 1
  let B := Problem520.harperCoordinateBox R
  let lower := harperScheduledAutomaticLowerBarrier start n
  let upper := harperScheduledAutomaticUpperBarrier start n
  have hballotLower : Real.exp (-2) / Real.sqrt (n : Real) <= Q.real A := by
    simpa only [Q, A] using
      hballot d start hstartBallot n hn y hy t htLower htUpper
  have hcover : A ⊆ (A ∩ B) ∪ Bᶜ := by
    intro omega homega
    by_cases hbox : omega ∈ B
    · exact Or.inl ⟨homega, hbox⟩
    · exact Or.inr hbox
  have hsplit : Q.real A <= Q.real (A ∩ B) + Q.real Bᶜ := by
    exact (measureReal_mono hcover).trans (measureReal_union_le _ _)
  have hinterLower :
      Real.exp (-2) / Real.sqrt (n : Real) - Q.real Bᶜ <=
        Q.real (A ∩ B) := by
    linarith
  have hinside : A ∩ B ⊆
      Problem520.harperPartialSumBarrierSet
          (fun k => lower k +
            Problem520.harperCumulativeCellWidth delta k)
          (fun k => upper k -
            Problem520.harperCumulativeCellWidth delta k) ∩ B := by
    rintro omega ⟨hsurv, hbox⟩
    refine ⟨?_, hbox⟩
    intro k
    have hupperPath : Problem520.harperPathPartialSum omega k <= 1 :=
      harperPathPartialSum_le_of_gaussianWalkSurvives n 1 omega hsurv k
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
    · dsimp only [lower, harperScheduledAutomaticLowerBarrier, delta, R]
      linarith
    · dsimp only [upper, harperScheduledAutomaticUpperBarrier, delta]
      linarith
  have hcontracted : Q.real (A ∩ B) <=
      Q.real
        (Problem520.harperPartialSumBarrierSet
            (fun k => lower k +
              Problem520.harperCumulativeCellWidth delta k)
            (fun k => upper k -
              Problem520.harperCumulativeCellWidth delta k) ∩ B) :=
    measureReal_mono hinside
  have hreverseMain := hreverse d start hstartReverse n y hy t
    htLower htUpper lower upper
  change (3 / 4 : Real) *
      (Real.exp (-2) / Real.sqrt (n : Real) - Q.real Bᶜ) <=
    P.real (Problem520.harperPartialSumBarrierSet lower upper)
  calc
    (3 / 4 : Real) *
        (Real.exp (-2) / Real.sqrt (n : Real) - Q.real Bᶜ) <=
        (3 / 4 : Real) * Q.real (A ∩ B) := by gcongr
    _ <= (3 / 4 : Real) * Q.real
        (Problem520.harperPartialSumBarrierSet
            (fun k => lower k +
              Problem520.harperCumulativeCellWidth delta k)
            (fun k => upper k -
              Problem520.harperCumulativeCellWidth delta k) ∩ B) := by gcongr
    _ <= P.real (Problem520.harperPartialSumBarrierSet lower upper) := by
      simpa only [Q, P, R, delta, lower, upper] using hreverseMain

/-- A single explicit numerical checkpoint absorbs the moderate-box error.
When the geometric box tail uses at most half of the Gaussian ballot mass,
the actual centered Harper block walk retains a fixed `3/8` fraction of the
elementary `exp (-2) / sqrt n` lower bound. -/
theorem
    exists_three_eighths_mul_exp_neg_two_div_sqrt_le_harperScheduledCentralBandBarrier :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start -> ∀ n : Nat, 0 < n ->
      ∀ y : Nat, Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
          64 * (1 / 2 : Real) ^ start <=
              (1 / 2 : Real) *
                (Real.exp (-2) / Real.sqrt (n : Real)) ->
            (3 / 8 : Real) *
                (Real.exp (-2) / Real.sqrt (n : Real)) <=
              (Measure.pi (fun i : Fin n =>
                Problem520.harperCenteredLinearBlockLaw y
                  (Problem520.harperScheduledPrimeBlock y
                    (start + (i : Nat))) t t)).real
                (Problem520.harperPartialSumBarrierSet
                  (harperScheduledAutomaticLowerBarrier start n)
                  (harperScheduledAutomaticUpperBarrier start n)) := by
  obtain ⟨Jmain, hmain⟩ :=
    exists_three_fourths_mul_gaussianBallot_sub_boxTail_le_harperScheduledCentralBandBarrier
  obtain ⟨Jvar, hvar⟩ :=
    Problem520.exists_harperScheduledCentralBandVarianceVector_quarter_half
  refine ⟨max 8 (max Jmain Jvar), ?_⟩
  intro d start hstart n hn y hy t htLower htUpper hbudget
  have hstart8 : 8 <= start := by omega
  have hstartMain : Jmain + d <= start := by omega
  have hstartVar : Jvar + d <= start := by omega
  let Q : Measure (Fin n -> Real) := Measure.pi (fun i : Fin n =>
    Problem520.harperGaussianBlockLaw y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t)
  let P : Measure (Fin n -> Real) := Measure.pi (fun i : Fin n =>
    Problem520.harperCenteredLinearBlockLaw y
      (Problem520.harperScheduledPrimeBlock y
        (start + (i : Nat))) t t)
  let box := Problem520.harperCoordinateBox
    (Problem520.harperScheduledModerateRadius start n)
  let barrier := Problem520.harperPartialSumBarrierSet
    (harperScheduledAutomaticLowerBarrier start n)
    (harperScheduledAutomaticUpperBarrier start n)
  let ballotMass := Real.exp (-2) / Real.sqrt (n : Real)
  have hvarianceVector := hvar d start hstartVar n y hy t htLower htUpper
    (fun _i : Fin n => t) (by intro i; simp)
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
  have hboxBudget : Q.real boxᶜ <= (1 / 2 : Real) * ballotMass :=
    hbox.trans (by simpa only [ballotMass] using hbudget)
  have htransfer : (3 / 4 : Real) * (ballotMass - Q.real boxᶜ) <=
      P.real barrier := by
    simpa only [Q, P, box, barrier, ballotMass] using
      hmain d start hstartMain n hn y hy t htLower htUpper
  have hremaining : (1 / 2 : Real) * ballotMass <= ballotMass - Q.real boxᶜ := by
    linarith
  calc
    (3 / 8 : Real) * ballotMass =
        (3 / 4 : Real) * ((1 / 2 : Real) * ballotMass) := by ring
    _ <= (3 / 4 : Real) * (ballotMass - Q.real boxᶜ) := by gcongr
    _ <= P.real barrier := htransfer

/-! ## Literal tilted-cube ballot event -/

/-- The finite-prime event whose centered scheduled block path stays between
the automatic lower barrier and the flat contracted upper barrier. -/
def harperCentralLowerBallotCubeEvent
    (y start n : Nat) (t : Real) : Set (Problem520.HarperPrimeCube y) :=
  (Problem520.harperScheduledCenteredBlockVectorVarying
      y start n t (fun _i : Fin n => t)) ⁻¹'
    Problem520.harperPartialSumBarrierSet
      (harperScheduledAutomaticLowerBarrier start n)
      (harperScheduledAutomaticUpperBarrier start n)

theorem measurableSet_harperCentralLowerBallotCubeEvent
    (y start n : Nat) (t : Real) :
    MeasurableSet (harperCentralLowerBallotCubeEvent y start n t) := by
  exact (Set.toFinite
    (harperCentralLowerBallotCubeEvent y start n t)).measurableSet

/-- At a fixed sign world, one centered prime coordinate depends continuously
on the diagonal tilt/height parameter. -/
theorem continuous_harperCenteredLinearPrimeIncrement_diagonal
    (p : Nat) (b : Bool) :
    Continuous (fun t : Real =>
      Problem520.harperCenteredLinearPrimeIncrement p t t b) := by
  unfold Problem520.harperCenteredLinearPrimeIncrement
    Problem520.harperLinearPrimeIncrement Problem520.harperTiltBias
  fun_prop

/-- The same diagonal continuity for an arbitrary finite prime block. -/
theorem continuous_harperCenteredLinearPrimeBlockSum_diagonal
    (y : Nat) (S : Finset (Problem520.HarperPrimeIndex y))
    (eta : Problem520.HarperPrimeCube y) :
    Continuous (fun t : Real =>
      Problem520.harperCenteredLinearPrimeBlockSum y S t t eta) := by
  unfold Problem520.harperCenteredLinearPrimeBlockSum
  exact continuous_finset_sum _ fun p _hp =>
    continuous_harperCenteredLinearPrimeIncrement_diagonal p.1 (eta p)

/-- Every scheduled diagonal partial sum is a continuous function of height. -/
theorem continuous_harperScheduledDiagonalPartialSum
    (y start n : Nat) (eta : Problem520.HarperPrimeCube y) (k : Fin n) :
    Continuous (fun t : Real =>
      Problem520.harperPathPartialSum
        (Problem520.harperScheduledCenteredBlockVectorVarying
          y start n t (fun _i : Fin n => t) eta) k) := by
  unfold Problem520.harperPathPartialSum
    Problem520.harperScheduledCenteredBlockVectorVarying
  exact continuous_finset_sum _ fun i _hi =>
    continuous_harperCenteredLinearPrimeBlockSum_diagonal y
      (Problem520.harperScheduledPrimeBlock y (start + (i : Nat))) eta

/-- Heights for which one fixed finite sign world satisfies the ballot. -/
def harperCentralLowerBallotHeightSection
    (y start n : Nat) (eta : Problem520.HarperPrimeCube y) : Set Real :=
  {t | eta ∈ harperCentralLowerBallotCubeEvent y start n t}

theorem measurableSet_harperCentralLowerBallotHeightSection
    (y start n : Nat) (eta : Problem520.HarperPrimeCube y) :
    MeasurableSet (harperCentralLowerBallotHeightSection y start n eta) := by
  let path : Real -> Fin n -> Real := fun t =>
    Problem520.harperScheduledCenteredBlockVectorVarying
      y start n t (fun _i : Fin n => t) eta
  have hsum (k : Fin n) : Measurable
      (fun t : Real => Problem520.harperPathPartialSum (path t) k) := by
    exact (continuous_harperScheduledDiagonalPartialSum
      y start n eta k).measurable
  rw [show harperCentralLowerBallotHeightSection y start n eta =
      ⋂ k : Fin n, {t : Real |
        harperScheduledAutomaticLowerBarrier start n k <=
            Problem520.harperPathPartialSum (path t) k ∧
          Problem520.harperPathPartialSum (path t) k <=
            harperScheduledAutomaticUpperBarrier start n k} by
    ext t
    simp only [harperCentralLowerBallotHeightSection,
      harperCentralLowerBallotCubeEvent,
      Problem520.mem_harperPartialSumBarrierSet, Set.mem_setOf_eq,
      Set.mem_iInter, Set.mem_preimage, path]]
  exact MeasurableSet.iInter fun k =>
    (measurableSet_le measurable_const (hsum k)).inter
      (measurableSet_le (hsum k) measurable_const)

/-- Joint height/sign graph corresponding to the literal finite-cube ballot
sections. -/
def harperCentralLowerBallotGraph
    (y start n : Nat) : Set (Real × Problem520.Omega) :=
  {w | Problem520.harperPrimeRestriction y w.2 ∈
    harperCentralLowerBallotCubeEvent y start n w.1}

theorem measurableSet_harperCentralLowerBallotGraph
    (y start n : Nat) :
    MeasurableSet (harperCentralLowerBallotGraph y start n) := by
  have heq : harperCentralLowerBallotGraph y start n =
      ⋃ eta : Problem520.HarperPrimeCube y,
        harperCentralLowerBallotHeightSection y start n eta ×ˢ
          ((Problem520.harperPrimeRestriction y) ⁻¹' {eta}) := by
    ext w
    constructor
    · intro hw
      change Problem520.harperPrimeRestriction y w.2 ∈
        harperCentralLowerBallotCubeEvent y start n w.1 at hw
      refine Set.mem_iUnion.2 ⟨Problem520.harperPrimeRestriction y w.2, ?_⟩
      change w.1 ∈ harperCentralLowerBallotHeightSection y start n
          (Problem520.harperPrimeRestriction y w.2) ∧
        Problem520.harperPrimeRestriction y w.2 =
          Problem520.harperPrimeRestriction y w.2
      exact ⟨hw, rfl⟩
    · rintro hw
      obtain ⟨eta, heta⟩ := Set.mem_iUnion.1 hw
      change w.1 ∈ harperCentralLowerBallotHeightSection y start n eta ∧
        Problem520.harperPrimeRestriction y w.2 = eta at heta
      change Problem520.harperPrimeRestriction y w.2 ∈
        harperCentralLowerBallotCubeEvent y start n w.1
      rw [heta.2]
      exact heta.1
  rw [heq]
  exact MeasurableSet.iUnion fun eta =>
    (measurableSet_harperCentralLowerBallotHeightSection
      y start n eta).prod
        ((measurableSet_singleton eta).preimage
          (Problem520.measurable_harperPrimeRestriction y))

theorem mem_harperCentralLowerBallotGraph_iff
    (y start n : Nat) (t : Real) (omega : Problem520.Omega) :
    (t, omega) ∈ harperCentralLowerBallotGraph y start n ↔
      Problem520.harperPrimeRestriction y omega ∈
        harperCentralLowerBallotCubeEvent y start n t := by
  rfl

/-- The one-height ballot lower bound in the literal finite tilted cube.  This
is the form consumed by the first-moment restricted-energy identity. -/
theorem
    exists_three_eighths_mul_exp_neg_two_div_sqrt_le_harperTiltedCubeLaw_centralLowerBallotEvent :
    ∃ J : Nat, ∀ d start : Nat, J + d <= start -> ∀ n : Nat, 0 < n ->
      ∀ y : Nat, Problem520.harperBlockEndpoint (start + n) <= y ->
        ∀ t : Real,
          (1 / 2 : Real) ^ (d + 1) < |t| ->
          |t| <= (1 / 2 : Real) ^ d ->
          64 * (1 / 2 : Real) ^ start <=
              (1 / 2 : Real) *
                (Real.exp (-2) / Real.sqrt (n : Real)) ->
            (3 / 8 : Real) *
                (Real.exp (-2) / Real.sqrt (n : Real)) <=
              (Problem520.harperTiltedCubeLaw y t).real
                (harperCentralLowerBallotCubeEvent y start n t) := by
  obtain ⟨J, hJ⟩ :=
    exists_three_eighths_mul_exp_neg_two_div_sqrt_le_harperScheduledCentralBandBarrier
  refine ⟨J, ?_⟩
  intro d start hstart n hn y hy t htLower htUpper hbudget
  have hproduct := hJ d start hstart n hn y hy t htLower htUpper hbudget
  unfold harperCentralLowerBallotCubeEvent
  rw [Problem520.harperTiltedCubeLaw_real_preimage_centeredBlockVectorVarying_eq_pi
    y start n t (fun _i : Fin n => t)
    (Problem520.harperPartialSumBarrierSet
      (harperScheduledAutomaticLowerBarrier start n)
      (harperScheduledAutomaticUpperBarrier start n))
    (Problem520.measurableSet_harperPartialSumBarrierSet
      (harperScheduledAutomaticLowerBarrier start n)
      (harperScheduledAutomaticUpperBarrier start n))]
  exact hproduct

/-! ## Critical-scale schedule -/

/-- A quarter of the real log-log scale, rounded down.  Starting at this same
index leaves room for a path of the same length and makes the box error
exponentially smaller than the ballot mass. -/
noncomputable def harper1144LowerBallotPathLength (y : Nat) : Nat :=
  Nat.floor ((1 + Problem520.logLogNat y) / 4)

/-- A scheduled endpoint gives a concrete lower bound for the real log-log
scale.  The intentionally loose factor `1/2` avoids all numerical delicacy
around `log 2`. -/
theorem half_index_le_logLogNat_of_harperBlockEndpoint_le
    {B y : Nat} (hy : Problem520.harperBlockEndpoint B <= y) :
    (B : Real) / 2 <= Problem520.logLogNat y := by
  have hlogTwoHalf : (1 / 2 : Real) <= Real.log 2 :=
    (by norm_num : (1 / 2 : Real) <= 0.6931471803).trans
      Real.log_two_gt_d9.le
  have hendpointPos : (0 : Real) < Problem520.harperBlockEndpoint B := by
    exact_mod_cast Problem520.harperBlockEndpoint_pos B
  have hyPos : (0 : Real) < y := hendpointPos.trans_le (by exact_mod_cast hy)
  have hlogMono :
      Real.log (Problem520.harperBlockEndpoint B : Real) <=
        Real.log (y : Real) :=
    Real.log_le_log hendpointPos (by exact_mod_cast hy)
  have hinside : (2 : Real) ^ B <=
      Real.log (Problem520.harperBlockEndpoint B : Real) := by
    rw [Problem520.log_harperBlockEndpoint_eq_sixteen_mul_two_pow]
    push_cast
    have hpow : 0 <= (2 : Real) ^ B := by positivity
    nlinarith
  have hlogEndpointPos : 0 <
      Real.log (Problem520.harperBlockEndpoint B : Real) :=
    (by positivity : (0 : Real) < (2 : Real) ^ B).trans_le hinside
  unfold Problem520.logLogNat
  calc
    (B : Real) / 2 <= (B : Real) * Real.log 2 := by
      have hBnonneg : (0 : Real) <= B := by positivity
      nlinarith
    _ = Real.log ((2 : Real) ^ B) := by rw [Real.log_pow]
    _ <= Real.log
        (Real.log (Problem520.harperBlockEndpoint B : Real)) :=
      Real.log_le_log (by positivity) hinside
    _ <= Real.log (Real.log (y : Real)) :=
      Real.log_le_log hlogEndpointPos hlogMono

/-- Exact one-height input on the fixed vertical band.  The three displayed
arithmetic hypotheses are the entire schedule bookkeeping: the path is long
enough for the box budget, beyond the analytic comparison threshold, and its
last endpoint fits below `y`. -/
theorem exists_harper1144LowerBallotPath_tiltedProbability_ge_criticalScale :
    ∃ J : Nat, ∀ y : Nat,
      let n := harper1144LowerBallotPathLength y
      16 <= n ->
      J + 1 <= n ->
      2 * n + 4 <= Problem520.harperAvailableLogScale y ->
      ∀ t ∈ harperLowerVerticalBand,
        (3 / 8 : Real) * Real.exp (-2) * harperInitialCriticalScale y <=
          (Problem520.harperTiltedCubeLaw y t).real
            (harperCentralLowerBallotCubeEvent y n n t) := by
  obtain ⟨J, hJ⟩ :=
    exists_three_eighths_mul_exp_neg_two_div_sqrt_le_harperTiltedCubeLaw_centralLowerBallotEvent
  refine ⟨J, ?_⟩
  intro y
  dsimp only
  intro hn16 hJn hfit t ht
  let n := harper1144LowerBallotPathLength y
  have hn16' : 16 <= n := by simpa only [n] using hn16
  have hJn' : J + 1 <= n := by simpa only [n] using hJn
  have hfit' : 2 * n + 4 <= Problem520.harperAvailableLogScale y := by
    simpa only [n] using hfit
  have hyne : y ≠ 0 := by
    intro hy
    simp [hy, Problem520.harperAvailableLogScale] at hfit'
  have hendpoint : Problem520.harperBlockEndpoint (n + n) <= y := by
    apply Problem520.harperBlockEndpoint_le_of_add_four_le_available hyne
    omega
  have htBounds : (1 / 3 : Real) <= t ∧ t <= (1 / 2 : Real) := ht
  have htPositive : 0 < t := by linarith
  have htLower : (1 / 2 : Real) ^ (1 + 1) < |t| := by
    rw [abs_of_pos htPositive]
    norm_num
    linarith
  have htUpper : |t| <= (1 / 2 : Real) ^ (1 : Nat) := by
    rw [abs_of_pos htPositive]
    norm_num
    exact htBounds.2
  have hraw := hJ 1 n hJn' n (by omega) y
    (by simpa only [two_mul] using hendpoint) t htLower htUpper
    (harperGaussian_box_budget_self n hn16')
  let L : Real := 1 + Problem520.logLogNat y
  have hLpos : 0 < L := by
    exact Problem520.one_add_logLogNat_pos_of_four_le (by
      have hyLower := Problem520.harperBlockEndpoint_ge_sixteen (n + n)
      omega)
  have hnL : (n : Real) <= L := by
    have hfloor : (n : Real) <= L / 4 := by
      simpa only [n, harper1144LowerBallotPathLength, L] using
        (Nat.floor_le (div_nonneg hLpos.le (by norm_num : (0 : Real) <= 4)))
    nlinarith
  have hnpos : 0 < (n : Real) := by positivity
  have hsqrtOrder : Real.sqrt (n : Real) <= Real.sqrt L :=
    Real.sqrt_le_sqrt hnL
  have hinvSqrt : (Real.sqrt L)⁻¹ <= (Real.sqrt (n : Real))⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (Real.sqrt_pos.2 hnpos) hsqrtOrder)
  have hcritical : harperInitialCriticalScale y <=
      (Real.sqrt (n : Real))⁻¹ := by
    have hrewrite : harperInitialCriticalScale y = (Real.sqrt L)⁻¹ := by
      unfold harperInitialCriticalScale
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hLpos.le]
      congr 2
      ring
    rw [hrewrite]
    exact hinvSqrt
  have hconstant : 0 <= (3 / 8 : Real) * Real.exp (-2) := by positivity
  calc
    (3 / 8 : Real) * Real.exp (-2) * harperInitialCriticalScale y <=
        (3 / 8 : Real) * Real.exp (-2) *
          (Real.sqrt (n : Real))⁻¹ :=
      mul_le_mul_of_nonneg_left hcritical hconstant
    _ = (3 / 8 : Real) *
        (Real.exp (-2) / Real.sqrt (n : Real)) := by
      rw [div_eq_mul_inv]
      ring
    _ <= (Problem520.harperTiltedCubeLaw y t).real
        (harperCentralLowerBallotCubeEvent y n n t) := hraw

/-- The one-height half of the restricted-energy certificate, with all
schedule conditions discharged.  The event is explicit and uses a path of
length `floor ((1 + log log y) / 4)` starting at the same block index. -/
theorem exists_eventually_harper1144LowerBallot_tiltedProbability_ge_criticalScale :
    ∃ delta : Real, 0 < delta ∧ ∃ Y : Nat, ∀ y : Nat, Y <= y ->
      ∀ t ∈ harperLowerVerticalBand,
        delta * harperInitialCriticalScale y <=
          (Problem520.harperTiltedCubeLaw y t).real
            (harperCentralLowerBallotCubeEvent y
              (harper1144LowerBallotPathLength y)
              (harper1144LowerBallotPathLength y) t) := by
  obtain ⟨J, hJ⟩ :=
    exists_harper1144LowerBallotPath_tiltedProbability_ge_criticalScale
  let B : Nat := max 128 (8 * (J + 1))
  let delta : Real := (3 / 8 : Real) * Real.exp (-2)
  refine ⟨delta, by positivity, Problem520.harperBlockEndpoint B, ?_⟩
  intro y hy t ht
  let n := harper1144LowerBallotPathLength y
  let L : Real := 1 + Problem520.logLogNat y
  let A := Problem520.harperAvailableLogScale y
  have hBscale : (B : Real) / 2 <= Problem520.logLogNat y :=
    half_index_le_logLogNat_of_harperBlockEndpoint_le hy
  have hB128 : 128 <= B := le_max_left _ _
  have hBJ : 8 * (J + 1) <= B := le_max_right _ _
  have hL64 : (64 : Real) <= L := by
    dsimp only [L]
    have hB128R : (128 : Real) <= B := by exact_mod_cast hB128
    nlinarith
  have hLJ : (4 * (J + 1) : Nat) <= L := by
    have hBJR : ((8 * (J + 1) : Nat) : Real) <= B := by
      exact_mod_cast hBJ
    push_cast at hBJR ⊢
    nlinarith
  have hLpos : 0 <= L := hL64.trans' (by norm_num)
  have hn16 : 16 <= n := by
    dsimp only [n, harper1144LowerBallotPathLength]
    apply Nat.le_floor
    dsimp only [L] at hL64 ⊢
    linarith
  have hJn : J + 1 <= n := by
    dsimp only [n, harper1144LowerBallotPathLength]
    apply Nat.le_floor
    dsimp only [L] at hLJ ⊢
    push_cast at hLJ ⊢
    linarith
  have hA : B <= A := by
    exact Problem520.threshold_le_harperAvailableLogScale_of_endpoint B hy
  have hA10 : 10 <= A := by
    have : 10 <= B := hB128.trans' (by norm_num)
    exact this.trans hA
  have hlogUpper : Problem520.logLogNat y <= (A : Real) + 1 :=
    Problem520.logLogNat_le_harperAvailableLogScale_add_one (by omega)
  have hnQuarter : (n : Real) <= L / 4 := by
    dsimp only [n, harper1144LowerBallotPathLength]
    exact Nat.floor_le (div_nonneg hLpos (by norm_num))
  have hfit : 2 * n + 4 <= A := by
    have hfitReal : ((2 * n + 4 : Nat) : Real) <= (A : Real) := by
      have hA10R : (10 : Real) <= A := by exact_mod_cast hA10
      push_cast
      dsimp only [L] at hnQuarter
      nlinarith
    exact_mod_cast hfitReal
  simpa only [delta, n] using hJ y hn16 hJn hfit t ht

/-! ## Closed first moment -/

/-- The explicit jointly measurable ballot graph has the sharp first moment
required by the restricted-energy argument.  No analytic hypothesis remains
in this one-height statement. -/
theorem exists_eventually_harperCentralLowerBallotGraph_firstMoment :
    ∃ c : Real, 0 < c ∧ ∃ Y : Nat, ∀ y : Nat, Y <= y ->
      c * harperInitialCriticalScale y <=
        ∫ omega,
          harperRestrictedGraphEnergy y
            (harperCentralLowerBallotGraph y
              (harper1144LowerBallotPathLength y)
              (harper1144LowerBallotPathLength y)) omega
          ∂Problem520.μ := by
  obtain ⟨delta, hdelta, Yprob, hprob⟩ :=
    exists_eventually_harper1144LowerBallot_tiltedProbability_ge_criticalScale
  refine ⟨delta / 12, div_pos hdelta (by norm_num), max 4 Yprob, ?_⟩
  intro y hy
  have hy4 : 4 <= y := (le_max_left _ _).trans hy
  have hyProb : Yprob <= y := (le_max_right _ _).trans hy
  let n := harper1144LowerBallotPathLength y
  let G := harperCentralLowerBallotGraph y n n
  let A : Real -> Set (Problem520.HarperPrimeCube y) := fun t =>
    harperCentralLowerBallotCubeEvent y n n t
  have hG : MeasurableSet G := by
    simpa only [G] using measurableSet_harperCentralLowerBallotGraph y n n
  have hsection : ∀ t omega,
      (t, omega) ∈ G ↔ Problem520.harperPrimeRestriction y omega ∈ A t := by
    intro t omega
    rfl
  have hK : 0 <= harperInitialCriticalScale y :=
    (harperInitialCriticalScale_pos hy4).le
  have hprob' : ∀ t ∈ harperLowerVerticalBand,
      delta * harperInitialCriticalScale y <=
        (Problem520.harperTiltedCubeLaw y t).real (A t) := by
    intro t ht
    simpa only [A, n] using hprob y hyProb t ht
  have hfirst := integral_harperRestrictedGraphEnergy_lower_of_tiltedProbabilities
    (y := y) (by omega) hG A hsection hdelta.le hK hprob'
  simpa only [G, n] using hfirst

end
end Problem1144
end Erdos

#print axioms
  Erdos.Problem1144.exists_eventually_harper1144LowerBallot_tiltedProbability_ge_criticalScale
#print axioms Erdos.Problem1144.exists_eventually_harperCentralLowerBallotGraph_firstMoment
#print axioms Erdos.Problem1144.invSqrt_mul_exp_eighth_le_gaussianReal_Icc_neg_half_half
#print axioms Erdos.Problem1144.half_exp_neg_two_div_sqrt_le_gaussianReal_Icc_neg_half_half
#print axioms Erdos.Problem1144.half_exp_neg_two_div_sqrt_le_gaussianVarianceWalk_probability_fin
