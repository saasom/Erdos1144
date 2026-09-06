import Erdos.Problem1144.HarperLogBallotLower
import Erdos.Problem520.HarperMovingHeightVerticalCumulative
import Erdos.Problem520.External.Sieve.AuxResults
import Mathlib.Probability.Independence.Integration

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem1144

noncomputable section

/-!
# A finite-energy tilt producing the logarithmic ballot barrier

For variance `v_j` at coordinate `j`, translate the centered Gaussian
increment down by

`h_j = (8 / (j+1)) v_j`.

The lower variance bound makes the cumulative translation dominate the
required `2 log(k+1)` pinch.  The upper variance bound makes its
Cameron--Martin energy uniformly bounded.  These deterministic facts are the
core of a direct reduction from the logarithmic ballot to a flat ballot.
-/

/-- Smooth inverse-time coefficient used by the logarithmic tilt. -/
def harper1144GaussianLogTiltRate {n : Nat} (i : Fin n) : Real :=
  8 / ((i.val + 1 : Nat) : Real)

/-- Coordinate drift, chosen proportional to the actual variance so that
the likelihood coefficient is the smooth inverse-time rate. -/
def harper1144GaussianLogTiltIncrement {n : Nat}
    (variance : Fin n -> NNReal) (i : Fin n) : Real :=
  harper1144GaussianLogTiltRate i * (variance i : Real)

/-- Cumulative downward displacement through coordinate `k`. -/
def harper1144GaussianLogTiltCumulative {n : Nat}
    (variance : Fin n -> NNReal) (k : Fin n) : Real :=
  ∑ i ∈ Finset.Iic k, harper1144GaussianLogTiltIncrement variance i

/-- Translate an increment path down by the logarithmic drift. -/
def harper1144GaussianLogTiltDown {n : Nat}
    (variance : Fin n -> NNReal) (omega : Fin n -> Real) : Fin n -> Real :=
  fun i => omega i - harper1144GaussianLogTiltIncrement variance i

theorem measurable_harper1144GaussianLogTiltDown {n : Nat}
    (variance : Fin n -> NNReal) :
    Measurable (harper1144GaussianLogTiltDown variance) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_pi_apply i).sub measurable_const

/-- Coordinatewise translation sends the centered Gaussian product to the
product with the prescribed negative means. -/
theorem map_pi_harper1144GaussianLogTiltDown {n : Nat}
    (variance : Fin n -> NNReal) :
    Measure.map (harper1144GaussianLogTiltDown variance)
        (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))) =
      Measure.pi (fun i : Fin n =>
        gaussianReal (-harper1144GaussianLogTiltIncrement variance i)
          (variance i)) := by
  let f : (i : Fin n) -> Real -> Real := fun i x =>
    x + (-harper1144GaussianLogTiltIncrement variance i)
  have hpi := Measure.pi_map_pi
    (μ := fun i : Fin n => gaussianReal 0 (variance i))
    (f := f) (fun i => (by fun_prop))
  calc
    Measure.map (harper1144GaussianLogTiltDown variance)
        (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))) =
        Measure.pi (fun i : Fin n =>
          Measure.map (f i) (gaussianReal 0 (variance i))) := by
      simpa only [harper1144GaussianLogTiltDown, f, sub_eq_add_neg] using hpi
    _ = Measure.pi (fun i : Fin n =>
        gaussianReal (-harper1144GaussianLogTiltIncrement variance i)
          (variance i)) := by
      congr 1
      funext i
      simpa only [f, zero_add] using
        (gaussianReal_map_add_const
          (μ := (0 : Real)) (v := variance i)
          (-harper1144GaussianLogTiltIncrement variance i))

/-- Reindex the harmonic sum over `Fin m` as the usual interval
`{1, ..., m}`. -/
theorem sum_fin_inv_succ_eq_sum_Icc (m : Nat) :
    (∑ i : Fin m, ((((i.val + 1 : Nat) : Real))⁻¹)) =
      ∑ j ∈ Finset.Icc 1 m, ((j : Real)⁻¹) := by
  rw [show (∑ i : Fin m, (((i.val + 1 : Nat) : Real)⁻¹)) =
      ∑ i ∈ Finset.range m, (((i + 1 : Nat) : Real)⁻¹) by
    simpa using (Fin.sum_univ_eq_sum_range
      (fun i : Nat => (((i + 1 : Nat) : Real)⁻¹)) m)]
  have hset : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset]
  symm
  simpa [add_comm] using (Finset.sum_Ico_eq_sum_range
    (fun j : Nat => ((j : Real)⁻¹)) 1 (m + 1))

/-- Every prefix harmonic sum dominates the logarithm of the next time. -/
theorem log_nat_succ_succ_le_sum_Iic_inv_succ {n : Nat} (k : Fin n) :
    Real.log ((k.val + 2 : Nat) : Real) <=
      ∑ i ∈ Finset.Iic k, ((((i.val + 1 : Nat) : Real))⁻¹) := by
  rw [Problem520.sum_Iic_eq_sum_fin_prefix
    (f := fun i : Nat => (((i + 1 : Nat) : Real)⁻¹))]
  rw [sum_fin_inv_succ_eq_sum_Icc (k.val + 1)]
  simpa only [Nat.add_assoc] using
    (Aux.log_add_one_le_sum_inv (k.val + 1))

/-- A single drift increment is at least twice the corresponding harmonic
increment when every variance is at least `1/4`. -/
theorem two_mul_inv_succ_le_harper1144GaussianLogTiltIncrement
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i) (i : Fin n) :
    2 * ((((i.val + 1 : Nat) : Real))⁻¹) <=
      harper1144GaussianLogTiltIncrement variance i := by
  have hden : (0 : Real) < ((i.val + 1 : Nat) : Real) := by positivity
  have hinv : 0 <= ((((i.val + 1 : Nat) : Real))⁻¹) :=
    inv_nonneg.mpr hden.le
  have hv : (1 / 4 : Real) <= (variance i : Real) := by
    exact_mod_cast hlower i
  unfold harper1144GaussianLogTiltIncrement harper1144GaussianLogTiltRate
  rw [div_eq_mul_inv]
  nlinarith

/-- The cumulative tilt dominates the desired logarithmic pinch, uniformly
over all variance vectors in the permitted window. -/
theorem two_mul_log_succ_succ_le_harper1144GaussianLogTiltCumulative
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i) (k : Fin n) :
    2 * Real.log ((k.val + 2 : Nat) : Real) <=
      harper1144GaussianLogTiltCumulative variance k := by
  have hsum :
      ∑ i ∈ Finset.Iic k, 2 * ((((i.val + 1 : Nat) : Real))⁻¹) <=
        ∑ i ∈ Finset.Iic k,
          harper1144GaussianLogTiltIncrement variance i := by
    exact Finset.sum_le_sum fun i _hi =>
      two_mul_inv_succ_le_harper1144GaussianLogTiltIncrement
        variance hlower i
  have hlog := log_nat_succ_succ_le_sum_Iic_inv_succ k
  unfold harper1144GaussianLogTiltCumulative
  rw [← Finset.mul_sum] at hsum
  linarith

/-- Partial sums commute exactly with the deterministic translation. -/
theorem harperPathPartialSum_harper1144GaussianLogTiltDown
    {n : Nat} (variance : Fin n -> NNReal)
    (omega : Fin n -> Real) (k : Fin n) :
    Problem520.harperPathPartialSum
        (harper1144GaussianLogTiltDown variance omega) k =
      Problem520.harperPathPartialSum omega k -
        harper1144GaussianLogTiltCumulative variance k := by
  unfold Problem520.harperPathPartialSum harper1144GaussianLogTiltDown
    harper1144GaussianLogTiltCumulative
  rw [Finset.sum_sub_distrib]

/-- The one-sided elapsed-prefix logarithmic upper event. -/
def harper1144GaussianLogUpperEvent (n : Nat) : Set (Fin n -> Real) :=
  Problem520.gaussianWalkTimeBarrierSet n 0
    (fun k => (1 / 2 : Real) -
      2 * Real.log ((k.val + 1 : Nat) : Real))

theorem measurableSet_harper1144GaussianLogUpperEvent (n : Nat) :
    MeasurableSet (harper1144GaussianLogUpperEvent n) := by
  exact Problem520.measurableSet_gaussianWalkTimeBarrierSet n 0 _

/-- Translating every flat-surviving path down by the finite-energy drift
puts it inside the desired logarithmic upper barrier. -/
theorem harper1144GaussianLogTiltDown_mem_upper_of_flat
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (omega : Fin n -> Real)
    (homega : omega ∈ Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real)) :
    harper1144GaussianLogTiltDown variance omega ∈
      harper1144GaussianLogUpperEvent n := by
  unfold harper1144GaussianLogUpperEvent
  apply Problem520.gaussianWalkTimeBarrierSurvives_of_partialSum_le
  intro k
  have hflat := harperPathPartialSum_le_of_gaussianWalkSurvives
    n (1 / 2 : Real) omega homega k
  have hshift :=
    two_mul_log_succ_succ_le_harper1144GaussianLogTiltCumulative
      variance hlower k
  have hnat : (0 : Real) < ((k.val + 1 : Nat) : Real) := by positivity
  have harg : ((k.val + 1 : Nat) : Real) <=
      ((k.val + 2 : Nat) : Real) := by norm_num
  have hlog : Real.log ((k.val + 1 : Nat) : Real) <=
      Real.log ((k.val + 2 : Nat) : Real) :=
    Real.log_le_log hnat harg
  rw [zero_add,
    harperPathPartialSum_harper1144GaussianLogTiltDown]
  linarith

/-- Pointwise form of the same flat-to-logarithmic upper-barrier
implication. -/
theorem harperPathPartialSum_logTiltDown_le_of_flat
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i)
    (omega : Fin n -> Real)
    (homega : omega ∈ Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real))
    (k : Fin n) :
    Problem520.harperPathPartialSum
        (harper1144GaussianLogTiltDown variance omega) k <=
      (1 / 2 : Real) -
        2 * Real.log ((k.val + 1 : Nat) : Real) := by
  have hflat := harperPathPartialSum_le_of_gaussianWalkSurvives
    n (1 / 2 : Real) omega homega k
  have hshift :=
    two_mul_log_succ_succ_le_harper1144GaussianLogTiltCumulative
      variance hlower k
  have hnat : (0 : Real) < ((k.val + 1 : Nat) : Real) := by positivity
  have harg : ((k.val + 1 : Nat) : Real) <=
      ((k.val + 2 : Nat) : Real) := by norm_num
  have hlog : Real.log ((k.val + 1 : Nat) : Real) <=
      Real.log ((k.val + 2 : Nat) : Real) :=
    Real.log_le_log hnat harg
  rw [harperPathPartialSum_harper1144GaussianLogTiltDown]
  linarith

/-- The total Cameron--Martin energy of the logarithmic tilt is bounded by
an absolute constant, independently of the path length. -/
theorem sum_harper1144GaussianLogTiltRate_sq_mul_variance_le
    {n : Nat} (variance : Fin n -> NNReal)
    (hupper : ∀ i, variance i <= (1 / 2 : NNReal)) :
    (∑ i : Fin n,
        harper1144GaussianLogTiltRate i ^ 2 * (variance i : Real)) <= 64 := by
  have hterm : ∀ i : Fin n,
      harper1144GaussianLogTiltRate i ^ 2 * (variance i : Real) <=
        32 * (((((i.val + 1 : Nat) : Real) ^ 2))⁻¹) := by
    intro i
    have hden : (0 : Real) < ((i.val + 1 : Nat) : Real) := by positivity
    have hv : (variance i : Real) <= (1 / 2 : Real) := by
      exact_mod_cast hupper i
    have hinvSq : 0 <= (((((i.val + 1 : Nat) : Real) ^ 2))⁻¹) := by
      positivity
    unfold harper1144GaussianLogTiltRate
    rw [div_pow, show (8 : Real) ^ 2 = 64 by norm_num]
    rw [div_eq_mul_inv]
    nlinarith
  calc
    (∑ i : Fin n,
        harper1144GaussianLogTiltRate i ^ 2 * (variance i : Real)) <=
        ∑ i : Fin n,
          32 * (((((i.val + 1 : Nat) : Real) ^ 2))⁻¹) :=
      Finset.sum_le_sum fun i _hi => hterm i
    _ = 32 *
        (∑ i ∈ Finset.range n,
          (((((i + 1 : Nat) : Real) ^ 2))⁻¹)) := by
      rw [← Finset.mul_sum]
      rw [show (∑ i : Fin n,
          (((((i.val + 1 : Nat) : Real) ^ 2))⁻¹)) =
          ∑ i ∈ Finset.range n,
            (((((i + 1 : Nat) : Real) ^ 2))⁻¹) by
        simpa using (Fin.sum_univ_eq_sum_range
          (fun i : Nat => (((((i + 1 : Nat) : Real) ^ 2))⁻¹)) n)]
    _ <= 32 * 2 := by
      exact mul_le_mul_of_nonneg_left
        (Problem520.sum_range_inv_nat_succ_sq_le_two n) (by norm_num)
    _ = 64 := by norm_num

/-! ## Exact finite-product likelihood -/

/-- A finite product of coordinatewise density changes is the corresponding
density change of the product measure. -/
theorem pi_withDensity_fintype_prod
    {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ ν : ι -> Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)]
    (f : ι -> α -> ENNReal) (hf : ∀ i, Measurable (f i))
    (hν : ∀ i, ν i = (μ i).withDensity (f i)) :
    Measure.pi ν = (Measure.pi μ).withDensity
      (fun omega => ∏ i, f i (omega i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hs)]
  let X : ι -> (ι -> α) -> ENNReal := fun i omega =>
    (s i).indicator (f i) (omega i)
  have hXmeas : ∀ i, Measurable (X i) := by
    intro i
    exact ((hf i).indicator (hs i)).comp (measurable_pi_apply i)
  have hXindep : iIndepFun X (Measure.pi μ) := by
    exact iIndepFun_pi
      (X := fun i x => (s i).indicator (f i) x)
      (fun i => ((hf i).indicator (hs i)).aemeasurable)
  have hfactor := lintegral_prod_eq_prod_lintegral_of_indepFun
    (Finset.univ : Finset ι) X hXindep hXmeas
  rw [show (fun omega : ι -> α =>
      (Set.univ.pi s).indicator (fun omega => ∏ i, f i (omega i)) omega) =
      (fun omega => ∏ i, X i omega) by
    funext omega
    by_cases homega : omega ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem homega]
      apply Finset.prod_congr rfl
      intro i _hi
      simp only [X, Set.indicator_of_mem (homega i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem homega]
      have : ∃ i, omega i ∉ s i := by
        simpa only [Set.mem_pi, Set.mem_univ, forall_true_left, not_forall]
          using homega
      obtain ⟨i, hi⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]
      change (s i).indicator (f i) (omega i) = 0
      exact Set.indicator_of_notMem hi (f i)]
  rw [hfactor]
  apply Finset.prod_congr rfl
  intro i _hi
  have hmp := measurePreserving_eval μ i
  rw [show (∫⁻ omega : ι -> α, X i omega ∂Measure.pi μ) =
      ∫⁻ x : α, (s i).indicator (f i) x ∂μ i by
    simpa only [X, Function.comp_apply] using
      hmp.lintegral_comp ((hf i).indicator (hs i))]
  rw [lintegral_indicator (hs i)]
  rw [← withDensity_apply (f i) (hs i)]
  rw [← hν i]

/-- Real-valued density identity for shifting a centered Gaussian by
`-lambda * variance`. -/
theorem gaussianPDFReal_neg_variance_tilt
    (v : NNReal) (hv : v ≠ 0) (lambda x : Real) :
    gaussianPDFReal 0 v x *
        Real.exp (-lambda * x -
          (1 / 2 : Real) * lambda ^ 2 * (v : Real)) =
      gaussianPDFReal (-(lambda * (v : Real))) v x := by
  have hvR : (v : Real) ≠ 0 := by exact_mod_cast hv
  unfold gaussianPDFReal
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  apply Real.exp_injective
  field_simp
  ring

/-- `ENNReal` form of the one-coordinate Gaussian likelihood identity. -/
theorem gaussianPDF_neg_variance_tilt
    (v : NNReal) (hv : v ≠ 0) (lambda x : Real) :
    gaussianPDF 0 v x *
        ENNReal.ofReal
          (Real.exp (-lambda * x -
            (1 / 2 : Real) * lambda ^ 2 * (v : Real))) =
      gaussianPDF (-(lambda * (v : Real))) v x := by
  rw [gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)]
  congr 1
  exact gaussianPDFReal_neg_variance_tilt v hv lambda x

/-- Exact one-coordinate change of measure from a centered Gaussian to the
negative-mean Gaussian used by the logarithmic tilt. -/
theorem gaussianReal_neg_variance_tilt_withDensity
    (v : NNReal) (hv : v ≠ 0) (lambda : Real) :
    gaussianReal (-(lambda * (v : Real))) v =
      (gaussianReal 0 v).withDensity (fun x =>
        ENNReal.ofReal
          (Real.exp (-lambda * x -
            (1 / 2 : Real) * lambda ^ 2 * (v : Real)))) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv]
  rw [← withDensity_mul volume (measurable_gaussianPDF 0 v) (by fun_prop)]
  congr 1
  funext x
  simpa only [Pi.mul_apply] using
    (gaussianPDF_neg_variance_tilt v hv lambda x).symm

/-- Coordinate likelihood of the negative logarithmic tilt relative to the
centered Gaussian law. -/
def harper1144GaussianLogTiltDensity {n : Nat}
    (variance : Fin n -> NNReal) (i : Fin n) (x : Real) : ENNReal :=
  ENNReal.ofReal (Real.exp
    (-harper1144GaussianLogTiltRate i * x -
      (1 / 2 : Real) * harper1144GaussianLogTiltRate i ^ 2 *
        (variance i : Real)))

theorem measurable_harper1144GaussianLogTiltDensity {n : Nat}
    (variance : Fin n -> NNReal) (i : Fin n) :
    Measurable (harper1144GaussianLogTiltDensity variance i) := by
  unfold harper1144GaussianLogTiltDensity
  fun_prop

/-- Linear part of the logarithmic-tilt likelihood. -/
def harper1144GaussianLogTiltLinear {n : Nat}
    (omega : Fin n -> Real) : Real :=
  ∑ i, harper1144GaussianLogTiltRate i * omega i

/-- Quadratic energy in the logarithmic-tilt likelihood. -/
def harper1144GaussianLogTiltEnergy {n : Nat}
    (variance : Fin n -> NNReal) : Real :=
  ∑ i, harper1144GaussianLogTiltRate i ^ 2 * (variance i : Real)

/-- The product likelihood is a single exponential with the expected linear
and quadratic terms. -/
theorem prod_harper1144GaussianLogTiltDensity_eq_exp
    {n : Nat} (variance : Fin n -> NNReal) (omega : Fin n -> Real) :
    (∏ i, harper1144GaussianLogTiltDensity variance i (omega i)) =
      ENNReal.ofReal (Real.exp
        (-harper1144GaussianLogTiltLinear omega -
          (1 / 2 : Real) * harper1144GaussianLogTiltEnergy variance)) := by
  unfold harper1144GaussianLogTiltDensity
    harper1144GaussianLogTiltLinear harper1144GaussianLogTiltEnergy
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun i _hi => (Real.exp_pos _).le)]
  rw [← Real.exp_sum]
  congr 2
  rw [Finset.sum_sub_distrib]
  rw [show (∑ x : Fin n,
      -harper1144GaussianLogTiltRate x * omega x) =
      -(∑ x : Fin n, harper1144GaussianLogTiltRate x * omega x) by
    calc
      (∑ x : Fin n,
          -harper1144GaussianLogTiltRate x * omega x) =
          ∑ x : Fin n,
            -(harper1144GaussianLogTiltRate x * omega x) := by
        apply Finset.sum_congr rfl
        intro x _hx
        ring
      _ = -(∑ x : Fin n,
          harper1144GaussianLogTiltRate x * omega x) := by
        simpa using
          (Finset.sum_neg_distrib
            (s := Finset.univ)
            (fun x : Fin n =>
              harper1144GaussianLogTiltRate x * omega x))]
  rw [show (∑ x : Fin n,
      (1 / 2 : Real) * harper1144GaussianLogTiltRate x ^ 2 *
        (variance x : Real)) =
      (1 / 2 : Real) * ∑ x : Fin n,
        harper1144GaussianLogTiltRate x ^ 2 * (variance x : Real) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring]

/-- Exact Cameron--Martin formula for the entire finite Gaussian path. -/
theorem pi_gaussianReal_neg_logTilt_eq_withDensity
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i) :
    Measure.pi (fun i : Fin n =>
        gaussianReal (-harper1144GaussianLogTiltIncrement variance i)
          (variance i)) =
      (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).withDensity
        (fun omega => ∏ i,
          harper1144GaussianLogTiltDensity variance i (omega i)) := by
  apply pi_withDensity_fintype_prod
  · exact fun i => measurable_harper1144GaussianLogTiltDensity variance i
  · intro i
    have hvi : variance i ≠ 0 := by
      intro hzero
      have h := hlower i
      simp [hzero] at h
    simpa only [harper1144GaussianLogTiltIncrement,
      harper1144GaussianLogTiltDensity] using
      gaussianReal_neg_variance_tilt_withDensity
        (variance i) hvi (harper1144GaussianLogTiltRate i)

/-- Exponential-likelihood form of the finite-path Cameron--Martin formula. -/
theorem pi_gaussianReal_neg_logTilt_eq_withDensity_exp
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i) :
    Measure.pi (fun i : Fin n =>
        gaussianReal (-harper1144GaussianLogTiltIncrement variance i)
          (variance i)) =
      (Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))).withDensity
        (fun omega => ENNReal.ofReal (Real.exp
          (-harper1144GaussianLogTiltLinear omega -
            (1 / 2 : Real) * harper1144GaussianLogTiltEnergy variance))) := by
  rw [pi_gaussianReal_neg_logTilt_eq_withDensity variance hlower]
  congr 1
  funext omega
  exact prod_harper1144GaussianLogTiltDensity_eq_exp variance omega

/-! ## Reduction to a flat ballot with one likelihood fence -/

theorem measurable_harper1144GaussianLogTiltLinear {n : Nat} :
    Measurable (@harper1144GaussianLogTiltLinear n) := by
  unfold harper1144GaussianLogTiltLinear
  fun_prop

theorem harper1144GaussianLogTiltEnergy_nonneg {n : Nat}
    (variance : Fin n -> NNReal) :
    0 <= harper1144GaussianLogTiltEnergy variance := by
  unfold harper1144GaussianLogTiltEnergy
  exact Finset.sum_nonneg fun i _hi => by positivity

/-- Target logarithmic corridor with the one extra likelihood fence needed
for a pointwise Cameron--Martin comparison. -/
def harper1144GaussianLogTiltTargetEvent {n : Nat}
    (variance : Fin n -> NNReal) (B : Real) : Set (Fin n -> Real) :=
  harper1144GaussianLogBallotCoreEvent n ∩
    {omega | -B <= harper1144GaussianLogTiltLinear omega +
      (1 / 2 : Real) * harper1144GaussianLogTiltEnergy variance}

theorem measurableSet_harper1144GaussianLogTiltTargetEvent {n : Nat}
    (variance : Fin n -> NNReal) (B : Real) :
    MeasurableSet (harper1144GaussianLogTiltTargetEvent variance B) := by
  exact (measurableSet_harper1144GaussianLogBallotCoreEvent n).inter
    (measurableSet_le measurable_const
      (measurable_harper1144GaussianLogTiltLinear.add measurable_const))

/-- On the likelihood-fenced target, the negative-shift density is at most
`exp B`. -/
theorem harper1144GaussianLogTiltDensity_exp_le_of_mem_target
    {n : Nat} (variance : Fin n -> NNReal) (B : Real)
    {omega : Fin n -> Real}
    (homega : omega ∈ harper1144GaussianLogTiltTargetEvent variance B) :
    ENNReal.ofReal (Real.exp
        (-harper1144GaussianLogTiltLinear omega -
          (1 / 2 : Real) * harper1144GaussianLogTiltEnergy variance)) <=
      ENNReal.ofReal (Real.exp B) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hlinear := homega.2
  change -B <= harper1144GaussianLogTiltLinear omega +
    (1 / 2 : Real) * harper1144GaussianLogTiltEnergy variance at hlinear
  linarith

/-- A density bounded by `C` on a measurable event charges that event by at
most `C` times the original measure. -/
theorem withDensity_apply_le_const_mul
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A : Set α) (hA : MeasurableSet A) (f : α -> ENNReal) (C : ENNReal)
    (hf : ∀ x ∈ A, f x <= C) :
    μ.withDensity f A <= C * μ A := by
  rw [withDensity_apply f hA]
  calc
    (∫⁻ x in A, f x ∂μ) <= ∫⁻ _x in A, C ∂μ := by
      exact setLIntegral_mono' hA hf
    _ = C * μ A := setLIntegral_const A C

/-- The shifted Gaussian law of the fenced logarithmic target is at most
`exp B` times its centered Gaussian probability. -/
theorem pi_gaussianReal_neg_logTilt_target_le
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i) (B : Real) :
    Measure.pi (fun i : Fin n =>
        gaussianReal (-harper1144GaussianLogTiltIncrement variance i)
          (variance i))
        (harper1144GaussianLogTiltTargetEvent variance B) <=
      ENNReal.ofReal (Real.exp B) *
        Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
          (harper1144GaussianLogTiltTargetEvent variance B) := by
  rw [pi_gaussianReal_neg_logTilt_eq_withDensity_exp variance hlower]
  exact withDensity_apply_le_const_mul _ _
    (measurableSet_harper1144GaussianLogTiltTargetEvent variance B) _ _
    (fun omega homega =>
      harper1144GaussianLogTiltDensity_exp_le_of_mem_target
        variance B homega)

/-- The residual source event: a flat-surviving centered path whose downward
translate obeys both the final lower guard and the likelihood fence.  The
translated upper logarithmic barrier is automatic from flat survival. -/
def harper1144GaussianLogTiltSourceEvent {n : Nat}
    (variance : Fin n -> NNReal) (B : Real) : Set (Fin n -> Real) :=
  Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real) ∩
    harper1144GaussianLogTiltDown variance ⁻¹'
      harper1144GaussianLogTiltTargetEvent variance B

/-- The source event written without a hidden preimage.  It is simply a flat
ballot, the very loose lower guard after translation, and the single scalar
likelihood fence. -/
def harper1144GaussianLogTiltCertificateEvent {n : Nat}
    (variance : Fin n -> NNReal) (B : Real) : Set (Fin n -> Real) :=
  {omega |
    omega ∈ Problem520.gaussianWalkSurvivalSet n (1 / 2 : Real) ∧
    (∀ k : Fin n,
      -32 * ((k.val + 1 : Nat) : Real) <=
        Problem520.harperPathPartialSum
          (harper1144GaussianLogTiltDown variance omega) k) ∧
    -B <= harper1144GaussianLogTiltLinear
        (harper1144GaussianLogTiltDown variance omega) +
      (1 / 2 : Real) * harper1144GaussianLogTiltEnergy variance}

theorem measurableSet_harper1144GaussianLogTiltCertificateEvent {n : Nat}
    (variance : Fin n -> NNReal) (B : Real) :
    MeasurableSet (harper1144GaussianLogTiltCertificateEvent variance B) := by
  unfold harper1144GaussianLogTiltCertificateEvent
  have hflat := Problem520.measurableSet_gaussianWalkSurvivalSet n
    (by norm_num : (0 : Real) <= 1 / 2)
  have hlower : MeasurableSet {omega : Fin n -> Real |
      ∀ k : Fin n,
        -32 * ((k.val + 1 : Nat) : Real) <=
          Problem520.harperPathPartialSum
            (harper1144GaussianLogTiltDown variance omega) k} := by
    rw [show {omega : Fin n -> Real |
        ∀ k : Fin n,
          -32 * ((k.val + 1 : Nat) : Real) <=
            Problem520.harperPathPartialSum
              (harper1144GaussianLogTiltDown variance omega) k} =
        ⋂ k : Fin n, {omega : Fin n -> Real |
          -32 * ((k.val + 1 : Nat) : Real) <=
            Problem520.harperPathPartialSum
              (harper1144GaussianLogTiltDown variance omega) k} by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_iInter]]
    apply MeasurableSet.iInter
    intro k
    unfold Problem520.harperPathPartialSum
    exact measurableSet_le measurable_const
      (Finset.measurable_sum _ fun i _hi =>
        (measurable_pi_apply i).comp
          (measurable_harper1144GaussianLogTiltDown variance))
  have hlikelihood : MeasurableSet {omega : Fin n -> Real |
      -B <= harper1144GaussianLogTiltLinear
          (harper1144GaussianLogTiltDown variance omega) +
        (1 / 2 : Real) * harper1144GaussianLogTiltEnergy variance} := by
    exact measurableSet_le measurable_const
      ((measurable_harper1144GaussianLogTiltLinear.comp
        (measurable_harper1144GaussianLogTiltDown variance)).add
          measurable_const)
  simpa only [Set.mem_setOf_eq] using hflat.inter (hlower.inter hlikelihood)

/-- The explicit three-condition certificate is exactly strong enough for
the source event consumed by the change-of-measure reduction. -/
theorem harper1144GaussianLogTiltCertificateEvent_subset_source
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i) (B : Real) :
    harper1144GaussianLogTiltCertificateEvent variance B ⊆
      harper1144GaussianLogTiltSourceEvent variance B := by
  intro omega homega
  refine ⟨homega.1, ?_⟩
  refine ⟨?_, homega.2.2⟩
  intro k
  exact ⟨homega.2.1 k,
    harperPathPartialSum_logTiltDown_le_of_flat
      variance hlower omega homega.1 k⟩

theorem measurableSet_harper1144GaussianLogTiltSourceEvent {n : Nat}
    (variance : Fin n -> NNReal) (B : Real) :
    MeasurableSet (harper1144GaussianLogTiltSourceEvent variance B) := by
  exact (Problem520.measurableSet_gaussianWalkSurvivalSet n
      (by norm_num : (0 : Real) <= 1 / 2)).inter
    ((measurableSet_harper1144GaussianLogTiltTargetEvent variance B).preimage
      (measurable_harper1144GaussianLogTiltDown variance))

/-- Exact pushforward identity for the fenced target. -/
theorem pi_gaussianReal_neg_logTilt_target_eq_preimage
    {n : Nat} (variance : Fin n -> NNReal) (B : Real) :
    Measure.pi (fun i : Fin n =>
        gaussianReal (-harper1144GaussianLogTiltIncrement variance i)
          (variance i))
        (harper1144GaussianLogTiltTargetEvent variance B) =
      Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
        (harper1144GaussianLogTiltDown variance ⁻¹'
          harper1144GaussianLogTiltTargetEvent variance B) := by
  rw [← map_pi_harper1144GaussianLogTiltDown variance]
  exact Measure.map_apply
    (measurable_harper1144GaussianLogTiltDown variance)
    (measurableSet_harper1144GaussianLogTiltTargetEvent variance B)

/-- Complete deterministic/change-of-measure reduction.  Proving a lower
bound for the residual flat source event immediately gives the same
`n^(-1/2)` scale for the logarithmic core, losing only `exp B`. -/
theorem pi_gaussianReal_logTiltSource_le_exp_mul_core
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i) (B : Real) :
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
        (harper1144GaussianLogTiltSourceEvent variance B) <=
      ENNReal.ofReal (Real.exp B) *
        Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
          (harper1144GaussianLogBallotCoreEvent n) := by
  let P : Measure (Fin n -> Real) :=
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
  let T := harper1144GaussianLogTiltDown variance
  let A := harper1144GaussianLogTiltTargetEvent variance B
  have hsource : harper1144GaussianLogTiltSourceEvent variance B ⊆ T ⁻¹' A :=
    fun _omega homega => homega.2
  have hmonoSource :
      P (harper1144GaussianLogTiltSourceEvent variance B) <= P (T ⁻¹' A) :=
    measure_mono hsource
  have hshift := pi_gaussianReal_neg_logTilt_target_le
    variance hlower B
  have hmap := pi_gaussianReal_neg_logTilt_target_eq_preimage variance B
  have htarget : A ⊆ harper1144GaussianLogBallotCoreEvent n :=
    fun _omega homega => homega.1
  have hmonoTarget : P A <= P (harper1144GaussianLogBallotCoreEvent n) :=
    measure_mono htarget
  calc
    P (harper1144GaussianLogTiltSourceEvent variance B) <=
        P (T ⁻¹' A) := hmonoSource
    _ = Measure.pi (fun i : Fin n =>
          gaussianReal (-harper1144GaussianLogTiltIncrement variance i)
            (variance i)) A := by
      simpa only [P, T, A] using hmap.symm
    _ <= ENNReal.ofReal (Real.exp B) * P A := by
      simpa only [P, A] using hshift
    _ <= ENNReal.ofReal (Real.exp B) *
        P (harper1144GaussianLogBallotCoreEvent n) := by
      exact mul_le_mul_left' hmonoTarget _

/-- Lean-facing final reduction for the one-height analytic task: it is
enough to lower-bound the explicit flat certificate event. -/
theorem pi_gaussianReal_logTiltCertificate_le_exp_mul_core
    {n : Nat} (variance : Fin n -> NNReal)
    (hlower : ∀ i, (1 / 4 : NNReal) <= variance i) (B : Real) :
    Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
        (harper1144GaussianLogTiltCertificateEvent variance B) <=
      ENNReal.ofReal (Real.exp B) *
        Measure.pi (fun i : Fin n => gaussianReal 0 (variance i))
          (harper1144GaussianLogBallotCoreEvent n) := by
  exact (measure_mono
      (harper1144GaussianLogTiltCertificateEvent_subset_source
        variance hlower B)).trans
    (pi_gaussianReal_logTiltSource_le_exp_mul_core variance hlower B)

#print axioms Erdos.Problem1144.map_pi_harper1144GaussianLogTiltDown
#print axioms Erdos.Problem1144.harper1144GaussianLogTiltDown_mem_upper_of_flat
#print axioms Erdos.Problem1144.sum_harper1144GaussianLogTiltRate_sq_mul_variance_le
#print axioms Erdos.Problem1144.pi_gaussianReal_neg_logTilt_eq_withDensity
#print axioms Erdos.Problem1144.pi_gaussianReal_neg_logTilt_eq_withDensity_exp
#print axioms Erdos.Problem1144.pi_gaussianReal_logTiltSource_le_exp_mul_core
#print axioms Erdos.Problem1144.pi_gaussianReal_logTiltCertificate_le_exp_mul_core

end

end Problem1144
end Erdos
