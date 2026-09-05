import StateDepMOR.PaperStatements
import StateDepMOR.PoissonCountLDP
import StateDepMOR.PoissonProcessExecution
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Monotone
import Mathlib.Data.List.Sort
import Mathlib.Topology.Algebra.Affine
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Covering.OneDim
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Sequences

open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set

namespace StateDepMOR

universe u v w

namespace PoissonFiniteArray

variable {Coord : Type u} [Fintype Coord]

/-- Independent Poisson counts with parameters `K * q a`. -/
noncomputable def countLaw (q : Coord -> NNReal) (K : Nat) :
    Measure (Coord -> Nat) :=
  Measure.pi fun a =>
    ProbabilityTheory.poissonMeasure ((K : NNReal) * q a)

/-- Coordinatewise division by the system size. -/
noncomputable def scale (K : Nat) (n : Coord -> Nat) : Coord -> Real :=
  fun a => (n a : Real) / K

/-- Law of the scaled finite Poisson array. -/
noncomputable def scaledLaw (q : Coord -> NNReal) (K : Nat) :
    Measure (Coord -> Real) :=
  (countLaw q K).map (scale K)

instance countLaw_isProbabilityMeasure (q : Coord -> NNReal) (K : Nat) :
    IsProbabilityMeasure (countLaw q K) := by
  unfold countLaw
  infer_instance

instance scaledLaw_isProbabilityMeasure (q : Coord -> NNReal) (K : Nat) :
    IsProbabilityMeasure (scaledLaw q K) := by
  unfold scaledLaw
  exact Measure.isProbabilityMeasure_map
    (Measurable.aemeasurable (by fun_prop))

/-- The finite-dimensional Poisson action. -/
noncomputable def action (q : Coord -> NNReal) (x : Coord -> Real) : ENNReal :=
  ∑ a, poissonCost (q a : Real) (x a)

/-- Exact atom formula for the count product. -/
theorem countLaw_singleton (q : Coord -> NNReal) (K : Nat)
    (n : Coord -> Nat) :
    countLaw q K {n} =
      ∏ a, ENNReal.ofReal
        (Real.exp (-((K : Real) * (q a : Real))) *
          ((K : Real) * (q a : Real)) ^ n a / Nat.factorial (n a)) := by
  simp only [countLaw, Measure.pi_singleton,
    ProbabilityTheory.poissonMeasure_singleton]
  apply Finset.prod_congr rfl
  intro a ha
  congr 2

/-- Scaling is injective at positive system size. -/
theorem scale_injective (K : Nat) (hK : 0 < K) :
    Function.Injective (scale K : (Coord -> Nat) -> Coord -> Real) := by
  intro m n hmn
  funext a
  have ha := congrFun hmn a
  unfold scale at ha
  have hKr : Ne (K : Real) 0 := by exact_mod_cast hK.ne'
  have : (m a : Real) = n a := (div_left_inj' hKr).mp ha
  exact_mod_cast this

/-- Exact atom formula after scaling. -/
theorem scaledLaw_singleton (q : Coord -> NNReal) (K : Nat)
    (n : Coord -> Nat) (hK : 0 < K) :
    scaledLaw q K {scale K n} = countLaw q K {n} := by
  have hpre : scale K ⁻¹' {scale K n} = {n} := by
    ext m
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (scale_injective K hK).eq_iff
  rw [scaledLaw, Measure.map_apply (by fun_prop)
    (measurableSet_singleton _), hpre]

/-- A zero nominal coordinate is supported exactly at zero. -/
theorem countLaw_singleton_eq_zero_of_zero
    (q : Coord -> NNReal) (K : Nat) (n : Coord -> Nat)
    (a : Coord) (hq : q a = 0) (hn : 0 < n a) :
    countLaw q K {n} = 0 := by
  classical
  rw [countLaw_singleton]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp [hq, Nat.ne_of_gt hn]

/-- The scalar Poisson cost is lower semicontinuous, including at nominal
rate zero and across the boundary of the nonnegative orthant. -/
theorem lowerSemicontinuous_poissonCost (nominal : NNReal) :
    LowerSemicontinuous (fun x : Real => poissonCost (nominal : Real) x) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c = (Top.top : ENNReal)
  · subst c
    simp
  rcases eq_or_ne nominal 0 with rfl | hn
  · have hset :
        (fun x : Real => poissonCost 0 x) ⁻¹' Iic c = ({0} : Set Real) := by
      ext x
      by_cases hx : x = 0
      · subst x
        simp
      · rcases lt_or_gt_of_ne hx with hxneg | hxpos
        · simp [poissonCost, hxneg, hc, hx]
        · simp [poissonCost, not_lt_of_ge hxpos.le, hx, hc]
    simp only [NNReal.coe_zero]
    rw [hset]
    exact isClosed_singleton
  · have hnpos : 0 < (nominal : Real) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hn)
    have hset :
        (fun x : Real => poissonCost (nominal : Real) x) ⁻¹' Iic c =
          Ici 0 ∩
            (fun x : Real => ENNReal.ofReal
              (poissonCostReal (nominal : Real) x)) ⁻¹' Iic c := by
      ext x
      by_cases hx : x < 0
      · simp [poissonCost, hx, hc]
      · have hx0 : 0 <= x := le_of_not_gt hx
        simp [poissonCost_of_nominal_pos hnpos hx0, poissonCostReal, hx0]
    rw [hset]
    exact isClosed_Ici.inter
      (isClosed_Iic.preimage (ENNReal.continuous_ofReal.comp
        (continuous_poissonCostReal_right hnpos)))

/-- The finite real action on the effective domain. -/
noncomputable def actionReal (q : Coord -> NNReal) (x : Coord -> Real) : Real :=
  ∑ a, if q a = 0 then 0 else poissonCostReal (q a : Real) (x a)

/-- Effective domain of the finite Poisson action. -/
def Admissible (q : Coord -> NNReal) (x : Coord -> Real) : Prop :=
  forall a, 0 <= x a /\ (q a = 0 -> x a = 0)

theorem continuous_actionReal (q : Coord -> NNReal) :
    Continuous (actionReal q) := by
  classical
  unfold actionReal
  apply continuous_finsetSum
  intro a ha
  by_cases hq : q a = 0
  · simpa [hq] using (continuous_const : Continuous (fun _ : Coord -> Real => (0 : Real)))
  · simp only [hq, if_false]
    exact (continuous_poissonCostReal_right (by
      exact_mod_cast (pos_iff_ne_zero.mpr hq))).comp (continuous_apply a)

theorem actionReal_nonnegative (q : Coord -> NNReal) (x : Coord -> Real)
    (hx : Admissible q x) :
    0 <= actionReal q x := by
  classical
  unfold actionReal
  apply Finset.sum_nonneg
  intro a ha
  by_cases hq : q a = 0
  · simp [hq]
  · simp only [hq, if_false]
    exact poissonCostReal_nonneg
      (by exact_mod_cast (pos_iff_ne_zero.mpr hq)) (hx a).1

theorem action_eq_of_admissible (q : Coord -> NNReal) (x : Coord -> Real)
    (hx : Admissible q x) :
    action q x = ENNReal.ofReal (actionReal q x) := by
  classical
  unfold action actionReal
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a ha
    by_cases hq : q a = 0
    · simp [hq, (hx a).2 hq]
    · simp only [hq, if_false]
      exact poissonCost_of_nominal_pos
        (by exact_mod_cast (pos_iff_ne_zero.mpr hq)) (hx a).1
  · intro a ha
    by_cases hq : q a = 0
    · simp [hq]
    · simp only [hq, if_false]
      exact poissonCostReal_nonneg
        (by exact_mod_cast (pos_iff_ne_zero.mpr hq)) (hx a).1

theorem action_coordinate_le (q : Coord -> NNReal) (x : Coord -> Real)
    (a : Coord) :
    poissonCost (q a : Real) (x a) <= action q x := by
  classical
  unfold action
  exact Finset.single_le_sum
    (fun b _ => (zero_le : (0 : ENNReal) <= _)) (Finset.mem_univ a)

theorem action_finite_nonnegative (q : Coord -> NNReal) (x : Coord -> Real)
    (hfinite : Ne (action q x) (Top.top : ENNReal)) (a : Coord) :
    0 <= x a := by
  by_contra h
  have hcost := poissonCost_of_candidate_neg (lt_of_not_ge h)
    (nominal := (q a : Real))
  have hle := action_coordinate_le q x a
  rw [hcost] at hle
  exact hfinite (top_unique hle)

theorem isClosed_admissible (q : Coord -> NNReal) :
    IsClosed {x : Coord -> Real | Admissible q x} := by
  classical
  have hnonneg : IsClosed {x : Coord -> Real | forall a, 0 <= x a} := by
    rw [show {x : Coord -> Real | forall a, 0 <= x a} =
        ⋂ a, (fun x : Coord -> Real => x a) ⁻¹' Ici 0 by
      ext x
      simp]
    exact isClosed_iInter fun a =>
      isClosed_Ici.preimage (continuous_apply a)
  have hzero :
      IsClosed {x : Coord -> Real | forall a, q a = 0 -> x a = 0} := by
    rw [show {x : Coord -> Real | forall a, q a = 0 -> x a = 0} =
        ⋂ a, if q a = 0 then
          (fun x : Coord -> Real => x a) ⁻¹' ({0} : Set Real)
        else Set.univ by
      ext x
      simp]
    apply isClosed_iInter
    intro a
    split
    · exact isClosed_singleton.preimage (continuous_apply a)
    · exact isClosed_univ
  rw [show {x : Coord -> Real | Admissible q x} =
      {x | forall a, 0 <= x a} ∩
        {x | forall a, q a = 0 -> x a = 0} by
    ext x
    simp [Admissible, forall_and]]
  exact hnonneg.inter hzero

theorem action_sublevel_eq (q : Coord -> NNReal) (c : ENNReal)
    (hc : Ne c (Top.top : ENNReal)) :
    {x : Coord -> Real | action q x <= c} =
      {x | Admissible q x} ∩
        (actionReal q) ⁻¹' Iic c.toReal := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
  constructor
  · intro hx
    have hfinite : Ne (action q x) (Top.top : ENNReal) :=
      ne_of_lt (hx.trans_lt (lt_top_iff_ne_top.mpr hc))
    have hadm : Admissible q x := by
      intro a
      have hnonneg := action_finite_nonnegative q x hfinite a
      refine ⟨hnonneg, ?_⟩
      intro hq
      by_contra hxa
      have hpos : 0 < x a := lt_of_le_of_ne hnonneg (Ne.symm hxa)
      have hcost : poissonCost (q a : Real) (x a) = (Top.top : ENNReal) := by
        simpa [hq] using poissonCost_zero_of_pos hpos
      have hle := action_coordinate_le q x a
      rw [hcost] at hle
      exact hfinite (top_unique hle)
    refine ⟨hadm, ?_⟩
    rw [action_eq_of_admissible q x hadm] at hx
    exact (ENNReal.ofReal_le_iff_le_toReal hc).mp hx
  · rintro ⟨hadm, hreal⟩
    rw [action_eq_of_admissible q x hadm]
    exact ENNReal.ofReal_le_of_le_toReal hreal

/-- The finite action is lower semicontinuous. -/
theorem lowerSemicontinuous_action (q : Coord -> NNReal) :
    LowerSemicontinuous (action q) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c = (Top.top : ENNReal)
  · subst c
    simp
  rw [show (action q) ⁻¹' Iic c =
      {x : Coord -> Real | action q x <= c} by rfl,
    action_sublevel_eq q c hc]
  exact (isClosed_admissible q).inter
    (isClosed_Iic.preimage (continuous_actionReal q))

theorem poissonCost_fenchel_one
    {nominal candidate : Real}
    (hnominal : 0 <= nominal) (hcandidate : 0 <= candidate) :
    ENNReal.ofReal candidate <=
      poissonCost nominal candidate +
        ENNReal.ofReal (nominal * (Real.exp 1 - 1)) := by
  rcases hnominal.eq_or_lt with rfl | hn
  · rcases hcandidate.eq_or_lt with rfl | hc
    · simp
    · simp [poissonCost_zero_of_pos hc]
  · rw [poissonCost_of_nominal_pos hn hcandidate]
    have hcost : 0 <= poissonCostReal nominal candidate :=
      poissonCostReal_nonneg hn hcandidate
    have hreal :
        candidate <= poissonCostReal nominal candidate +
          nominal * (Real.exp 1 - 1) := by
      rcases hcandidate.eq_or_lt with rfl | hc
      · exact add_nonneg hcost
          (mul_nonneg hn.le (sub_nonneg.mpr
            (Real.one_le_exp (by norm_num))))
      · have hr : 0 < candidate / nominal := div_pos hc hn
        have he := Real.add_one_le_exp
          (1 - Real.log (candidate / nominal))
        rw [Real.exp_sub, Real.exp_log hr] at he
        have hscaled := mul_le_mul_of_nonneg_left he hcandidate
        have hcancel :
            candidate * (Real.exp 1 / (candidate / nominal)) =
              nominal * Real.exp 1 := by
          field_simp
        rw [hcancel] at hscaled
        dsimp [poissonCostReal]
        nlinarith
    calc
      ENNReal.ofReal candidate <=
          ENNReal.ofReal (poissonCostReal nominal candidate +
            nominal * (Real.exp 1 - 1)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (poissonCostReal nominal candidate) +
          ENNReal.ofReal (nominal * (Real.exp 1 - 1)) := by
        rw [ENNReal.ofReal_add hcost
          (mul_nonneg hn.le (sub_nonneg.mpr
            (Real.one_le_exp (by norm_num))))]

/-- A coordinate of a finite action sublevel has an explicit upper bound. -/
theorem sublevel_coordinate_bound (q : Coord -> NNReal) (x : Coord -> Real)
    (c : Real) (hx : action q x <= ENNReal.ofReal c) (a : Coord) :
    x a <= max c 0 + (q a : Real) * (Real.exp 1 - 1) := by
  have hfinite : Ne (action q x) (Top.top : ENNReal) :=
    ne_of_lt (hx.trans_lt ENNReal.ofReal_lt_top)
  have hx0 := action_finite_nonnegative q x hfinite a
  have hfenchel := poissonCost_fenchel_one
    (show 0 <= (q a : Real) by positivity) hx0
  have hle :
      ENNReal.ofReal (x a) <=
        ENNReal.ofReal c +
          ENNReal.ofReal ((q a : Real) * (Real.exp 1 - 1)) := by
    exact hfenchel.trans (add_le_add (action_coordinate_le q x a |>.trans hx) le_rfl)
  have hcmax : ENNReal.ofReal c = ENNReal.ofReal (max c 0) := by
    rw [ENNReal.ofReal_max]
    simp
  have hconst : 0 <= (q a : Real) * (Real.exp 1 - 1) :=
    mul_nonneg (by positivity)
      (sub_nonneg.mpr (Real.one_le_exp (by norm_num)))
  rw [hcmax, ← ENNReal.ofReal_add (le_max_right c 0) hconst] at hle
  exact (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg (le_max_right c 0) hconst)).mp hle

/-- Every real sublevel of the finite-array action is compact. -/
theorem isCompact_action_sublevel (q : Coord -> NNReal) (c : Real) :
    IsCompact {x : Coord -> Real | action q x <= ENNReal.ofReal c} := by
  classical
  let upper : Coord -> Real :=
    fun a => max c 0 + (q a : Real) * (Real.exp 1 - 1)
  have hclosed :
      IsClosed {x : Coord -> Real | action q x <= ENNReal.ofReal c} := by
    simpa only [Set.preimage, Set.mem_Iic] using
      (lowerSemicontinuous_action q).isClosed_preimage (ENNReal.ofReal c)
  have hsubset :
      {x : Coord -> Real | action q x <= ENNReal.ofReal c} <=
        Set.Icc (fun _ => 0) upper := by
    intro x hx
    rw [Set.mem_Icc]
    constructor
    · intro a
      exact action_finite_nonnegative q x
        (ne_of_lt (hx.trans_lt ENNReal.ofReal_lt_top)) a
    · intro a
      exact sublevel_coordinate_bound q x c hx a
  exact isCompact_Icc.of_isClosed_subset hclosed hsubset

/-- Canonical lattice approximation of a nonnegative array. -/
noncomputable def floorCount (x : Coord -> Real) (K : Nat) : Coord -> Nat :=
  fun a => Nat.floor (x a * K)

theorem floorCount_zero (x : Coord -> Real) (a : Coord) (hx : x a = 0) :
    forall K, floorCount x K a = 0 := by
  intro K
  simp [floorCount, hx]

theorem floorCount_scale_tendsto (x : Coord -> Real)
    (hx : forall a, 0 <= x a) (a : Coord) :
    Tendsto (fun K => (floorCount x K a : Real) / K)
      atTop (nhds (x a)) := by
  convert
    (tendsto_nat_floor_mul_div_atTop (R := Real) (hx a)).comp
      (tendsto_natCast_atTop_atTop (R := Real)) using 1 <;>
    simp [floorCount, Function.comp_def, mul_comm]

/-- Real product appearing in the exact atom formula. -/
noncomputable def atomReal (q : Coord -> NNReal) (K : Nat)
    (n : Coord -> Nat) : Real :=
  ∏ a, poissonAtomReal K 1 (q a : Real) (n a)

theorem countLaw_real_singleton (q : Coord -> NNReal) (K : Nat)
    (n : Coord -> Nat) :
    (countLaw q K).real {n} = atomReal q K n := by
  classical
  rw [measureReal_def, countLaw_singleton]
  simp only [ENNReal.toReal_prod]
  unfold atomReal
  apply Finset.prod_congr rfl
  intro a ha
  rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [poissonAtomReal]
  ring_nf

theorem atomReal_pos (q : Coord -> NNReal) (K : Nat)
    (n : Coord -> Nat)
    (hK : 0 < K)
    (hsupport : forall a, q a = 0 -> n a = 0) :
    0 < atomReal q K n := by
  classical
  unfold atomReal
  apply Finset.prod_pos
  intro a ha
  rcases eq_or_ne (q a) 0 with hq | hq
  · simp [hq, hsupport a hq, poissonAtomReal]
  · exact poissonAtomReal_pos K (n a) 1 (q a : Real)
      hK (by norm_num)
      (by exact_mod_cast (pos_iff_ne_zero.mpr hq))

/-- Finite-product logarithmic atom asymptotic, including every zero-rate
coordinate. -/
theorem atomReal_log_asymptotic (q : Coord -> NNReal)
    (x : Coord -> Real) (hx : Admissible q x)
    (n : Nat -> Coord -> Nat)
    (hsupport : forall a, q a = 0 -> forall K, n K a = 0)
    (hn : forall a, Tendsto (fun K => (n K a : Real) / K)
      atTop (nhds (x a))) :
    Tendsto
      (fun K => -Real.log ((countLaw q K).real {n K}) / (K : Real))
      atTop (nhds (actionReal q x)) := by
  classical
  have hsum :
      Tendsto
        (fun K => ∑ a,
          -Real.log (poissonAtomReal K 1 (q a : Real) (n K a)) /
            (K : Real))
        atTop
        (nhds (∑ a,
          poissonCostReal (q a : Real) (x a))) := by
    apply tendsto_finset_sum Finset.univ
    intro a ha
    simpa using poissonAtomReal_log_asymptotic_nonneg
      1 (q a : Real) (x a) (by norm_num) (by positivity)
      (fun K => n K a)
      (fun h K => hsupport a (NNReal.coe_eq_zero.mp h) K)
      (by simpa using hn a)
  have htarget :
      (∑ a, poissonCostReal (q a : Real) (x a)) = actionReal q x := by
    unfold actionReal
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hq : q a = 0
    · simp [hq, (hx a).2 hq, poissonCostReal]
    · simp [hq]
  rw [htarget] at hsum
  apply hsum.congr'
  filter_upwards [eventually_atTop.2 (show exists N : Nat,
      forall K, N <= K -> 0 < K by
    exact ⟨1, fun K hK => Nat.zero_lt_of_lt hK⟩)] with K hK
  rw [countLaw_real_singleton, atomReal]
  have hpos (a : Coord) :
      0 < poissonAtomReal K 1 (q a : Real) (n K a) := by
    rcases eq_or_ne (q a) 0 with hq | hq
    · simp [hq, hsupport a hq K, poissonAtomReal]
    · exact poissonAtomReal_pos K (n K a) 1 (q a : Real)
        hK (by norm_num) (by exact_mod_cast (pos_iff_ne_zero.mpr hq))
  rw [Real.log_prod (fun a ha => (hpos a).ne')]
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.sum_neg_distrib,
    neg_mul]

/-- The EReal logarithmic atom asymptotic in the convention used by
`scaledLogMass`. -/
theorem countLaw_log_atom_asymptotic (q : Coord -> NNReal)
    (x : Coord -> Real) (hx : Admissible q x)
    (n : Nat -> Coord -> Nat)
    (hsupport : forall a, q a = 0 -> forall K, n K a = 0)
    (hn : forall a, Tendsto (fun K => (n K a : Real) / K)
      atTop (nhds (x a))) :
    Tendsto
      (fun K => ENNReal.log (countLaw q K {n K}) / (K : EReal))
      atTop (nhds (-(action q x : EReal))) := by
  have hreal := atomReal_log_asymptotic q x hx n hsupport hn
  have hcoe :
      Tendsto
        (fun K => ((Real.log ((countLaw q K).real {n K}) /
          (K : Real) : Real) : EReal))
        atTop (nhds ((-(actionReal q x) : Real) : EReal)) := by
    rw [EReal.tendsto_coe]
    convert hreal.neg using 1 <;> ring
  have heq :
      (fun K => ENNReal.log (countLaw q K {n K}) / (K : EReal)) =ᶠ[atTop]
        (fun K => ((Real.log ((countLaw q K).real {n K}) /
          (K : Real) : Real) : EReal)) := by
    filter_upwards [eventually_atTop.2 (show exists N : Nat,
        forall K, N <= K -> 0 < K by
      exact ⟨1, fun K hK => Nat.zero_lt_of_lt hK⟩)] with K hK
    have hp : 0 < (countLaw q K {n K}).toReal := by
      rw [← measureReal_def, countLaw_real_singleton]
      exact atomReal_pos q K (n K) hK
        (fun a hqa => hsupport a hqa K)
    rw [ENNReal.log_pos_real' hp]
    norm_cast
  have htarget :
      ((-(actionReal q x) : Real) : EReal) = -(action q x : EReal) := by
    rw [action_eq_of_admissible q x hx, EReal.coe_ennreal_ofReal,
      max_eq_left (actionReal_nonnegative q x hx)]
    norm_cast
  rw [← htarget]
  exact hcoe.congr' heq.symm

theorem floorCount_log_atom_asymptotic (q : Coord -> NNReal)
    (x : Coord -> Real) (hx : Admissible q x) :
    Tendsto
      (fun K => ENNReal.log (countLaw q K {floorCount x K}) / (K : EReal))
      atTop (nhds (-(action q x : EReal))) := by
  apply countLaw_log_atom_asymptotic q x hx (floorCount x)
  · intro a hq K
    exact floorCount_zero x a ((hx a).2 hq) K
  · intro a
    exact floorCount_scale_tendsto x (fun b => (hx b).1) a

theorem admissible_of_action_ne_top (q : Coord -> NNReal)
    (x : Coord -> Real) (hfinite : Ne (action q x) (Top.top : ENNReal)) :
    Admissible q x := by
  intro a
  have hnonneg := action_finite_nonnegative q x hfinite a
  refine ⟨hnonneg, ?_⟩
  intro hq
  by_contra hxa
  have hpos : 0 < x a := lt_of_le_of_ne hnonneg (Ne.symm hxa)
  have hcost : poissonCost (q a : Real) (x a) = (Top.top : ENNReal) := by
    simpa [hq] using poissonCost_zero_of_pos hpos
  have hle := action_coordinate_le q x a
  rw [hcost] at hle
  exact hfinite (top_unique hle)

theorem floorScale_tendsto (x : Coord -> Real)
    (hx : forall a, 0 <= x a) :
    Tendsto (fun K => scale K (floorCount x K)) atTop (nhds x) := by
  rw [tendsto_pi_nhds]
  intro a
  exact floorCount_scale_tendsto x hx a

theorem scaledLogMass_nonpos (q : Coord -> NNReal)
    (event : Set (Coord -> Real)) (K : Nat) :
    scaledLogMass (scaledLaw q) event K <= 0 := by
  unfold scaledLogMass
  have hm : scaledLaw q (K + 1) event <= 1 := by
    calc
      scaledLaw q (K + 1) event <= scaledLaw q (K + 1) Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have hlog : ENNReal.log (scaledLaw q (K + 1) event) <= 0 :=
    ENNReal.log_le_zero_iff.mpr hm
  exact EReal.div_nonpos_of_nonpos_of_nonneg hlog (by positivity)

theorem liminf_scaledLogMass_nonpos (q : Coord -> NNReal)
    (event : Set (Coord -> Real)) :
    liminf (scaledLogMass (scaledLaw q) event) atTop <= 0 := by
  calc
    liminf (scaledLogMass (scaledLaw q) event) atTop <=
        liminf (fun _ : Nat => (0 : EReal)) atTop :=
      liminf_le_liminf (Eventually.of_forall
        (scaledLogMass_nonpos q event))
    _ = 0 := liminf_const (0 : EReal)

theorem open_lower_point (q : Coord -> NNReal)
    {G : Set (Coord -> Real)} (hG : IsOpen G)
    {x : Coord -> Real} (hxG : x ∈ G)
    (hfinite : Ne (action q x) (Top.top : ENNReal)) :
    -(action q x : EReal) <=
      liminf (scaledLogMass (scaledLaw q) G) atTop := by
  have hadm := admissible_of_action_ne_top q x hfinite
  have hfloor :
      Tendsto (fun K => scale K (floorCount x K)) atTop (nhds x) :=
    floorScale_tendsto x (fun a => (hadm a).1)
  have hmem :
      ∀ᶠ K in atTop, scale (K + 1) (floorCount x (K + 1)) ∈ G :=
    (hfloor.comp (tendsto_add_atTop_nat 1)).eventually (hG.mem_nhds hxG)
  have hatom :=
    (floorCount_log_atom_asymptotic q x hadm).comp
      (tendsto_add_atTop_nat 1)
  have hmono :
      ∀ᶠ K in atTop,
        ENNReal.log
            (countLaw q (K + 1) {floorCount x (K + 1)}) /
              ((K + 1 : Nat) : EReal) <=
          scaledLogMass (scaledLaw q) G K := by
    filter_upwards [hmem] with K hKG
    unfold scaledLogMass
    have hmass :
        countLaw q (K + 1) {floorCount x (K + 1)} <=
          scaledLaw q (K + 1) G := by
      rw [← scaledLaw_singleton q (K + 1) (floorCount x (K + 1))
        (by omega)]
      exact measure_mono (singleton_subset_iff.mpr hKG)
    exact EReal.div_le_div_right_of_nonneg (by positivity)
      (ENNReal.log_le_log hmass)
  calc
    -(action q x : EReal) =
        liminf
          (fun K =>
            ENNReal.log
                (countLaw q (K + 1) {floorCount x (K + 1)}) /
              ((K + 1 : Nat) : EReal))
          atTop := hatom.liminf_eq.symm
    _ <= liminf (scaledLogMass (scaledLaw q) G) atTop :=
      liminf_le_liminf hmono

theorem neg_rateInf_le_of_pointwise
    (q : Coord -> NNReal) (G : Set (Coord -> Real))
    (hpoint : forall x, x ∈ G ->
      -(action q x : EReal) <=
        liminf (scaledLogMass (scaledLaw q) G) atTop) :
    -(rateInf (action q) G : EReal) <=
      liminf (scaledLogMass (scaledLaw q) G) atTop := by
  let L := liminf (scaledLogMass (scaledLaw q) G) atTop
  have hL : L <= 0 := liminf_scaledLogMass_nonpos q G
  have hz : 0 <= -L := EReal.neg_nonneg.mpr hL
  have hto :
      (-L).toENNReal <= rateInf (action q) G := by
    unfold rateInf
    apply le_sInf
    intro y hy
    rcases hy with ⟨x, hxG, rfl⟩
    have hneg := hpoint x hxG
    have hrev : -L <= (action q x : EReal) := by
      simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hneg
    simpa only [EReal.toENNReal_coe] using
      EReal.toENNReal_le_toENNReal hrev
  have hcoe :
      -L <= (rateInf (action q) G : EReal) := by
    rw [← EReal.coe_toENNReal hz]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hto
  simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hcoe

/-- Open-set lower bound for the finite scaled product law. -/
theorem open_lower_bound (q : Coord -> NNReal)
    (G : Set (Coord -> Real)) (hG : IsOpen G) :
    -(rateInf (action q) G : EReal) <=
      liminf (scaledLogMass (scaledLaw q) G) atTop := by
  apply neg_rateInf_le_of_pointwise q G
  intro x hxG
  by_cases hfinite : action q x = (Top.top : ENNReal)
  · simp [hfinite]
  · exact open_lower_point q hG hxG hfinite

theorem neg_log_atomReal_ge_actionReal (q : Coord -> NNReal)
    (K : Nat) (hK : 0 < K) (n : Coord -> Nat)
    (hsupport : forall a, q a = 0 -> n a = 0) :
    actionReal q (scale K n) <=
      -Real.log ((countLaw q K).real {n}) / (K : Real) := by
  classical
  rw [countLaw_real_singleton, atomReal,
    Real.log_prod (fun a ha => by
      rcases eq_or_ne (q a) 0 with hq | hq
      · simp [hq, hsupport a hq, poissonAtomReal]
      · exact (poissonAtomReal_pos K (n a) 1 (q a : Real)
          hK (by norm_num)
          (by exact_mod_cast (pos_iff_ne_zero.mpr hq))).ne')]
  unfold actionReal
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  apply Finset.sum_le_sum
  intro a ha
  by_cases hq : q a = 0
  · simp [hq, hsupport a hq, scale, poissonCostReal, poissonAtomReal]
  · simp only [hq, if_false]
    have heq := neg_log_poissonAtomReal_eq K (n a) 1 (q a : Real)
      hK (by norm_num) (by exact_mod_cast (pos_iff_ne_zero.mpr hq))
    rw [heq]
    have herr : 0 <= stirlingLogError (n a) / (K : Real) :=
      div_nonneg (stirlingLogError_nonneg (n a))
        (show (0 : Real) <= K by exact_mod_cast hK.le)
    simpa only [scale, one_mul] using
      (le_add_of_nonneg_right
        (a := poissonCostReal (q a : Real) ((n a : Real) / K)) herr)

/-- Exact atom upper estimate in EReal logarithmic form. -/
theorem countLaw_atom_log_le (q : Coord -> NNReal)
    (K : Nat) (hK : 0 < K) (n : Coord -> Nat) :
    ENNReal.log (countLaw q K {n}) / (K : EReal) <=
      -(action q (scale K n) : EReal) := by
  by_cases hsupport : forall a, q a = 0 -> n a = 0
  · have hadm : Admissible q (scale K n) := by
      intro a
      refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
      intro hq
      simp [scale, hsupport a hq]
    have hp : 0 < (countLaw q K {n}).toReal := by
      rw [← measureReal_def, countLaw_real_singleton]
      exact atomReal_pos q K n hK hsupport
    rw [ENNReal.log_pos_real' hp, action_eq_of_admissible q (scale K n) hadm,
      EReal.coe_ennreal_ofReal,
      max_eq_left (actionReal_nonnegative q (scale K n) hadm)]
    apply EReal.coe_le_coe_iff.mpr
    have hneg := neg_log_atomReal_ge_actionReal q K hK n hsupport
    rw [measureReal_def] at hneg
    change Real.log (countLaw q K {n}).toReal / (K : Real) <=
      -actionReal q (scale K n)
    simpa only [neg_div, neg_neg] using neg_le_neg hneg
  · push_neg at hsupport
    obtain ⟨a, hqa, hna⟩ := hsupport
    have hzero := countLaw_singleton_eq_zero_of_zero q K n a hqa
      (Nat.zero_lt_of_ne_zero hna)
    rw [hzero, ENNReal.log_zero]
    rw [EReal.bot_div_of_pos_ne_top (by positivity)
      (EReal.natCast_ne_top K)]
    exact bot_le

theorem countLaw_atom_le_exp (q : Coord -> NNReal)
    (K : Nat) (hK : 0 < K) (n : Coord -> Nat) (c : Real)
    (hc : ENNReal.ofReal c <= action q (scale K n)) :
    countLaw q K {n} <=
      ENNReal.ofReal (Real.exp (-(K : Real) * c)) := by
  by_cases hc0 : c <= 0
  · calc
      countLaw q K {n} <= 1 := by
        calc
          countLaw q K {n} <= countLaw q K Set.univ :=
            measure_mono (subset_univ _)
          _ = 1 := measure_univ
      _ <= ENNReal.ofReal (Real.exp (-(K : Real) * c)) := by
        rw [← ENNReal.ofReal_one,
          ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le]
        exact Real.one_le_exp
          (mul_nonneg_of_nonpos_of_nonpos
            (neg_nonpos.mpr (Nat.cast_nonneg K)) hc0)
  have hscaled := countLaw_atom_log_le q K hK n
  have hcost :
      -(action q (scale K n) : EReal) <=
        -((ENNReal.ofReal c : ENNReal) : EReal) :=
    EReal.neg_le_neg_iff.mpr
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hc)
  have hdiv :
      ENNReal.log (countLaw q K {n}) / (K : EReal) <=
        -((ENNReal.ofReal c : ENNReal) : EReal) :=
    hscaled.trans hcost
  have hlog :
      ENNReal.log (countLaw q K {n}) <=
        ((K : Nat) : EReal) *
          -((ENNReal.ofReal c : ENNReal) : EReal) := by
    calc
      ENNReal.log (countLaw q K {n}) =
          ((K : Nat) : EReal) *
            (ENNReal.log (countLaw q K {n}) / (K : EReal)) := by
        rw [EReal.mul_div_cancel (EReal.natCast_ne_bot K)
          (EReal.natCast_ne_top K) (by positivity)]
      _ <= ((K : Nat) : EReal) *
          -((ENNReal.ofReal c : ENNReal) : EReal) :=
        mul_le_mul_of_nonneg_left hdiv
          (EReal.coe_ennreal_nonneg (K : ENNReal))
  rw [← ENNReal.log_le_log_iff]
  rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _)]
  have hcpos : 0 < c := lt_of_not_ge hc0
  rw [EReal.coe_ennreal_ofReal, max_eq_left hcpos.le] at hlog
  refine hlog.trans_eq ?_
  norm_cast
  rw [Real.log_exp]
  push_cast
  ring

/-- A subexponential prefactor does not affect the EReal logarithmic upper
bound. -/
theorem limsup_of_subexponential_bound
    (mu : Nat -> Measure (Coord -> Real))
    (event : Set (Coord -> Real)) (A : Nat -> Real) (c : Real)
    (hApos : forall K, 0 < K -> 0 < A K)
    (hbound : forall K, 0 < K ->
      mu K event <= ENNReal.ofReal (A K * Real.exp (-(K : Real) * c)))
    (hsubexp : Tendsto (fun K => Real.log (A K) / (K : Real))
      atTop (nhds 0)) :
    limsup (scaledLogMass mu event) atTop <= -(c : EReal) := by
  have hright :
      Tendsto (fun K =>
        ((Real.log (A (K + 1)) / ((K + 1 : Nat) : Real) - c : Real) : EReal))
        atTop (nhds (-(c : EReal))) := by
    have hnegcoe : -(c : EReal) = ((-c : Real) : EReal) := by norm_cast
    rw [hnegcoe, EReal.tendsto_coe]
    have hs := hsubexp.comp (tendsto_add_atTop_nat 1)
    have hs' :
        Tendsto (fun K => Real.log (A (K + 1)) / ((K + 1 : Nat) : Real))
          atTop (nhds 0) := by
      convert hs using 1
      funext K
      simp [Function.comp_def]
    simpa using hs'.sub (tendsto_const_nhds : Tendsto (fun _ : Nat => c)
      atTop (nhds c))
  have hle :
      forall K,
        scaledLogMass mu event K <=
          ((Real.log (A (K + 1)) / ((K + 1 : Nat) : Real) - c : Real) : EReal) := by
    intro K
    unfold scaledLogMass
    have hb := hbound (K + 1) (by omega)
    have hlog := ENNReal.log_le_log hb
    rw [ENNReal.log_ofReal_of_pos
      (mul_pos (hApos (K + 1) (by omega)) (Real.exp_pos _))] at hlog
    rw [Real.log_mul (ne_of_gt (hApos (K + 1) (by omega)))
      (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hden : (0 : EReal) <= ((K + 1 : Nat) : EReal) := by positivity
    refine (EReal.div_le_div_right_of_nonneg hden hlog).trans_eq ?_
    have heq :
        (Real.log (A (K + 1)) + -(((K + 1 : Nat) : Real)) * c) /
              (((K + 1 : Nat) : Real)) =
            Real.log (A (K + 1)) / (((K + 1 : Nat) : Real)) - c := by
      field_simp
      ring
    rw [← EReal.coe_natCast, ← EReal.coe_div]
    exact congrArg (fun z : Real => (z : EReal)) heq
  calc
    limsup (scaledLogMass mu event) atTop <=
        limsup
          (fun K =>
            ((Real.log (A (K + 1)) / ((K + 1 : Nat) : Real) - c : Real) : EReal))
          atTop :=
      limsup_le_limsup (Eventually.of_forall hle)
    _ = -(c : EReal) := hright.limsup_eq

/-- All count arrays whose coordinates are at most `B`. -/
noncomputable def boundedCounts (B : Nat) : Finset (Coord -> Nat) := by
  classical
  exact Finset.univ.map
    ⟨fun f : Coord -> Fin (B + 1) => fun a => f a,
      fun f g h => by
        funext a
        exact Fin.ext (congrFun h a)⟩

theorem mem_boundedCounts_iff (B : Nat) (n : Coord -> Nat) :
    n ∈ boundedCounts B <-> forall a, n a <= B := by
  classical
  constructor
  · intro hn a
    rw [boundedCounts, Finset.mem_map] at hn
    obtain ⟨f, -, rfl⟩ := hn
    exact Nat.le_of_lt_succ (f a).isLt
  · intro hn
    rw [boundedCounts, Finset.mem_map]
    let f : Coord -> Fin (B + 1) :=
      fun a => ⟨n a, Nat.lt_succ_iff.mpr (hn a)⟩
    exact ⟨f, Finset.mem_univ _, rfl⟩

theorem card_boundedCounts (B : Nat) :
    (boundedCounts (Coord := Coord) B).card =
      (B + 1) ^ Fintype.card Coord := by
  classical
  simp [boundedCounts]

theorem log_poly_prefactor_tendsto_zero (m d : Nat) :
    Tendsto
      (fun K => Real.log (((K * m + 1) ^ d : Nat) : Real) / (K : Real))
      atTop (nhds 0) := by
  have hK : ∀ᶠ K : Nat in atTop, 0 < K :=
    eventually_atTop.2 ⟨1, fun K h => Nat.zero_lt_of_lt h⟩
  have hnonneg : forall K : Nat,
      0 <= Real.log (((K * m + 1) ^ d : Nat) : Real) / (K : Real) := by
    intro K
    exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  by_cases hm : m = 0
  · subst m
    simpa using (tendsto_const_nhds :
      Tendsto (fun _ : Nat => (0 : Real)) atTop (nhds 0))
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hlogdiv :
      Tendsto (fun K : Nat => Real.log (K : Real) / K)
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, id_eq] using
      (Real.isLittleO_log_id_atTop.comp_tendsto
        (tendsto_natCast_atTop_atTop (R := Real))).tendsto_div_nhds_zero
  let upper : Nat -> Real := fun K =>
    (d : Real) *
      (Real.log (K : Real) / K +
        Real.log ((m + 1 : Nat) : Real) / K)
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp [upper]
    convert tendsto_const_nhds.mul
      (hlogdiv.add
        (tendsto_const_div_atTop_nhds_zero_nat
          (Real.log ((m + 1 : Nat) : Real)))) using 1 <;> ring
  apply squeeze_zero' (Eventually.of_forall hnonneg) ?_ hupper
  filter_upwards [hK] with K hKpos
  have hbasepos : (0 : Real) < ((K * m + 1 : Nat) : Real) := by positivity
  have hKreal : (0 : Real) < K := by exact_mod_cast hKpos
  have hm1real : (0 : Real) < ((m + 1 : Nat) : Real) := by positivity
  have hbase :
      ((K * m + 1 : Nat) : Real) <= (K : Real) * (m + 1 : Nat) := by
    exact_mod_cast (show K * m + 1 <= K * (m + 1) by
      rw [Nat.mul_add, Nat.mul_one]
      omega)
  have hlogbase :
      Real.log ((K * m + 1 : Nat) : Real) <=
        Real.log (K : Real) + Real.log ((m + 1 : Nat) : Real) := by
    calc
      Real.log ((K * m + 1 : Nat) : Real) <=
          Real.log ((K : Real) * (m + 1 : Nat)) :=
        Real.log_le_log hbasepos hbase
      _ = Real.log (K : Real) + Real.log ((m + 1 : Nat) : Real) := by
        rw [Real.log_mul hKreal.ne' hm1real.ne']
  rw [Nat.cast_pow, Real.log_pow]
  dsimp [upper]
  have hmul := mul_le_mul_of_nonneg_left hlogbase (Nat.cast_nonneg d)
  apply div_le_iff₀ hKreal |>.2
  field_simp
  nlinarith

/-- Finite-size atom summation estimate for a coordinatewise bounded event. -/
theorem bounded_mass_le
    (q : Coord -> NNReal) (event : Set (Coord -> Real))
    (hevent : MeasurableSet event) (m : Nat)
    (hbounded : forall x, x ∈ event -> forall a, x a <= m)
    (c : Real) (hc : ENNReal.ofReal c <= rateInf (action q) event)
    (K : Nat) (hK : 0 < K) :
    scaledLaw q K event <=
      ENNReal.ofReal
        (((((K * m + 1) ^ Fintype.card Coord : Nat) : Real)) *
          Real.exp (-(K : Real) * c)) := by
  classical
  rw [scaledLaw, Measure.map_apply (by fun_prop) hevent]
  let counts : Finset (Coord -> Nat) :=
    (boundedCounts (Coord := Coord) (K * m)).filter
      (fun n => scale K n ∈ event)
  have hpre :
      scale K ⁻¹' event ⊆
        ⋃ n ∈ counts, ({n} : Set (Coord -> Nat)) := by
    intro n hn
    have hnle : forall a, n a <= K * m := by
      intro a
      have hscaled := hbounded (scale K n) hn a
      unfold scale at hscaled
      have hKr : (0 : Real) < K := by exact_mod_cast hK
      have hreal : (n a : Real) <= K * m := by
        apply (div_le_iff₀ hKr).mp at hscaled
        simpa [Nat.cast_mul, mul_comm] using hscaled
      exact_mod_cast hreal
    have hmem : n ∈ counts := by
      simp only [counts, Finset.mem_filter]
      exact ⟨(mem_boundedCounts_iff (K * m) n).2 hnle, hn⟩
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨n, hmem, rfl⟩
  calc
    countLaw q K (scale K ⁻¹' event) <=
        countLaw q K (⋃ n ∈ counts, ({n} : Set (Coord -> Nat))) :=
      measure_mono hpre
    _ <= ∑ n ∈ counts, countLaw q K {n} :=
      measure_biUnion_finset_le counts (fun n => ({n} : Set (Coord -> Nat)))
    _ <= ∑ _n ∈ counts,
        ENNReal.ofReal (Real.exp (-(K : Real) * c)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnevent : scale K n ∈ event := (Finset.mem_filter.mp hn).2
      have hrate :
          rateInf (action q) event <= action q (scale K n) := by
        unfold rateInf
        exact sInf_le ⟨scale K n, hnevent, rfl⟩
      exact countLaw_atom_le_exp q K hK n c (hc.trans hrate)
    _ = (counts.card : ENNReal) *
        ENNReal.ofReal (Real.exp (-(K : Real) * c)) := by
      simp [nsmul_eq_mul]
    _ <= (((K * m + 1) ^ Fintype.card Coord : Nat) : ENNReal) *
        ENNReal.ofReal (Real.exp (-(K : Real) * c)) := by
      gcongr
      exact_mod_cast
        (calc
          counts.card <=
              (boundedCounts (Coord := Coord) (K * m)).card :=
            Finset.card_filter_le _ _
          _ = (K * m + 1) ^ Fintype.card Coord :=
            card_boundedCounts (Coord := Coord) (K * m))
    _ = ENNReal.ofReal
        (((((K * m + 1) ^ Fintype.card Coord : Nat) : Real)) *
          Real.exp (-(K : Real) * c)) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- A bounded measurable event has the expected logarithmic upper estimate
at every real level below its rate infimum. -/
theorem bounded_upper_bound_real
    (q : Coord -> NNReal) (event : Set (Coord -> Real))
    (hevent : MeasurableSet event) (m : Nat)
    (hbounded : forall x, x ∈ event -> forall a, x a <= m)
    (c : Real) (hc : ENNReal.ofReal c <= rateInf (action q) event) :
    limsup (scaledLogMass (scaledLaw q) event) atTop <= -(c : EReal) := by
  apply limsup_of_subexponential_bound
    (mu := scaledLaw q) (event := event)
    (A := fun K => (((K * m + 1) ^ Fintype.card Coord : Nat) : Real))
    (c := c)
  · intro K hK
    positivity
  · exact fun K hK =>
      bounded_mass_le q event hevent m hbounded c hc K hK
  · exact log_poly_prefactor_tendsto_zero m (Fintype.card Coord)

/-- A compact set in the finite Euclidean array space has a common
nonnegative integer coordinate bound. -/
theorem compact_exists_coordinate_bound
    (C : Set (Coord -> Real)) (hC : IsCompact C) :
    exists m : Nat, forall x, x ∈ C -> forall a, x a <= m := by
  classical
  have hcoord : forall a : Coord,
      exists R : Real, forall x, x ∈ C -> ‖x a‖ <= R := by
    intro a
    have himage : IsCompact ((fun x : Coord -> Real => x a) '' C) :=
      hC.image (continuous_apply a)
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp himage.isBounded
    exact ⟨R, fun x hx => hR (x a) ⟨x, hx, rfl⟩⟩
  choose R hR using hcoord
  choose m hm using fun a => exists_nat_ge (R a)
  let M : Nat := ∑ a, m a
  refine ⟨M, ?_⟩
  intro x hx a
  calc
    x a <= ‖x a‖ := le_trans (le_abs_self _) (by rw [Real.norm_eq_abs])
    _ <= R a := hR a x hx
    _ <= m a := hm a
    _ <= M := by
      exact_mod_cast (Finset.single_le_sum
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a))

theorem integrable_exp_natCast_poissonMeasure (r : NNReal) (t : Real) :
    Integrable (fun n : Nat => Real.exp (t * (n : Real)))
      (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have hs :
      Summable (fun n : Nat =>
        Real.exp (-(r : Real)) *
          (((r : Real) * Real.exp t) ^ n / Nat.factorial n)) :=
    (Real.summable_pow_div_factorial ((r : Real) * Real.exp t)).mul_left
      (Real.exp (-(r : Real)))
  apply hs.congr
  intro n
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  push_cast
  rw [show t * (n : Real) = (n : Real) * t by ring,
    Real.exp_nat_mul]
  ring

/-- Exact Poisson MGF, including at parameter zero. -/
theorem poissonMeasure_mgf_natCast (r : NNReal) (t : Real) :
    ProbabilityTheory.mgf (fun n : Nat => (n : Real))
        (ProbabilityTheory.poissonMeasure r) t =
      Real.exp ((r : Real) * (Real.exp t - 1)) := by
  rw [ProbabilityTheory.mgf, ProbabilityTheory.integral_poissonMeasure]
  rw [show
      (∑' n : Nat,
        (Real.exp (-(r : Real)) * (r : Real) ^ n /
            Nat.factorial n) • Real.exp (t * (n : Real))) =
        Real.exp (-(r : Real)) *
          ∑' n : Nat,
            (((r : Real) * Real.exp t) ^ n / Nat.factorial n) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [smul_eq_mul]
    push_cast
    rw [show t * (n : Real) = (n : Real) * t by ring,
      Real.exp_nat_mul]
    ring]
  have hexp :
      (∑' n : Nat,
        (((r : Real) * Real.exp t) ^ n / Nat.factorial n)) =
        Real.exp ((r : Real) * Real.exp t) := by
    rw [← congrFun NormedSpace.exp_eq_tsum_div
      ((r : Real) * Real.exp t)]
    exact (congrFun Real.exp_eq_exp_ℝ _).symm
  rw [hexp, ← Real.exp_add]
  congr 1
  ring

/-- One-dimensional Poisson Chernoff estimate, valid also at rate zero. -/
theorem poissonMeasure_upper_tail_chernoff
    (r : NNReal) (a t : Real) (ht : 0 <= t) :
    (ProbabilityTheory.poissonMeasure r).real
        {n : Nat | a <= (n : Real)} <=
      Real.exp (-t * a + (r : Real) * (Real.exp t - 1)) := by
  calc
    (ProbabilityTheory.poissonMeasure r).real
        {n : Nat | a <= (n : Real)} <=
      Real.exp (-t * a) *
        ProbabilityTheory.mgf (fun n : Nat => (n : Real))
          (ProbabilityTheory.poissonMeasure r) t :=
      ProbabilityTheory.measure_ge_le_exp_mul_mgf a ht
        (integrable_exp_natCast_poissonMeasure r t)
    _ = Real.exp (-t * a + (r : Real) * (Real.exp t - 1)) := by
      rw [poissonMeasure_mgf_natCast, ← Real.exp_add]

/-- Every coordinate projection of the finite product count law has exactly
its declared Poisson marginal. -/
theorem countLaw_map_eval (q : Coord -> NNReal) (K : Nat) (a : Coord) :
    (countLaw q K).map (Function.eval a) =
      ProbabilityTheory.poissonMeasure ((K : NNReal) * q a) := by
  classical
  rw [countLaw, Measure.pi_map_eval]
  simp

/-- Chernoff estimate for one coordinate of the product count law. -/
theorem countLaw_coordinate_upper_tail
    (q : Coord -> NNReal) (K : Nat) (a : Coord) (M t : Real)
    (ht : 0 <= t) :
    countLaw q K {n | (K : Real) * M <= (n a : Real)} <=
      ENNReal.ofReal
        (Real.exp ((K : Real) *
          (-t * M + (q a : Real) * (Real.exp t - 1)))) := by
  let S : Set Nat := {n | (K : Real) * M <= (n : Real)}
  have hmap :
      countLaw q K {n | (K : Real) * M <= (n a : Real)} =
        (ProbabilityTheory.poissonMeasure ((K : NNReal) * q a)) S := by
    rw [← countLaw_map_eval q K a,
      Measure.map_apply (by fun_prop) MeasurableSet.of_discrete]
    rfl
  rw [hmap]
  have hreal := poissonMeasure_upper_tail_chernoff
    ((K : NNReal) * q a) ((K : Real) * M) t ht
  apply (ENNReal.toReal_le_toReal
    (measure_ne_top _ _)
    (ENNReal.ofReal_ne_top)).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  change
    (ProbabilityTheory.poissonMeasure ((K : NNReal) * q a)).real S <= _
  convert hreal using 1
  simp only [NNReal.coe_mul, NNReal.coe_natCast]
  congr 1
  ring

/-- Finite-size Chernoff estimate for leaving a positive coordinate box. -/
theorem coordinate_box_compl_mass_le
    (q : Coord -> NNReal) (M : Real) (K : Nat) (hK : 0 < K) :
    scaledLaw q K {x | exists a, M < x a} <=
      ENNReal.ofReal
        (((Fintype.card Coord + 1 : Nat) : Real) *
          Real.exp (-(K : Real) *
            (M - (∑ a, (q a : Real)) * (Real.exp 1 - 1)))) := by
  classical
  let Q : Real := ∑ a, (q a : Real)
  let c : Real := M - Q * (Real.exp 1 - 1)
  have hevent : MeasurableSet {x : Coord -> Real | exists a, M < x a} := by
    have hopen := isOpen_iUnion fun a : Coord =>
      isOpen_lt
        (continuous_const :
          Continuous (fun _ : Coord -> Real => M))
        (continuous_apply a)
    rw [show {x : Coord -> Real | exists a, M < x a} =
        ⋃ a : Coord, {x | M < x a} by
      ext x
      simp]
    exact hopen.measurableSet
  rw [scaledLaw, Measure.map_apply (by fun_prop) hevent]
  have hpre :
      scale K ⁻¹' {x : Coord -> Real | exists a, M < x a} ⊆
        ⋃ a : Coord, {n | (K : Real) * M <= (n a : Real)} := by
    intro n hn
    rcases hn with ⟨a, ha⟩
    have hKr : (0 : Real) < K := by exact_mod_cast hK
    have hle : (K : Real) * M <= n a := by
      unfold scale at ha
      simpa [mul_comm] using
        (lt_of_lt_of_le ((lt_div_iff₀ hKr).mp ha) (le_refl _)).le
    exact Set.mem_iUnion_of_mem a hle
  calc
    countLaw q K
        (scale K ⁻¹' {x : Coord -> Real | exists a, M < x a}) <=
        countLaw q K
          (⋃ a : Coord, {n | (K : Real) * M <= (n a : Real)}) :=
      measure_mono hpre
    _ <= ∑ a : Coord,
        countLaw q K {n | (K : Real) * M <= (n a : Real)} :=
      measure_iUnion_fintype_le (countLaw q K) _
    _ <= ∑ _a : Coord,
        ENNReal.ofReal (Real.exp (-(K : Real) * c)) := by
      apply Finset.sum_le_sum
      intro a ha
      apply (countLaw_coordinate_upper_tail q K a M 1 (by norm_num)).trans
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      dsimp [c, Q]
      have hqa :
          (q a : Real) <= ∑ b, (q b : Real) :=
        Finset.single_le_sum
          (fun b hb => NNReal.coe_nonneg (q b))
          (Finset.mem_univ a)
      have hexp : 0 <= Real.exp 1 - 1 :=
        sub_nonneg.mpr (Real.one_le_exp (by norm_num))
      calc
        (K : Real) *
            (-1 * M + (q a : Real) * (Real.exp 1 - 1)) <=
            (K : Real) *
              (-1 * M + (∑ b, (q b : Real)) *
                (Real.exp 1 - 1)) := by
          gcongr
        _ = -(K : Real) * c := by
          dsimp [c, Q]
          ring
    _ <= ENNReal.ofReal
        (((Fintype.card Coord + 1 : Nat) : Real) *
          Real.exp (-(K : Real) * c)) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      gcongr
      exact_mod_cast Nat.le_add_right (Fintype.card Coord) 1

/-- Exponential upper tail for leaving a positive coordinate box. -/
theorem coordinate_box_compl_upper_bound
    (q : Coord -> NNReal) (M : Real) :
    limsup
        (scaledLogMass (scaledLaw q)
          {x | exists a, M < x a}) atTop <=
      -((M - (∑ a, (q a : Real)) * (Real.exp 1 - 1) : Real) : EReal) := by
  apply limsup_of_subexponential_bound
    (mu := scaledLaw q) (event := {x | exists a, M < x a})
    (A := fun _ => (Fintype.card Coord + 1 : Nat))
    (c := M - (∑ a, (q a : Real)) * (Real.exp 1 - 1))
  · intro K hK
    positivity
  · exact fun K hK => coordinate_box_compl_mass_le q M K hK
  · exact tendsto_const_div_atTop_nhds_zero_nat _

/-- Exponential tightness in the finite Euclidean array space. -/
theorem exponential_tightness (q : Coord -> NNReal) (L : Real) :
    exists C : Set (Coord -> Real), IsCompact C /\
      limsup (scaledLogMass (scaledLaw q) C.compl) atTop <= -(L : EReal) := by
  classical
  let Q : Real := ∑ a, (q a : Real)
  obtain ⟨m, hm⟩ :=
    exists_nat_ge (max 0 (L + Q * (Real.exp 1 - 1)))
  let C : Set (Coord -> Real) :=
    {x | forall a, x a ∈ Icc (0 : Real) (m : Real)}
  let tail : Set (Coord -> Real) :=
    {x | exists a, (m : Real) < x a}
  have hC : IsCompact C := by
    dsimp [C]
    exact isCompact_pi_infinite fun _ => isCompact_Icc
  refine ⟨C, hC, ?_⟩
  have htailmeas : MeasurableSet tail := by
    dsimp [tail]
    have hopen := isOpen_iUnion fun a : Coord =>
      isOpen_lt
        (continuous_const :
          Continuous (fun _ : Coord -> Real => (m : Real)))
        (continuous_apply a)
    rw [show {x : Coord -> Real | exists a, (m : Real) < x a} =
        ⋃ a : Coord, {x | (m : Real) < x a} by
      ext x
      simp]
    exact hopen.measurableSet
  have hmass :
      forall K : Nat, 0 < K ->
        scaledLaw q K C.compl = scaledLaw q K tail := by
    intro K hK
    have hpre :
        scale K ⁻¹' C.compl = scale K ⁻¹' tail := by
      dsimp [C, tail]
      ext n
      constructor
      · intro hn
        have hn' :
            scale K n ∉
              {x : Coord -> Real |
                forall a, x a ∈ Icc (0 : Real) (m : Real)} := hn
        by_contra htail
        apply hn'
        intro a
        refine ⟨?_, le_of_not_gt (not_exists.mp htail a)⟩
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · intro htail
        have htail' : exists a, (m : Real) < scale K n a := htail
        have hn' :
            scale K n ∉
              {x : Coord -> Real |
                forall a, x a ∈ Icc (0 : Real) (m : Real)} := by
          intro hcube
          obtain ⟨a, ha⟩ := htail'
          exact (not_lt_of_ge (hcube a).2) ha
        exact hn'
    unfold scaledLaw
    calc
      (Measure.map (scale K) (countLaw q K)) C.compl =
          countLaw q K (scale K ⁻¹' C.compl) :=
        Measure.map_apply (by fun_prop) hC.isClosed.measurableSet.compl
      _ = countLaw q K (scale K ⁻¹' tail) := congrArg _ hpre
      _ = (Measure.map (scale K) (countLaw q K)) tail :=
        (Measure.map_apply (by fun_prop) htailmeas).symm
  have hlogeq :
      scaledLogMass (scaledLaw q) C.compl =
        scaledLogMass (scaledLaw q) tail := by
    funext K
    unfold scaledLogMass
    rw [hmass (K + 1) (by omega)]
  rw [hlogeq]
  refine (coordinate_box_compl_upper_bound q (m : Real)).trans ?_
  apply EReal.neg_le_neg_iff.mpr
  apply EReal.coe_le_coe_iff.mpr
  change L <= (m : Real) - Q * (Real.exp 1 - 1)
  apply (le_sub_iff_add_le).2
  exact le_trans (le_max_right _ _) hm

theorem log_two_poly_prefactor_tendsto_zero (m d : Nat) :
    Tendsto
      (fun K =>
        Real.log
            (2 * ((((K * m + 1) ^ d : Nat) : Real))) /
          (K : Real))
      atTop (nhds 0) := by
  have hpoly := log_poly_prefactor_tendsto_zero m d
  have htwo :
      Tendsto (fun K : Nat => Real.log 2 / (K : Real))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hsum := htwo.add hpoly
  simpa only [zero_add] using hsum.congr' (Eventually.of_forall fun K => by
    rw [Real.log_mul (by norm_num) (by positivity)]
    ring)

/-- Closed-set upper bound at every real level below the rate infimum. -/
theorem closed_upper_bound_real
    (q : Coord -> NNReal) (F : Set (Coord -> Real)) (hF : IsClosed F)
    (c : Real) (hc : ENNReal.ofReal c <= rateInf (action q) F) :
    limsup (scaledLogMass (scaledLaw q) F) atTop <= -(c : EReal) := by
  classical
  let d : Nat := Fintype.card Coord
  let Q : Real := ∑ a, (q a : Real)
  obtain ⟨m, hm⟩ := exists_nat_ge (c + Q * (Real.exp 1 - 1))
  let box : Set (Coord -> Real) := {x | forall a, x a <= (m : Real)}
  let C : Set (Coord -> Real) := F ∩ box
  have hbox : IsClosed box := by
    dsimp [box]
    rw [show {x : Coord -> Real | forall a, x a <= (m : Real)} =
        ⋂ a : Coord, {x | x a <= (m : Real)} by
      ext x
      simp]
    exact isClosed_iInter fun a =>
      isClosed_le (continuous_apply a) continuous_const
  have hCmeas : MeasurableSet C :=
    (hF.inter hbox).measurableSet
  have hCbound : forall x, x ∈ C -> forall a, x a <= m := by
    intro x hx a
    exact hx.2 a
  have hrate_mono :
      rateInf (action q) F <= rateInf (action q) C := by
    unfold rateInf
    apply le_sInf
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact sInf_le ⟨x, hx.1, rfl⟩
  have hcC : ENNReal.ofReal c <= rateInf (action q) C :=
    hc.trans hrate_mono
  have htailc :
      c <= (m : Real) - Q * (Real.exp 1 - 1) := by
    exact (le_sub_iff_add_le).2 hm
  let bigM : Nat := m + d + 2
  apply limsup_of_subexponential_bound
    (mu := scaledLaw q) (event := F)
    (A := fun K =>
      2 * (((K * bigM + 1) ^ (d + 1) : Nat) : Real))
    (c := c)
  · intro K hK
    positivity
  · intro K hK
    let tail : Set (Coord -> Real) :=
      {x | exists a, (m : Real) < x a}
    have hsubset : F ⊆ C ∪ tail := by
      intro x hxF
      by_cases hxbox : forall a, x a <= (m : Real)
      · exact Or.inl ⟨hxF, hxbox⟩
      · right
        push_neg at hxbox
        exact hxbox
    have hbounded := bounded_mass_le q C hCmeas m hCbound c hcC K hK
    have htail := coordinate_box_compl_mass_le q (m : Real) K hK
    have hbase :
        K * m + 1 <= K * bigM + 1 := by
      have hmM : m <= bigM := by
        dsimp [bigM]
        omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left K hmM) 1
    have hbigpos : 0 < K * bigM + 1 := by omega
    have hpoly :
        (K * m + 1) ^ d <= (K * bigM + 1) ^ (d + 1) :=
      (Nat.pow_le_pow_left hbase d).trans
        (Nat.pow_le_pow_right hbigpos (Nat.le_add_right d 1))
    have hconst :
        d + 1 <= (K * bigM + 1) ^ (d + 1) := by
      have hdbase : d + 1 <= K * bigM + 1 := by
        have hdM : d + 1 <= bigM := by
          dsimp [bigM]
          omega
        have hMmul : bigM <= K * bigM := by
          simpa using Nat.mul_le_mul_right bigM hK
        exact (hdM.trans hMmul).trans (Nat.le_add_right _ 1)
      exact hdbase.trans (Nat.le_pow (by omega))
    let B : Real := (((K * bigM + 1) ^ (d + 1) : Nat) : Real)
    let e : Real := Real.exp (-(K : Real) * c)
    have he : 0 <= e := (Real.exp_pos _).le
    have hbounded' :
        scaledLaw q K C <= ENNReal.ofReal (B * e) := by
      exact hbounded.trans (ENNReal.ofReal_le_ofReal (by
        dsimp [B, e, d]
        gcongr))
    have htail_exp :
        Real.exp (-(K : Real) *
            ((m : Real) -
              (∑ a, (q a : Real)) * (Real.exp 1 - 1))) <= e := by
      apply Real.exp_le_exp.mpr
      dsimp [e, Q] at htailc ⊢
      exact mul_le_mul_of_nonpos_left htailc (neg_nonpos.mpr (Nat.cast_nonneg K))
    have htail' :
        scaledLaw q K tail <= ENNReal.ofReal (B * e) := by
      apply htail.trans
      apply ENNReal.ofReal_le_ofReal
      dsimp [tail, B, e, d] at *
      calc
        ((Fintype.card Coord + 1 : Nat) : Real) *
            Real.exp (-(K : Real) *
              ((m : Real) -
                (∑ a, (q a : Real)) * (Real.exp 1 - 1))) <=
            ((Fintype.card Coord + 1 : Nat) : Real) * e := by
          gcongr
        _ <= (((K * bigM + 1) ^ (Fintype.card Coord + 1) : Nat) : Real) *
              e := by
          gcongr
    calc
      scaledLaw q K F <= scaledLaw q K (C ∪ tail) :=
        measure_mono hsubset
      _ <= scaledLaw q K C + scaledLaw q K tail :=
        measure_union_le C tail
      _ <= ENNReal.ofReal (B * e) + ENNReal.ofReal (B * e) :=
        add_le_add hbounded' htail'
      _ = ENNReal.ofReal ((2 * B) * e) := by
        calc
          ENNReal.ofReal (B * e) + ENNReal.ofReal (B * e) =
              2 * ENNReal.ofReal (B * e) := (two_mul _).symm
          _ = ENNReal.ofReal 2 * ENNReal.ofReal (B * e) := by norm_num
          _ = ENNReal.ofReal (2 * (B * e)) :=
            (ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 2)).symm
          _ = ENNReal.ofReal ((2 * B) * e) := by ring
  · exact log_two_poly_prefactor_tendsto_zero bigM (d + 1)

theorem limsup_scaledLogMass_nonpos (q : Coord -> NNReal)
    (event : Set (Coord -> Real)) :
    limsup (scaledLogMass (scaledLaw q) event) atTop <= 0 := by
  calc
    limsup (scaledLogMass (scaledLaw q) event) atTop <=
        limsup (fun _ : Nat => (0 : EReal)) atTop :=
      limsup_le_limsup (Eventually.of_forall
        (scaledLogMass_nonpos q event))
    _ = 0 := limsup_const (0 : EReal)

/-- Exact closed-set upper bound with the repository's `EReal` and
`rateInf` conventions, including an infinite rate infimum. -/
theorem closed_upper_bound
    (q : Coord -> NNReal) (F : Set (Coord -> Real)) (hF : IsClosed F) :
    limsup (scaledLogMass (scaledLaw q) F) atTop <=
      -(rateInf (action q) F : EReal) := by
  let L := limsup (scaledLogMass (scaledLaw q) F) atTop
  let r := rateInf (action q) F
  have hL : L <= 0 := limsup_scaledLogMass_nonpos q F
  have hminus : 0 <= -L := EReal.neg_nonneg.mpr hL
  by_cases hr : r = (Top.top : ENNReal)
  · have hall : forall s : NNReal, (s : ENNReal) <= (-L).toENNReal := by
      intro s
      have hs :
          L <= -(((s : Real)) : EReal) := by
        apply closed_upper_bound_real q F hF (s : Real)
        rw [ENNReal.ofReal_coe_nnreal]
        change (s : ENNReal) <= r
        rw [hr]
        exact le_top
      have hs' : (((s : Real)) : EReal) <= -L := by
        simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hs
      have hto := EReal.toENNReal_le_toENNReal hs'
      simpa using hto
    have htop : (-L).toENNReal = (Top.top : ENNReal) :=
      ENNReal.eq_top_of_forall_nnreal_le hall
    have hminusTop : -L = (Top.top : EReal) := by
      have hcoe := EReal.coe_toENNReal hminus
      rw [htop] at hcoe
      exact hcoe.symm
    have hLbot : L = (Bot.bot : EReal) := by
      have hneg := congrArg (fun z : EReal => -z) hminusTop
      simpa using hneg
    simp [L, r, hr, hLbot]
  · have hreal :
        L <= -((r.toReal : Real) : EReal) :=
      closed_upper_bound_real q F hF r.toReal
        (by
          change ENNReal.ofReal r.toReal <= r
          exact (ENNReal.ofReal_toReal hr).le)
    have hcoe : ((r.toReal : Real) : EReal) = (r : EReal) :=
      EReal.coe_ennreal_toReal hr
    simpa [L, r, hcoe] using hreal

/-- Compact-set upper bound, exposed separately for finite-dimensional
transport arguments. -/
theorem compact_upper_bound
    (q : Coord -> NNReal) (C : Set (Coord -> Real)) (hC : IsCompact C) :
    limsup (scaledLogMass (scaledLaw q) C) atTop <=
      -(rateInf (action q) C : EReal) :=
  closed_upper_bound q C hC.isClosed

/-- Unconditional finite-dimensional good LDP for an arbitrary finite
array of independent Poisson counts with parameters `K * q a`. -/
theorem goodLDP (q : Coord -> NNReal) :
    IsGoodLDP (Coord -> Real) (scaledLaw q) (action q) := by
  refine ⟨isCompact_action_sublevel q, ?_⟩
  intro event hevent
  refine ⟨?_, ?_, ?_⟩
  · calc
      -(rateInf (action q) (interior event) : EReal) <=
          liminf
            (scaledLogMass (scaledLaw q) (interior event)) atTop :=
        open_lower_bound q (interior event) isOpen_interior
      _ <= liminf (scaledLogMass (scaledLaw q) event) atTop := by
        apply liminf_le_liminf
        · exact Eventually.of_forall fun K =>
          EReal.div_le_div_right_of_nonneg (by positivity)
            (ENNReal.log_le_log
              (measure_mono interior_subset))
        · exact Filter.isBoundedUnder_of
            ⟨(Bot.bot : EReal), fun _ => bot_le⟩
        · exact Filter.isCoboundedUnder_ge_of_le atTop
            (scaledLogMass_nonpos q event)
  · exact liminf_le_limsup
      (Filter.isBoundedUnder_of_eventually_le
        (Eventually.of_forall (scaledLogMass_nonpos q event)))
      (Filter.isBoundedUnder_of
        ⟨(Bot.bot : EReal), fun _ => bot_le⟩)
  · calc
      limsup (scaledLogMass (scaledLaw q) event) atTop <=
          limsup
            (scaledLogMass (scaledLaw q) (closure event)) atTop := by
        apply limsup_le_limsup
        · exact Eventually.of_forall fun K =>
          EReal.div_le_div_right_of_nonneg (by positivity)
            (ENNReal.log_le_log
              (measure_mono subset_closure))
        · exact Filter.isCoboundedUnder_le_of_le atTop
            (fun _ => bot_le)
        · exact Filter.isBoundedUnder_of_eventually_le
            (Eventually.of_forall
              (scaledLogMass_nonpos q (closure event)))
      _ <= -(rateInf (action q) (closure event) : EReal) :=
        closed_upper_bound q (closure event) isClosed_closure

end PoissonFiniteArray

namespace PoissonFinitePartition

variable {Cell : Type u} {Buffer : Type v} {Server : Type w}
variable [Fintype Cell] [Fintype Buffer] [Fintype Server]

abbrev Array := Cell × Server × Buffer -> Real
abbrev CountArray := Cell × Server × Buffer -> Nat

/-- The intensity of partition cell `(i,j,k)`. -/
noncomputable def intensity (dt : Cell -> NNReal)
    (phi : Server -> Buffer -> NNReal) :
    Cell × Server × Buffer -> NNReal :=
  fun a => dt a.1 * phi a.2.1 a.2.2

/-- Exact finite product count law with parameters `K * dt_i * phi_jk`. -/
noncomputable def countLaw (dt : Cell -> NNReal)
    (phi : Server -> Buffer -> NNReal) (K : Nat) :
    Measure (Cell × Server × Buffer -> Nat) :=
  PoissonFiniteArray.countLaw (intensity dt phi) K

/-- Scaled finite product law on the Euclidean array space. -/
noncomputable def scaledLaw (dt : Cell -> NNReal)
    (phi : Server -> Buffer -> NNReal) (K : Nat) :
    Measure (Cell × Server × Buffer -> Real) :=
  PoissonFiniteArray.scaledLaw (intensity dt phi) K

/-- Partition action, with all zero-width and zero-rate conventions inherited
from `poissonCost`. -/
noncomputable def action (dt : Cell -> NNReal)
    (phi : Server -> Buffer -> NNReal)
    (x : Cell × Server × Buffer -> Real) : ENNReal :=
  PoissonFiniteArray.action (intensity dt phi) x

instance countLaw_isProbabilityMeasure
    (dt : Cell -> NNReal) (phi : Server -> Buffer -> NNReal) (K : Nat) :
    IsProbabilityMeasure (countLaw dt phi K) := by
  unfold countLaw
  infer_instance

instance scaledLaw_isProbabilityMeasure
    (dt : Cell -> NNReal) (phi : Server -> Buffer -> NNReal) (K : Nat) :
    IsProbabilityMeasure (scaledLaw dt phi K) := by
  unfold scaledLaw
  infer_instance

/-- Exact singleton law of the independent partition count array. -/
theorem countLaw_singleton
    (dt : Cell -> NNReal) (phi : Server -> Buffer -> NNReal)
    (K : Nat) (n : CountArray) :
    countLaw dt phi K {n} =
      ∏ a, ENNReal.ofReal
        (Real.exp (-((K : Real) * (intensity dt phi a : Real))) *
          ((K : Real) * (intensity dt phi a : Real)) ^ n a /
            Nat.factorial (n a)) :=
  PoissonFiniteArray.countLaw_singleton (intensity dt phi) K n

/-- Exact singleton law after coordinatewise scaling. -/
theorem scaledLaw_singleton
    (dt : Cell -> NNReal) (phi : Server -> Buffer -> NNReal)
    (K : Nat) (n : CountArray) (hK : 0 < K) :
    scaledLaw dt phi K {PoissonFiniteArray.scale K n} =
      countLaw dt phi K {n} :=
  PoissonFiniteArray.scaledLaw_singleton (intensity dt phi) K n hK

theorem isCompact_action_sublevel
    (dt : Cell -> NNReal) (phi : Server -> Buffer -> NNReal) (c : Real) :
    IsCompact {x | action dt phi x <= ENNReal.ofReal c} :=
  PoissonFiniteArray.isCompact_action_sublevel (intensity dt phi) c

/-- Open-set lower bound for the partition array law. -/
theorem open_lower_bound
    (dt : Cell -> NNReal) (phi : Server -> Buffer -> NNReal)
    (G : Set Array) (hG : IsOpen G) :
    -(rateInf (action dt phi) G : EReal) <=
      liminf (scaledLogMass (scaledLaw dt phi) G) atTop :=
  PoissonFiniteArray.open_lower_bound (intensity dt phi) G hG

/-- Closed-set upper bound for the partition array law. -/
theorem closed_upper_bound
    (dt : Cell -> NNReal) (phi : Server -> Buffer -> NNReal)
    (F : Set Array) (hF : IsClosed F) :
    limsup (scaledLogMass (scaledLaw dt phi) F) atTop <=
      -(rateInf (action dt phi) F : EReal) :=
  PoissonFiniteArray.closed_upper_bound (intensity dt phi) F hF

theorem compact_upper_bound
    (dt : Cell -> NNReal) (phi : Server -> Buffer -> NNReal)
    (C : Set Array) (hC : IsCompact C) :
    limsup (scaledLogMass (scaledLaw dt phi) C) atTop <=
      -(rateInf (action dt phi) C : EReal) :=
  PoissonFiniteArray.compact_upper_bound (intensity dt phi) C hC

theorem exponential_tightness
    (dt : Cell -> NNReal) (phi : Server -> Buffer -> NNReal) (L : Real) :
    exists C : Set Array, IsCompact C /\
      limsup (scaledLogMass (scaledLaw dt phi) C.compl) atTop <=
        -(L : EReal) :=
  PoissonFiniteArray.exponential_tightness (intensity dt phi) L

/-- Unconditional finite-partition good LDP at speed `K`, allowing every
combination of zero cell widths and zero coordinate rates. -/
theorem goodLDP
    (dt : Cell -> NNReal) (phi : Server -> Buffer -> NNReal) :
    IsGoodLDP Array (scaledLaw dt phi) (action dt phi) :=
  PoissonFiniteArray.goodLDP (intensity dt phi)

end PoissonFinitePartition

end StateDepMOR
/-!
# Concrete path space for the calendar-time Poisson LDP

This file begins the construction needed to instantiate
`SamplePathLDPStatement` with the calendar-time primitives from
`PoissonProcessExecution`.

The topology below is generated by the usual Skorokhod `J1` neighborhoods:
paths may be compared after an increasing homeomorphic change of time, and
both the uniform time error and uniform path error must be small.
-/

open scoped ENNReal Topology
open Filter MeasureTheory ProbabilityTheory Set

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

namespace PoissonSamplePath

/-- The compact time interval on which sample paths are observed. -/
abbrev Horizon (T : Real) := Set.Icc (0 : Real) T

/-- A finite matrix of real coordinates. -/
abbrev FiniteMatrix (Server : Type v) (Buffer : Type u) :=
  Server -> Buffer -> Real

/-- Right continuity on `[0,T]`, expressed in the subspace topology. -/
def IsRightContinuous
    (T : Real) (f : Horizon T -> FiniteMatrix Server Buffer) : Prop :=
  forall t : Horizon T, (t : Real) < T ->
    ContinuousWithinAt f (Set.Ici t) t

/-- Existence of a finite left limit at every time in `(0,T]`. -/
def HasLeftLimits
    (T : Real) (f : Horizon T -> FiniteMatrix Server Buffer) : Prop :=
  forall t : Horizon T, 0 < (t : Real) ->
    exists y : FiniteMatrix Server Buffer,
      Tendsto f (nhdsWithin t (Set.Iio t)) (nhds y)

/-- Genuine finite-matrix, coordinatewise nonnegative cadlag paths on
`[0,T]`. -/
structure Path (T : Real) where
  toFun : Horizon T -> FiniteMatrix Server Buffer
  nonnegative : forall t j k, 0 <= toFun t j k
  rightContinuous : IsRightContinuous T toFun
  leftLimits : HasLeftLimits T toFun

instance (T : Real) :
    CoeFun (Path (Buffer := Buffer) (Server := Server) T)
      (fun _ => Horizon T -> FiniteMatrix Server Buffer) :=
  ⟨Path.toFun⟩

@[ext]
theorem Path.ext {T : Real}
    {x y : Path (Buffer := Buffer) (Server := Server) T}
    (h : x.toFun = y.toFun) : x = y := by
  cases x
  cases y
  cases h
  rfl

/-- The identically zero cadlag path. -/
def zeroPath (T : Real) :
    Path (Buffer := Buffer) (Server := Server) T where
  toFun := fun _ _ _ => 0
  nonnegative := by simp
  rightContinuous := by
    intro t ht
    exact continuousWithinAt_const
  leftLimits := by
    intro t ht
    exact ⟨fun _ _ => 0, tendsto_const_nhds⟩

/-- Clamp a real time to `[0,T]`. -/
def clampToHorizon (T : Real) (hT : 0 <= T) (t : Real) : Horizon T :=
  ⟨max 0 (min t T), by
    constructor
    · exact le_max_left _ _
    · exact max_le hT (min_le_right _ _)⟩

/-- Read a horizon path as the repository's real-indexed `MatrixPath`,
holding it constant before zero and after `T`. For the irrelevant case
`T < 0`, where the active statement is false, use the zero matrix path. -/
noncomputable def asMatrix (T : Real)
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    MatrixPath Server Buffer := by
  classical
  exact if hT : 0 <= T then
      fun t => x (clampToHorizon T hT t)
    else
      fun _ _ _ => 0

@[simp]
theorem asMatrix_apply_of_mem {T t : Real} (hT : 0 <= T)
    (ht : t ∈ Set.Icc (0 : Real) T)
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    asMatrix T x t = x ⟨t, ht⟩ := by
  simp only [asMatrix, hT, dite_true, clampToHorizon]
  congr
  simp [ht.1, ht.2]

/-- Increasing homeomorphic changes of time used in the `J1` topology. -/
structure TimeChange (T : Real) where
  toHomeomorph : Horizon T ≃ₜ Horizon T
  strictMono : StrictMono toHomeomorph

instance (T : Real) : CoeFun (TimeChange T) (fun _ => Horizon T -> Horizon T) :=
  ⟨fun e => e.toHomeomorph⟩

/-- The identity time change. -/
def identityTimeChange (T : Real) : TimeChange T where
  toHomeomorph := Homeomorph.refl _
  strictMono := strictMono_id

/-- Composition of admissible time changes. The value of `e.trans f` at
`t` is `f (e t)`. -/
def TimeChange.trans {T : Real}
    (e f : TimeChange T) : TimeChange T where
  toHomeomorph := e.toHomeomorph.trans f.toHomeomorph
  strictMono := f.strictMono.comp e.strictMono

@[simp]
theorem TimeChange.trans_apply {T : Real}
    (e f : TimeChange T) (t : Horizon T) :
    e.trans f t = f (e t) :=
  rfl

/-- Uniform displacement of a time change. -/
noncomputable def timeError {T : Real} (e : TimeChange T) : ENNReal :=
  iSup fun t : Horizon T => ENNReal.ofReal |((e t : Horizon T) : Real) - (t : Real)|

set_option maxRecDepth 10000

private def NodeLT (p q : Prod Real Real) : Prop :=
  p.1 < q.1 /\ p.2 < q.2

/-- Corresponding finite source and target time nodes for a piecewise-affine
time change. -/
structure FiniteTimeNodes (T : Real) where
  nodes : List (Prod Real Real)
  nodes_strict : nodes.Pairwise NodeLT
  first_node : nodes.head? = some (0, 0)
  last_node : nodes.getLast? = some (T, T)

namespace FiniteTimeNodes

def sourceTimes {T : Real} (d : FiniteTimeNodes T) : List Real :=
  d.nodes.map Prod.fst

def targetTimes {T : Real} (d : FiniteTimeNodes T) : List Real :=
  d.nodes.map Prod.snd

noncomputable def tailNodes {T : Real} (d : FiniteTimeNodes T) :
    List (Prod Real Real) :=
  (List.head?_eq_some_iff.mp d.first_node).choose

theorem nodes_eq_cons_tailNodes {T : Real} (d : FiniteTimeNodes T) :
    d.nodes = (0, 0) :: d.tailNodes :=
  (List.head?_eq_some_iff.mp d.first_node).choose_spec

noncomputable def beforeLastNodes {T : Real} (d : FiniteTimeNodes T) :
    List (Prod Real Real) :=
  (List.getLast?_eq_some_iff.mp d.last_node).choose

theorem nodes_eq_beforeLast_append {T : Real} (d : FiniteTimeNodes T) :
    d.nodes = d.beforeLastNodes ++ [(T, T)] :=
  (List.getLast?_eq_some_iff.mp d.last_node).choose_spec

@[simp]
theorem sourceTimes_length {T : Real} (d : FiniteTimeNodes T) :
    d.sourceTimes.length = d.nodes.length := by
  simp [sourceTimes]

@[simp]
theorem targetTimes_length {T : Real} (d : FiniteTimeNodes T) :
    d.targetTimes.length = d.nodes.length := by
  simp [targetTimes]

theorem sourceTimes_strict {T : Real} (d : FiniteTimeNodes T) :
    d.sourceTimes.Pairwise (fun x y => x < y) := by
  rw [sourceTimes, List.pairwise_map]
  exact d.nodes_strict.imp fun h => h.1

theorem targetTimes_strict {T : Real} (d : FiniteTimeNodes T) :
    d.targetTimes.Pairwise (fun x y => x < y) := by
  rw [targetTimes, List.pairwise_map]
  exact d.nodes_strict.imp fun h => h.2

@[simp]
theorem sourceTimes_head? {T : Real} (d : FiniteTimeNodes T) :
    d.sourceTimes.head? = some 0 := by
  simp [sourceTimes, nodes_eq_cons_tailNodes]

@[simp]
theorem targetTimes_head? {T : Real} (d : FiniteTimeNodes T) :
    d.targetTimes.head? = some 0 := by
  simp [targetTimes, nodes_eq_cons_tailNodes]

@[simp]
theorem sourceTimes_getLast? {T : Real} (d : FiniteTimeNodes T) :
    d.sourceTimes.getLast? = some T := by
  simp [sourceTimes, nodes_eq_beforeLast_append]

@[simp]
theorem targetTimes_getLast? {T : Real} (d : FiniteTimeNodes T) :
    d.targetTimes.getLast? = some T := by
  simp [targetTimes, nodes_eq_beforeLast_append]

private noncomputable def segment (p q : Prod Real Real) (t : Real) : Real :=
  p.2 + ((t - p.1) / (q.1 - p.1)) * (q.2 - p.2)

private theorem segment_left (p q : Prod Real Real) (_h : p.1 < q.1) :
    segment p q p.1 = p.2 := by
  simp [segment]

private theorem segment_right (p q : Prod Real Real) (h : p.1 < q.1) :
    segment p q q.1 = q.2 := by
  have hne : Not (q.1 - p.1 = 0) := sub_ne_zero.mpr h.ne'
  rw [segment, div_self hne]
  ring

private theorem segment_strictMono (p q : Prod Real Real)
    (hs : p.1 < q.1) (ht : p.2 < q.2) :
    StrictMono (segment p q) := by
  intro a b hab
  dsimp [segment]
  have hden : 0 < q.1 - p.1 := sub_pos.mpr hs
  have hrange : 0 < q.2 - p.2 := sub_pos.mpr ht
  have hratio : (a - p.1) / (q.1 - p.1) <
      (b - p.1) / (q.1 - p.1) := by
    exact (div_lt_div_iff_of_pos_right hden).2 (sub_lt_sub_right hab _)
  nlinarith

private theorem continuous_segment (p q : Prod Real Real) :
    Continuous (segment p q) := by
  unfold segment
  fun_prop

private theorem segment_displacement_le (p q : Prod Real Real)
    (hs : p.1 < q.1) {t : Real} (ht0 : p.1 <= t) (ht1 : t <= q.1) :
    |segment p q t - t| <= max |p.2 - p.1| |q.2 - q.1| := by
  let r := (t - p.1) / (q.1 - p.1)
  have hden : 0 < q.1 - p.1 := sub_pos.mpr hs
  have hr0 : 0 <= r := div_nonneg (sub_nonneg.mpr ht0) hden.le
  have hr1 : r <= 1 := by
    rw [div_le_one hden]
    linarith
  have hid :
      segment p q t - t =
        (1 - r) * (p.2 - p.1) + r * (q.2 - q.1) := by
    dsimp [segment, r]
    field_simp [ne_of_gt hden]
    ring
  rw [hid]
  calc
    |(1 - r) * (p.2 - p.1) + r * (q.2 - q.1)| <=
        |(1 - r) * (p.2 - p.1)| + |r * (q.2 - q.1)| :=
      abs_add_le _ _
    _ = (1 - r) * |p.2 - p.1| + r * |q.2 - q.1| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hr0,
        abs_of_nonneg (sub_nonneg.mpr hr1)]
    _ <= max |p.2 - p.1| |q.2 - q.1| := by
      have hp := le_max_left |p.2 - p.1| |q.2 - q.1|
      have hq := le_max_right |p.2 - p.1| |q.2 - q.1|
      nlinarith

private noncomputable def interpolateFrom (p : Prod Real Real) :
    List (Prod Real Real) -> Real -> Real
  | [], _ => p.2
  | q :: qs, t =>
      if t <= q.1 then segment p q t else interpolateFrom q qs t

private theorem interpolateFrom_self (p : Prod Real Real)
    (qs : List (Prod Real Real)) (h : (p :: qs).Pairwise NodeLT) :
    interpolateFrom p qs p.1 = p.2 := by
  cases qs with
  | nil => simp [interpolateFrom]
  | cons q qs =>
      have hpq : NodeLT p q := (List.pairwise_cons.mp h).1 q (by simp)
      simp [interpolateFrom, hpq.1.le, segment_left p q hpq.1]

private theorem continuous_interpolateFrom (p : Prod Real Real)
    (qs : List (Prod Real Real)) (h : (p :: qs).Pairwise NodeLT) :
    Continuous (interpolateFrom p qs) := by
  induction qs generalizing p with
  | nil =>
      simp only [interpolateFrom]
      fun_prop
  | cons q qs ih =>
      have hpq : NodeLT p q := (List.pairwise_cons.mp h).1 q (by simp)
      have hq : (q :: qs).Pairwise NodeLT := (List.pairwise_cons.mp h).2
      simp only [interpolateFrom]
      apply Continuous.if_le
      next => exact continuous_segment p q
      next => exact ih q hq
      next => fun_prop
      next => fun_prop
      next =>
        intro t ht
        subst t
        rw [segment_right p q hpq.1]
        exact (interpolateFrom_self q qs hq).symm

private theorem interpolateFrom_eq_of_ge (p q : Prod Real Real)
    (qs : List (Prod Real Real)) (hpq : NodeLT p q)
    (hq : (q :: qs).Pairwise NodeLT) {t : Real} (ht : q.1 <= t) :
    interpolateFrom p (q :: qs) t = interpolateFrom q qs t := by
  rcases ht.eq_or_lt with h | h
  case inl =>
    subst t
    simp [interpolateFrom, segment_right p q hpq.1,
      interpolateFrom_self q qs hq]
  case inr =>
    simp [interpolateFrom, (not_le_of_gt h)]

private theorem strictMonoOn_interpolateFrom (p r : Prod Real Real)
    (qs : List (Prod Real Real)) (h : (p :: qs).Pairwise NodeLT)
    (hlast : (p :: qs).getLast? = some r) :
    StrictMonoOn (interpolateFrom p qs) (Icc p.1 r.1) := by
  induction qs generalizing p with
  | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst r
      intro x hx y hy hxy
      have hx' : x = p.1 := le_antisymm hx.2 hx.1
      have hy' : y = p.1 := le_antisymm hy.2 hy.1
      subst x
      subst y
      exact (lt_irrefl _ hxy).elim
  | cons q qs ih =>
      have hpq : NodeLT p q := (List.pairwise_cons.mp h).1 q (by simp)
      have hq : (q :: qs).Pairwise NodeLT := (List.pairwise_cons.mp h).2
      have hlast' : (q :: qs).getLast? = some r := by
        simpa using hlast
      have hrmem : Membership.mem (q :: qs) r := by
        let before := (List.getLast?_eq_some_iff.mp hlast').choose
        have hbefore :=
          (List.getLast?_eq_some_iff.mp hlast').choose_spec
        rw [hbefore]
        simp
      have hqr : q.1 <= r.1 := by
        by_cases heq : r = q
        case pos =>
          subst r
          exact le_rfl
        case neg =>
          exact ((List.pairwise_cons.mp hq).1 r (by
            simpa [heq] using hrmem)).1.le
      have hmono := ih q hq hlast'
      intro x hx y hy hxy
      by_cases hyq : y <= q.1
      case pos =>
        have hxq : x <= q.1 := hxy.le.trans hyq
        simp only [interpolateFrom, if_pos hxq, if_pos hyq]
        exact segment_strictMono p q hpq.1 hpq.2 hxy
      case neg =>
        have hqy : q.1 < y := lt_of_not_ge hyq
        by_cases hqx : q.1 <= x
        case pos =>
          rw [interpolateFrom_eq_of_ge p q qs hpq hq hqx,
              interpolateFrom_eq_of_ge p q qs hpq hq hqy.le]
          exact hmono (And.intro hqx hx.2) (And.intro hqy.le hy.2) hxy
        case neg =>
          have hxq : x < q.1 := lt_of_not_ge hqx
          calc
            interpolateFrom p (q :: qs) x =
                segment p q x := by
                  simp [interpolateFrom, hxq.le]
            _ < segment p q q.1 :=
              segment_strictMono p q hpq.1 hpq.2 hxq
            _ = interpolateFrom q qs q.1 := by
              rw [segment_right p q hpq.1,
                interpolateFrom_self q qs hq]
            _ < interpolateFrom q qs y := by
              exact hmono (And.intro le_rfl hqr)
                (And.intro hqy.le hy.2) hqy
            _ = interpolateFrom p (q :: qs) y := by
              exact (interpolateFrom_eq_of_ge p q qs hpq hq hqy.le).symm

private theorem interpolateFrom_node (p r : Prod Real Real)
    (qs : List (Prod Real Real)) (h : (p :: qs).Pairwise NodeLT)
    (hr : Membership.mem (p :: qs) r) :
    interpolateFrom p qs r.1 = r.2 := by
  induction qs generalizing p with
  | nil =>
      simp only [List.mem_singleton] at hr
      subst r
      exact interpolateFrom_self p [] (by simp)
  | cons q qs ih =>
      have hpq : NodeLT p q := (List.pairwise_cons.mp h).1 q (by simp)
      have hq : (q :: qs).Pairwise NodeLT := (List.pairwise_cons.mp h).2
      rw [List.mem_cons] at hr
      rcases hr with (rfl | hr)
      case inl =>
        exact interpolateFrom_self r (q :: qs) h
      case inr =>
        by_cases hrq : r = q
        case pos =>
          subst r
          simp [interpolateFrom, segment_right p q hpq.1]
        case neg =>
          have hqr : NodeLT q r :=
            (List.pairwise_cons.mp hq).1 r (by
              simpa [hrq] using hr)
          rw [interpolateFrom_eq_of_ge p q qs hpq hq hqr.1.le]
          exact ih q hq hr

/-- The largest absolute displacement among the finitely many node pairs. -/
def maxNodeDisplacement {T : Real} (d : FiniteTimeNodes T) : Real :=
  d.nodes.foldr (fun p m => max |p.2 - p.1| m) 0

private theorem interpolateFrom_displacement_le (p r : Prod Real Real)
    (qs : List (Prod Real Real)) (h : (p :: qs).Pairwise NodeLT)
    (hlast : (p :: qs).getLast? = some r) {t : Real}
    (ht : Membership.mem (Icc p.1 r.1) t) :
    |interpolateFrom p qs t - t| <=
      (p :: qs).foldr (fun z m => max |z.2 - z.1| m) 0 := by
  induction qs generalizing p with
  | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hlast
      subst r
      have htt : t = p.1 := le_antisymm ht.2 ht.1
      subst t
      exact le_max_left _ _
  | cons q qs ih =>
      have hpq : NodeLT p q := (List.pairwise_cons.mp h).1 q (by simp)
      have hq : (q :: qs).Pairwise NodeLT := (List.pairwise_cons.mp h).2
      have hlast' : (q :: qs).getLast? = some r := by
        simpa using hlast
      by_cases htq : t <= q.1
      case pos =>
        rw [interpolateFrom, if_pos htq]
        calc
          |segment p q t - t| <=
              max |p.2 - p.1| |q.2 - q.1| :=
            segment_displacement_le p q hpq.1 ht.1 htq
          _ <= max |p.2 - p.1|
              ((q :: qs).foldr (fun z m => max |z.2 - z.1| m) 0) := by
            apply max_le_max_left
            exact le_max_left _ _
          _ = (p :: q :: qs).foldr
              (fun z m => max |z.2 - z.1| m) 0 := rfl
      case neg =>
        rw [interpolateFrom, if_neg htq]
        exact (ih q hq hlast'
          (And.intro (le_of_not_ge htq) ht.2)).trans
          (le_max_right _ _)

/-- The real piecewise-affine interpolation through all finite time nodes. -/
noncomputable def piecewiseAffine {T : Real} (d : FiniteTimeNodes T) :
    Real -> Real :=
  interpolateFrom (0, 0) d.nodes.tail

theorem continuous_piecewiseAffine {T : Real} (d : FiniteTimeNodes T) :
    Continuous d.piecewiseAffine := by
  rw [piecewiseAffine, nodes_eq_cons_tailNodes]
  exact continuous_interpolateFrom (0, 0) d.tailNodes (by
    simpa [nodes_eq_cons_tailNodes] using d.nodes_strict)

theorem piecewiseAffine_apply_node {T : Real} (d : FiniteTimeNodes T)
    (p : Prod Real Real) (hp : Membership.mem d.nodes p) :
    d.piecewiseAffine p.1 = p.2 := by
  rw [piecewiseAffine, nodes_eq_cons_tailNodes]
  exact interpolateFrom_node (0, 0) p d.tailNodes (by
    simpa [nodes_eq_cons_tailNodes] using d.nodes_strict) (by
      simpa [nodes_eq_cons_tailNodes] using hp)

@[simp]
theorem piecewiseAffine_zero {T : Real} (d : FiniteTimeNodes T) :
    d.piecewiseAffine 0 = 0 := by
  apply piecewiseAffine_apply_node d (0, 0)
  simp [nodes_eq_cons_tailNodes]

@[simp]
theorem piecewiseAffine_T {T : Real} (d : FiniteTimeNodes T) :
    d.piecewiseAffine T = T := by
  apply piecewiseAffine_apply_node d (T, T)
  simp [nodes_eq_beforeLast_append]

theorem strictMonoOn_piecewiseAffine {T : Real} (d : FiniteTimeNodes T) :
    StrictMonoOn d.piecewiseAffine (Icc 0 T) := by
  rw [piecewiseAffine, nodes_eq_cons_tailNodes]
  exact strictMonoOn_interpolateFrom (0, 0) (T, T) d.tailNodes
    (by simpa [nodes_eq_cons_tailNodes] using d.nodes_strict)
    (by simpa [nodes_eq_cons_tailNodes] using d.last_node)

theorem piecewiseAffine_displacement_le {T : Real} (d : FiniteTimeNodes T)
    {t : Real} (ht : Membership.mem (Icc 0 T) t) :
    |d.piecewiseAffine t - t| <= d.maxNodeDisplacement := by
  rw [piecewiseAffine, maxNodeDisplacement, nodes_eq_cons_tailNodes]
  exact interpolateFrom_displacement_le (0, 0) (T, T) d.tailNodes
    (by simpa [nodes_eq_cons_tailNodes] using d.nodes_strict)
    (by simpa [nodes_eq_cons_tailNodes] using d.last_node) ht

/-- Piecewise-affine interpolation as a self-map of the horizon. -/
noncomputable def piecewiseAffineHorizonMap {T : Real} (hT : 0 < T)
    (d : FiniteTimeNodes T) : Horizon T -> Horizon T :=
  fun t => Subtype.mk (d.piecewiseAffine t) (by
    have hmono := (strictMonoOn_piecewiseAffine d).monotoneOn
    constructor
    case left =>
      simpa using hmono (And.intro le_rfl hT.le)
        t.property t.property.1
    case right =>
      simpa using hmono t.property
        (And.intro hT.le le_rfl) t.property.2)

theorem strictMono_piecewiseAffineHorizonMap {T : Real} (hT : 0 < T)
    (d : FiniteTimeNodes T) :
    StrictMono (piecewiseAffineHorizonMap hT d) := by
  intro s t hst
  exact strictMonoOn_piecewiseAffine d s.property t.property hst

theorem surjective_piecewiseAffineHorizonMap {T : Real} (hT : 0 < T)
    (d : FiniteTimeNodes T) :
    Function.Surjective (piecewiseAffineHorizonMap hT d) := by
  intro y
  have hy : Membership.mem
      (Icc (d.piecewiseAffine 0) (d.piecewiseAffine T)) (y : Real) := by
    rw [piecewiseAffine_zero, piecewiseAffine_T]
    exact y.property
  have hIV :=
    intermediate_value_Icc hT.le (continuous_piecewiseAffine d).continuousOn hy
  let x := hIV.choose
  have hx := hIV.choose_spec.1
  have hxy := hIV.choose_spec.2
  exact Exists.intro (Subtype.mk x hx) (Subtype.ext hxy)

/-- The piecewise-affine time change carrying every source node to its
corresponding target node. -/
noncomputable def finitePiecewiseAffineTimeChange (T : Real) (hT : 0 < T)
    (d : FiniteTimeNodes T) : TimeChange T where
  toHomeomorph :=
    (StrictMono.orderIsoOfSurjective
      (piecewiseAffineHorizonMap hT d)
      (strictMono_piecewiseAffineHorizonMap hT d)
      (surjective_piecewiseAffineHorizonMap hT d)).toHomeomorph
  strictMono := strictMono_piecewiseAffineHorizonMap hT d

@[simp]
theorem finitePiecewiseAffineTimeChange_apply {T : Real} (hT : 0 < T)
    (d : FiniteTimeNodes T) (t : Horizon T) :
    (((finitePiecewiseAffineTimeChange T hT d) t : Horizon T) : Real) =
      d.piecewiseAffine t := rfl

theorem finitePiecewiseAffineTimeChange_apply_node {T : Real} (hT : 0 < T)
    (d : FiniteTimeNodes T) (p : Prod Real Real)
    (hp : Membership.mem d.nodes p)
    (hpH : Membership.mem (Icc 0 T) p.1) :
    (((finitePiecewiseAffineTimeChange T hT d) (Subtype.mk p.1 hpH) :
      Horizon T) : Real) = p.2 := by
  rw [finitePiecewiseAffineTimeChange_apply]
  exact piecewiseAffine_apply_node d p hp

theorem timeError_finitePiecewiseAffineTimeChange_le {T : Real}
    (hT : 0 < T) (d : FiniteTimeNodes T) :
    timeError (finitePiecewiseAffineTimeChange T hT d) <=
      ENNReal.ofReal d.maxNodeDisplacement := by
  unfold timeError
  apply iSup_le
  intro t
  rw [finitePiecewiseAffineTimeChange_apply]
  exact ENNReal.ofReal_le_ofReal
    (piecewiseAffine_displacement_le d t.property)

end FiniteTimeNodes

/-- Uniform finite-matrix discrepancy after applying a time change. -/
noncomputable def pathError {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T)
    (e : TimeChange T) : ENNReal :=
  iSup fun t : Horizon T =>
    iSup fun j : Server =>
      iSup fun k : Buffer =>
        ENNReal.ofReal |x (e t) j k - y t j k|

/-- Standard `J1` comparison cost for a fixed time change. -/
noncomputable def j1Cost {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T)
    (e : TimeChange T) : ENNReal :=
  max (timeError e) (pathError x y e)

/-- One directed Skorokhod `J1` gauge, obtained by taking the infimum over
all increasing homeomorphic changes of time. -/
noncomputable def directedJ1EDist {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T) : ENNReal :=
  ⨅ e : TimeChange T, j1Cost x y e

/-- The symmetric J1 gauge. The two directed terms are mathematically equal
by inversion of a time change; taking their maximum makes symmetry immediate
and does not change the J1 topology. -/
noncomputable def symmetricJ1EDist {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T) : ENNReal :=
  max (directedJ1EDist x y) (directedJ1EDist y x)

/-- The bounded Skorokhod J1 extended distance. Truncation at one only
changes balls of radius at least one and therefore preserves the J1
topology. -/
noncomputable def j1EDist {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T) : ENNReal :=
  symmetricJ1EDist x y ⊓ 1

def TimeChange.symm {T : Real} (e : TimeChange T) : TimeChange T where
  toHomeomorph := e.toHomeomorph.symm
  strictMono := by
    intro a b hab
    apply lt_of_not_ge
    intro h
    have hmono := e.strictMono.monotone h
    have hba : b <= a := by
      simpa using hmono
    exact (not_le_of_gt hab) hba

@[simp]
theorem TimeChange.symm_apply_apply {T : Real}
    (e : TimeChange T) (t : Horizon T) :
    e.symm (e t) = t :=
  e.toHomeomorph.left_inv t

@[simp]
theorem TimeChange.apply_symm_apply {T : Real}
    (e : TimeChange T) (t : Horizon T) :
    e (e.symm t) = t :=
  e.toHomeomorph.right_inv t

theorem timeError_symm_le {T : Real} (e : TimeChange T) :
    timeError e.symm <= timeError e := by
  unfold timeError
  apply iSup_le
  intro t
  have h :=
    le_iSup
      (fun s : Horizon T =>
        ENNReal.ofReal |((e s : Horizon T) : Real) - (s : Real)|)
      (e.symm t)
  simpa [abs_sub_comm] using h

theorem pathError_symm_le {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T)
    (e : TimeChange T) :
    pathError y x e.symm <= pathError x y e := by
  unfold pathError
  apply iSup_le
  intro t
  apply iSup_le
  intro j
  apply iSup_le
  intro k
  have h :=
    le_iSup
      (fun s : Horizon T =>
        iSup fun i : Server =>
          iSup fun q : Buffer =>
            ENNReal.ofReal |x (e s) i q - y s i q|)
      (e.symm t)
  have hj :=
    le_iSup
      (fun i : Server =>
        iSup fun q : Buffer =>
          ENNReal.ofReal
            |x (e (e.symm t)) i q - y (e.symm t) i q|)
      j
  have hk :=
    le_iSup
      (fun q : Buffer =>
        ENNReal.ofReal
          |x (e (e.symm t)) j q - y (e.symm t) j q|)
      k
  have hk' :
      ENNReal.ofReal |y (e.symm t) j k - x t j k| <=
        iSup fun q : Buffer =>
          ENNReal.ofReal
            |x (e (e.symm t)) j q - y (e.symm t) j q| := by
    simpa [abs_sub_comm] using hk
  exact hk'.trans (hj.trans h)

/-- One explicit time alignment bounds both directed terms in the symmetric
J1 gauge. -/
theorem symmetricJ1EDist_le_j1Cost {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T)
    (e : TimeChange T) :
    symmetricJ1EDist x y <= j1Cost x y e := by
  unfold symmetricJ1EDist
  apply max_le
  · exact iInf_le (fun f : TimeChange T => j1Cost x y f) e
  · calc
      directedJ1EDist y x <= j1Cost y x e.symm :=
        iInf_le (fun f : TimeChange T => j1Cost y x f) e.symm
      _ <= j1Cost x y e := by
        unfold j1Cost
        exact max_le_max (timeError_symm_le e)
          (pathError_symm_le x y e)

theorem timeError_trans_le {T : Real}
    (e f : TimeChange T) :
    timeError (f.trans e) <= timeError e + timeError f := by
  unfold timeError
  apply iSup_le
  intro t
  rw [TimeChange.trans_apply]
  calc
    ENNReal.ofReal
        |((e (f t) : Horizon T) : Real) - (t : Real)| <=
      ENNReal.ofReal
        (|((e (f t) : Horizon T) : Real) - ((f t : Horizon T) : Real)| +
          |((f t : Horizon T) : Real) - (t : Real)|) := by
            apply ENNReal.ofReal_le_ofReal
            exact abs_sub_le _ _ _
    _ = ENNReal.ofReal
          |((e (f t) : Horizon T) : Real) -
            ((f t : Horizon T) : Real)| +
        ENNReal.ofReal
          |((f t : Horizon T) : Real) - (t : Real)| := by
            rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    _ <= timeError e + timeError f := by
      apply add_le_add
      · exact le_iSup (fun q : Horizon T =>
          ENNReal.ofReal
            |((e q : Horizon T) : Real) - (q : Real)|) (f t)
      · exact le_iSup (fun q : Horizon T =>
          ENNReal.ofReal
            |((f q : Horizon T) : Real) - (q : Real)|) t

theorem pathError_trans_le {T : Real}
    (x y z : Path (Buffer := Buffer) (Server := Server) T)
    (e f : TimeChange T) :
    pathError x z (f.trans e) <=
      pathError x y e + pathError y z f := by
  unfold pathError
  apply iSup_le
  intro t
  apply iSup_le
  intro j
  apply iSup_le
  intro k
  rw [TimeChange.trans_apply]
  calc
    ENNReal.ofReal |x (e (f t)) j k - z t j k| <=
      ENNReal.ofReal
        (|x (e (f t)) j k - y (f t) j k| +
          |y (f t) j k - z t j k|) := by
            apply ENNReal.ofReal_le_ofReal
            exact abs_sub_le _ _ _
    _ = ENNReal.ofReal |x (e (f t)) j k - y (f t) j k| +
        ENNReal.ofReal |y (f t) j k - z t j k| := by
          rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    _ <= pathError x y e + pathError y z f := by
      apply add_le_add
      · exact le_trans
          (le_iSup (fun q : Buffer =>
            ENNReal.ofReal |x (e (f t)) j q - y (f t) j q|) k)
          (le_trans
            (le_iSup (fun i : Server =>
              iSup fun q : Buffer =>
                ENNReal.ofReal |x (e (f t)) i q - y (f t) i q|) j)
            (le_iSup (fun s : Horizon T =>
              iSup fun i : Server =>
                iSup fun q : Buffer =>
                  ENNReal.ofReal |x (e s) i q - y s i q|) (f t)))
      · exact le_trans
          (le_iSup (fun q : Buffer =>
            ENNReal.ofReal |y (f t) j q - z t j q|) k)
          (le_trans
            (le_iSup (fun i : Server =>
              iSup fun q : Buffer =>
                ENNReal.ofReal |y (f t) i q - z t i q|) j)
            (le_iSup (fun s : Horizon T =>
              iSup fun i : Server =>
                iSup fun q : Buffer =>
                  ENNReal.ofReal |y (f s) i q - z s i q|) t))

theorem j1Cost_trans_le {T : Real}
    (x y z : Path (Buffer := Buffer) (Server := Server) T)
    (e f : TimeChange T) :
    j1Cost x z (f.trans e) <= j1Cost x y e + j1Cost y z f := by
  unfold j1Cost
  apply max_le
  · exact (timeError_trans_le e f).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (pathError_trans_le x y z e f).trans
      (add_le_add (le_max_right _ _) (le_max_right _ _))

@[simp]
theorem directedJ1EDist_self {T : Real}
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    directedJ1EDist x x = 0 := by
  apply le_antisymm
  · refine (iInf_le (fun e : TimeChange T => j1Cost x x e)
      (identityTimeChange T)).trans ?_
    simp [j1Cost, timeError, pathError, identityTimeChange]
  · exact bot_le

theorem directedJ1EDist_triangle {T : Real}
    (x y z : Path (Buffer := Buffer) (Server := Server) T) :
    directedJ1EDist x z <=
      directedJ1EDist x y + directedJ1EDist y z := by
  unfold directedJ1EDist
  apply ENNReal.le_iInf_add_iInf
  intro e f
  exact (iInf_le (fun g : TimeChange T => j1Cost x z g)
    (f.trans e)).trans (j1Cost_trans_le x y z e f)

@[simp]
theorem symmetricJ1EDist_self {T : Real}
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    symmetricJ1EDist x x = 0 := by
  simp [symmetricJ1EDist]

theorem symmetricJ1EDist_comm {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T) :
    symmetricJ1EDist x y = symmetricJ1EDist y x := by
  simp [symmetricJ1EDist, max_comm]

theorem symmetricJ1EDist_triangle {T : Real}
    (x y z : Path (Buffer := Buffer) (Server := Server) T) :
    symmetricJ1EDist x z <=
      symmetricJ1EDist x y + symmetricJ1EDist y z := by
  unfold symmetricJ1EDist
  apply max_le
  · exact (directedJ1EDist_triangle x y z).trans
      (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (directedJ1EDist_triangle z y x).trans
      ((add_le_add (le_max_right _ _) (le_max_right _ _)).trans_eq
        (add_comm _ _))

private theorem inf_one_add_inf_one (a b : ENNReal) :
    (a + b) ⊓ 1 <= (a ⊓ 1) + (b ⊓ 1) := by
  by_cases ha : 1 <= a
  · calc
      (a + b) ⊓ 1 <= 1 := inf_le_right
      _ <= 1 + (b ⊓ 1) := le_add_of_nonneg_right bot_le
      _ = (a ⊓ 1) + (b ⊓ 1) := by rw [inf_eq_right.mpr ha]
  · by_cases hb : 1 <= b
    · calc
        (a + b) ⊓ 1 <= 1 := inf_le_right
        _ <= (a ⊓ 1) + 1 := le_add_of_nonneg_left bot_le
        _ = (a ⊓ 1) + (b ⊓ 1) := by rw [inf_eq_right.mpr hb]
    · rw [inf_eq_left.mpr (le_of_not_ge ha),
        inf_eq_left.mpr (le_of_not_ge hb)]
      exact inf_le_left

@[simp]
theorem j1EDist_self {T : Real}
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    j1EDist x x = 0 := by
  simp [j1EDist]

theorem j1EDist_comm {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T) :
    j1EDist x y = j1EDist y x := by
  simp [j1EDist, symmetricJ1EDist_comm]

theorem j1EDist_triangle {T : Real}
    (x y z : Path (Buffer := Buffer) (Server := Server) T) :
    j1EDist x z <= j1EDist x y + j1EDist y z := by
  unfold j1EDist
  exact (inf_le_inf (symmetricJ1EDist_triangle x y z) le_rfl).trans
    (inf_one_add_inf_one _ _)

theorem j1EDist_le_one {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T) :
    j1EDist x y <= 1 :=
  inf_le_right

/-- An open ball for the standard Skorokhod `J1` distance. -/
noncomputable def j1Ball {T : Real}
    (x : Path (Buffer := Buffer) (Server := Server) T) (epsilon : Real) :
    Set (Path (Buffer := Buffer) (Server := Server) T) :=
  {y | j1EDist x y < ENNReal.ofReal epsilon}

/-- The pseudo-emetric structure induced by the proved bounded J1
distance. -/
noncomputable def pathPseudoEMetricSpace (T : Real) :
    PseudoEMetricSpace
      (Path (Buffer := Buffer) (Server := Server) T) :=
  PseudoEMetricSpace.ofEDist j1EDist j1EDist_self
    j1EDist_comm j1EDist_triangle

/-- The J1 distance is bounded, so its extended metric gives a genuine
pseudometric topology. -/
noncomputable instance pathPseudoMetricSpace (T : Real) :
    PseudoMetricSpace
      (Path (Buffer := Buffer) (Server := Server) T) := by
  letI : PseudoEMetricSpace
      (Path (Buffer := Buffer) (Server := Server) T) :=
    pathPseudoEMetricSpace T
  exact PseudoEMetricSpace.toPseudoMetricSpace fun x y =>
    ne_of_lt ((j1EDist_le_one x y).trans_lt ENNReal.one_lt_top)

/-- The declared J1 neighborhoods are exactly the open extended-metric
balls of the proved J1 pseudometric. -/
theorem j1Ball_eq_eball {T : Real}
    (x : Path (Buffer := Buffer) (Server := Server) T) (epsilon : Real) :
    j1Ball x epsilon = Metric.eball x (ENNReal.ofReal epsilon) := by
  ext y
  simp only [j1Ball, Set.mem_setOf_eq, Metric.mem_eball]
  rw [j1EDist_comm]
  rfl

private theorem timeChange_fix_rightEndpoint {T : Real} (hT : 0 <= T)
    (e : TimeChange T) :
    e (Subtype.mk T (by exact mem_Icc.mpr ⟨hT, le_rfl⟩)) =
      Subtype.mk T (by exact mem_Icc.mpr ⟨hT, le_rfl⟩) := by
  let tT : Horizon T := ⟨T, hT, le_rfl⟩
  obtain ⟨s, hs⟩ := e.toHomeomorph.surjective tT
  have hse : s <= tT := s.property.2
  have hmono : e s <= e tT := e.strictMono.monotone hse
  rw [hs] at hmono
  apply Subtype.ext
  exact le_antisymm (e tT).property.2 hmono

private theorem exists_j1Cost_lt_of_directed_eq_zero {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T)
    (hxy : directedJ1EDist x y = 0) {eta : Real} (heta : 0 < eta) :
    exists e : TimeChange T, j1Cost x y e < ENNReal.ofReal eta := by
  have hlt : directedJ1EDist x y < ENNReal.ofReal eta := by
    rw [hxy]
    exact ENNReal.ofReal_pos.mpr heta
  simpa only [directedJ1EDist, iInf_lt_iff] using hlt

private theorem time_displacement_lt_of_cost_lt {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T)
    (e : TimeChange T) {eta : Real} (heta : 0 < eta)
    (he : j1Cost x y e < ENNReal.ofReal eta) (t : Horizon T) :
    abs (((e t : Horizon T) : Real) - (t : Real)) < eta := by
  have hpoint :
      ENNReal.ofReal
          (abs (((e t : Horizon T) : Real) - (t : Real))) <=
        timeError e :=
    le_iSup
      (fun s : Horizon T =>
        ENNReal.ofReal
          (abs (((e s : Horizon T) : Real) - (s : Real)))) t
  have hlt : ENNReal.ofReal
      (abs (((e t : Horizon T) : Real) - (t : Real))) <
      ENNReal.ofReal eta :=
    hpoint.trans_lt ((le_max_left _ _).trans_lt he)
  exact (ENNReal.ofReal_lt_ofReal_iff heta).mp hlt

private theorem coordinate_error_lt_of_cost_lt {T : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T)
    (e : TimeChange T) {eta : Real} (heta : 0 < eta)
    (he : j1Cost x y e < ENNReal.ofReal eta)
    (t : Horizon T) (j : Server) (k : Buffer) :
    abs (x (e t) j k - y t j k) < eta := by
  have hk :
      ENNReal.ofReal (abs (x (e t) j k - y t j k)) <=
        iSup fun q : Buffer =>
          ENNReal.ofReal (abs (x (e t) j q - y t j q)) :=
    le_iSup
      (fun q : Buffer =>
        ENNReal.ofReal (abs (x (e t) j q - y t j q))) k
  have hj :
      (iSup fun q : Buffer =>
          ENNReal.ofReal (abs (x (e t) j q - y t j q))) <=
        iSup fun i : Server =>
          iSup fun q : Buffer =>
            ENNReal.ofReal (abs (x (e t) i q - y t i q)) :=
    le_iSup
      (fun i : Server =>
        iSup fun q : Buffer =>
          ENNReal.ofReal (abs (x (e t) i q - y t i q))) j
  have ht :
      (iSup fun i : Server =>
          iSup fun q : Buffer =>
            ENNReal.ofReal (abs (x (e t) i q - y t i q))) <=
        pathError x y e :=
    le_iSup
      (fun s : Horizon T =>
        iSup fun i : Server =>
          iSup fun q : Buffer =>
            ENNReal.ofReal (abs (x (e s) i q - y s i q))) t
  have hlt :
      ENNReal.ofReal (abs (x (e t) j k - y t j k)) <
        ENNReal.ofReal eta :=
    (hk.trans (hj.trans ht)).trans_lt ((le_max_right _ _).trans_lt he)
  exact (ENNReal.ofReal_lt_ofReal_iff heta).mp hlt

private theorem coordinate_rightContinuous {T : Real}
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (t : Horizon T) (ht : (t : Real) < T) (j : Server) (k : Buffer) :
    ContinuousWithinAt (fun s : Horizon T => x s j k) (Ici t) t := by
  exact ((continuous_apply k).comp (continuous_apply j)).continuousAt
    |>.comp_continuousWithinAt (x.rightContinuous t ht)

/-- On a positive horizon the J1 gauge separates cadlag paths. -/
theorem j1EDist_eq_zero_imp_eq {T : Real} (hT : 0 < T)
    {x y : Path (Buffer := Buffer) (Server := Server) T}
    (hxy : j1EDist x y = 0) :
    x = y := by
  have hsym : symmetricJ1EDist x y = 0 := by
    have hmin : symmetricJ1EDist x y ⊓ 1 = 0 := by
      simpa only [j1EDist] using hxy
    rcases le_total (symmetricJ1EDist x y) 1 with hle | hge
    · rwa [inf_eq_left.mpr hle] at hmin
    · have hone : (1 : ENNReal) = 0 := by
        rwa [inf_eq_right.mpr hge] at hmin
      exact (one_ne_zero hone).elim
  have hdir : directedJ1EDist x y = 0 :=
    (max_eq_zero.mp (by simpa only [symmetricJ1EDist] using hsym)).1
  apply Path.ext
  funext t j k
  apply eq_of_forall_dist_le
  intro epsilon hepsilon
  by_cases ht : (t : Real) = T
  · obtain ⟨e, he⟩ :=
      exists_j1Cost_lt_of_directed_eq_zero x y hdir hepsilon
    have heT := timeChange_fix_rightEndpoint hT.le e
    have herr :=
      coordinate_error_lt_of_cost_lt x y e hepsilon he t j k
    have het : e t = t := by
      have htt :
          t = Subtype.mk T (by exact mem_Icc.mpr ⟨hT.le, le_rfl⟩) := by
        apply Subtype.ext
        exact ht
      simpa only [htt] using heT
    rw [het] at herr
    simpa only [Real.dist_eq] using herr.le
  · have htT : (t : Real) < T := lt_of_le_of_ne t.property.2 ht
    have hxc := coordinate_rightContinuous x t htT j k
    have hyc := coordinate_rightContinuous y t htT j k
    obtain ⟨deltaX, hdeltaX, hxdelta⟩ :=
      (Metric.continuousWithinAt_iff.mp hxc) (epsilon / 3) (by positivity)
    obtain ⟨deltaY, hdeltaY, hydelta⟩ :=
      (Metric.continuousWithinAt_iff.mp hyc) (epsilon / 3) (by positivity)
    let rho : Real := min (min deltaX deltaY) (T - (t : Real))
    have hrho : 0 < rho := by
      dsimp [rho]
      exact lt_min (lt_min hdeltaX hdeltaY) (sub_pos.mpr htT)
    let sReal : Real := (t : Real) + rho / 2
    have hs0 : 0 <= sReal := by
      dsimp [sReal]
      linarith [t.property.1, hrho]
    have hsT : sReal <= T := by
      have hrhoT : rho <= T - (t : Real) := min_le_right _ _
      dsimp [sReal]
      linarith
    let s : Horizon T := ⟨sReal, hs0, hsT⟩
    let eta : Real := min (rho / 4) (epsilon / 3)
    have heta : 0 < eta := by
      dsimp [eta]
      exact lt_min (by positivity) (by positivity)
    obtain ⟨e, he⟩ :=
      exists_j1Cost_lt_of_directed_eq_zero x y hdir heta
    have htime := time_displacement_lt_of_cost_lt x y e heta he s
    have hpath := coordinate_error_lt_of_cost_lt x y e heta he s j k
    have hetaRho : eta <= rho / 4 := min_le_left _ _
    have hetaEps : eta <= epsilon / 3 := min_le_right _ _
    have hts : t <= s := by
      apply Subtype.coe_le_coe.mp
      dsimp [s, sReal]
      linarith
    have hte : t <= e s := by
      apply Subtype.coe_le_coe.mp
      rw [abs_lt] at htime
      dsimp [s, sReal] at htime
      linarith
    have hdistS : dist s t < deltaY := by
      have hrhoY : rho <= deltaY :=
        (min_le_left (min deltaX deltaY) (T - (t : Real))).trans
          (min_le_right deltaX deltaY)
      rw [Subtype.dist_eq, Real.dist_eq]
      dsimp [s, sReal]
      rw [abs_of_nonneg]
      · linarith
      · linarith
    have hdistE : dist (e s) t < deltaX := by
      have hrhoX : rho <= deltaX :=
        (min_le_left (min deltaX deltaY) (T - (t : Real))).trans
          (min_le_left deltaX deltaY)
      rw [Subtype.dist_eq, Real.dist_eq]
      rw [abs_of_nonneg]
      · rw [abs_lt] at htime
        dsimp [s, sReal] at htime
        linarith
      · exact sub_nonneg.mpr (by exact_mod_cast hte)
    have hxclose := hxdelta (show e s ∈ Ici t from hte) hdistE
    have hyclose := hydelta (show s ∈ Ici t from hts) hdistS
    rw [Real.dist_eq] at hxclose hyclose
    have hxclose' :
        abs (x t j k - x (e s) j k) < epsilon / 3 := by
      simpa only [abs_sub_comm] using hxclose
    rw [Real.dist_eq]
    calc
      abs (x t j k - y t j k) <=
          abs (x t j k - x (e s) j k) +
            abs (x (e s) j k - y s j k) +
              abs (y s j k - y t j k) := by
        calc
          abs (x t j k - y t j k) =
              abs ((x t j k - x (e s) j k) +
                ((x (e s) j k - y s j k) +
                  (y s j k - y t j k))) := by ring_nf
          _ <= abs (x t j k - x (e s) j k) +
              abs ((x (e s) j k - y s j k) +
                (y s j k - y t j k)) := abs_add_le _ _
          _ <= abs (x t j k - x (e s) j k) +
              (abs (x (e s) j k - y s j k) +
                abs (y s j k - y t j k)) :=
            add_le_add le_rfl (abs_add_le _ _)
          _ = _ := by ring
      _ <= epsilon := by
        linarith [hxclose', hpath, hyclose, hetaEps]

/-- A genuine extended metric whose distance is exactly the bounded J1
gauge on every positive horizon. -/
noncomputable def pathEMetricSpace (T : Real) (hT : 0 < T) :
    EMetricSpace (Path (Buffer := Buffer) (Server := Server) T) where
  __ := pathPseudoEMetricSpace T
  eq_of_edist_eq_zero := by
    intro x y hxy
    exact j1EDist_eq_zero_imp_eq hT hxy

theorem pathEMetricSpace_edist (T : Real) (hT : 0 < T)
    (x y : Path (Buffer := Buffer) (Server := Server) T) :
    @edist _ (pathEMetricSpace T hT).toEDist x y = j1EDist x y :=
  rfl

/-- The corresponding finite metric structure. -/
noncomputable def pathMetricSpace (T : Real) (hT : 0 < T) :
    MetricSpace (Path (Buffer := Buffer) (Server := Server) T) := by
  letI : EMetricSpace (Path (Buffer := Buffer) (Server := Server) T) :=
    pathEMetricSpace T hT
  exact EMetricSpace.toMetricSpace fun x y =>
    ne_of_lt ((j1EDist_le_one x y).trans_lt ENNReal.one_lt_top)

theorem pathMetricSpace_edist (T : Real) (hT : 0 < T)
    (x y : Path (Buffer := Buffer) (Server := Server) T) :
    @edist _ (pathMetricSpace T hT).toPseudoMetricSpace.toEDist x y =
      j1EDist x y :=
  rfl

theorem pathMetricSpace_dist (T : Real) (hT : 0 < T)
    (x y : Path (Buffer := Buffer) (Server := Server) T) :
    @dist _ (pathMetricSpace T hT).toDist x y =
      ENNReal.toReal (j1EDist x y) :=
  rfl

/-- The genuine metric and the originally installed J1 pseudometric induce
definitionally the same topology. -/
theorem pathEMetricSpace_topology_eq_existing (T : Real) (hT : 0 < T) :
    (pathEMetricSpace (Buffer := Buffer) (Server := Server) T hT).toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace =
      (pathPseudoMetricSpace (Buffer := Buffer) (Server := Server) T).toUniformSpace.toTopologicalSpace :=
  rfl

theorem pathMetricSpace_topology_eq_existing (T : Real) (hT : 0 < T) :
    (pathMetricSpace (Buffer := Buffer) (Server := Server) T hT).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (pathPseudoMetricSpace (Buffer := Buffer) (Server := Server) T).toUniformSpace.toTopologicalSpace :=
  rfl

namespace J1EMetric

noncomputable scoped instance (T : Real) [hT : Fact (0 < T)] :
    EMetricSpace (Path (Buffer := Buffer) (Server := Server) T) :=
  pathEMetricSpace T hT.out

end J1EMetric

namespace J1Metric

noncomputable scoped instance (T : Real) [hT : Fact (0 < T)] :
    MetricSpace (Path (Buffer := Buffer) (Server := Server) T) :=
  pathMetricSpace T hT.out

end J1Metric

/-- A standard basic J1 neighborhood: one increasing homeomorphism makes
both the time displacement and path discrepancy smaller than `r`. -/
noncomputable def standardJ1EBall {T : Real}
    (x : Path (Buffer := Buffer) (Server := Server) T) (r : ENNReal) :
    Set (Path (Buffer := Buffer) (Server := Server) T) :=
  {y | exists e : TimeChange T, j1Cost x y e < r}

theorem mem_standardJ1EBall_iff {T : Real}
    {x y : Path (Buffer := Buffer) (Server := Server) T} {r : ENNReal} :
    y ∈ standardJ1EBall x r <->
      exists e : TimeChange T,
        timeError e < r /\ pathError x y e < r := by
  simp only [standardJ1EBall, Set.mem_setOf_eq, j1Cost, max_lt_iff]

theorem j1EDist_lt_iff_exists_timeChange {T : Real}
    {x y : Path (Buffer := Buffer) (Server := Server) T} {r : ENNReal}
    (hr : r <= 1) :
    j1EDist x y < r <->
      exists e : TimeChange T, j1Cost x y e < r := by
  constructor
  · intro h
    have hs : symmetricJ1EDist x y < r := by
      rcases (inf_lt_iff.mp
          (show symmetricJ1EDist x y ⊓ 1 < r from h)) with hs | h1
      · exact hs
      · exact (not_lt_of_ge hr h1).elim
    have hd : directedJ1EDist x y < r :=
      (le_max_left _ _).trans_lt hs
    simpa only [directedJ1EDist, iInf_lt_iff] using hd
  · rintro ⟨e, he⟩
    exact inf_le_left.trans_lt
      ((symmetricJ1EDist_le_j1Cost x y e).trans_lt he)

theorem standardJ1EBall_eq_eball {T : Real}
    (x : Path (Buffer := Buffer) (Server := Server) T) {r : ENNReal}
    (hr : r <= 1) :
    standardJ1EBall x r = Metric.eball x r := by
  ext y
  rw [Metric.mem_eball]
  change (exists e : TimeChange T, j1Cost x y e < r) <->
    j1EDist y x < r
  rw [j1EDist_comm y x, j1EDist_lt_iff_exists_timeChange hr]

/-- The metric neighborhoods are exactly the usual increasing-homeomorphism
Skorokhod J1 neighborhoods. -/
theorem standardJ1_nhds_basis (T : Real) (hT : 0 < T)
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    @Filter.HasBasis
      (Path (Buffer := Buffer) (Server := Server) T)
      ENNReal
      (@nhds _
        (pathEMetricSpace T hT).toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace x)
      (fun r => 0 < r /\ r <= 1)
      (standardJ1EBall x) := by
  letI : EMetricSpace
      (Path (Buffer := Buffer) (Server := Server) T) :=
    pathEMetricSpace T hT
  have hb := Metric.nhds_basis_eball
    (α := Path (Buffer := Buffer) (Server := Server) T) (x := x)
  have hb' := hb.restrict (q := fun r : ENNReal => r <= 1) (by
    intro r hr
    refine ⟨r ⊓ 1, ?_, inf_le_right, ?_⟩
    · exact lt_inf_iff.mpr ⟨hr, zero_lt_one⟩
    · exact Metric.eball_subset_eball inf_le_left)
  exact hb'.congr (fun _ => Iff.rfl) fun r hr =>
    (standardJ1EBall_eq_eball x hr.2).symm

theorem standardJ1_isOpen_iff (T : Real) (hT : 0 < T)
    (s : Set (Path (Buffer := Buffer) (Server := Server) T)) :
    @IsOpen _
        (pathEMetricSpace T hT).toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace s <->
      forall x, x ∈ s -> exists r : ENNReal,
        0 < r /\ r <= 1 /\ standardJ1EBall x r ⊆ s := by
  letI : EMetricSpace
      (Path (Buffer := Buffer) (Server := Server) T) :=
    pathEMetricSpace T hT
  rw [isOpen_iff_mem_nhds]
  constructor
  · intro hs x hx
    rcases (standardJ1_nhds_basis T hT x).mem_iff.mp (hs x hx) with
      ⟨r, hr, hrs⟩
    exact ⟨r, hr.1, hr.2, hrs⟩
  · intro hs x hx
    rcases hs x hx with ⟨r, hr0, hr1, hrs⟩
    exact (standardJ1_nhds_basis T hT x).mem_iff.mpr
      ⟨r, ⟨hr0, hr1⟩, hrs⟩

/-- The measurable structure is the Borel sigma algebra of the `J1`
topology. -/
noncomputable instance pathMeasurableSpace (T : Real) :
    MeasurableSpace (Path (Buffer := Buffer) (Server := Server) T) :=
  borel _

noncomputable instance pathBorelSpace (T : Real) :
    BorelSpace (Path (Buffer := Buffer) (Server := Server) T) where
  measurable_eq := rfl

/-- Restriction of the concrete scaled calendar input to `[0,T]`. -/
noncomputable def calendarInputFunction
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    Horizon T -> FiniteMatrix Server Buffer :=
  fun t j k => N.calendarScaledInput K omega t j k

/-- Canonical exponential samples have strictly positive interarrivals and
obey the renewal strong law in every marked coordinate. -/
def IsRegularSample
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) : Prop :=
  (forall j k r, 0 < omega j k r) /\
    forall j k,
      Tendsto
        (fun n : Nat =>
          Network.renewalEpoch (omega j k) n / (n : Real))
        atTop (nhds 1)

theorem unitExp_pos_ae :
    ∀ᵐ x ∂ProbabilityTheory.expMeasure 1, 0 < x := by
  rw [ae_iff]
  rw [show {a : Real | ¬0 < a} = Set.Iic 0 by ext a; simp]
  change ProbabilityTheory.expMeasure 1 (Set.Iic 0) = 0
  rw [← ProbabilityTheory.ofReal_cdf]
  simp [ProbabilityTheory.cdf_expMeasure_eq]

theorem calendarInterarrival_pos_ae
    (N : Network Buffer Server) (j : Server) (k : Buffer) (r : Nat) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure, 0 < omega j k r := by
  let f :
      Network.CalendarPoissonSample
        (Buffer := Buffer) (Server := Server) -> Real :=
    fun omega => omega j k r
  have hf : AEMeasurable f N.calendarPoissonMeasure := by
    apply Measurable.aemeasurable
    exact (measurable_pi_apply r).comp
      ((measurable_pi_apply k).comp (measurable_pi_apply j))
  apply MeasureTheory.ae_of_ae_map hf
  rw [show N.calendarPoissonMeasure.map f =
      ProbabilityTheory.expMeasure 1 by
    exact N.clockInterarrival_map j k r]
  exact unitExp_pos_ae

theorem regularSample_ae (N : Network Buffer Server) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure, IsRegularSample omega := by
  have hpos :
      ∀ᵐ omega ∂N.calendarPoissonMeasure,
        forall j k r, 0 < omega j k r := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro r
    exact calendarInterarrival_pos_ae N j k r
  filter_upwards [hpos, N.all_renewalEpoch_ratio_tendsto_ae] with
    omega homegaPos homegaSLLN
  exact ⟨homegaPos, homegaSLLN⟩

theorem measurable_renewalEpoch (n : Nat) :
    Measurable (fun clock : Network.UnitRateClockPath =>
      Network.renewalEpoch clock n) := by
  unfold Network.renewalEpoch
  fun_prop

private def totalCrossingPred (s : Real)
    (clock : Network.UnitRateClockPath) (n : Nat) : Prop :=
  s < Network.renewalEpoch clock n \/
    ((forall m, Not (s < Network.renewalEpoch clock m)) /\ n = 0)

private theorem totalCrossingPred_exists (s : Real)
    (clock : Network.UnitRateClockPath) :
    exists n, totalCrossingPred s clock n := by
  classical
  by_cases h : exists n, s < Network.renewalEpoch clock n
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨0, Or.inr ⟨not_exists.mp h, rfl⟩⟩

private noncomputable def firstCrossingIndex (s : Real)
    (clock : Network.UnitRateClockPath) : Nat := by
  classical
  exact Nat.find (totalCrossingPred_exists s clock)

private theorem measurableSet_totalCrossingPred (s : Real) (n : Nat) :
    MeasurableSet
      {clock : Network.UnitRateClockPath |
        totalCrossingPred s clock n} := by
  classical
  have hcross (m : Nat) :
      MeasurableSet
        {clock : Network.UnitRateClockPath |
          s < Network.renewalEpoch clock m} :=
    measurableSet_lt measurable_const (measurable_renewalEpoch m)
  have hnone :
      MeasurableSet
        {clock : Network.UnitRateClockPath |
          forall m, Not (s < Network.renewalEpoch clock m)} := by
    rw [show
      {clock : Network.UnitRateClockPath |
          forall m, Not (s < Network.renewalEpoch clock m)} =
        ⋂ m, {clock : Network.UnitRateClockPath |
          s < Network.renewalEpoch clock m}ᶜ by
      ext clock
      simp]
    exact MeasurableSet.iInter fun m => (hcross m).compl
  change MeasurableSet
    ({clock : Network.UnitRateClockPath |
        s < Network.renewalEpoch clock n} ∪
      ({clock : Network.UnitRateClockPath |
          forall m, Not (s < Network.renewalEpoch clock m)} ∩
        {clock : Network.UnitRateClockPath | n = 0}))
  exact (hcross n).union
    (hnone.inter (MeasurableSet.const (n = 0)))

private theorem measurable_firstCrossingIndex (s : Real) :
    Measurable (firstCrossingIndex s) := by
  classical
  exact measurable_find
    (totalCrossingPred_exists s)
    (measurableSet_totalCrossingPred s)

private theorem firstCrossingIndex_eq_find {s : Real}
    (clock : Network.UnitRateClockPath)
    (h : exists n, s < Network.renewalEpoch clock n) :
    firstCrossingIndex s clock = Nat.find h := by
  classical
  unfold firstCrossingIndex
  apply Nat.find_congr' (p := fun n => totalCrossingPred s clock n)
    (q := fun n => s < Network.renewalEpoch clock n)
  intro n
  simp only [totalCrossingPred]
  constructor
  · rintro (hn | ⟨hnone, -⟩)
    · exact hn
    · exact False.elim (not_exists.mpr hnone h)
  · exact Or.inl

theorem unitPoissonCount_eq_firstCrossingIndex
    (clock : Network.UnitRateClockPath) (s : Real) :
    Network.unitPoissonCount clock s =
      if 0 < s then firstCrossingIndex s clock - 1 else 0 := by
  classical
  by_cases hs : 0 < s
  · simp only [hs, if_true]
    by_cases hcross : exists n, s < Network.renewalEpoch clock n
    · rw [Network.unitPoissonCount_eq_find clock hs hcross,
        firstCrossingIndex_eq_find clock hcross]
    · have hpzero : totalCrossingPred s clock 0 :=
        Or.inr ⟨not_exists.mp hcross, rfl⟩
      have hfindzero : firstCrossingIndex s clock = 0 := by
        unfold firstCrossingIndex
        exact (Nat.find_eq_zero _).2 hpzero
      simp [Network.unitPoissonCount, hs, hcross, hfindzero]
  · simp [Network.unitPoissonCount, hs]

theorem measurable_unitPoissonCount (s : Real) :
    Measurable (fun clock : Network.UnitRateClockPath =>
      Network.unitPoissonCount clock s) := by
  rw [show (fun clock : Network.UnitRateClockPath =>
      Network.unitPoissonCount clock s) =
      fun clock =>
        if 0 < s then firstCrossingIndex s clock - 1 else 0 by
    funext clock
    exact unitPoissonCount_eq_firstCrossingIndex clock s]
  split_ifs
  · exact (measurable_of_countable (fun n : Nat => n - 1)).comp
      (measurable_firstCrossingIndex s)
  · fun_prop

theorem measurable_calendarTokenCount
    (N : Network Buffer Server) (K : PNat) (t : Real)
    (j : Server) (k : Buffer) :
    Measurable
      (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        N.calendarTokenCount K omega t j k) := by
  exact (measurable_unitPoissonCount
    (N.coordinateOperationalTime K t j k)).comp
      ((measurable_pi_apply k).comp (measurable_pi_apply j))

theorem measurable_calendarScaledInput
    (N : Network Buffer Server) (K : PNat) (t : Real)
    (j : Server) (k : Buffer) :
    Measurable
      (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        N.calendarScaledInput K omega t j k) := by
  unfold Network.calendarScaledInput
  exact
    ((MeasurableEmbedding.natCast (α := Real)).measurable.comp
      (measurable_calendarTokenCount N K t j k)).div_const _

theorem measurable_calendarScaledInputPath
    (N : Network Buffer Server) (K : PNat) :
    Measurable
      (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        N.calendarScaledInput K omega) := by
  apply measurable_pi_iff.mpr
  intro t
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro k
  exact measurable_calendarScaledInput N K t j k

theorem calendarTokenCount_coordinate_iIndep
    (N : Network Buffer Server) (K : PNat)
    (t : Sigma (fun _ : Server => Buffer) -> Real) :
    ProbabilityTheory.iIndepFun
      (fun p : Sigma (fun _ : Server => Buffer) =>
        fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
            N.calendarTokenCount K omega (t p) p.1 p.2)
      N.calendarPoissonMeasure := by
  have h := N.coordinateClock_iIndep.comp
    (fun p clock =>
      Network.unitPoissonCount clock
        (N.coordinateOperationalTime K (t p) p.1 p.2))
    (fun p => measurable_unitPoissonCount
      (N.coordinateOperationalTime K (t p) p.1 p.2))
  simpa [Function.comp_def, Network.calendarTokenCount] using h

theorem measurable_poissonCost (nominal : Real) :
    Measurable (poissonCost nominal) := by
  unfold poissonCost
  apply Measurable.ite
    (measurableSet_lt measurable_id measurable_const)
    measurable_const
  by_cases hnominal : nominal = 0
  · simp only [hnominal, ↓reduceIte]
    exact Measurable.ite (measurableSet_singleton 0)
      measurable_const measurable_const
  · simp only [hnominal, ↓reduceIte]
    fun_prop

theorem measurable_localRate
    (N : Network Buffer Server) (A : MatrixPath Server Buffer) :
    Measurable (fun t => N.localRate (pathDerivative A t)) := by
  classical
  unfold Network.localRate pathDerivative
  apply Finset.measurable_fun_sum
  intro j hj
  apply Finset.measurable_fun_sum
  intro k hk
  exact (measurable_poissonCost (N.phi j k)).comp
    (measurable_deriv (fun s => A s j k))

/-- Finite action forces a zero derivative almost everywhere in every
coordinate whose nominal Poisson rate is zero. -/
theorem poissonPathRate_ne_top_implies_zeroRate_deriv_ae
    (N : Network Buffer Server) (T : Real)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N T A) (⊤ : ENNReal))
    (j : Server) (k : Buffer) (hphi : N.phi j k = 0) :
    Filter.Eventually
      (fun t => pathDerivative A t j k = 0)
      (MeasureTheory.ae (volume.restrict (Icc 0 T))) := by
  classical
  have hvalid :=
    poissonPathRate_ne_top_implies_valid N T A hfinite
  have hintegral :
      Ne (∫⁻ t in Icc 0 T, N.localRate (pathDerivative A t))
        (⊤ : ENNReal) := by
    simpa [poissonPathRate, hvalid] using hfinite
  have hae :
      Filter.Eventually
        (fun t => N.localRate (pathDerivative A t) < (⊤ : ENNReal))
        (MeasureTheory.ae (volume.restrict (Icc 0 T))) :=
    ae_lt_top (measurable_localRate N A) hintegral
  filter_upwards [hae] with t ht
  exact N.localRate_ne_top_implies_zero_of_phi_eq_zero
    (pathDerivative A t) ht.ne j k hphi

/-- The preceding almost-everywhere derivative restriction and absolute
continuity force the whole zero-rate coordinate path to vanish. -/
theorem poissonPathRate_ne_top_implies_zeroRate_path
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N T A) (⊤ : ENNReal))
    (j : Server) (k : Buffer) (hphi : N.phi j k = 0) :
    forall t, t ∈ Icc (0 : Real) T -> A t j k = 0 := by
  classical
  let f : Real -> Real := fun t => A t j k
  have hvalid :=
    poissonPathRate_ne_top_implies_valid N T A hfinite
  have hac : AbsolutelyContinuousOnInterval f 0 T := hvalid.1 j k
  have hzero_restrict :
      Filter.Eventually
        (fun t => deriv f t = 0)
        (MeasureTheory.ae (volume.restrict (Icc 0 T))) := by
    simpa [f, pathDerivative] using
      poissonPathRate_ne_top_implies_zeroRate_deriv_ae
        N T A hfinite j k hphi
  have hzero :
      Filter.Eventually
        (fun t => t ∈ Icc (0 : Real) T -> deriv f t = 0)
        (MeasureTheory.ae volume) :=
    (ae_restrict_iff' measurableSet_Icc).mp hzero_restrict
  have hhas :
      Filter.Eventually
        (fun t => t ∈ uIcc (0 : Real) T -> HasDerivAt f 0 t)
        (MeasureTheory.ae volume) := by
    filter_upwards [hac.ae_differentiableAt, hzero] with t hdiff hz ht
    have htIcc : t ∈ Icc (0 : Real) T := by
      simpa [uIcc_of_le hT] using ht
    have hderiv : deriv f t = 0 := hz htIcc
    simpa [hderiv] using (hdiff ht).hasDerivAt
  obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero hhas
  intro t ht
  calc
    A t j k = f t := rfl
    _ = C := hC t (by simpa [uIcc_of_le hT] using ht)
    _ = f 0 := (hC 0 (by simp)).symm
    _ = 0 := hvalid.2 j k

theorem integrable_exp_natCast_poissonMeasure (r : NNReal) (t : Real) :
    Integrable (fun n : Nat => Real.exp (t * (n : Real)))
      (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have hs :
      Summable (fun n : Nat =>
        Real.exp (-(r : Real)) *
          (((r : Real) * Real.exp t) ^ n / Nat.factorial n)) :=
    (Real.summable_pow_div_factorial ((r : Real) * Real.exp t)).mul_left
      (Real.exp (-(r : Real)))
  apply hs.congr
  intro n
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  push_cast
  rw [show t * (n : Real) = (n : Real) * t by ring,
    Real.exp_nat_mul]
  ring

theorem poissonMeasure_mgf_natCast (r : NNReal) (t : Real) :
    ProbabilityTheory.mgf (fun n : Nat => (n : Real))
        (ProbabilityTheory.poissonMeasure r) t =
      Real.exp ((r : Real) * (Real.exp t - 1)) := by
  rw [ProbabilityTheory.mgf, ProbabilityTheory.integral_poissonMeasure]
  rw [show
      (∑' n : Nat,
        (Real.exp (-(r : Real)) * (r : Real) ^ n /
            Nat.factorial n) • Real.exp (t * (n : Real))) =
        Real.exp (-(r : Real)) *
          ∑' n : Nat,
            (((r : Real) * Real.exp t) ^ n / Nat.factorial n) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [smul_eq_mul]
    push_cast
    rw [show t * (n : Real) = (n : Real) * t by ring,
      Real.exp_nat_mul]
    ring]
  have hexp :
      (∑' n : Nat,
        (((r : Real) * Real.exp t) ^ n / Nat.factorial n)) =
        Real.exp ((r : Real) * Real.exp t) := by
    rw [← congrFun NormedSpace.exp_eq_tsum_div
      ((r : Real) * Real.exp t)]
    exact (congrFun Real.exp_eq_exp_ℝ _).symm
  rw [hexp, ← Real.exp_add]
  congr 1
  ring

theorem poissonMeasure_upper_tail_chernoff
    (r : NNReal) (a t : Real) (ht : 0 <= t) :
    (ProbabilityTheory.poissonMeasure r).real
        {n : Nat | a <= (n : Real)} <=
      Real.exp (-t * a + (r : Real) * (Real.exp t - 1)) := by
  calc
    (ProbabilityTheory.poissonMeasure r).real
        {n : Nat | a <= (n : Real)} <=
      Real.exp (-t * a) *
        ProbabilityTheory.mgf (fun n : Nat => (n : Real))
          (ProbabilityTheory.poissonMeasure r) t :=
      ProbabilityTheory.measure_ge_le_exp_mul_mgf a ht
        (integrable_exp_natCast_poissonMeasure r t)
    _ = Real.exp (-t * a + (r : Real) * (Real.exp t - 1)) := by
      rw [poissonMeasure_mgf_natCast, ← Real.exp_add]

theorem scaledPoisson_upper_tail_chernoff
    (K : Nat) (T : NNReal) (nominal M t : Real)
    (hnominal : 0 <= nominal) (ht : 0 <= t) :
    (ProbabilityTheory.poissonMeasure
        (scaledPoissonParameter K T nominal)).real
        {n : Nat | (K : Real) * M <= (n : Real)} <=
      Real.exp ((K : Real) *
        (-t * M + (T : Real) * nominal * (Real.exp t - 1))) := by
  convert poissonMeasure_upper_tail_chernoff
    (scaledPoissonParameter K T nominal) ((K : Real) * M) t ht using 1
  unfold scaledPoissonParameter
  simp only [NNReal.coe_mul, NNReal.coe_natCast]
  rw [Real.coe_toNNReal _ hnominal]
  congr 1
  ring

/-- The raw calendar input has a genuine probability law in the ambient
product measurable space. This is an intermediate law; the active theorem
uses its cadlag realization with the J1 Borel structure below. -/
noncomputable def calendarScaledInputProductLaw
    (N : Network Buffer Server) (K : PNat) :
    Measure (MatrixPath Server Buffer) :=
  N.calendarPoissonMeasure.map
    (fun omega => N.calendarScaledInput K omega)

instance calendarScaledInputProductLaw_isProbabilityMeasure
    (N : Network Buffer Server) (K : PNat) :
    IsProbabilityMeasure (calendarScaledInputProductLaw N K) := by
  unfold calendarScaledInputProductLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_calendarScaledInputPath N K).aemeasurable

theorem renewalEpoch_strictMono
    (clock : Network.UnitRateClockPath)
    (hpos : forall r, 0 < clock r) :
    StrictMono (Network.renewalEpoch clock) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [Network.renewalEpoch_succ]
  exact lt_add_of_pos_right _ (hpos n)

theorem renewalEpoch_tendsto_atTop
    (clock : Network.UnitRateClockPath)
    (hEpoch :
      Tendsto
        (fun n : Nat =>
          Network.renewalEpoch clock n / (n : Real))
        atTop (nhds 1)) :
    Tendsto (Network.renewalEpoch clock) atTop atTop := by
  have hprod :=
    hEpoch.pos_mul_atTop zero_lt_one
      (tendsto_natCast_atTop_atTop (R := Real))
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
  simp [Nat.ne_of_gt hn]

theorem renewalEpoch_eventually_crosses
    (clock : Network.UnitRateClockPath)
    (hEpoch :
      Tendsto
        (fun n : Nat =>
          Network.renewalEpoch clock n / (n : Real))
        atTop (nhds 1))
    (s : Real) :
    exists n, s < Network.renewalEpoch clock n :=
  ((renewalEpoch_tendsto_atTop clock hEpoch).eventually_gt_atTop s).exists

theorem unitPoissonCount_monotone
    (clock : Network.UnitRateClockPath)
    (hEpoch :
      Tendsto
        (fun n : Nat =>
          Network.renewalEpoch clock n / (n : Real))
        atTop (nhds 1)) :
    Monotone (Network.unitPoissonCount clock) := by
  intro s t hst
  by_cases hs : 0 < s
  · have ht : 0 < t := hs.trans_le hst
    let hsCross :
        Exists (fun n => s < Network.renewalEpoch clock n) :=
      renewalEpoch_eventually_crosses clock hEpoch s
    let htCross :
        Exists (fun n => t < Network.renewalEpoch clock n) :=
      renewalEpoch_eventually_crosses clock hEpoch t
    rw [Network.unitPoissonCount_eq_find clock hs hsCross,
      Network.unitPoissonCount_eq_find clock ht htCross]
    apply Nat.sub_le_sub_right
    apply Nat.find_min' hsCross
    exact hst.trans_lt (Nat.find_spec htCross)
  · have hsNonpos : s <= 0 := le_of_not_gt hs
    rw [Network.unitPoissonCount_of_nonpos clock hsNonpos]
    exact Nat.zero_le _

theorem unitPoissonCount_eventuallyEq_right
    (clock : Network.UnitRateClockPath)
    (hfirst : 0 < clock 0)
    (hEpoch :
      Tendsto
        (fun n : Nat =>
          Network.renewalEpoch clock n / (n : Real))
        atTop (nhds 1))
    (s : Real) :
    (fun u => Network.unitPoissonCount clock u) =ᶠ[nhdsWithin s (Set.Ici s)]
      fun _ => Network.unitPoissonCount clock s := by
  rcases lt_trichotomy s 0 with hsneg | rfl | hspos
  · filter_upwards
      [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hsneg),
        self_mem_nhdsWithin] with u hu huRight
    rw [Network.unitPoissonCount_of_nonpos clock hu.le,
      Network.unitPoissonCount_of_nonpos clock hsneg.le]
  · have hepochOne :
        0 < Network.renewalEpoch clock 1 := by
      simpa [Network.renewalEpoch_succ] using hfirst
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hepochOne),
        self_mem_nhdsWithin] with u hu huNonneg
    change 0 <= u at huNonneg
    rcases huNonneg.eq_or_lt with rfl | hupos
    · rfl
    · let hcross :
          Exists (fun n => u < Network.renewalEpoch clock n) :=
        ⟨1, hu⟩
      rw [Network.unitPoissonCount_eq_find clock hupos hcross,
        Network.unitPoissonCount_of_nonpos clock le_rfl]
      have hfind : Nat.find hcross = 1 := by
        apply le_antisymm
        · exact Nat.find_min' hcross hu
        · exact Network.one_le_find_renewal_crossing clock hupos hcross
      omega
  · let hsCross :
        Exists (fun n => s < Network.renewalEpoch clock n) :=
      renewalEpoch_eventually_crosses clock hEpoch s
    have hbound : s < Network.renewalEpoch clock (Nat.find hsCross) :=
      Nat.find_spec hsCross
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hbound),
        self_mem_nhdsWithin] with u hu hsu
    change s <= u at hsu
    have hupos : 0 < u := hspos.trans_le hsu
    let huCross :
        Exists (fun n => u < Network.renewalEpoch clock n) :=
      ⟨Nat.find hsCross, hu⟩
    rw [Network.unitPoissonCount_eq_find clock hupos huCross,
      Network.unitPoissonCount_eq_find clock hspos hsCross]
    have hfind : Nat.find huCross = Nat.find hsCross := by
      apply le_antisymm
      · exact Nat.find_min' huCross hu
      · by_contra hnot
        have hlt : Nat.find huCross < Nat.find hsCross :=
          Nat.lt_of_not_ge hnot
        exact (Nat.find_min hsCross hlt)
          (hsu.trans_lt (Nat.find_spec huCross))
    rw [hfind]

theorem unitPoissonCount_real_continuousWithinAt_right
    (clock : Network.UnitRateClockPath)
    (hfirst : 0 < clock 0)
    (hEpoch :
      Tendsto
        (fun n : Nat =>
          Network.renewalEpoch clock n / (n : Real))
        atTop (nhds 1))
    (scale s : Real) :
    ContinuousWithinAt
      (fun u => (Network.unitPoissonCount clock u : Real) / scale)
      (Set.Ici s) s := by
  apply tendsto_nhds_of_eventually_eq
  filter_upwards
    [unitPoissonCount_eventuallyEq_right clock hfirst hEpoch s] with u hu
  rw [hu]

theorem calendarInputFunction_nonnegative
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    forall t j k, 0 <= calendarInputFunction N T K omega t j k := by
  intro t j k
  simp only [calendarInputFunction, Network.calendarScaledInput]
  positivity

theorem calendarScaledInput_monotone
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hEpoch :
      forall j k,
        Tendsto
          (fun n : Nat =>
            Network.renewalEpoch (omega j k) n / (n : Real))
          atTop (nhds 1))
    (j : Server) (k : Buffer) :
    Monotone
      (fun t : Horizon T => N.calendarScaledInput K omega t j k) := by
  intro s t hst
  have htime :
      N.coordinateOperationalTime K s j k <=
        N.coordinateOperationalTime K t j k := by
    unfold Network.coordinateOperationalTime
    have hstReal : (s : Real) <= (t : Real) := hst
    exact mul_le_mul_of_nonneg_left
      (max_le_max_right 0 hstReal)
      (mul_nonneg (by positivity) (N.phi_nonneg j k))
  have hcount :=
    unitPoissonCount_monotone (omega j k) (hEpoch j k) htime
  simp only [Network.calendarScaledInput, Network.calendarTokenCount]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast hcount) (by positivity)

theorem calendarInputFunction_rightContinuous
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega) :
    IsRightContinuous T (calendarInputFunction N T K omega) := by
  intro t ht
  rw [continuousWithinAt_pi]
  intro j
  rw [continuousWithinAt_pi]
  intro k
  let g : Horizon T -> Real :=
    fun q => N.coordinateOperationalTime K q j k
  have hg : ContinuousWithinAt g (Set.Ici t) t := by
    apply Continuous.continuousWithinAt
    dsimp only [g, Network.coordinateOperationalTime]
    fun_prop
  have hmaps : Set.MapsTo g (Set.Ici t) (Set.Ici (g t)) := by
    intro q hq
    change g t <= g q
    dsimp only [g, Network.coordinateOperationalTime]
    have htq : (t : Real) <= (q : Real) := hq
    exact mul_le_mul_of_nonneg_left
      (max_le_max_right 0 htq)
      (mul_nonneg (by positivity) (N.phi_nonneg j k))
  have hcount :=
    unitPoissonCount_real_continuousWithinAt_right
      (omega j k) (hregular.1 j k 0) (hregular.2 j k)
      (((K : Nat) : Real)) (g t)
  have hcomp := hcount.comp hg hmaps
  simpa only [calendarInputFunction, Network.calendarScaledInput,
    Network.calendarTokenCount, g, Function.comp_def] using hcomp

theorem calendarInputFunction_leftLimits
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega) :
    HasLeftLimits T (calendarInputFunction N T K omega) := by
  intro t ht
  let f := calendarInputFunction N T K omega
  let y : FiniteMatrix Server Buffer :=
    fun j k => sSup ((fun q : Horizon T => f q j k) '' Set.Iio t)
  refine ⟨y, ?_⟩
  rw [tendsto_pi_nhds]
  intro j
  rw [tendsto_pi_nhds]
  intro k
  exact
    (calendarScaledInput_monotone N T K omega hregular.2 j k).tendsto_nhdsLT t

theorem calendarInputFunction_isPathData
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega) :
    (forall t j k, 0 <= calendarInputFunction N T K omega t j k) /\
      IsRightContinuous T (calendarInputFunction N T K omega) /\
      HasLeftLimits T (calendarInputFunction N T K omega) :=
  ⟨calendarInputFunction_nonnegative N T K omega,
    calendarInputFunction_rightContinuous N T K omega hregular,
    calendarInputFunction_leftLimits N T K omega hregular⟩

/-- Calendar input viewed in the bundled path space. On exceptional raw
clock sequences for which the total renewal construction is not cadlag, use
the zero path. The exceptional branch is null by `calendarPath_toFun_ae`. -/
noncomputable def calendarPath
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    Path (Buffer := Buffer) (Server := Server) T := by
  classical
  let f := calendarInputFunction N T K omega
  by_cases h :
      (forall t j k, 0 <= f t j k) /\
        IsRightContinuous T f /\ HasLeftLimits T f
  · exact
      { toFun := f
        nonnegative := h.1
        rightContinuous := h.2.1
        leftLimits := h.2.2 }
  · exact zeroPath T

theorem calendarPath_toFun_eq
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega) :
    (calendarPath N T K omega).toFun =
      calendarInputFunction N T K omega := by
  unfold calendarPath
  dsimp only
  split
  · rfl
  · rename_i hbad
    exact False.elim
      (hbad (calendarInputFunction_isPathData N T K omega hregular))

theorem calendarPath_toFun_ae
    (N : Network Buffer Server) (T : Real) (K : PNat) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      (calendarPath N T K omega).toFun =
        calendarInputFunction N T K omega := by
  filter_upwards [regularSample_ae N] with omega hregular
  exact calendarPath_toFun_eq N T K omega hregular

theorem calendarPath_apply_ae
    (N : Network Buffer Server) (T : Real) (K : PNat) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      forall t j k,
        calendarPath N T K omega t j k =
          N.calendarScaledInput K omega t j k := by
  filter_upwards [calendarPath_toFun_ae N T K] with omega homega
  intro t j k
  exact congrFun (congrFun (congrFun homega t) j) k

/-- Deterministic operational-time mesh for finite clock-prefix
approximations. -/
noncomputable def clockMesh (n : Nat) : Real :=
  (((n + 1 : Nat) : Real) ^ 2)⁻¹

theorem clockMesh_pos (n : Nat) : 0 < clockMesh n := by
  simp [clockMesh]
  positivity

theorem clockMesh_tendsto_zero :
    Tendsto clockMesh atTop (nhds 0) := by
  unfold clockMesh
  have hbase :
      Tendsto (fun n : Nat => (n : Real) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hinv := hbase.inv_tendsto_atTop
  convert hinv.pow 2 using 1 <;> simp [Nat.cast_add, inv_pow]

/-- Finite natural data recording rounded interarrivals in every marked
coordinate. -/
abbrev ClockPrefixCode (n : Nat) :=
  Server -> Buffer -> Fin n -> Nat

/-- Decode finite rounded interarrivals, completing every clock by unit
interarrivals. -/
noncomputable def decodeClockPrefix (n : Nat) (d : ClockPrefixCode
    (Buffer := Buffer) (Server := Server) n) :
    Network.CalendarPoissonSample (Buffer := Buffer) (Server := Server) :=
  fun j k r =>
    if hr : r < n then
      clockMesh n * ((d j k (⟨r, hr⟩ : Fin n) + 1 : Nat) : Real)
    else 1

/-- Round the first `n` interarrivals upward to the deterministic mesh. -/
noncomputable def encodeClockPrefix (n : Nat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    ClockPrefixCode (Buffer := Buffer) (Server := Server) n :=
  fun j k r =>
    Nat.floor (max (omega j k r) 0 / clockMesh n)

theorem measurable_encodeClockPrefix (n : Nat) :
    Measurable (encodeClockPrefix
      (Buffer := Buffer) (Server := Server) n) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro k
  apply measurable_pi_iff.mpr
  intro r
  apply Measurable.nat_floor
  exact (((measurable_pi_apply (r : Nat)).comp
    ((measurable_pi_apply k).comp (measurable_pi_apply j))).max
      measurable_const).div_const _

/-- Every decoded finite-data sample is regular; its unit tail supplies the
renewal strong-law limit. -/
theorem decodeClockPrefix_regular (n : Nat)
    (d : ClockPrefixCode (Buffer := Buffer) (Server := Server) n) :
    IsRegularSample (decodeClockPrefix n d) := by
  constructor
  · intro j k r
    unfold decodeClockPrefix
    split_ifs
    · exact mul_pos (clockMesh_pos n) (by positivity)
    · norm_num
  · intro j k
    let c : Real :=
      Network.renewalEpoch ((decodeClockPrefix n d) j k) n - (n : Real)
    have heq : (fun m : Nat =>
        Network.renewalEpoch ((decodeClockPrefix n d) j k) m /
          (m : Real)) =ᶠ[atTop]
        (fun m : Nat => 1 + c / (m : Real)) := by
      filter_upwards [eventually_ge_atTop n,
        eventually_gt_atTop (0 : Nat)] with m hnm hm
      have hsplit :
          Network.renewalEpoch ((decodeClockPrefix n d) j k) m =
            Network.renewalEpoch ((decodeClockPrefix n d) j k) n +
              (m - n : Nat) := by
        rw [Network.renewalEpoch]
        rw [← Finset.sum_range_add_sum_Ico _ hnm]
        congr 1
        calc
          (Finset.Ico n m).sum
              (fun x => (decodeClockPrefix n d) j k x) =
              (Finset.Ico n m).sum (fun _x => (1 : Real)) := by
                apply Finset.sum_congr rfl
                intro r hr
                simp only [decodeClockPrefix]
                rw [dif_neg (not_lt_of_ge (Finset.mem_Ico.mp hr).1)]
          _ = (m - n : Nat) := by simp
      rw [hsplit]
      dsimp only [c]
      rw [Nat.cast_sub hnm]
      have hm0 : Ne (m : Real) 0 := by positivity
      field_simp [hm0]
      ring
    apply Tendsto.congr' heq.symm
    have hcdiv :
        Tendsto (fun m : Nat => c / (m : Real)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using tendsto_const_nhds.add hcdiv

/-- The finite-data calendar path approximant. -/
noncomputable def delayedCalendarPath
    (N : Network Buffer Server) (T : Real) (K : PNat) (n : Nat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    Path (Buffer := Buffer) (Server := Server) T :=
  calendarPath N T K
    (decodeClockPrefix n (encodeClockPrefix n omega))

/-- Each finite clock-prefix approximant is measurable in the actual J1
Borel space because it factors through a countable finite array. -/
theorem delayedCalendarPath_aemeasurable
    (N : Network Buffer Server) (T : Real) (K : PNat) (n : Nat) :
    AEMeasurable (delayedCalendarPath N T K n)
      N.calendarPoissonMeasure := by
  let F : ClockPrefixCode (Buffer := Buffer) (Server := Server) n ->
      Path (Buffer := Buffer) (Server := Server) T :=
    fun d => calendarPath N T K (decodeClockPrefix n d)
  have hF : Measurable F := measurable_of_countable F
  exact (hF.comp (measurable_encodeClockPrefix n)).aemeasurable

/-- Turn a natural index into a positive system size. At every index used by
`scaledLogMass`, namely `K + 1`, this is exactly that index. -/
def positiveSize (K : Nat) : PNat :=
  ⟨max K 1, lt_of_lt_of_le Nat.zero_lt_one (le_max_right K 1)⟩

@[simp]
theorem positiveSize_succ_val (K : Nat) :
    ((positiveSize (K + 1) : PNat) : Nat) = K + 1 := by
  simp [positiveSize]

/-- Mapped law of the actual calendar-time scaled input at speed `K + 1`. -/
noncomputable def calendarPathLaw
    (N : Network Buffer Server) (T : Real) (K : Nat) :
    Measure (Path (Buffer := Buffer) (Server := Server) T) :=
  N.calendarPoissonMeasure.map
    (calendarPath N T (positiveSize K))

/-- The exact active sample-path LDP statement specialized to the concrete
`J1` path space and the mapped calendar-time laws. -/
def ConcreteSamplePathLDPStatement
    (N : Network Buffer Server) (T : Real) : Prop :=
  PaperStatements.SamplePathLDPStatement N T
    (Path (Buffer := Buffer) (Server := Server) T)
    (calendarPathLaw N T) (asMatrix T)

end PoissonSamplePath

namespace Network

/-!
The next lemmas identify the generalized-inverse renewal count used by the
calendar execution with Mathlib's Poisson law.  They are proved from the
exponential product measure rather than assumed as process semantics.
-/

theorem unitRateClock_eval_map (r : Nat) :
    unitRateClockMeasure.map (Function.eval r) = expMeasure 1 := by
  unfold unitRateClockMeasure
  exact Measure.infinitePi_map_eval (fun _ : Nat => expMeasure 1) r

theorem unitRateClock_interarrival_pos_ae (r : Nat) :
    ∀ᵐ clock ∂unitRateClockMeasure, 0 < clock r := by
  rw [← ae_map_iff (measurable_pi_apply r).aemeasurable measurableSet_Ioi]
  rw [unitRateClock_eval_map]
  exact PoissonSamplePath.unitExp_pos_ae

theorem unitRateClock_all_interarrival_pos_ae :
    ∀ᵐ clock ∂unitRateClockMeasure, forall r, 0 < clock r := by
  rw [ae_all_iff]
  exact unitRateClock_interarrival_pos_ae

theorem measurable_renewalEpoch (n : Nat) :
    Measurable (fun clock : UnitRateClockPath => renewalEpoch clock n) :=
  PoissonSamplePath.measurable_renewalEpoch n

theorem renewalEpoch_strictMono
    {clock : UnitRateClockPath} (hclock : forall r, 0 < clock r) :
    StrictMono (renewalEpoch clock) :=
  PoissonSamplePath.renewalEpoch_strictMono clock hclock

theorem renewalEpoch_tendsto_atTop
    {clock : UnitRateClockPath}
    (hEpoch :
      Tendsto (fun n : Nat => renewalEpoch clock n / (n : Real))
        atTop (nhds 1)) :
    Tendsto (renewalEpoch clock) atTop atTop :=
  PoissonSamplePath.renewalEpoch_tendsto_atTop clock hEpoch

theorem measurable_unitPoissonCount (s : Real) :
    Measurable (fun clock : UnitRateClockPath => unitPoissonCount clock s) :=
  PoissonSamplePath.measurable_unitPoissonCount s

open scoped ENNReal

noncomputable def erlangPDF (n : Nat) (x : Real) : ENNReal :=
  ENNReal.ofReal
    (if 0 <= x then x ^ n / n.factorial * Real.exp (-x) else 0)

noncomputable def erlangPDFReal (n : Nat) (x : Real) : Real :=
  if 0 <= x then x ^ n / n.factorial * Real.exp (-x) else 0

theorem erlangPDFReal_eq_gammaPDFReal (n : Nat) :
    erlangPDFReal n = gammaPDFReal ((n + 1 : Nat) : Real) 1 := by
  funext x
  simp only [erlangPDFReal, gammaPDFReal]
  split_ifs with hx
  · push_cast
    rw [Real.Gamma_nat_eq_factorial]
    rw [show ((n : Real) + 1 - 1) = n by ring]
    rw [Real.rpow_natCast]
    norm_num
    rw [div_eq_inv_mul]
  · rfl

theorem erlangPDF_eq_gammaPDF (n : Nat) :
    erlangPDF n = gammaPDF ((n + 1 : Nat) : Real) 1 := by
  funext x
  simp only [erlangPDF, gammaPDF, gammaPDFReal]
  congr 1
  split_ifs with hx
  · push_cast
    rw [Real.Gamma_nat_eq_factorial]
    rw [show ((n : Real) + 1 - 1) = n by ring]
    rw [Real.rpow_natCast]
    norm_num
    rw [div_eq_inv_mul]
  · rfl

theorem cdf_gammaMeasure_nat_eq_intervalIntegral
    (n : Nat) {s : Real} (hs : 0 <= s) :
    cdf (gammaMeasure ((n + 1 : Nat) : Real) 1) s =
      ∫ x in (0 : Real)..s,
        x ^ n / n.factorial * Real.exp (-x) := by
  rw [cdf_gammaMeasure_eq_integral (by positivity) (by norm_num)]
  rw [← erlangPDFReal_eq_gammaPDFReal n]
  rw [← integral_indicator measurableSet_Iic]
  have hfun :
      (Iic s).indicator (erlangPDFReal n) =
        (Icc 0 s).indicator
          (fun x : Real =>
            x ^ n / n.factorial * Real.exp (-x)) := by
    funext x
    by_cases hx : x ∈ Icc (0 : Real) s
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem (show x ∈ Iic s from hx.2)]
      simp [erlangPDFReal, hx.1]
    · rw [Set.indicator_of_notMem hx]
      by_cases hxs : x <= s
      · rw [Set.indicator_of_mem (show x ∈ Iic s from hxs)]
        have hx0 : Not (0 <= x) := by
          intro h
          exact hx ⟨h, hxs⟩
        simp [erlangPDFReal, hx0]
      · rw [Set.indicator_of_notMem
          (show x ∉ Iic s from hxs)]
  rw [hfun, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]

theorem cdf_gammaMeasure_nat_sub_succ
    (n : Nat) {s : Real} (hs : 0 <= s) :
    cdf (gammaMeasure ((n + 1 : Nat) : Real) 1) s -
        cdf (gammaMeasure ((n + 2 : Nat) : Real) 1) s =
      Real.exp (-s) * s ^ (n + 1) / (n + 1).factorial := by
  rw [cdf_gammaMeasure_nat_eq_intervalIntegral n hs,
    cdf_gammaMeasure_nat_eq_intervalIntegral (n + 1) hs]
  have hfirst :
      IntervalIntegrable
        (fun x : Real => x ^ n / n.factorial * Real.exp (-x))
        volume 0 s := by
    exact (by fun_prop : Continuous
      (fun x : Real => x ^ n / n.factorial * Real.exp (-x))).intervalIntegrable 0 s
  have hsecond :
      IntervalIntegrable
        (fun x : Real =>
          x ^ (n + 1) / (n + 1).factorial * Real.exp (-x))
        volume 0 s := by
    exact (by fun_prop : Continuous
      (fun x : Real =>
        x ^ (n + 1) / (n + 1).factorial *
          Real.exp (-x))).intervalIntegrable 0 s
  rw [← intervalIntegral.integral_sub hfirst hsecond]
  let F : Real -> Real := fun x =>
    x ^ (n + 1) / (n + 1).factorial * Real.exp (-x)
  have hderiv (x : Real) :
      HasDerivAt F
        (x ^ n / n.factorial * Real.exp (-x) -
          x ^ (n + 1) / (n + 1).factorial * Real.exp (-x)) x := by
    dsimp only [F]
    have hd := ((hasDerivAt_pow (n + 1) x).div_const
      ((n + 1).factorial : Real)).mul ((hasDerivAt_neg x).exp)
    rw [show n + 1 - 1 = n by omega] at hd
    change HasDerivAt
      (fun y : Real =>
        y ^ (n + 1) / (n + 1).factorial * Real.exp (-y))
      _ x at hd
    apply hd.congr_deriv
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    (hfirst.sub hsecond)]
  dsimp only [F]
  simp
  ring

theorem erlangPDF_lconvolution (n : Nat) :
    erlangPDF n ⋆ₗ[(volume : Measure Real)] erlangPDF 0 =
      erlangPDF (n + 1) := by
  funext x
  rw [lconvolution_def]
  by_cases hx : 0 <= x
  · have hintegrand :
        (fun y : Real => erlangPDF n y * erlangPDF 0 (-y + x)) =
          (Icc 0 x).indicator (fun y =>
            ENNReal.ofReal
              (y ^ n / n.factorial * Real.exp (-x))) := by
      funext y
      by_cases hy : y ∈ Icc (0 : Real) x
      · have hy0 : 0 <= y := hy.1
        have hyx : 0 <= -y + x := by linarith [hy.2]
        rw [Set.indicator_of_mem hy]
        simp only [erlangPDF, if_pos hy0, if_pos hyx, pow_zero,
          Nat.factorial_zero, Nat.cast_one, div_one]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        simp only [one_mul]
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring_nf
      · rw [Set.indicator_of_notMem hy]
        by_cases hy0 : 0 <= y
        · have hyx : Not (0 <= -y + x) := by
            intro h
            apply hy
            exact ⟨hy0, by linarith⟩
          simp [erlangPDF, hy0, hyx]
        · simp [erlangPDF, hy0]
    rw [hintegrand, lintegral_indicator measurableSet_Icc]
    have hint :
        IntegrableOn
          (fun y : Real =>
            y ^ n / n.factorial * Real.exp (-x))
          (Icc 0 x) := by
      apply ContinuousOn.integrableOn_Icc
      fun_prop
    have hnonneg :
        ∀ᵐ y ∂((volume : Measure Real).restrict (Icc 0 x)),
          0 <= y ^ n / n.factorial * Real.exp (-x) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Icc] with y hy
      have hfac : 0 < (n.factorial : Real) := by positivity
      exact mul_nonneg (div_nonneg (pow_nonneg hy.1 n) hfac.le)
        (Real.exp_pos _).le
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hx]
    have hcalc :
        (∫ y in (0 : Real)..x,
            y ^ n / n.factorial * Real.exp (-x)) =
          x ^ (n + 1) / (n + 1).factorial * Real.exp (-x) := by
      rw [show (fun y : Real =>
          y ^ n / n.factorial * Real.exp (-x)) =
          fun y => (n.factorial : Real)⁻¹ *
            Real.exp (-x) * y ^ n by
              funext y
              rw [div_eq_inv_mul]
              ring]
      rw [intervalIntegral.integral_const_mul,
        integral_pow]
      rw [zero_pow (Nat.succ_ne_zero n)]
      push_cast
      rw [Nat.factorial_succ]
      field_simp
      push_cast
      ring
    rw [hcalc]
    simp [erlangPDF, hx]
  · have hxlt : x < 0 := lt_of_not_ge hx
    have hzero :
        (fun y : Real => erlangPDF n y * erlangPDF 0 (-y + x)) =
          fun _ => 0 := by
      funext y
      by_cases hy : 0 <= y
      · have hyx : Not (0 <= -y + x) := by linarith
        simp [erlangPDF, hy, hyx]
      · simp [erlangPDF, hy]
    rw [hzero, lintegral_zero]
    simp [erlangPDF, hx]

theorem gammaMeasure_succ_conv_expMeasure (n : Nat) :
    gammaMeasure ((n + 1 : Nat) : Real) 1 ∗ expMeasure 1 =
      gammaMeasure ((n + 2 : Nat) : Real) 1 := by
  rw [expMeasure, gammaMeasure, gammaMeasure, gammaMeasure]
  rw [← erlangPDF_eq_gammaPDF n]
  rw [show gammaPDF (1 : Real) 1 = erlangPDF 0 by
    simpa using (erlangPDF_eq_gammaPDF 0).symm]
  rw [show gammaPDF ((n + 2 : Nat) : Real) 1 =
      erlangPDF (n + 1) by
    exact (erlangPDF_eq_gammaPDF (n + 1)).symm]
  have hn : Measurable (erlangPDF n) := by
    rw [erlangPDF_eq_gammaPDF]
    exact (measurable_gammaPDFReal _ _).ennreal_ofReal
  have hzero : Measurable (erlangPDF 0) := by
    rw [erlangPDF_eq_gammaPDF]
    exact (measurable_gammaPDFReal _ _).ennreal_ofReal
  rw [conv_withDensity_eq_lconvolution hn hzero,
    erlangPDF_lconvolution]

theorem unitRateClock_iIndep :
    iIndepFun
      (fun r : Nat => fun clock : UnitRateClockPath => clock r)
      unitRateClockMeasure := by
  unfold unitRateClockMeasure
  exact iIndepFun_infinitePi
    (X := fun _ : Nat => fun x : Real => x) (by fun_prop)

theorem unitRateClock_eval_hasLaw (r : Nat) :
    HasLaw (fun clock : UnitRateClockPath => clock r)
      (expMeasure 1) unitRateClockMeasure where
  aemeasurable := (measurable_pi_apply r).aemeasurable
  map_eq := unitRateClock_eval_map r

theorem unit_renewalEpoch_ratio_tendsto_ae :
    ∀ᵐ clock ∂unitRateClockMeasure,
      Tendsto
        (fun n : Nat => renewalEpoch clock n / (n : Real))
        atTop (nhds 1) := by
  let X : Nat -> UnitRateClockPath -> Real :=
    fun r clock => clock r
  have hXmap (r : Nat) :
      unitRateClockMeasure.map (X r) = expMeasure 1 := by
    exact unitRateClock_eval_map r
  have hXintegrable : Integrable (X 0) unitRateClockMeasure := by
    have hbase :
        Integrable (fun x : Real => x)
          (unitRateClockMeasure.map (X 0)) := by
      rw [hXmap]
      exact unitExp_integrable
    simpa [Function.comp_def] using hbase.comp_measurable (by fun_prop)
  have hXindep : Pairwise
      (fun r q => IndepFun (X r) (X q) unitRateClockMeasure) := by
    intro r q hrq
    exact unitRateClock_iIndep.indepFun hrq
  have hXident : forall r, IdentDistrib (X r) (X 0)
      unitRateClockMeasure unitRateClockMeasure := by
    intro r
    refine ⟨by fun_prop, by fun_prop, ?_⟩
    rw [hXmap r, hXmap 0]
  have hmean : integral unitRateClockMeasure (X 0) = 1 := by
    calc
      integral unitRateClockMeasure (X 0) =
          integral (unitRateClockMeasure.map (X 0))
            (fun x : Real => x) := by
              rw [integral_map (by fun_prop) (by fun_prop)]
      _ = integral (expMeasure 1) (fun x : Real => x) := by
        rw [hXmap]
      _ = 1 := unitExp_integral
  have hstrong :=
    strong_law_ae_real X hXintegrable hXindep hXident
  simpa only [X, renewalEpoch, hmean] using hstrong

theorem unit_renewalEpoch_tendsto_atTop_ae :
    ∀ᵐ clock ∂unitRateClockMeasure,
      Tendsto (renewalEpoch clock) atTop atTop := by
  filter_upwards [unit_renewalEpoch_ratio_tendsto_ae] with clock hclock
  exact renewalEpoch_tendsto_atTop hclock

theorem unitPoissonCount_eq_iff_epoch
    {clock : UnitRateClockPath} (hpos : forall r, 0 < clock r)
    (hTop : Tendsto (renewalEpoch clock) atTop atTop)
    {s : Real} (hs : 0 < s) (n : Nat) :
    unitPoissonCount clock s = n <->
      renewalEpoch clock n <= s /\
        s < renewalEpoch clock (n + 1) := by
  have hcross : Exists (fun m => s < renewalEpoch clock m) :=
    (hTop.eventually_gt_atTop s).exists
  constructor
  · intro hcount
    rw [← hcount]
    exact ⟨renewalEpoch_count_le clock hs hcross,
      lt_renewalEpoch_count_add_one clock hs hcross⟩
  · rintro ⟨hnle, hnnext⟩
    have hmono : Monotone (renewalEpoch clock) :=
      (renewalEpoch_strictMono hpos).monotone
    have hfind : Nat.find hcross = n + 1 := by
      apply (Nat.find_eq_iff hcross).mpr
      refine ⟨hnnext, ?_⟩
      intro m hm
      have hmn : m <= n := by omega
      exact not_lt_of_ge ((hmono hmn).trans hnle)
    rw [unitPoissonCount_eq_find clock hs hcross, hfind]
    omega

theorem renewalEpoch_succ_hasLaw_gamma (n : Nat) :
    HasLaw
      (fun clock : UnitRateClockPath => renewalEpoch clock (n + 1))
      (gammaMeasure ((n + 1 : Nat) : Real) 1)
      unitRateClockMeasure := by
  induction n with
  | zero =>
      simpa [renewalEpoch, expMeasure] using unitRateClock_eval_hasLaw 0
  | succ n ih =>
      have hindep :
          IndepFun
            (fun clock : UnitRateClockPath =>
              renewalEpoch clock (n + 1))
            (fun clock => clock (n + 1))
            unitRateClockMeasure := by
        have h := unitRateClock_iIndep.indepFun_sum_range_succ
          (fun _ => measurable_pi_apply _) (n + 1)
        convert h using 1
        funext clock
        simp [renewalEpoch]
      letI : IsProbabilityMeasure
          (gammaMeasure ((n + 1 : Nat) : Real) 1) :=
        isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
      have hsum := hindep.hasLaw_add ih
        (unitRateClock_eval_hasLaw (n + 1))
      rw [gammaMeasure_succ_conv_expMeasure n] at hsum
      convert hsum using 1
      funext clock
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega,
        renewalEpoch_succ]
      rfl

theorem unitPoissonCount_real_singleton
    {s : Real} (hs : 0 <= s) (n : Nat) :
    unitRateClockMeasure.real
        {clock | unitPoissonCount clock s = n} =
      Real.exp (-s) * s ^ n / n.factorial := by
  rcases hs.eq_or_lt with rfl | hspos
  · cases n <;> simp [unitPoissonCount_of_nonpos]
  let A : Set UnitRateClockPath :=
    {clock | renewalEpoch clock n <= s}
  let B : Set UnitRateClockPath :=
    {clock | renewalEpoch clock (n + 1) <= s}
  have hA : MeasurableSet A :=
    measurableSet_le (measurable_renewalEpoch n) measurable_const
  have hB : MeasurableSet B :=
    measurableSet_le (measurable_renewalEpoch (n + 1)) measurable_const
  have hcount :
      {clock | unitPoissonCount clock s = n} =ᵐ[unitRateClockMeasure]
        A \ B := by
    filter_upwards [unitRateClock_all_interarrival_pos_ae,
      unit_renewalEpoch_tendsto_atTop_ae] with clock hclock htop
    apply propext
    change (unitPoissonCount clock s = n) <->
      (clock ∈ A /\ clock ∉ B)
    rw [unitPoissonCount_eq_iff_epoch hclock htop hspos n]
    dsimp only [A, B]
    constructor
    · rintro ⟨hn, hnnext⟩
      exact ⟨hn, not_le_of_gt hnnext⟩
    · rintro ⟨hn, hnnext⟩
      exact ⟨hn, lt_of_not_ge hnnext⟩
  have hmono :
      (A ∩ B : Set UnitRateClockPath) =ᵐ[unitRateClockMeasure] B := by
    filter_upwards [unitRateClock_all_interarrival_pos_ae] with clock hclock
    have hm := (renewalEpoch_strictMono hclock).monotone
    apply propext
    change (clock ∈ A /\ clock ∈ B) <-> clock ∈ B
    dsimp only [A, B]
    constructor
    · exact And.right
    · intro hnnext
      exact ⟨(hm (Nat.le_add_right n 1)).trans hnnext, hnnext⟩
  calc
    unitRateClockMeasure.real
        {clock | unitPoissonCount clock s = n} =
        unitRateClockMeasure.real (A \ B) := by
      exact congrArg ENNReal.toReal (measure_congr hcount)
    _ = unitRateClockMeasure.real (A \ (A ∩ B)) := by
      congr 1
      ext clock
      simp
    _ = unitRateClockMeasure.real A -
        unitRateClockMeasure.real (A ∩ B) := by
      exact measureReal_sdiff inter_subset_left (hA.inter hB)
    _ = unitRateClockMeasure.real A -
        unitRateClockMeasure.real B := by
      congr 1
      exact congrArg ENNReal.toReal (measure_congr hmono)
    _ = Real.exp (-s) * s ^ n / n.factorial := by
      cases n with
      | zero =>
          have hBcdf :
              unitRateClockMeasure.real B =
                cdf (expMeasure 1) s := by
            rw [cdf_eq_real]
            change unitRateClockMeasure.real
                {clock | renewalEpoch clock 1 <= s} =
              (expMeasure 1).real {x | x <= s}
            simpa [B, renewalEpoch] using
              (unitRateClock_eval_hasLaw 0).measureReal_eq
                (p := fun x : Real => x <= s) measurableSet_Iic
          have hAuniv : A = Set.univ := by
            ext clock
            simp [A, hspos.le]
          rw [hAuniv, probReal_univ, hBcdf,
            cdf_expMeasure_eq (by norm_num), if_pos hspos.le]
          norm_num
      | succ m =>
          letI : IsProbabilityMeasure
              (gammaMeasure ((m + 1 : Nat) : Real) 1) :=
            isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
          letI : IsProbabilityMeasure
              (gammaMeasure ((m + 2 : Nat) : Real) 1) :=
            isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
          have hAcdf :
              unitRateClockMeasure.real A =
                cdf (gammaMeasure ((m + 1 : Nat) : Real) 1) s := by
            rw [cdf_eq_real]
            change unitRateClockMeasure.real
                {clock | renewalEpoch clock (m + 1) <= s} =
              (gammaMeasure ((m + 1 : Nat) : Real) 1).real
                {x | x <= s}
            simpa [A] using
              (renewalEpoch_succ_hasLaw_gamma m).measureReal_eq
                (p := fun x : Real => x <= s) measurableSet_Iic
          have hBcdf :
              unitRateClockMeasure.real B =
                cdf (gammaMeasure ((m + 2 : Nat) : Real) 1) s := by
            rw [cdf_eq_real]
            change unitRateClockMeasure.real
                {clock | renewalEpoch clock (m + 2) <= s} =
              (gammaMeasure ((m + 2 : Nat) : Real) 1).real
                {x | x <= s}
            simpa [B, Nat.add_assoc] using
              (renewalEpoch_succ_hasLaw_gamma (m + 1)).measureReal_eq
                (p := fun x : Real => x <= s) measurableSet_Iic
          rw [hAcdf, hBcdf, cdf_gammaMeasure_nat_sub_succ m hspos.le]

theorem unitPoissonCount_hasLaw_poisson
    {s : Real} (hs : 0 <= s) :
    HasLaw
      (fun clock : UnitRateClockPath => unitPoissonCount clock s)
      (poissonMeasure (⟨s, hs⟩ : NNReal))
      unitRateClockMeasure := by
  letI := instIsProbabilityMeasureNatPoissonMeasure
    (⟨s, hs⟩ : NNReal)
  refine ⟨(measurable_unitPoissonCount s).aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro n
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change
    (unitRateClockMeasure.map
      (fun clock : UnitRateClockPath =>
        unitPoissonCount clock s)).real {n} =
      (poissonMeasure (⟨s, hs⟩ : NNReal)).real {n}
  rw [map_measureReal_apply_of_aemeasurable
    (measurable_unitPoissonCount s).aemeasurable
    (MeasurableSet.singleton n)]
  change unitRateClockMeasure.real
      {clock | unitPoissonCount clock s = n} =
    (poissonMeasure (⟨s, hs⟩ : NNReal)).real {n}
  rw [poissonMeasure_real_singleton (⟨s, hs⟩ : NNReal) n]
  change unitRateClockMeasure.real
      {clock | unitPoissonCount clock s = n} =
    Real.exp (-s) * s ^ n / n.factorial
  exact unitPoissonCount_real_singleton hs n

theorem coordinateClock_hasLaw
    {Buffer : Type u} {Server : Type v}
    [Fintype Buffer] [Fintype Server]
    [DecidableEq Buffer] [DecidableEq Server]
    [Nonempty Buffer]
    (N : Network Buffer Server) (j : Server) (k : Buffer) :
    HasLaw
      (fun omega : CalendarPoissonSample
        (Buffer := Buffer) (Server := Server) => omega j k)
      unitRateClockMeasure N.calendarPoissonMeasure where
  aemeasurable :=
    ((measurable_pi_apply k).comp (measurable_pi_apply j)).aemeasurable
  map_eq := N.coordinateClock_map j k

theorem calendarTokenCount_hasLaw_poisson
    {Buffer : Type u} {Server : Type v}
    [Fintype Buffer] [Fintype Server]
    [DecidableEq Buffer] [DecidableEq Server]
    [Nonempty Buffer]
    (N : Network Buffer Server)
    (K : PNat) (t : Real) (j : Server) (k : Buffer) :
    HasLaw
      (fun omega : CalendarPoissonSample
        (Buffer := Buffer) (Server := Server) =>
          N.calendarTokenCount K omega t j k)
      (poissonMeasure
        (⟨N.coordinateOperationalTime K t j k,
          mul_nonneg
            (mul_nonneg (by positivity) (N.phi_nonneg j k))
            (le_max_right t 0)⟩ : NNReal))
      N.calendarPoissonMeasure := by
  let s := N.coordinateOperationalTime K t j k
  have hs : 0 <= s := by
    exact mul_nonneg
      (mul_nonneg (by positivity) (N.phi_nonneg j k))
      (le_max_right t 0)
  have hunit := unitPoissonCount_hasLaw_poisson hs
  have hcoord := coordinateClock_hasLaw N j k
  have hcomp := hunit.fun_comp hcoord
  simpa only [calendarTokenCount, s] using hcomp

theorem calendarTokenCount_phi_zero_hasLaw
    {Buffer : Type u} {Server : Type v}
    [Fintype Buffer] [Fintype Server]
    [DecidableEq Buffer] [DecidableEq Server]
    [Nonempty Buffer]
    (N : Network Buffer Server)
    (K : PNat) (t : Real) (j : Server) (k : Buffer)
    (hphi : N.phi j k = 0) :
    HasLaw
      (fun omega : CalendarPoissonSample
        (Buffer := Buffer) (Server := Server) =>
          N.calendarTokenCount K omega t j k)
      (poissonMeasure 0)
      N.calendarPoissonMeasure := by
  convert calendarTokenCount_hasLaw_poisson N K t j k using 1
  congr 2
  apply Subtype.ext
  simp [coordinateOperationalTime, hphi]

end Network

end StateDepMOR

namespace StateDepMOR.PoissonSamplePath

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

set_option maxRecDepth 10000

/-- Positive-rate labeled arrivals in `(0,T]`. -/
def positiveRateCalendarJumpsOn
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) (T : Real) :
    Set (Network.CalendarEvent (Buffer := Buffer) (Server := Server)) :=
  {e | 0 < N.phi e.1.1 e.1.2 /\
    N.calendarEventTime K omega e ∈ Ioc 0 T}

theorem coordinateClock_hasLaw'
    (N : Network Buffer Server) (j : Server) (k : Buffer) :
    HasLaw
      (fun omega : Network.CalendarPoissonSample
        (Buffer := Buffer) (Server := Server) => omega j k)
      Network.unitRateClockMeasure N.calendarPoissonMeasure where
  aemeasurable :=
    ((measurable_pi_apply k).comp (measurable_pi_apply j)).aemeasurable
  map_eq := N.coordinateClock_map j k

theorem coordinate_renewalEpoch_succ_hasLaw_gamma
    (N : Network Buffer Server) (j : Server) (k : Buffer) (r : Nat) :
    HasLaw
      (fun omega : Network.CalendarPoissonSample
        (Buffer := Buffer) (Server := Server) =>
          Network.renewalEpoch (omega j k) (r + 1))
      (gammaMeasure ((r + 1 : Nat) : Real) 1)
      N.calendarPoissonMeasure := by
  simpa [Function.comp_def] using
    (Network.renewalEpoch_succ_hasLaw_gamma r).comp
      (coordinateClock_hasLaw' N j k)

theorem gamma_prod_scaled_ne_ae
    (r q : Nat) {a b : Real} (ha : a ≠ 0) (hb : b ≠ 0) :
    ∀ᵐ z ∂((gammaMeasure ((r + 1 : Nat) : Real) 1).prod
      (gammaMeasure ((q + 1 : Nat) : Real) 1)),
      z.1 / a ≠ z.2 / b := by
  letI : IsProbabilityMeasure
      (gammaMeasure ((r + 1 : Nat) : Real) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  letI : IsProbabilityMeasure
      (gammaMeasure ((q + 1 : Nat) : Real) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  letI : NullSingletonClass
      (gammaMeasure ((q + 1 : Nat) : Real) 1) := by
    rw [gammaMeasure]
    infer_instance
  rw [Measure.ae_prod_iff_ae_ae (by measurability)]
  refine Filter.Eventually.of_forall fun x => ?_
  filter_upwards
    [Measure.ae_ne (gammaMeasure ((q + 1 : Nat) : Real) 1)
      (x * b / a)] with y hy
  intro heq
  apply hy
  field_simp [ha, hb] at heq ⊢
  nlinarith

theorem distinct_coordinate_calendarEventTime_ne_ae
    (N : Network Buffer Server) (K : PNat)
    {j j' : Server} {k k' : Buffer}
    (hcoord : (j, k) ≠ (j', k'))
    (hphi : 0 < N.phi j k) (hphi' : 0 < N.phi j' k')
    (r q : Nat) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      N.calendarEventTime K omega ((j, k), r) ≠
        N.calendarEventTime K omega ((j', k'), q) := by
  let p : Sigma (fun _ : Server => Buffer) := ⟨j, k⟩
  let p' : Sigma (fun _ : Server => Buffer) := ⟨j', k'⟩
  have hpp' : p ≠ p' := by
    intro h
    have hs : j = j' /\ k = k' := by
      simpa only [p, p', Sigma.mk.inj_iff, heq_eq_eq] using h
    exact hcoord (Prod.ext hs.1 hs.2)
  have hindepClock :
      IndepFun
        (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) => omega j k)
        (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) => omega j' k')
        N.calendarPoissonMeasure := by
    simpa [p, p'] using N.coordinateClock_iIndep.indepFun hpp'
  have hindepEpoch :
      IndepFun
        (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
            Network.renewalEpoch (omega j k) (r + 1))
        (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
            Network.renewalEpoch (omega j' k') (q + 1))
        N.calendarPoissonMeasure := by
    simpa [Function.comp_def] using hindepClock.comp
      (Network.measurable_renewalEpoch (r + 1))
      (Network.measurable_renewalEpoch (q + 1))
  have hpairLaw :
      HasLaw
        (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
          (Network.renewalEpoch (omega j k) (r + 1),
            Network.renewalEpoch (omega j' k') (q + 1)))
        ((gammaMeasure ((r + 1 : Nat) : Real) 1).prod
          (gammaMeasure ((q + 1 : Nat) : Real) 1))
        N.calendarPoissonMeasure :=
    hindepEpoch.hasLaw_prod
      (coordinate_renewalEpoch_succ_hasLaw_gamma N j k r)
      (coordinate_renewalEpoch_succ_hasLaw_gamma N j' k' q)
  have hden : (((K : Nat) : Real) * N.phi j k) ≠ 0 :=
    mul_ne_zero (by positivity) hphi.ne'
  have hden' : (((K : Nat) : Real) * N.phi j' k') ≠ 0 :=
    mul_ne_zero (by positivity) hphi'.ne'
  have hne := gamma_prod_scaled_ne_ae r q hden hden'
  rw [← hpairLaw.ae_iff (by fun_prop)] at hne
  simpa [Network.calendarEventTime] using hne

theorem positiveRateCalendarJumpsOn_finite
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) (T : Real)
    (hEpoch : forall j k,
      Tendsto
        (fun n : Nat =>
          Network.renewalEpoch (omega j k) n / (n : Real))
        atTop (nhds 1)) :
    (positiveRateCalendarJumpsOn N K omega T).Finite := by
  classical
  let fiber : Server × Buffer ->
      Set (Network.CalendarEvent (Buffer := Buffer) (Server := Server)) :=
    fun p =>
      {e | e.1 = p /\ 0 < N.phi p.1 p.2 /\
        N.calendarEventTime K omega e ∈ Ioc 0 T}
  have hfiber : forall p, (fiber p).Finite := by
    rintro ⟨j, k⟩
    by_cases hphi : 0 < N.phi j k
    · have htop :
          Tendsto (Network.renewalEpoch (omega j k)) atTop atTop :=
        renewalEpoch_tendsto_atTop (omega j k) (hEpoch j k)
      let B : Real := T * (((K : Nat) : Real) * N.phi j k)
      obtain ⟨n0, hn0⟩ :=
        Filter.eventually_atTop.mp (htop.eventually_gt_atTop B)
      have hrFinite :
          {r : Nat |
            N.calendarEventTime K omega ((j, k), r) ∈ Ioc 0 T}.Finite := by
        apply (Set.finite_Iio n0).subset
        intro r hr
        have hden : 0 < (((K : Nat) : Real) * N.phi j k) :=
          mul_pos (by positivity) hphi
        have hle :
            Network.renewalEpoch (omega j k) (r + 1) <= B := by
          dsimp only [B]
          exact (div_le_iff₀ hden).mp hr.2
        by_contra hnot
        change Not (r < n0) at hnot
        have hn0le : n0 <= r + 1 :=
          (Nat.le_of_not_gt hnot).trans (Nat.le_succ r)
        exact (not_lt_of_ge hle) (hn0 (r + 1) hn0le)
      have himage :
          ((fun r : Nat => ((j, k), r)) ''
            {r : Nat |
              N.calendarEventTime K omega ((j, k), r) ∈ Ioc 0 T}).Finite :=
        hrFinite.image _
      apply himage.subset
      rintro ⟨⟨j', k'⟩, r⟩ he
      rcases he with ⟨hp, -, ht⟩
      simp only [Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩
      exact ⟨r, ht, rfl⟩
    · have hempty : fiber (j, k) = ∅ := by
        ext e
        simp [fiber, hphi]
      rw [hempty]
      exact Set.finite_empty
  have hunion : (Set.iUnion fiber).Finite := Set.finite_iUnion hfiber
  apply hunion.subset
  rintro ⟨⟨j, k⟩, r⟩ he
  exact Set.mem_iUnion.2 ⟨(j, k), rfl, he.1, he.2⟩

theorem zeroRate_calendarEventTime_eq_zero
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    {j : Server} {k : Buffer} (hphi : N.phi j k = 0) (r : Nat) :
    N.calendarEventTime K omega ((j, k), r) = 0 := by
  simp [Network.calendarEventTime, hphi]

/-- The common probability-one clock event needed by the J1 alignment. -/
theorem noSimultaneousPoissonJumps_ae
    (N : Network Buffer Server) (K : PNat) {T : Real} (hT : 0 < T) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      (positiveRateCalendarJumpsOn N K omega T).Finite /\
      (forall j k, N.phi j k = 0 ->
        forall r, N.calendarEventTime K omega ((j, k), r) = 0) /\
      (forall j k j' k',
        0 < N.phi j k -> 0 < N.phi j' k' ->
        (j, k) ≠ (j', k') -> forall r q,
          N.calendarEventTime K omega ((j, k), r) ≠
            N.calendarEventTime K omega ((j', k'), q)) := by
  have hcollisions :
      ∀ᵐ omega ∂N.calendarPoissonMeasure,
        forall j k j' k',
          0 < N.phi j k -> 0 < N.phi j' k' ->
          (j, k) ≠ (j', k') -> forall r q,
            N.calendarEventTime K omega ((j, k), r) ≠
              N.calendarEventTime K omega ((j', k'), q) := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    rw [ae_all_iff]
    intro j'
    rw [ae_all_iff]
    intro k'
    by_cases hphi : 0 < N.phi j k
    · simp only [hphi, forall_const]
      by_cases hphi' : 0 < N.phi j' k'
      · simp only [hphi', forall_const]
        by_cases hc : (j, k) ≠ (j', k')
        · have hbase :
              ∀ᵐ omega ∂N.calendarPoissonMeasure, forall r q,
                N.calendarEventTime K omega ((j, k), r) ≠
                  N.calendarEventTime K omega ((j', k'), q) := by
            rw [ae_all_iff]
            intro r
            rw [ae_all_iff]
            intro q
            exact distinct_coordinate_calendarEventTime_ne_ae
              N K hc hphi hphi' r q
          filter_upwards [hbase] with omega hne
          exact fun _ => hne
        · simp [hc]
      · simp [hphi']
    · simp [hphi]
  filter_upwards
    [N.all_renewalEpoch_ratio_tendsto_ae, hcollisions] with
      omega hEpoch hcollision
  refine
    ⟨positiveRateCalendarJumpsOn_finite N K omega T hEpoch, ?_, hcollision⟩
  intro j k hphi r
  exact zeroRate_calendarEventTime_eq_zero N K omega hphi r

theorem decode_encode_interarrival_bounds
    (n r : Nat) (hr : r < n)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hpos : forall j k q, 0 < omega j k q)
    (j : Server) (k : Buffer) :
    omega j k r <
        (decodeClockPrefix n (encodeClockPrefix n omega)) j k r /\
      (decodeClockPrefix n (encodeClockPrefix n omega)) j k r <=
        omega j k r + clockMesh n := by
  have hd := clockMesh_pos n
  have hx := hpos j k r
  have hq0 : 0 <= omega j k r / clockMesh n :=
    div_nonneg hx.le hd.le
  have hfloor :
      ((Nat.floor (omega j k r / clockMesh n) : Nat) : Real) <=
        omega j k r / clockMesh n :=
    Nat.floor_le hq0
  have hfloor' :
      omega j k r / clockMesh n <
        ((Nat.floor (omega j k r / clockMesh n) + 1 : Nat) : Real) := by
    exact_mod_cast Nat.lt_floor_add_one
      (omega j k r / clockMesh n)
  simp only [decodeClockPrefix, dif_pos hr, encodeClockPrefix,
    max_eq_left hx.le]
  constructor
  · calc
      omega j k r =
          clockMesh n * (omega j k r / clockMesh n) := by
            field_simp [ne_of_gt hd]
      _ < clockMesh n *
          ((Nat.floor (omega j k r / clockMesh n) + 1 : Nat) : Real) :=
        mul_lt_mul_of_pos_left hfloor' hd
  · calc
      clockMesh n *
          ((Nat.floor (omega j k r / clockMesh n) + 1 : Nat) : Real) <=
          clockMesh n * (omega j k r / clockMesh n + 1) := by
        gcongr
        simpa only [Nat.cast_add, Nat.cast_one, add_comm] using
          add_le_add_right hfloor 1
      _ = omega j k r + clockMesh n := by
        field_simp [ne_of_gt hd]

theorem decode_encode_interarrival_tendsto
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hpos : forall j k q, 0 < omega j k q)
    (j : Server) (k : Buffer) (r : Nat) :
    Tendsto
      (fun n =>
        (decodeClockPrefix n (encodeClockPrefix n omega)) j k r)
      atTop (nhds (omega j k r)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_
    clockMesh_tendsto_zero
  filter_upwards [eventually_gt_atTop r] with n hrn
  rw [Real.dist_eq]
  have hb :=
    decode_encode_interarrival_bounds n r hrn omega hpos j k
  rw [abs_of_nonneg (sub_nonneg.mpr hb.1.le)]
  linarith

theorem decode_encode_renewalEpoch_tendsto
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hpos : forall j k q, 0 < omega j k q)
    (j : Server) (k : Buffer) (m : Nat) :
    Tendsto
      (fun n =>
        Network.renewalEpoch
          ((decodeClockPrefix n (encodeClockPrefix n omega)) j k) m)
      atTop (nhds (Network.renewalEpoch (omega j k) m)) := by
  simp only [Network.renewalEpoch]
  exact tendsto_finsetSum (Finset.range m)
    (fun r _ => decode_encode_interarrival_tendsto omega hpos j k r)

noncomputable def delayedCalendarEventTime
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (e : Network.CalendarEvent (Buffer := Buffer) (Server := Server)) :
    Real :=
  N.calendarEventTime K
    (decodeClockPrefix n (encodeClockPrefix n omega)) e

theorem delayedCalendarEventTime_tendsto
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hpos : forall j k q, 0 < omega j k q)
    (e : Network.CalendarEvent (Buffer := Buffer) (Server := Server)) :
    Tendsto (fun n => delayedCalendarEventTime N K n omega e)
      atTop (nhds (N.calendarEventTime K omega e)) := by
  unfold delayedCalendarEventTime Network.calendarEventTime
  exact (decode_encode_renewalEpoch_tendsto omega hpos
    e.1.1 e.1.2 (e.2 + 1)).div_const _

theorem calendarEventTime_ne_const_ae
    (N : Network Buffer Server) (K : PNat)
    {j : Server} {k : Buffer} (hphi : 0 < N.phi j k)
    (r : Nat) (t : Real) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      N.calendarEventTime K omega ((j, k), r) ≠ t := by
  have hlaw :=
    coordinate_renewalEpoch_succ_hasLaw_gamma N j k r
  have hden : (((K : Nat) : Real) * N.phi j k) ≠ 0 :=
    mul_ne_zero (by positivity) hphi.ne'
  have hgamma :
      ∀ᵐ x ∂gammaMeasure ((r + 1 : Nat) : Real) 1,
        x ≠ t * (((K : Nat) : Real) * N.phi j k) := by
    letI : NullSingletonClass
        (gammaMeasure ((r + 1 : Nat) : Real) 1) := by
      rw [gammaMeasure]
      infer_instance
    exact Measure.ae_ne _ _
  rw [← hlaw.ae_iff (by measurability)] at hgamma
  filter_upwards [hgamma] with omega hne
  intro heq
  apply hne
  rw [Network.calendarEventTime] at heq
  exact (div_eq_iff hden).mp heq

theorem noHorizonPoissonJump_ae
    (N : Network Buffer Server) (K : PNat) (T : Real) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      forall j k, 0 < N.phi j k -> forall r,
        N.calendarEventTime K omega ((j, k), r) ≠ T := by
  rw [ae_all_iff]
  intro j
  rw [ae_all_iff]
  intro k
  by_cases hp : 0 < N.phi j k
  · simp only [hp, true_implies]
    rw [ae_all_iff]
    intro r
    exact calendarEventTime_ne_const_ae N K hp r T
  · simp [hp]

noncomputable def calendarEventTieKey
    (e : Network.CalendarEvent (Buffer := Buffer) (Server := Server)) :
    Lex (Fin (Fintype.card Server) ×
      Lex (Fin (Fintype.card Buffer) × Nat)) :=
  toLex (Fintype.equivFin Server e.1.1,
    toLex (Fintype.equivFin Buffer e.1.2, e.2))

theorem calendarEventTieKey_injective :
    Function.Injective
      (calendarEventTieKey (Buffer := Buffer) (Server := Server)) := by
  rintro ⟨⟨j, k⟩, r⟩ ⟨⟨j', k'⟩, r'⟩ h
  have houter := congrArg ofLex h
  have hj : j = j' :=
    (Fintype.equivFin Server).injective (congrArg Prod.fst houter)
  subst j'
  have hinner := congrArg (fun z => ofLex z.2) houter
  have hk : k = k' :=
    (Fintype.equivFin Buffer).injective (congrArg Prod.fst hinner)
  subst k'
  have hr : r = r' := congrArg Prod.snd hinner
  subst r'
  rfl

noncomputable def calendarEventLinearOrder
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    LinearOrder
      (Network.CalendarEvent (Buffer := Buffer) (Server := Server)) :=
  LinearOrder.lift'
    (fun e => toLex
      (N.calendarEventTime K omega e, calendarEventTieKey e))
    (by
      intro e f h
      apply calendarEventTieKey_injective
      have hp := congrArg ofLex h
      exact congrArg Prod.snd hp)

noncomputable def sortedPositiveRateCalendarJumps
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) (T : Real)
    (hfin : (positiveRateCalendarJumpsOn N K omega T).Finite) :
    List (Network.CalendarEvent (Buffer := Buffer) (Server := Server)) :=
  letI := calendarEventLinearOrder N K omega
  hfin.toFinset.sort

theorem sortedPositiveRateCalendarJumps_mem
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) (T : Real)
    (hfin : (positiveRateCalendarJumpsOn N K omega T).Finite)
    (e : Network.CalendarEvent (Buffer := Buffer) (Server := Server)) :
    e ∈ sortedPositiveRateCalendarJumps N K omega T hfin ↔
      e ∈ positiveRateCalendarJumpsOn N K omega T := by
  classical
  letI := calendarEventLinearOrder N K omega
  simp [sortedPositiveRateCalendarJumps]

theorem calendarEventTime_injective_on_positive
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hpos : forall j k q, 0 < omega j k q)
    (hcross : forall j k j' k',
      0 < N.phi j k -> 0 < N.phi j' k' ->
      (j, k) ≠ (j', k') -> forall r q,
        N.calendarEventTime K omega ((j, k), r) ≠
          N.calendarEventTime K omega ((j', k'), q)) :
    Set.InjOn (N.calendarEventTime K omega)
      {e | 0 < N.phi e.1.1 e.1.2} := by
  rintro ⟨⟨j, k⟩, r⟩ hr ⟨⟨j', k'⟩, q⟩ hq heq
  by_cases hc : (j, k) = (j', k')
  · rcases Prod.mk.inj hc with ⟨rfl, rfl⟩
    congr 1
    have hmono :=
      renewalEpoch_strictMono (omega j k) (hpos j k)
    apply Nat.succ.inj
    apply hmono.injective
    have hden : (((K : Nat) : Real) * N.phi j k) ≠ 0 :=
      mul_ne_zero (by positivity) hr.ne'
    exact (div_left_inj' hden).mp heq
  · exact False.elim ((hcross j k j' k' hr hq hc r q) heq)

theorem sortedPositiveRateCalendarJumps_pairwise
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) (T : Real)
    (hfin : (positiveRateCalendarJumpsOn N K omega T).Finite)
    (hpos : forall j k q, 0 < omega j k q)
    (hcross : forall j k j' k',
      0 < N.phi j k -> 0 < N.phi j' k' ->
      (j, k) ≠ (j', k') -> forall r q,
        N.calendarEventTime K omega ((j, k), r) ≠
          N.calendarEventTime K omega ((j', k'), q)) :
    (sortedPositiveRateCalendarJumps N K omega T hfin).Pairwise
      (fun e f =>
        N.calendarEventTime K omega e <
          N.calendarEventTime K omega f) := by
  classical
  letI := calendarEventLinearOrder N K omega
  let l := sortedPositiveRateCalendarJumps N K omega T hfin
  have hsorted : l.Pairwise (fun e f => e <= f) := by
    dsimp only [l, sortedPositiveRateCalendarJumps]
    exact Finset.pairwise_sort _ _
  have hnodup : l.Nodup := by
    dsimp only [l, sortedPositiveRateCalendarJumps]
    exact Finset.sort_nodup _ _
  have hinj := calendarEventTime_injective_on_positive
    N K omega hpos hcross
  have hdmem :
      l.Pairwise (fun e f => e ∈ l /\ f ∈ l /\ e ≠ f) :=
    List.Pairwise.and_mem.1 hnodup
  apply (hsorted.and hdmem).imp
  rintro e f ⟨hef, he, hf, hne⟩
  change toLex
      (N.calendarEventTime K omega e, calendarEventTieKey e) <=
    toLex (N.calendarEventTime K omega f, calendarEventTieKey f) at hef
  rcases Prod.Lex.toLex_le_toLex.mp hef with hef | ⟨heq, -⟩
  · exact hef
  · exact False.elim (hne (hinj
      (((sortedPositiveRateCalendarJumps_mem
        N K omega T hfin e).mp he).1)
      (((sortedPositiveRateCalendarJumps_mem
        N K omega T hfin f).mp hf).1) heq))

private theorem eventually_delayed_lt_all
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hpos : forall j k q, 0 < omega j k q)
    (e : Network.CalendarEvent (Buffer := Buffer) (Server := Server))
    (l : List (Network.CalendarEvent
      (Buffer := Buffer) (Server := Server)))
    (h : forall f, f ∈ l ->
      N.calendarEventTime K omega e <
        N.calendarEventTime K omega f) :
    ∀ᶠ n in atTop, forall f, f ∈ l ->
      delayedCalendarEventTime N K n omega e <
        delayedCalendarEventTime N K n omega f := by
  induction l with
  | nil => simp
  | cons f l ih =>
      have hef :
          ∀ᶠ n in atTop,
            delayedCalendarEventTime N K n omega e <
              delayedCalendarEventTime N K n omega f :=
        (delayedCalendarEventTime_tendsto N K omega hpos e).eventually_lt
          (delayedCalendarEventTime_tendsto N K omega hpos f)
          (h f (by simp))
      have htail := ih (fun q hq => h q (by simp [hq]))
      filter_upwards [hef, htail] with n hn hnt
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hn
      · exact hnt q hq

theorem eventually_delayedCalendarEventTime_pairwise
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hpos : forall j k q, 0 < omega j k q)
    (l : List (Network.CalendarEvent
      (Buffer := Buffer) (Server := Server)))
    (hl : l.Pairwise (fun e f =>
      N.calendarEventTime K omega e <
        N.calendarEventTime K omega f)) :
    ∀ᶠ n in atTop,
      l.Pairwise (fun e f =>
        delayedCalendarEventTime N K n omega e <
          delayedCalendarEventTime N K n omega f) := by
  induction l with
  | nil => simp
  | cons e l ih =>
      rw [List.pairwise_cons] at hl
      have hhead :=
        eventually_delayed_lt_all N K omega hpos e l hl.1
      have htail := ih hl.2
      filter_upwards [hhead, htail] with n hn hnt
      rw [List.pairwise_cons]
      exact ⟨hn, hnt⟩

private theorem eventually_delayed_in_Ioo
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hpos : forall j k q, 0 < omega j k q)
    (T : Real)
    (l : List (Network.CalendarEvent
      (Buffer := Buffer) (Server := Server)))
    (hl : forall e, e ∈ l ->
      N.calendarEventTime K omega e ∈ Ioo 0 T) :
    ∀ᶠ n in atTop, forall e, e ∈ l ->
      delayedCalendarEventTime N K n omega e ∈ Ioo 0 T := by
  induction l with
  | nil => simp
  | cons e l ih =>
      have he :
          ∀ᶠ n in atTop,
            delayedCalendarEventTime N K n omega e ∈ Ioo 0 T :=
        (delayedCalendarEventTime_tendsto N K omega hpos e).eventually
          (Ioo_mem_nhds (hl e (by simp)).1 (hl e (by simp)).2)
      have htail := ih (fun q hq => hl q (by simp [hq]))
      filter_upwards [he, htail] with n hn hnt
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact hn
      · exact hnt q hq

theorem calendarTokenCount_lt_iff_eventTime_le
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega)
    {j : Server} {k : Buffer} (hphi : 0 < N.phi j k)
    {t : Real} (ht : 0 <= t) (r : Nat) :
    r < N.calendarTokenCount K omega t j k ↔
      N.calendarEventTime K omega ((j, k), r) <= t := by
  have hden : 0 < (((K : Nat) : Real) * N.phi j k) :=
    mul_pos (by positivity) hphi
  rcases ht.eq_or_lt with rfl | ht
  · have hepoch :
        0 < Network.renewalEpoch (omega j k) (r + 1) := by
      have hm := renewalEpoch_strictMono (omega j k) (hregular.1 j k)
      simpa using hm (Nat.zero_lt_succ r)
    simp [Network.calendarTokenCount_of_nonpos N K omega le_rfl,
      Network.calendarEventTime, not_le_of_gt (div_pos hepoch hden)]
  · let s := N.coordinateOperationalTime K t j k
    have hs : 0 < s := by
      simp only [s, Network.coordinateOperationalTime, max_eq_left ht.le]
      positivity
    have htop :
        Tendsto (Network.renewalEpoch (omega j k)) atTop atTop :=
      renewalEpoch_tendsto_atTop (omega j k) (hregular.2 j k)
    let c := N.calendarTokenCount K omega t j k
    have hc :
        Network.renewalEpoch (omega j k) c <= s /\
          s < Network.renewalEpoch (omega j k) (c + 1) := by
      have hiff := Network.unitPoissonCount_eq_iff_epoch
        (hregular.1 j k) htop hs c
      exact hiff.mp rfl
    have hmono :=
      (renewalEpoch_strictMono (omega j k) (hregular.1 j k)).monotone
    have hr :
        r < c ↔ Network.renewalEpoch (omega j k) (r + 1) <= s := by
      constructor
      · intro hrc
        exact (hmono (Nat.succ_le_iff.mpr hrc)).trans hc.1
      · intro hre
        by_contra hnot
        have hcr : c + 1 <= r + 1 :=
          Nat.succ_le_succ (Nat.le_of_not_gt hnot)
        exact (not_lt_of_ge ((hmono hcr).trans hre)) hc.2
    rw [hr]
    simp only [Network.calendarEventTime]
    rw [div_le_iff₀ hden]
    dsimp only [s, Network.coordinateOperationalTime]
    rw [max_eq_left ht.le]
    ring_nf

private def alignmentNodeList {E : Type*} (T : Real)
    (source target : E -> Real) (events : List E) :
    List (Real × Real) :=
  (0, 0) :: (events.map (fun e => (source e, target e)) ++ [(T, T)])

private theorem alignmentNodeList_pairwise {E : Type*} {T : Real}
    {source target : E -> Real} {events : List E}
    (hT : 0 < T)
    (hsource : events.Pairwise (fun e f => source e < source f))
    (htarget : events.Pairwise (fun e f => target e < target f))
    (hsource_mem : forall e, e ∈ events -> source e ∈ Ioo 0 T)
    (htarget_mem : forall e, e ∈ events -> target e ∈ Ioo 0 T) :
    (alignmentNodeList T source target events).Pairwise
      (fun p q => p.1 < q.1 /\ p.2 < q.2) := by
  rw [alignmentNodeList, List.pairwise_cons, List.pairwise_append]
  constructor
  · intro p hp
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hp
    rcases hp with (⟨e, he, rfl⟩ | rfl)
    · exact ⟨(hsource_mem e he).1, (htarget_mem e he).1⟩
    · exact ⟨hT, hT⟩
  · refine ⟨?_, by simp, ?_⟩
    · rw [List.pairwise_map]
      exact (hsource.and htarget).imp fun h => ⟨h.1, h.2⟩
    · intro p hp q hq
      simp only [List.mem_map] at hp
      simp only [List.mem_singleton] at hq
      rcases hp with ⟨e, he, rfl⟩
      subst q
      exact ⟨(hsource_mem e he).2, (htarget_mem e he).2⟩

private noncomputable def alignmentTimeNodes {E : Type*} (T : Real)
    (source target : E -> Real) (events : List E)
    (hT : 0 < T)
    (hsource : events.Pairwise (fun e f => source e < source f))
    (htarget : events.Pairwise (fun e f => target e < target f))
    (hsource_mem : forall e, e ∈ events -> source e ∈ Ioo 0 T)
    (htarget_mem : forall e, e ∈ events -> target e ∈ Ioo 0 T) :
    FiniteTimeNodes T where
  nodes := alignmentNodeList T source target events
  nodes_strict :=
    alignmentNodeList_pairwise hT hsource htarget hsource_mem htarget_mem
  first_node := by simp [alignmentNodeList]
  last_node := by
    change
      (((0, 0) :: events.map (fun e => (source e, target e))) ++
        [(T, T)]).getLast? = some (T, T)
    exact List.getLast?_concat

private def listMaxTimeError {E : Type*}
    (source target : E -> Real) : List E -> Real
  | [] => 0
  | e :: events =>
      max |target e - source e| (listMaxTimeError source target events)

private theorem listMaxTimeError_nonneg {E : Type*}
    (source target : E -> Real) (events : List E) :
    0 <= listMaxTimeError source target events := by
  induction events with
  | nil => simp [listMaxTimeError]
  | cons e events ih =>
      exact le_max_of_le_left (abs_nonneg (target e - source e))

private theorem foldr_alignment_eq_listMaxTimeError {E : Type*}
    (source target : E -> Real) (events : List E) :
    (events.map (fun e => (source e, target e))).foldr
        (fun p m => max |p.2 - p.1| m) 0 =
      listMaxTimeError source target events := by
  induction events with
  | nil => rfl
  | cons e events ih =>
      simp only [List.map_cons, List.foldr_cons, listMaxTimeError]
      rw [ih]

private theorem maxNodeDisplacement_alignmentTimeNodes {E : Type*}
    (T : Real) (source target : E -> Real) (events : List E)
    (hT hsource htarget hsource_mem htarget_mem) :
    (alignmentTimeNodes T source target events hT hsource htarget
      hsource_mem htarget_mem).maxNodeDisplacement =
        listMaxTimeError source target events := by
  simp only [FiniteTimeNodes.maxNodeDisplacement, alignmentTimeNodes,
    alignmentNodeList, List.foldr_cons, List.foldr_append,
    List.foldr_nil, sub_self, abs_zero, max_self]
  rw [foldr_alignment_eq_listMaxTimeError, max_eq_right
    (listMaxTimeError_nonneg source target events)]

private theorem listMaxTimeError_tendsto_zero {E : Type*}
    (source : E -> Real) (target : Nat -> E -> Real) (events : List E)
    (htarget : forall e, e ∈ events ->
      Tendsto (fun n => target n e) atTop (nhds (source e))) :
    Tendsto (fun n => listMaxTimeError source (target n) events)
      atTop (nhds 0) := by
  induction events with
  | nil => simp [listMaxTimeError]
  | cons e events ih =>
      have he :
          Tendsto (fun n => |target n e - source e|) atTop (nhds 0) := by
        convert
          ((htarget e (by simp)).sub tendsto_const_nhds).abs using 1 <;>
          simp
      have htail := ih (fun q hq => htarget q (by simp [hq]))
      simpa [listMaxTimeError] using he.max htail

private theorem eventually_target_mem_Ioo {E : Type*}
    (source : E -> Real) (target : Nat -> E -> Real)
    (T : Real) (events : List E)
    (hsource : forall e, e ∈ events -> source e ∈ Ioo 0 T)
    (htarget : forall e, e ∈ events ->
      Tendsto (fun n => target n e) atTop (nhds (source e))) :
    ∀ᶠ n in atTop, forall e, e ∈ events ->
      target n e ∈ Ioo 0 T := by
  induction events with
  | nil => simp
  | cons e events ih =>
      have he :
          ∀ᶠ n in atTop, target n e ∈ Ioo 0 T :=
        (htarget e (by simp)).eventually
          (Ioo_mem_nhds (hsource e (by simp)).1
            (hsource e (by simp)).2)
      have htail := ih
        (fun q hq => hsource q (by simp [hq]))
        (fun q hq => htarget q (by simp [hq]))
      filter_upwards [he, htail] with n hn hnt
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hn
      · exact hnt q hq

theorem calendarEventTime_le_delayedCalendarEventTime
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hpos : forall j k q, 0 < omega j k q)
    {j : Server} {k : Buffer} (hphi : 0 < N.phi j k)
    (n r : Nat) (hr : r < n) :
    N.calendarEventTime K omega ((j, k), r) <=
      delayedCalendarEventTime N K n omega ((j, k), r) := by
  have hden : 0 < (((K : Nat) : Real) * N.phi j k) :=
    mul_pos (by positivity) hphi
  rw [Network.calendarEventTime, delayedCalendarEventTime,
    Network.calendarEventTime, div_le_div_iff_of_pos_right hden]
  unfold Network.renewalEpoch
  apply Finset.sum_le_sum
  intro q hq
  exact (decode_encode_interarrival_bounds n q
    ((Finset.mem_range.mp hq).trans_le hr) omega hpos j k).1.le

theorem calendarEventTime_monotone_index
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega)
    {j : Server} {k : Buffer} (hphi : 0 < N.phi j k) :
    Monotone (fun r =>
      N.calendarEventTime K omega ((j, k), r)) := by
  intro r q hrq
  unfold Network.calendarEventTime
  exact div_le_div_of_nonneg_right
    ((renewalEpoch_strictMono (omega j k)
      (hregular.1 j k)).monotone (Nat.succ_le_succ hrq))
    (mul_nonneg (by positivity) hphi.le)

theorem delayedCalendarEventTime_no_extra_before
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega)
    {T : Real} (hT : 0 <= T)
    {j : Server} {k : Buffer} (hphi : 0 < N.phi j k)
    {n : Nat}
    (hn : N.calendarTokenCount K omega T j k < n)
    (r : Nat)
    (hrT : delayedCalendarEventTime N K n omega ((j, k), r) <= T) :
    r < N.calendarTokenCount K omega T j k := by
  let c := N.calendarTokenCount K omega T j k
  have hcT :
      T < N.calendarEventTime K omega ((j, k), c) := by
    have hcnot :
        Not (N.calendarEventTime K omega ((j, k), c) <= T) := by
      intro hc
      exact (Nat.lt_irrefl c)
        ((calendarTokenCount_lt_iff_eventTime_le N K omega hregular
          hphi hT c).mpr hc)
    exact lt_of_not_ge hcnot
  have hcd :
      N.calendarEventTime K omega ((j, k), c) <=
        delayedCalendarEventTime N K n omega ((j, k), c) :=
    calendarEventTime_le_delayedCalendarEventTime
      N K omega hregular.1 hphi n c hn
  have hdregular :
      IsRegularSample
        (decodeClockPrefix n (encodeClockPrefix n omega)) :=
    decodeClockPrefix_regular n (encodeClockPrefix n omega)
  have hdmono :
      Monotone (fun q =>
        delayedCalendarEventTime N K n omega ((j, k), q)) := by
    simpa [delayedCalendarEventTime] using
      calendarEventTime_monotone_index N K
        (decodeClockPrefix n (encodeClockPrefix n omega))
        hdregular hphi
  by_contra hrc
  have hcr : c <= r := Nat.le_of_not_gt hrc
  exact (not_lt_of_ge hrT)
    (hcT.trans_le (hcd.trans (hdmono hcr)))

theorem calendarEventTime_pos
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega)
    {j : Server} {k : Buffer} (hphi : 0 < N.phi j k)
    (r : Nat) :
    0 < N.calendarEventTime K omega ((j, k), r) := by
  have hepoch :
      0 < Network.renewalEpoch (omega j k) (r + 1) := by
    have hm := renewalEpoch_strictMono (omega j k) (hregular.1 j k)
    simpa using hm (Nat.zero_lt_succ r)
  exact div_pos hepoch (mul_pos (by positivity) hphi)

theorem calendarTokenCount_eq_of_event_alignment
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega)
    {T : Real} (hT : 0 < T)
    (hfin : (positiveRateCalendarJumpsOn N K omega T).Finite)
    (n : Nat)
    (hn : forall j k,
      N.calendarTokenCount K omega T j k < n)
    (e : TimeChange T)
    (hmap : forall event,
      event ∈ sortedPositiveRateCalendarJumps N K omega T hfin ->
      (((e (clampToHorizon T hT.le
        (N.calendarEventTime K omega event)) : Horizon T) : Real)) =
        delayedCalendarEventTime N K n omega event)
    (t : Horizon T) (j : Server) (k : Buffer) :
    N.calendarTokenCount K
        (decodeClockPrefix n (encodeClockPrefix n omega))
        (e t) j k =
      N.calendarTokenCount K omega t j k := by
  by_cases hphi : N.phi j k = 0
  · simp [Network.calendarTokenCount_of_phi_eq_zero N K _ _ j k hphi]
  have hphiPos : 0 < N.phi j k :=
    lt_of_le_of_ne (N.phi_nonneg j k) (Ne.symm hphi)
  have hdregular :
      IsRegularSample
        (decodeClockPrefix n (encodeClockPrefix n omega)) :=
    decodeClockPrefix_regular n (encodeClockPrefix n omega)
  have hiff (r : Nat) :
      r < N.calendarTokenCount K
          (decodeClockPrefix n (encodeClockPrefix n omega))
          (e t) j k ↔
        r < N.calendarTokenCount K omega t j k := by
    rw [calendarTokenCount_lt_iff_eventTime_le N K
      (decodeClockPrefix n (encodeClockPrefix n omega))
      hdregular hphiPos (e t).property.1 r]
    rw [calendarTokenCount_lt_iff_eventTime_le N K omega hregular
      hphiPos t.property.1 r]
    constructor
    · intro hdr
      change delayedCalendarEventTime N K n omega ((j, k), r) <=
        ((e t : Horizon T) : Real) at hdr
      have hrT :
          delayedCalendarEventTime N K n omega ((j, k), r) <= T :=
        hdr.trans (e t).property.2
      have hrcount :
          r < N.calendarTokenCount K omega T j k :=
        delayedCalendarEventTime_no_extra_before N K omega hregular
          hT.le hphiPos (hn j k) r hrT
      have hactualT :
          N.calendarEventTime K omega ((j, k), r) <= T :=
        (calendarTokenCount_lt_iff_eventTime_le N K omega hregular
          hphiPos hT.le r).mp hrcount
      have hactive :
          ((j, k), r) ∈ positiveRateCalendarJumpsOn N K omega T :=
        ⟨hphiPos, calendarEventTime_pos N K omega hregular hphiPos r,
          hactualT⟩
      have hlist :
          ((j, k), r) ∈
            sortedPositiveRateCalendarJumps N K omega T hfin :=
        (sortedPositiveRateCalendarJumps_mem
          N K omega T hfin ((j, k), r)).mpr hactive
      let s : Horizon T :=
        clampToHorizon T hT.le
          (N.calendarEventTime K omega ((j, k), r))
      have hs :
          (s : Real) = N.calendarEventTime K omega ((j, k), r) := by
        simp [s, clampToHorizon, hactive.2.1.le, hactive.2.2]
      have hes :
          ((e s : Horizon T) : Real) =
            delayedCalendarEventTime N K n omega ((j, k), r) := by
        exact hmap ((j, k), r) hlist
      have hest : e s <= e t := by
        change ((e s : Horizon T) : Real) <= ((e t : Horizon T) : Real)
        simpa [hes] using hdr
      have hst : s <= t := e.strictMono.le_iff_le.mp hest
      change (s : Real) <= (t : Real) at hst
      rw [hs] at hst
      exact hst
    · intro har
      have hactualT :
          N.calendarEventTime K omega ((j, k), r) <= T :=
        har.trans t.property.2
      have hactive :
          ((j, k), r) ∈ positiveRateCalendarJumpsOn N K omega T :=
        ⟨hphiPos, calendarEventTime_pos N K omega hregular hphiPos r,
          hactualT⟩
      have hlist :
          ((j, k), r) ∈
            sortedPositiveRateCalendarJumps N K omega T hfin :=
        (sortedPositiveRateCalendarJumps_mem
          N K omega T hfin ((j, k), r)).mpr hactive
      let s : Horizon T :=
        clampToHorizon T hT.le
          (N.calendarEventTime K omega ((j, k), r))
      have hs :
          (s : Real) = N.calendarEventTime K omega ((j, k), r) := by
        simp [s, clampToHorizon, hactive.2.1.le, hactive.2.2]
      have hes :
          ((e s : Horizon T) : Real) =
            delayedCalendarEventTime N K n omega ((j, k), r) := by
        exact hmap ((j, k), r) hlist
      have hst : s <= t := by
        change (s : Real) <= (t : Real)
        rw [hs]
        exact har
      have hest := e.strictMono.monotone hst
      change
        delayedCalendarEventTime N K n omega ((j, k), r) <=
          ((e t : Horizon T) : Real)
      rw [← hes]
      exact hest
  apply le_antisymm
  · by_contra hle
    have hlt :
        N.calendarTokenCount K omega t j k <
          N.calendarTokenCount K
            (decodeClockPrefix n (encodeClockPrefix n omega))
            (e t) j k := Nat.lt_of_not_ge hle
    exact (Nat.lt_irrefl _)
      ((hiff (N.calendarTokenCount K omega t j k)).mp hlt)
  · by_contra hle
    have hlt :
        N.calendarTokenCount K
            (decodeClockPrefix n (encodeClockPrefix n omega))
            (e t) j k <
          N.calendarTokenCount K omega t j k :=
      Nat.lt_of_not_ge hle
    exact (Nat.lt_irrefl _)
      ((hiff (N.calendarTokenCount K
        (decodeClockPrefix n (encodeClockPrefix n omega))
        (e t) j k)).mpr hlt)

theorem pathError_delayedCalendarPath_eq_zero
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega)
    {T : Real} (hT : 0 < T)
    (hfin : (positiveRateCalendarJumpsOn N K omega T).Finite)
    (n : Nat)
    (hn : forall j k,
      N.calendarTokenCount K omega T j k < n)
    (e : TimeChange T)
    (hmap : forall event,
      event ∈ sortedPositiveRateCalendarJumps N K omega T hfin ->
      (((e (clampToHorizon T hT.le
        (N.calendarEventTime K omega event)) : Horizon T) : Real)) =
        delayedCalendarEventTime N K n omega event) :
    pathError (delayedCalendarPath N T K n omega)
      (calendarPath N T K omega) e = 0 := by
  have hdregular :
      IsRegularSample
        (decodeClockPrefix n (encodeClockPrefix n omega)) :=
    decodeClockPrefix_regular n (encodeClockPrefix n omega)
  have hdpath :=
    calendarPath_toFun_eq N T K
      (decodeClockPrefix n (encodeClockPrefix n omega)) hdregular
  have hapath := calendarPath_toFun_eq N T K omega hregular
  apply le_antisymm
  · unfold pathError
    apply iSup_le
    intro t
    apply iSup_le
    intro j
    apply iSup_le
    intro k
    have hcount :=
      calendarTokenCount_eq_of_event_alignment N K omega hregular hT
        hfin n hn e hmap t j k
    have hvalue :
        delayedCalendarPath N T K n omega (e t) j k =
          calendarPath N T K omega t j k := by
      change
        (calendarPath N T K
          (decodeClockPrefix n (encodeClockPrefix n omega))).toFun
            (e t) j k =
          (calendarPath N T K omega).toFun t j k
      rw [hdpath, hapath]
      dsimp only [calendarInputFunction, Network.calendarScaledInput]
      rw [hcount]
    simp [hvalue]
  · exact bot_le

theorem delayedCalendarPath_tendsto_j1_of_regular
    (N : Network Buffer Server) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    {T : Real} (hT : 0 < T)
    (hregular : IsRegularSample omega)
    (hfin : (positiveRateCalendarJumpsOn N K omega T).Finite)
    (hnoT : forall j k, 0 < N.phi j k -> forall r,
      N.calendarEventTime K omega ((j, k), r) ≠ T)
    (hcross : forall j k j' k',
      0 < N.phi j k -> 0 < N.phi j' k' ->
      (j, k) ≠ (j', k') -> forall r q,
        N.calendarEventTime K omega ((j, k), r) ≠
          N.calendarEventTime K omega ((j', k'), q)) :
    Tendsto (fun n => delayedCalendarPath N T K n omega)
      atTop (nhds (calendarPath N T K omega)) := by
  let events :=
    sortedPositiveRateCalendarJumps N K omega T hfin
  let source : Network.CalendarEvent
      (Buffer := Buffer) (Server := Server) -> Real :=
    N.calendarEventTime K omega
  let target : Nat -> Network.CalendarEvent
      (Buffer := Buffer) (Server := Server) -> Real :=
    fun n => delayedCalendarEventTime N K n omega
  have hsource_pairwise :
      events.Pairwise (fun a b => source a < source b) := by
    exact sortedPositiveRateCalendarJumps_pairwise
      N K omega T hfin hregular.1 hcross
  have hsource_mem :
      forall event, event ∈ events -> source event ∈ Ioo 0 T := by
    intro event hevent
    have he :=
      (sortedPositiveRateCalendarJumps_mem
        N K omega T hfin event).mp hevent
    have hne := hnoT event.1.1 event.1.2 he.1 event.2
    exact ⟨he.2.1, lt_of_le_of_ne he.2.2 hne⟩
  have htarget_tendsto :
      forall event, event ∈ events ->
        Tendsto (fun n => target n event) atTop
          (nhds (source event)) := by
    intro event hevent
    exact delayedCalendarEventTime_tendsto
      N K omega hregular.1 event
  have htarget_pairwise :
      ∀ᶠ n in atTop,
        events.Pairwise (fun a b => target n a < target n b) := by
    exact eventually_delayedCalendarEventTime_pairwise
      N K omega hregular.1 events hsource_pairwise
  have htarget_mem :
      ∀ᶠ n in atTop, forall event, event ∈ events ->
        target n event ∈ Ioo 0 T :=
    eventually_target_mem_Ioo source target T events
      hsource_mem htarget_tendsto
  have hprefix :
      ∀ᶠ n in atTop, forall j k,
        N.calendarTokenCount K omega T j k < n := by
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro k
    exact eventually_gt_atTop
      (N.calendarTokenCount K omega T j k)
  have hmax :
      Tendsto
        (fun n => listMaxTimeError source (target n) events)
        atTop (nhds 0) :=
    listMaxTimeError_tendsto_zero source target events htarget_tendsto
  have hupper :
      Tendsto
        (fun n =>
          ENNReal.ofReal (listMaxTimeError source (target n) events))
        atTop (nhds 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hmax
  have hbound :
      ∀ᶠ n in atTop,
        j1EDist (delayedCalendarPath N T K n omega)
          (calendarPath N T K omega) <=
        ENNReal.ofReal
          (listMaxTimeError source (target n) events) := by
    filter_upwards [htarget_pairwise, htarget_mem, hprefix] with
      n htarget_pairwise_n htarget_mem_n hprefix_n
    let d : FiniteTimeNodes T :=
      alignmentTimeNodes T source (target n) events hT
        hsource_pairwise htarget_pairwise_n
        hsource_mem htarget_mem_n
    let e : TimeChange T :=
      FiniteTimeNodes.finitePiecewiseAffineTimeChange T hT d
    have hmap : forall event, event ∈ events ->
        (((e (clampToHorizon T hT.le (source event)) :
          Horizon T) : Real)) = target n event := by
      intro event hevent
      have hp :
          (source event, target n event) ∈ d.nodes := by
        change
          (source event, target n event) ∈
            alignmentNodeList T source (target n) events
        simp only [alignmentNodeList, List.mem_cons, List.mem_append,
          List.mem_map, List.mem_singleton]
        exact Or.inr (Or.inl ⟨event, hevent, rfl⟩)
      have hpH : source event ∈ Icc 0 T :=
        ⟨(hsource_mem event hevent).1.le,
          (hsource_mem event hevent).2.le⟩
      have hc :
          clampToHorizon T hT.le (source event) =
            (⟨source event, hpH⟩ : Horizon T) := by
        apply Subtype.ext
        simp [clampToHorizon, hpH.1, hpH.2]
      rw [hc]
      exact FiniteTimeNodes.finitePiecewiseAffineTimeChange_apply_node
        hT d (source event, target n event) hp hpH
    have hpath :
        pathError (delayedCalendarPath N T K n omega)
          (calendarPath N T K omega) e = 0 := by
      apply pathError_delayedCalendarPath_eq_zero
        N K omega hregular hT hfin n hprefix_n e
      simpa [events, source, target] using hmap
    calc
      j1EDist (delayedCalendarPath N T K n omega)
          (calendarPath N T K omega) <=
          symmetricJ1EDist (delayedCalendarPath N T K n omega)
            (calendarPath N T K omega) :=
        inf_le_left
      _ <= j1Cost (delayedCalendarPath N T K n omega)
            (calendarPath N T K omega) e :=
        symmetricJ1EDist_le_j1Cost _ _ e
      _ = timeError e := by simp [j1Cost, hpath]
      _ <= ENNReal.ofReal d.maxNodeDisplacement :=
        FiniteTimeNodes.timeError_finitePiecewiseAffineTimeChange_le hT d
      _ = ENNReal.ofReal
          (listMaxTimeError source (target n) events) := by
        congr 1
        exact maxNodeDisplacement_alignmentTimeNodes
          T source (target n) events hT hsource_pairwise
            htarget_pairwise_n hsource_mem htarget_mem_n
  rw [tendsto_iff_edist_tendsto_0]
  change Tendsto
    (fun n => j1EDist (delayedCalendarPath N T K n omega)
      (calendarPath N T K omega)) atTop (nhds 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => bot_le) hbound

/-- The finite clock-prefix paths converge almost surely in the exact J1
topology on every positive horizon. -/
theorem delayedCalendarPath_tendsto_j1_ae
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) (K : PNat) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      Tendsto (fun n => delayedCalendarPath N T K n omega)
        atTop (nhds (calendarPath N T K omega)) := by
  filter_upwards [regularSample_ae N,
    noSimultaneousPoissonJumps_ae N K hT,
    noHorizonPoissonJump_ae N K T] with
      omega hregular hsimple hnoT
  exact delayedCalendarPath_tendsto_j1_of_regular
    N K omega hT hregular hsimple.1 hnoT hsimple.2.2

/-- On a positive horizon, the calendar-time Poisson input is almost
everywhere measurable into the Borel sigma algebra of the genuine J1
topology. -/
theorem calendarPath_aemeasurable
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) (K : PNat) :
    AEMeasurable (calendarPath N T K) N.calendarPoissonMeasure := by
  exact aemeasurable_of_tendsto_metrizable_ae'
    (fun n => delayedCalendarPath_aemeasurable N T K n)
    (delayedCalendarPath_tendsto_j1_ae N hT K)

/-- The concrete J1-valued calendar path has exactly the mapped law used
in the LDP statement. -/
theorem calendarPath_hasLaw
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) (K : Nat) :
    HasLaw
      (calendarPath N T (positiveSize K))
      (calendarPathLaw N T K)
      N.calendarPoissonMeasure where
  aemeasurable := calendarPath_aemeasurable N hT (positiveSize K)
  map_eq := rfl

/-- Every speed-indexed calendar path law is an actual probability
pushforward on a positive horizon. -/
theorem calendarPathLaw_isProbabilityMeasure
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) (K : Nat) :
    IsProbabilityMeasure (calendarPathLaw N T K) := by
  unfold calendarPathLaw
  exact Measure.isProbabilityMeasure_map
    (calendarPath_aemeasurable N hT (positiveSize K))

/-- Evaluation of the genuine calendar-path pushforward on a measurable
J1 event. -/
theorem calendarPathLaw_apply
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) (K : Nat)
    {s : Set (Path (Buffer := Buffer) (Server := Server) T)}
    (hs : MeasurableSet s) :
    calendarPathLaw N T K s =
      N.calendarPoissonMeasure
        ((calendarPath N T (positiveSize K)) ⁻¹' s) := by
  unfold calendarPathLaw
  exact Measure.map_apply_of_aemeasurable
    (calendarPath_aemeasurable N hT (positiveSize K)) hs

end StateDepMOR.PoissonSamplePath

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]

/-- A finite, strictly increasing partition of `[0,T]`. -/
structure ActionPartition (T : Real) where
  intervals : Nat
  point : Fin (intervals + 1) -> Real
  point_zero : point 0 = 0
  point_last : point (Fin.last intervals) = T
  strictMono_point : StrictMono point

namespace ActionPartition

variable {T : Real} (P : ActionPartition T)

def left (i : Fin P.intervals) : Real := P.point i.castSucc

def right (i : Fin P.intervals) : Real := P.point i.succ

def width (i : Fin P.intervals) : Real := P.right i - P.left i

theorem left_lt_right (i : Fin P.intervals) : P.left i < P.right i := by
  exact P.strictMono_point Fin.castSucc_lt_succ

theorem width_pos (i : Fin P.intervals) : 0 < P.width i :=
  sub_pos.mpr (P.left_lt_right i)

theorem cell_subset {T : Real} (_hT : 0 <= T)
    (P : ActionPartition T) (i : Fin P.intervals) :
    Icc (P.left i) (P.right i) ⊆ Icc (0 : Real) T := by
  intro t ht
  have hleft_nonneg : 0 <= P.left i := by
    rw [left, ← P.point_zero]
    exact P.strictMono_point.monotone (Fin.zero_le _)
  have hright_le : P.right i <= T := by
    calc
      P.right i = P.point i.succ := rfl
      _ <= P.point (Fin.last P.intervals) :=
        P.strictMono_point.monotone (Fin.le_last _)
      _ = T := P.point_last
  exact ⟨hleft_nonneg.trans ht.1, ht.2.trans hright_le⟩

noncomputable def natPoint (k : Nat) : Real :=
  if h : k < P.intervals + 1 then P.point ⟨k, h⟩ else T

theorem natPoint_eq_point (k : Nat) (hk : k < P.intervals + 1) :
    P.natPoint k = P.point ⟨k, hk⟩ := by
  simp [natPoint, hk]

@[simp]
theorem natPoint_zero : P.natPoint 0 = 0 := by
  rw [P.natPoint_eq_point 0 (Nat.zero_lt_succ _)]
  exact P.point_zero

@[simp]
theorem natPoint_intervals : P.natPoint P.intervals = T := by
  rw [P.natPoint_eq_point P.intervals (Nat.lt_add_one _)]
  exact P.point_last

theorem natPoint_eq_left (k : Nat) (hk : k < P.intervals) :
    P.natPoint k = P.left ⟨k, hk⟩ := by
  rw [P.natPoint_eq_point k (hk.trans (Nat.lt_succ_self _))]
  rfl

theorem natPoint_succ_eq_right (k : Nat) (hk : k < P.intervals) :
    P.natPoint (k + 1) = P.right ⟨k, hk⟩ := by
  rw [P.natPoint_eq_point (k + 1) (Nat.add_lt_add_right hk 1)]
  rfl

end ActionPartition

/-- The matrix chord rate on one cell of a partition. -/
noncomputable def partitionChord
    (A : MatrixPath Server Buffer) {T : Real}
    (P : ActionPartition T) (i : Fin P.intervals) :
    Server -> Buffer -> Real :=
  fun j k => (A (P.right i) j k - A (P.left i) j k) / P.width i

/-- The finite-dimensional Poisson action of the chords of a path. -/
noncomputable def poissonPartitionAction
    (N : Network Buffer Server) (A : MatrixPath Server Buffer)
    {T : Real} (P : ActionPartition T) : ENNReal :=
  ∑ i : Fin P.intervals,
    ENNReal.ofReal (P.width i) * N.localRate (partitionChord A P i)

/-- The finite real Poisson cost for a positive nominal rate, written in a
form whose convexity is immediate from convexity of `x log x`. -/
noncomputable def positivePoissonCostReal (nominal candidate : Real) : Real :=
  candidate * Real.log candidate -
    (Real.log nominal + 1) * candidate + nominal

theorem positivePoissonCostReal_eq
    {nominal candidate : Real} (hnominal : 0 < nominal)
    (hcandidate : 0 <= candidate) :
    positivePoissonCostReal nominal candidate =
      poissonCostReal nominal candidate := by
  rcases hcandidate.eq_or_lt with rfl | hcandidate
  · simp [positivePoissonCostReal, poissonCostReal]
  · rw [positivePoissonCostReal, poissonCostReal,
      Real.log_div hcandidate.ne' hnominal.ne']
    ring

theorem continuous_positivePoissonCostReal (nominal : Real) :
    Continuous (positivePoissonCostReal nominal) := by
  unfold positivePoissonCostReal
  fun_prop

theorem convexOn_positivePoissonCostReal (nominal : Real) :
    ConvexOn Real (Ici 0) (positivePoissonCostReal nominal) := by
  have hlinear :
      ConcaveOn Real (Ici (0 : Real))
        (fun x : Real => (Real.log nominal + 1) * x) :=
    by
      refine ⟨convex_Ici 0, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [smul_eq_mul]
      ring_nf
      exact le_rfl
  refine ((Real.convexOn_mul_log.sub hlinear).add_const nominal).congr ?_
  intro x hx
  simp only [Pi.sub_apply, Pi.add_apply]
  unfold positivePoissonCostReal
  ring

theorem poissonCost_le_localRate
    (N : Network Buffer Server) (f : Server -> Buffer -> Real)
    (j : Server) (k : Buffer) :
    poissonCost (N.phi j k) (f j k) <= N.localRate f := by
  classical
  rw [Network.localRate]
  calc
    poissonCost (N.phi j k) (f j k) <=
        ∑ q : Buffer, poissonCost (N.phi j q) (f j q) :=
      Finset.single_le_sum
        (f := fun q : Buffer => poissonCost (N.phi j q) (f j q))
        (fun _ _ => bot_le) (Finset.mem_univ k)
    _ <= ∑ q : Server, ∑ r : Buffer,
        poissonCost (N.phi q r) (f q r) :=
      Finset.single_le_sum
        (f := fun q : Server =>
          ∑ r : Buffer, poissonCost (N.phi q r) (f q r))
        (fun _ _ => bot_le) (Finset.mem_univ j)

theorem measurable_localRate_general
    (N : Network Buffer Server) (A : MatrixPath Server Buffer) :
    Measurable (fun t => N.localRate (pathDerivative A t)) := by
  classical
  unfold Network.localRate pathDerivative
  apply Finset.measurable_fun_sum
  intro j hj
  apply Finset.measurable_fun_sum
  intro k hk
  exact (PoissonSamplePath.measurable_poissonCost (N.phi j k)).comp
    (measurable_deriv (fun s => A s j k))

theorem finiteAction_localRate_lt_top_ae
    (N : Network Buffer Server) (T : Real)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      N.localRate (pathDerivative A t) < (⊤ : ENNReal) := by
  classical
  have hvalid := poissonPathRate_ne_top_implies_valid N T A hfinite
  have hint :
      (∫⁻ t in Icc 0 T, N.localRate (pathDerivative A t)) ≠
        (⊤ : ENNReal) := by
    simpa [poissonPathRate, hvalid] using hfinite
  exact ae_lt_top (measurable_localRate_general N A) hint

theorem finiteAction_derivative_nonneg_ae
    (N : Network Buffer Server) (T : Real)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (j : Server) (k : Buffer) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      0 <= pathDerivative A t j k := by
  filter_upwards [finiteAction_localRate_lt_top_ae N T A hfinite] with t ht
  by_contra hneg
  have hcost :
      poissonCost (N.phi j k) (pathDerivative A t j k) = (⊤ : ENNReal) :=
    poissonCost_of_candidate_neg (lt_of_not_ge hneg)
  have hle := poissonCost_le_localRate N (pathDerivative A t) j k
  rw [hcost] at hle
  exact ht.ne (top_unique hle)

theorem finiteAction_derivative_integrableOn
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (j : Server) (k : Buffer) :
    IntegrableOn (fun t => pathDerivative A t j k) (Icc 0 T) volume := by
  have hac :=
    (poissonPathRate_ne_top_implies_valid N T A hfinite).1 j k
  have hint := hac.intervalIntegrable_deriv
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT] at hint
  simpa [pathDerivative] using hint

theorem finiteAction_derivative_integrableOn_matrix
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal)) :
    IntegrableOn (pathDerivative A) (Icc 0 T) volume := by
  unfold IntegrableOn
  rw [integrable_pi_iff]
  intro j
  rw [integrable_pi_iff]
  intro k
  exact finiteAction_derivative_integrableOn N hT A hfinite j k

theorem finiteAction_zeroDerivative_ae
    (N : Network Buffer Server) (T : Real)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (j : Server) (k : Buffer) (hphi : N.phi j k = 0) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      pathDerivative A t j k = 0 := by
  filter_upwards [finiteAction_localRate_lt_top_ae N T A hfinite] with t ht
  exact N.localRate_ne_top_implies_zero_of_phi_eq_zero
    (pathDerivative A t) ht.ne j k hphi

theorem finiteAction_localRate_toReal_integrableOn
    (N : Network Buffer Server) (T : Real)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal)) :
    IntegrableOn
      (fun t => (N.localRate (pathDerivative A t)).toReal)
      (Icc 0 T) volume := by
  have hvalid := poissonPathRate_ne_top_implies_valid N T A hfinite
  have hint :
      (∫⁻ t in Icc 0 T, N.localRate (pathDerivative A t)) ≠
        (⊤ : ENNReal) := by
    simpa [poissonPathRate, hvalid] using hfinite
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_localRate_general N A).aemeasurable hint

theorem finiteAction_positiveCost_integrableOn
    (N : Network Buffer Server) (T : Real)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (j : Server) (k : Buffer) (hphi : 0 < N.phi j k) :
    IntegrableOn
      (fun t =>
        positivePoissonCostReal (N.phi j k) (pathDerivative A t j k))
      (Icc 0 T) volume := by
  classical
  unfold IntegrableOn
  refine (finiteAction_localRate_toReal_integrableOn N T A hfinite).mono'
    ?_ ?_
  · exact (continuous_positivePoissonCostReal (N.phi j k)).aestronglyMeasurable.comp_measurable
      (measurable_deriv (fun s => A s j k))
  · filter_upwards
      [finiteAction_localRate_lt_top_ae N T A hfinite,
       finiteAction_derivative_nonneg_ae N T A hfinite j k] with t ht hnonneg
    have hcost_nonneg :=
      poissonCostReal_nonneg hphi hnonneg
    have hpositive :
        0 <= positivePoissonCostReal (N.phi j k)
          (pathDerivative A t j k) := by
      rw [positivePoissonCostReal_eq hphi hnonneg]
      exact hcost_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hpositive]
    rw [positivePoissonCostReal_eq hphi hnonneg]
    have hcost :
        (poissonCost (N.phi j k) (pathDerivative A t j k)).toReal =
          poissonCostReal (N.phi j k) (pathDerivative A t j k) := by
      rw [poissonCost_of_nominal_pos hphi hnonneg]
      change (ENNReal.ofReal
        (poissonCostReal (N.phi j k) (pathDerivative A t j k))).toReal =
          poissonCostReal (N.phi j k) (pathDerivative A t j k)
      exact ENNReal.toReal_ofReal hcost_nonneg
    rw [← hcost]
    exact ENNReal.toReal_mono ht.ne
      (poissonCost_le_localRate N (pathDerivative A t) j k)

theorem positivePoissonCostReal_setAverage_le
    {nominal a b : Real} (_hnominal : 0 < nominal) (hab : a < b)
    {f : Real -> Real}
    (hf_nonneg : ∀ᵐ t ∂volume.restrict (Icc a b), 0 <= f t)
    (hf_int : IntegrableOn f (Icc a b) volume)
    (hcost_int :
      IntegrableOn (fun t => positivePoissonCostReal nominal (f t))
        (Icc a b) volume) :
    positivePoissonCostReal nominal (⨍ t in Icc a b, f t ∂volume) <=
      ⨍ t in Icc a b, positivePoissonCostReal nominal (f t) ∂volume := by
  apply (convexOn_positivePoissonCostReal nominal).map_set_average_le
    (continuous_positivePoissonCostReal nominal).continuousOn
    isClosed_Ici
  · rw [Real.volume_Icc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  · exact hf_nonneg
  · exact hf_int
  · simpa [Function.comp_def] using hcost_int

theorem derivative_setAverage_eq_partitionChord
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (P : ActionPartition T) (i : Fin P.intervals)
    (j : Server) (k : Buffer) :
    (⨍ t in Icc (P.left i) (P.right i),
        pathDerivative A t j k ∂volume) =
      partitionChord A P i j k := by
  have hvalid := poissonPathRate_ne_top_implies_valid N T A hfinite
  have hsub :
      uIcc (P.left i) (P.right i) ⊆ uIcc (0 : Real) T := by
    rw [uIcc_of_le (P.left_lt_right i).le, uIcc_of_le hT]
    exact P.cell_subset hT i
  have hac :=
    (hvalid.1 j k).mono hsub
  rw [setAverage_eq, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (P.left_lt_right i).le)]
  simp only [smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (P.left_lt_right i).le]
  change (P.width i)⁻¹ *
      (∫ t in P.left i..P.right i, deriv (fun s => A s j k) t) =
    partitionChord A P i j k
  rw [hac.integral_deriv_eq_sub]
  unfold partitionChord
  rw [div_eq_inv_mul]

theorem positiveCost_partitionChord_mul_width_le_integral
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (P : ActionPartition T) (i : Fin P.intervals)
    (j : Server) (k : Buffer) (hphi : 0 < N.phi j k) :
    P.width i * positivePoissonCostReal (N.phi j k)
        (partitionChord A P i j k) <=
      ∫ t in Icc (P.left i) (P.right i),
        positivePoissonCostReal (N.phi j k)
          (pathDerivative A t j k) ∂volume := by
  have hsub := P.cell_subset hT i
  have hnonneg_global :=
    finiteAction_derivative_nonneg_ae N T A hfinite j k
  have hnonneg_ambient :
      ∀ᵐ t ∂volume, t ∈ Icc (0 : Real) T ->
        0 <= pathDerivative A t j k :=
    (ae_restrict_iff' measurableSet_Icc).mp hnonneg_global
  have hnonneg_cell :
      ∀ᵐ t ∂volume.restrict (Icc (P.left i) (P.right i)),
        0 <= pathDerivative A t j k :=
    (ae_restrict_iff' measurableSet_Icc).mpr <| by
      filter_upwards [hnonneg_ambient] with t ht
      intro hcell
      exact ht (hsub hcell)
  have hderiv_int :=
    (finiteAction_derivative_integrableOn N hT A hfinite j k).mono_set hsub
  have hcost_int :=
    (finiteAction_positiveCost_integrableOn N T A hfinite j k hphi).mono_set hsub
  have hjensen :=
    positivePoissonCostReal_setAverage_le hphi (P.left_lt_right i)
      hnonneg_cell hderiv_int hcost_int
  rw [derivative_setAverage_eq_partitionChord N hT A hfinite P i j k,
    setAverage_eq, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (P.left_lt_right i).le)] at hjensen
  simp only [smul_eq_mul] at hjensen
  calc
    P.width i * positivePoissonCostReal (N.phi j k)
        (partitionChord A P i j k)
      <= P.width i * ((P.width i)⁻¹ *
          ∫ t in Icc (P.left i) (P.right i),
            positivePoissonCostReal (N.phi j k)
              (pathDerivative A t j k) ∂volume) :=
        mul_le_mul_of_nonneg_left hjensen (P.width_pos i).le
    _ = ∫ t in Icc (P.left i) (P.right i),
          positivePoissonCostReal (N.phi j k)
            (pathDerivative A t j k) ∂volume := by
      rw [← mul_assoc, mul_inv_cancel₀ (P.width_pos i).ne', one_mul]

theorem partitionChord_nonneg
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (P : ActionPartition T) (i : Fin P.intervals)
    (j : Server) (k : Buffer) :
    0 <= partitionChord A P i j k := by
  have hsub := P.cell_subset hT i
  have hnonneg_ambient :
      ∀ᵐ t ∂volume, t ∈ Icc (0 : Real) T ->
        0 <= pathDerivative A t j k :=
    (ae_restrict_iff' measurableSet_Icc).mp
      (finiteAction_derivative_nonneg_ae N T A hfinite j k)
  have hnonneg_cell :
      ∀ᵐ t ∂volume.restrict (Icc (P.left i) (P.right i)),
        pathDerivative A t j k ∈ Ici (0 : Real) :=
    (ae_restrict_iff' measurableSet_Icc).mpr <| by
      filter_upwards [hnonneg_ambient] with t ht
      intro hcell
      exact ht (hsub hcell)
  have hderiv_int :=
    (finiteAction_derivative_integrableOn N hT A hfinite j k).mono_set hsub
  have havg :
      (⨍ t in Icc (P.left i) (P.right i),
        pathDerivative A t j k ∂volume) ∈ Ici (0 : Real) :=
    (convex_Ici (0 : Real)).set_average_mem isClosed_Ici
      (by
        rw [Real.volume_Icc]
        exact (ENNReal.ofReal_pos.mpr
          (sub_pos.mpr (P.left_lt_right i))).ne')
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      hnonneg_cell hderiv_int
  rw [derivative_setAverage_eq_partitionChord N hT A hfinite P i j k] at havg
  exact havg

theorem partitionChord_eq_zero_of_phi_eq_zero
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (P : ActionPartition T) (i : Fin P.intervals)
    (j : Server) (k : Buffer) (hphi : N.phi j k = 0) :
    partitionChord A P i j k = 0 := by
  rw [← derivative_setAverage_eq_partitionChord N hT A hfinite P i j k,
    setAverage_eq]
  have hzero_ambient :
      ∀ᵐ t ∂volume, t ∈ Icc (0 : Real) T ->
        pathDerivative A t j k = 0 :=
    (ae_restrict_iff' measurableSet_Icc).mp
      (finiteAction_zeroDerivative_ae N T A hfinite j k hphi)
  have hzero_cell :
      (fun t => pathDerivative A t j k) =ᵐ[
        volume.restrict (Icc (P.left i) (P.right i))] 0 :=
    (ae_restrict_iff' measurableSet_Icc).mpr <| by
      filter_upwards [hzero_ambient] with t ht
      intro hcell
      exact ht (P.cell_subset hT i hcell)
  rw [integral_congr_ae hzero_cell]
  simp

theorem poissonCost_partitionChord_mul_width_le_lintegral
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (P : ActionPartition T) (i : Fin P.intervals)
    (j : Server) (k : Buffer) :
    ENNReal.ofReal (P.width i) *
        poissonCost (N.phi j k) (partitionChord A P i j k) <=
      ∫⁻ t in Icc (P.left i) (P.right i),
        poissonCost (N.phi j k) (pathDerivative A t j k) := by
  rcases (N.phi_nonneg j k).eq_or_lt with hphi | hphi
  · have hchord :=
      partitionChord_eq_zero_of_phi_eq_zero
        N hT A hfinite P i j k hphi.symm
    rw [← hphi, hchord, poissonCost_zero_zero, mul_zero]
    exact bot_le
  · have hchord_nonneg :=
      partitionChord_nonneg N hT A hfinite P i j k
    have hcost_chord_nonneg :=
      poissonCostReal_nonneg hphi hchord_nonneg
    have hreal :=
      positiveCost_partitionChord_mul_width_le_integral
        N hT A hfinite P i j k hphi
    have hsub := P.cell_subset hT i
    have hcost_int :=
      (finiteAction_positiveCost_integrableOn
        N T A hfinite j k hphi).mono_set hsub
    have hderiv_nonneg_ambient :
        ∀ᵐ t ∂volume, t ∈ Icc (0 : Real) T ->
          0 <= pathDerivative A t j k :=
      (ae_restrict_iff' measurableSet_Icc).mp
        (finiteAction_derivative_nonneg_ae N T A hfinite j k)
    have hderiv_nonneg_cell :
        ∀ᵐ t ∂volume.restrict (Icc (P.left i) (P.right i)),
          0 <= pathDerivative A t j k :=
      (ae_restrict_iff' measurableSet_Icc).mpr <| by
        filter_upwards [hderiv_nonneg_ambient] with t ht
        intro hcell
        exact ht (hsub hcell)
    have hpositive_nonneg :
        ∀ᵐ t ∂volume.restrict (Icc (P.left i) (P.right i)),
          0 <= positivePoissonCostReal (N.phi j k)
            (pathDerivative A t j k) :=
      hderiv_nonneg_cell.mono fun t ht => by
        rw [positivePoissonCostReal_eq hphi ht]
        exact poissonCostReal_nonneg hphi ht
    calc
      ENNReal.ofReal (P.width i) *
          poissonCost (N.phi j k) (partitionChord A P i j k)
        = ENNReal.ofReal
            (P.width i * positivePoissonCostReal (N.phi j k)
              (partitionChord A P i j k)) := by
          rw [ENNReal.ofReal_mul (P.width_pos i).le,
            poissonCost_of_nominal_pos hphi hchord_nonneg,
            positivePoissonCostReal_eq hphi hchord_nonneg]
          rfl
      _ <= ENNReal.ofReal
          (∫ t in Icc (P.left i) (P.right i),
            positivePoissonCostReal (N.phi j k)
              (pathDerivative A t j k) ∂volume) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ∫⁻ t in Icc (P.left i) (P.right i),
          ENNReal.ofReal (positivePoissonCostReal (N.phi j k)
            (pathDerivative A t j k)) :=
        ofReal_integral_eq_lintegral_ofReal hcost_int hpositive_nonneg
      _ = ∫⁻ t in Icc (P.left i) (P.right i),
          poissonCost (N.phi j k) (pathDerivative A t j k) := by
        apply lintegral_congr_ae
        filter_upwards [hderiv_nonneg_cell] with t ht
        rw [poissonCost_of_nominal_pos hphi ht,
          positivePoissonCostReal_eq hphi ht]
        rfl

theorem localRate_partitionChord_mul_width_le_lintegral
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (P : ActionPartition T) (i : Fin P.intervals) :
    ENNReal.ofReal (P.width i) * N.localRate (partitionChord A P i) <=
      ∫⁻ t in Icc (P.left i) (P.right i),
        N.localRate (pathDerivative A t) := by
  classical
  unfold Network.localRate
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  calc
    ∑ j : Server, ∑ k : Buffer,
        ENNReal.ofReal (P.width i) *
          poissonCost (N.phi j k) (partitionChord A P i j k)
      <= ∑ j : Server, ∑ k : Buffer,
          ∫⁻ t in Icc (P.left i) (P.right i),
            poissonCost (N.phi j k) (pathDerivative A t j k) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact poissonCost_partitionChord_mul_width_le_lintegral
          N hT A hfinite P i j k
    _ = ∫⁻ t in Icc (P.left i) (P.right i),
          ∑ j : Server, ∑ k : Buffer,
            poissonCost (N.phi j k) (pathDerivative A t j k) := by
      rw [lintegral_finsetSum]
      · congr with j
        rw [lintegral_finsetSum]
        intro k hk
        exact (PoissonSamplePath.measurable_poissonCost (N.phi j k)).comp
          (measurable_deriv (fun s => A s j k))
      · intro j hj
        apply Finset.measurable_fun_sum
        intro k hk
        exact (PoissonSamplePath.measurable_poissonCost (N.phi j k)).comp
          (measurable_deriv (fun s => A s j k))

theorem sum_intervalIntegral_partition
    {T : Real} (hT : 0 <= T) (P : ActionPartition T)
    {f : Real -> Real} (hf : IntegrableOn f (Icc 0 T) volume) :
    ∑ i : Fin P.intervals, ∫ t in P.left i..P.right i, f t =
      ∫ t in (0 : Real)..T, f t := by
  classical
  calc
    ∑ i : Fin P.intervals, ∫ t in P.left i..P.right i, f t =
      ∑ i : Fin P.intervals,
        ∫ t in P.natPoint i.val..P.natPoint (i.val + 1), f t := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [P.natPoint_eq_left i.val i.isLt,
            P.natPoint_succ_eq_right i.val i.isLt]
    _ =
      ∑ k ∈ Finset.range P.intervals,
        ∫ t in P.natPoint k..P.natPoint (k + 1), f t :=
      Fin.sum_univ_eq_sum_range
        (fun k => ∫ t in P.natPoint k..P.natPoint (k + 1), f t)
        P.intervals
    _ = ∫ t in P.natPoint 0..P.natPoint P.intervals, f t := by
      apply intervalIntegral.sum_integral_adjacent_intervals
      intro k hk
      rw [P.natPoint_eq_left k hk, P.natPoint_succ_eq_right k hk,
        intervalIntegrable_iff_integrableOn_Icc_of_le
          (P.left_lt_right ⟨k, hk⟩).le]
      exact hf.mono_set (P.cell_subset hT ⟨k, hk⟩)
    _ = ∫ t in (0 : Real)..T, f t := by
      rw [P.natPoint_zero, P.natPoint_intervals]

theorem sum_cell_localRate_lintegral_eq
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (P : ActionPartition T) :
    ∑ i : Fin P.intervals,
        ∫⁻ t in Icc (P.left i) (P.right i),
          N.localRate (pathDerivative A t) =
      ∫⁻ t in Icc 0 T, N.localRate (pathDerivative A t) := by
  classical
  let g : Real -> ENNReal :=
    fun t => N.localRate (pathDerivative A t)
  let gr : Real -> Real := fun t => (g t).toReal
  have hvalid := poissonPathRate_ne_top_implies_valid N T A hfinite
  have hglobal_ne_top :
      (∫⁻ t in Icc 0 T, g t) ≠ (⊤ : ENNReal) := by
    simpa [g, poissonPathRate, hvalid] using hfinite
  have hg_meas : Measurable g := by
    simpa [g] using measurable_localRate_general N A
  have hglobal_lt :
      ∀ᵐ t ∂volume.restrict (Icc 0 T), g t < (⊤ : ENNReal) :=
    ae_lt_top hg_meas hglobal_ne_top
  have hglobal_lt_ambient :
      ∀ᵐ t ∂volume, t ∈ Icc (0 : Real) T -> g t < (⊤ : ENNReal) :=
    (ae_restrict_iff' measurableSet_Icc).mp hglobal_lt
  have hgr_int : IntegrableOn gr (Icc 0 T) volume := by
    simpa [gr, g] using
      finiteAction_localRate_toReal_integrableOn N T A hfinite
  have hcell_ne_top (i : Fin P.intervals) :
      (∫⁻ t in Icc (P.left i) (P.right i), g t) ≠ (⊤ : ENNReal) := by
    apply ne_top_of_le_ne_top hglobal_ne_top
    exact lintegral_mono'
      (Measure.restrict_mono_set volume (P.cell_subset hT i)) le_rfl
  have hsum_ne_top :
      (∑ i : Fin P.intervals,
        ∫⁻ t in Icc (P.left i) (P.right i), g t) ≠ (⊤ : ENNReal) := by
    rw [ENNReal.sum_ne_top]
    intro i hi
    exact hcell_ne_top i
  apply (ENNReal.toReal_eq_toReal_iff' hsum_ne_top hglobal_ne_top).mp
  rw [ENNReal.toReal_sum (fun i hi => hcell_ne_top i)]
  calc
    ∑ i : Fin P.intervals,
        (∫⁻ t in Icc (P.left i) (P.right i), g t).toReal =
      ∑ i : Fin P.intervals, ∫ t in P.left i..P.right i, gr t := by
        apply Finset.sum_congr rfl
        intro i hi
        have hcell_lt :
            ∀ᵐ t ∂volume.restrict (Icc (P.left i) (P.right i)),
              g t < (⊤ : ENNReal) :=
          (ae_restrict_iff' measurableSet_Icc).mpr <| by
            filter_upwards [hglobal_lt_ambient] with t ht
            intro hcell
            exact ht (P.cell_subset hT i hcell)
        rw [← integral_toReal hg_meas.aemeasurable hcell_lt]
        change (∫ t in Icc (P.left i) (P.right i), gr t) =
          ∫ t in P.left i..P.right i, gr t
        rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le (P.left_lt_right i).le]
    _ = ∫ t in (0 : Real)..T, gr t :=
      sum_intervalIntegral_partition hT P hgr_int
    _ = ∫ t in Icc (0 : Real) T, gr t := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hT]
    _ = (∫⁻ t in Icc (0 : Real) T, g t).toReal :=
      integral_toReal hg_meas.aemeasurable hglobal_lt

/-- Jensen's inequality on every cell: every finite chord-action is bounded
above by the full Poisson path action. -/
theorem poissonPartitionAction_le_poissonPathRate
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (P : ActionPartition T) :
    poissonPartitionAction N A P <= poissonPathRate N T A := by
  classical
  have hvalid := poissonPathRate_ne_top_implies_valid N T A hfinite
  unfold poissonPartitionAction
  calc
    ∑ i : Fin P.intervals,
        ENNReal.ofReal (P.width i) *
          N.localRate (partitionChord A P i)
      <= ∑ i : Fin P.intervals,
          ∫⁻ t in Icc (P.left i) (P.right i),
            N.localRate (pathDerivative A t) := by
        apply Finset.sum_le_sum
        intro i hi
        exact localRate_partitionChord_mul_width_le_lintegral
          N hT A hfinite P i
    _ = ∫⁻ t in Icc 0 T, N.localRate (pathDerivative A t) :=
      sum_cell_localRate_lintegral_eq N hT A hfinite P
    _ = poissonPathRate N T A := by
      rw [poissonPathRate, if_pos hvalid]

/-- The uniform partition into `n + 1` cells. -/
noncomputable def uniformActionPartition (T : Real) (hT : 0 < T) (n : Nat) :
    ActionPartition T where
  intervals := n + 1
  point i := (i.val : Real) * T / (n + 1 : Nat)
  point_zero := by simp
  point_last := by
    change ((n + 1 : Nat) : Real) * T / ((n + 1 : Nat) : Real) = T
    field_simp
  strictMono_point := by
    intro i j hij
    have hij' : (i.val : Real) < j.val := by exact_mod_cast hij
    have hm : 0 < (n + 1 : Real) := by positivity
    simpa [Nat.cast_add, Nat.cast_one] using
      (div_lt_div_iff_of_pos_right hm).mpr
        (mul_lt_mul_of_pos_right hij' hT)

namespace UniformPartition

noncomputable def cellIndex (T : Real) (n : Nat) (t : Real) : Nat :=
  Nat.floor (((n + 1 : Nat) : Real) * t / T)

theorem cellIndex_lt {T : Real} (hT : 0 < T) (n : Nat)
    {t : Real} (ht0 : 0 <= t) (ht : t < T) :
    cellIndex T n t < n + 1 := by
  have hm : 0 < ((n + 1 : Nat) : Real) := by positivity
  have hx_nonneg :
      0 <= (((n + 1 : Nat) : Real) * t / T) := by
    positivity
  have hx_lt :
      (((n + 1 : Nat) : Real) * t / T) <
        ((n + 1 : Nat) : Real) := by
    calc
      ((n + 1 : Nat) : Real) * t / T <
          ((n + 1 : Nat) : Real) * T / T := by
        exact div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_left ht hm) hT
      _ = ((n + 1 : Nat) : Real) := by field_simp
  exact (Nat.floor_lt hx_nonneg).mpr hx_lt

theorem mem_uniform_cell {T : Real} (hT : 0 < T) (n : Nat)
    {t : Real} (ht0 : 0 <= t) (htT : t < T) :
    t ∈ Ico
      ((uniformActionPartition T hT n).left
        ⟨cellIndex T n t, cellIndex_lt hT n ht0 htT⟩)
      ((uniformActionPartition T hT n).right
        ⟨cellIndex T n t, cellIndex_lt hT n ht0 htT⟩) := by
  have hm : 0 < ((n + 1 : Nat) : Real) := by positivity
  have hx_nonneg :
      0 <= ((n + 1 : Nat) : Real) * t / T := by
    positivity
  have hfloor := Nat.floor_le hx_nonneg
  have hceil :=
    Nat.lt_floor_add_one (((n + 1 : Nat) : Real) * t / T)
  constructor
  · simp only [ActionPartition.left, uniformActionPartition,
      Fin.castSucc_mk]
    change ((cellIndex T n t : Nat) : Real) * T /
      ((n + 1 : Nat) : Real) <= t
    rw [div_le_iff₀ hm, ← le_div_iff₀ hT]
    simpa [cellIndex, mul_comm, mul_left_comm, mul_assoc] using hfloor
  · simp only [ActionPartition.right, uniformActionPartition,
      Fin.succ_mk]
    change t < ((cellIndex T n t + 1 : Nat) : Real) * T /
      ((n + 1 : Nat) : Real)
    rw [lt_div_iff₀ hm, ← div_lt_iff₀ hT]
    simpa [cellIndex, mul_comm, mul_left_comm, mul_assoc] using hceil

end UniformPartition

/-- Piecewise-constant chord cost attached to a partition. Endpoints are
assigned with half-open cells; this choice is immaterial to its integral. -/
noncomputable def partitionStepCost
    (N : Network Buffer Server) (A : MatrixPath Server Buffer)
    {T : Real} (P : ActionPartition T) (t : Real) : ENNReal :=
  ∑ i : Fin P.intervals,
    (Ico (P.left i) (P.right i)).indicator
      (fun _ => N.localRate (partitionChord A P i)) t

theorem measurable_partitionStepCost
    (N : Network Buffer Server) (A : MatrixPath Server Buffer)
    {T : Real} (P : ActionPartition T) :
    Measurable (partitionStepCost N A P) := by
  classical
  unfold partitionStepCost
  apply Finset.measurable_fun_sum
  intro i hi
  exact measurable_const.indicator measurableSet_Ico

theorem lintegral_partitionStepCost
    (N : Network Buffer Server) (A : MatrixPath Server Buffer)
    {T : Real} (P : ActionPartition T) :
    ∫⁻ t, partitionStepCost N A P t =
      poissonPartitionAction N A P := by
  classical
  unfold partitionStepCost poissonPartitionAction
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [lintegral_indicator measurableSet_Ico, setLIntegral_const,
      Real.volume_Ico]
    simp [ActionPartition.width, mul_comm]
  · intro i hi
    exact measurable_const.indicator measurableSet_Ico

theorem lintegral_partitionStepCost_Icc
    (N : Network Buffer Server) (A : MatrixPath Server Buffer)
    {T : Real} (hT : 0 <= T) (P : ActionPartition T) :
    ∫⁻ t in Icc 0 T, partitionStepCost N A P t =
      poissonPartitionAction N A P := by
  rw [← lintegral_partitionStepCost N A P]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Icc (0 : Real) T
  · simp [ht]
  · have hzero : partitionStepCost N A P t = 0 := by
      unfold partitionStepCost
      apply Finset.sum_eq_zero
      intro i hi
      rw [Set.indicator_of_notMem]
      intro hcell
      exact ht (P.cell_subset hT i ⟨hcell.1, hcell.2.le⟩)
    simp [ht, hzero]

noncomputable def uniformCellChord
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (n : Nat) (t : Real) : Server -> Buffer -> Real :=
  if ht : 0 <= t /\ t < T then
    partitionChord A (uniformActionPartition T hT n)
      ⟨UniformPartition.cellIndex T n t,
        UniformPartition.cellIndex_lt hT n ht.1 ht.2⟩
  else 0

omit [Fintype Buffer] [Fintype Server] in
theorem uniformCellChord_eq
    {T : Real} (hT : 0 < T) (A : MatrixPath Server Buffer)
    (n : Nat) {t : Real} (ht : 0 <= t /\ t < T) :
    uniformCellChord T hT A n t =
      partitionChord A (uniformActionPartition T hT n)
        ⟨UniformPartition.cellIndex T n t,
          UniformPartition.cellIndex_lt hT n ht.1 ht.2⟩ := by
  unfold uniformCellChord
  rw [dif_pos ht]

theorem uniformCellChord_nonneg
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N T A) (⊤ : ENNReal))
    (n : Nat) {t : Real} (ht : 0 <= t /\ t < T)
    (j : Server) (k : Buffer) :
    0 <= uniformCellChord T hT A n t j k := by
  rw [uniformCellChord_eq hT A n ht]
  exact partitionChord_nonneg N hT.le A hfinite
    (uniformActionPartition T hT n)
    ⟨UniformPartition.cellIndex T n t,
      UniformPartition.cellIndex_lt hT n ht.1 ht.2⟩ j k

noncomputable def uniformCellCenter
    (T : Real) (hT : 0 < T) (n : Nat) (t : Real) : Real :=
  if ht : 0 <= t /\ t < T then
    let i : Fin (uniformActionPartition T hT n).intervals :=
      ⟨UniformPartition.cellIndex T n t,
        UniformPartition.cellIndex_lt hT n ht.1 ht.2⟩
    ((uniformActionPartition T hT n).left i +
      (uniformActionPartition T hT n).right i) / 2
  else 0

noncomputable def uniformCellRadius (T : Real) (n : Nat) : Real :=
  T / (2 * ((n + 1 : Nat) : Real))

theorem uniformCellRadius_pos {T : Real} (hT : 0 < T) (n : Nat) :
    0 < uniformCellRadius T n := by
  unfold uniformCellRadius
  positivity

theorem tendsto_uniformCellRadius {T : Real} (hT : 0 < T) :
    Tendsto (uniformCellRadius T) atTop (𝓝[>] (0 : Real)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)).const_mul
        (T / 2)
    convert h using 1
    · funext n
      unfold uniformCellRadius
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp
    · simp
  · exact Filter.Eventually.of_forall fun n =>
      uniformCellRadius_pos hT n

theorem closedBall_uniformCellCenter
    {T : Real} (hT : 0 < T) (n : Nat)
    {t : Real} (ht0 : 0 <= t) (htT : t < T) :
    Metric.closedBall (uniformCellCenter T hT n t) (uniformCellRadius T n) =
      Icc
        ((uniformActionPartition T hT n).left
          ⟨UniformPartition.cellIndex T n t,
            UniformPartition.cellIndex_lt hT n ht0 htT⟩)
        ((uniformActionPartition T hT n).right
          ⟨UniformPartition.cellIndex T n t,
            UniformPartition.cellIndex_lt hT n ht0 htT⟩) := by
  let i : Fin (n + 1) :=
    ⟨UniformPartition.cellIndex T n t,
      UniformPartition.cellIndex_lt hT n ht0 htT⟩
  rw [Real.closedBall_eq_Icc]
  simp only [uniformCellCenter, ht0, htT, and_self, dite_true,
    uniformCellRadius]
  change Icc
    ((((uniformActionPartition T hT n).left i +
      (uniformActionPartition T hT n).right i) / 2) -
        T / (2 * ((n + 1 : Nat) : Real)))
    ((((uniformActionPartition T hT n).left i +
      (uniformActionPartition T hT n).right i) / 2) +
        T / (2 * ((n + 1 : Nat) : Real))) =
      Icc ((uniformActionPartition T hT n).left i)
        ((uniformActionPartition T hT n).right i)
  apply congrArg₂ Icc
  · simp only [ActionPartition.left, ActionPartition.right,
      uniformActionPartition]
    have hcast : ((i.castSucc.val : Nat) : Real) = i.val := by simp
    have hsucc : ((i.succ.val : Nat) : Real) = i.val + 1 := by simp
    rw [hcast, hsucc]
    field_simp
    ring
  · simp only [ActionPartition.left, ActionPartition.right,
      uniformActionPartition]
    have hcast : ((i.castSucc.val : Nat) : Real) = i.val := by simp
    have hsucc : ((i.succ.val : Nat) : Real) = i.val + 1 := by simp
    rw [hcast, hsucc]
    field_simp
    ring

theorem setAverage_restrictedDerivative_eq_uniformCellChord
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N T A) (⊤ : ENNReal))
    (n : Nat) {t : Real} (ht0 : 0 <= t) (htT : t < T) :
    (⨍ s in Metric.closedBall (uniformCellCenter T hT n t)
          (uniformCellRadius T n),
        (Icc (0 : Real) T).indicator (pathDerivative A) s ∂volume) =
      uniformCellChord T hT A n t := by
  classical
  let P := uniformActionPartition T hT n
  let i : Fin (n + 1) :=
    ⟨UniformPartition.cellIndex T n t,
      UniformPartition.cellIndex_lt hT n ht0 htT⟩
  rw [closedBall_uniformCellCenter hT n ht0 htT]
  simp only [uniformCellChord, ht0, htT, and_self, dite_true]
  change (⨍ s in Icc (P.left i) (P.right i),
      (Icc (0 : Real) T).indicator (pathDerivative A) s ∂volume) =
    partitionChord A P i
  have hcell_subset : Icc (P.left i) (P.right i) ⊆ Icc (0 : Real) T :=
    P.cell_subset hT.le i
  have hmatrix_int :
      IntegrableOn (pathDerivative A) (Icc 0 T) volume :=
    finiteAction_derivative_integrableOn_matrix N hT.le A hfinite
  have hindicator_int :
      Integrable ((Icc (0 : Real) T).indicator (pathDerivative A)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hmatrix_int
  rw [setAverage_eq]
  funext j
  funext k
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [eval_integral (fun q => (hindicator_int.eval q).integrableOn) j]
  rw [eval_integral
    (fun r => ((hindicator_int.eval j).eval r).integrableOn) k]
  have hcoord :
        (⨍ s in Icc (P.left i) (P.right i),
          pathDerivative A s j k ∂volume) =
            partitionChord A P i j k :=
    derivative_setAverage_eq_partitionChord N hT.le A hfinite P i j k
  rw [setAverage_eq] at hcoord
  simp only [smul_eq_mul] at hcoord
  rw [← hcoord]
  congr 1
  apply integral_congr_ae
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards with s
  intro hs
  simp [hcell_subset hs]

theorem uniformCellChord_tendsto_ae
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N T A) (⊤ : ENNReal)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      Tendsto (fun n => uniformCellChord T hT A n t) atTop
        (𝓝 (pathDerivative A t)) := by
  classical
  let f : Real -> (Server -> Buffer -> Real) :=
    (Icc (0 : Real) T).indicator (pathDerivative A)
  have hmatrix_int :
      IntegrableOn (pathDerivative A) (Icc 0 T) volume :=
    finiteAction_derivative_integrableOn_matrix N hT.le A hfinite
  have hf_int : Integrable f volume := by
    exact (integrable_indicator_iff measurableSet_Icc).mpr hmatrix_int
  have hldt :=
    IsUnifLocDoublingMeasure.ae_tendsto_average volume
      hf_int.locallyIntegrable 1
  have hae_zero : ∀ᵐ t : Real ∂volume, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hae_T : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hldt, hae_zero, hae_T] with t hx ht_ne_zero ht_ne_T
  intro ht
  have ht0 : 0 <= t := ht.1
  have htT : t < T := ht.2.lt_of_ne ht_ne_T
  have ht_mem_f : t ∈ Icc (0 : Real) T := ⟨ht0, htT.le⟩
  have hmem :
      ∀ᶠ n in atTop,
        t ∈ Metric.closedBall (uniformCellCenter T hT n t)
          (1 * uniformCellRadius T n) := by
    filter_upwards with n
    rw [one_mul, closedBall_uniformCellCenter hT n ht0 htT]
    have hcell := UniformPartition.mem_uniform_cell hT n ht0 htT
    exact ⟨hcell.1, hcell.2.le⟩
  have havg :=
    hx (uniformCellCenter T hT · t) (uniformCellRadius T)
      (tendsto_uniformCellRadius hT) hmem
  have havg' :
      Tendsto
        (fun n => uniformCellChord T hT A n t) atTop
        (𝓝 (f t)) := by
    refine (Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) havg)
    exact setAverage_restrictedDerivative_eq_uniformCellChord
      N hT A hfinite n ht0 htT
  simpa [f, ht_mem_f] using havg'

theorem localRate_uniformCellChord_tendsto_ae
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N T A) (⊤ : ENNReal)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      Tendsto
        (fun n => N.localRate (uniformCellChord T hT A n t))
        atTop (𝓝 (N.localRate (pathDerivative A t))) := by
  classical
  have hnonneg_all :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        forall j k, 0 <= pathDerivative A t j k := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    exact finiteAction_derivative_nonneg_ae N T A hfinite j k
  have hzero_all :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        forall j k, N.phi j k = 0 -> pathDerivative A t j k = 0 := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    by_cases hphi : N.phi j k = 0
    · exact (finiteAction_zeroDerivative_ae N T A hfinite j k hphi).mono
        fun t ht _ => ht
    · exact Filter.Eventually.of_forall fun t ht => (hphi ht).elim
  have hae_T : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  have hinterior :
      ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 <= t /\ t < T :=
    (ae_restrict_iff' measurableSet_Icc).mpr <| by
      filter_upwards [hae_T] with t ht_ne
      intro ht
      exact ⟨ht.1, ht.2.lt_of_ne ht_ne⟩
  filter_upwards
    [uniformCellChord_tendsto_ae N hT A hfinite,
      hnonneg_all, hzero_all, hinterior]
      with t hchord hderiv_nonneg hderiv_zero ht
  unfold Network.localRate
  apply tendsto_finsetSum Finset.univ
  intro j hj
  apply tendsto_finsetSum Finset.univ
  intro k hk
  rcases (N.phi_nonneg j k).eq_or_lt with hphi | hphi
  · have hphi0 : N.phi j k = 0 := hphi.symm
    have hlimit0 := hderiv_zero j k hphi0
    have hseq0 (n : Nat) :
        uniformCellChord T hT A n t j k = 0 :=
      by
        rw [uniformCellChord_eq hT A n ht]
        exact partitionChord_eq_zero_of_phi_eq_zero N hT.le A hfinite
          (uniformActionPartition T hT n)
          ⟨UniformPartition.cellIndex T n t,
            UniformPartition.cellIndex_lt hT n ht.1 ht.2⟩
          j k hphi0
    simp [hphi0, hlimit0, hseq0]
  · have hscalar :
        Tendsto (fun n => uniformCellChord T hT A n t j k)
          atTop (𝓝 (pathDerivative A t j k)) :=
      (hchord.apply_nhds j).apply_nhds k
    have hpositive :
        Tendsto
          (fun n => positivePoissonCostReal (N.phi j k)
            (uniformCellChord T hT A n t j k))
          atTop
          (𝓝 (positivePoissonCostReal (N.phi j k)
            (pathDerivative A t j k))) :=
      ((continuous_positivePoissonCostReal (N.phi j k)).tendsto _).comp hscalar
    have hofReal :=
      (ENNReal.continuous_ofReal.tendsto _).comp hpositive
    have hlimit_nonneg := hderiv_nonneg j k
    have hlimit_eq :
        poissonCost (N.phi j k) (pathDerivative A t j k) =
          ENNReal.ofReal (positivePoissonCostReal (N.phi j k)
            (pathDerivative A t j k)) := by
      rw [poissonCost_of_nominal_pos hphi hlimit_nonneg,
        positivePoissonCostReal_eq hphi hlimit_nonneg]
      rfl
    rw [hlimit_eq]
    refine (Filter.Tendsto.congr' ?_ hofReal)
    filter_upwards with n
    have hseq_nonneg :=
      uniformCellChord_nonneg N hT A hfinite n ht j k
    simp only [Function.comp_apply]
    rw [poissonCost_of_nominal_pos hphi hseq_nonneg,
      positivePoissonCostReal_eq hphi hseq_nonneg]
    rfl

theorem partitionStepCost_uniform_eq
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (A : MatrixPath Server Buffer) (n : Nat)
    {t : Real} (ht0 : 0 <= t) (htT : t < T) :
    partitionStepCost N A (uniformActionPartition T hT n) t =
      N.localRate (uniformCellChord T hT A n t) := by
  classical
  let i : Fin (uniformActionPartition T hT n).intervals :=
    ⟨UniformPartition.cellIndex T n t,
      UniformPartition.cellIndex_lt hT n ht0 htT⟩
  have hmem :
      t ∈ Ico ((uniformActionPartition T hT n).left i)
        ((uniformActionPartition T hT n).right i) :=
    UniformPartition.mem_uniform_cell hT n ht0 htT
  unfold partitionStepCost
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hmem]
    simp [uniformCellChord, ht0, htT, i]
  · intro q hq hqi
    rw [Set.indicator_of_notMem]
    intro hmemq
    rcases lt_or_gt_of_ne hqi with hqi | hqi
    · have hright_le_left :
          (uniformActionPartition T hT n).right q <=
            (uniformActionPartition T hT n).left i := by
        change ((q.val + 1 : Nat) : Real) * T / (n + 1 : Nat) <=
          (i.val : Real) * T / (n + 1 : Nat)
        have hnat : q.val + 1 <= i.val := Nat.add_one_le_iff.mpr hqi
        gcongr
      exact (not_lt_of_ge hright_le_left)
        (hmem.1.trans_lt hmemq.2)
    · have hright_le_left :
          (uniformActionPartition T hT n).right i <=
            (uniformActionPartition T hT n).left q := by
        change ((i.val + 1 : Nat) : Real) * T / (n + 1 : Nat) <=
          (q.val : Real) * T / (n + 1 : Nat)
        have hnat : i.val + 1 <= q.val := Nat.add_one_le_iff.mpr hqi
        gcongr
      exact (not_lt_of_ge hright_le_left)
        (hmemq.1.trans_lt hmem.2)
  · exact fun hi => (hi (Finset.mem_univ i)).elim

theorem partitionStepCost_uniform_tendsto_ae
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N T A) (⊤ : ENNReal)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      Tendsto
        (fun n =>
          partitionStepCost N A (uniformActionPartition T hT n) t)
        atTop (𝓝 (N.localRate (pathDerivative A t))) := by
  have hae_T : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  have hinterior :
      ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 <= t /\ t < T :=
    (ae_restrict_iff' measurableSet_Icc).mpr <| by
      filter_upwards [hae_T] with t ht_ne
      intro ht
      exact ⟨ht.1, ht.2.lt_of_ne ht_ne⟩
  filter_upwards
    [localRate_uniformCellChord_tendsto_ae N hT A hfinite, hinterior]
      with t hlocal ht
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hlocal
  exact (partitionStepCost_uniform_eq N T hT A n ht.1 ht.2).symm

theorem poissonPathRate_le_liminf_uniformPartitionAction
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N T A) (⊤ : ENNReal)) :
    poissonPathRate N T A <=
      liminf
        (fun n => poissonPartitionAction N A
          (uniformActionPartition T hT n)) atTop := by
  have hvalid := poissonPathRate_ne_top_implies_valid N T A hfinite
  rw [poissonPathRate, if_pos hvalid]
  calc
    (∫⁻ t in Icc 0 T, N.localRate (pathDerivative A t)) =
        ∫⁻ t in Icc 0 T,
          liminf
            (fun n =>
              partitionStepCost N A
                (uniformActionPartition T hT n) t) atTop := by
      apply lintegral_congr_ae
      filter_upwards
        [partitionStepCost_uniform_tendsto_ae N hT A hfinite]
          with t ht
      exact ht.liminf_eq.symm
    _ <= liminf
        (fun n =>
          ∫⁻ t in Icc 0 T,
            partitionStepCost N A
              (uniformActionPartition T hT n) t) atTop :=
      lintegral_liminf_le fun n =>
        measurable_partitionStepCost N A
          (uniformActionPartition T hT n)
    _ = liminf
        (fun n => poissonPartitionAction N A
          (uniformActionPartition T hT n)) atTop := by
      congr 1
      funext n
      exact lintegral_partitionStepCost_Icc N A hT.le
        (uniformActionPartition T hT n)

theorem exists_uniformPartitionAction_toReal_ge_sub
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N T A) (⊤ : ENNReal))
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists n : Nat,
      (poissonPathRate N T A).toReal - epsilon <=
        (poissonPartitionAction N A
          (uniformActionPartition T hT n)).toReal := by
  let u : Nat -> ENNReal := fun n =>
    poissonPartitionAction N A (uniformActionPartition T hT n)
  have hu_le (n : Nat) : u n <= poissonPathRate N T A :=
    poissonPartitionAction_le_poissonPathRate N hT.le A hfinite
      (uniformActionPartition T hT n)
  have hliminf_ennreal :
      poissonPathRate N T A <= liminf u atTop := by
    exact poissonPathRate_le_liminf_uniformPartitionAction
      N hT A hfinite
  have hliminf_le :
      liminf u atTop <= poissonPathRate N T A := by
    apply liminf_le_of_le (u := u) (f := atTop) ⟨0, by simp⟩
    intro y hy
    obtain ⟨n, hn⟩ :=
      (hy.and (Filter.Eventually.of_forall hu_le)).exists
    exact hn.1.trans hn.2
  have hliminf_ne_top : Ne (liminf u atTop) (⊤ : ENNReal) :=
    ne_top_of_le_ne_top hfinite hliminf_le
  have hliminf_real :
      (poissonPathRate N T A).toReal <=
        liminf (fun n => (u n).toReal) atTop := by
    rw [ENNReal.liminf_toReal_eq hfinite
      (Filter.Eventually.of_forall hu_le)]
    exact ENNReal.toReal_mono hliminf_ne_top hliminf_ennreal
  have hu_bdd :
      IsBoundedUnder GE.ge atTop (fun n => (u n).toReal) := by
    refine ⟨0, ?_⟩
    simpa only [eventually_map] using
      (Filter.Eventually.of_forall fun n => ENNReal.toReal_nonneg)
  obtain ⟨n, hn⟩ :=
    Filter.exists_lt_of_le_liminf hu_bdd hliminf_real
      (neg_lt_zero.mpr hepsilon)
  refine ⟨n, ?_⟩
  change (poissonPathRate N T A).toReal - epsilon <= (u n).toReal
  rw [sub_eq_add_neg]
  exact hn.le

/-- A finite strictly increasing partition whose chord action approximates
the finite path action from below, together with the upper bound for every
finite strictly increasing partition. -/
theorem exists_actionPartition_approximating_poissonPathRate
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N T A) (⊤ : ENNReal))
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists P : ActionPartition T,
      (poissonPathRate N T A).toReal - epsilon <=
          (poissonPartitionAction N A P).toReal /\
        forall Q : ActionPartition T,
          poissonPartitionAction N A Q <= poissonPathRate N T A := by
  obtain ⟨n, hn⟩ :=
    exists_uniformPartitionAction_toReal_ge_sub
      N hT A hfinite hepsilon
  refine ⟨uniformActionPartition T hT n, hn, ?_⟩
  intro Q
  exact poissonPartitionAction_le_poissonPathRate
    N hT.le A hfinite Q

end StateDepMOR

namespace StateDepMOR.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

variable (N : Network Buffer Server)

theorem expMeasure_memoryless (a : Real) (ha : 0 <= a) :
    ((expMeasure 1).restrict (Ici a)).map (fun x => x - a) =
      ENNReal.ofReal (Real.exp (-a)) • expMeasure 1 := by
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB,
    Measure.restrict_apply (hB.preimage (by fun_prop))]
  rw [expMeasure, gammaMeasure,
    withDensity_apply _ ((hB.preimage (by fun_prop)).inter measurableSet_Ici)]
  rw [Measure.smul_apply, withDensity_apply _ hB]
  change
    (∫⁻ x in (fun x : Real => x - a) ⁻¹' B ∩ Ici a,
        exponentialPDF 1 x) =
      ENNReal.ofReal (Real.exp (-a)) *
        ∫⁻ x in B, exponentialPDF 1 x
  rw [← lintegral_indicator
    ((hB.preimage (by fun_prop)).inter measurableSet_Ici)]
  rw [← lintegral_add_right_eq_self
    (((((fun x : Real => x - a) ⁻¹' B) ∩ Ici a).indicator
      (exponentialPDF 1))) a]
  rw [← lintegral_indicator hB]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [] with x
  by_cases hxnonneg : 0 <= x
  · have hxa : a <= x + a := by linarith
    by_cases hxB : x ∈ B
    · rw [Set.indicator_of_mem
        (show x + a ∈ (fun x : Real => x - a) ⁻¹' B ∩ Ici a by
          constructor
          · simpa using hxB
          · exact hxa),
        Set.indicator_of_mem hxB]
      simp only [exponentialPDF_eq, if_pos hxnonneg,
        if_pos (show 0 <= x + a by linarith), one_mul]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      rw [← Real.exp_add]
      congr 1
      ring
    · rw [Set.indicator_of_notMem
        (show x + a ∉ (fun x : Real => x - a) ⁻¹' B ∩ Ici a by
          intro h
          apply hxB
          simpa using h.1),
        Set.indicator_of_notMem hxB]
      simp
  · have hxneg : x < 0 := lt_of_not_ge hxnonneg
    have hxnot : Not (x + a ∈ Ici a) := by
      change Not (a <= x + a)
      linarith
    simp [hxnot, exponentialPDF_of_neg hxneg]

theorem expMeasure_memoryless_open (a : Real) (ha : 0 <= a) :
    ((expMeasure 1).restrict (Ioi a)).map (fun x => x - a) =
      ENNReal.ofReal (Real.exp (-a)) • expMeasure 1 := by
  change
    (((volume.withDensity (gammaPDF 1 1)).restrict (Ioi a)).map
      (fun x => x - a)) =
        ENNReal.ofReal (Real.exp (-a)) •
          volume.withDensity (gammaPDF 1 1)
  rw [restrict_Ioi_eq_restrict_Ici]
  simpa only [expMeasure, gammaMeasure] using expMeasure_memoryless a ha

theorem expMeasure_memoryless_apply (a : Real) (ha : 0 <= a)
    (A : Set Real) (hA : MeasurableSet A) :
    expMeasure 1 {x | a < x /\ x - a ∈ A} =
      ENNReal.ofReal (Real.exp (-a)) * expMeasure 1 A := by
  have h := congrArg (fun mu : Measure Real => mu A)
    (expMeasure_memoryless_open a ha)
  rw [Measure.map_apply (by fun_prop) hA,
    Measure.restrict_apply (hA.preimage (by fun_prop)),
    Measure.smul_apply] at h
  have hset :
      {x : Real | a < x /\ x - a ∈ A} =
        (fun x : Real => x - a) ⁻¹' A ∩ Ioi a := by
    ext x
    simp [and_comm]
  rw [hset]
  exact h

theorem measurable_nat_select {Omega E : Type*}
    [MeasurableSpace Omega] [MeasurableSpace E]
    (q : Omega -> Nat) (hq : Measurable q)
    (f : Nat -> Omega -> E) (hf : forall n, Measurable (f n)) :
    Measurable (fun omega => f (q omega) omega) := by
  intro s hs
  rw [show (fun omega => f (q omega) omega) ⁻¹' s =
      ⋃ n : Nat, {omega | q omega = n} ∩ f n ⁻¹' s by
    ext omega
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro h
      exact ⟨q omega, rfl, h⟩
    · rintro ⟨n, hn, h⟩
      simpa [hn] using h]
  exact MeasurableSet.iUnion fun n =>
    (hq (measurableSet_singleton n)).inter ((hf n) hs)

/-- The residual renewal clock seen immediately after deterministic time `s`. -/
noncomputable def postRenewalClock (s : Real)
    (clock : UnitRateClockPath) : UnitRateClockPath
  | 0 =>
      renewalEpoch clock (unitPoissonCount clock s + 1) - s
  | r + 1 =>
      clock (unitPoissonCount clock s + 1 + r)

theorem measurable_postRenewalClock (s : Real) :
    Measurable (postRenewalClock s) := by
  rw [measurable_pi_iff]
  intro r
  cases r with
  | zero =>
      exact measurable_nat_select
        (fun clock : UnitRateClockPath => unitPoissonCount clock s)
        (PoissonSamplePath.measurable_unitPoissonCount s)
        (fun q clock => renewalEpoch clock (q + 1) - s)
        (fun q => (measurable_renewalEpoch (q + 1)).sub_const s)
  | succ r =>
      exact measurable_nat_select
        (fun clock : UnitRateClockPath => unitPoissonCount clock s)
        (PoissonSamplePath.measurable_unitPoissonCount s)
        (fun q clock => clock (q + 1 + r))
        (fun q => measurable_pi_apply (q + 1 + r))

noncomputable def renewalEpochMeasure : Nat -> Measure Real
  | 0 => Measure.dirac 0
  | n + 1 => gammaMeasure ((n + 1 : Nat) : Real) 1

theorem renewalEpoch_hasLaw (n : Nat) :
    HasLaw
      (fun clock : UnitRateClockPath => renewalEpoch clock n)
      (renewalEpochMeasure n) unitRateClockMeasure := by
  cases n with
  | zero =>
      refine ⟨(measurable_renewalEpoch 0).aemeasurable, ?_⟩
      rw [renewalEpochMeasure]
      simpa [renewalEpoch] using
        (Measure.map_const (μ := unitRateClockMeasure) (measurable_const :
          Measurable (fun _ : UnitRateClockPath => (0 : Real))))
  | succ n =>
      simpa [renewalEpochMeasure] using renewalEpoch_succ_hasLaw_gamma n

theorem renewalEpoch_indep_boundary (n : Nat) :
    IndepFun
      (fun clock : UnitRateClockPath => renewalEpoch clock n)
      (fun clock => clock n) unitRateClockMeasure := by
  have h := unitRateClock_iIndep.indepFun_sum_range_succ
    (fun _ => measurable_pi_apply _) n
  convert h using 1
  funext clock
  simp [renewalEpoch]

theorem renewalEpoch_boundary_hasLaw (n : Nat) :
    HasLaw
      (fun clock : UnitRateClockPath =>
        (renewalEpoch clock n, clock n))
      ((renewalEpochMeasure n).prod (expMeasure 1))
      unitRateClockMeasure := by
  exact (renewalEpoch_indep_boundary n).hasLaw_prod
    (renewalEpoch_hasLaw n) (unitRateClock_eval_hasLaw n)

theorem renewalEpoch_boundary_event_factor (n : Nat)
    {s : Real} (hs : 0 <= s) (A : Set Real) (hA : MeasurableSet A) :
    unitRateClockMeasure
        {clock |
          renewalEpoch clock n <= s /\
          s < renewalEpoch clock n + clock n /\
          renewalEpoch clock n + clock n - s ∈ A} =
      unitRateClockMeasure
          {clock |
            renewalEpoch clock n <= s /\
            s < renewalEpoch clock n + clock n} *
        expMeasure 1 A := by
  let E : Set (Real × Real) :=
    {p | p.1 <= s /\ s < p.1 + p.2 /\ p.1 + p.2 - s ∈ A}
  let F : Set (Real × Real) :=
    {p | p.1 <= s /\ s < p.1 + p.2}
  have hE : MeasurableSet E := by
    dsimp only [E]
    exact (measurableSet_le measurable_fst
      (measurable_const : Measurable (fun _ : Real × Real => s))).inter
      ((measurableSet_lt
        (measurable_const : Measurable (fun _ : Real × Real => s))
        (measurable_fst.add measurable_snd)).inter
          (hA.preimage ((measurable_fst.add measurable_snd).sub_const s)))
  have hF : MeasurableSet F := by
    dsimp only [F]
    exact (measurableSet_le measurable_fst
      (measurable_const : Measurable (fun _ : Real × Real => s))).inter
      (measurableSet_lt
        (measurable_const : Measurable (fun _ : Real × Real => s))
        (measurable_fst.add measurable_snd))
  have hLaw := renewalEpoch_boundary_hasLaw n
  rw [show {clock |
        renewalEpoch clock n <= s /\
        s < renewalEpoch clock n + clock n /\
        renewalEpoch clock n + clock n - s ∈ A} =
      {clock | (renewalEpoch clock n, clock n) ∈ E} by rfl]
  rw [show {clock |
        renewalEpoch clock n <= s /\
        s < renewalEpoch clock n + clock n} =
      {clock | (renewalEpoch clock n, clock n) ∈ F} by rfl]
  have hLawE :
      unitRateClockMeasure
          {clock | (renewalEpoch clock n, clock n) ∈ E} =
        (renewalEpochMeasure n).prod (expMeasure 1) E :=
    hLaw.measure_eq hE
  have hLawF :
      unitRateClockMeasure
          {clock | (renewalEpoch clock n, clock n) ∈ F} =
        (renewalEpochMeasure n).prod (expMeasure 1) F :=
    hLaw.measure_eq hF
  rw [hLawE, hLawF]
  rw [Measure.prod_apply hE, Measure.prod_apply hF]
  calc
    (∫⁻ y, expMeasure 1 (Prod.mk y ⁻¹' E) ∂renewalEpochMeasure n) =
        ∫⁻ y, expMeasure 1 A *
          expMeasure 1 (Prod.mk y ⁻¹' F) ∂renewalEpochMeasure n := by
      apply lintegral_congr
      intro y
      by_cases hys : y <= s
      · have hmem :
            expMeasure 1 (Prod.mk y ⁻¹' E) =
              ENNReal.ofReal (Real.exp (-(s - y))) *
                expMeasure 1 A := by
          rw [show Prod.mk y ⁻¹' E =
              {x : Real | s - y < x /\ x - (s - y) ∈ A} by
            ext x
            simp only [mem_preimage, E, mem_setOf_eq]
            constructor
            · rintro ⟨-, hlt, hmem⟩
              constructor
              · linarith
              · convert hmem using 1 <;> ring
            · rintro ⟨hlt, hmem⟩
              refine ⟨hys, by linarith, ?_⟩
              convert hmem using 1 <;> ring]
          exact expMeasure_memoryless_apply (s - y) (sub_nonneg.mpr hys) A hA
        have hbase :
            expMeasure 1 (Prod.mk y ⁻¹' F) =
              ENNReal.ofReal (Real.exp (-(s - y))) := by
          rw [show Prod.mk y ⁻¹' F =
              {x : Real | s - y < x /\ x - (s - y) ∈ Set.univ} by
            ext x
            simp only [mem_preimage, F, mem_setOf_eq, mem_univ, and_true]
            constructor
            · rintro ⟨-, hlt⟩
              linarith
            · intro hlt
              exact ⟨hys, by linarith⟩]
          rw [expMeasure_memoryless_apply (s - y)
            (sub_nonneg.mpr hys) Set.univ MeasurableSet.univ]
          simp
        rw [hmem, hbase]
        ac_rfl
      · have hyF : Prod.mk y ⁻¹' F = (∅ : Set Real) := by
          ext x
          simp [F, hys]
        have hyE : Prod.mk y ⁻¹' E = (∅ : Set Real) := by
          ext x
          simp [E, hys]
        rw [hyE, hyF]
        simp
    _ = expMeasure 1 A *
        ∫⁻ y, expMeasure 1 (Prod.mk y ⁻¹' F) ∂renewalEpochMeasure n := by
      rw [lintegral_const_mul' _ _ (measure_ne_top _ _)]
    _ = (∫⁻ y, expMeasure 1 (Prod.mk y ⁻¹' F) ∂renewalEpochMeasure n) *
        expMeasure 1 A := by ac_rfl

theorem unitPoissonCount_post_zero_factor {s : Real} (hs : 0 < s)
    (n : Nat) (A : Set Real) (hA : MeasurableSet A) :
    unitRateClockMeasure
        {clock |
          unitPoissonCount clock s = n /\
            postRenewalClock s clock 0 ∈ A} =
      unitRateClockMeasure {clock | unitPoissonCount clock s = n} *
        expMeasure 1 A := by
  let E : Set UnitRateClockPath :=
    {clock |
      renewalEpoch clock n <= s /\
        s < renewalEpoch clock n + clock n /\
        renewalEpoch clock n + clock n - s ∈ A}
  let F : Set UnitRateClockPath :=
    {clock |
      renewalEpoch clock n <= s /\
        s < renewalEpoch clock n + clock n}
  have hE :
      {clock |
        unitPoissonCount clock s = n /\
          postRenewalClock s clock 0 ∈ A} =ᵐ[unitRateClockMeasure] E := by
    filter_upwards [unitRateClock_all_interarrival_pos_ae,
      unit_renewalEpoch_tendsto_atTop_ae] with clock hpos htop
    apply propext
    constructor
    · rintro ⟨hcount, hpost⟩
      have hepoch :=
        (unitPoissonCount_eq_iff_epoch hpos htop hs n).mp hcount
      refine ⟨hepoch.1, ?_, ?_⟩
      · simpa [renewalEpoch_succ] using hepoch.2
      · simpa [postRenewalClock, hcount, renewalEpoch_succ] using hpost
    · rintro ⟨hn, hnnext, hpost⟩
      have hcount : unitPoissonCount clock s = n :=
        (unitPoissonCount_eq_iff_epoch hpos htop hs n).mpr
          ⟨hn, by simpa [renewalEpoch_succ] using hnnext⟩
      exact ⟨hcount, by
        simpa [postRenewalClock, hcount, renewalEpoch_succ] using hpost⟩
  have hF :
      {clock | unitPoissonCount clock s = n} =ᵐ[unitRateClockMeasure] F := by
    filter_upwards [unitRateClock_all_interarrival_pos_ae,
      unit_renewalEpoch_tendsto_atTop_ae] with clock hpos htop
    apply propext
    change unitPoissonCount clock s = n <->
      renewalEpoch clock n <= s /\
        s < renewalEpoch clock n + clock n
    rw [unitPoissonCount_eq_iff_epoch hpos htop hs n]
    rw [renewalEpoch_succ]
  rw [measure_congr hE, measure_congr hF]
  exact renewalEpoch_boundary_event_factor n hs.le A hA

theorem renewalEpoch_boundary_indep_fresh
    {I : Type*} [Fintype I] (n : Nat) (q : I -> Nat)
    (hq : forall i, n < q i) :
    IndepFun
      (fun clock : UnitRateClockPath =>
        (renewalEpoch clock n, clock n))
      (fun clock i => clock (q i)) unitRateClockMeasure := by
  classical
  let S : Finset Nat := Finset.range (n + 1)
  let T : Finset Nat := Finset.univ.image q
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro r hrS hrT
    rw [Finset.mem_range] at hrS
    rw [Finset.mem_image] at hrT
    rcases hrT with ⟨i, -, rfl⟩
    have hi := hq i
    omega
  have hgroup := unitRateClock_iIndep.indepFun_finset S T hST
    (fun _ => measurable_pi_apply _)
  let left : (S -> Real) -> Real × Real := fun x =>
    ((∑ r : Fin n,
        x (⟨r, by
          simpa only [S, Finset.mem_range] using
            r.isLt.trans (Nat.lt_succ_self n)⟩ : S)),
      x ⟨n, by simp [S]⟩)
  let right : (T -> Real) -> (I -> Real) := fun x i =>
    x ⟨q i, by simp [T]⟩
  have hleft : Measurable left := by
    apply Measurable.prodMk
    · exact Finset.measurable_fun_sum Finset.univ fun r _ =>
        measurable_pi_apply
          (⟨r, by
            simpa only [S, Finset.mem_range] using
              r.isLt.trans (Nat.lt_succ_self n)⟩ : S)
    · exact measurable_pi_apply (⟨n, by simp [S]⟩ : S)
  have hright : Measurable right := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (⟨q i, by simp [T]⟩ : T)
  have h := hgroup.comp hleft hright
  convert h using 1
  · funext clock
    simp [left, renewalEpoch, Fin.sum_univ_eq_sum_range]
  · funext clock i
    rfl

theorem renewalEpoch_boundary_fresh_factor
    {I : Type*} [Fintype I] (n : Nat) (q : I -> Nat)
    (hq : forall i, n < q i) (hqin : Function.Injective q)
    {s : Real} (A : Set Real) (hA : MeasurableSet A)
    (B : I -> Set Real) (hB : forall i, MeasurableSet (B i)) :
    unitRateClockMeasure
        ({clock |
          renewalEpoch clock n <= s /\
          s < renewalEpoch clock n + clock n /\
          renewalEpoch clock n + clock n - s ∈ A} ∩
        {clock | forall i, clock (q i) ∈ B i}) =
      unitRateClockMeasure
          {clock |
            renewalEpoch clock n <= s /\
            s < renewalEpoch clock n + clock n /\
            renewalEpoch clock n + clock n - s ∈ A} *
        ∏ i, expMeasure 1 (B i) := by
  let E : Set (Real × Real) :=
    {p | p.1 <= s /\ s < p.1 + p.2 /\ p.1 + p.2 - s ∈ A}
  let D : Set (I -> Real) := Set.pi Set.univ B
  have hE : MeasurableSet E := by
    dsimp only [E]
    exact (measurableSet_le measurable_fst
      (measurable_const : Measurable (fun _ : Real × Real => s))).inter
      ((measurableSet_lt
        (measurable_const : Measurable (fun _ : Real × Real => s))
        (measurable_fst.add measurable_snd)).inter
          (hA.preimage ((measurable_fst.add measurable_snd).sub_const s)))
  have hD : MeasurableSet D := MeasurableSet.univ_pi hB
  have hindep := renewalEpoch_boundary_indep_fresh n q hq
  have hmeasure :=
    hindep.measure_inter_preimage_eq_mul E D hE hD
  have hYi : iIndepFun
      (fun i : I => fun clock : UnitRateClockPath => clock (q i))
      unitRateClockMeasure :=
    unitRateClock_iIndep.precomp hqin
  have hYlaw :
      HasLaw
        (fun clock : UnitRateClockPath => fun i => clock (q i))
        (Measure.pi fun _ : I => expMeasure 1)
        unitRateClockMeasure :=
    hYi.hasLaw_pi (fun i => unitRateClock_eval_hasLaw (q i))
  have htail :
      unitRateClockMeasure
          ((fun clock : UnitRateClockPath => fun i => clock (q i)) ⁻¹' D) =
        ∏ i, expMeasure 1 (B i) := by
    calc
      unitRateClockMeasure
          ((fun clock : UnitRateClockPath => fun i => clock (q i)) ⁻¹' D) =
          unitRateClockMeasure.map
            (fun clock : UnitRateClockPath => fun i => clock (q i)) D := by
              rw [Measure.map_apply (by fun_prop) hD]
      _ = (Measure.pi fun _ : I => expMeasure 1) D := by
        rw [hYlaw.map_eq]
      _ = ∏ i, expMeasure 1 (B i) := by
        simpa [D] using
          (Measure.pi_pi (fun _ : I => expMeasure 1) B hB)
  rw [show {clock |
        renewalEpoch clock n <= s /\
        s < renewalEpoch clock n + clock n /\
        renewalEpoch clock n + clock n - s ∈ A} =
      (fun clock : UnitRateClockPath =>
        (renewalEpoch clock n, clock n)) ⁻¹' E by rfl]
  rw [show {clock | forall i, clock (q i) ∈ B i} =
      (fun clock : UnitRateClockPath => fun i => clock (q i)) ⁻¹' D by
    ext clock
    simp [D]]
  rw [hmeasure]
  exact congrArg
    (fun z => unitRateClockMeasure
      ((fun clock : UnitRateClockPath =>
        (renewalEpoch clock n, clock n)) ⁻¹' E) * z) htail

theorem postRenewalClock_apply_pos {s : Real} {clock : UnitRateClockPath}
    {n r : Nat} (hcount : unitPoissonCount clock s = n) (hr : 0 < r) :
    postRenewalClock s clock r = clock (n + r) := by
  cases r with
  | zero => omega
  | succ r =>
      simp only [postRenewalClock, hcount]
      congr 1
      omega

theorem postRenewalClock_mem_pi_iff
    {s : Real} {clock : UnitRateClockPath} {n : Nat}
    (hcount : unitPoissonCount clock s = n)
    (I : Finset Nat) (t : Nat -> Set Real) :
    postRenewalClock s clock ∈ Set.pi I t <->
      postRenewalClock s clock 0 ∈
          (if 0 ∈ I then t 0 else Set.univ) /\
        forall r : (I.erase 0 : Finset Nat),
          clock (n + r.1) ∈ t r.1 := by
  classical
  constructor
  · intro h
    have hcoord : forall r, r ∈ I ->
        postRenewalClock s clock r ∈ t r := by
      intro r hr
      exact h r (by simpa using hr)
    constructor
    · by_cases h0 : 0 ∈ I
      · simp only [h0, if_true]
        exact hcoord 0 h0
      · simp only [h0, if_false, mem_univ]
    · intro r
      have hrI : r.1 ∈ I := (Finset.mem_erase.mp r.2).2
      have hrpos : 0 < r.1 := Nat.pos_of_ne_zero
        (Finset.mem_erase.mp r.2).1
      rw [← postRenewalClock_apply_pos hcount hrpos]
      exact hcoord r.1 hrI
  · rintro ⟨hzero, htail⟩
    rw [Set.mem_pi]
    intro r hrI
    by_cases hr0 : r = 0
    · subst r
      have hrIF : 0 ∈ I := by simpa using hrI
      simp only [hrIF, if_true] at hzero
      exact hzero
    · let q : (I.erase 0 : Finset Nat) :=
        ⟨r, Finset.mem_erase.mpr ⟨hr0, hrI⟩⟩
      have hq := htail q
      have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
      rw [postRenewalClock_apply_pos hcount hrpos]
      exact hq

theorem unitPoissonCount_post_cylinder {s : Real} (hs : 0 < s)
    (n : Nat) (I : Finset Nat) (t : Nat -> Set Real)
    (ht : forall r, MeasurableSet (t r)) :
    unitRateClockMeasure
        {clock |
          unitPoissonCount clock s = n /\
            postRenewalClock s clock ∈ Set.pi I t} =
      unitRateClockMeasure {clock | unitPoissonCount clock s = n} *
        ∏ r ∈ I, expMeasure 1 (t r) := by
  classical
  let J : Finset Nat := I.erase 0
  let A : Set Real := if 0 ∈ I then t 0 else Set.univ
  let G : Set UnitRateClockPath :=
    {clock |
      renewalEpoch clock n <= s /\
        s < renewalEpoch clock n + clock n /\
        renewalEpoch clock n + clock n - s ∈ A} ∩
    {clock | forall r : J, clock (n + r.1) ∈ t r.1}
  have hA : MeasurableSet A := by
    dsimp only [A]
    split_ifs
    · exact ht 0
    · exact MeasurableSet.univ
  have hG :
      {clock |
        unitPoissonCount clock s = n /\
          postRenewalClock s clock ∈ Set.pi I t} =ᵐ[unitRateClockMeasure] G := by
    filter_upwards [unitRateClock_all_interarrival_pos_ae,
      unit_renewalEpoch_tendsto_atTop_ae] with clock hpos htop
    apply propext
    constructor
    · rintro ⟨hcount, hpi⟩
      have hepoch :=
        (unitPoissonCount_eq_iff_epoch hpos htop hs n).mp hcount
      have hsplit :=
        (postRenewalClock_mem_pi_iff hcount I t).mp hpi
      constructor
      · refine ⟨hepoch.1, ?_, ?_⟩
        · simpa [renewalEpoch_succ] using hepoch.2
        · simpa [A, postRenewalClock, hcount, renewalEpoch_succ] using hsplit.1
      · simpa [J] using hsplit.2
    · rintro ⟨⟨hn, hnnext, hzero⟩, htail⟩
      have hcount : unitPoissonCount clock s = n :=
        (unitPoissonCount_eq_iff_epoch hpos htop hs n).mpr
          ⟨hn, by simpa [renewalEpoch_succ] using hnnext⟩
      refine ⟨hcount, (postRenewalClock_mem_pi_iff hcount I t).mpr ?_⟩
      constructor
      · simpa [A, postRenewalClock, hcount, renewalEpoch_succ] using hzero
      · simpa [J] using htail
  have hbase :
      unitRateClockMeasure
          {clock |
            renewalEpoch clock n <= s /\
              s < renewalEpoch clock n + clock n} =
        unitRateClockMeasure {clock | unitPoissonCount clock s = n} := by
    apply measure_congr
    filter_upwards [unitRateClock_all_interarrival_pos_ae,
      unit_renewalEpoch_tendsto_atTop_ae] with clock hpos htop
    apply propext
    change
      (renewalEpoch clock n <= s /\
        s < renewalEpoch clock n + clock n) <->
          unitPoissonCount clock s = n
    rw [unitPoissonCount_eq_iff_epoch hpos htop hs n]
    rw [renewalEpoch_succ]
  have hfresh := renewalEpoch_boundary_fresh_factor
    (I := J) n (fun r : J => n + r.1)
    (fun r => by
      have hr0 : r.1 ≠ 0 := (Finset.mem_erase.mp r.2).1
      omega)
    (by
      intro r q h
      change n + r.1 = n + q.1 at h
      apply Subtype.ext
      omega)
    (s := s) A hA (fun r : J => t r.1) (fun r => ht r.1)
  have hcentral := renewalEpoch_boundary_event_factor n hs.le A hA
  have hprod :
      expMeasure 1 A * ∏ r : J, expMeasure 1 (t r.1) =
        ∏ r ∈ I, expMeasure 1 (t r) := by
    dsimp only [A, J]
    rw [Finset.prod_coe_sort (I.erase 0)
      (fun r : Nat => expMeasure 1 (t r))]
    by_cases h0 : 0 ∈ I
    · rw [if_pos h0, mul_comm,
        Finset.prod_erase_mul I (fun r => expMeasure 1 (t r)) h0]
    · rw [if_neg h0, measure_univ, one_mul, Finset.erase_eq_self.mpr h0]
  rw [measure_congr hG]
  rw [hfresh, hcentral, hbase]
  rw [mul_assoc, hprod]

theorem unitPoissonCount_post_restrict_map {s : Real} (hs : 0 < s)
    (n : Nat) :
    (unitRateClockMeasure.restrict
        {clock | unitPoissonCount clock s = n}).map
          (postRenewalClock s) =
      unitRateClockMeasure {clock | unitPoissonCount clock s = n} •
        unitRateClockMeasure := by
  let c : ENNReal :=
    unitRateClockMeasure {clock | unitPoissonCount clock s = n}
  let nu : Measure UnitRateClockPath :=
    c⁻¹ •
      (unitRateClockMeasure.restrict
        {clock | unitPoissonCount clock s = n}).map
          (postRenewalClock s)
  have hcposReal :
      0 < unitRateClockMeasure.real
        {clock | unitPoissonCount clock s = n} := by
    rw [unitPoissonCount_real_singleton hs.le n]
    positivity
  have hcne : c ≠ 0 := by
    intro hc
    have hreal :
        unitRateClockMeasure.real
          {clock | unitPoissonCount clock s = n} = 0 := by
      rw [measureReal_def]
      simp [c, hc]
    exact (ne_of_gt hcposReal) hreal
  have hcTop : c ≠ ⊤ := by
    dsimp only [c]
    exact measure_ne_top _ _
  have hnu : nu = unitRateClockMeasure := by
    unfold unitRateClockMeasure
    apply Measure.eq_infinitePi
    intro I t ht
    have hpi : MeasurableSet (Set.pi (I : Set Nat) t) :=
      MeasurableSet.pi I.countable_toSet fun i _ => ht i
    rw [show nu (Set.pi (I : Set Nat) t) =
        c⁻¹ *
          unitRateClockMeasure
            {clock |
              unitPoissonCount clock s = n /\
                postRenewalClock s clock ∈ Set.pi I t} by
      dsimp only [nu]
      rw [Measure.smul_apply,
        Measure.map_apply (measurable_postRenewalClock s) hpi,
        Measure.restrict_apply
          (hpi.preimage (measurable_postRenewalClock s))]
      congr 2
      ext clock
      simp [and_comm]]
    rw [unitPoissonCount_post_cylinder hs n I t ht]
    change c⁻¹ * (c * ∏ i ∈ I, expMeasure 1 (t i)) =
      ∏ i ∈ I, expMeasure 1 (t i)
    rw [← mul_assoc, ENNReal.inv_mul_cancel hcne hcTop, one_mul]
  calc
    (unitRateClockMeasure.restrict
        {clock | unitPoissonCount clock s = n}).map
          (postRenewalClock s) =
        1 •
          (unitRateClockMeasure.restrict
            {clock | unitPoissonCount clock s = n}).map
              (postRenewalClock s) :=
      (one_smul ENNReal _).symm
    _ = (c * c⁻¹) •
          (unitRateClockMeasure.restrict
            {clock | unitPoissonCount clock s = n}).map
              (postRenewalClock s) := by
      rw [ENNReal.mul_inv_cancel hcne hcTop]
    _ = c • nu := by
      simp only [nu, smul_smul]
    _ = c • unitRateClockMeasure := by rw [hnu]
    _ = unitRateClockMeasure
          {clock | unitPoissonCount clock s = n} •
            unitRateClockMeasure := by rfl

theorem unitPoissonCount_post_inter_apply {s : Real} (hs : 0 < s)
    (n : Nat) (B : Set UnitRateClockPath) (hB : MeasurableSet B) :
    unitRateClockMeasure
        {clock |
          unitPoissonCount clock s = n /\ postRenewalClock s clock ∈ B} =
      unitRateClockMeasure {clock | unitPoissonCount clock s = n} *
        unitRateClockMeasure B := by
  have h := congrArg (fun mu : Measure UnitRateClockPath => mu B)
    (unitPoissonCount_post_restrict_map hs n)
  rw [Measure.map_apply (measurable_postRenewalClock s) hB,
    Measure.restrict_apply
      (hB.preimage (measurable_postRenewalClock s)),
    Measure.smul_apply] at h
  have hset :
      {clock |
        unitPoissonCount clock s = n /\ postRenewalClock s clock ∈ B} =
        (postRenewalClock s) ⁻¹' B ∩
          {clock | unitPoissonCount clock s = n} := by
    ext clock
    simp [and_comm]
  rw [hset]
  exact h

theorem unitPoissonCount_post_hasLaw {s : Real} (hs : 0 < s) :
    HasLaw
      (fun clock : UnitRateClockPath =>
        (unitPoissonCount clock s, postRenewalClock s clock))
      ((poissonMeasure (⟨s, hs.le⟩ : NNReal)).prod unitRateClockMeasure)
      unitRateClockMeasure := by
  let X : UnitRateClockPath -> Nat × UnitRateClockPath := fun clock =>
    (unitPoissonCount clock s, postRenewalClock s clock)
  have hX : Measurable X :=
    (PoissonSamplePath.measurable_unitPoissonCount s).prodMk
      (measurable_postRenewalClock s)
  refine ⟨hX.aemeasurable, ?_⟩
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply hX (hA.prod hB), Measure.prod_prod]
  change unitRateClockMeasure
      {clock | unitPoissonCount clock s ∈ A /\ postRenewalClock s clock ∈ B} =
    poissonMeasure (⟨s, hs.le⟩ : NNReal) A * unitRateClockMeasure B
  let C : A -> Set UnitRateClockPath := fun n =>
    {clock |
      unitPoissonCount clock s = n.1 /\ postRenewalClock s clock ∈ B}
  have hCmeas : forall n, MeasurableSet (C n) := by
    intro n
    exact ((PoissonSamplePath.measurable_unitPoissonCount s)
      (measurableSet_singleton n.1)).inter
      (hB.preimage (measurable_postRenewalClock s))
  have hCdisj : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro n m hnm
    rw [Set.disjoint_left]
    intro clock hn hm
    apply hnm
    apply Subtype.ext
    exact hn.1.symm.trans hm.1
  have hCunion :
      {clock |
        unitPoissonCount clock s ∈ A /\ postRenewalClock s clock ∈ B} =
        ⋃ n : A, C n := by
    ext clock
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · rintro ⟨hcount, hpost⟩
      exact ⟨⟨unitPoissonCount clock s, hcount⟩, rfl, hpost⟩
    · rintro ⟨n, hcount, hpost⟩
      exact ⟨hcount ▸ n.2, hpost⟩
  have hcountUnion :
      unitRateClockMeasure {clock | unitPoissonCount clock s ∈ A} =
        ∑' n : A,
          unitRateClockMeasure {clock | unitPoissonCount clock s = n.1} := by
    rw [show {clock | unitPoissonCount clock s ∈ A} =
        ⋃ n : A, {clock | unitPoissonCount clock s = n.1} by
      ext clock
      simp only [mem_setOf_eq, mem_iUnion]
      constructor
      · intro h
        exact ⟨⟨unitPoissonCount clock s, h⟩, rfl⟩
      · rintro ⟨n, h⟩
        exact h ▸ n.2]
    rw [measure_iUnion]
    · intro i j hij
      change Disjoint
        {clock | unitPoissonCount clock s = i.1}
        {clock | unitPoissonCount clock s = j.1}
      rw [Set.disjoint_left]
      intro clock hi hj
      apply hij
      apply Subtype.ext
      exact hi.symm.trans hj
    · intro i
      exact (PoissonSamplePath.measurable_unitPoissonCount s)
        (measurableSet_singleton i.1)
  rw [hCunion, measure_iUnion hCdisj hCmeas]
  calc
    (∑' n : A, unitRateClockMeasure (C n)) =
        ∑' n : A,
          unitRateClockMeasure {clock | unitPoissonCount clock s = n.1} *
            unitRateClockMeasure B := by
      apply tsum_congr
      intro n
      exact unitPoissonCount_post_inter_apply hs n.1 B hB
    _ = (∑' n : A,
          unitRateClockMeasure {clock | unitPoissonCount clock s = n.1}) *
            unitRateClockMeasure B := ENNReal.tsum_mul_right
    _ = unitRateClockMeasure {clock | unitPoissonCount clock s ∈ A} *
          unitRateClockMeasure B := by rw [hcountUnion]
    _ = poissonMeasure (⟨s, hs.le⟩ : NNReal) A *
          unitRateClockMeasure B := by
      have hm :
          unitRateClockMeasure
              {clock | unitPoissonCount clock s ∈ A} =
            poissonMeasure (⟨s, hs.le⟩ : NNReal) A :=
        (unitPoissonCount_hasLaw_poisson hs.le).measure_eq hA
      rw [hm]

theorem postRenewalClock_zero (clock : UnitRateClockPath) :
    postRenewalClock 0 clock = clock := by
  funext r
  cases r with
  | zero =>
      simp [postRenewalClock, unitPoissonCount_of_nonpos, renewalEpoch_succ]
  | succ r =>
      simp [postRenewalClock, unitPoissonCount_of_nonpos]
      congr 1
      omega

theorem unitPoissonCount_post_hasLaw_nonneg {s : Real} (hs : 0 <= s) :
    HasLaw
      (fun clock : UnitRateClockPath =>
        (unitPoissonCount clock s, postRenewalClock s clock))
      ((poissonMeasure (⟨s, hs⟩ : NNReal)).prod unitRateClockMeasure)
      unitRateClockMeasure := by
  rcases hs.eq_or_lt with rfl | hspos
  · have hcount := unitPoissonCount_hasLaw_poisson (s := 0) le_rfl
    have hid : HasLaw (fun clock : UnitRateClockPath => clock)
        unitRateClockMeasure unitRateClockMeasure := HasLaw.id
    have hind : IndepFun
        (fun clock : UnitRateClockPath => unitPoissonCount clock 0)
        (fun clock : UnitRateClockPath => clock) unitRateClockMeasure := by
      convert indepFun_const_left (μ := unitRateClockMeasure) (0 : Nat)
        (fun clock : UnitRateClockPath => clock) using 1
      funext clock
      exact unitPoissonCount_of_nonpos clock le_rfl
    have hpair := hind.hasLaw_prod hcount hid
    simpa [unitPoissonCount_of_nonpos, postRenewalClock_zero] using hpair
  · exact unitPoissonCount_post_hasLaw hspos

theorem renewalEpoch_postRenewalClock_succ
    {s : Real} {clock : UnitRateClockPath} {n : Nat}
    (hcount : unitPoissonCount clock s = n) (m : Nat) :
    renewalEpoch (postRenewalClock s clock) (m + 1) =
      renewalEpoch clock (n + m + 1) - s := by
  induction m with
  | zero =>
      simp [renewalEpoch_succ, postRenewalClock, hcount]
  | succ m ih =>
      calc
        renewalEpoch (postRenewalClock s clock) ((m + 1) + 1) =
            renewalEpoch (postRenewalClock s clock) (m + 1) +
              postRenewalClock s clock (m + 1) :=
          renewalEpoch_succ _ _
        _ = (renewalEpoch clock (n + m + 1) - s) +
              clock (n + m + 1) := by
          rw [ih, postRenewalClock_apply_pos hcount (by omega)]
          congr 2 <;> omega
        _ = (renewalEpoch clock (n + m + 1) +
              clock (n + m + 1)) - s := by ring
        _ = renewalEpoch clock ((n + m + 1) + 1) - s := by
          exact congrArg (fun x : Real => x - s)
            (renewalEpoch_succ clock (n + m + 1)).symm
        _ = renewalEpoch clock (n + (m + 1) + 1) - s := by
          congr 2

theorem unitPoissonCount_add_eq_count_post
    {s u : Real} (hs : 0 < s) (hu : 0 <= u)
    {clock : UnitRateClockPath}
    (hpos : forall r, 0 < clock r)
    (htop : Tendsto (renewalEpoch clock) atTop atTop) :
    unitPoissonCount clock (s + u) =
      unitPoissonCount clock s +
        unitPoissonCount (postRenewalClock s clock) u := by
  let n := unitPoissonCount clock s
  have hnEpoch :=
    (unitPoissonCount_eq_iff_epoch hpos htop hs n).mp rfl
  have hpostPos : forall r, 0 < postRenewalClock s clock r := by
    intro r
    cases r with
    | zero =>
        simp only [postRenewalClock]
        have hnext : s < renewalEpoch clock (n + 1) := by
          simpa only [n] using hnEpoch.2
        linarith
    | succ r =>
        simp only [postRenewalClock]
        exact hpos (n + 1 + r)
  have hadd : Tendsto (fun m : Nat => n + m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_add_left m n) tendsto_id
  have hshift :
      Tendsto (fun m : Nat => renewalEpoch clock (n + m) - s)
        atTop atTop := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-s) (htop.comp hadd)
  have hpostTop :
      Tendsto (renewalEpoch (postRenewalClock s clock)) atTop atTop := by
    apply hshift.congr'
    filter_upwards [eventually_gt_atTop (0 : Nat)] with m hm
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le
      (Nat.one_le_iff_ne_zero.mpr hm.ne')
    rw [Nat.one_add] at hq
    have heq := renewalEpoch_postRenewalClock_succ (n := n) rfl q
    rw [hq]
    simpa [add_assoc] using heq.symm
  rcases hu.eq_or_lt with rfl | hupos
  · simp [unitPoissonCount_of_nonpos]
  · let m := unitPoissonCount (postRenewalClock s clock) u
    have hmEpoch :=
      (unitPoissonCount_eq_iff_epoch hpostPos hpostTop hupos m).mp rfl
    have hsumpos : 0 < s + u := add_pos hs hupos
    apply (unitPoissonCount_eq_iff_epoch hpos htop hsumpos (n + m)).mpr
    constructor
    · by_cases hm0 : m = 0
      · rw [hm0, add_zero]
        exact hnEpoch.1.trans (le_add_of_nonneg_right hu)
      · obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le
          (Nat.one_le_iff_ne_zero.mpr hm0)
        rw [Nat.one_add] at hq
        have heq := renewalEpoch_postRenewalClock_succ (n := n) rfl q
        rw [hq] at hmEpoch ⊢
        rw [heq] at hmEpoch
        change renewalEpoch clock (n + q + 1) <= s + u
        linarith [hmEpoch.1]
    · have heq := renewalEpoch_postRenewalClock_succ (n := n) rfl m
      linarith [hmEpoch.2, heq]

/-- The increments of one unit-rate renewal clock over a finite partition. -/
noncomputable def unitPoissonIncrements (n : Nat)
    (t : Fin (n + 1) -> Real) (clock : UnitRateClockPath) (i : Fin n) : Nat :=
  unitPoissonCount clock (t i.succ) -
    unitPoissonCount clock (t i.castSucc)

/-- The calendar-time increments in one marked coordinate. -/
noncomputable def calendarTokenIncrements (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) (i : Fin n) : Nat :=
  N.calendarTokenCount K omega (t i.succ) j k -
    N.calendarTokenCount K omega (t i.castSucc) j k

theorem measurable_unitPoissonIncrements (n : Nat)
    (t : Fin (n + 1) -> Real) :
    Measurable (unitPoissonIncrements n t) := by
  rw [measurable_pi_iff]
  intro i
  exact (measurable_of_countable
      (fun p : Nat × Nat => p.1 - p.2)).comp
    ((PoissonSamplePath.measurable_unitPoissonCount (t i.succ)).prodMk
      (PoissonSamplePath.measurable_unitPoissonCount (t i.castSucc)))

theorem measurable_calendarTokenIncrements (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real) (j : Server) (k : Buffer) :
    Measurable (fun omega : CalendarPoissonSample
        (Buffer := Buffer) (Server := Server) =>
      N.calendarTokenIncrements K n t omega j k) := by
  rw [measurable_pi_iff]
  intro i
  exact (measurable_of_countable
      (fun p : Nat × Nat => p.1 - p.2)).comp
    ((PoissonSamplePath.measurable_calendarTokenCount
        N K (t i.succ) j k).prodMk
      (PoissonSamplePath.measurable_calendarTokenCount
        N K (t i.castSucc) j k))

noncomputable def unitPoissonIncrementParameter (n : Nat)
    (t : Fin (n + 1) -> Real) (ht : Monotone t) (i : Fin n) : NNReal :=
  ⟨t i.succ - t i.castSucc,
    sub_nonneg.mpr (ht i.castSucc_le_succ)⟩

theorem unitPoissonIncrements_hasLaw (n : Nat)
    (t : Fin (n + 1) -> Real)
    (ht0 : t 0 = 0) (ht : Monotone t) :
    HasLaw
      (unitPoissonIncrements n t)
      (Measure.pi fun i : Fin n =>
        poissonMeasure (unitPoissonIncrementParameter n t ht i))
      unitRateClockMeasure := by
  induction n with
  | zero =>
      have hind :
          iIndepFun
            (fun i : Fin 0 => fun clock : UnitRateClockPath =>
              unitPoissonIncrements 0 t clock i)
            unitRateClockMeasure :=
        iIndepFun.of_subsingleton
      exact hind.hasLaw_pi (fun i => Fin.elim0 i)
  | succ n ih =>
      let s : Real := t ⟨1, by omega⟩
      let u : Fin (n + 1) -> Real := fun i => t i.succ - s
      have hs0 : 0 <= s := by
        dsimp only [s]
        rw [← ht0]
        apply ht
        exact Fin.le_iff_val_le_val.mpr (by simp)
      have hu0 : u 0 = 0 := by
        simp [u, s]
      have hu : Monotone u := by
        intro i j hij
        exact sub_le_sub_right
          (ht (Fin.succ_le_succ_iff.mpr hij)) s
      have htail := ih u hu0 hu
      have hfirst := unitPoissonCount_hasLaw_poisson hs0
      have hpair := unitPoissonCount_post_hasLaw_nonneg hs0
      have hpost : HasLaw (postRenewalClock s)
          unitRateClockMeasure unitRateClockMeasure := by
        refine ⟨(measurable_postRenewalClock s).aemeasurable, ?_⟩
        calc
          unitRateClockMeasure.map (postRenewalClock s) =
              (unitRateClockMeasure.map
                (fun c => (unitPoissonCount c s,
                  postRenewalClock s c))).map Prod.snd := by
            rw [Measure.map_map measurable_snd
              ((PoissonSamplePath.measurable_unitPoissonCount s).prodMk
                (measurable_postRenewalClock s))]
            rfl
          _ = ((poissonMeasure (⟨s, hs0⟩ : NNReal)).prod
                unitRateClockMeasure).map Prod.snd := by
            rw [hpair.map_eq]
          _ = unitRateClockMeasure := by
            letI : IsProbabilityMeasure
                (poissonMeasure (⟨s, hs0⟩ : NNReal)) :=
              instIsProbabilityMeasureNatPoissonMeasure _
            rw [Measure.map_snd_prod, measure_univ, one_smul]
      have hind : IndepFun
          (fun clock : UnitRateClockPath => unitPoissonCount clock s)
          (postRenewalClock s) unitRateClockMeasure :=
        (indepFun_iff_hasLaw_prodMk_prod hfirst hpost).mpr hpair
      have hindTail : IndepFun
          (fun clock : UnitRateClockPath => unitPoissonCount clock s)
          (fun clock => unitPoissonIncrements n u
            (postRenewalClock s clock))
          unitRateClockMeasure :=
        hind.comp measurable_id (measurable_unitPoissonIncrements n u)
      have htailPost := htail.fun_comp hpost
      have hjoint := hindTail.hasLaw_prod hfirst htailPost
      let mu : Fin (n + 1) -> Measure Nat := fun i =>
        poissonMeasure
          (unitPoissonIncrementParameter (n + 1) t ht i)
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => Nat) (0 : Fin (n + 1))
      have htailParameter :
          (fun j : Fin n => mu ((0 : Fin (n + 1)).succAbove j)) =
            (fun j : Fin n =>
              poissonMeasure
                (unitPoissonIncrementParameter n u hu j)) := by
        funext j
        apply congrArg poissonMeasure
        apply NNReal.eq
        simp [mu, unitPoissonIncrementParameter, u, s]
      have hfirstParameter :
          mu (0 : Fin (n + 1)) =
            poissonMeasure (⟨s, hs0⟩ : NNReal) := by
        apply congrArg poissonMeasure
        apply NNReal.eq
        simp [mu, unitPoissonIncrementParameter, s, ht0]
      have hmp := measurePreserving_piFinSuccAbove mu (0 : Fin (n + 1))
      rw [htailParameter, hfirstParameter] at hmp
      have hmapped := hmp.symm.comp_hasLaw hjoint
      apply hmapped.congr
      filter_upwards [unitRateClock_all_interarrival_pos_ae,
        unit_renewalEpoch_tendsto_atTop_ae] with clock hpos htop
      apply e.injective
      apply Prod.ext
      · simp [e, unitPoissonIncrements, s, ht0,
          unitPoissonCount_of_nonpos]
      · funext j
        simp only [e, MeasurableEquiv.piFinSuccAbove_apply,
          Fin.insertNth_apply_succAbove,
          MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
        change
          unitPoissonIncrements (n + 1) t clock
              ((0 : Fin (n + 1)).succAbove j) =
            unitPoissonIncrements n u (postRenewalClock s clock) j
        rcases hs0.eq_or_lt with hszero | hspos
        · have hsz : s = 0 := hszero.symm
          simp [unitPoissonIncrements, u, hsz, postRenewalClock_zero]
        · have huNonneg : forall i, 0 <= u i := by
            intro i
            rw [← hu0]
            exact hu (Fin.zero_le i)
          have hleft := unitPoissonCount_add_eq_count_post hspos
            (huNonneg j.castSucc) hpos htop
          have hright := unitPoissonCount_add_eq_count_post hspos
            (huNonneg j.succ) hpos htop
          unfold unitPoissonIncrements
          rw [show t ((0 : Fin (n + 1)).succAbove j).succ =
              s + u j.succ by
            simp [u, s]]
          rw [show t ((0 : Fin (n + 1)).succAbove j).castSucc =
              s + u j.castSucc by
            simp [u, s]]
          rw [hleft, hright]
          omega

theorem unitPoissonIncrements_hasLaw_nonneg (n : Nat)
    (t : Fin (n + 1) -> Real)
    (ht0 : 0 <= t 0) (ht : Monotone t) :
    HasLaw
      (unitPoissonIncrements n t)
      (Measure.pi fun i : Fin n =>
        poissonMeasure (unitPoissonIncrementParameter n t ht i))
      unitRateClockMeasure := by
  let s : Real := t 0
  let u : Fin (n + 1) -> Real := fun i => t i - s
  have hu0 : u 0 = 0 := by simp [u, s]
  have hu : Monotone u := fun _ _ hij =>
    sub_le_sub_right (ht hij) s
  have huLaw := unitPoissonIncrements_hasLaw n u hu0 hu
  have hpost := unitPoissonCount_post_hasLaw_nonneg ht0
  have hpostLaw : HasLaw (postRenewalClock s)
      unitRateClockMeasure unitRateClockMeasure := by
    refine ⟨(measurable_postRenewalClock s).aemeasurable, ?_⟩
    calc
      unitRateClockMeasure.map (postRenewalClock s) =
          (unitRateClockMeasure.map
            (fun c => (unitPoissonCount c s,
              postRenewalClock s c))).map Prod.snd := by
        rw [Measure.map_map measurable_snd
          ((PoissonSamplePath.measurable_unitPoissonCount s).prodMk
            (measurable_postRenewalClock s))]
        rfl
      _ = ((poissonMeasure (⟨s, ht0⟩ : NNReal)).prod
            unitRateClockMeasure).map Prod.snd := by
        rw [hpost.map_eq]
      _ = unitRateClockMeasure := by
        letI : IsProbabilityMeasure
            (poissonMeasure (⟨s, ht0⟩ : NNReal)) :=
          instIsProbabilityMeasureNatPoissonMeasure _
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hshifted := huLaw.fun_comp hpostLaw
  have hparameters :
      (fun i : Fin n =>
        poissonMeasure (unitPoissonIncrementParameter n u hu i)) =
      (fun i : Fin n =>
        poissonMeasure (unitPoissonIncrementParameter n t ht i)) := by
    funext i
    apply congrArg poissonMeasure
    apply NNReal.eq
    simp [unitPoissonIncrementParameter, u, s]
  rw [hparameters] at hshifted
  apply hshifted.congr
  filter_upwards [unitRateClock_all_interarrival_pos_ae,
    unit_renewalEpoch_tendsto_atTop_ae] with clock hpos htop
  funext i
  rcases ht0.eq_or_lt with hszero | hspos
  · have hs : s = 0 := hszero.symm
    simp [unitPoissonIncrements, u, hs, postRenewalClock_zero]
  · have huNonneg : forall r, 0 <= u r := by
      intro r
      dsimp only [u]
      exact sub_nonneg.mpr (ht (Fin.zero_le r))
    have hleft := unitPoissonCount_add_eq_count_post (s := s) hspos
      (huNonneg i.castSucc) hpos htop
    have hright := unitPoissonCount_add_eq_count_post (s := s) hspos
      (huNonneg i.succ) hpos htop
    unfold unitPoissonIncrements
    rw [show t i.succ = s + u i.succ by simp [u, s]]
    rw [show t i.castSucc = s + u i.castSucc by simp [u, s]]
    rw [hleft, hright]
    exact Nat.add_sub_add_left _ _ _

noncomputable def calendarTokenIncrementParameter (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real) (ht : Monotone t)
    (j : Server) (k : Buffer) (i : Fin n) : NNReal :=
  ⟨((K : Nat) : Real) * N.phi j k *
      (t i.succ - t i.castSucc),
    mul_nonneg
      (mul_nonneg (by positivity) (N.phi_nonneg j k))
      (sub_nonneg.mpr (ht i.castSucc_le_succ))⟩

theorem calendarTokenIncrements_hasLaw (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real)
    (ht0 : 0 <= t 0) (ht : Monotone t)
    (j : Server) (k : Buffer) :
    HasLaw
      (fun omega : CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        N.calendarTokenIncrements K n t omega j k)
      (Measure.pi fun i : Fin n =>
        poissonMeasure
          (N.calendarTokenIncrementParameter K n t ht j k i))
      N.calendarPoissonMeasure := by
  let q : Fin (n + 1) -> Real := fun r =>
    N.coordinateOperationalTime K (t r) j k
  have hc : 0 <= ((K : Nat) : Real) * N.phi j k :=
    mul_nonneg (by positivity) (N.phi_nonneg j k)
  have hq0 : 0 <= q 0 := by
    exact mul_nonneg hc (le_max_right (t 0) 0)
  have hq : Monotone q := by
    intro a b hab
    exact mul_le_mul_of_nonneg_left
      (max_le_max (ht hab) le_rfl) hc
  have hunit := unitPoissonIncrements_hasLaw_nonneg n q hq0 hq
  have hcomp := hunit.fun_comp (coordinateClock_hasLaw N j k)
  have htNonneg : forall r, 0 <= t r := fun r =>
    ht0.trans (ht (Fin.zero_le r))
  have hparameters :
      (fun i : Fin n =>
        poissonMeasure (unitPoissonIncrementParameter n q hq i)) =
      (fun i : Fin n =>
        poissonMeasure
          (N.calendarTokenIncrementParameter K n t ht j k i)) := by
    funext i
    apply congrArg poissonMeasure
    apply NNReal.eq
    change
      q i.succ - q i.castSucc =
        ((K : Nat) : Real) * N.phi j k *
          (t i.succ - t i.castSucc)
    dsimp only [q, coordinateOperationalTime]
    rw [max_eq_left (htNonneg i.succ),
      max_eq_left (htNonneg i.castSucc)]
    ring
  rw [hparameters] at hcomp
  change HasLaw
    (fun omega : CalendarPoissonSample
        (Buffer := Buffer) (Server := Server) =>
      unitPoissonIncrements n q (omega j k))
    (Measure.pi fun i : Fin n =>
      poissonMeasure
        (N.calendarTokenIncrementParameter K n t ht j k i))
    N.calendarPoissonMeasure
  exact hcomp

theorem calendarTokenIncrements_coordinate_iIndep (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real) :
    iIndepFun
      (fun p : Sigma (fun _ : Server => Buffer) =>
        fun omega : CalendarPoissonSample
            (Buffer := Buffer) (Server := Server) =>
          N.calendarTokenIncrements K n t omega p.1 p.2)
      N.calendarPoissonMeasure := by
  have h := N.coordinateClock_iIndep.comp
    (fun p clock =>
      unitPoissonIncrements n
        (fun r => N.coordinateOperationalTime K (t r) p.1 p.2)
        clock)
    (fun p =>
      measurable_unitPoissonIncrements n
        (fun r => N.coordinateOperationalTime K (t r) p.1 p.2))
  change iIndepFun
    (fun p : Sigma (fun _ : Server => Buffer) =>
      fun omega : CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        unitPoissonIncrements n
          (fun r => N.coordinateOperationalTime K (t r) p.1 p.2)
          (omega p.1 p.2))
    N.calendarPoissonMeasure
  simpa only [Function.comp_def] using h

theorem calendarTokenIncrements_joint_hasLaw (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real)
    (ht0 : 0 <= t 0) (ht : Monotone t) :
    HasLaw
      (fun omega : CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        fun p : Sigma (fun _ : Server => Buffer) =>
          fun i : Fin n =>
            N.calendarTokenIncrements K n t omega p.1 p.2 i)
      (Measure.pi fun p : Sigma (fun _ : Server => Buffer) =>
        Measure.pi fun i : Fin n =>
          poissonMeasure
            (N.calendarTokenIncrementParameter K n t ht p.1 p.2 i))
      N.calendarPoissonMeasure := by
  exact (N.calendarTokenIncrements_coordinate_iIndep K n t).hasLaw_pi
    (fun p =>
      N.calendarTokenIncrements_hasLaw K n t ht0 ht p.1 p.2)

theorem calendarTokenIncrements_phi_zero_hasLaw (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real)
    (ht0 : 0 <= t 0) (ht : Monotone t)
    (j : Server) (k : Buffer) (hphi : N.phi j k = 0) :
    HasLaw
      (fun omega : CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        N.calendarTokenIncrements K n t omega j k)
      (Measure.pi fun _ : Fin n => poissonMeasure 0)
      N.calendarPoissonMeasure := by
  have h := N.calendarTokenIncrements_hasLaw K n t ht0 ht j k
  have hparameters :
      (fun i : Fin n =>
        poissonMeasure
          (N.calendarTokenIncrementParameter K n t ht j k i)) =
      (fun _ : Fin n => poissonMeasure 0) := by
    funext i
    apply congrArg poissonMeasure
    apply NNReal.eq
    change
      ((K : Nat) : Real) * N.phi j k *
          (t i.succ - t i.castSucc) = 0
    simp [hphi]
  rw [hparameters] at h
  exact h

end StateDepMOR.Network

namespace StateDepMOR.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

/-- The exact product law of all calendar-time partition increments. -/
noncomputable def calendarIncrementProductLaw
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real) (ht : Monotone t) :
    Measure ((p : Sigma (fun _ : Server => Buffer)) -> Fin n -> Nat) :=
  Measure.pi fun p =>
    Measure.pi fun i =>
      poissonMeasure
        (N.calendarTokenIncrementParameter K n t ht p.1 p.2 i)

/-- Flatten all marked-coordinate increments into one finite vector. -/
noncomputable def calendarIncrementVector
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real)
    (omega : CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    (p : Sigma (fun _ : Server => Buffer)) -> Fin n -> Nat :=
  fun p => N.calendarTokenIncrements K n t omega p.1 p.2

theorem measurable_calendarIncrementVector
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real) :
    Measurable (calendarIncrementVector N K n t) := by
  apply measurable_pi_iff.mpr
  intro p
  exact N.measurable_calendarTokenIncrements K n t p.1 p.2

theorem calendarIncrementVector_hasLaw
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real)
    (ht0 : 0 <= t 0) (ht : Monotone t) :
    HasLaw
      (calendarIncrementVector N K n t)
      (calendarIncrementProductLaw N K n t ht)
      N.calendarPoissonMeasure := by
  change HasLaw
    (fun omega p =>
      N.calendarTokenIncrements K n t omega p.1 p.2)
    (Measure.pi fun p : Sigma (fun _ : Server => Buffer) =>
      Measure.pi fun i : Fin n =>
        poissonMeasure
          (N.calendarTokenIncrementParameter K n t ht p.1 p.2 i))
    N.calendarPoissonMeasure
  exact N.calendarTokenIncrements_joint_hasLaw K n t ht0 ht

theorem calendarPoissonMeasure_map_calendarIncrementVector
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real)
    (ht0 : 0 <= t 0) (ht : Monotone t) :
    Measure.map
        (calendarIncrementVector N K n t)
        N.calendarPoissonMeasure =
      calendarIncrementProductLaw N K n t ht :=
  (calendarIncrementVector_hasLaw N K n t ht0 ht).map_eq

/-- Coordinatewise fluid scaling of the finite increment vector. -/
noncomputable def scaleCalendarIncrementVector (K : PNat) {n : Nat}
    (x : (p : Sigma (fun _ : Server => Buffer)) -> Fin n -> Nat) :
    (p : Sigma (fun _ : Server => Buffer)) -> Fin n -> Real :=
  fun p i => (x p i : Real) / ((K : Nat) : Real)

theorem measurable_scaleCalendarIncrementVector (K : PNat) (n : Nat) :
    Measurable
      (scaleCalendarIncrementVector
        (Buffer := Buffer) (Server := Server) K (n := n)) := by
  apply measurable_pi_iff.mpr
  intro p
  apply measurable_pi_iff.mpr
  intro i
  exact ((MeasurableEmbedding.natCast (α := Real)).measurable.comp
    ((measurable_pi_apply i).comp
      (measurable_pi_apply p))).div_const _

/-- Differences of the actual fluid-scaled calendar input. -/
noncomputable def calendarScaledIncrementVector
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real)
    (omega : CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    (p : Sigma (fun _ : Server => Buffer)) -> Fin n -> Real :=
  fun p i =>
    N.calendarScaledInput K omega (t i.succ) p.1 p.2 -
      N.calendarScaledInput K omega (t i.castSucc) p.1 p.2

theorem measurable_calendarScaledIncrementVector
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real) :
    Measurable (calendarScaledIncrementVector N K n t) := by
  apply measurable_pi_iff.mpr
  intro p
  apply measurable_pi_iff.mpr
  intro i
  exact
    (PoissonSamplePath.measurable_calendarScaledInput
      N K (t i.succ) p.1 p.2).sub
    (PoissonSamplePath.measurable_calendarScaledInput
      N K (t i.castSucc) p.1 p.2)

theorem calendarScaledIncrementVector_ae_eq_scale
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real) (ht : Monotone t) :
    calendarScaledIncrementVector N K n t =ᵐ[N.calendarPoissonMeasure]
      fun omega =>
        scaleCalendarIncrementVector K
          (calendarIncrementVector N K n t omega) := by
  filter_upwards [N.all_renewalEpoch_ratio_tendsto_ae] with omega hEpoch
  funext p i
  have htime :
      N.coordinateOperationalTime K (t i.castSucc) p.1 p.2 <=
        N.coordinateOperationalTime K (t i.succ) p.1 p.2 := by
    unfold coordinateOperationalTime
    exact mul_le_mul_of_nonneg_left
      (max_le_max_right 0 (ht i.castSucc_le_succ))
      (mul_nonneg (by positivity) (N.phi_nonneg p.1 p.2))
  have hle :
      N.calendarTokenCount K omega (t i.castSucc) p.1 p.2 <=
        N.calendarTokenCount K omega (t i.succ) p.1 p.2 := by
    exact PoissonSamplePath.unitPoissonCount_monotone
      (omega p.1 p.2) (hEpoch p.1 p.2) htime
  simp only [calendarScaledIncrementVector, scaleCalendarIncrementVector,
    calendarIncrementVector, calendarTokenIncrements, calendarScaledInput]
  rw [Nat.cast_sub hle]
  ring

/-- Exact law of the fluid-scaled full partition increment array. -/
theorem calendarScaledIncrementVector_hasLaw
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real)
    (ht0 : 0 <= t 0) (ht : Monotone t) :
    HasLaw
      (calendarScaledIncrementVector N K n t)
      (Measure.map
        (scaleCalendarIncrementVector
          (Buffer := Buffer) (Server := Server) K (n := n))
        (calendarIncrementProductLaw N K n t ht))
      N.calendarPoissonMeasure := by
  let scale :=
    scaleCalendarIncrementVector
      (Buffer := Buffer) (Server := Server) K (n := n)
  have hscale :
      HasLaw scale
        (Measure.map scale (calendarIncrementProductLaw N K n t ht))
        (calendarIncrementProductLaw N K n t ht) :=
    ⟨(measurable_scaleCalendarIncrementVector
        (Buffer := Buffer) (Server := Server) K n).aemeasurable, rfl⟩
  have hcomp := hscale.fun_comp
    (calendarIncrementVector_hasLaw N K n t ht0 ht)
  exact hcomp.congr
    (calendarScaledIncrementVector_ae_eq_scale N K n t ht)

theorem calendarPoissonMeasure_map_calendarScaledIncrementVector
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real)
    (ht0 : 0 <= t 0) (ht : Monotone t) :
    Measure.map
        (calendarScaledIncrementVector N K n t)
        N.calendarPoissonMeasure =
      Measure.map
        (scaleCalendarIncrementVector
          (Buffer := Buffer) (Server := Server) K (n := n))
        (calendarIncrementProductLaw N K n t ht) :=
  (calendarScaledIncrementVector_hasLaw N K n t ht0 ht).map_eq

end StateDepMOR.Network

namespace StateDepMOR.PoissonSamplePath

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

/-- Finite increment projection of a bundled matrix path. -/
def pathPartitionIncrements {T : Real} {n : Nat}
    (t : Fin (n + 1) -> Horizon T)
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    (p : Sigma (fun _ : Server => Buffer)) -> Fin n -> Real :=
  fun p i => x (t i.succ) p.1 p.2 - x (t i.castSucc) p.1 p.2

/-- The actual calendar path has the scaled full product increment law. -/
theorem calendarPath_partitionIncrements_hasLaw
    (N : Network Buffer Server) {T : Real} (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Horizon T)
    (ht0 : 0 <= (t 0 : Real))
    (ht : Monotone (fun q => (t q : Real))) :
    HasLaw
      (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        pathPartitionIncrements t (calendarPath N T K omega))
      (Measure.map
        (Network.scaleCalendarIncrementVector
          (Buffer := Buffer) (Server := Server) K (n := n))
        (Network.calendarIncrementProductLaw N K n
          (fun q => (t q : Real)) ht))
      N.calendarPoissonMeasure := by
  have hraw :=
    Network.calendarScaledIncrementVector_hasLaw N K n
      (fun q => (t q : Real)) ht0 ht
  apply hraw.congr
  filter_upwards [calendarPath_apply_ae N T K] with omega homega
  funext p i
  simp only [pathPartitionIncrements,
    Network.calendarScaledIncrementVector]
  rw [homega (t i.succ) p.1 p.2,
    homega (t i.castSucc) p.1 p.2]

/-- `Measure.map` form of the actual path partition-increment law. -/
theorem calendarPoissonMeasure_map_calendarPath_partitionIncrements
    (N : Network Buffer Server) {T : Real} (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Horizon T)
    (ht0 : 0 <= (t 0 : Real))
    (ht : Monotone (fun q => (t q : Real))) :
    Measure.map
        (fun omega : Network.CalendarPoissonSample
            (Buffer := Buffer) (Server := Server) =>
          pathPartitionIncrements t (calendarPath N T K omega))
        N.calendarPoissonMeasure =
      Measure.map
        (Network.scaleCalendarIncrementVector
          (Buffer := Buffer) (Server := Server) K (n := n))
        (Network.calendarIncrementProductLaw N K n
          (fun q => (t q : Real)) ht) :=
  (calendarPath_partitionIncrements_hasLaw N K n t ht0 ht).map_eq

end StateDepMOR.PoissonSamplePath

namespace StateDepMOR.PoissonSamplePath

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

abbrev PartitionCoord (P : ActionPartition T) :=
  Sigma (fun _ : Server => Buffer) × Fin P.intervals

noncomputable def partitionIntensity
    (N : Network Buffer Server) {T : Real} (P : ActionPartition T) :
    PartitionCoord (Buffer := Buffer) (Server := Server) P -> NNReal :=
  fun a =>
    Real.toNNReal (P.width a.2) * Real.toNNReal (N.phi a.1.1 a.1.2)

noncomputable def partitionIncrementProductLaw
    (N : Network Buffer Server) (K : PNat) {T : Real}
    (P : ActionPartition T) :
    Measure
      ((p : Sigma (fun _ : Server => Buffer)) -> Fin P.intervals -> Nat) :=
  Measure.pi fun p =>
    Measure.pi fun i =>
      ProbabilityTheory.poissonMeasure
        (N.calendarTokenIncrementParameter K P.intervals P.point
          P.strictMono_point.monotone p.1 p.2 i)

theorem partitionIncrements_hasLaw
    (N : Network Buffer Server) (K : PNat) {T : Real}
    (P : ActionPartition T) :
    HasLaw
      (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        fun p i =>
          N.calendarTokenIncrements K P.intervals P.point omega p.1 p.2 i)
      (partitionIncrementProductLaw N K P)
      N.calendarPoissonMeasure := by
  exact N.calendarTokenIncrements_joint_hasLaw K P.intervals P.point
    (by rw [P.point_zero]) P.strictMono_point.monotone

@[simp]
theorem coe_calendarTokenIncrementParameter
    (N : Network Buffer Server) (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Real) (ht : Monotone t)
    (j : Server) (k : Buffer) (i : Fin n) :
    (N.calendarTokenIncrementParameter K n t ht j k i : Real) =
      ((K : Nat) : Real) * N.phi j k *
        (t i.succ - t i.castSucc) := by
  rfl

theorem calendarIncrementProductLaw_singleton_eq_countLaw
    (N : Network Buffer Server) (K : PNat) {T : Real}
    (P : ActionPartition T)
    (n : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Nat) :
    partitionIncrementProductLaw N K P {fun p i => n (p, i)} =
      PoissonFiniteArray.countLaw (partitionIntensity N P) K {n} := by
  classical
  letI : forall p : Sigma (fun _ : Server => Buffer),
      IsProbabilityMeasure
        (Measure.pi fun i =>
          ProbabilityTheory.poissonMeasure
            (N.calendarTokenIncrementParameter K P.intervals P.point
              P.strictMono_point.monotone p.1 p.2 i)) :=
    fun p => by
      infer_instance
  unfold partitionIncrementProductLaw
  rw [Measure.pi_singleton]
  unfold PoissonFiniteArray.countLaw
  rw [Measure.pi_singleton]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Measure.pi_singleton]
  unfold partitionIntensity
  apply Finset.prod_congr rfl
  intro i hi
  congr 2
  apply NNReal.eq
  rw [coe_calendarTokenIncrementParameter]
  simp only [NNReal.coe_mul, NNReal.coe_natCast, Prod.fst, Prod.snd,
    Sigma.fst, Sigma.snd]
  rw [Real.coe_toNNReal (P.width i) (P.width_pos i).le,
    Real.coe_toNNReal (N.phi p.1 p.2) (N.phi_nonneg p.1 p.2)]
  unfold ActionPartition.width ActionPartition.right ActionPartition.left
  ring

end StateDepMOR.PoissonSamplePath


open Real Set Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction
open MeasureTheory

namespace InformationTheory

noncomputable section

lemma klFun_conjugate_bound (r : ℝ) (hr : 0 ≤ r) (a : ℝ) :
    r * a + 1 - exp a ≤ klFun r := by
  by_cases h : r = 0
  · simp [h, klFun_zero, Real.exp_nonneg]
  have hr' : 0 < r := lt_of_le_of_ne hr (Ne.symm h)
  have he := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (a - log r)) hr
  rw [Real.exp_sub, Real.exp_log hr'] at he
  have hcancel : r * (exp a / r) = exp a := by field_simp
  rw [hcancel] at he
  rw [klFun]
  linarith

variable {X : Type*} [MeasurableSpace X]

def entropyTest (mu nu : Measure X) (f : X → ℝ) : ℝ :=
  ∫ x, f x ∂mu + ∫ x, (1 - exp (f x)) ∂nu

lemma entropyTest_le_klDiv (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (f : X → ℝ) (hf : Integrable f mu) (hfe : Integrable (fun x => exp (f x)) nu) :
    ENNReal.ofReal (entropyTest mu nu f) ≤ klDiv mu nu := by
  by_cases hac : mu ≪ nu
  swap
  · simp [klDiv_of_not_ac hac]
  by_cases hint : Integrable (llr mu nu) mu
  swap
  · simp [klDiv_of_not_integrable hint]
  have hfr : Integrable (fun x => (mu.rnDeriv nu x).toReal * f x) nu := by
    rw [integrable_toReal_rnDeriv_mul_iff hac]
    exact hf
  have hq : Integrable
      (fun x => (mu.rnDeriv nu x).toReal * f x + 1 - exp (f x)) nu :=
    (hfr.add (integrable_const 1)).sub hfe
  have hle :
      ∫ x, ((mu.rnDeriv nu x).toReal * f x + 1 - exp (f x)) ∂nu ≤
        ∫ x, klFun (mu.rnDeriv nu x).toReal ∂nu := by
    apply integral_mono_ae hq
    · rwa [integrable_klFun_rnDeriv_iff hac]
    · filter_upwards with x
      exact klFun_conjugate_bound _ ENNReal.toReal_nonneg _
  have hle' :
      (∫ x, (mu.rnDeriv nu x).toReal * f x ∂nu) + (∫ _x, (1 : ℝ) ∂nu) -
          (∫ x, exp (f x) ∂nu) ≤
        ∫ x, klFun (mu.rnDeriv nu x).toReal ∂nu := by
    rw [← integral_add hfr (integrable_const 1)]
    have heq := integral_sub (hfr.add (integrable_const 1)) hfe
    exact heq ▸ hle
  rw [integral_toReal_rnDeriv_mul hac] at hle'
  rw [integral_klFun_rnDeriv hac hint, integral_const, smul_eq_mul, mul_one] at hle'
  rw [entropyTest, integral_sub (integrable_const 1) hfe,
    klDiv_of_ac_of_integrable hac hint]
  simp only [integral_const, smul_eq_mul, mul_one]
  apply ENNReal.ofReal_le_ofReal
  linarith

lemma continuous_entropyTest (nu : Measure X) [IsFiniteMeasure nu]
    [TopologicalSpace X] [OpensMeasurableSpace X] (f : X →ᵇ ℝ) :
    Continuous (fun mu : FiniteMeasure X => entropyTest (mu : Measure X) nu f) := by
  have hfirst : Continuous
      (fun mu : FiniteMeasure X => ∫ x, f x ∂(mu : Measure X)) := by
    rw [continuous_iff_continuousAt]
    intro mu
    exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_id f)
  change Continuous
    ((fun mu : FiniteMeasure X => ∫ x, f x ∂(mu : Measure X)) +
      fun _ => ∫ x, (1 - exp (f x)) ∂nu)
  exact hfirst.add continuous_const

lemma continuous_ofReal_entropyTest (nu : Measure X) [IsFiniteMeasure nu]
    [TopologicalSpace X] [OpensMeasurableSpace X] (f : X →ᵇ ℝ) :
    Continuous (fun mu : FiniteMeasure X =>
      ENNReal.ofReal (entropyTest (mu : Measure X) nu f)) :=
  ENNReal.continuous_ofReal.comp (continuous_entropyTest nu f)

def clip (M x : ℝ) : ℝ := max (-M) (min x M)

lemma lipschitzWith_clip (M : ℝ) : LipschitzWith 1 (clip M) :=
  (LipschitzWith.id.min_const M).const_max (-M)

lemma clip_eq_self {M x : ℝ} (hx : x ∈ Icc (-M) M) : clip M x = x := by
  simp [clip, hx.1, hx.2]

lemma clip_mem_Icc {M : ℝ} (hM : 0 ≤ M) (x : ℝ) : clip M x ∈ Icc (-M) M := by
  simp only [clip, mem_Icc]
  constructor <;> grind

lemma norm_exp_sub_exp_le {M x y : ℝ} (hx : x ∈ Icc (-M) M) (hy : y ∈ Icc (-M) M) :
    ‖exp x - exp y‖ ≤ exp M * ‖x - y‖ := by
  have h := (convex_Icc (-M) M).norm_image_sub_le_of_norm_deriv_le
    (f := exp) (x := x) (y := y) (C := exp M)
    (fun _ _ => Real.differentiable_exp.differentiableAt)
    (fun z hz => by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
      exact Real.exp_le_exp.mpr hz.2)
    hx hy
  simpa [norm_sub_rev] using h

lemma exists_boundedContinuous_entropyTest_ge
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X]
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    {h : X → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M)
    (hhM : ∀ x, h x ∈ Icc (-M) M) {eps : ℝ} (heps : 0 < eps) :
    ∃ g : X →ᵇ ℝ, entropyTest mu nu h ≤ entropyTest mu nu g + eps := by
  let rho := mu + nu
  let delta := eps / (1 + exp M)
  have hdelta : 0 < delta := div_pos heps (by positivity)
  have hi : Integrable h rho := Integrable.of_bound hh.aestronglyMeasurable M <|
    .of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_le).2 (hhM x)
  obtain ⟨g, hg, hgint⟩ := hi.exists_boundedContinuous_integral_sub_le hdelta
  let gc : X →ᵇ ℝ := BoundedContinuousFunction.comp (clip M) (lipschitzWith_clip M) g
  have hgcM (x : X) : gc x ∈ Icc (-M) M := clip_mem_Icc hM _
  have hcontract (x : X) : ‖h x - gc x‖ ≤ ‖h x - g x‖ := by
    have hlip := (lipschitzWith_iff_dist_le_mul.mp (lipschitzWith_clip M)) (h x) (g x)
    rw [clip_eq_self (hhM x)] at hlip
    simpa [gc, Real.dist_eq] using hlip
  have hgcint : Integrable (gc : X → ℝ) rho :=
    Integrable.of_bound gc.continuous.aestronglyMeasurable M <|
      .of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact (abs_le).2 (hgcM x)
  have hdiffint : Integrable (fun x => ‖h x - gc x‖) rho := (hi.sub hgcint).norm
  have hrawint : Integrable (fun x => ‖h x - g x‖) rho := (hi.sub hgint).norm
  have herr : ∫ x, ‖h x - gc x‖ ∂rho ≤ delta :=
    (integral_mono_ae hdiffint hrawint (.of_forall hcontract)).trans hg
  have hrho_mu : mu ≤ rho := Measure.le_add_right le_rfl
  have hrho_nu : nu ≤ rho := Measure.le_add_left le_rfl
  have herr_mu : ∫ x, ‖h x - gc x‖ ∂mu ≤ delta :=
    (integral_mono_measure hrho_mu (.of_forall fun _ => norm_nonneg _)
      hdiffint).trans herr
  have herr_nu : ∫ x, ‖h x - gc x‖ ∂nu ≤ delta :=
    (integral_mono_measure hrho_nu (.of_forall fun _ => norm_nonneg _)
      hdiffint).trans herr
  have hi_mu : Integrable h mu := hi.mono_measure hrho_mu
  have hgc_mu : Integrable (gc : X → ℝ) mu := hgcint.mono_measure hrho_mu
  have hi_nu : Integrable h nu := hi.mono_measure hrho_nu
  have hgc_nu : Integrable (gc : X → ℝ) nu := hgcint.mono_measure hrho_nu
  have hexp_h : Integrable (fun x => exp (h x)) nu :=
    Integrable.of_bound
      ((Real.continuous_exp.measurable.comp hh).aestronglyMeasurable) (exp M) <|
      .of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (hhM x).2
  have hexp_gc : Integrable (fun x => exp (gc x)) nu :=
    Integrable.of_bound (gc.continuous.rexp.aestronglyMeasurable) (exp M) <|
      .of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (hgcM x).2
  have hlin :
      ‖(∫ x, h x ∂mu) - ∫ x, gc x ∂mu‖ ≤ delta := by
    rw [← integral_sub hi_mu hgc_mu]
    exact (norm_integral_le_integral_norm _).trans herr_mu
  have hexp :
      ‖(∫ x, exp (h x) ∂nu) - ∫ x, exp (gc x) ∂nu‖ ≤ exp M * delta := by
    rw [← integral_sub hexp_h hexp_gc]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpoint : ∀ x, ‖exp (h x) - exp (gc x)‖ ≤
        exp M * ‖h x - gc x‖ :=
      fun x => norm_exp_sub_exp_le (hhM x) (hgcM x)
    calc
      ∫ x, ‖exp (h x) - exp (gc x)‖ ∂nu
          ≤ ∫ x, exp M * ‖h x - gc x‖ ∂nu := by
            apply integral_mono_ae (hexp_h.sub hexp_gc).norm
              ((hdiffint.mono_measure hrho_nu).const_mul (exp M))
            exact .of_forall hpoint
      _ = exp M * ∫ x, ‖h x - gc x‖ ∂nu := by
            rw [integral_const_mul]
      _ ≤ exp M * delta := mul_le_mul_of_nonneg_left herr_nu (Real.exp_nonneg _)
  refine ⟨gc, ?_⟩
  simp only [entropyTest]
  rw [integral_sub (integrable_const 1) hexp_h,
    integral_sub (integrable_const 1) hexp_gc]
  rw [Real.norm_eq_abs, abs_le] at hlin hexp
  dsimp [delta] at hlin hexp ⊢
  have hden : 0 < 1 + exp M := by positivity
  have hsum : eps / (1 + exp M) + exp M * (eps / (1 + exp M)) = eps := by
    field_simp
  linarith

def klSlope (n : ℕ) (r : ℝ) : ℝ :=
  if r = 0 then -(n : ℝ) else clip n (log r)

lemma measurable_klSlope (n : ℕ) : Measurable (klSlope n) := by
  unfold klSlope clip
  apply Measurable.ite
  · exact measurableSet_singleton 0
  · fun_prop
  · fun_prop

lemma klSlope_mem_Icc (n : ℕ) (r : ℝ) :
    klSlope n r ∈ Icc (-(n : ℝ)) n := by
  by_cases hr : r = 0
  · simp [klSlope, hr]
  · simpa [klSlope, hr] using clip_mem_Icc (Nat.cast_nonneg n) (log r)

lemma klSlope_payoff_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ r * klSlope n r + 1 - exp (klSlope n r) := by
  by_cases hr0 : r = 0
  · simp only [klSlope, hr0, if_pos, zero_mul, zero_add]
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n)))
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  by_cases hlo : log r ≤ -(n : ℝ)
  · have hs : klSlope n r = -(n : ℝ) := by
      simp [klSlope, hr0, clip, hlo]
    rw [hs]
    have hre : r ≤ exp (-(n : ℝ)) := by
      rw [← Real.exp_log hrpos]
      exact Real.exp_le_exp.mpr hlo
    have hk := klFun_nonneg (Real.exp_nonneg (-(n : ℝ)))
    rw [klFun, Real.log_exp] at hk
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hre)
      (neg_nonpos.mpr (Nat.cast_nonneg n))]
  · have hlo' : -(n : ℝ) < log r := lt_of_not_ge hlo
    by_cases hhi : (n : ℝ) ≤ log r
    · have hs : klSlope n r = n := by
        simp [klSlope, hr0, clip, hhi]
      rw [hs]
      have hre : exp (n : ℝ) ≤ r := by
        rw [← Real.exp_log hrpos]
        exact Real.exp_le_exp.mpr hhi
      have hk := klFun_nonneg (Real.exp_nonneg (n : ℝ))
      rw [klFun, Real.log_exp] at hk
      nlinarith [mul_nonneg (sub_nonneg.mpr hre) (Nat.cast_nonneg n)]
    · have hhi' : log r < (n : ℝ) := lt_of_not_ge hhi
      have hs : klSlope n r = log r := by
        simp [klSlope, hr0, clip, le_of_lt hlo', le_of_lt hhi']
      rw [hs, Real.exp_log hrpos]
      simpa [klFun] using klFun_nonneg hr

lemma tendsto_klSlope_payoff (r : ℝ) (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ => r * klSlope n r + 1 - exp (klSlope n r))
      atTop (𝓝 (klFun r)) := by
  by_cases hr0 : r = 0
  · subst r
    simp only [klSlope, if_pos, zero_mul, zero_add, klFun_zero]
    simpa using tendsto_const_nhds.sub
      (Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
  have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  obtain ⟨N, hN⟩ := exists_nat_ge |log r|
  have hev : ∀ᶠ n : ℕ in atTop, |log r| ≤ (n : ℝ) :=
    (eventually_ge_atTop N).mono fun n hn => hN.trans (Nat.cast_le.mpr hn)
  apply tendsto_const_nhds.congr'
  filter_upwards [hev] with n hn
  have hs : klSlope n r = log r := by
    apply if_neg hr0 |>.trans
    apply clip_eq_self
    rw [mem_Icc]
    constructor <;> linarith [le_abs_self (log r), neg_le_abs (log r)]
  rw [hs, Real.exp_log hrpos, klFun]

lemma exists_boundedContinuous_entropyTest_gt_of_ac
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X]
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hac : mu ≪ nu) {c : ℝ} (hc : ENNReal.ofReal c < klDiv mu nu) :
    ∃ g : X →ᵇ ℝ, c < entropyTest mu nu g := by
  let r : X → ℝ := fun x => (mu.rnDeriv nu x).toReal
  let h : ℕ → X → ℝ := fun n x => klSlope n (r x)
  let q : ℕ → X → ℝ := fun n x => r x * h n x + 1 - exp (h n x)
  have hr (x : X) : 0 ≤ r x := ENNReal.toReal_nonneg
  have hrmeas : Measurable r := (Measure.measurable_rnDeriv mu nu).ennreal_toReal
  have hh (n : ℕ) : Measurable (h n) := (measurable_klSlope n).comp hrmeas
  have hq (n : ℕ) : Measurable (q n) := by
    dsimp [q]
    fun_prop
  have hqnonneg (n : ℕ) (x : X) : 0 ≤ q n x := klSlope_payoff_nonneg n (hr x)
  have hfatou :
      (∫⁻ x, ENNReal.ofReal (klFun (r x)) ∂nu) ≤
        liminf (fun n => ∫⁻ x, ENNReal.ofReal (q n x) ∂nu) atTop := by
    calc
      (∫⁻ x, ENNReal.ofReal (klFun (r x)) ∂nu) =
          ∫⁻ x, liminf (fun n => ENNReal.ofReal (q n x)) atTop ∂nu := by
            apply lintegral_congr
            intro x
            symm
            exact ((ENNReal.continuous_ofReal.tendsto _).comp
              (tendsto_klSlope_payoff (r x) (hr x))).liminf_eq
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (q n x) ∂nu) atTop :=
        lintegral_liminf_le fun n => (ENNReal.continuous_ofReal.measurable.comp (hq n))
  have hkl :
      klDiv mu nu = ∫⁻ x, ENNReal.ofReal (klFun (r x)) ∂nu := by
    simpa [r] using klDiv_eq_lintegral_klFun_of_ac hac
  have hclim : ENNReal.ofReal c <
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (q n x) ∂nu) atTop :=
    hc.trans_le (hkl.symm ▸ hfatou)
  have hev : ∀ᶠ n in atTop,
      ENNReal.ofReal c < ∫⁻ x, ENNReal.ofReal (q n x) ∂nu :=
    eventually_lt_of_lt_liminf hclim
  obtain ⟨n, hn⟩ := hev.exists
  have hhbound (x : X) : h n x ∈ Icc (-(n : ℝ)) n := klSlope_mem_Icc n (r x)
  have hh_mu : Integrable (h n) mu :=
    Integrable.of_bound (hh n).aestronglyMeasurable n <|
      .of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact (abs_le).2 (hhbound x)
  have hh_nu : Integrable (h n) nu :=
    Integrable.of_bound (hh n).aestronglyMeasurable n <|
      .of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact (abs_le).2 (hhbound x)
  have hexp : Integrable (fun x => exp (h n x)) nu :=
    Integrable.of_bound
      ((Real.continuous_exp.measurable.comp (hh n)).aestronglyMeasurable) (exp n) <|
      .of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (hhbound x).2
  have hrh : Integrable (fun x => r x * h n x) nu := by
    dsimp [r]
    rwa [integrable_toReal_rnDeriv_mul_iff hac]
  have hqint : Integrable (q n) nu := (hrh.add (integrable_const 1)).sub hexp
  have hn' : ENNReal.ofReal c < ENNReal.ofReal (∫ x, q n x ∂nu) := by
    rw [ofReal_integral_eq_lintegral_ofReal hqint (.of_forall (hqnonneg n))]
    exact hn
  have hqpos : 0 < ∫ x, q n x ∂nu := by
    by_contra h
    have : ENNReal.ofReal (∫ x, q n x ∂nu) = 0 := ENNReal.ofReal_eq_zero.mpr (le_of_not_gt h)
    simp [this] at hn'
  have hcq : c < ∫ x, q n x ∂nu :=
    (ENNReal.ofReal_lt_ofReal_iff hqpos).mp hn'
  have htest : entropyTest mu nu (h n) = ∫ x, q n x ∂nu := by
    rw [entropyTest, integral_sub (integrable_const 1) hexp]
    have hrh_eq := integral_toReal_rnDeriv_mul hac (f := h n)
    rw [← hrh_eq]
    have hadd :
        (∫ x, r x * h n x + 1 ∂nu) =
          (∫ x, r x * h n x ∂nu) + ∫ _x, (1 : ℝ) ∂nu := by
      convert integral_add hrh (integrable_const 1)
    have hsub :
        (∫ x, (r x * h n x + 1) - exp (h n x) ∂nu) =
          (∫ x, r x * h n x + 1 ∂nu) - ∫ x, exp (h n x) ∂nu := by
      convert integral_sub (hrh.add (integrable_const 1)) hexp <;>
        simp only [Pi.add_apply]
    rw [show (∫ x, q n x ∂nu) =
        (∫ x, r x * h n x ∂nu) + (∫ _x, (1 : ℝ) ∂nu) -
          ∫ x, exp (h n x) ∂nu by
      rw [← hadd, ← hsub]
      ]
    linarith
  let eps := (entropyTest mu nu (h n) - c) / 2
  have heps : 0 < eps := by
    change 0 < (entropyTest mu nu (h n) - c) / 2
    rw [htest]
    linarith
  obtain ⟨g, hg⟩ := exists_boundedContinuous_entropyTest_ge mu nu (hh n)
    (Nat.cast_nonneg n) hhbound heps
  refine ⟨g, ?_⟩
  dsimp [eps] at hg
  linarith

lemma exists_boundedContinuous_entropyTest_gt_of_not_ac
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X]
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hac : ¬ mu ≪ nu) (c : ℝ) :
    ∃ g : X →ᵇ ℝ, c < entropyTest mu nu g := by
  simp only [Measure.AbsolutelyContinuous] at hac
  push Not at hac
  obtain ⟨s, hnus, hmus⟩ := hac
  obtain ⟨t, hst, ht, hmut, hnut⟩ := exists_measurable_superset₂ mu nu s
  have hnut0 : nu t = 0 := hnut.trans hnus
  have hmut0 : mu t ≠ 0 := by
    intro h
    apply hmus
    exact measure_mono_null hst h
  have hmutpos : 0 < (mu t).toReal :=
    ENNReal.toReal_pos hmut0 (measure_ne_top mu t)
  let A := (max c 0 + 1) / (mu t).toReal
  have hA : 0 < A := div_pos (by positivity) hmutpos
  let h : X → ℝ := t.indicator fun _ => A
  have hh : Measurable h := measurable_const.indicator ht
  have hhbound (x : X) : h x ∈ Icc (-A) A := by
    by_cases hx : x ∈ t <;> simp [h, hx, hA.le]
  have hh_mu : Integrable h mu :=
    Integrable.of_bound hh.aestronglyMeasurable A <|
      .of_forall fun x => by
        rw [Real.norm_eq_abs]
        exact (abs_le).2 (hhbound x)
  have hzero : h =ᵐ[nu] 0 := by
    have haunt : ∀ᵐ x ∂nu, x ∉ t := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using hnut0
    filter_upwards [haunt] with x hx
    simp [h, hx]
  have hexpzero : (fun x => exp (h x)) =ᵐ[nu] 1 := hzero.fun_comp exp |>.trans <| by simp
  have hfirst : ∫ x, h x ∂mu = A * (mu t).toReal := by
    dsimp [h]
    rw [integral_indicator ht]
    simp [measureReal_def, mul_comm]
  have hsecond : ∫ x, (1 - exp (h x)) ∂nu = 0 := by
    have hz : (fun x => 1 - exp (h x)) =ᵐ[nu] 0 := by
      filter_upwards [hexpzero] with x hx
      rw [hx]
      simp
    calc
      (∫ x, (1 - exp (h x)) ∂nu) = ∫ _x, (0 : ℝ) ∂nu := integral_congr_ae hz
      _ = 0 := by simp
  have htest : entropyTest mu nu h = max c 0 + 1 := by
    rw [entropyTest, hfirst, hsecond, add_zero]
    dsimp [A]
    field_simp
  let eps := (max c 0 + 1 - c) / 2
  have heps : 0 < eps := by
    dsimp [eps]
    have := le_max_left c 0
    linarith
  obtain ⟨g, hg⟩ := exists_boundedContinuous_entropyTest_ge mu nu hh hA.le hhbound heps
  refine ⟨g, ?_⟩
  rw [htest] at hg
  dsimp [eps] at hg
  have := le_max_left c 0
  linarith

lemma exists_boundedContinuous_entropyTest_gt
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X]
    (mu nu : Measure X) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    {c : ℝ} (hc : ENNReal.ofReal c < klDiv mu nu) :
    ∃ g : X →ᵇ ℝ, c < entropyTest mu nu g := by
  by_cases hac : mu ≪ nu
  · exact exists_boundedContinuous_entropyTest_gt_of_ac mu nu hac hc
  · exact exists_boundedContinuous_entropyTest_gt_of_not_ac mu nu hac c

theorem lowerSemicontinuous_klDiv
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] [BorelSpace X]
    (nu : FiniteMeasure X) :
    LowerSemicontinuous
      (fun mu : FiniteMeasure X => klDiv (mu : Measure X) (nu : Measure X)) := by
  rw [lowerSemicontinuous_iff]
  intro mu
  rw [lowerSemicontinuousAt_iff]
  intro y hy
  have hyne : y ≠ ∞ := ne_top_of_lt hy
  have hyrepr : ENNReal.ofReal y.toReal = y := ENNReal.ofReal_toReal hyne
  obtain ⟨g, hg⟩ := exists_boundedContinuous_entropyTest_gt
    (mu : Measure X) (nu : Measure X) (c := y.toReal) (by simpa [hyrepr] using hy)
  have htestpos : 0 < entropyTest (mu : Measure X) (nu : Measure X) g :=
    (ENNReal.toReal_nonneg.trans_lt hg)
  have hytest : y <
      ENNReal.ofReal (entropyTest (mu : Measure X) (nu : Measure X) g) := by
    rw [← hyrepr]
    exact (ENNReal.ofReal_lt_ofReal_iff htestpos).2 hg
  have hev : ∀ᶠ mu' : FiniteMeasure X in 𝓝 mu,
      y < ENNReal.ofReal (entropyTest (mu' : Measure X) (nu : Measure X) g) :=
    ((continuous_ofReal_entropyTest (nu : Measure X) g).tendsto mu).eventually
      (Ioi_mem_nhds hytest)
  filter_upwards [hev] with mu' hmu'
  refine hmu'.trans_le (entropyTest_le_klDiv (mu' : Measure X) (nu : Measure X) g
    (BoundedContinuousFunction.integrable _ g) ?_)
  let eg : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => exp (g x)) g.continuous.rexp (exp ‖g‖) fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact (le_abs_self (g x)).trans (by
        simpa [Real.norm_eq_abs] using g.norm_coe_le_norm x)
  exact BoundedContinuousFunction.integrable (nu : Measure X) eg

theorem isCompact_fixedMass_klDiv_sublevel
    [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    [T2Space X] [BorelSpace X] [CompactSpace X]
    (nu : FiniteMeasure X) (mass : ℝ≥0) (C : ℝ≥0∞) :
    IsCompact {mu : FiniteMeasure X |
      mu.mass = mass ∧ klDiv (mu : Measure X) (nu : Measure X) ≤ C} := by
  have hm := isCompact_setOfPred_finiteMeasure_eq_of_compactSpace X mass
  have hkl : IsClosed {mu : FiniteMeasure X |
      klDiv (mu : Measure X) (nu : Measure X) ≤ C} := by
    change IsClosed ((fun mu : FiniteMeasure X =>
      klDiv (mu : Measure X) (nu : Measure X)) ⁻¹' Iic C)
    exact (lowerSemicontinuous_klDiv nu).isClosed_preimage C
  have hi := hm.inter_right hkl
  convert hi using 1
  ext mu
  simp

end

end InformationTheory

namespace StateDepMOR.PoissonSamplePath

open InformationTheory

noncomputable section

theorem klDiv_lowerSemicontinuous (T : ℝ) (nu : FiniteMeasure (Horizon T)) :
    LowerSemicontinuous
      (fun mu : FiniteMeasure (Horizon T) =>
        klDiv (mu : Measure (Horizon T)) (nu : Measure (Horizon T))) :=
  InformationTheory.lowerSemicontinuous_klDiv nu

theorem isCompact_fixedMass_klDiv_sublevel
    (T : ℝ) (nu : FiniteMeasure (Horizon T)) (mass : ℝ≥0) (C : ℝ≥0∞) :
    IsCompact {mu : FiniteMeasure (Horizon T) |
      mu.mass = mass ∧
        klDiv (mu : Measure (Horizon T)) (nu : Measure (Horizon T)) ≤ C} :=
  InformationTheory.isCompact_fixedMass_klDiv_sublevel nu mass C

end

end StateDepMOR.PoissonSamplePath


open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set

namespace InformationTheory

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [TopologicalSpace.PseudoMetrizableSpace X] [T2Space X] [BorelSpace X]
  [CompactSpace X]

/-- KL sublevels of finite measures on a compact space are compact even
when the total mass is not fixed. -/
theorem isCompact_klDiv_sublevel
    (nu : FiniteMeasure X) (C : ENNReal)
    (hC : Ne C (⊤ : ENNReal)) :
    IsCompact {mu : FiniteMeasure X |
      klDiv (mu : Measure X) (nu : Measure X) <= C} := by
  let B : Real :=
    C.toReal + nu.mass + nu.mass * (Real.exp 1 - 1)
  let M : NNReal := Real.toNNReal B
  have hB : 0 <= B := by
    dsimp [B]
    have hexp : 1 <= Real.exp 1 := Real.one_le_exp (by norm_num)
    positivity
  have hsubset :
      {mu : FiniteMeasure X |
        klDiv (mu : Measure X) (nu : Measure X) <= C} <=
      {mu : FiniteMeasure X | mu.mass <= M} := by
    intro mu hmu
    have htest :=
      entropyTest_le_klDiv (mu : Measure X) (nu : Measure X)
        (fun _ => (1 : Real)) (integrable_const 1)
        (by simpa using (integrable_const (Real.exp 1) :
          Integrable (fun _ : X => Real.exp 1) (nu : Measure X)))
    have htestC :
        ENNReal.ofReal
            (entropyTest (mu : Measure X) (nu : Measure X)
              (fun _ => (1 : Real))) <= C :=
      htest.trans hmu
    have hreal :
        entropyTest (mu : Measure X) (nu : Measure X)
            (fun _ => (1 : Real)) <= C.toReal := by
      exact (ENNReal.ofReal_le_iff_le_toReal hC).mp htestC
    have hmass :
        (mu.mass : Real) <= B := by
      simp only [entropyTest, integral_const, smul_eq_mul, mul_one] at hreal
      change (mu.mass : Real) + (nu.mass : Real) * (1 - Real.exp 1) <=
        C.toReal at hreal
      dsimp [B]
      nlinarith
    change (mu.mass : Real) <= (M : Real)
    rw [Real.coe_toNNReal B hB]
    exact hmass
  have hclosed :
      IsClosed {mu : FiniteMeasure X |
        klDiv (mu : Measure X) (nu : Measure X) <= C} := by
    change IsClosed ((fun mu : FiniteMeasure X =>
      klDiv (mu : Measure X) (nu : Measure X)) ⁻¹' Iic C)
    exact (lowerSemicontinuous_klDiv nu).isClosed_preimage C
  exact
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace X M).of_isClosed_subset
      hclosed hsubset

end

end InformationTheory

namespace StateDepMOR.PoissonSamplePath

noncomputable section

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

theorem rate_ne_top_of_mem_sublevel
    (N : Network Buffer Server) (T c : Real)
    {x : Path (Buffer := Buffer) (Server := Server) T}
    (hx : poissonPathRate N T (asMatrix T x) <= ENNReal.ofReal c) :
    Ne (poissonPathRate N T (asMatrix T x)) (⊤ : ENNReal) :=
  ne_of_lt (hx.trans_lt ENNReal.ofReal_lt_top)

theorem sublevel_zeroRate_coordinate
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    {x : Path (Buffer := Buffer) (Server := Server) T}
    (hx : poissonPathRate N T (asMatrix T x) <= ENNReal.ofReal c)
    (j : Server) (k : Buffer) (hphi : N.phi j k = 0) :
    forall t : Horizon T, x t j k = 0 := by
  intro t
  have hzero :=
    poissonPathRate_ne_top_implies_zeroRate_path
      N hT.le (asMatrix T x) (rate_ne_top_of_mem_sublevel N T c hx)
      j k hphi (t : Real) t.property
  simpa [asMatrix_apply_of_mem hT.le t.property x] using hzero

/-- Finite-action coordinates are continuous on the horizon. -/
theorem sublevel_coordinate_continuous
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    {x : Path (Buffer := Buffer) (Server := Server) T}
    (hx : poissonPathRate N T (asMatrix T x) <= ENNReal.ofReal c)
    (j : Server) (k : Buffer) :
    Continuous (fun t : Horizon T => x t j k) := by
  have hcont :
      ContinuousOn (fun t : Real => asMatrix T x t j k) (Icc 0 T) :=
    finiteCostPath_continuousOn N hT.le (asMatrix T x)
      (hx.trans_lt ENNReal.ofReal_lt_top) j k
  convert hcont.domRestrict using 1
  funext t
  change x t j k = asMatrix T x (t : Real) j k
  rw [asMatrix_apply_of_mem hT.le t.property x]

abbrev ContinuousMatrixPath (T : Real) :=
  BoundedContinuousFunction (Horizon T) (FiniteMatrix Server Buffer)

/-- Continuous nonnegative paths, used as the Arzela-Ascoli model of every
finite Poisson-action path. -/
abbrev ContinuousNonnegativePath (T : Real) :=
  {f : ContinuousMatrixPath (Buffer := Buffer) (Server := Server) T //
    forall t j k, 0 <= f t j k}

/-- Forget continuity while retaining the repository's bundled path type. -/
def continuousNonnegativeToPath {T : Real}
    (f : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T) :
    Path (Buffer := Buffer) (Server := Server) T where
  toFun := f.1
  nonnegative := f.2
  rightContinuous := by
    intro t ht
    exact f.1.continuous.continuousAt.continuousWithinAt
  leftLimits := by
    intro t ht
    exact ⟨f.1 t, f.1.continuous.continuousAt.continuousWithinAt⟩

@[simp]
theorem continuousNonnegativeToPath_apply {T : Real}
    (f : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (t : Horizon T) :
    continuousNonnegativeToPath f t = f.1 t :=
  rfl

/-- Uniform convergence of continuous paths implies J1 convergence. -/
theorem j1EDist_continuousNonnegativeToPath_le {T : Real}
    (f g : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T) :
    j1EDist (continuousNonnegativeToPath f)
        (continuousNonnegativeToPath g) <=
      ENNReal.ofReal (dist f g) := by
  refine (inf_le_left : symmetricJ1EDist
      (continuousNonnegativeToPath f) (continuousNonnegativeToPath g) ⊓ 1 <=
        symmetricJ1EDist
          (continuousNonnegativeToPath f) (continuousNonnegativeToPath g)).trans ?_
  refine symmetricJ1EDist_le_j1Cost
    (continuousNonnegativeToPath f) (continuousNonnegativeToPath g)
    (identityTimeChange T) |>.trans ?_
  apply max_le
  · simp [timeError, identityTimeChange]
  · unfold pathError
    apply iSup_le
    intro t
    apply iSup_le
    intro j
    apply iSup_le
    intro k
    apply ENNReal.ofReal_le_ofReal
    calc
      |continuousNonnegativeToPath f
          (identityTimeChange T t) j k -
        continuousNonnegativeToPath g t j k| =
          dist (f.1 t j k) (g.1 t j k) := by
            simp [identityTimeChange, Real.dist_eq]
      _ <= dist (f.1 t) (g.1 t) := by
        have hj :=
          (dist_pi_le_iff dist_nonneg).mp
            (le_rfl : dist (f.1 t) (g.1 t) <= dist (f.1 t) (g.1 t)) j
        exact (dist_pi_le_iff dist_nonneg).mp hj k
      _ <= dist f.1 g.1 :=
        BoundedContinuousFunction.dist_coe_le_dist t
      _ = dist f g := rfl

theorem continuous_continuousNonnegativeToPath {T : Real} :
    Continuous
      (continuousNonnegativeToPath
        (Buffer := Buffer) (Server := Server) (T := T)) := by
  apply LipschitzWith.continuous (K := 1)
  intro f g
  change j1EDist (continuousNonnegativeToPath f)
      (continuousNonnegativeToPath g) <=
    (1 : ENNReal) * edist f g
  rw [one_mul, edist_dist]
  exact j1EDist_continuousNonnegativeToPath_le f g

def continuousRateSublevel
    (N : Network Buffer Server) (T c : Real) :
    Set (ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T) :=
  {f | poissonPathRate N T
      (asMatrix T (continuousNonnegativeToPath f)) <= ENNReal.ofReal c}

/-- Bundle a finite-action repository path as a bounded continuous path. -/
noncomputable def sublevelToContinuous
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hx : poissonPathRate N T (asMatrix T x) <= ENNReal.ofReal c) :
    ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T := by
  letI : CompactSpace (Horizon T) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let f : ContinuousMap (Horizon T) (FiniteMatrix Server Buffer) :=
    ⟨x.toFun, by
      apply continuous_pi
      intro j
      apply continuous_pi
      intro k
      exact sublevel_coordinate_continuous N hT hx j k⟩
  exact
    ⟨BoundedContinuousFunction.mkOfCompact f, x.nonnegative⟩

@[simp]
theorem continuousNonnegativeToPath_sublevelToContinuous
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hx : poissonPathRate N T (asMatrix T x) <= ENNReal.ofReal c) :
    continuousNonnegativeToPath (sublevelToContinuous N hT x hx) = x := by
  apply Path.ext
  rfl

theorem poissonSublevel_eq_continuous_image
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T) :
    {x : Path (Buffer := Buffer) (Server := Server) T |
      poissonPathRate N T (asMatrix T x) <= ENNReal.ofReal c} =
      continuousNonnegativeToPath ''
        continuousRateSublevel N T c := by
  ext x
  constructor
  · intro hx
    let f := sublevelToContinuous N hT x hx
    refine ⟨f, ?_, ?_⟩
    · change poissonPathRate N T
        (asMatrix T (continuousNonnegativeToPath f)) <= ENNReal.ofReal c
      rw [continuousNonnegativeToPath_sublevelToContinuous N hT x hx]
      exact hx
    · exact continuousNonnegativeToPath_sublevelToContinuous N hT x hx
  · rintro ⟨f, hf, rfl⟩
    exact hf

/-- Moving uniform-cell averages converge almost everywhere to the path
derivative. -/
theorem uniformCellChord_tendsto_ae_goodness
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      Tendsto (fun n => uniformCellChord T hT A n t) atTop
        (𝓝 (pathDerivative A t)) := by
  classical
  let f : Real -> (Server -> Buffer -> Real) :=
    (Icc (0 : Real) T).indicator (pathDerivative A)
  have hmatrix_int :
      IntegrableOn (pathDerivative A) (Icc 0 T) volume :=
    finiteAction_derivative_integrableOn_matrix N hT.le A hfinite
  have hf_int : Integrable f volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hmatrix_int
  have hldt :=
    IsUnifLocDoublingMeasure.ae_tendsto_average volume
      hf_int.locallyIntegrable 1
  have hae_zero : ∀ᵐ t : Real ∂volume, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hae_T : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hldt, hae_zero, hae_T] with t hx ht_ne_zero ht_ne_T
  intro ht
  have ht0 : 0 <= t := ht.1
  have htT : t < T := ht.2.lt_of_ne ht_ne_T
  have ht_mem_f : t ∈ Icc (0 : Real) T := ⟨ht0, htT.le⟩
  have hmem :
      ∀ᶠ n in atTop,
        t ∈ Metric.closedBall (uniformCellCenter T hT n t)
          (1 * uniformCellRadius T n) := by
    filter_upwards with n
    rw [one_mul, closedBall_uniformCellCenter hT n ht0 htT]
    have hcell := UniformPartition.mem_uniform_cell hT n ht0 htT
    exact ⟨hcell.1, hcell.2.le⟩
  have havg :=
    hx (uniformCellCenter T hT · t) (uniformCellRadius T)
      (tendsto_uniformCellRadius hT) hmem
  have havg' :
      Tendsto
        (fun n => uniformCellChord T hT A n t) atTop
        (𝓝 (f t)) := by
    refine Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n => ?_) havg
    exact setAverage_restrictedDerivative_eq_uniformCellChord
      N hT A hfinite n ht0 htT
  simpa [f, ht_mem_f] using havg'

/-- The local Poisson rate of the uniform chord converges almost everywhere
to the derivative rate.  Zero nominal rates are handled by exact vanishing,
not by extending the positive-rate continuity argument to the boundary. -/
theorem localRate_uniformCellChord_tendsto_ae_goodness
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      Tendsto
        (fun n => N.localRate (uniformCellChord T hT A n t))
        atTop (𝓝 (N.localRate (pathDerivative A t))) := by
  classical
  have hnonneg_all :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        ∀ j k, 0 <= pathDerivative A t j k := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    exact finiteAction_derivative_nonneg_ae N T A hfinite j k
  have hzero_all :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        ∀ j k, N.phi j k = 0 -> pathDerivative A t j k = 0 := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    by_cases hphi : N.phi j k = 0
    · exact (finiteAction_zeroDerivative_ae N T A hfinite j k hphi).mono
        fun _ ht _ => ht
    · exact Filter.Eventually.of_forall fun _ ht => (hphi ht).elim
  have hae_T : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  have hinterior :
      ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 <= t ∧ t < T :=
    (ae_restrict_iff' measurableSet_Icc).mpr <| by
      filter_upwards [hae_T] with t ht_ne
      intro ht
      exact ⟨ht.1, ht.2.lt_of_ne ht_ne⟩
  filter_upwards
    [uniformCellChord_tendsto_ae_goodness N hT A hfinite,
      hnonneg_all, hzero_all, hinterior]
      with t hchord hderiv_nonneg hderiv_zero ht
  unfold Network.localRate
  apply tendsto_finsetSum Finset.univ
  intro j hj
  apply tendsto_finsetSum Finset.univ
  intro k hk
  rcases (N.phi_nonneg j k).eq_or_lt with hphi | hphi
  · have hphi0 : N.phi j k = 0 := hphi.symm
    have hlimit0 := hderiv_zero j k hphi0
    have hseq0 (n : Nat) :
        uniformCellChord T hT A n t j k = 0 := by
      simp only [uniformCellChord, ht, dite_true]
      exact partitionChord_eq_zero_of_phi_eq_zero N hT.le A hfinite
        (uniformActionPartition T hT n)
        ⟨UniformPartition.cellIndex T n t,
          UniformPartition.cellIndex_lt hT n ht.1 ht.2⟩
        j k hphi0
    simp [hphi0, hlimit0, hseq0]
  · have hscalar :
        Tendsto (fun n => uniformCellChord T hT A n t j k)
          atTop (𝓝 (pathDerivative A t j k)) :=
      (hchord.apply_nhds j).apply_nhds k
    have hpositive :
        Tendsto
          (fun n => positivePoissonCostReal (N.phi j k)
            (uniformCellChord T hT A n t j k))
          atTop
          (𝓝 (positivePoissonCostReal (N.phi j k)
            (pathDerivative A t j k))) :=
      Filter.Tendsto.comp
        ((continuous_positivePoissonCostReal (N.phi j k)).tendsto
          (pathDerivative A t j k))
        hscalar
    have hofReal :
        Tendsto
          (fun n => ENNReal.ofReal
            (positivePoissonCostReal (N.phi j k)
              (uniformCellChord T hT A n t j k)))
          atTop
          (𝓝 (ENNReal.ofReal
            (positivePoissonCostReal (N.phi j k)
              (pathDerivative A t j k)))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hpositive
    have hlimit_nonneg := hderiv_nonneg j k
    have hcostseq :
        (fun n => poissonCost (N.phi j k)
          (uniformCellChord T hT A n t j k)) =
        (fun n => ENNReal.ofReal
          (positivePoissonCostReal (N.phi j k)
            (uniformCellChord T hT A n t j k))) := by
      funext n
      have hseq_nonneg :=
        partitionChord_nonneg N hT.le A hfinite
          (uniformActionPartition T hT n)
          ⟨UniformPartition.cellIndex T n t,
            UniformPartition.cellIndex_lt hT n ht.1 ht.2⟩
          j k
      have hcell_eq :
          uniformCellChord T hT A n t j k =
            partitionChord A (uniformActionPartition T hT n)
              ⟨UniformPartition.cellIndex T n t,
                UniformPartition.cellIndex_lt hT n ht.1 ht.2⟩ j k := by
        simp [uniformCellChord, ht]
      have hseq_nonneg' :
          0 <= uniformCellChord T hT A n t j k := by
        rw [hcell_eq]
        exact hseq_nonneg
      rw [poissonCost_of_nominal_pos hphi hseq_nonneg']
      congr 1
      exact (positivePoissonCostReal_eq hphi hseq_nonneg').symm
    have hcostlimit :
        poissonCost (N.phi j k) (pathDerivative A t j k) =
          ENNReal.ofReal
            (positivePoissonCostReal (N.phi j k)
              (pathDerivative A t j k)) := by
      rw [poissonCost_of_nominal_pos hphi hlimit_nonneg]
      congr 1
      exact (positivePoissonCostReal_eq hphi hlimit_nonneg).symm
    rw [hcostseq, hcostlimit]
    exact hofReal

/-- Uniform chord actions recover the full action from below.  The
zero-nominal coordinates are covered by
`localRate_uniformCellChord_tendsto_ae`, where every chord is exactly zero. -/
theorem poissonPathRate_le_liminf_uniformPartitionAction
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal)) :
    poissonPathRate N T A <=
      liminf
        (fun n =>
          poissonPartitionAction N A (uniformActionPartition T hT n))
        atTop := by
  classical
  let F : Nat -> Real -> ENNReal :=
    fun n t =>
      partitionStepCost N A (uniformActionPartition T hT n) t
  have hvalid :=
    poissonPathRate_ne_top_implies_valid N T A hfinite
  have hae_T : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  have hinterior :
      ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 <= t ∧ t < T :=
    (ae_restrict_iff' measurableSet_Icc).mpr <| by
      filter_upwards [hae_T] with t ht_ne
      intro ht
      exact ⟨ht.1, ht.2.lt_of_ne ht_ne⟩
  have hconv :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        Tendsto (fun n => F n t) atTop
          (𝓝 (N.localRate (pathDerivative A t))) := by
    filter_upwards
      [localRate_uniformCellChord_tendsto_ae_goodness N hT A hfinite,
        hinterior] with t htend ht
    apply Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n => ?_) htend
    exact (partitionStepCost_uniform_eq N T hT A n ht.1 ht.2).symm
  rw [poissonPathRate, if_pos hvalid]
  calc
    (∫⁻ t in Icc 0 T, N.localRate (pathDerivative A t)) =
        ∫⁻ t in Icc 0 T, liminf (fun n => F n t) atTop := by
          apply lintegral_congr_ae
          exact hconv.mono fun t ht => ht.liminf_eq.symm
    _ <= liminf
        (fun n => ∫⁻ t in Icc 0 T, F n t) atTop :=
      lintegral_liminf_le' fun n => by
        simpa [F] using
          (measurable_partitionStepCost N A
            (uniformActionPartition T hT n)).aemeasurable
    _ = liminf
        (fun n =>
          poissonPartitionAction N A (uniformActionPartition T hT n))
        atTop := by
          congr 1
          funext n
          exact lintegral_partitionStepCost_Icc N A hT.le
            (uniformActionPartition T hT n)

/-- Real Fenchel bound for the positive-rate Poisson cost. -/
theorem positivePoissonCostReal_fenchel
    {nominal candidate theta : Real}
    (hnominal : 0 < nominal) (hcandidate : 0 <= candidate) :
    theta * candidate - nominal * (Real.exp theta - 1) <=
      positivePoissonCostReal nominal candidate := by
  rw [positivePoissonCostReal_eq hnominal hcandidate]
  rcases hcandidate.eq_or_lt with rfl | hcandidate
  · simp only [mul_zero, zero_div, Real.log_zero, zero_mul]
    have hexp : 0 < Real.exp theta := Real.exp_pos theta
    dsimp [poissonCostReal]
    nlinarith
  · have hratio : 0 < candidate / nominal :=
      div_pos hcandidate hnominal
    have hexpBound :=
      Real.add_one_le_exp (theta - Real.log (candidate / nominal))
    have hexpLog :
        Real.exp (theta - Real.log (candidate / nominal)) =
          Real.exp theta * nominal / candidate := by
      rw [Real.exp_sub, Real.exp_log hratio]
      field_simp
    rw [hexpLog] at hexpBound
    have hscaled :=
      mul_le_mul_of_nonneg_left hexpBound hcandidate.le
    have hcancel :
        candidate * (Real.exp theta * nominal / candidate) =
          nominal * Real.exp theta := by
      field_simp
    rw [hcancel] at hscaled
    dsimp [poissonCostReal]
    nlinarith

/-- Entropy controls a coordinate derivative on every measurable subset of
the horizon. -/
theorem coordinate_setIntegral_derivative_bound
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hsublevel : poissonPathRate N T A <= ENNReal.ofReal c)
    (j : Server) (k : Buffer) (hphi : 0 < N.phi j k)
    (theta : Real) (htheta : 0 < theta)
    {s : Set Real} (hs : MeasurableSet s) (hsubset : s ⊆ Icc 0 T) :
    theta * ∫ t in s, pathDerivative A t j k <=
      max c 0 +
        N.phi j k * (Real.exp theta - 1) * volume.real s := by
  classical
  have hfinite :
      poissonPathRate N T A ≠ (⊤ : ENNReal) :=
    ne_of_lt (hsublevel.trans_lt ENNReal.ofReal_lt_top)
  let g : Real -> Real :=
    fun t => (N.localRate (pathDerivative A t)).toReal
  let K : Real := N.phi j k * (Real.exp theta - 1)
  have hg_int : IntegrableOn g (Icc 0 T) volume := by
    simpa [g] using
      finiteAction_localRate_toReal_integrableOn N T A hfinite
  have hd_int :
      IntegrableOn (fun t => pathDerivative A t j k) (Icc 0 T) volume :=
    finiteAction_derivative_integrableOn N hT.le A hfinite j k
  have hs_ne_top : volume s ≠ (⊤ : ENNReal) :=
    ne_top_of_le_ne_top
      (measure_Icc_lt_top : volume (Icc (0 : Real) T) < (⊤ : ENNReal)).ne
      (measure_mono hsubset)
  have hlocal_lt :=
    finiteAction_localRate_lt_top_ae N T A hfinite
  have hderiv_nonneg :=
    finiteAction_derivative_nonneg_ae N T A hfinite j k
  have hpoint :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        theta * pathDerivative A t j k <= g t + K := by
    filter_upwards [hlocal_lt, hderiv_nonneg] with t hlt hnonneg
    have hcost_le :=
      poissonCost_le_localRate N (pathDerivative A t) j k
    have hcost_real :
        positivePoissonCostReal (N.phi j k)
            (pathDerivative A t j k) <= g t := by
      rw [positivePoissonCostReal_eq hphi hnonneg]
      have hcost_nonneg :=
        poissonCostReal_nonneg hphi hnonneg
      change poissonCostReal (N.phi j k)
          (pathDerivative A t j k) <=
        (N.localRate (pathDerivative A t)).toReal
      rw [← ENNReal.toReal_ofReal hcost_nonneg]
      rw [show ENNReal.ofReal
          (poissonCostReal (N.phi j k) (pathDerivative A t j k)) =
          poissonCost (N.phi j k) (pathDerivative A t j k) by
        rw [poissonCost_of_nominal_pos hphi hnonneg]
        rfl]
      exact ENNReal.toReal_mono hlt.ne hcost_le
    have hfenchel :=
      positivePoissonCostReal_fenchel hphi hnonneg
        (theta := theta)
    dsimp [K]
    linarith
  have hpoint_s :
      ∀ᵐ t ∂volume.restrict s,
        theta * pathDerivative A t j k <= g t + K := by
    apply (ae_restrict_iff' hs).mpr
    have hambient :=
      (ae_restrict_iff' measurableSet_Icc).mp hpoint
    filter_upwards [hambient] with t ht
    intro hts
    exact ht (hsubset hts)
  have hint :
      ∫ t in s, theta * pathDerivative A t j k <=
        ∫ t in s, (g t + K) := by
    apply integral_mono_ae
    · exact (hd_int.mono_set hsubset).const_mul theta
    · exact (hg_int.mono_set hsubset).add
        (integrableOn_const (C := K) hs_ne_top)
    · exact hpoint_s
  have hg_nonneg :
      ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 <= g t :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hg_set_le :
      (∫ t in s, g t) <= ∫ t in Icc 0 T, g t :=
    setIntegral_mono_set hg_int hg_nonneg
      (Filter.Eventually.of_forall fun _ ht => hsubset ht)
  have hglobal :
      (∫ t in Icc 0 T, g t) =
        (poissonPathRate N T A).toReal := by
    have hvalid :=
      poissonPathRate_ne_top_implies_valid N T A hfinite
    have hlt :
        ∀ᵐ t ∂volume.restrict (Icc 0 T),
          N.localRate (pathDerivative A t) < (⊤ : ENNReal) :=
      hlocal_lt
    rw [integral_toReal
      (measurable_localRate_general N A).aemeasurable hlt]
    rw [poissonPathRate, if_pos hvalid]
  have hrate :
      (poissonPathRate N T A).toReal <= max c 0 := by
    have hreal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hsublevel
    rwa [ENNReal.toReal_ofReal'] at hreal
  calc
    theta * ∫ t in s, pathDerivative A t j k =
        ∫ t in s, theta * pathDerivative A t j k := by
          rw [integral_const_mul]
    _ <= ∫ t in s, (g t + K) := hint
    _ = (∫ t in s, g t) + K * volume.real s := by
          rw [integral_add (hg_int.mono_set hsubset)
            (integrableOn_const (C := K) hs_ne_top), setIntegral_const]
          simp [smul_eq_mul, mul_comm]
    _ <= max c 0 + K * volume.real s := by
          gcongr
          exact hg_set_le.trans_eq hglobal |>.trans hrate
    _ = max c 0 +
        N.phi j k * (Real.exp theta - 1) * volume.real s := rfl

/-- The set integral of a finite-action derivative over an unordered
interval is the endpoint distance. -/
theorem coordinate_dist_eq_setIntegral_derivative
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hsublevel : poissonPathRate N T A <= ENNReal.ofReal c)
    (j : Server) (k : Buffer) {a b : Real}
    (ha : a ∈ Icc (0 : Real) T) (hb : b ∈ Icc (0 : Real) T) :
    dist (A a j k) (A b j k) =
      ∫ t in uIoc a b, pathDerivative A t j k := by
  have hfinite :
      poissonPathRate N T A ≠ (⊤ : ENNReal) :=
    ne_of_lt (hsublevel.trans_lt ENNReal.ofReal_lt_top)
  let q : Real -> Real := fun t => A t j k
  have hac :
      AbsolutelyContinuousOnInterval q 0 T :=
    (poissonPathRate_ne_top_implies_valid N T A hfinite).1 j k
  have huIcc : uIcc a b ⊆ Icc (0 : Real) T :=
    uIcc_subset_Icc ha hb
  have hacab : AbsolutelyContinuousOnInterval q a b := by
    apply hac.mono
    simpa [uIcc_of_le hT.le] using huIcc
  have hderiv_nonneg :=
    finiteAction_derivative_nonneg_ae N T A hfinite j k
  have hnonneg_uIoc :
      ∀ᵐ t ∂volume.restrict (uIoc a b),
        0 <= pathDerivative A t j k := by
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    have hambient :=
      (ae_restrict_iff' measurableSet_Icc).mp hderiv_nonneg
    filter_upwards [hambient] with t ht
    intro htab
    exact ht (huIcc (uIoc_subset_uIcc htab))
  have hintegral_nonneg :
      0 <= ∫ t in uIoc a b, pathDerivative A t j k :=
    integral_nonneg_of_ae hnonneg_uIoc
  have heq :
      (∫ t in a..b, pathDerivative A t j k) =
        A b j k - A a j k := by
    simpa [q, pathDerivative] using hacab.integral_deriv_eq_sub
  calc
    dist (A a j k) (A b j k) =
        |A b j k - A a j k| := by
          rw [Real.dist_eq, abs_sub_comm]
    _ = |∫ t in a..b, pathDerivative A t j k| := by rw [heq]
    _ = |∫ t in uIoc a b, pathDerivative A t j k| :=
      intervalIntegral.abs_integral_eq_abs_integral_uIoc _
    _ = ∫ t in uIoc a b, pathDerivative A t j k :=
      abs_of_nonneg hintegral_nonneg

/-- Quantitative entropy modulus for every positive-rate coordinate. -/
theorem sublevel_coordinate_dist_bound
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hsublevel : poissonPathRate N T A <= ENNReal.ofReal c)
    (j : Server) (k : Buffer) (hphi : 0 < N.phi j k)
    (theta : Real) (htheta : 0 < theta)
    {a b : Real}
    (ha : a ∈ Icc (0 : Real) T) (hb : b ∈ Icc (0 : Real) T) :
    theta * dist (A a j k) (A b j k) <=
      max c 0 +
        N.phi j k * (Real.exp theta - 1) * dist a b := by
  have hsubset : uIoc a b ⊆ Icc (0 : Real) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)
  have hbound :=
    coordinate_setIntegral_derivative_bound N hT A hsublevel
      j k hphi theta htheta measurableSet_uIoc hsubset
  rw [← coordinate_dist_eq_setIntegral_derivative
    N hT A hsublevel j k ha hb] at hbound
  simpa [measureReal_def, Real.volume_uIoc, Real.dist_eq,
    ENNReal.toReal_ofReal', abs_sub_comm a b] using hbound

/-- The entropy modulus summed over a finite disjoint family of intervals. -/
theorem sublevel_coordinate_sum_dist_bound
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hsublevel : poissonPathRate N T A <= ENNReal.ofReal c)
    (j : Server) (k : Buffer) (hphi : 0 < N.phi j k)
    (theta : Real) (htheta : 0 < theta)
    (E : Nat × (Nat -> Real × Real))
    (hE : E ∈ AbsolutelyContinuousOnInterval.disjWithin 0 T) :
    theta *
        ∑ i ∈ Finset.range E.1,
          dist (A (E.2 i).1 j k) (A (E.2 i).2 j k) <=
      max c 0 +
        N.phi j k * (Real.exp theta - 1) *
          ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
  classical
  let S : Set Real :=
    ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have hSmeas : MeasurableSet S :=
    Finset.measurableSet_biUnion _ fun _ _ => measurableSet_uIoc
  have hSsub : S ⊆ Icc (0 : Real) T := by
    exact
      (AbsolutelyContinuousOnInterval.biUnion_uIoc_subset_of_mem_disjWithin
        hE).trans (uIoc_subset_uIcc.trans (by simp [uIcc_of_le hT.le]))
  have hpair :
      Set.PairwiseDisjoint (↑(Finset.range E.1))
        (fun i => uIoc (E.2 i).1 (E.2 i).2) :=
    hE.2
  have hfinite :
      poissonPathRate N T A ≠ (⊤ : ENNReal) :=
    ne_of_lt (hsublevel.trans_lt ENNReal.ofReal_lt_top)
  have hd_int :
      IntegrableOn (fun t => pathDerivative A t j k) (Icc 0 T) volume :=
    finiteAction_derivative_integrableOn N hT.le A hfinite j k
  have hsum_integral :
      (∫ t in S, pathDerivative A t j k) =
        ∑ i ∈ Finset.range E.1,
          ∫ t in uIoc (E.2 i).1 (E.2 i).2,
            pathDerivative A t j k := by
    apply integral_biUnion_finset
    · exact fun _ _ => measurableSet_uIoc
    · exact hpair
    · intro i hi
      exact hd_int.mono_set fun t ht =>
        hSsub (by
          dsimp [S]
          exact Set.mem_iUnion_of_mem i
            (Set.mem_iUnion_of_mem hi ht))
  have hsum_dist :
      (∫ t in S, pathDerivative A t j k) =
        ∑ i ∈ Finset.range E.1,
          dist (A (E.2 i).1 j k) (A (E.2 i).2 j k) := by
    rw [hsum_integral]
    apply Finset.sum_congr rfl
    intro i hi
    have hai : (E.2 i).1 ∈ Icc (0 : Real) T := by
      simpa [uIcc_of_le hT.le] using (hE.1 i hi).1
    have hbi : (E.2 i).2 ∈ Icc (0 : Real) T := by
      simpa [uIcc_of_le hT.le] using (hE.1 i hi).2
    rw [coordinate_dist_eq_setIntegral_derivative
      N hT A hsublevel j k hai hbi]
  have hmeasure :
      volume.real S =
        ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
    rw [measureReal_biUnion_finset hpair
      (fun _ _ => measurableSet_uIoc) (fun i hi => by
        rw [Real.volume_uIoc]
        exact ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro i hi
    simp [measureReal_def, Real.volume_uIoc, ENNReal.toReal_ofReal',
      Real.dist_eq, abs_sub_comm (E.2 i).1 (E.2 i).2]
  have hbound :=
    coordinate_setIntegral_derivative_bound N hT A hsublevel
      j k hphi theta htheta hSmeas hSsub
  rw [hsum_dist, hmeasure] at hbound
  exact hbound

/-- The finite-family entropy estimate is preserved by uniform limits. -/
theorem limit_coordinate_sum_dist_bound
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (f : Nat -> ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hf : forall n, f n ∈ continuousRateSublevel N T c)
    (x : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hfx : Tendsto f atTop (𝓝 x))
    (j : Server) (k : Buffer) (hphi : 0 < N.phi j k)
    (theta : Real) (htheta : 0 < theta)
    (E : Nat × (Nat -> Real × Real))
    (hE : E ∈ AbsolutelyContinuousOnInterval.disjWithin 0 T) :
    theta *
        ∑ i ∈ Finset.range E.1,
          dist
            (asMatrix T (continuousNonnegativeToPath x) (E.2 i).1 j k)
            (asMatrix T (continuousNonnegativeToPath x) (E.2 i).2 j k) <=
      max c 0 +
        N.phi j k * (Real.exp theta - 1) *
          ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
  classical
  let endpointSum :
      ContinuousNonnegativePath
        (Buffer := Buffer) (Server := Server) T -> Real :=
    fun y =>
      ∑ i ∈ Finset.range E.1,
        dist
          (asMatrix T (continuousNonnegativeToPath y) (E.2 i).1 j k)
          (asMatrix T (continuousNonnegativeToPath y) (E.2 i).2 j k)
  have hcontinuous : Continuous endpointSum := by
    dsimp [endpointSum, asMatrix, continuousNonnegativeToPath]
    simp only [dif_pos hT.le]
    fun_prop
  have htend :
      Tendsto (fun n => theta * endpointSum (f n)) atTop
        (𝓝 (theta * endpointSum x)) :=
    (continuous_const.mul hcontinuous).tendsto x |>.comp hfx
  apply le_of_tendsto htend
  filter_upwards with n
  have hn :=
    sublevel_coordinate_sum_dist_bound N hT
      (asMatrix T (continuousNonnegativeToPath (f n)))
      (hf n) j k hphi theta htheta E hE
  simpa only [endpointSum, asMatrix_apply_of_mem hT.le] using hn

theorem finiteAction_coordinate_monotoneOn
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hsublevel : poissonPathRate N T A <= ENNReal.ofReal c)
    (j : Server) (k : Buffer) :
    MonotoneOn (fun t => A t j k) (Icc 0 T) := by
  intro a ha b hb hab
  have hfinite :
      poissonPathRate N T A ≠ (⊤ : ENNReal) :=
    ne_of_lt (hsublevel.trans_lt ENNReal.ofReal_lt_top)
  let q : Real -> Real := fun t => A t j k
  have hac :
      AbsolutelyContinuousOnInterval q 0 T :=
    (poissonPathRate_ne_top_implies_valid N T A hfinite).1 j k
  have hacab : AbsolutelyContinuousOnInterval q a b := by
    apply hac.mono
    intro t ht
    simpa [uIcc_of_le hT.le] using
      (uIcc_subset_Icc ha hb ht)
  have heq :
      (∫ t in a..b, pathDerivative A t j k) =
        A b j k - A a j k := by
    simpa [q, pathDerivative] using hacab.integral_deriv_eq_sub
  have hnonneg :=
    finiteAction_derivative_nonneg_ae N T A hfinite j k
  have hnonneg_ab :
      ∀ᵐ t ∂volume, t ∈ Ioc a b ->
        0 <= pathDerivative A t j k := by
    have hambient := (ae_restrict_iff' measurableSet_Icc).mp hnonneg
    filter_upwards [hambient] with t ht
    intro htab
    exact ht ⟨ha.1.trans htab.1.le, htab.2.trans hb.2⟩
  have hint_nonneg :
      0 <= ∫ t in a..b, pathDerivative A t j k := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_nonneg_ae measurableSet_Ioc hnonneg_ab
  linarith [heq]

theorem limit_zeroRate_coordinate
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (f : Nat -> ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hf : forall n, f n ∈ continuousRateSublevel N T c)
    (x : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hfx : Tendsto f atTop (𝓝 x))
    (j : Server) (k : Buffer) (hphi : N.phi j k = 0)
    (t : Horizon T) :
    x.1 t j k = 0 := by
  have hcont :
      Continuous (fun y : ContinuousNonnegativePath
        (Buffer := Buffer) (Server := Server) T => y.1 t j k) := by
    fun_prop
  have htend :=
    (hcont.tendsto x).comp hfx
  change Tendsto (fun n => (f n).1 t j k) atTop
    (𝓝 (x.1 t j k)) at htend
  have hzero :
      (fun n => (f n).1 t j k) = fun _ => 0 := by
    funext n
    exact sublevel_zeroRate_coordinate N hT (hf n) j k hphi t
  rw [hzero] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

theorem limit_coordinate_start_zero
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (f : Nat -> ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hf : forall n, f n ∈ continuousRateSublevel N T c)
    (x : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hfx : Tendsto f atTop (𝓝 x))
    (j : Server) (k : Buffer) :
    x.1 ⟨0, ⟨le_rfl, hT.le⟩⟩ j k = 0 := by
  let t0 : Horizon T := ⟨0, ⟨le_rfl, hT.le⟩⟩
  have hcont :
      Continuous (fun y : ContinuousNonnegativePath
        (Buffer := Buffer) (Server := Server) T => y.1 t0 j k) := by
    fun_prop
  have htend := (hcont.tendsto x).comp hfx
  have hzero :
      (fun n => (f n).1 t0 j k) = fun _ => 0 := by
    funext n
    have hfinite :=
      rate_ne_top_of_mem_sublevel N T c (hf n)
    have hvalid :=
      poissonPathRate_ne_top_implies_valid N T
        (asMatrix T (continuousNonnegativeToPath (f n))) hfinite
    simpa [t0, asMatrix, hT.le, clampToHorizon,
      continuousNonnegativeToPath] using hvalid.2 j k
  change Tendsto (fun n => (f n).1 t0 j k) atTop
    (𝓝 (x.1 t0 j k)) at htend
  rw [hzero] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

theorem limit_coordinate_monotoneOn
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (f : Nat -> ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hf : forall n, f n ∈ continuousRateSublevel N T c)
    (x : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hfx : Tendsto f atTop (𝓝 x))
    (j : Server) (k : Buffer) :
    MonotoneOn
      (fun t : Real =>
        asMatrix T (continuousNonnegativeToPath x) t j k)
      (Icc 0 T) := by
  intro a ha b hb hab
  have hconta :
      Continuous (fun y : ContinuousNonnegativePath
        (Buffer := Buffer) (Server := Server) T =>
          asMatrix T (continuousNonnegativeToPath y) a j k) := by
    dsimp [asMatrix, continuousNonnegativeToPath]
    simp only [dif_pos hT.le]
    fun_prop
  have hcontb :
      Continuous (fun y : ContinuousNonnegativePath
        (Buffer := Buffer) (Server := Server) T =>
          asMatrix T (continuousNonnegativeToPath y) b j k) := by
    dsimp [asMatrix, continuousNonnegativeToPath]
    simp only [dif_pos hT.le]
    fun_prop
  apply le_of_tendsto_of_tendsto
    ((hconta.tendsto x).comp hfx) ((hcontb.tendsto x).comp hfx)
  filter_upwards with n
  exact finiteAction_coordinate_monotoneOn N hT
    (asMatrix T (continuousNonnegativeToPath (f n)))
    (hf n) j k ha hb hab

theorem limit_coordinate_absolutelyContinuous
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (f : Nat -> ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hf : forall n, f n ∈ continuousRateSublevel N T c)
    (x : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hfx : Tendsto f atTop (𝓝 x))
    (j : Server) (k : Buffer) :
    AbsolutelyContinuousOnInterval
      (fun t : Real =>
        asMatrix T (continuousNonnegativeToPath x) t j k) 0 T := by
  rcases (N.phi_nonneg j k).eq_or_lt with hphi | hphi
  · have hphi0 : N.phi j k = 0 := hphi.symm
    have hzero :
        (fun t : Real =>
          asMatrix T (continuousNonnegativeToPath x) t j k) =
          fun _ => 0 := by
      funext t
      simp only [asMatrix, dif_pos hT.le]
      exact limit_zeroRate_coordinate N hT f hf x hfx j k hphi0
        (clampToHorizon T hT.le t)
    rw [hzero]
    exact (LipschitzWith.const (α := Real) (0 : Real)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval
  · rw [absolutelyContinuousOnInterval_iff]
    intro epsilon hepsilon
    let C : Real := max c 0
    let theta : Real := 2 * (C + 1) / epsilon
    have hC : 0 <= C := le_max_right c 0
    have htheta : 0 < theta := by
      dsimp [theta]
      positivity
    let K : Real := N.phi j k * (Real.exp theta - 1)
    have hK : 0 <= K := by
      dsimp [K]
      exact mul_nonneg hphi.le
        (sub_nonneg.mpr (Real.one_le_exp htheta.le))
    let delta : Real := theta * epsilon / (2 * (K + 1))
    have hdelta : 0 < delta := by
      dsimp [delta]
      positivity
    refine ⟨delta, hdelta, fun E hE hlength => ?_⟩
    have hbound :=
      limit_coordinate_sum_dist_bound N hT f hf x hfx
        j k hphi theta htheta E hE
    have hCsmall : C < theta * epsilon / 2 := by
      dsimp [theta]
      field_simp
      linarith
    have hKsmall :
        K * (∑ i ∈ Finset.range E.1,
          dist (E.2 i).1 (E.2 i).2) < theta * epsilon / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hlength.le hK
      have hratio : K / (K + 1) < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      have hpos : 0 < theta * epsilon / 2 := by positivity
      calc
        K * (∑ i ∈ Finset.range E.1,
            dist (E.2 i).1 (E.2 i).2) <=
            K * delta := hmul
        _ = (theta * epsilon / 2) * (K / (K + 1)) := by
          dsimp [delta]
          field_simp
        _ < (theta * epsilon / 2) * 1 :=
          mul_lt_mul_of_pos_left hratio hpos
        _ = theta * epsilon / 2 := mul_one _
    change
      ∑ i ∈ Finset.range E.1,
        dist
          (asMatrix T (continuousNonnegativeToPath x) (E.2 i).1 j k)
          (asMatrix T (continuousNonnegativeToPath x) (E.2 i).2 j k) <
        epsilon
    dsimp [C, K] at hbound hCsmall hKsmall
    nlinarith

theorem derivative_nonneg_ae_of_monotoneOn
    {T : Real} (hT : 0 < T) (A : MatrixPath Server Buffer)
    (j : Server) (k : Buffer)
    (hmono : MonotoneOn (fun t => A t j k) (Icc 0 T)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      0 <= pathDerivative A t j k := by
  have hae_zero : ∀ᵐ t : Real ∂volume, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hae_T : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hae_zero, hae_T] with t ht0 htT
  intro ht
  have hinterior : t ∈ Ioo (0 : Real) T :=
    ⟨ht.1.lt_of_ne' ht0, ht.2.lt_of_ne htT⟩
  unfold pathDerivative
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hinterior.1 hinterior.2)]
  exact hmono.derivWithin_nonneg

theorem derivative_setAverage_eq_partitionChord_of_valid
    {T : Real} (hT : 0 <= T) (A : MatrixPath Server Buffer)
    (hvalid : IsAbsolutelyContinuousMatrixPath T A)
    (P : ActionPartition T) (i : Fin P.intervals)
    (j : Server) (k : Buffer) :
    (⨍ t in Icc (P.left i) (P.right i),
        pathDerivative A t j k ∂volume) =
      partitionChord A P i j k := by
  have hsub :
      uIcc (P.left i) (P.right i) ⊆ uIcc (0 : Real) T := by
    rw [uIcc_of_le (P.left_lt_right i).le, uIcc_of_le hT]
    exact P.cell_subset hT i
  have hac := (hvalid j k).mono hsub
  rw [setAverage_eq, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (P.left_lt_right i).le)]
  simp only [smul_eq_mul]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (P.left_lt_right i).le]
  change (P.width i)⁻¹ *
      (∫ t in P.left i..P.right i, deriv (fun s => A s j k) t) =
    partitionChord A P i j k
  rw [hac.integral_deriv_eq_sub]
  unfold partitionChord
  rw [div_eq_inv_mul]

theorem setAverage_restrictedDerivative_eq_uniformCellChord_of_valid
    {T : Real} (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hvalid : IsAbsolutelyContinuousMatrixPath T A)
    (n : Nat) {t : Real} (ht0 : 0 <= t) (htT : t < T) :
    (⨍ s in Metric.closedBall (uniformCellCenter T hT n t)
          (uniformCellRadius T n),
        (Icc (0 : Real) T).indicator (pathDerivative A) s ∂volume) =
      uniformCellChord T hT A n t := by
  classical
  let P := uniformActionPartition T hT n
  let i : Fin (n + 1) :=
    ⟨UniformPartition.cellIndex T n t,
      UniformPartition.cellIndex_lt hT n ht0 htT⟩
  rw [closedBall_uniformCellCenter hT n ht0 htT]
  simp only [uniformCellChord, ht0, htT, and_self, dite_true]
  change (⨍ s in Icc (P.left i) (P.right i),
      (Icc (0 : Real) T).indicator (pathDerivative A) s ∂volume) =
    partitionChord A P i
  have hcell_subset : Icc (P.left i) (P.right i) ⊆ Icc (0 : Real) T :=
    P.cell_subset hT.le i
  have hmatrix_int :
      IntegrableOn (pathDerivative A) (Icc 0 T) volume := by
    unfold IntegrableOn
    rw [integrable_pi_iff]
    intro q
    rw [integrable_pi_iff]
    intro r
    have hint := (hvalid q r).intervalIntegrable_deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le] at hint
    change Integrable
      (fun x => deriv (fun s => A s q r) x)
      (volume.restrict (Icc 0 T)) at hint ⊢
    exact hint
  have hindicator_int :
      Integrable ((Icc (0 : Real) T).indicator (pathDerivative A)) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hmatrix_int
  rw [setAverage_eq]
  funext j
  funext k
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [eval_integral (fun q => (hindicator_int.eval q).integrableOn) j]
  rw [eval_integral
    (fun r => ((hindicator_int.eval j).eval r).integrableOn) k]
  have hcoord :
      (⨍ s in Icc (P.left i) (P.right i),
        pathDerivative A s j k ∂volume) =
          partitionChord A P i j k :=
    derivative_setAverage_eq_partitionChord_of_valid hT.le A hvalid
      P i j k
  rw [setAverage_eq] at hcoord
  simp only [smul_eq_mul] at hcoord
  rw [← hcoord]
  congr 1
  apply integral_congr_ae
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards with s
  intro hs
  simp [hcell_subset hs]

theorem uniformCellChord_tendsto_ae_of_valid
    {T : Real} (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hvalid : IsAbsolutelyContinuousMatrixPath T A) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      Tendsto (fun n => uniformCellChord T hT A n t) atTop
        (𝓝 (pathDerivative A t)) := by
  classical
  let g : Real -> (Server -> Buffer -> Real) :=
    (Icc (0 : Real) T).indicator (pathDerivative A)
  have hmatrix_int :
      IntegrableOn (pathDerivative A) (Icc 0 T) volume := by
    unfold IntegrableOn
    rw [integrable_pi_iff]
    intro j
    rw [integrable_pi_iff]
    intro k
    have hint := (hvalid j k).intervalIntegrable_deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le] at hint
    change Integrable
      (fun x => deriv (fun s => A s j k) x)
      (volume.restrict (Icc 0 T)) at hint ⊢
    exact hint
  have hg_int : Integrable g volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hmatrix_int
  have hldt :=
    IsUnifLocDoublingMeasure.ae_tendsto_average volume
      hg_int.locallyIntegrable 1
  have hae_zero : ∀ᵐ t : Real ∂volume, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have hae_T : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hldt, hae_zero, hae_T] with t hx ht_ne_zero ht_ne_T
  intro ht
  have ht0 : 0 <= t := ht.1
  have htT : t < T := ht.2.lt_of_ne ht_ne_T
  have ht_mem_g : t ∈ Icc (0 : Real) T := ⟨ht0, htT.le⟩
  have hmem :
      ∀ᶠ n in atTop,
        t ∈ Metric.closedBall (uniformCellCenter T hT n t)
          (1 * uniformCellRadius T n) := by
    filter_upwards with n
    rw [one_mul, closedBall_uniformCellCenter hT n ht0 htT]
    have hcell := UniformPartition.mem_uniform_cell hT n ht0 htT
    exact ⟨hcell.1, hcell.2.le⟩
  have havg :=
    hx (uniformCellCenter T hT · t) (uniformCellRadius T)
      (tendsto_uniformCellRadius hT) hmem
  have havg' :
      Tendsto (fun n => uniformCellChord T hT A n t) atTop
        (𝓝 (g t)) := by
    refine Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n => ?_) havg
    exact setAverage_restrictedDerivative_eq_uniformCellChord_of_valid
      hT A hvalid n ht0 htT
  simpa [g, ht_mem_g] using havg'

theorem localRate_uniformCellChord_tendsto_ae_of_valid
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hvalid : IsAbsolutelyContinuousMatrixPath T A)
    (hmono : forall j k, MonotoneOn (fun t => A t j k) (Icc 0 T))
    (hzero : forall j k, N.phi j k = 0 -> forall t, A t j k = 0) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      Tendsto
        (fun n => N.localRate (uniformCellChord T hT A n t))
        atTop (𝓝 (N.localRate (pathDerivative A t))) := by
  classical
  have hnonneg_all :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        ∀ j k, 0 <= pathDerivative A t j k := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    exact derivative_nonneg_ae_of_monotoneOn hT A j k (hmono j k)
  have hae_T : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  have hinterior :
      ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 <= t ∧ t < T :=
    (ae_restrict_iff' measurableSet_Icc).mpr <| by
      filter_upwards [hae_T] with t ht_ne
      intro ht
      exact ⟨ht.1, ht.2.lt_of_ne ht_ne⟩
  filter_upwards
    [uniformCellChord_tendsto_ae_of_valid hT A hvalid,
      hnonneg_all, hinterior]
      with t hchord hderiv_nonneg ht
  unfold Network.localRate
  apply tendsto_finsetSum Finset.univ
  intro j hj
  apply tendsto_finsetSum Finset.univ
  intro k hk
  rcases (N.phi_nonneg j k).eq_or_lt with hphi | hphi
  · have hphi0 : N.phi j k = 0 := hphi.symm
    have hpathzero := hzero j k hphi0
    have hlimit0 : pathDerivative A t j k = 0 := by
      unfold pathDerivative
      have hfun : (fun s => A s j k) = fun _ => 0 := by
        funext s
        exact hpathzero s
      rw [hfun]
      simp
    have hseq0 (n : Nat) :
        uniformCellChord T hT A n t j k = 0 := by
      let i : Fin (uniformActionPartition T hT n).intervals :=
        ⟨UniformPartition.cellIndex T n t,
          UniformPartition.cellIndex_lt hT n ht.1 ht.2⟩
      have hcell_eq :
          uniformCellChord T hT A n t j k =
            partitionChord A (uniformActionPartition T hT n) i j k := by
        simp [uniformCellChord, ht, i]
      rw [hcell_eq]
      unfold partitionChord
      rw [hpathzero, hpathzero, sub_self, zero_div]
    simp [hphi0, hlimit0, hseq0]
  · have hscalar :
        Tendsto (fun n => uniformCellChord T hT A n t j k)
          atTop (𝓝 (pathDerivative A t j k)) :=
      (hchord.apply_nhds j).apply_nhds k
    have hpositive :
        Tendsto
          (fun n => positivePoissonCostReal (N.phi j k)
            (uniformCellChord T hT A n t j k))
          atTop
          (𝓝 (positivePoissonCostReal (N.phi j k)
            (pathDerivative A t j k))) :=
      Filter.Tendsto.comp
        ((continuous_positivePoissonCostReal (N.phi j k)).tendsto
          (pathDerivative A t j k))
        hscalar
    have hofReal :
        Tendsto
          (fun n => ENNReal.ofReal
            (positivePoissonCostReal (N.phi j k)
              (uniformCellChord T hT A n t j k)))
          atTop
          (𝓝 (ENNReal.ofReal
            (positivePoissonCostReal (N.phi j k)
              (pathDerivative A t j k)))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hpositive
    have hlimit_nonneg := hderiv_nonneg j k
    have hseq_nonneg (n : Nat) :
        0 <= uniformCellChord T hT A n t j k := by
      let P := uniformActionPartition T hT n
      let i : Fin P.intervals :=
        ⟨UniformPartition.cellIndex T n t,
          UniformPartition.cellIndex_lt hT n ht.1 ht.2⟩
      have hcell_eq :
          uniformCellChord T hT A n t j k =
            partitionChord A P i j k := by
        simp [uniformCellChord, ht, P, i]
      rw [hcell_eq]
      unfold partitionChord
      have hleft : P.left i ∈ Icc (0 : Real) T :=
        P.cell_subset hT.le i ⟨le_rfl, (P.left_lt_right i).le⟩
      have hright : P.right i ∈ Icc (0 : Real) T :=
        P.cell_subset hT.le i ⟨(P.left_lt_right i).le, le_rfl⟩
      exact div_nonneg
        (sub_nonneg.mpr <| hmono j k hleft hright (P.left_lt_right i).le)
        (P.width_pos i).le
    have hcostseq :
        (fun n => poissonCost (N.phi j k)
          (uniformCellChord T hT A n t j k)) =
        (fun n => ENNReal.ofReal
          (positivePoissonCostReal (N.phi j k)
            (uniformCellChord T hT A n t j k))) := by
      funext n
      rw [poissonCost_of_nominal_pos hphi (hseq_nonneg n)]
      congr 1
      exact (positivePoissonCostReal_eq hphi (hseq_nonneg n)).symm
    have hcostlimit :
        poissonCost (N.phi j k) (pathDerivative A t j k) =
          ENNReal.ofReal
            (positivePoissonCostReal (N.phi j k)
              (pathDerivative A t j k)) := by
      rw [poissonCost_of_nominal_pos hphi hlimit_nonneg]
      congr 1
      exact (positivePoissonCostReal_eq hphi hlimit_nonneg).symm
    rw [hcostseq, hcostlimit]
    exact hofReal

theorem poissonPathRate_le_liminf_uniformPartitionAction_of_valid
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hvalid : IsAbsolutelyContinuousMatrixPath T A /\
      forall j k, A 0 j k = 0)
    (hmono : forall j k, MonotoneOn (fun t => A t j k) (Icc 0 T))
    (hzero : forall j k, N.phi j k = 0 -> forall t, A t j k = 0) :
    poissonPathRate N T A <=
      liminf
        (fun n =>
          poissonPartitionAction N A (uniformActionPartition T hT n))
        atTop := by
  classical
  let F : Nat -> Real -> ENNReal :=
    fun n t =>
      partitionStepCost N A (uniformActionPartition T hT n) t
  have hae_T : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  have hinterior :
      ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 <= t ∧ t < T :=
    (ae_restrict_iff' measurableSet_Icc).mpr <| by
      filter_upwards [hae_T] with t ht_ne
      intro ht
      exact ⟨ht.1, ht.2.lt_of_ne ht_ne⟩
  have hconv :
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        Tendsto (fun n => F n t) atTop
          (𝓝 (N.localRate (pathDerivative A t))) := by
    filter_upwards
      [localRate_uniformCellChord_tendsto_ae_of_valid
        N hT A hvalid.1 hmono hzero,
        hinterior] with t htend ht
    apply Filter.Tendsto.congr'
      (Filter.Eventually.of_forall fun n => ?_) htend
    exact (partitionStepCost_uniform_eq N T hT A n ht.1 ht.2).symm
  rw [poissonPathRate, if_pos hvalid]
  calc
    (∫⁻ t in Icc 0 T, N.localRate (pathDerivative A t)) =
        ∫⁻ t in Icc 0 T, liminf (fun n => F n t) atTop := by
          apply lintegral_congr_ae
          exact hconv.mono fun t ht => ht.liminf_eq.symm
    _ <= liminf
        (fun n => ∫⁻ t in Icc 0 T, F n t) atTop :=
      lintegral_liminf_le' fun n => by
        simpa [F] using
          (measurable_partitionStepCost N A
            (uniformActionPartition T hT n)).aemeasurable
    _ = liminf
        (fun n =>
          poissonPartitionAction N A (uniformActionPartition T hT n))
        atTop := by
          congr 1
          funext n
          exact lintegral_partitionStepCost_Icc N A hT.le
            (uniformActionPartition T hT n)

theorem tendsto_poissonPartitionAction_of_sublevel_limit
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (f : Nat -> ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hf : forall n, f n ∈ continuousRateSublevel N T c)
    (x : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hfx : Tendsto f atTop (𝓝 x))
    (P : ActionPartition T) :
    Tendsto
      (fun n => poissonPartitionAction N
        (asMatrix T (continuousNonnegativeToPath (f n))) P)
      atTop
      (𝓝 (poissonPartitionAction N
        (asMatrix T (continuousNonnegativeToPath x)) P)) := by
  classical
  unfold poissonPartitionAction Network.localRate
  apply tendsto_finsetSum Finset.univ
  intro i hi
  apply ENNReal.Tendsto.const_mul
  · apply tendsto_finsetSum Finset.univ
    intro j hj
    apply tendsto_finsetSum Finset.univ
    intro k hk
    let chord :
        ContinuousNonnegativePath
          (Buffer := Buffer) (Server := Server) T -> Real :=
      fun y =>
        partitionChord
          (asMatrix T (continuousNonnegativeToPath y)) P i j k
    have hchord_cont : Continuous chord := by
      dsimp [chord, partitionChord, asMatrix, continuousNonnegativeToPath]
      simp only [dif_pos hT.le]
      fun_prop
    have hchord :
        Tendsto (fun n => chord (f n)) atTop (𝓝 (chord x)) :=
      (hchord_cont.tendsto x).comp hfx
    rcases (N.phi_nonneg j k).eq_or_lt with hphi | hphi
    · have hphi0 : N.phi j k = 0 := hphi.symm
      have hseq0 (n : Nat) : chord (f n) = 0 := by
        unfold chord partitionChord
        have hleft :
            asMatrix T (continuousNonnegativeToPath (f n)) (P.left i) j k =
              0 := by
          have hmem := P.cell_subset hT.le i
            ⟨le_rfl, (P.left_lt_right i).le⟩
          rw [asMatrix_apply_of_mem hT.le hmem]
          exact sublevel_zeroRate_coordinate N hT (hf n) j k hphi0
            ⟨P.left i, hmem⟩
        have hright :
            asMatrix T (continuousNonnegativeToPath (f n)) (P.right i) j k =
              0 := by
          have hmem := P.cell_subset hT.le i
            ⟨(P.left_lt_right i).le, le_rfl⟩
          rw [asMatrix_apply_of_mem hT.le hmem]
          exact sublevel_zeroRate_coordinate N hT (hf n) j k hphi0
            ⟨P.right i, hmem⟩
        rw [hleft, hright, sub_self, zero_div]
      have hlimit0 : chord x = 0 := by
        unfold chord partitionChord
        have hleft :
            asMatrix T (continuousNonnegativeToPath x) (P.left i) j k = 0 := by
          simp only [asMatrix, dif_pos hT.le]
          exact limit_zeroRate_coordinate N hT f hf x hfx j k hphi0 _
        have hright :
            asMatrix T (continuousNonnegativeToPath x) (P.right i) j k = 0 := by
          simp only [asMatrix, dif_pos hT.le]
          exact limit_zeroRate_coordinate N hT f hf x hfx j k hphi0 _
        rw [hleft, hright, sub_self, zero_div]
      have hcostseq :
          (fun n => poissonCost (N.phi j k) (chord (f n))) =
            fun _ => (0 : ENNReal) := by
        funext n
        rw [hphi0, hseq0 n, poissonCost_zero_zero]
      have hcostlimit :
          poissonCost (N.phi j k) (chord x) = 0 := by
        rw [hphi0, hlimit0, poissonCost_zero_zero]
      change Tendsto
        (fun n => poissonCost (N.phi j k) (chord (f n))) atTop
        (𝓝 (poissonCost (N.phi j k) (chord x)))
      rw [hcostseq, hcostlimit]
      exact tendsto_const_nhds
    · have hseq_nonneg (n : Nat) : 0 <= chord (f n) := by
        have hfinite :=
          rate_ne_top_of_mem_sublevel N T c (hf n)
        exact partitionChord_nonneg N hT.le
          (asMatrix T (continuousNonnegativeToPath (f n)))
          hfinite P i j k
      have hlimit_nonneg : 0 <= chord x := by
        unfold chord partitionChord
        have hleft := P.cell_subset hT.le i
          ⟨le_rfl, (P.left_lt_right i).le⟩
        have hright := P.cell_subset hT.le i
          ⟨(P.left_lt_right i).le, le_rfl⟩
        exact div_nonneg
          (sub_nonneg.mpr <| limit_coordinate_monotoneOn N hT f hf x hfx
            j k hleft hright (P.left_lt_right i).le)
          (P.width_pos i).le
      have hpositive :
          Tendsto
            (fun n => positivePoissonCostReal (N.phi j k) (chord (f n)))
            atTop
            (𝓝 (positivePoissonCostReal (N.phi j k) (chord x))) :=
        Filter.Tendsto.comp
          ((continuous_positivePoissonCostReal (N.phi j k)).tendsto (chord x))
          hchord
      have hofReal := (ENNReal.continuous_ofReal.tendsto _).comp hpositive
      have hseqeq :
          (fun n => poissonCost (N.phi j k) (chord (f n))) =
            fun n => ENNReal.ofReal
              (positivePoissonCostReal (N.phi j k) (chord (f n))) := by
        funext n
        rw [poissonCost_of_nominal_pos hphi (hseq_nonneg n)]
        congr 1
        exact (positivePoissonCostReal_eq hphi (hseq_nonneg n)).symm
      have hlimiteq :
          poissonCost (N.phi j k) (chord x) =
            ENNReal.ofReal
              (positivePoissonCostReal (N.phi j k) (chord x)) := by
        rw [poissonCost_of_nominal_pos hphi hlimit_nonneg]
        congr 1
        exact (positivePoissonCostReal_eq hphi hlimit_nonneg).symm
      change Tendsto
        (fun n => poissonCost (N.phi j k) (chord (f n))) atTop
        (𝓝 (poissonCost (N.phi j k) (chord x)))
      rw [hseqeq, hlimiteq]
      exact hofReal
  · exact Or.inr ENNReal.ofReal_ne_top

theorem limit_mem_continuousRateSublevel
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (f : Nat -> ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hf : forall n, f n ∈ continuousRateSublevel N T c)
    (x : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T)
    (hfx : Tendsto f atTop (𝓝 x)) :
    x ∈ continuousRateSublevel N T c := by
  classical
  let A := asMatrix T (continuousNonnegativeToPath x)
  have hac : IsAbsolutelyContinuousMatrixPath T A :=
    fun j k => limit_coordinate_absolutelyContinuous N hT f hf x hfx j k
  have hstart : forall j k, A 0 j k = 0 := by
    intro j k
    dsimp [A]
    rw [asMatrix_apply_of_mem hT.le ⟨le_rfl, hT.le⟩]
    exact limit_coordinate_start_zero N hT f hf x hfx j k
  have hmono :
      forall j k, MonotoneOn (fun t => A t j k) (Icc 0 T) :=
    fun j k => limit_coordinate_monotoneOn N hT f hf x hfx j k
  have hzero :
      forall j k, N.phi j k = 0 -> forall t, A t j k = 0 := by
    intro j k hphi t
    dsimp [A, asMatrix]
    simp only [dif_pos hT.le]
    exact limit_zeroRate_coordinate N hT f hf x hfx j k hphi
      (clampToHorizon T hT.le t)
  have hrecover :=
    poissonPathRate_le_liminf_uniformPartitionAction_of_valid
      N hT A ⟨hac, hstart⟩ hmono hzero
  have hpart (m : Nat) :
      poissonPartitionAction N A (uniformActionPartition T hT m) <=
        ENNReal.ofReal c := by
    have htend :=
      tendsto_poissonPartitionAction_of_sublevel_limit
        N hT f hf x hfx (uniformActionPartition T hT m)
    apply le_of_tendsto htend
    filter_upwards with n
    exact (poissonPartitionAction_le_poissonPathRate N hT.le
      (asMatrix T (continuousNonnegativeToPath (f n)))
      (rate_ne_top_of_mem_sublevel N T c (hf n))
      (uniformActionPartition T hT m)).trans (hf n)
  exact hrecover.trans <|
    liminf_le_of_frequently_le'
      (Filter.Frequently.of_forall hpart)

theorem isClosed_continuousRateSublevel
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T) :
    IsClosed
      (continuousRateSublevel N T c) := by
  apply IsSeqClosed.isClosed
  intro f x hf hfx
  exact limit_mem_continuousRateSublevel N hT f hf x hfx

def continuousRateSublevelBase
    (N : Network Buffer Server) (T c : Real) :
    Set (ContinuousMatrixPath
      (Buffer := Buffer) (Server := Server) T) :=
  ((fun f : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T => f.1) ''
    continuousRateSublevel N T c)

theorem isClosed_continuousRateSublevelBase
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T) :
    IsClosed
      (continuousRateSublevelBase N T c) := by
  apply IsSeqClosed.isClosed
  intro f x hf hfx
  choose g hg hgf using hf
  have hgval :
      Tendsto
        (fun n => (g n).1) atTop (𝓝 x) := by
    simpa only [hgf] using hfx
  have hxnonneg : forall t j k, 0 <= x t j k := by
    intro t j k
    have htend :
        Tendsto (fun n => (g n).1 t j k) atTop (𝓝 (x t j k)) := by
      have hcontinuous :
          Continuous
            (fun y : ContinuousMatrixPath
              (Buffer := Buffer) (Server := Server) T => y t j k) := by
        fun_prop
      exact (hcontinuous.tendsto x).comp hgval
    apply ge_of_tendsto htend
    filter_upwards with n
    exact (g n).2 t j k
  let x' : ContinuousNonnegativePath
      (Buffer := Buffer) (Server := Server) T :=
    ⟨x, hxnonneg⟩
  have hgx' : Tendsto g atTop (𝓝 x') := by
    apply tendsto_subtype_rng.mpr
    exact hgval
  refine ⟨x', ?_, rfl⟩
  exact limit_mem_continuousRateSublevel N hT g hg x' hgx'

theorem network_phi_le_one
    (N : Network Buffer Server) (j : Server) (k : Buffer) :
    N.phi j k <= 1 := by
  calc
    N.phi j k <= Finset.univ.sum
        (fun p : Server × Buffer => N.phi p.1 p.2) := by
      exact Finset.single_le_sum
        (fun p _ => N.phi_nonneg p.1 p.2)
        (Finset.mem_univ (j, k))
    _ = 1 := by
      rw [Fintype.sum_prod_type, N.total_rate]

theorem continuousRateSublevelBase_range_bound
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T)
    (f : ContinuousMatrixPath
      (Buffer := Buffer) (Server := Server) T)
    (hf : f ∈ continuousRateSublevelBase N T c)
    (t : Horizon T) :
    dist (f t) 0 <=
      max c 0 + (Real.exp 1 - 1) * T := by
  rcases hf with ⟨g, hg, rfl⟩
  have hC : 0 <= max c 0 := le_max_right c 0
  have hE : 0 <= Real.exp 1 - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hM : 0 <= max c 0 + (Real.exp 1 - 1) * T :=
    add_nonneg hC (mul_nonneg hE hT.le)
  apply (dist_pi_le_iff hM).2
  intro j
  apply (dist_pi_le_iff hM).2
  intro k
  rcases (N.phi_nonneg j k).eq_or_lt with hphi | hphi
  · have hphi0 : N.phi j k = 0 := hphi.symm
    have hzero :=
      sublevel_zeroRate_coordinate N hT hg j k hphi0 t
    rw [show g.1 t j k = 0 from hzero]
    simpa using hM
  · have hbound :=
      sublevel_coordinate_dist_bound N hT
        (asMatrix T (continuousNonnegativeToPath g)) hg
        j k hphi 1 (by norm_num)
        (a := 0) (b := (t : Real))
        ⟨le_rfl, hT.le⟩ t.property
    simp only [one_mul] at hbound
    have hstart :
        g.1 ⟨0, ⟨le_rfl, hT.le⟩⟩ j k = 0 := by
      have hfinite := rate_ne_top_of_mem_sublevel N T c hg
      have hvalid :=
        poissonPathRate_ne_top_implies_valid N T
          (asMatrix T (continuousNonnegativeToPath g)) hfinite
      simpa [asMatrix, hT.le, clampToHorizon,
        continuousNonnegativeToPath] using hvalid.2 j k
    have ht_dist : dist (0 : Real) (t : Real) <= T := by
      simpa [Real.dist_eq, abs_of_nonneg t.property.1] using t.property.2
    have hphiE :
        N.phi j k * (Real.exp 1 - 1) <= Real.exp 1 - 1 := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (network_phi_le_one N j k) hE)
    have hproduct :
        N.phi j k * (Real.exp 1 - 1) * dist (0 : Real) (t : Real) <=
          (Real.exp 1 - 1) * T := by
      calc
        N.phi j k * (Real.exp 1 - 1) * dist (0 : Real) (t : Real) <=
            (Real.exp 1 - 1) * dist (0 : Real) (t : Real) :=
          mul_le_mul_of_nonneg_right hphiE dist_nonneg
        _ <= (Real.exp 1 - 1) * T :=
          mul_le_mul_of_nonneg_left ht_dist hE
    have hbound' :
        dist
            (asMatrix T (continuousNonnegativeToPath g) 0 j k)
            (asMatrix T (continuousNonnegativeToPath g) (t : Real) j k) <=
          max c 0 + (Real.exp 1 - 1) * T :=
      hbound.trans (add_le_add le_rfl hproduct)
    have hAstart :
        asMatrix T (continuousNonnegativeToPath g) 0 j k = 0 := by
      rw [asMatrix_apply_of_mem hT.le ⟨le_rfl, hT.le⟩]
      exact hstart
    rw [hAstart,
      asMatrix_apply_of_mem hT.le t.property] at hbound'
    simpa [Real.dist_eq] using hbound'

theorem equicontinuous_continuousRateSublevelBase
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T) :
    Equicontinuous
      ((↑) :
        continuousRateSublevelBase N T c ->
          Horizon T -> FiniteMatrix Server Buffer) := by
  apply UniformEquicontinuous.equicontinuous
  rw [Metric.uniformEquicontinuous_iff]
  intro epsilon hepsilon
  let C : Real := max c 0
  let theta : Real := 2 * (C + 1) / epsilon
  have hC : 0 <= C := le_max_right c 0
  have htheta : 0 < theta := by
    dsimp [theta]
    positivity
  let K : Real := Real.exp theta - 1
  have hK : 0 <= K := by
    dsimp [K]
    exact sub_nonneg.mpr (Real.one_le_exp htheta.le)
  let delta : Real := theta * epsilon / (2 * (K + 1))
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  refine ⟨delta, hdelta, fun s t hst f => ?_⟩
  rcases f.2 with ⟨g, hg, hgf⟩
  change dist (f.1 s) (f.1 t) < epsilon
  rw [← hgf]
  apply (dist_pi_lt_iff hepsilon).2
  intro j
  apply (dist_pi_lt_iff hepsilon).2
  intro k
  rcases (N.phi_nonneg j k).eq_or_lt with hphi | hphi
  · have hphi0 : N.phi j k = 0 := hphi.symm
    have hs0 :=
      sublevel_zeroRate_coordinate N hT hg j k hphi0 s
    have ht0 :=
      sublevel_zeroRate_coordinate N hT hg j k hphi0 t
    rw [show g.1 s j k = 0 from hs0,
      show g.1 t j k = 0 from ht0, dist_self]
    exact hepsilon
  · have hbound :=
      sublevel_coordinate_dist_bound N hT
        (asMatrix T (continuousNonnegativeToPath g)) hg
        j k hphi theta htheta
        (a := (s : Real)) (b := (t : Real))
        s.property t.property
    rw [asMatrix_apply_of_mem hT.le s.property,
      asMatrix_apply_of_mem hT.le t.property] at hbound
    have htime : dist (s : Real) (t : Real) <= delta := by
      exact hst.le
    have hphiK : N.phi j k * K <= K := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (network_phi_le_one N j k) hK)
    have hterm :
        N.phi j k * K * dist (s : Real) (t : Real) <
          theta * epsilon / 2 := by
      have hratio : K / (K + 1) < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      have hpositive : 0 < theta * epsilon / 2 := by
        positivity
      calc
        N.phi j k * K * dist (s : Real) (t : Real) <=
            K * dist (s : Real) (t : Real) :=
          mul_le_mul_of_nonneg_right hphiK dist_nonneg
        _ <= K * delta :=
          mul_le_mul_of_nonneg_left htime hK
        _ = (theta * epsilon / 2) * (K / (K + 1)) := by
          dsimp [delta]
          field_simp
        _ < (theta * epsilon / 2) * 1 :=
          mul_lt_mul_of_pos_left hratio hpositive
        _ = theta * epsilon / 2 := mul_one _
    have hCsmall : C < theta * epsilon / 2 := by
      dsimp [theta]
      field_simp
      linarith
    have hthetaDist :
        theta * dist (g.1 s j k) (g.1 t j k) <
          theta * epsilon := by
      calc
        theta * dist (g.1 s j k) (g.1 t j k) <=
            C + N.phi j k * K * dist (s : Real) (t : Real) := by
          simpa only [C, K, continuousNonnegativeToPath_apply,
            Subtype.coe_eta] using hbound
        _ < theta * epsilon / 2 + theta * epsilon / 2 :=
          add_lt_add hCsmall hterm
        _ = theta * epsilon := by ring
    exact lt_of_mul_lt_mul_left hthetaDist htheta.le

theorem isCompact_continuousRateSublevelBase
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T) :
    IsCompact
      (continuousRateSublevelBase N T c) := by
  let M : Real := max c 0 + (Real.exp 1 - 1) * T
  apply BoundedContinuousFunction.arzela_ascoli₂
    (Metric.closedBall
      (0 : FiniteMatrix Server Buffer) M)
    (isCompact_closedBall (0 : FiniteMatrix Server Buffer) M)
    (continuousRateSublevelBase N T c)
    (isClosed_continuousRateSublevelBase N hT)
  · intro f t hf
    rw [Metric.mem_closedBall]
    exact continuousRateSublevelBase_range_bound N hT f hf t
  · exact equicontinuous_continuousRateSublevelBase N hT

theorem isCompact_continuousRateSublevel
    (N : Network Buffer Server) {T c : Real} (hT : 0 < T) :
    IsCompact
      (continuousRateSublevel N T c) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  exact isCompact_continuousRateSublevelBase N hT

/-- Every real sublevel of the Poisson sample-path action is compact in the
repository's separated J1 path topology. -/
theorem isCompact_poissonPathRate_sublevel
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) (c : Real) :
    IsCompact
      {x : Path (Buffer := Buffer) (Server := Server) T |
        poissonPathRate N T (asMatrix T x) <= ENNReal.ofReal c} := by
  rw [poissonSublevel_eq_continuous_image N hT]
  exact
    (isCompact_continuousRateSublevel N hT).image
      continuous_continuousNonnegativeToPath

theorem poissonPathRate_isGood
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) :
    forall c : Real,
      IsCompact
        {x : Path (Buffer := Buffer) (Server := Server) T |
          poissonPathRate N T (asMatrix T x) <= ENNReal.ofReal c} :=
  isCompact_poissonPathRate_sublevel N hT

end

end StateDepMOR.PoissonSamplePath


open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory ProbabilityTheory Set

namespace StateDepMOR


namespace PoissonSamplePath

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

set_option maxRecDepth 10000

/-- The genuine open-set lower bound for the actual calendar-time path law. -/
def CalendarPathOpenLowerBound
    (N : Network Buffer Server) (T : Real) : Prop :=
  forall G : Set (Path (Buffer := Buffer) (Server := Server) T),
    IsOpen G ->
      -(rateInf
          (fun x : Path (Buffer := Buffer) (Server := Server) T =>
            poissonPathRate N T (asMatrix T x))
          G : EReal) <=
        liminf (scaledLogMass (calendarPathLaw N T) G) atTop

theorem timeError_identity_lower (T : Real) :
    timeError (identityTimeChange T) = 0 := by
  simp [timeError, identityTimeChange]

theorem pathError_identity_le_of_uniform
    {T delta : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T)
    (hxy : forall t j k, |x t j k - y t j k| <= delta) :
    pathError x y (identityTimeChange T) <= ENNReal.ofReal delta := by
  unfold pathError
  apply iSup_le
  intro t
  apply iSup_le
  intro j
  apply iSup_le
  intro k
  simpa [identityTimeChange] using ENNReal.ofReal_le_ofReal (hxy t j k)

theorem j1EDist_le_of_uniform
    {T delta : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T)
    (hdelta : 0 <= delta)
    (hxy : forall t j k, |x t j k - y t j k| <= delta) :
    j1EDist x y <= ENNReal.ofReal delta := by
  have hcost :
      j1Cost x y (identityTimeChange T) <= ENNReal.ofReal delta := by
    rw [j1Cost, timeError_identity_lower]
    exact max_le (by simp)
      (pathError_identity_le_of_uniform x y hxy)
  exact inf_le_of_left_le
    ((symmetricJ1EDist_le_j1Cost x y (identityTimeChange T)).trans hcost)

theorem mem_j1Ball_of_uniform
    {T delta epsilon : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) T)
    (hdelta : 0 <= delta) (hde : delta < epsilon)
    (hxy : forall t j k, |x t j k - y t j k| <= delta) :
    y ∈ j1Ball x epsilon := by
  have hepsilon : 0 < epsilon := hdelta.trans_lt hde
  exact (j1EDist_le_of_uniform x y hdelta hxy).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hepsilon).2 hde)

noncomputable def partitionTarget
    (A : MatrixPath Server Buffer) {T : Real} (P : ActionPartition T) :
    PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real :=
  fun a => A (P.right a.2) a.1.1 a.1.2 -
    A (P.left a.2) a.1.1 a.1.2

theorem partitionTarget_eq_width_mul_chord
    (A : MatrixPath Server Buffer) {T : Real} (P : ActionPartition T)
    (a : PartitionCoord (Buffer := Buffer) (Server := Server) P) :
    partitionTarget A P a =
      P.width a.2 * partitionChord A P a.2 a.1.1 a.1.2 := by
  unfold partitionTarget partitionChord
  field_simp [ne_of_gt (P.width_pos a.2)]

theorem partitionTarget_admissible
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (P : ActionPartition T) :
    PoissonFiniteArray.Admissible (partitionIntensity N P)
      (partitionTarget A P) := by
  intro a
  have hw := P.width_pos a.2
  have hc := partitionChord_nonneg N hT A hfinite P a.2 a.1.1 a.1.2
  constructor
  · rw [partitionTarget_eq_width_mul_chord]
    positivity
  · intro hq
    have hprod :
        Real.toNNReal (P.width a.2) *
            Real.toNNReal (N.phi a.1.1 a.1.2) = 0 := by
      exact hq
    have hw0 : Real.toNNReal (P.width a.2) ≠ 0 := by
      exact ne_of_gt (Real.toNNReal_pos.mpr hw)
    have hphiNN : Real.toNNReal (N.phi a.1.1 a.1.2) = 0 :=
      (mul_eq_zero.mp hprod).resolve_left hw0
    have hphi : N.phi a.1.1 a.1.2 = 0 := by
      rw [Real.toNNReal_eq_zero] at hphiNN
      exact le_antisymm hphiNN (N.phi_nonneg _ _)
    rw [partitionTarget_eq_width_mul_chord,
      partitionChord_eq_zero_of_phi_eq_zero
        N hT A hfinite P a.2 a.1.1 a.1.2 hphi, mul_zero]

theorem poissonCost_scale
    {w nominal candidate : Real} (hw : 0 < w)
    (hnominal : 0 <= nominal) (hcandidate : 0 <= candidate)
    (hzero : nominal = 0 -> candidate = 0) :
    poissonCost (w * nominal) (w * candidate) =
      ENNReal.ofReal w * poissonCost nominal candidate := by
  rcases hnominal.eq_or_lt with hnominal0 | hnominal
  · have hn0 : nominal = 0 := hnominal0.symm
    have hc0 := hzero hn0
    subst nominal
    subst candidate
    simp
  · have hwn : 0 < w * nominal := mul_pos hw hnominal
    rw [poissonCost_of_nominal_pos hwn (mul_nonneg hw.le hcandidate),
      poissonCost_of_nominal_pos hnominal hcandidate,
      ← ENNReal.ofReal_mul hw.le]
    congr 1
    by_cases hc0 : candidate = 0
    · simp [hc0]
    · have hc : 0 < candidate :=
        lt_of_le_of_ne hcandidate (Ne.symm hc0)
      have hratio :
          w * candidate / (w * nominal) = candidate / nominal := by
        field_simp
      rw [hratio]
      ring

theorem partitionAction_eq
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (P : ActionPartition T) :
    PoissonFiniteArray.action (partitionIntensity N P)
        (partitionTarget A P) =
      poissonPartitionAction N A P := by
  classical
  unfold PoissonFiniteArray.action poissonPartitionAction
  rw [Fintype.sum_prod_type, Fintype.sum_sigma]
  calc
    (∑ j : Server, ∑ k : Buffer, ∑ i : Fin P.intervals,
          poissonCost
            (partitionIntensity N P (⟨j, k⟩, i))
            (partitionTarget A P (⟨j, k⟩, i))) =
        ∑ j : Server, ∑ i : Fin P.intervals, ∑ k : Buffer,
          poissonCost
            (partitionIntensity N P (⟨j, k⟩, i))
            (partitionTarget A P (⟨j, k⟩, i)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = ∑ i : Fin P.intervals, ∑ j : Server, ∑ k : Buffer,
          poissonCost
            (partitionIntensity N P (⟨j, k⟩, i))
            (partitionTarget A P (⟨j, k⟩, i)) := Finset.sum_comm
    _ = ∑ i : Fin P.intervals,
        ENNReal.ofReal (P.width i) *
          N.localRate (partitionChord A P i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Network.localRate]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hw := P.width_pos i
      have hc := partitionChord_nonneg N hT A hfinite P i j k
      have hzero :
          N.phi j k = 0 -> partitionChord A P i j k = 0 :=
        partitionChord_eq_zero_of_phi_eq_zero
          N hT A hfinite P i j k
      rw [show partitionTarget A P (⟨j, k⟩, i) =
          P.width i * partitionChord A P i j k by
            exact partitionTarget_eq_width_mul_chord
              A P (⟨j, k⟩, i)]
      simp only [partitionIntensity, NNReal.coe_mul,
        Real.coe_toNNReal (P.width i) hw.le,
        Real.coe_toNNReal (N.phi j k) (N.phi_nonneg j k)]
      rw [poissonCost_scale hw (N.phi_nonneg j k) hc hzero]

theorem finiteRate_coordinate_monotoneOn
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hfinite :
      poissonPathRate N T (asMatrix T x) ≠ (⊤ : ENNReal))
    (j : Server) (k : Buffer) :
    MonotoneOn (fun t : Real => asMatrix T x t j k) (Icc 0 T) := by
  intro s hs t ht hst
  let f : Real -> Real := fun r => asMatrix T x r j k
  have hac : AbsolutelyContinuousOnInterval f 0 T :=
    (poissonPathRate_ne_top_implies_valid
      N T (asMatrix T x) hfinite).1 j k
  have hsub : Icc s t ⊆ Icc (0 : Real) T := by
    intro r hr
    exact ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
  have hacst : AbsolutelyContinuousOnInterval f s t := by
    apply hac.mono
    simpa [uIcc_of_le hT.le, uIcc_of_le hst] using hsub
  have hderiv_restrict :
      Filter.Eventually (fun r => 0 <= deriv f r)
        (ae (volume.restrict (Icc 0 T))) := by
    simpa [f, pathDerivative] using
      finiteAction_derivative_nonneg_ae
        N T (asMatrix T x) hfinite j k
  have hderiv :
      Filter.Eventually (fun r => r ∈ Icc s t -> 0 <= deriv f r)
        (ae volume) := by
    have hglobal :=
      (ae_restrict_iff' measurableSet_Icc).mp hderiv_restrict
    filter_upwards [hglobal] with r hr hrt
    exact hr (hsub hrt)
  have hint_nonneg : 0 <= ∫ r in s..t, deriv f r := by
    rw [intervalIntegral.integral_of_le hst]
    exact setIntegral_nonneg_ae measurableSet_Ioc
      (hderiv.mono fun r hr hrt => hr ⟨hrt.1.le, hrt.2⟩)
  have heq := hacst.integral_deriv_eq_sub
  exact sub_nonneg.mp (heq ▸ hint_nonneg)

theorem finiteRate_coordinate_continuous
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hfinite :
      poissonPathRate N T (asMatrix T x) ≠ (⊤ : ENNReal))
    (j : Server) (k : Buffer) :
    Continuous (fun t : Horizon T => x t j k) := by
  have hcont :
      ContinuousOn (fun t : Real => asMatrix T x t j k) (Icc 0 T) :=
    finiteCostPath_continuousOn N hT.le (asMatrix T x)
      (lt_top_iff_ne_top.mpr hfinite) j k
  convert hcont.domRestrict using 1
  funext t
  change x t j k = asMatrix T x (t : Real) j k
  rw [asMatrix_apply_of_mem hT.le t.property x]

theorem partitionEndpointError_le
    {T eta : Real} (P : ActionPartition T)
    (f g : Real -> Real)
    (heta : 0 <= eta) (hzero : g 0 = f 0)
    (hincrement : forall i : Fin P.intervals,
      |(g (P.right i) - g (P.left i)) -
        (f (P.right i) - f (P.left i))| <= eta) :
    forall m : Nat, m <= P.intervals ->
      |g (P.natPoint m) - f (P.natPoint m)| <= m * eta := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp [hzero]
  | succ m ih =>
      intro hm
      have hm' : m < P.intervals := Nat.lt_of_succ_le hm
      let i : Fin P.intervals := ⟨m, hm'⟩
      have hprev := ih (Nat.le_of_lt hm')
      have hinc := hincrement i
      change |g (P.natPoint (m + 1)) - f (P.natPoint (m + 1))| <=
        ((m + 1 : Nat) : Real) * eta
      rw [P.natPoint_eq_left m hm'] at hprev
      rw [P.natPoint_succ_eq_right m hm']
      have hid :
          g (P.right i) - f (P.right i) =
            (g (P.left i) - f (P.left i)) +
              ((g (P.right i) - g (P.left i)) -
                (f (P.right i) - f (P.left i))) := by
        ring
      rw [hid]
      calc
        |(g (P.left i) - f (P.left i)) +
            ((g (P.right i) - g (P.left i)) -
              (f (P.right i) - f (P.left i)))|
            <= |g (P.left i) - f (P.left i)| +
              |(g (P.right i) - g (P.left i)) -
                (f (P.right i) - f (P.left i))| := abs_add_le _ _
        _ <= m * eta + eta := add_le_add hprev hinc
        _ = ((m + 1 : Nat) : Real) * eta := by
          norm_num
          ring

theorem uniformPartition_uniformError_le
    {T eta rho : Real} (hT : 0 < T) (n : Nat)
    (f g : Real -> Real)
    (heta : 0 <= eta) (hrho : 0 <= rho)
    (hfmono : MonotoneOn f (Icc 0 T))
    (hgmono : MonotoneOn g (Icc 0 T))
    (hzero : g 0 = f 0)
    (hosc : forall i : Fin (n + 1),
      f ((uniformActionPartition T hT n).right i) -
        f ((uniformActionPartition T hT n).left i) <= rho)
    (hincrement : forall i : Fin (n + 1),
      |(g ((uniformActionPartition T hT n).right i) -
          g ((uniformActionPartition T hT n).left i)) -
        (f ((uniformActionPartition T hT n).right i) -
          f ((uniformActionPartition T hT n).left i))| <= eta) :
    forall t : Real, t ∈ Icc 0 T ->
      |g t - f t| <= (n + 1) * eta + rho := by
  let P := uniformActionPartition T hT n
  have hend := partitionEndpointError_le P f g heta hzero hincrement
  intro t ht
  by_cases htT : t < T
  · let i : Fin (n + 1) :=
      ⟨UniformPartition.cellIndex T n t,
        UniformPartition.cellIndex_lt hT n ht.1 htT⟩
    have hcell :
        t ∈ Icc (P.left i) (P.right i) := by
      exact ⟨(UniformPartition.mem_uniform_cell
        hT n ht.1 htT).1,
        (UniformPartition.mem_uniform_cell hT n ht.1 htT).2.le⟩
    have hcellSet := P.cell_subset hT.le i
    have hfleft := hfmono (hcellSet ⟨le_rfl, (P.left_lt_right i).le⟩)
      (hcellSet hcell) hcell.1
    have hfright := hfmono (hcellSet hcell)
      (hcellSet ⟨(P.left_lt_right i).le, le_rfl⟩) hcell.2
    have hgleft := hgmono (hcellSet ⟨le_rfl, (P.left_lt_right i).le⟩)
      (hcellSet hcell) hcell.1
    have hgright := hgmono (hcellSet hcell)
      (hcellSet ⟨(P.left_lt_right i).le, le_rfl⟩) hcell.2
    have hleft :
        |g (P.left i) - f (P.left i)| <= (n + 1) * eta := by
      have hi := hend i.val (Nat.le_trans (Nat.le_of_lt i.isLt)
        (Nat.le_refl (n + 1)))
      rw [P.natPoint_eq_left i.val i.isLt] at hi
      have hcast : (i.val : Real) <= (n : Real) + 1 := by
        exact_mod_cast Nat.le_of_lt i.isLt
      exact hi.trans (mul_le_mul_of_nonneg_right hcast heta)
    have hright :
        |g (P.right i) - f (P.right i)| <= (n + 1) * eta := by
      have hi := hend (i.val + 1) (Nat.add_one_le_iff.mpr i.isLt)
      rw [P.natPoint_succ_eq_right i.val i.isLt] at hi
      have hcast : ((i.val + 1 : Nat) : Real) <= (n : Real) + 1 := by
        exact_mod_cast Nat.add_one_le_iff.mpr i.isLt
      exact hi.trans (mul_le_mul_of_nonneg_right hcast heta)
    have hosc_i := hosc i
    rw [abs_le]
    constructor <;>
      rw [abs_le] at hleft hright <;>
      linarith
  · have htEq : t = T := le_antisymm ht.2 (le_of_not_gt htT)
    subst t
    have hintervals : P.intervals = n + 1 := rfl
    have hlast := hend (n + 1) (by rw [hintervals])
    rw [← hintervals] at hlast
    rw [P.natPoint_intervals] at hlast
    have hcoe : (P.intervals : Real) = (n : Real) + 1 := by
      change (((n + 1 : Nat) : Real)) = (n : Real) + 1
      push_cast
      rfl
    rw [hcoe] at hlast
    exact hlast.trans (le_add_of_nonneg_right hrho)

theorem exists_uniformPartition_targetOscillation_lt
    (N : Network Buffer Server) {T rho : Real} (hT : 0 < T)
    (hrho : 0 < rho)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hfinite :
      poissonPathRate N T (asMatrix T x) ≠ (⊤ : ENNReal)) :
    exists n : Nat, forall i : Fin (n + 1), forall j k,
      asMatrix T x ((uniformActionPartition T hT n).right i) j k -
        asMatrix T x ((uniformActionPartition T hT n).left i) j k < rho := by
  let F : Horizon T -> FiniteMatrix Server Buffer := fun t j k => x t j k
  have hF : Continuous F := by
    apply continuous_pi
    intro j
    apply continuous_pi
    intro k
    exact finiteRate_coordinate_continuous N hT x hfinite j k
  have hFu : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous hF
  obtain ⟨delta, hdelta, hmod⟩ :=
    Metric.uniformContinuous_iff.mp hFu rho hrho
  have hmesh :
      Tendsto (fun n : Nat => T / (((n + 1 : Nat) : Real)))
        atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hevent :
      Filter.Eventually
        (fun n : Nat => T / (((n + 1 : Nat) : Real)) < delta) atTop :=
    hmesh.eventually (Iio_mem_nhds hdelta)
  obtain ⟨n, hn⟩ := hevent.exists
  refine ⟨n, ?_⟩
  intro i j k
  let P := uniformActionPartition T hT n
  have hleftMem : P.left i ∈ Icc (0 : Real) T :=
    P.cell_subset hT.le i ⟨le_rfl, (P.left_lt_right i).le⟩
  have hrightMem : P.right i ∈ Icc (0 : Real) T :=
    P.cell_subset hT.le i ⟨(P.left_lt_right i).le, le_rfl⟩
  let left : Horizon T := ⟨P.left i, hleftMem⟩
  let right : Horizon T := ⟨P.right i, hrightMem⟩
  have hwidth :
      P.right i - P.left i = T / (((n + 1 : Nat) : Real)) := by
    change (((i.val + 1 : Nat) : Real) * T / (((n + 1 : Nat) : Real))) -
      (i.val : Real) * T / (((n + 1 : Nat) : Real)) =
        T / (((n + 1 : Nat) : Real))
    push_cast
    field_simp
    ring
  have hlr : dist left right < delta := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hnonneg : 0 <= P.right i - P.left i :=
      sub_nonneg.mpr (P.left_lt_right i).le
    rw [abs_sub_comm, abs_of_nonneg hnonneg, hwidth]
    exact hn
  have hmatrix : dist (F left) (F right) < rho := hmod hlr
  have hcoord : dist (F left j k) (F right j k) < rho :=
    (dist_pi_lt_iff hrho).mp ((dist_pi_lt_iff hrho).mp hmatrix j) k
  rw [Real.dist_eq] at hcoord
  have hmono := finiteRate_coordinate_monotoneOn N hT x hfinite j k
    hleftMem hrightMem (P.left_lt_right i).le
  have hmonoX : x left j k <= x right j k := by
    rw [← asMatrix_apply_of_mem hT.le hleftMem x,
      ← asMatrix_apply_of_mem hT.le hrightMem x]
    exact hmono
  simp only [F] at hcoord
  rw [abs_of_nonpos (sub_nonpos.mpr hmonoX)] at hcoord
  change asMatrix T x (P.right i) j k -
    asMatrix T x (P.left i) j k < rho
  rw [asMatrix_apply_of_mem hT.le hrightMem x,
    asMatrix_apply_of_mem hT.le hleftMem x]
  simpa [F, left, right, P] using hcoord

theorem eventually_uniformPartition_targetOscillation_lt
    (N : Network Buffer Server) {T rho : Real} (hT : 0 < T)
    (hrho : 0 < rho)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hfinite :
      poissonPathRate N T (asMatrix T x) ≠ (⊤ : ENNReal)) :
    Filter.Eventually
      (fun n : Nat => forall i : Fin (n + 1), forall j k,
        asMatrix T x ((uniformActionPartition T hT n).right i) j k -
          asMatrix T x ((uniformActionPartition T hT n).left i) j k < rho)
      atTop := by
  let F : Horizon T -> FiniteMatrix Server Buffer := fun t j k => x t j k
  have hF : Continuous F := by
    apply continuous_pi
    intro j
    apply continuous_pi
    intro k
    exact finiteRate_coordinate_continuous N hT x hfinite j k
  have hFu : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous hF
  obtain ⟨delta, hdelta, hmod⟩ :=
    Metric.uniformContinuous_iff.mp hFu rho hrho
  have hmesh :
      Tendsto (fun n : Nat => T / (((n + 1 : Nat) : Real)))
        atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hevent :
      Filter.Eventually
        (fun n : Nat => T / (((n + 1 : Nat) : Real)) < delta) atTop :=
    hmesh.eventually (Iio_mem_nhds hdelta)
  filter_upwards [hevent] with n hn
  intro i j k
  let P := uniformActionPartition T hT n
  have hleftMem : P.left i ∈ Icc (0 : Real) T :=
    P.cell_subset hT.le i ⟨le_rfl, (P.left_lt_right i).le⟩
  have hrightMem : P.right i ∈ Icc (0 : Real) T :=
    P.cell_subset hT.le i ⟨(P.left_lt_right i).le, le_rfl⟩
  let left : Horizon T := ⟨P.left i, hleftMem⟩
  let right : Horizon T := ⟨P.right i, hrightMem⟩
  have hwidth :
      P.right i - P.left i = T / (((n + 1 : Nat) : Real)) := by
    change (((i.val + 1 : Nat) : Real) * T / (((n + 1 : Nat) : Real))) -
      (i.val : Real) * T / (((n + 1 : Nat) : Real)) =
        T / (((n + 1 : Nat) : Real))
    push_cast
    field_simp
    ring
  have hlr : dist left right < delta := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hnonneg : 0 <= P.right i - P.left i :=
      sub_nonneg.mpr (P.left_lt_right i).le
    rw [abs_sub_comm, abs_of_nonneg hnonneg, hwidth]
    exact hn
  have hmatrix : dist (F left) (F right) < rho := hmod hlr
  have hcoord : dist (F left j k) (F right j k) < rho :=
    (dist_pi_lt_iff hrho).mp ((dist_pi_lt_iff hrho).mp hmatrix j) k
  rw [Real.dist_eq] at hcoord
  have hmono := finiteRate_coordinate_monotoneOn N hT x hfinite j k
    hleftMem hrightMem (P.left_lt_right i).le
  have hmonoX : x left j k <= x right j k := by
    rw [← asMatrix_apply_of_mem hT.le hleftMem x,
      ← asMatrix_apply_of_mem hT.le hrightMem x]
    exact hmono
  simp only [F] at hcoord
  rw [abs_of_nonpos (sub_nonpos.mpr hmonoX)] at hcoord
  change asMatrix T x (P.right i) j k -
    asMatrix T x (P.left i) j k < rho
  rw [asMatrix_apply_of_mem hT.le hrightMem x,
    asMatrix_apply_of_mem hT.le hleftMem x]
  simpa [F, left, right, P] using hcoord

theorem exists_late_uniformPartitionAction_toReal_ge_sub
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal))
    (n0 : Nat) {epsilon : Real} (hepsilon : 0 < epsilon) :
    exists n : Nat, n0 <= n /\
      (poissonPathRate N T A).toReal - epsilon <=
        (poissonPartitionAction N A
          (uniformActionPartition T hT n)).toReal := by
  let u : Nat -> ENNReal := fun n =>
    poissonPartitionAction N A (uniformActionPartition T hT n)
  have hu_le (n : Nat) : u n <= poissonPathRate N T A :=
    poissonPartitionAction_le_poissonPathRate N hT.le A hfinite
      (uniformActionPartition T hT n)
  have hliminf_ennreal :
      poissonPathRate N T A <= liminf u atTop :=
    poissonPathRate_le_liminf_uniformPartitionAction N hT A hfinite
  have hliminf_le :
      liminf u atTop <= poissonPathRate N T A := by
    apply liminf_le_of_le (u := u) (f := atTop) ⟨0, by simp⟩
    intro y hy
    obtain ⟨n, hn⟩ :=
      (hy.and (Filter.Eventually.of_forall hu_le)).exists
    exact hn.1.trans hn.2
  have hliminf_ne_top : liminf u atTop ≠ (⊤ : ENNReal) :=
    ne_top_of_le_ne_top hfinite hliminf_le
  have hliminf_real :
      (poissonPathRate N T A).toReal <=
        liminf (fun n => (u n).toReal) atTop := by
    rw [ENNReal.liminf_toReal_eq hfinite
      (Filter.Eventually.of_forall hu_le)]
    exact ENNReal.toReal_mono hliminf_ne_top hliminf_ennreal
  let v : Nat -> Real := fun m => (u (m + n0)).toReal
  have hv_liminf :
      (poissonPathRate N T A).toReal <= liminf v atTop := by
    rw [show liminf v atTop =
        liminf (fun n => (u n).toReal) atTop by
      exact liminf_nat_add (fun n => (u n).toReal) n0]
    exact hliminf_real
  have hv_bdd : IsBoundedUnder GE.ge atTop v := by
    refine ⟨0, ?_⟩
    simpa only [eventually_map, v] using
      (Filter.Eventually.of_forall fun m : Nat =>
        (ENNReal.toReal_nonneg :
          (0 : Real) <= (u (m + n0)).toReal))
  obtain ⟨m, hm⟩ :=
    Filter.exists_lt_of_le_liminf hv_bdd hv_liminf
      (neg_lt_zero.mpr hepsilon)
  refine ⟨m + n0, Nat.le_add_left n0 m, ?_⟩
  change (poissonPathRate N T A).toReal - epsilon <= (u (m + n0)).toReal
  rw [sub_eq_add_neg]
  exact hm.le

theorem exists_fine_actionApproximating_uniformPartition
    (N : Network Buffer Server) {T rho actionError : Real} (hT : 0 < T)
    (hrho : 0 < rho) (hactionError : 0 < actionError)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hfinite :
      poissonPathRate N T (asMatrix T x) ≠ (⊤ : ENNReal)) :
    exists n : Nat,
      (forall i : Fin (n + 1), forall j k,
        asMatrix T x ((uniformActionPartition T hT n).right i) j k -
          asMatrix T x ((uniformActionPartition T hT n).left i) j k <
            rho) /\
      (poissonPathRate N T (asMatrix T x)).toReal - actionError <=
        (poissonPartitionAction N (asMatrix T x)
          (uniformActionPartition T hT n)).toReal := by
  have hosc :=
    eventually_uniformPartition_targetOscillation_lt
      N hT hrho x hfinite
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hosc
  obtain ⟨n, hn, haction⟩ :=
    exists_late_uniformPartitionAction_toReal_ge_sub
      N hT (asMatrix T x) hfinite n0 hactionError
  exact ⟨n, hn0 n hn, haction⟩

theorem regular_calendarPath_coordinate_monotoneOn
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega) (j : Server) (k : Buffer) :
    MonotoneOn
      (fun t : Real => asMatrix T (calendarPath N T K omega) t j k)
      (Icc 0 T) := by
  intro s hs t ht hst
  let sh : Horizon T := ⟨s, hs⟩
  let th : Horizon T := ⟨t, ht⟩
  change asMatrix T (calendarPath N T K omega) s j k <=
    asMatrix T (calendarPath N T K omega) t j k
  rw [asMatrix_apply_of_mem hT hs, asMatrix_apply_of_mem hT ht,
    calendarPath_toFun_eq N T K omega hregular]
  exact calendarScaledInput_monotone N T K omega hregular.2 j k
    (show sh <= th from hst)

theorem regular_calendarPath_zero
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega) (j : Server) (k : Buffer) :
    asMatrix T (calendarPath N T K omega) 0 j k = 0 := by
  have hzero : (0 : Real) ∈ Icc (0 : Real) T := ⟨le_rfl, hT⟩
  rw [asMatrix_apply_of_mem hT hzero,
    calendarPath_toFun_eq N T K omega hregular]
  simp [calendarInputFunction, Network.calendarScaledInput,
    Network.calendarTokenCount, Network.coordinateOperationalTime,
    Network.unitPoissonCount_of_nonpos]

theorem regular_calendarPath_partitionIncrement
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega) (P : ActionPartition T)
    (j : Server) (k : Buffer) (i : Fin P.intervals) :
    asMatrix T (calendarPath N T K omega) (P.right i) j k -
        asMatrix T (calendarPath N T K omega) (P.left i) j k =
      (N.calendarTokenIncrements K P.intervals P.point omega j k i : Real) /
        ((K : Nat) : Real) := by
  have hleft := P.cell_subset hT i
    ⟨le_rfl, (P.left_lt_right i).le⟩
  have hright := P.cell_subset hT i
    ⟨(P.left_lt_right i).le, le_rfl⟩
  have htime :
      N.coordinateOperationalTime K (P.left i) j k <=
        N.coordinateOperationalTime K (P.right i) j k := by
    unfold Network.coordinateOperationalTime
    exact mul_le_mul_of_nonneg_left
      (max_le_max_right 0 (P.left_lt_right i).le)
      (mul_nonneg (by positivity) (N.phi_nonneg j k))
  have hcount :
      N.calendarTokenCount K omega (P.left i) j k <=
        N.calendarTokenCount K omega (P.right i) j k := by
    exact unitPoissonCount_monotone (omega j k) (hregular.2 j k) htime
  have hcount' :
      N.calendarTokenCount K omega (P.point i.castSucc) j k <=
        N.calendarTokenCount K omega (P.point i.succ) j k := hcount
  rw [asMatrix_apply_of_mem hT hright,
    asMatrix_apply_of_mem hT hleft,
    calendarPath_toFun_eq N T K omega hregular]
  simp only [calendarInputFunction, Network.calendarScaledInput,
    Network.calendarTokenIncrements, ActionPartition.right,
    ActionPartition.left]
  rw [Nat.cast_sub hcount']
  ring

noncomputable def roundedPartitionIncrementEvent
    (N : Network Buffer Server) {T : Real}
    (A : MatrixPath Server Buffer) (P : ActionPartition T) (K : PNat) :
    Set (Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :=
  {omega |
    (fun p i =>
      N.calendarTokenIncrements K P.intervals P.point omega p.1 p.2 i) =
    (fun p i =>
      PoissonFiniteArray.floorCount (partitionTarget A P) (K : Nat) (p, i))}

theorem eventually_floorCount_scaled_close
    {Coord : Type*} [Fintype Coord]
    (d : Coord -> Real) (hd : forall a, 0 <= d a)
    {eta : Real} (heta : 0 < eta) :
    Filter.Eventually
      (fun K : Nat => forall a,
        |(PoissonFiniteArray.floorCount d K a : Real) / K - d a| <= eta)
      atTop := by
  rw [eventually_all]
  intro a
  have ht :=
    PoissonFiniteArray.floorCount_scale_tendsto d hd a
  have hevent := ht.eventually (Metric.ball_mem_nhds (d a) heta)
  filter_upwards [hevent] with K hK
  rw [Real.dist_eq] at hK
  exact hK.le

theorem eventually_roundedIncrementEvent_subset_j1Ball
    (N : Network Buffer Server) {T epsilon rho : Real} (hT : 0 < T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hfinite :
      poissonPathRate N T (asMatrix T x) ≠ (⊤ : ENNReal))
    (n : Nat) (hrho0 : 0 <= rho) (hrho : rho < epsilon)
    (hosc : forall i : Fin (n + 1), forall j k,
      asMatrix T x ((uniformActionPartition T hT n).right i) j k -
        asMatrix T x ((uniformActionPartition T hT n).left i) j k <= rho) :
    Filter.Eventually
      (fun r : Nat =>
        Filter.Eventually
          (fun omega =>
            omega ∈ roundedPartitionIncrementEvent N (asMatrix T x)
                (uniformActionPartition T hT n) (positiveSize (r + 1)) ->
              calendarPath N T (positiveSize (r + 1)) omega ∈
                j1Ball x epsilon)
          (ae N.calendarPoissonMeasure))
      atTop := by
  let P := uniformActionPartition T hT n
  let d := partitionTarget (asMatrix T x) P
  let eta : Real := (epsilon - rho) / (2 * (n + 1))
  let delta : Real := (epsilon + rho) / 2
  have heta : 0 < eta := by
    dsimp only [eta]
    positivity
  have hd : forall a, 0 <= d a :=
    fun a => (partitionTarget_admissible N hT.le (asMatrix T x)
      hfinite P a).1
  have hfloor := eventually_floorCount_scaled_close d hd heta
  have hfloorSucc :
      Filter.Eventually
        (fun r : Nat => forall a,
          |(PoissonFiniteArray.floorCount d (r + 1) a : Real) /
              (r + 1 : Nat) - d a| <= eta)
        atTop :=
    (tendsto_add_atTop_nat 1).eventually hfloor
  filter_upwards [hfloorSucc] with r hround
  filter_upwards [regularSample_ae N] with omega hregular
  intro homega
  let y := calendarPath N T (positiveSize (r + 1)) omega
  have hyzero :
      asMatrix T y 0 = asMatrix T x 0 := by
    funext j k
    rw [regular_calendarPath_zero N hT.le
      (positiveSize (r + 1)) omega hregular j k]
    exact (poissonPathRate_ne_top_implies_valid
      N T (asMatrix T x) hfinite).2 j k |>.symm
  have hyinc : forall i : Fin (n + 1), forall j k,
      |(asMatrix T y (P.right i) j k -
          asMatrix T y (P.left i) j k) -
        (asMatrix T x (P.right i) j k -
          asMatrix T x (P.left i) j k)| <= eta := by
    intro i j k
    have hatom := congrFun
      (congrFun homega (⟨j, k⟩ :
        Sigma (fun _ : Server => Buffer))) i
    rw [regular_calendarPath_partitionIncrement N hT.le
      (positiveSize (r + 1)) omega hregular P j k i]
    rw [positiveSize_succ_val]
    rw [hatom]
    simpa only [positiveSize_succ_val, d, P, partitionTarget] using
      hround (⟨j, k⟩, i)
  have huniform : forall t : Real, t ∈ Icc 0 T -> forall j k,
      |asMatrix T y t j k - asMatrix T x t j k| <= delta := by
    intro t ht j k
    have hbound := uniformPartition_uniformError_le hT n
      (fun s => asMatrix T x s j k)
      (fun s => asMatrix T y s j k)
      heta.le hrho0
      (finiteRate_coordinate_monotoneOn N hT x hfinite j k)
      (regular_calendarPath_coordinate_monotoneOn
        N hT.le (positiveSize (r + 1)) omega hregular j k)
      (congrFun (congrFun hyzero j) k)
      (fun i => hosc i j k) (fun i => hyinc i j k) t ht
    have hcalc : (n + 1 : Real) * eta + rho = delta := by
      dsimp only [eta, delta]
      have hn : (0 : Real) < n + 1 := by positivity
      field_simp
      ring
    rw [hcalc] at hbound
    exact hbound
  have hdelta : 0 <= delta := by
    dsimp only [delta]
    linarith
  have hdeltalt : delta < epsilon := by
    dsimp only [delta]
    linarith
  apply mem_j1Ball_of_uniform x y hdelta hdeltalt
  intro t j k
  have hu := huniform (t : Real) t.property j k
  rw [asMatrix_apply_of_mem hT.le t.property y,
    asMatrix_apply_of_mem hT.le t.property x] at hu
  simpa only [abs_sub_comm] using hu

theorem roundedPartitionIncrementEvent_measure
    (N : Network Buffer Server) {T : Real}
    (A : MatrixPath Server Buffer) (P : ActionPartition T) (K : PNat) :
    N.calendarPoissonMeasure
        (roundedPartitionIncrementEvent N A P K) =
      PoissonFiniteArray.countLaw (partitionIntensity N P) K
        {PoissonFiniteArray.floorCount
          (partitionTarget A P) (K : Nat)} := by
  let target :
      (p : Sigma (fun _ : Server => Buffer)) -> Fin P.intervals -> Nat :=
    fun p i =>
      PoissonFiniteArray.floorCount
        (partitionTarget A P) (K : Nat) (p, i)
  have hlaw := partitionIncrements_hasLaw N K P
  have hmeasure := hlaw.measure_eq (measurableSet_singleton target)
  change N.calendarPoissonMeasure
      ((fun omega =>
        fun p i =>
          N.calendarTokenIncrements K P.intervals P.point
            omega p.1 p.2 i) ⁻¹' {target}) =
    partitionIncrementProductLaw N K P {target} at hmeasure
  have hevent :
      roundedPartitionIncrementEvent N A P K =
        (fun omega =>
          fun p i =>
            N.calendarTokenIncrements K P.intervals P.point
              omega p.1 p.2 i) ⁻¹' {target} := by
    ext omega
    simp only [roundedPartitionIncrementEvent, mem_setOf_eq,
      mem_preimage, mem_singleton_iff, target]
  rw [hevent]
  calc
    N.calendarPoissonMeasure
        ((fun omega =>
          fun p i =>
            N.calendarTokenIncrements K P.intervals P.point
              omega p.1 p.2 i) ⁻¹' {target}) =
      partitionIncrementProductLaw N K P {target} := hmeasure
    _ = PoissonFiniteArray.countLaw (partitionIntensity N P) K
        {PoissonFiniteArray.floorCount
          (partitionTarget A P) (K : Nat)} := by
      exact calendarIncrementProductLaw_singleton_eq_countLaw
        N K P (PoissonFiniteArray.floorCount
          (partitionTarget A P) (K : Nat))

theorem exists_j1Ball_subset_of_open
    {T : Real}
    {G : Set (Path (Buffer := Buffer) (Server := Server) T)}
    (hG : IsOpen G)
    {x : Path (Buffer := Buffer) (Server := Server) T} (hx : x ∈ G) :
    exists epsilon : Real, 0 < epsilon /\ j1Ball x epsilon ⊆ G := by
  obtain ⟨R, hR, hRG⟩ := (EMetric.isOpen_iff.mp hG) x hx
  let r : ENNReal := R ⊓ 1
  have hr : 0 < r := lt_inf_iff.mpr ⟨hR, zero_lt_one⟩
  have hrTop : r ≠ (⊤ : ENNReal) :=
    ne_top_of_le_ne_top ENNReal.one_ne_top inf_le_right
  let epsilon := r.toReal
  have hepsilon : 0 < epsilon :=
    ENNReal.toReal_pos hr.ne' hrTop
  refine ⟨epsilon, hepsilon, ?_⟩
  rw [j1Ball_eq_eball, ENNReal.ofReal_toReal hrTop]
  exact (Metric.eball_subset_eball inf_le_left).trans hRG

theorem calendarPath_open_lower_point
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    {G : Set (Path (Buffer := Buffer) (Server := Server) T)}
    (hG : IsOpen G)
    (x : Path (Buffer := Buffer) (Server := Server) T) (hx : x ∈ G)
    (hfinite :
      poissonPathRate N T (asMatrix T x) ≠ (⊤ : ENNReal)) :
    -(poissonPathRate N T (asMatrix T x) : EReal) <=
      liminf (scaledLogMass (calendarPathLaw N T) G) atTop := by
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    exists_j1Ball_subset_of_open hG hx
  let rho : Real := epsilon / 2
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  obtain ⟨n, hoscStrict, hactionApprox⟩ :=
    exists_fine_actionApproximating_uniformPartition
      N hT hrho hepsilon x hfinite
  let P := uniformActionPartition T hT n
  let q := partitionIntensity N P
  let d := partitionTarget (asMatrix T x) P
  have hadm : PoissonFiniteArray.Admissible q d :=
    partitionTarget_admissible N hT.le (asMatrix T x) hfinite P
  have hosc : forall i : Fin (n + 1), forall j k,
      asMatrix T x (P.right i) j k -
        asMatrix T x (P.left i) j k <= rho := by
    intro i j k
    exact (hoscStrict i j k).le
  have hrhoEpsilon : rho < epsilon := by
    dsimp only [rho]
    linarith
  have hinclusion :=
    eventually_roundedIncrementEvent_subset_j1Ball
      N hT x hfinite n hrho.le hrhoEpsilon hosc
  have hatom :=
    (PoissonFiniteArray.floorCount_log_atom_asymptotic q d hadm).comp
      (tendsto_add_atTop_nat 1)
  have hmono :
      Filter.Eventually
        (fun r : Nat =>
          ENNReal.log
              (PoissonFiniteArray.countLaw q (r + 1)
                {PoissonFiniteArray.floorCount d (r + 1)}) /
                ((r + 1 : Nat) : EReal) <=
            scaledLogMass (calendarPathLaw N T) G r)
        atTop := by
    filter_upwards [hinclusion] with r hr
    have hmass :
        PoissonFiniteArray.countLaw q (r + 1)
            {PoissonFiniteArray.floorCount d (r + 1)} <=
          calendarPathLaw N T (r + 1) G := by
      calc
        PoissonFiniteArray.countLaw q (r + 1)
            {PoissonFiniteArray.floorCount d (r + 1)} =
            N.calendarPoissonMeasure
              (roundedPartitionIncrementEvent N (asMatrix T x) P
                (positiveSize (r + 1))) := by
              symm
              simpa only [q, d, P, positiveSize_succ_val] using
                roundedPartitionIncrementEvent_measure
                  N (asMatrix T x) P (positiveSize (r + 1))
        _ <= N.calendarPoissonMeasure
            ((calendarPath N T (positiveSize (r + 1))) ⁻¹' G) := by
              apply measure_mono_ae
              filter_upwards [hr] with omega homega
              intro hatomMem
              exact hball (homega hatomMem)
        _ = calendarPathLaw N T (r + 1) G := by
              symm
              exact calendarPathLaw_apply N hT (r + 1) hG.measurableSet
    unfold scaledLogMass
    exact EReal.div_le_div_right_of_nonneg (by positivity)
      (ENNReal.log_le_log hmass)
  have hactionWindow :
      (poissonPathRate N T (asMatrix T x)).toReal - epsilon <=
          (poissonPartitionAction N (asMatrix T x) P).toReal /\
        poissonPartitionAction N (asMatrix T x) P <=
          poissonPathRate N T (asMatrix T x) :=
    ⟨hactionApprox,
      poissonPartitionAction_le_poissonPathRate
        N hT.le (asMatrix T x) hfinite P⟩
  have hpart := hactionWindow.2
  calc
    -(poissonPathRate N T (asMatrix T x) : EReal) <=
        -(poissonPartitionAction N (asMatrix T x) P : EReal) := by
      exact EReal.neg_le_neg_iff.mpr
        (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpart)
    _ = -(PoissonFiniteArray.action q d : EReal) := by
      rw [partitionAction_eq N hT.le (asMatrix T x) hfinite P]
    _ = liminf
        (fun r : Nat =>
          ENNReal.log
              (PoissonFiniteArray.countLaw q (r + 1)
                {PoissonFiniteArray.floorCount d (r + 1)}) /
            ((r + 1 : Nat) : EReal))
        atTop := hatom.liminf_eq.symm
    _ <= liminf (scaledLogMass (calendarPathLaw N T) G) atTop :=
      liminf_le_liminf hmono

theorem calendarPath_scaledLogMass_nonpos
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (event : Set (Path (Buffer := Buffer) (Server := Server) T))
    (r : Nat) :
    scaledLogMass (calendarPathLaw N T) event r <= 0 := by
  unfold scaledLogMass
  letI : IsProbabilityMeasure (calendarPathLaw N T (r + 1)) :=
    calendarPathLaw_isProbabilityMeasure N hT (r + 1)
  have hmass : calendarPathLaw N T (r + 1) event <= 1 := by
    calc
      calendarPathLaw N T (r + 1) event <=
          calendarPathLaw N T (r + 1) Set.univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
  have hlog :
      ENNReal.log (calendarPathLaw N T (r + 1) event) <= 0 :=
    ENNReal.log_le_zero_iff.mpr hmass
  exact EReal.div_nonpos_of_nonpos_of_nonneg hlog (by positivity)

theorem calendarPath_liminf_scaledLogMass_nonpos
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (event : Set (Path (Buffer := Buffer) (Server := Server) T)) :
    liminf (scaledLogMass (calendarPathLaw N T) event) atTop <= 0 := by
  calc
    liminf (scaledLogMass (calendarPathLaw N T) event) atTop <=
        liminf (fun _ : Nat => (0 : EReal)) atTop :=
      liminf_le_liminf (Filter.Eventually.of_forall
        (calendarPath_scaledLogMass_nonpos N hT event))
    _ = 0 := liminf_const (0 : EReal)

theorem calendarPath_neg_rateInf_le_of_pointwise
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (G : Set (Path (Buffer := Buffer) (Server := Server) T))
    (hpoint : forall x, x ∈ G ->
      -(poissonPathRate N T (asMatrix T x) : EReal) <=
        liminf (scaledLogMass (calendarPathLaw N T) G) atTop) :
    -(rateInf
        (fun x : Path (Buffer := Buffer) (Server := Server) T =>
          poissonPathRate N T (asMatrix T x))
        G : EReal) <=
      liminf (scaledLogMass (calendarPathLaw N T) G) atTop := by
  let L := liminf (scaledLogMass (calendarPathLaw N T) G) atTop
  have hL : L <= 0 := calendarPath_liminf_scaledLogMass_nonpos N hT G
  have hz : 0 <= -L := EReal.neg_nonneg.mpr hL
  have hto :
      (-L).toENNReal <=
        rateInf
          (fun x : Path (Buffer := Buffer) (Server := Server) T =>
            poissonPathRate N T (asMatrix T x))
          G := by
    unfold rateInf
    apply le_sInf
    intro y hy
    rcases hy with ⟨x, hxG, rfl⟩
    have hneg := hpoint x hxG
    have hrev :
        -L <= (poissonPathRate N T (asMatrix T x) : EReal) := by
      simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hneg
    simpa only [EReal.toENNReal_coe] using
      EReal.toENNReal_le_toENNReal hrev
  have hcoe :
      -L <=
        (rateInf
          (fun x : Path (Buffer := Buffer) (Server := Server) T =>
            poissonPathRate N T (asMatrix T x))
          G : EReal) := by
    rw [← EReal.coe_toENNReal hz]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hto
  simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hcoe

theorem calendarPath_open_lower_bound
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) :
    CalendarPathOpenLowerBound N T := by
  intro G hG
  apply calendarPath_neg_rateInf_le_of_pointwise N hT G
  intro x hxG
  by_cases hfinite :
      poissonPathRate N T (asMatrix T x) = (⊤ : ENNReal)
  · simp [hfinite]
  · exact calendarPath_open_lower_point N hT hG x hxG hfinite

end PoissonSamplePath
end StateDepMOR


open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set

namespace StateDepMOR.PoissonPolygonalBridge

noncomputable section

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

open PoissonSamplePath

abbrev Coord (P : ActionPartition T) :=
  PoissonSamplePath.PartitionCoord
    (Buffer := Buffer) (Server := Server) P

/-- The clipped affine coordinate on one partition cell. -/
def cellRamp {T : Real} (P : ActionPartition T)
    (i : Fin P.intervals) (t : Real) : Real :=
  max 0 (min 1 ((t - P.left i) / P.width i))

theorem cellRamp_nonneg {T : Real} (P : ActionPartition T)
    (i : Fin P.intervals) (t : Real) :
    0 <= cellRamp P i t :=
  le_max_left _ _

theorem cellRamp_le_one {T : Real} (P : ActionPartition T)
    (i : Fin P.intervals) (t : Real) :
    cellRamp P i t <= 1 := by
  unfold cellRamp
  exact max_le zero_le_one (min_le_left _ _)

theorem cellRamp_eq_zero_of_le_left {T : Real} (P : ActionPartition T)
    (i : Fin P.intervals) {t : Real} (ht : t <= P.left i) :
    cellRamp P i t = 0 := by
  rw [cellRamp, max_eq_left]
  exact (min_le_right _ _).trans
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (P.width_pos i).le)

theorem cellRamp_eq_one_of_right_le {T : Real} (P : ActionPartition T)
    (i : Fin P.intervals) {t : Real} (ht : P.right i <= t) :
    cellRamp P i t = 1 := by
  rw [cellRamp, min_eq_left, max_eq_right zero_le_one]
  rw [le_div_iff₀ (P.width_pos i)]
  unfold ActionPartition.width
  linarith

theorem cellRamp_eq_of_mem {T : Real} (P : ActionPartition T)
    (i : Fin P.intervals) {t : Real}
    (ht : t ∈ Icc (P.left i) (P.right i)) :
    cellRamp P i t = (t - P.left i) / P.width i := by
  unfold cellRamp
  rw [min_eq_right, max_eq_right]
  · exact div_nonneg (sub_nonneg.mpr ht.1) (P.width_pos i).le
  · rw [div_le_one (P.width_pos i)]
    exact sub_le_sub_right ht.2 _

theorem continuous_cellRamp {T : Real} (P : ActionPartition T)
    (i : Fin P.intervals) :
    Continuous (cellRamp P i) := by
  unfold cellRamp
  fun_prop

theorem cellRamp_lipschitz {T : Real} (P : ActionPartition T)
    (i : Fin P.intervals) :
    LipschitzWith ‖(P.width i)⁻¹‖₊ (cellRamp P i) := by
  have hdiv :
      LipschitzWith ‖(P.width i)⁻¹‖₊
        (fun t : Real => (t - P.left i) / P.width i) := by
    simpa [div_eq_inv_mul, Function.comp_def]
      using (lipschitzWith_smul (P.width i)⁻¹).comp
        (LipschitzWith.id.sub (LipschitzWith.const (P.left i)))
  change LipschitzWith ‖(P.width i)⁻¹‖₊
    (fun t => max 0 (min 1 ((t - P.left i) / P.width i)))
  exact (hdiv.const_min 1).const_max 0

/-- The ambient real-indexed polygonal interpolation of a finite array. -/
def interpolation {T : Real} (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real) :
    MatrixPath Server Buffer :=
  fun t j k =>
    ∑ i : Fin P.intervals, z (⟨j, k⟩, i) * cellRamp P i t

theorem continuous_interpolation_coordinate {T : Real}
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (j : Server) (k : Buffer) :
    Continuous (fun t => interpolation P z t j k) := by
  unfold interpolation
  apply continuous_finset_sum
  intro i hi
  exact continuous_const.mul (continuous_cellRamp P i)

theorem interpolation_coordinate_lipschitz {T : Real}
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (j : Server) (k : Buffer) :
    exists K : NNReal,
      LipschitzWith K (fun t => interpolation P z t j k) := by
  unfold interpolation
  have hsum :
      exists K : NNReal, LipschitzWith K
        (∑ i : Fin P.intervals,
          fun t => z (⟨j, k⟩, i) * cellRamp P i t) := by
    refine Finset.sum_induction
      (s := Finset.univ)
      (f := fun i => fun t => z (⟨j, k⟩, i) * cellRamp P i t)
      (p := fun f : Real -> Real => exists K : NNReal, LipschitzWith K f)
      ?_ ?_ ?_
    · intro f g hf hg
      rcases hf with ⟨Kf, hf⟩
      rcases hg with ⟨Kg, hg⟩
      exact ⟨Kf + Kg, hf.add hg⟩
    · exact ⟨0, LipschitzWith.const 0⟩
    · intro i hi
      refine ⟨‖z (⟨j, k⟩, i)‖₊ * ‖(P.width i)⁻¹‖₊, ?_⟩
      change LipschitzWith _ ((fun x : Real =>
        z (⟨j, k⟩, i) * x) ∘ cellRamp P i)
      exact (lipschitzWith_smul (z (⟨j, k⟩, i))).comp
        (cellRamp_lipschitz P i)
  rw [show (fun t => ∑ i : Fin P.intervals,
      z (⟨j, k⟩, i) * cellRamp P i t) =
      ∑ i : Fin P.intervals,
        fun t => z (⟨j, k⟩, i) * cellRamp P i t by
    funext t
    simp]
  exact hsum

theorem interpolation_nonneg {T : Real} (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (hz : forall a, 0 <= z a) (t : Real) (j : Server) (k : Buffer) :
    0 <= interpolation P z t j k := by
  unfold interpolation
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hz (⟨j, k⟩, i)) (cellRamp_nonneg P i t)

theorem interpolation_absolutelyContinuous {T : Real}
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real) :
    IsAbsolutelyContinuousMatrixPath T (interpolation P z) := by
  intro j k
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  exact (interpolation_coordinate_lipschitz P z j k).choose_spec.lipschitzOnWith

theorem interpolation_zero {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (j : Server) (k : Buffer) :
    interpolation P z 0 j k = 0 := by
  unfold interpolation
  apply Finset.sum_eq_zero
  intro i hi
  rw [cellRamp_eq_zero_of_le_left]
  · simp
  · exact ((P.cell_subset hT i)
      ⟨le_rfl, (P.left_lt_right i).le⟩).1

abbrev NonnegativeArray (P : ActionPartition T) :=
  {z : Coord (Buffer := Buffer) (Server := Server) P -> Real //
    forall a, 0 <= z a}

/-- The polygonal interpolation bundled as the repository's nonnegative path. -/
def polygonalPath {T : Real} (P : ActionPartition T)
    (z : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P) :
    Path (Buffer := Buffer) (Server := Server) T where
  toFun := fun t => interpolation P z.1 t
  nonnegative := fun t j k => interpolation_nonneg P z.1 z.2 t j k
  rightContinuous := by
    intro t ht
    have hcont : Continuous (fun t : Horizon T => interpolation P z.1 t) := by
      apply continuous_pi
      intro j
      apply continuous_pi
      intro k
      exact (continuous_interpolation_coordinate P z.1 j k).comp
        continuous_subtype_val
    exact hcont.continuousAt.continuousWithinAt
  leftLimits := by
    intro t ht
    refine ⟨interpolation P z.1 t, ?_⟩
    have hcont : Continuous (fun t : Horizon T => interpolation P z.1 t) := by
      apply continuous_pi
      intro j
      apply continuous_pi
      intro k
      exact (continuous_interpolation_coordinate P z.1 j k).comp
        continuous_subtype_val
    exact hcont.continuousAt.mono_left inf_le_left

@[simp]
theorem polygonalPath_apply {T : Real} (P : ActionPartition T)
    (z : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P)
    (t : Horizon T) (j : Server) (k : Buffer) :
    polygonalPath P z t j k = interpolation P z.1 t j k :=
  rfl

theorem polygonalPath_startsAtZero {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (z : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P)
    (j : Server) (k : Buffer) :
    polygonalPath P z ⟨0, le_rfl, hT⟩ j k = 0 :=
  interpolation_zero hT P z.1 j k

theorem asMatrix_polygonalPath_absolutelyContinuous {T : Real}
    (hT : 0 <= T) (P : ActionPartition T)
    (z : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P) :
    IsAbsolutelyContinuousMatrixPath T (asMatrix T (polygonalPath P z)) := by
  intro j k
  have hEq :
      (fun t => asMatrix T (polygonalPath P z) t j k) =
        fun t => interpolation P z.1 (max 0 (min t T)) j k := by
    funext t
    simp [asMatrix, hT, clampToHorizon]
  rw [hEq]
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  have hclamp : LipschitzWith 1 (fun t : Real => max 0 (min t T)) :=
    by simpa [min_comm] using (LipschitzWith.id.const_min T).const_max 0
  exact ((interpolation_coordinate_lipschitz P z.1 j k).choose_spec.comp
    hclamp).lipschitzOnWith

def arrayChord {T : Real} (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (i : Fin P.intervals) : Server -> Buffer -> Real :=
  fun j k => z (⟨j, k⟩, i) / P.width i

theorem right_le_left_of_lt {T : Real} (P : ActionPartition T)
    {i q : Fin P.intervals} (hqi : q < i) :
    P.right q <= P.left i := by
  apply P.strictMono_point.monotone
  exact Fin.mk_le_mk.mpr (Nat.succ_le_of_lt hqi)

theorem right_le_left_of_lt' {T : Real} (P : ActionPartition T)
    {i q : Fin P.intervals} (hiq : i < q) :
    P.right i <= P.left q := by
  apply P.strictMono_point.monotone
  exact Fin.mk_le_mk.mpr (Nat.succ_le_of_lt hiq)

theorem hasDerivAt_cellRamp {T : Real} (P : ActionPartition T)
    (i : Fin P.intervals) {t : Real}
    (ht : t ∈ Ioo (P.left i) (P.right i)) :
    HasDerivAt (cellRamp P i) (1 / P.width i) t := by
  have hbase :
      HasDerivAt (fun s : Real => (s - P.left i) / P.width i)
        (1 / P.width i) t :=
    ((hasDerivAt_id t).sub_const (P.left i)).div_const (P.width i)
  apply hbase.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact cellRamp_eq_of_mem P i ⟨hs.1.le, hs.2.le⟩

theorem hasDerivAt_cellRamp_of_before {T : Real}
    (P : ActionPartition T) (i : Fin P.intervals) {t : Real}
    (ht : t < P.left i) :
    HasDerivAt (cellRamp P i) (0 : Real) t := by
  have hbase : HasDerivAt (fun _ : Real => (0 : Real)) (0 : Real) t :=
    hasDerivAt_const t (0 : Real)
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds ht] with s hs
  show cellRamp P i s = (0 : Real)
  exact cellRamp_eq_zero_of_le_left P i hs.le

theorem hasDerivAt_cellRamp_of_after {T : Real}
    (P : ActionPartition T) (i : Fin P.intervals) {t : Real}
    (ht : P.right i < t) :
    HasDerivAt (cellRamp P i) (0 : Real) t := by
  have hbase : HasDerivAt (fun _ : Real => (1 : Real)) (0 : Real) t :=
    hasDerivAt_const t (1 : Real)
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with s hs
  show cellRamp P i s = (1 : Real)
  exact cellRamp_eq_one_of_right_le P i hs.le

theorem hasDerivAt_interpolation_of_mem_cell {T : Real}
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (i : Fin P.intervals) {t : Real}
    (ht : t ∈ Ioo (P.left i) (P.right i))
    (j : Server) (k : Buffer) :
    HasDerivAt (fun s => interpolation P z s j k)
      (arrayChord P z i j k) t := by
  unfold interpolation arrayChord
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun q s => z (⟨j, k⟩, q) * cellRamp P q s)
    (A' := fun q => if q = i then z (⟨j, k⟩, i) / P.width i else 0)
    (x := t) (fun q hq => by
      by_cases hqi : q = i
      · subst q
        simpa [div_eq_mul_inv, mul_comm] using
          (hasDerivAt_cellRamp P i ht).const_mul (z (⟨j, k⟩, i))
      · rcases lt_or_gt_of_ne hqi with hq_lt | hi_lt
        · have hafter : P.right q < t :=
            (right_le_left_of_lt P hq_lt).trans_lt ht.1
          simpa [hqi] using
            (hasDerivAt_cellRamp_of_after P q hafter).const_mul
              (z (⟨j, k⟩, q))
        · have hbefore : t < P.left q :=
            ht.2.trans_le (right_le_left_of_lt' P hi_lt)
          simpa [hqi] using
            (hasDerivAt_cellRamp_of_before P q hbefore).const_mul
              (z (⟨j, k⟩, q)))
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using hsum

theorem pathDerivative_interpolation_of_mem_cell {T : Real}
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (i : Fin P.intervals) {t : Real}
    (ht : t ∈ Ioo (P.left i) (P.right i)) :
    pathDerivative (interpolation P z) t = arrayChord P z i := by
  funext j k
  exact (hasDerivAt_interpolation_of_mem_cell P z i ht j k).deriv

theorem pathDerivative_interpolation_ae_cell {T : Real}
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (i : Fin P.intervals) :
    ∀ᵐ t ∂volume.restrict (Icc (P.left i) (P.right i)),
      pathDerivative (interpolation P z) t = arrayChord P z i := by
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  have hleft : ∀ᵐ t : Real ∂volume, t ≠ P.left i := by
    simp [ae_iff, measure_singleton]
  have hright : ∀ᵐ t : Real ∂volume, t ≠ P.right i := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hleft, hright] with t htl htr
  intro ht
  exact pathDerivative_interpolation_of_mem_cell P z i
    ⟨ht.1.lt_of_ne' htl, ht.2.lt_of_ne htr⟩

theorem intervals_pos {T : Real} (hT : 0 < T)
    (P : ActionPartition T) :
    0 < P.intervals := by
  apply Nat.pos_of_ne_zero
  intro hn
  have hfin : Fin.last P.intervals = 0 := by
    apply Fin.eq_of_val_eq
    simp [hn]
  have hlast := P.point_last
  rw [hfin, P.point_zero] at hlast
  linarith

theorem exists_mem_partition_cell {T t : Real} (hT : 0 < T)
    (P : ActionPartition T) (ht : t ∈ Ioo (0 : Real) T) :
    exists i : Fin P.intervals, t ∈ Ico (P.left i) (P.right i) := by
  classical
  let S : Finset (Fin (P.intervals + 1)) :=
    Finset.univ.filter fun q => t < P.point q
  have hS : S.Nonempty := by
    refine ⟨Fin.last P.intervals, ?_⟩
    simp [S, P.point_last, ht.2]
  let q : Fin (P.intervals + 1) := S.min' hS
  have hqS : q ∈ S := Finset.min'_mem S hS
  have hqright : t < P.point q := (Finset.mem_filter.mp hqS).2
  have hqpos : 0 < q.val := by
    by_contra h
    have hq0 : q = 0 := Fin.eq_of_val_eq (Nat.eq_zero_of_not_pos h)
    rw [hq0, P.point_zero] at hqright
    exact (not_lt_of_ge ht.1.le) hqright
  have hqle : q.val - 1 < P.intervals := by omega
  let i : Fin P.intervals := ⟨q.val - 1, hqle⟩
  have hi_succ : i.succ = q := by
    apply Fin.eq_of_val_eq
    dsimp [i]
    omega
  refine ⟨i, ?_, ?_⟩
  · by_contra hleft
    have hlt : t < P.point i.castSucc := lt_of_not_ge hleft
    have himem : i.castSucc ∈ S := by
      simp [S, hlt]
    have hmin := Finset.min'_le S i.castSucc himem
    change q.val <= i.val at hmin
    dsimp [i] at hmin
    omega
  · simpa [ActionPartition.right, hi_succ] using hqright

theorem hasDerivAt_asMatrix_polygonalPath_of_mem_cell {T : Real}
    (hT : 0 < T) (P : ActionPartition T)
    (z : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P)
    (i : Fin P.intervals) {t : Real}
    (ht : t ∈ Ioo (P.left i) (P.right i))
    (j : Server) (k : Buffer) :
    HasDerivAt
      (fun s => asMatrix T (polygonalPath P z) s j k)
      (arrayChord P z.1 i j k) t := by
  have hcell := P.cell_subset hT.le i
  have htglobal : t ∈ Ioo (0 : Real) T :=
    ⟨(hcell ⟨ht.1.le, ht.2.le⟩).1.lt_of_ne' (by
        intro h
        subst t
        exact (not_lt_of_ge
          ((hcell ⟨le_rfl, (P.left_lt_right i).le⟩).1)) ht.1),
      (hcell ⟨ht.1.le, ht.2.le⟩).2.lt_of_ne (by
        intro h
        subst t
        exact (not_lt_of_ge
          ((hcell ⟨(P.left_lt_right i).le, le_rfl⟩).2)) ht.2)⟩
  have hinterp :=
    hasDerivAt_interpolation_of_mem_cell P z.1 i ht j k
  apply hinterp.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds htglobal.1 htglobal.2] with s hs
  rw [asMatrix_apply_of_mem hT.le ⟨hs.1.le, hs.2.le⟩]
  rfl

theorem pathDerivative_asMatrix_polygonalPath_of_mem_cell {T : Real}
    (hT : 0 < T) (P : ActionPartition T)
    (z : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P)
    (i : Fin P.intervals) {t : Real}
    (ht : t ∈ Ioo (P.left i) (P.right i)) :
    pathDerivative (asMatrix T (polygonalPath P z)) t =
      arrayChord P z.1 i := by
  funext j k
  exact (hasDerivAt_asMatrix_polygonalPath_of_mem_cell
    hT P z i ht j k).deriv

theorem pathDerivative_asMatrix_polygonalPath_ae_cell {T : Real}
    (hT : 0 < T) (P : ActionPartition T)
    (z : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P)
    (i : Fin P.intervals) :
    ∀ᵐ t ∂volume.restrict (Icc (P.left i) (P.right i)),
      pathDerivative (asMatrix T (polygonalPath P z)) t =
        arrayChord P z.1 i := by
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  have hleft : ∀ᵐ t : Real ∂volume, t ≠ P.left i := by
    simp [ae_iff, measure_singleton]
  have hright : ∀ᵐ t : Real ∂volume, t ≠ P.right i := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hleft, hright] with t htl htr
  intro ht
  exact pathDerivative_asMatrix_polygonalPath_of_mem_cell hT P z i
    ⟨ht.1.lt_of_ne' htl, ht.2.lt_of_ne htr⟩

def arrayStepRate (N : Network Buffer Server) {T : Real}
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (t : Real) : ENNReal :=
  ∑ i : Fin P.intervals,
    (Ico (P.left i) (P.right i)).indicator
      (fun _ => N.localRate (arrayChord P z i)) t

theorem arrayStepRate_eq_of_mem_cell
    (N : Network Buffer Server) {T t : Real}
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (i : Fin P.intervals) (ht : t ∈ Ico (P.left i) (P.right i)) :
    arrayStepRate N P z t = N.localRate (arrayChord P z i) := by
  classical
  unfold arrayStepRate
  calc
    ∑ q : Fin P.intervals,
        (Ico (P.left q) (P.right q)).indicator
          (fun _ => N.localRate (arrayChord P z q)) t =
        (Ico (P.left i) (P.right i)).indicator
          (fun _ => N.localRate (arrayChord P z i)) t := by
      rw [Finset.sum_eq_single i]
      · intro q hq hqi
        rw [Set.indicator_of_notMem]
        intro hqt
        rcases lt_or_gt_of_ne hqi with hq_lt | hi_lt
        · exact (not_lt_of_ge
            ((right_le_left_of_lt P hq_lt).trans ht.1)) hqt.2
        · exact (not_lt_of_ge
            ((right_le_left_of_lt' P hi_lt).trans hqt.1)) ht.2
      · simp
    _ = N.localRate (arrayChord P z i) := by simp [ht]

theorem localRate_pathDerivative_eq_arrayStepRate_ae
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (P : ActionPartition T)
    (z : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      N.localRate
          (pathDerivative (asMatrix T (polygonalPath P z)) t) =
        arrayStepRate N P z.1 t := by
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  have hpoints :
      ∀ᵐ t : Real ∂volume, forall q : Fin (P.intervals + 1),
        t ≠ P.point q := by
    simp only [ae_all_iff]
    intro q
    simp [ae_iff, measure_singleton]
  filter_upwards [hpoints] with t htpoints
  intro ht
  have hinterior : t ∈ Ioo (0 : Real) T := by
    refine ⟨ht.1.lt_of_ne' ?_, ht.2.lt_of_ne ?_⟩
    · simpa [P.point_zero] using htpoints 0
    · simpa [P.point_last] using htpoints (Fin.last P.intervals)
  rcases exists_mem_partition_cell hT P hinterior with ⟨i, hi⟩
  have hiopen : t ∈ Ioo (P.left i) (P.right i) :=
    ⟨hi.1.lt_of_ne' (by
        change t ≠ P.point i.castSucc
        exact htpoints i.castSucc),
      hi.2⟩
  rw [pathDerivative_asMatrix_polygonalPath_of_mem_cell
    hT P z i hiopen]
  exact (arrayStepRate_eq_of_mem_cell N P z.1 i hi).symm

theorem lintegral_arrayStepRate
    (N : Network Buffer Server) {T : Real}
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real) :
    ∫⁻ t, arrayStepRate N P z t =
      ∑ i : Fin P.intervals,
        ENNReal.ofReal (P.width i) *
          N.localRate (arrayChord P z i) := by
  classical
  unfold arrayStepRate
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [lintegral_indicator measurableSet_Ico,
      setLIntegral_const, Real.volume_Ico]
    simp [ActionPartition.width, mul_comm]
  · intro i hi
    exact measurable_const.indicator measurableSet_Ico

theorem lintegral_arrayStepRate_Icc
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real) :
    ∫⁻ t in Icc 0 T, arrayStepRate N P z t =
      ∑ i : Fin P.intervals,
        ENNReal.ofReal (P.width i) *
          N.localRate (arrayChord P z i) := by
  rw [← lintegral_arrayStepRate N P z]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Icc (0 : Real) T
  · simp [ht]
  · have hzero : arrayStepRate N P z t = 0 := by
      unfold arrayStepRate
      apply Finset.sum_eq_zero
      intro i hi
      rw [Set.indicator_of_notMem]
      intro hcell
      exact ht (P.cell_subset hT i ⟨hcell.1, hcell.2.le⟩)
    simp [ht, hzero]

theorem poissonPathRate_polygonal_eq_sum
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (P : ActionPartition T)
    (z : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P) :
    poissonPathRate N T (asMatrix T (polygonalPath P z)) =
      ∑ i : Fin P.intervals,
        ENNReal.ofReal (P.width i) *
          N.localRate (arrayChord P z.1 i) := by
  rw [poissonPathRate, if_pos]
  · calc
      (∫⁻ t in Icc 0 T,
          N.localRate
            (pathDerivative (asMatrix T (polygonalPath P z)) t)) =
          ∫⁻ t in Icc 0 T, arrayStepRate N P z.1 t := by
            apply lintegral_congr_ae
            exact localRate_pathDerivative_eq_arrayStepRate_ae N hT P z
      _ = _ := lintegral_arrayStepRate_Icc N hT.le P z.1
  · constructor
    · exact asMatrix_polygonalPath_absolutelyContinuous hT.le P z
    · intro j k
      rw [asMatrix_apply_of_mem hT.le ⟨le_rfl, hT.le⟩]
      exact polygonalPath_startsAtZero hT.le P z j k

theorem poissonCost_scale_width
    {w nominal candidate : Real} (hw : 0 < w)
    (hnominal : 0 <= nominal) (hcandidate : 0 <= candidate)
    (hzero : nominal = 0 -> candidate = 0) :
    poissonCost (w * nominal) candidate =
      ENNReal.ofReal w * poissonCost nominal (candidate / w) := by
  rcases hnominal.eq_or_lt with rfl | hnominal_pos
  · have hc : candidate = 0 := hzero rfl
    subst candidate
    simp [poissonCost_zero_zero, hw.le]
  · have hw_nominal : 0 < w * nominal := mul_pos hw hnominal_pos
    have hcdiv : 0 <= candidate / w :=
      div_nonneg hcandidate hw.le
    rw [poissonCost_of_nominal_pos hw_nominal hcandidate,
      poissonCost_of_nominal_pos hnominal_pos hcdiv,
      ← ENNReal.ofReal_mul hw.le]
    congr 1
    have hscale :=
      poissonCostReal_scale w nominal (candidate / w) hw hnominal_pos
    rw [mul_div_cancel₀ candidate hw.ne'] at hscale
    exact hscale

theorem finiteArray_action_eq_sum
    (N : Network Buffer Server) {T : Real}
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (hz : PoissonFiniteArray.Admissible
      (PoissonSamplePath.partitionIntensity N P) z) :
    PoissonFiniteArray.action
        (PoissonSamplePath.partitionIntensity N P) z =
      ∑ i : Fin P.intervals,
        ENNReal.ofReal (P.width i) *
          N.localRate (arrayChord P z i) := by
  classical
  unfold PoissonFiniteArray.action
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sigma]
  unfold PoissonSamplePath.partitionIntensity Network.localRate arrayChord
  have hterm (j : Server) (k : Buffer) (i : Fin P.intervals) :
      poissonCost
          ((Real.toNNReal (P.width i) *
            Real.toNNReal (N.phi j k) : NNReal) : Real)
          (z (⟨j, k⟩, i)) =
        ENNReal.ofReal (P.width i) *
          poissonCost (N.phi j k) (z (⟨j, k⟩, i) / P.width i) := by
    rw [NNReal.coe_mul,
      Real.coe_toNNReal (P.width i) (P.width_pos i).le,
      Real.coe_toNNReal (N.phi j k) (N.phi_nonneg j k)]
    apply poissonCost_scale_width (P.width_pos i) (N.phi_nonneg j k)
      (hz (⟨j, k⟩, i)).1
    intro hphi
    apply (hz (⟨j, k⟩, i)).2
    unfold PoissonSamplePath.partitionIntensity
    simp [hphi]
  simp_rw [hterm]
  calc
    ∑ j : Server, ∑ k : Buffer, ∑ i : Fin P.intervals,
        ENNReal.ofReal (P.width i) *
          poissonCost (N.phi j k) (z (⟨j, k⟩, i) / P.width i) =
      ∑ j : Server, ∑ i : Fin P.intervals, ∑ k : Buffer,
        ENNReal.ofReal (P.width i) *
          poissonCost (N.phi j k) (z (⟨j, k⟩, i) / P.width i) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_comm]
    _ = ∑ i : Fin P.intervals, ∑ j : Server, ∑ k : Buffer,
        ENNReal.ofReal (P.width i) *
          poissonCost (N.phi j k) (z (⟨j, k⟩, i) / P.width i) := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin P.intervals,
        ENNReal.ofReal (P.width i) *
          ∑ j : Server, ∑ k : Buffer,
            poissonCost (N.phi j k)
              (z (⟨j, k⟩, i) / P.width i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.mul_sum]

theorem poissonPathRate_polygonal
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (hz : PoissonFiniteArray.Admissible
      (PoissonSamplePath.partitionIntensity N P) z) :
    poissonPathRate N T
        (asMatrix T
          (polygonalPath P
            ⟨z, fun a => (hz a).1⟩)) =
      PoissonFiniteArray.action
        (PoissonSamplePath.partitionIntensity N P) z := by
  rw [poissonPathRate_polygonal_eq_sum N hT P
    ⟨z, fun a => (hz a).1⟩]
  exact (finiteArray_action_eq_sum N P z hz).symm

theorem interpolation_sub_abs_le
    {T : Real} (P : ActionPartition T)
    (z w : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P)
    (t : Real) (j : Server) (k : Buffer) :
    |interpolation P z.1 t j k - interpolation P w.1 t j k| <=
      (P.intervals : Real) * dist z w := by
  have hcoord (i : Fin P.intervals) :
      |(z.1 (⟨j, k⟩, i) - w.1 (⟨j, k⟩, i)) * cellRamp P i t| <=
        dist z w := by
    calc
      |(z.1 (⟨j, k⟩, i) - w.1 (⟨j, k⟩, i)) *
          cellRamp P i t| =
          |z.1 (⟨j, k⟩, i) - w.1 (⟨j, k⟩, i)| *
            cellRamp P i t := by
              rw [abs_mul, abs_of_nonneg (cellRamp_nonneg P i t)]
      _ <= |z.1 (⟨j, k⟩, i) - w.1 (⟨j, k⟩, i)| := by
        nlinarith [cellRamp_nonneg P i t, cellRamp_le_one P i t,
          abs_nonneg (z.1 (⟨j, k⟩, i) - w.1 (⟨j, k⟩, i))]
      _ = dist (z.1 (⟨j, k⟩, i)) (w.1 (⟨j, k⟩, i)) := by
        rw [Real.dist_eq]
      _ <= dist z.1 w.1 :=
        (dist_pi_le_iff dist_nonneg).mp le_rfl
          ((⟨j, k⟩, i) :
            Coord (Buffer := Buffer) (Server := Server) P)
      _ = dist z w := rfl
  rw [show interpolation P z.1 t j k - interpolation P w.1 t j k =
      ∑ i : Fin P.intervals,
        (z.1 (⟨j, k⟩, i) - w.1 (⟨j, k⟩, i)) *
          cellRamp P i t by
    unfold interpolation
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  calc
    |∑ i : Fin P.intervals,
        (z.1 (⟨j, k⟩, i) - w.1 (⟨j, k⟩, i)) *
          cellRamp P i t| <=
      ∑ i : Fin P.intervals,
        |(z.1 (⟨j, k⟩, i) - w.1 (⟨j, k⟩, i)) *
          cellRamp P i t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _i : Fin P.intervals, dist z w :=
      Finset.sum_le_sum fun i hi => hcoord i
    _ = (P.intervals : Real) * dist z w := by simp

theorem j1EDist_polygonalPath_le
    {T : Real} (P : ActionPartition T)
    (z w : NonnegativeArray
      (Buffer := Buffer) (Server := Server) P) :
    j1EDist (polygonalPath P z) (polygonalPath P w) <=
      ENNReal.ofReal ((P.intervals : Real) * dist z w) := by
  refine (inf_le_left : symmetricJ1EDist
      (polygonalPath P z) (polygonalPath P w) ⊓ 1 <=
        symmetricJ1EDist (polygonalPath P z) (polygonalPath P w)).trans ?_
  refine symmetricJ1EDist_le_j1Cost
    (polygonalPath P z) (polygonalPath P w)
    (identityTimeChange T) |>.trans ?_
  apply max_le
  · simp [timeError, identityTimeChange]
  · unfold pathError
    apply iSup_le
    intro t
    apply iSup_le
    intro j
    apply iSup_le
    intro k
    apply ENNReal.ofReal_le_ofReal
    simpa [identityTimeChange] using
      interpolation_sub_abs_le P z w (t : Real) j k

theorem lipschitzWith_polygonalPath {T : Real} (P : ActionPartition T) :
    LipschitzWith (P.intervals : NNReal)
      (polygonalPath
        (Buffer := Buffer) (Server := Server) P) := by
  intro z w
  change j1EDist (polygonalPath P z) (polygonalPath P w) <=
    ((P.intervals : NNReal) : ENNReal) * edist z w
  have hnat :
      ((P.intervals : NNReal) : ENNReal) =
        ENNReal.ofReal (P.intervals : Real) := by simp
  rw [hnat, edist_dist, ← ENNReal.ofReal_mul]
  · simpa using j1EDist_polygonalPath_le P z w
  · positivity

theorem continuous_polygonalPath {T : Real} (P : ActionPartition T) :
    Continuous
      (polygonalPath
        (Buffer := Buffer) (Server := Server) P) :=
  (lipschitzWith_polygonalPath P).continuous

theorem measurable_polygonalPath {T : Real} (P : ActionPartition T) :
    Measurable
      (polygonalPath
        (Buffer := Buffer) (Server := Server) P) :=
  (continuous_polygonalPath P).measurable

def cellLeftTime {T : Real} (hT : 0 <= T)
    (P : ActionPartition T) (i : Fin P.intervals) :
    Horizon T :=
  ⟨P.left i, (P.cell_subset hT i
    ⟨le_rfl, (P.left_lt_right i).le⟩)⟩

def cellRightTime {T : Real} (hT : 0 <= T)
    (P : ActionPartition T) (i : Fin P.intervals) :
    Horizon T :=
  ⟨P.right i, (P.cell_subset hT i
    ⟨(P.left_lt_right i).le, le_rfl⟩)⟩

def pathPartitionArray {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    Coord (Buffer := Buffer) (Server := Server) P -> Real :=
  fun a =>
    x (cellRightTime hT P a.2) a.1.1 a.1.2 -
      x (cellLeftTime hT P a.2) a.1.1 a.1.2

theorem pathPartitionArray_nonneg {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hmono : forall j k,
      Monotone (fun t : Horizon T => x t j k)) :
    forall a, 0 <= pathPartitionArray hT P x a := by
  intro a
  unfold pathPartitionArray
  exact sub_nonneg.mpr (hmono a.1.1 a.1.2
    (show cellLeftTime hT P a.2 <= cellRightTime hT P a.2 by
      exact (P.left_lt_right a.2).le))

theorem interpolation_cell_increment
    {T : Real} (hT : 0 <= T) (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (i : Fin P.intervals) (j : Server) (k : Buffer) :
    interpolation P z (P.right i) j k -
        interpolation P z (P.left i) j k =
      z (⟨j, k⟩, i) := by
  have hac := (interpolation_absolutelyContinuous P z j k).mono
    (show uIcc (P.left i) (P.right i) ⊆ uIcc (0 : Real) T by
      rw [uIcc_of_le (P.left_lt_right i).le, uIcc_of_le hT]
      exact P.cell_subset hT i)
  have hfund := hac.integral_deriv_eq_sub
  rw [← hfund]
  have hae :=
    (ae_restrict_iff' measurableSet_Icc).mp
      (pathDerivative_interpolation_ae_cell P z i)
  rw [intervalIntegral.integral_congr_ae]
  · rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, arrayChord]
    exact mul_div_cancel₀ (z (⟨j, k⟩, i)) (P.width_pos i).ne'
  · filter_upwards [hae] with t ht
    intro htu
    have htIcc : t ∈ Icc (P.left i) (P.right i) := by
      rw [uIoc_of_le (P.left_lt_right i).le] at htu
      exact ⟨htu.1.le, htu.2⟩
    exact congrFun (congrFun (ht htIcc) j) k

theorem interpolation_left_eq_of_increment
    {T : Real} (hT : 0 <= T) (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (A : Real -> Real) (j : Server) (k : Buffer)
    (hA0 : A 0 = 0)
    (hz : forall i : Fin P.intervals,
      z (⟨j, k⟩, i) = A (P.right i) - A (P.left i))
    (i : Fin P.intervals) :
    interpolation P z (P.left i) j k = A (P.left i) := by
  have hF0 : interpolation P z 0 j k = 0 :=
    interpolation_zero hT P z j k
  generalize hn : i.val = n
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
      cases n with
      | zero =>
          have hi0 : i = ⟨0, by omega⟩ := Fin.eq_of_val_eq hn
          have hleft : P.left i = 0 := by
            rw [hi0]
            exact P.point_zero
          rw [hleft, hF0, hA0]
      | succ n =>
          have hnlt : n < P.intervals := by omega
          let q : Fin P.intervals := ⟨n, hnlt⟩
          have hqi : q.val = n := rfl
          have hleft : P.right q = P.left i := by
            unfold ActionPartition.right ActionPartition.left
            congr 1
            apply Fin.eq_of_val_eq
            dsimp [q]
            omega
          have hiq :=
            ih n (Nat.lt_succ_self n) q hqi
          have hinc := interpolation_cell_increment hT P z q j k
          rw [hz q, hleft] at hinc
          linarith

theorem interpolation_sub_left_of_mem_cell
    {T : Real} (hT : 0 <= T) (P : ActionPartition T)
    (z : Coord (Buffer := Buffer) (Server := Server) P -> Real)
    (i : Fin P.intervals) {t : Real}
    (ht : t ∈ Icc (P.left i) (P.right i))
    (j : Server) (k : Buffer) :
    interpolation P z t j k - interpolation P z (P.left i) j k =
      ((t - P.left i) / P.width i) * z (⟨j, k⟩, i) := by
  have hsub : uIcc (P.left i) t ⊆ uIcc (0 : Real) T := by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    intro s hs
    exact P.cell_subset hT i ⟨hs.1, hs.2.trans ht.2⟩
  have hac :=
    (interpolation_absolutelyContinuous P z j k).mono hsub
  have hfund := hac.integral_deriv_eq_sub
  rw [← hfund]
  have hae :=
    (ae_restrict_iff' measurableSet_Icc).mp
      (pathDerivative_interpolation_ae_cell P z i)
  calc
    (∫ s in P.left i..t,
        deriv (fun r => interpolation P z r j k) s) =
        ∫ _s in P.left i..t, z (⟨j, k⟩, i) / P.width i := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [hae] with s hs
          intro hsu
          have hsIcc : s ∈ Icc (P.left i) (P.right i) := by
            rw [uIoc_of_le ht.1] at hsu
            exact ⟨hsu.1.le, hsu.2.trans ht.2⟩
          exact congrFun (congrFun (hs hsIcc) j) k
    _ = ((t - P.left i) / P.width i) * z (⟨j, k⟩, i) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

theorem exists_mem_partition_closed_cell {T : Real} (hT : 0 < T)
    (P : ActionPartition T) {t : Real} (ht : t ∈ Icc (0 : Real) T) :
    exists i : Fin P.intervals, t ∈ Icc (P.left i) (P.right i) := by
  by_cases ht0 : t = 0
  · subst t
    let i : Fin P.intervals := ⟨0, intervals_pos hT P⟩
    refine ⟨i, ?_⟩
    have hleft : P.left i = 0 := by
      unfold ActionPartition.left
      rw [show i.castSucc = 0 by
        apply Fin.eq_of_val_eq
        rfl]
      exact P.point_zero
    exact ⟨hleft.le, (hleft ▸ P.left_lt_right i).le⟩
  by_cases htT : t = T
  · subst t
    have hn : 0 < P.intervals := intervals_pos hT P
    let i : Fin P.intervals := ⟨P.intervals - 1, by omega⟩
    refine ⟨i, ?_⟩
    have hright : P.right i = T := by
      unfold ActionPartition.right
      rw [show i.succ = Fin.last P.intervals by
        apply Fin.eq_of_val_eq
        dsimp [i]
        omega]
      exact P.point_last
    exact ⟨(hright ▸ P.left_lt_right i).le, hright.ge⟩
  rcases exists_mem_partition_cell hT P
    ⟨ht.1.lt_of_ne' ht0, ht.2.lt_of_ne htT⟩ with ⟨i, hi⟩
  exact ⟨i, hi.1, hi.2.le⟩

def interpolatedPath {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hmono : forall j k,
      Monotone (fun t : Horizon T => x t j k)) :
    Path (Buffer := Buffer) (Server := Server) T :=
  polygonalPath P
    ⟨pathPartitionArray hT P x,
      pathPartitionArray_nonneg hT P x hmono⟩

def maximumPartitionIncrement {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T) : Real :=
  let values :=
    Finset.univ.image (pathPartitionArray hT P x)
  (insert 0 values).max' (by simp)

theorem pathPartitionArray_le_maximum {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (a : Coord (Buffer := Buffer) (Server := Server) P) :
    pathPartitionArray hT P x a <=
      maximumPartitionIncrement hT P x := by
  unfold maximumPartitionIncrement
  apply Finset.le_max'
  simp

theorem maximumPartitionIncrement_nonneg {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    0 <= maximumPartitionIncrement hT P x := by
  unfold maximumPartitionIncrement
  apply Finset.le_max'
  simp

theorem interpolation_pathPartitionArray_left
    {T : Real} (hT : 0 < T) (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hzero : forall j k, x ⟨0, le_rfl, hT.le⟩ j k = 0)
    (i : Fin P.intervals) (j : Server) (k : Buffer) :
    interpolation P (pathPartitionArray hT.le P x) (P.left i) j k =
      x (cellLeftTime hT.le P i) j k := by
  let A : Real -> Real := fun t => asMatrix T x t j k
  have hA0 : A 0 = 0 := by
    dsimp [A]
    rw [asMatrix_apply_of_mem hT.le ⟨le_rfl, hT.le⟩ x]
    exact hzero j k
  have hz (q : Fin P.intervals) :
      pathPartitionArray hT.le P x (⟨j, k⟩, q) =
        A (P.right q) - A (P.left q) := by
    unfold pathPartitionArray
    dsimp [A]
    rw [asMatrix_apply_of_mem (T := T) (t := P.right q) hT.le
        (cellRightTime hT.le P q).property x,
      asMatrix_apply_of_mem (T := T) (t := P.left q) hT.le
        (cellLeftTime hT.le P q).property x]
    rfl
  have hleft := interpolation_left_eq_of_increment
    hT.le P (pathPartitionArray hT.le P x) A j k hA0 hz i
  rw [hleft]
  dsimp [A]
  rw [asMatrix_apply_of_mem (T := T) (t := P.left i) hT.le
    (cellLeftTime hT.le P i).property x]
  rfl

theorem uniform_interpolatedPath_error_le
    {T : Real} (hT : 0 < T) (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hmono : forall j k,
      Monotone (fun t : Horizon T => x t j k))
    (hzero : forall j k, x ⟨0, le_rfl, hT.le⟩ j k = 0)
    (t : Horizon T) (j : Server) (k : Buffer) :
    |x t j k - interpolatedPath hT.le P x hmono t j k| <=
      maximumPartitionIncrement hT.le P x := by
  rcases exists_mem_partition_closed_cell hT P t.property with ⟨i, hi⟩
  let z := pathPartitionArray hT.le P x
  let inc := z (⟨j, k⟩, i)
  let left := x (cellLeftTime hT.le P i) j k
  let right := x (cellRightTime hT.le P i) j k
  have hleft_t : cellLeftTime hT.le P i <= t := hi.1
  have ht_right : t <= cellRightTime hT.le P i := hi.2
  have hxlow : left <= x t j k := hmono j k hleft_t
  have hxhigh : x t j k <= right := hmono j k ht_right
  have hinc : inc = right - left := rfl
  have hinc_nonneg : 0 <= inc := by
    rw [hinc]
    exact sub_nonneg.mpr (hmono j k
      (show cellLeftTime hT.le P i <= cellRightTime hT.le P i by
        exact (P.left_lt_right i).le))
  let theta := ((t : Real) - P.left i) / P.width i
  have htheta0 : 0 <= theta :=
    div_nonneg (sub_nonneg.mpr hi.1) (P.width_pos i).le
  have htheta1 : theta <= 1 := by
    rw [div_le_one (P.width_pos i)]
    exact sub_le_sub_right hi.2 _
  have hanchor :=
    interpolation_pathPartitionArray_left hT P x hzero i j k
  have haffine := interpolation_sub_left_of_mem_cell hT.le P z i hi j k
  have hpoly :
      interpolatedPath hT.le P x hmono t j k =
        left + theta * inc := by
    change interpolation P z (t : Real) j k = left + theta * inc
    dsimp [theta, inc]
    rw [← haffine, hanchor]
    ring
  have hpolylow : left <= interpolatedPath hT.le P x hmono t j k := by
    rw [hpoly]
    nlinarith
  have hpolyhigh : interpolatedPath hT.le P x hmono t j k <= right := by
    rw [hpoly, hinc]
    nlinarith
  have habs :
      |x t j k - interpolatedPath hT.le P x hmono t j k| <= inc := by
    rw [abs_le]
    constructor <;> linarith
  exact habs.trans (pathPartitionArray_le_maximum hT.le P x (⟨j, k⟩, i))

theorem j1EDist_interpolatedPath_le
    {T : Real} (hT : 0 < T) (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (hmono : forall j k,
      Monotone (fun t : Horizon T => x t j k))
    (hzero : forall j k, x ⟨0, le_rfl, hT.le⟩ j k = 0) :
    j1EDist x (interpolatedPath hT.le P x hmono) <=
      ENNReal.ofReal (maximumPartitionIncrement hT.le P x) := by
  refine (inf_le_left : symmetricJ1EDist x
      (interpolatedPath hT.le P x hmono) ⊓ 1 <=
        symmetricJ1EDist x (interpolatedPath hT.le P x hmono)).trans ?_
  refine symmetricJ1EDist_le_j1Cost x
    (interpolatedPath hT.le P x hmono) (identityTimeChange T) |>.trans ?_
  apply max_le
  · simp [timeError, identityTimeChange]
  · unfold pathError
    apply iSup_le
    intro t
    apply iSup_le
    intro j
    apply iSup_le
    intro k
    apply ENNReal.ofReal_le_ofReal
    simpa [identityTimeChange] using
      uniform_interpolatedPath_error_le hT P x hmono hzero t j k

end

end StateDepMOR.PoissonPolygonalBridge


open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory ProbabilityTheory Set

namespace StateDepMOR.PoissonSamplePath

universe u v w

/-! ## Compact diagonal unions -/

theorem isCompact_compactFibers_approaching
    {X : Type w} [PseudoMetricSpace X] [T2Space X]
    (C : Set X) (F : Nat -> Set X) (epsilon : Nat -> Real)
    (hC : IsCompact C) (hF : forall n, IsCompact (F n))
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hnear : forall n, F n <= Metric.cthickening (epsilon n) C) :
    IsCompact (Set.union C (Set.iUnion F)) := by
  rw [isCompact_iff_isSeqCompact]
  intro x hx
  by_cases hCne : C.Nonempty
  · let G : Nat -> Set X
      | 0 => Set.union C (F 0)
      | n + 1 => F (n + 1)
    have hGcompact : forall n, IsCompact (G n) := by
      intro n
      cases n with
      | zero => exact hC.union (hF 0)
      | succ n => exact hF (n + 1)
    have hGnear : forall n, G n <= Metric.cthickening (epsilon n) C := by
      intro n y hy
      cases n with
      | zero =>
          rcases hy with hyC | hyF
          · exact Metric.closure_subset_cthickening (epsilon 0) C
              (subset_closure hyC)
          · exact hnear 0 hyF
      | succ n => exact hnear (n + 1) hy
    have hxG : forall n, exists i, x n ∈ G i := by
      intro n
      rcases hx n with hnC | hnF
      · exact ⟨0, Or.inl hnC⟩
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hnF
        cases i with
        | zero => exact ⟨0, Or.inr hi⟩
        | succ i => exact ⟨i + 1, hi⟩
    choose fiber hfiber using hxG
    by_cases htop : Tendsto fiber atTop atTop
    · choose center hcenter hdist using fun n =>
        hC.exists_infEDist_eq_edist hCne (x n)
      obtain ⟨c, hcC, phi, hphi, hcphi⟩ :=
        hC.tendsto_subseq (fun n => hcenter n)
      have heps :
          Tendsto (fun n => ENNReal.ofReal (epsilon (fiber (phi n))))
            atTop (nhds 0) := by
        have hreal :
            Tendsto (fun n => epsilon (fiber (phi n))) atTop (nhds 0) :=
          hepsilon.comp (htop.comp hphi.tendsto_atTop)
        simpa using ENNReal.tendsto_ofReal hreal
      have hxdist :
          Tendsto (fun n => edist (x (phi n)) (center (phi n)))
            atTop (nhds 0) := by
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
          tendsto_const_nhds heps
          (Eventually.of_forall fun _ => bot_le)
          (Eventually.of_forall fun n => by
            rw [← hdist]
            exact hGnear (fiber (phi n)) (hfiber (phi n)))
      have hxphi : Tendsto (x ∘ phi) atTop (nhds c) := by
        rw [tendsto_iff_edist_tendsto_0]
        have hcenterDist :
            Tendsto (fun n => edist (center (phi n)) c) atTop (nhds 0) := by
          simpa only [Function.comp_apply] using
            (tendsto_iff_edist_tendsto_0.mp hcphi)
        have hsum := hxdist.add hcenterDist
        exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
          tendsto_const_nhds (by
            simpa only [zero_add, Function.comp_apply] using hsum)
          (Eventually.of_forall fun _ => bot_le)
          (Eventually.of_forall fun n => edist_triangle _ _ _)
      exact ⟨c, Or.inl hcC, phi, hphi, hxphi⟩
    · rw [tendsto_atTop_atTop] at htop
      push_neg at htop
      obtain ⟨b, hb⟩ := htop
      have hfreq : Filter.Frequently (fun n => fiber n <= b) atTop := by
        rw [frequently_atTop']
        intro i
        obtain ⟨a, hia, ha⟩ := hb (i + 1)
        exact ⟨a, by omega, by omega⟩
      let D : Set X := Set.iUnion fun i : Fin (b + 1) => G i
      have hD : IsCompact D := isCompact_iUnion fun i => hGcompact i
      have hxD : Filter.Frequently (fun n => x n ∈ D) atTop := by
        exact hfreq.mono fun n hn =>
          mem_iUnion.mpr
            ⟨(⟨fiber n, Nat.lt_succ_iff.mpr hn⟩ : Fin (b + 1)), hfiber n⟩
      obtain ⟨c, hcD, phi, hphi, hcphi⟩ :=
        hD.tendsto_subseq' hxD
      have hcUnion : c ∈ Set.union C (Set.iUnion F) := by
        obtain ⟨i, hi⟩ := mem_iUnion.mp hcD
        cases i using Fin.cases with
        | zero =>
            change c ∈ G 0 at hi
            change c ∈ Set.union C (F 0) at hi
            rcases hi with hiC | hiF
            · exact Or.inl hiC
            · exact Or.inr (mem_iUnion.mpr ⟨0, hiF⟩)
        | succ i => exact Or.inr (mem_iUnion.mpr ⟨i + 1, hi⟩)
      exact ⟨c, hcUnion, phi, hphi, hcphi⟩
  · have hCempty : C = ∅ := not_nonempty_iff_eq_empty.mp hCne
    have hFempty : forall n, F n = ∅ := by
      intro n
      ext y
      simp only [mem_empty_iff_false, iff_false]
      intro hy
      have hbad := hnear n hy
      simpa [hCempty] using hbad
    have hbad := hx 0
    rcases hbad with hbad | hbad
    · rw [hCempty] at hbad
      exact False.elim hbad
    · obtain ⟨n, hn⟩ := mem_iUnion.mp hbad
      rw [hFempty n] at hn
      exact False.elim hn

end StateDepMOR.PoissonSamplePath

namespace StateDepMOR.PoissonSamplePath

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

/-- A partition point bundled as an element of the time horizon. -/
def actionPartitionTime {T : Real} (hT : 0 <= T)
    (P : ActionPartition T) (i : Fin (P.intervals + 1)) : Horizon T :=
  ⟨P.point i, by
    constructor
    · rw [← P.point_zero]
      exact P.strictMono_point.monotone (Fin.zero_le i)
    · calc
        P.point i <= P.point (Fin.last P.intervals) :=
          P.strictMono_point.monotone (Fin.le_last i)
        _ = T := P.point_last⟩

@[simp]
theorem actionPartitionTime_coe {T : Real} (hT : 0 <= T)
    (P : ActionPartition T) (i : Fin (P.intervals + 1)) :
    (actionPartitionTime hT P i : Real) = P.point i :=
  rfl

/-- Flattened increments of a path on an action partition. -/
def pathPartitionArray {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real :=
  fun a =>
    x (actionPartitionTime hT P a.2.succ) a.1.1 a.1.2 -
      x (actionPartitionTime hT P a.2.castSucc) a.1.1 a.1.2

def flattenPartitionCounts {T : Real} (P : ActionPartition T)
    (x : (p : Sigma (fun _ : Server => Buffer)) -> Fin P.intervals -> Nat) :
    PartitionCoord (Buffer := Buffer) (Server := Server) P -> Nat :=
  fun a => x a.1 a.2

def flattenPartitionReals {T : Real} (P : ActionPartition T)
    (x : (p : Sigma (fun _ : Server => Buffer)) -> Fin P.intervals -> Real) :
    PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real :=
  fun a => x a.1 a.2

theorem measurable_flattenPartitionCounts {T : Real}
    (P : ActionPartition T) :
    Measurable
      (flattenPartitionCounts
        (Buffer := Buffer) (Server := Server) P) := by
  fun_prop

theorem measurable_flattenPartitionReals {T : Real}
    (P : ActionPartition T) :
    Measurable
      (flattenPartitionReals
        (Buffer := Buffer) (Server := Server) P) := by
  apply measurable_pi_iff.mpr
  intro a
  exact (measurable_pi_apply a.2).comp (measurable_pi_apply a.1)

theorem partitionIncrementProductLaw_map_flatten
    (N : Network Buffer Server) (K : PNat) {T : Real}
    (P : ActionPartition T) :
    Measure.map
        (flattenPartitionCounts
          (Buffer := Buffer) (Server := Server) P)
        (partitionIncrementProductLaw N K P) =
      PoissonFiniteArray.countLaw (partitionIntensity N P) K := by
  classical
  apply Measure.ext_of_singleton
  intro n
  rw [Measure.map_apply
    (measurable_flattenPartitionCounts P)
    (MeasurableSet.singleton n)]
  have hpre :
      flattenPartitionCounts
          (Buffer := Buffer) (Server := Server) P ⁻¹' {n} =
        {fun p i => n (p, i)} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hx
      funext p i
      exact congrFun hx (p, i)
    · intro hx
      subst x
      rfl
  rw [hpre]
  exact calendarIncrementProductLaw_singleton_eq_countLaw N K P n

theorem flatten_scaleCalendarIncrementVector {T : Real}
    (P : ActionPartition T) (K : PNat)
    (x : (p : Sigma (fun _ : Server => Buffer)) ->
      Fin P.intervals -> Nat) :
    flattenPartitionReals
        (Buffer := Buffer) (Server := Server) P
        (Network.scaleCalendarIncrementVector K x) =
      PoissonFiniteArray.scale K
        (flattenPartitionCounts
          (Buffer := Buffer) (Server := Server) P x) := by
  funext a
  rfl

theorem scaledPartitionProductLaw_map_flatten
    (N : Network Buffer Server) (K : PNat) {T : Real}
    (P : ActionPartition T) :
    Measure.map
        (flattenPartitionReals
          (Buffer := Buffer) (Server := Server) P)
        (Measure.map
          (Network.scaleCalendarIncrementVector
            (Buffer := Buffer) (Server := Server) K
            (n := P.intervals))
          (partitionIncrementProductLaw N K P)) =
      PoissonFiniteArray.scaledLaw (partitionIntensity N P) K := by
  rw [Measure.map_map
    (measurable_flattenPartitionReals P)
    (Network.measurable_scaleCalendarIncrementVector K P.intervals)]
  unfold PoissonFiniteArray.scaledLaw
  rw [← partitionIncrementProductLaw_map_flatten N K P]
  rw [Measure.map_map
    (by fun_prop)
    (measurable_flattenPartitionCounts P)]
  apply Measure.map_congr
  filter_upwards with x
  exact flatten_scaleCalendarIncrementVector P K x

/-- The actual calendar path's grid increments have the exact scaled
finite independent Poisson law. -/
theorem calendarPath_partitionArray_hasLaw
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (K : PNat) (P : ActionPartition T) :
    HasLaw
      (fun omega : Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        pathPartitionArray hT P (calendarPath N T K omega))
      (PoissonFiniteArray.scaledLaw (partitionIntensity N P) K)
      N.calendarPoissonMeasure := by
  let times : Fin (P.intervals + 1) -> Horizon T :=
    actionPartitionTime hT P
  have hraw :=
    calendarPath_partitionIncrements_hasLaw N K P.intervals times
      (by simp [times, actionPartitionTime, P.point_zero])
      (P.strictMono_point.monotone)
  have hflat :
      HasLaw
        (flattenPartitionReals
          (Buffer := Buffer) (Server := Server) P)
        (Measure.map
          (flattenPartitionReals
            (Buffer := Buffer) (Server := Server) P)
          (Measure.map
            (Network.scaleCalendarIncrementVector
              (Buffer := Buffer) (Server := Server) K
              (n := P.intervals))
            (Network.calendarIncrementProductLaw N K P.intervals
              P.point P.strictMono_point.monotone)))
        (Measure.map
          (Network.scaleCalendarIncrementVector
            (Buffer := Buffer) (Server := Server) K
            (n := P.intervals))
          (Network.calendarIncrementProductLaw N K P.intervals
            P.point P.strictMono_point.monotone)) :=
    ⟨(measurable_flattenPartitionReals P).aemeasurable, rfl⟩
  have hcomp := hflat.fun_comp hraw
  rw [show Network.calendarIncrementProductLaw N K P.intervals
      P.point P.strictMono_point.monotone =
      partitionIncrementProductLaw N K P by rfl] at hcomp
  rw [scaledPartitionProductLaw_map_flatten N K P] at hcomp
  apply hcomp.congr
  filter_upwards with omega
  rfl

end StateDepMOR.PoissonSamplePath

namespace StateDepMOR.PoissonSamplePath

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

set_option maxRecDepth 10000

/-! ## Finite-partition polygonal interpolation -/

/-- The nonnegative cell velocity associated with a finite increment array.
The `max` makes the construction a total path-valued map; on Poisson
increment arrays it is definitionally redundant. -/
noncomputable def partitionArrayVelocity {T : Real}
    (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real)
    (t : Real) (j : Server) (k : Buffer) : Real :=
  ∑ i : Fin P.intervals,
    (Ico (P.left i) (P.right i)).indicator
      (fun _ => max
        (z ((⟨j, k⟩ : Sigma fun _ : Server => Buffer), i)) 0 /
          P.width i) t

theorem partitionArrayVelocity_nonnegative {T : Real}
    (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real)
    (t : Real) (j : Server) (k : Buffer) :
    0 <= partitionArrayVelocity P z t j k := by
  classical
  unfold partitionArrayVelocity
  apply Finset.sum_nonneg
  intro i hi
  by_cases ht : t ∈ Ico (P.left i) (P.right i)
  · rw [Set.indicator_of_mem ht]
    exact div_nonneg (le_max_right _ _) (P.width_pos i).le
  · rw [Set.indicator_of_notMem ht]

theorem integrable_partitionArrayVelocity {T : Real}
    (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real)
    (j : Server) (k : Buffer) :
    Integrable (fun t => partitionArrayVelocity P z t j k) volume := by
  classical
  unfold partitionArrayVelocity
  let f : Fin P.intervals -> Real -> Real := fun i =>
    (Ico (P.left i) (P.right i)).indicator
      (fun _ => max
        (z ((⟨j, k⟩ : Sigma fun _ : Server => Buffer), i)) 0 /
          P.width i)
  have hf : forall i, i ∈ (Finset.univ : Finset (Fin P.intervals)) ->
      Integrable (f i) volume := by
    intro i hi
    apply IntegrableOn.integrable_indicator
    · exact integrableOn_const (measure_Ico_lt_top.ne)
    · exact measurableSet_Ico
  have h := MeasureTheory.integrable_finsetSum'
    (Finset.univ : Finset (Fin P.intervals)) hf
  have heq :
      (fun t => ∑ i : Fin P.intervals,
        (Ico (P.left i) (P.right i)).indicator
          (fun _ => max
            (z ((⟨j, k⟩ : Sigma fun _ : Server => Buffer), i)) 0 /
              P.width i) t) =
        ∑ i : Fin P.intervals, f i := by
    funext t
    simp [f]
  rw [heq]
  simpa using h

/-- Cumulative integral of the cell velocity.  It is the linear
interpolation of the cumulative increments. -/
noncomputable def partitionArrayPrimitive {T : Real}
    (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real)
    (t : Real) (j : Server) (k : Buffer) : Real :=
  ∫ s in (0 : Real)..t, partitionArrayVelocity P z s j k

theorem partitionArrayPrimitive_nonnegative {T : Real}
    (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real)
    {t : Real} (ht : 0 <= t) (j : Server) (k : Buffer) :
    0 <= partitionArrayPrimitive P z t j k := by
  unfold partitionArrayPrimitive
  exact intervalIntegral.integral_nonneg_of_forall ht
    (fun s => partitionArrayVelocity_nonnegative P z s j k)

theorem partitionArrayPrimitive_absolutelyContinuous {T : Real}
    (hT : 0 <= T) (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real)
    (j : Server) (k : Buffer) :
    AbsolutelyContinuousOnInterval
      (fun t => partitionArrayPrimitive P z t j k) 0 T := by
  unfold partitionArrayPrimitive
  exact
    (integrable_partitionArrayVelocity P z j k).intervalIntegrable
      |>.absolutelyContinuousOnInterval_intervalIntegral
        (by simp [uIcc_of_le hT, hT])

theorem continuous_partitionArrayPrimitive_horizon {T : Real}
    (hT : 0 <= T) (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real)
    (j : Server) (k : Buffer) :
    Continuous (fun t : Horizon T =>
      partitionArrayPrimitive P z t j k) := by
  have hc : ContinuousOn
      (fun t => partitionArrayPrimitive P z t j k) (Icc 0 T) := by
    simpa [uIcc_of_le hT] using
      (partitionArrayPrimitive_absolutelyContinuous hT P z j k).continuousOn
  exact hc.comp_continuous continuous_subtype_val (fun t => t.property)

/-- The absolutely continuous path obtained by linearly interpolating the
cumulative finite-partition increments. -/
noncomputable def partitionArrayPath {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real) :
    Path (Buffer := Buffer) (Server := Server) T where
  toFun := fun t j k => partitionArrayPrimitive P z t j k
  nonnegative := fun t j k =>
    partitionArrayPrimitive_nonnegative P z t.property.1 j k
  rightContinuous := by
    intro t ht
    rw [continuousWithinAt_pi]
    intro j
    rw [continuousWithinAt_pi]
    intro k
    exact
      (continuous_partitionArrayPrimitive_horizon hT P z j k).continuousAt
        |>.continuousWithinAt
  leftLimits := by
    intro t ht
    refine ⟨fun j k => partitionArrayPrimitive P z t j k, ?_⟩
    apply tendsto_pi_nhds.mpr
    intro j
    apply tendsto_pi_nhds.mpr
    intro k
    exact
      (continuous_partitionArrayPrimitive_horizon hT P z j k).continuousAt
        |>.continuousWithinAt

@[simp]
theorem partitionArrayPath_apply {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real)
    (t : Horizon T) (j : Server) (k : Buffer) :
    partitionArrayPath hT P z t j k =
      partitionArrayPrimitive P z t j k :=
  rfl

theorem partitionArrayPath_valid {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real) :
    IsAbsolutelyContinuousMatrixPath T
        (asMatrix T (partitionArrayPath hT P z)) /\
      forall j k,
        asMatrix T (partitionArrayPath hT P z) 0 j k = 0 := by
  constructor
  · intro j k
    have hac :=
      partitionArrayPrimitive_absolutelyContinuous hT P z j k
    rw [absolutelyContinuousOnInterval_iff] at hac ⊢
    intro epsilon hepsilon
    obtain ⟨delta, hdelta, hacdelta⟩ := hac epsilon hepsilon
    refine ⟨delta, hdelta, ?_⟩
    intro E hE hlength
    have hpoint (q : Real) (hq : q ∈ uIcc (0 : Real) T) :
        asMatrix T (partitionArrayPath hT P z) q j k =
          partitionArrayPrimitive P z q j k := by
      have hq' : q ∈ Icc (0 : Real) T := by
        simpa [uIcc_of_le hT] using hq
      rw [asMatrix_apply_of_mem hT hq']
      rfl
    calc
      ∑ i ∈ Finset.range E.1,
          dist
            (asMatrix T (partitionArrayPath hT P z) (E.2 i).1 j k)
            (asMatrix T (partitionArrayPath hT P z) (E.2 i).2 j k) =
          ∑ i ∈ Finset.range E.1,
            dist
              (partitionArrayPrimitive P z (E.2 i).1 j k)
              (partitionArrayPrimitive P z (E.2 i).2 j k) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hpoint _ (hE.1 i hi).1, hpoint _ (hE.1 i hi).2]
      _ < epsilon := hacdelta E hE hlength
  · intro j k
    rw [asMatrix_apply_of_mem hT ⟨le_rfl, hT⟩]
    simp [partitionArrayPath_apply, partitionArrayPrimitive]

theorem pathDerivative_partitionArrayPath_ae {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T),
      pathDerivative (asMatrix T (partitionArrayPath hT P z)) t =
        fun j k => partitionArrayVelocity P z t j k := by
  have hzero : ∀ᵐ t : Real ∂volume, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have htop : ∀ᵐ t : Real ∂volume, t ≠ T := by
    simp [ae_iff, measure_singleton]
  have hderiv (j : Server) (k : Buffer) :
      ∀ᵐ t : Real ∂volume,
        deriv (fun s => partitionArrayPrimitive P z s j k) t =
          partitionArrayVelocity P z t j k := by
    have hae := LocallyIntegrable.ae_hasDerivAt_integral
      (integrable_partitionArrayVelocity P z j k).locallyIntegrable
    filter_upwards [hae] with t ht
    exact (ht 0).deriv
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hzero, htop,
    eventually_all.mpr (fun j => eventually_all.mpr (hderiv j))] with
      t ht0 htT htder ht
  funext j k
  unfold pathDerivative
  have hinterior : t ∈ Ioo (0 : Real) T :=
    ⟨ht.1.lt_of_ne' ht0, ht.2.lt_of_ne htT⟩
  have heq :
      (fun s => asMatrix T (partitionArrayPath hT P z) s j k) =ᶠ[nhds t]
        (fun s => partitionArrayPrimitive P z s j k) := by
    filter_upwards [Icc_mem_nhds hinterior.1 hinterior.2] with s hs
    rw [asMatrix_apply_of_mem hT hs]
    rfl
  rw [heq.deriv_eq, htder j k]

/-- Piecewise-constant Poisson action density of an increment array. -/
noncomputable def partitionArrayStepCost
    (N : Network Buffer Server) {T : Real} (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real)
    (t : Real) : ENNReal :=
  ∑ i : Fin P.intervals,
    (Ico (P.left i) (P.right i)).indicator
      (fun _ => N.localRate (fun j k =>
        z ((⟨j, k⟩ : Sigma fun _ : Server => Buffer), i) / P.width i)) t

theorem partitionArrayVelocity_uniform_eq
    {T : Real} (hT : 0 < T) (n : Nat)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server)
      (uniformActionPartition T hT n) -> Real)
    (hz : forall a, 0 <= z a)
    {t : Real} (ht0 : 0 <= t) (htT : t < T) :
    partitionArrayVelocity (uniformActionPartition T hT n) z t =
      fun j k =>
        z ((⟨j, k⟩ : Sigma fun _ : Server => Buffer),
          (⟨UniformPartition.cellIndex T n t,
            UniformPartition.cellIndex_lt hT n ht0 htT⟩ :
              Fin (n + 1))) /
          (uniformActionPartition T hT n).width
            ⟨UniformPartition.cellIndex T n t,
              UniformPartition.cellIndex_lt hT n ht0 htT⟩ := by
  classical
  let P := uniformActionPartition T hT n
  let i : Fin P.intervals :=
    ⟨UniformPartition.cellIndex T n t,
      UniformPartition.cellIndex_lt hT n ht0 htT⟩
  have hmem : t ∈ Ico (P.left i) (P.right i) :=
    UniformPartition.mem_uniform_cell hT n ht0 htT
  funext j k
  unfold partitionArrayVelocity
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hmem, max_eq_left (hz ((⟨j, k⟩, i)))]
    rfl
  · intro q hq hqi
    rw [Set.indicator_of_notMem]
    intro hmemq
    rcases lt_or_gt_of_ne hqi with hqi | hqi
    · have hright_le_left : P.right q <= P.left i := by
        change ((q.val + 1 : Nat) : Real) * T / (n + 1 : Nat) <=
          (i.val : Real) * T / (n + 1 : Nat)
        have hnat : q.val + 1 <= i.val := Nat.add_one_le_iff.mpr hqi
        gcongr
      exact (not_lt_of_ge hright_le_left)
        (hmem.1.trans_lt hmemq.2)
    · have hright_le_left : P.right i <= P.left q := by
        change ((i.val + 1 : Nat) : Real) * T / (n + 1 : Nat) <=
          (q.val : Real) * T / (n + 1 : Nat)
        have hnat : i.val + 1 <= q.val := Nat.add_one_le_iff.mpr hqi
        gcongr
      exact (not_lt_of_ge hright_le_left)
        (hmemq.1.trans_lt hmem.2)
  · exact fun hi => (hi (Finset.mem_univ i)).elim

theorem partitionArrayStepCost_uniform_eq
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) (n : Nat)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server)
      (uniformActionPartition T hT n) -> Real)
    {t : Real} (ht0 : 0 <= t) (htT : t < T) :
    partitionArrayStepCost N (uniformActionPartition T hT n) z t =
      N.localRate (fun j k =>
        z ((⟨j, k⟩ : Sigma fun _ : Server => Buffer),
          (⟨UniformPartition.cellIndex T n t,
            UniformPartition.cellIndex_lt hT n ht0 htT⟩ :
              Fin (n + 1))) /
          (uniformActionPartition T hT n).width
            ⟨UniformPartition.cellIndex T n t,
              UniformPartition.cellIndex_lt hT n ht0 htT⟩) := by
  classical
  let P := uniformActionPartition T hT n
  let i : Fin P.intervals :=
    ⟨UniformPartition.cellIndex T n t,
      UniformPartition.cellIndex_lt hT n ht0 htT⟩
  have hmem : t ∈ Ico (P.left i) (P.right i) :=
    UniformPartition.mem_uniform_cell hT n ht0 htT
  unfold partitionArrayStepCost
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem hmem]
    rfl
  · intro q hq hqi
    rw [Set.indicator_of_notMem]
    intro hmemq
    rcases lt_or_gt_of_ne hqi with hqi | hqi
    · have hright_le_left : P.right q <= P.left i := by
        change ((q.val + 1 : Nat) : Real) * T / (n + 1 : Nat) <=
          (i.val : Real) * T / (n + 1 : Nat)
        have hnat : q.val + 1 <= i.val := Nat.add_one_le_iff.mpr hqi
        gcongr
      exact (not_lt_of_ge hright_le_left)
        (hmem.1.trans_lt hmemq.2)
    · have hright_le_left : P.right i <= P.left q := by
        change ((i.val + 1 : Nat) : Real) * T / (n + 1 : Nat) <=
          (q.val : Real) * T / (n + 1 : Nat)
        have hnat : i.val + 1 <= q.val := Nat.add_one_le_iff.mpr hqi
        gcongr
      exact (not_lt_of_ge hright_le_left)
        (hmemq.1.trans_lt hmem.2)
  · exact fun hi => (hi (Finset.mem_univ i)).elim

theorem poissonCost_interval_scale
    {width nominal candidate : Real}
    (hwidth : 0 < width) (hnominal : 0 <= nominal) :
    poissonCost (width * nominal) candidate =
      ENNReal.ofReal width * poissonCost nominal (candidate / width) := by
  by_cases hc : candidate < 0
  · have hcdiv : candidate / width < 0 := div_neg_of_neg_of_pos hc hwidth
    rw [poissonCost_of_candidate_neg hc,
      poissonCost_of_candidate_neg hcdiv]
    simp [ENNReal.ofReal_ne_zero_iff.mpr hwidth]
  have hc0 : 0 <= candidate := le_of_not_gt hc
  rcases hnominal.eq_or_lt with hnominal0 | hnominal
  · subst nominal
    rcases hc0.eq_or_lt with rfl | hcpos
    · simp
    · have hcdiv : 0 < candidate / width := div_pos hcpos hwidth
      simp [poissonCost_zero_of_pos hcpos,
        poissonCost_zero_of_pos hcdiv,
        ENNReal.ofReal_ne_zero_iff.mpr hwidth]
  · have hscaled : 0 < width * nominal := mul_pos hwidth hnominal
    have hcdiv : 0 <= candidate / width := div_nonneg hc0 hwidth.le
    rw [poissonCost_of_nominal_pos hscaled hc0,
      poissonCost_of_nominal_pos hnominal hcdiv,
      ← ENNReal.ofReal_mul hwidth.le]
    congr 1
    have harg :
        candidate / (width * nominal) =
          (candidate / width) / nominal := by
      field_simp
    rw [harg]
    field_simp

theorem poissonCost_partitionArray
    (N : Network Buffer Server) {T : Real} (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real)
    (a : PartitionCoord (Buffer := Buffer) (Server := Server) P) :
    poissonCost (partitionIntensity N P a) (z a) =
      ENNReal.ofReal (P.width a.2) *
        poissonCost (N.phi a.1.1 a.1.2) (z a / P.width a.2) := by
  rw [show (partitionIntensity N P a : Real) =
      P.width a.2 * N.phi a.1.1 a.1.2 by
    simp only [partitionIntensity, NNReal.coe_mul]
    rw [Real.coe_toNNReal (P.width a.2) (P.width_pos a.2).le,
      Real.coe_toNNReal (N.phi a.1.1 a.1.2)
        (N.phi_nonneg a.1.1 a.1.2)]]
  exact poissonCost_interval_scale (P.width_pos a.2)
    (N.phi_nonneg a.1.1 a.1.2)

theorem finiteArrayAction_eq_partitionArrayStepSum
    (N : Network Buffer Server) {T : Real} (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real) :
    PoissonFiniteArray.action (partitionIntensity N P) z =
      ∑ i : Fin P.intervals,
        ENNReal.ofReal (P.width i) *
          N.localRate (fun j k =>
            z ((⟨j, k⟩ : Sigma fun _ : Server => Buffer), i) /
              P.width i) := by
  classical
  unfold PoissonFiniteArray.action Network.localRate
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_sigma]
  simp_rw [poissonCost_partitionArray N P z]
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    enter [2, j]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem lintegral_partitionArrayStepCost
    (N : Network Buffer Server) {T : Real} (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real) :
    ∫⁻ t, partitionArrayStepCost N P z t =
      PoissonFiniteArray.action (partitionIntensity N P) z := by
  classical
  rw [finiteArrayAction_eq_partitionArrayStepSum N P z]
  unfold partitionArrayStepCost
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [lintegral_indicator measurableSet_Ico, setLIntegral_const,
      Real.volume_Ico]
    simp [ActionPartition.width, mul_comm]
  · intro i hi
    exact measurable_const.indicator measurableSet_Ico

theorem lintegral_partitionArrayStepCost_Icc
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (P : ActionPartition T)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real) :
    ∫⁻ t in Icc (0 : Real) T, partitionArrayStepCost N P z t =
      PoissonFiniteArray.action (partitionIntensity N P) z := by
  rw [← lintegral_partitionArrayStepCost N P z]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Icc (0 : Real) T
  · simp [ht]
  · have hzero : partitionArrayStepCost N P z t = 0 := by
      unfold partitionArrayStepCost
      apply Finset.sum_eq_zero
      intro i hi
      rw [Set.indicator_of_notMem]
      intro hcell
      exact ht (P.cell_subset hT i ⟨hcell.1, hcell.2.le⟩)
    simp [ht, hzero]

/-- On a uniform grid, the full sample-path action of the actual linear
interpolation is exactly the finite independent-increment action. -/
theorem poissonPathRate_partitionArrayPath_uniform
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) (n : Nat)
    (z : PartitionCoord (Buffer := Buffer) (Server := Server)
      (uniformActionPartition T hT n) -> Real)
    (hz : forall a, 0 <= z a) :
    poissonPathRate N T
        (asMatrix T
          (partitionArrayPath hT.le (uniformActionPartition T hT n) z)) =
      PoissonFiniteArray.action
        (partitionIntensity N (uniformActionPartition T hT n)) z := by
  let P := uniformActionPartition T hT n
  have hvalid :=
    partitionArrayPath_valid hT.le P z
  rw [poissonPathRate, if_pos hvalid]
  calc
    (∫⁻ t in Icc (0 : Real) T,
        N.localRate
          (pathDerivative
            (asMatrix T (partitionArrayPath hT.le P z)) t)) =
        ∫⁻ t in Icc (0 : Real) T,
          N.localRate (fun j k => partitionArrayVelocity P z t j k) := by
      apply lintegral_congr_ae
      filter_upwards
        [pathDerivative_partitionArrayPath_ae hT.le P z] with t ht
      rw [ht]
    _ = ∫⁻ t in Icc (0 : Real) T,
          partitionArrayStepCost N P z t := by
      apply lintegral_congr_ae
      have hne : ∀ᵐ t : Real ∂volume, t ≠ T := by
        simp [ae_iff, measure_singleton]
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      filter_upwards [hne] with t htT ht
      have hinterior : 0 <= t /\ t < T :=
        ⟨ht.1, ht.2.lt_of_ne htT⟩
      rw [partitionArrayVelocity_uniform_eq hT n z hz
        hinterior.1 hinterior.2]
      rw [partitionArrayStepCost_uniform_eq N hT n z
        hinterior.1 hinterior.2]
    _ = PoissonFiniteArray.action (partitionIntensity N P) z :=
      lintegral_partitionArrayStepCost_Icc N hT.le P z

end StateDepMOR.PoissonSamplePath

namespace PoissonFixedKCompact

universe u v w

theorem measurable_edist_factor_countable
    {Omega : Type u} {Code : Type v} {Y : Type w}
    [MeasurableSpace Omega] [MeasurableSpace Code]
    [Countable Code] [MeasurableSingletonClass Code]
    [PseudoEMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (code : Omega -> Code) (hcode : Measurable code)
    (F : Code -> Y) {g : Omega -> Y} (hg : Measurable g) :
    Measurable (fun x => edist (F (code x)) (g x)) := by
  let H : Omega × Code -> ENNReal := fun z => edist (F z.2) (g z.1)
  have hH : Measurable H := by
    apply measurable_from_prod_countable_left
    intro d
    change Measurable (fun x => edist (F d) (g x))
    exact (continuous_const.edist continuous_id).measurable.comp hg
  exact hH.comp (measurable_id.prodMk hcode)

theorem continuousOn_finite_compact_fibers
    {Omega : Type u} {Code : Type v} {Y : Type w}
    [TopologicalSpace Omega] [T2Space Omega] [TopologicalSpace Y]
    {S : Set Code} (hS : S.Finite) (code : Omega -> Code) (F : Code -> Y)
    (K : S -> Set Omega)
    (hKcompact : forall d, IsCompact (K d))
    (hKfiber : forall d, K d ⊆ code ⁻¹' {d.1}) :
    ContinuousOn (fun x => F (code x)) (⋃ d, K d) := by
  classical
  letI : Fintype S := hS.fintype
  have hone (d : S) : ContinuousOn (fun x => F (code x)) (K d) := by
    refine (continuousOn_const :
      ContinuousOn (fun _x : Omega => F d.1) (K d)).congr ?_
    intro x hx
    have hxd : code x = d.1 := by
      simpa using hKfiber d hx
    simpa [hxd]
  have hclosed (d : S) : IsClosed (K d) := (hKcompact d).isClosed
  let G : Finset S -> Set Omega := fun s => ⋃ d ∈ s, K d
  have hGclosed (s : Finset S) : IsClosed (G s) := by
    exact s.finite_toSet.isClosed_biUnion fun d _ => hclosed d
  have hfin : forall s : Finset S,
      ContinuousOn (fun x => F (code x)) (G s) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa [G] using
          (continuousOn_empty :
            ContinuousOn (fun x => F (code x)) (∅ : Set Omega))
    | @insert d s hd ih =>
        rw [show G (insert d s) = K d ∪ G s by
          simp only [G, Finset.set_biUnion_insert]]
        apply ContinuousOn.union_of_isClosed (hone d) ih (hclosed d)
        exact hGclosed s
  simpa [G, Set.biUnion_univ] using hfin Finset.univ

theorem exists_compact_continuousOn_factor
    {Omega : Type u} {Code : Type v} {Y : Type w}
    [MeasurableSpace Omega] [TopologicalSpace Omega] [T2Space Omega]
    [SecondCountableTopology Omega]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace Omega]
    [BorelSpace Omega]
    [MeasurableSpace Code] [TopologicalSpace Code]
    [Countable Code] [MeasurableSingletonClass Code]
    [DiscreteTopology Code] [SecondCountableTopology Code]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace Code]
    [BorelSpace Code]
    [TopologicalSpace Y]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (code : Omega -> Code) (hcode : Measurable code)
    (F : Code -> Y) (eps : ENNReal) (heps : 0 < eps) :
    exists K : Set Omega, IsCompact K /\
      mu K.compl <= 3 * eps /\
      ContinuousOn (fun x => F (code x)) K := by
  classical
  let nu : Measure Code := mu.map code
  letI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map hcode.aemeasurable
  have htight : IsTightMeasureSet ({nu} : Set (Measure Code)) :=
    isTightMeasureSet_singleton
  obtain ⟨S, hScompact, hnuS⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight)
      eps heps
  have hSfinite : S.Finite := hScompact.finite_of_discrete
  have hpreS :
      mu (code ⁻¹' Sᶜ) <= eps := by
    have h := hnuS nu (by simp)
    change (mu.map code) Sᶜ <= eps at h
    rw [Measure.map_apply_of_aemeasurable hcode.aemeasurable
      hScompact.isClosed.measurableSet.compl] at h
    exact h
  by_cases hSempty : S = ∅
  · refine ⟨∅, isCompact_empty, ?_, continuousOn_empty _⟩
    subst S
    simp only [compl_empty, preimage_univ, measure_univ] at hpreS
    change mu (∅ᶜ : Set Omega) <= 3 * eps
    rw [compl_empty, measure_univ]
    calc
      1 <= eps := hpreS
      _ <= 3 * eps := by
        rw [show 3 * eps = eps + eps + eps by ring]
        exact (le_add_right le_rfl).trans (le_add_right le_rfl)
  have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSempty
  let delta : ENNReal := eps / (S.ncard : ENNReal)
  have hdelta : delta ≠ 0 := by
    change eps / (S.ncard : ENNReal) ≠ 0
    rw [ENNReal.div_ne_zero]
    exact ⟨heps.ne', ENNReal.natCast_ne_top _⟩
  letI : mu.InnerRegularCompactLTTop :=
    instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace mu
  have hfiber (d : S) :
      MeasurableSet (code ⁻¹' ({d.1} : Set Code)) :=
    (measurableSet_singleton d.1).preimage hcode
  choose K hKsub hKcompact hKclosed hKloss using
    fun d : S =>
      (hfiber d).exists_isCompact_isClosed_sdiff_lt
        (measure_ne_top mu _) hdelta
  let C : Set Omega := ⋃ d : S, K d
  have hCcompact : IsCompact C := by
    letI : Fintype S := hSfinite.fintype
    simpa [C, Set.biUnion_univ] using
      (Set.finite_univ.isCompact_biUnion
        (fun d _ => hKcompact d))
  have hCcont :
      ContinuousOn (fun x => F (code x)) C :=
    continuousOn_finite_compact_fibers hSfinite code F K
      hKcompact hKsub
  have hcompl_subset :
      C.compl ⊆
        code ⁻¹' Sᶜ ∪
          ⋃ d : S, (code ⁻¹' ({d.1} : Set Code)) \ K d := by
    intro x hx
    by_cases hcodeS : code x ∈ S
    · right
      let d : S := ⟨code x, hcodeS⟩
      refine Set.mem_iUnion.2 ⟨d, ?_⟩
      refine ⟨by simp [d], ?_⟩
      intro hxK
      exact hx (Set.mem_iUnion.2 ⟨d, hxK⟩)
    · left
      exact hcodeS
  have htail :
      mu (⋃ d : S, (code ⁻¹' ({d.1} : Set Code)) \ K d) <= eps := by
    letI : Fintype S := hSfinite.fintype
    calc
      mu (⋃ d : S, (code ⁻¹' ({d.1} : Set Code)) \ K d) <=
          ∑ d : S, mu ((code ⁻¹' ({d.1} : Set Code)) \ K d) :=
        measure_iUnion_fintype_le _ _
      _ <= ∑ _d : S, delta := by
        exact Finset.sum_le_sum fun d _ => (hKloss d).le
      _ = (S.ncard : ENNReal) * delta := by
        have hcard : Fintype.card S = S.ncard := by
          rw [Set.ncard_eq_toFinset_card' S]
          simpa using Fintype.card_coe S.toFinset
        simp [hcard]
      _ = eps := by
        change (S.ncard : ENNReal) *
          (eps / (S.ncard : ENNReal)) = eps
        rw [ENNReal.mul_div_cancel]
        · have hn : S.ncard ≠ 0 :=
            ((Set.ncard_pos (s := S)).mpr hSne).ne'
          exact_mod_cast hn
        · exact ENNReal.natCast_ne_top _
  refine ⟨C, hCcompact, ?_, hCcont⟩
  calc
    mu C.compl <=
        mu (code ⁻¹' Sᶜ ∪
          ⋃ d : S, (code ⁻¹' ({d.1} : Set Code)) \ K d) :=
      measure_mono hcompl_subset
    _ <= mu (code ⁻¹' Sᶜ) +
        mu (⋃ d : S, (code ⁻¹' ({d.1} : Set Code)) \ K d) :=
      measure_union_le _ _
    _ <= eps + eps := add_le_add hpreS htail
    _ <= 3 * eps := by
      rw [show 3 * eps = eps + eps + eps by ring]
      exact le_add_of_nonneg_right bot_le

end PoissonFixedKCompact

namespace StateDepMOR.PoissonSamplePath

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

open PoissonFixedKCompact

theorem calendarPathLaw_fixed_positive_compact_containment
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) (K : PNat)
    (eta : ENNReal) (heta : 0 < eta) :
    exists D : Set (Path (Buffer := Buffer) (Server := Server) T),
      IsCompact D /\ calendarPathLaw N T (K : Nat) D.compl <= eta := by
  classical
  let Omega :=
    Network.CalendarPoissonSample (Buffer := Buffer) (Server := Server)
  let mu : Measure Omega := N.calendarPoissonMeasure
  let speed : PNat := positiveSize (K : Nat)
  let f : Omega -> Path (Buffer := Buffer) (Server := Server) T :=
    calendarPath N T speed
  have hf : AEMeasurable f mu :=
    calendarPath_aemeasurable N hT speed
  let g : Omega -> Path (Buffer := Buffer) (Server := Server) T :=
    hf.mk f
  have hg : Measurable g := hf.measurable_mk
  by_cases hetaTop : eta = Top.top
  · refine ⟨∅, isCompact_empty, ?_⟩
    subst eta
    exact le_top
  let quarter : ENNReal := eta / 4
  have hquarter : 0 < quarter :=
    ENNReal.div_pos heta.ne' (by norm_num)
  have hquarterTop : quarter ≠ Top.top := by
    exact ENNReal.div_ne_top hetaTop (by norm_num)
  let er : Real := quarter.toReal
  have her : 0 < er :=
    ENNReal.toReal_pos hquarter.ne' hquarterTop
  let fn : Nat -> Omega ->
      Path (Buffer := Buffer) (Server := Server) T :=
    fun n => delayedCalendarPath N T speed n
  let code : (n : Nat) -> Omega ->
      ClockPrefixCode (Buffer := Buffer) (Server := Server) n :=
    fun n => encodeClockPrefix n
  let decodePath : (n : Nat) ->
      ClockPrefixCode (Buffer := Buffer) (Server := Server) n ->
        Path (Buffer := Buffer) (Server := Server) T :=
    fun n d => calendarPath N T speed (decodeClockPrefix n d)
  have hfn_factor (n : Nat) :
      fn n = fun omega => decodePath n (code n omega) := rfl
  have hed (n : Nat) :
      Measurable (fun omega => edist (fn n omega) (g omega)) := by
    rw [hfn_factor]
    exact measurable_edist_factor_countable
      (code n) (measurable_encodeClockPrefix n) (decodePath n) hg
  have hconv :
      ∀ᵐ omega ∂mu,
        Tendsto (fun n => fn n omega) atTop (nhds (g omega)) := by
    filter_upwards [delayedCalendarPath_tendsto_j1_ae N hT speed,
      hf.ae_eq_mk] with omega homega heq
    change Tendsto (fun n => fn n omega) atTop
      (nhds (hf.mk f omega))
    rw [← heq]
    change Tendsto
      (fun n => delayedCalendarPath N T speed n omega) atTop
      (nhds (calendarPath N T speed omega))
    exact homega
  obtain ⟨bad, hbadMeas, hbad, hunif⟩ :=
    tendstoUniformlyOn_of_ae_tendsto_of_measurable_edist'
      hed hconv her
  have hbadQuarter : mu bad <= quarter := by
    simpa [er, ENNReal.ofReal_toReal hquarterTop] using hbad
  letI : mu.InnerRegularCompactLTTop :=
    instInnerRegularCompactLTTopOfIsCompletelyPseudoMetrizableSpace mu
  obtain ⟨C0, hC0sub, hC0compact, hC0closed, hC0loss⟩ :=
    hbadMeas.compl.exists_isCompact_isClosed_sdiff_lt
      (measure_ne_top mu _) hquarter.ne'
  have hC0compl : mu C0.compl <= quarter + quarter := by
    have hsubset :
        C0.compl ⊆ bad ∪ (bad.compl \ C0) := by
      intro omega homega
      by_cases hb : omega ∈ bad
      · exact Or.inl hb
      · exact Or.inr ⟨hb, homega⟩
    calc
      mu C0.compl <= mu (bad ∪ (bad.compl \ C0)) :=
        measure_mono hsubset
      _ <= mu bad + mu (bad.compl \ C0) := measure_union_le _ _
      _ <= quarter + quarter :=
        add_le_add hbadQuarter hC0loss.le
  obtain ⟨budget, hbudgetPos, hbudgetSum⟩ :=
    ENNReal.exists_pos_sum_of_countable' hquarter.ne' Nat
  have hthird (n : Nat) : 0 < budget n / 3 :=
    ENNReal.div_pos (hbudgetPos n).ne' (by norm_num)
  choose C hCcompact hCcompl hCcont using fun n =>
    exists_compact_continuousOn_factor mu
      (code n) (measurable_encodeClockPrefix n) (decodePath n)
      (budget n / 3) (hthird n)
  have hCcompl' (n : Nat) : mu (C n).compl <= budget n := by
    calc
      mu (C n).compl <= 3 * (budget n / 3) := hCcompl n
      _ = budget n := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  let A : Set Omega := C0 ∩ ⋂ n, C n
  have hAcompact : IsCompact A := by
    apply hC0compact.inter_right
    exact isClosed_iInter fun n => (hCcompact n).isClosed
  have hAsub : A ⊆ bad.compl :=
    fun _ h => hC0sub h.1
  have hAcont (n : Nat) : ContinuousOn (fn n) A := by
    rw [hfn_factor]
    exact (hCcont n).mono fun omega homega =>
      Set.mem_iInter.mp homega.2 n
  have hgA : ContinuousOn g A := by
    apply (hunif.mono hAsub).continuousOn
    exact (Filter.Eventually.of_forall hAcont).frequently
  have hAcompl : mu A.compl <= eta := by
    have hsubset :
        A.compl ⊆ C0.compl ∪ ⋃ n, (C n).compl := by
      intro omega homega
      change omega ∉ A at homega
      by_cases h0 : omega ∈ C0
      · right
        have hn : omega ∉ ⋂ n, C n := by
          intro hall
          exact homega ⟨h0, hall⟩
        simp only [Set.mem_iInter, not_forall] at hn
        obtain ⟨n, hn⟩ := hn
        exact Set.mem_iUnion.2 ⟨n, hn⟩
      · exact Or.inl h0
    calc
      mu A.compl <= mu (C0.compl ∪ ⋃ n, (C n).compl) :=
        measure_mono hsubset
      _ <= mu C0.compl + mu (⋃ n, (C n).compl) :=
        measure_union_le _ _
      _ <= (quarter + quarter) + ∑' n, mu (C n).compl :=
        add_le_add hC0compl (measure_iUnion_le _)
      _ <= (quarter + quarter) + ∑' n, budget n :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum hCcompl')
      _ <= (quarter + quarter) + quarter :=
        add_le_add le_rfl hbudgetSum.le
      _ <= eta := by
        change eta / 4 + eta / 4 + eta / 4 <= eta
        calc
          eta / 4 + eta / 4 + eta / 4 <=
              eta / 4 + eta / 4 + eta / 4 + eta / 4 :=
            le_add_right le_rfl
          _ = 4 * (eta / 4) := by ring
          _ = eta := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  let D : Set (Path (Buffer := Buffer) (Server := Server) T) := g '' A
  have hDcompact : IsCompact D := hAcompact.image_of_continuousOn hgA
  have hDclosed : IsClosed D := by
    letI : T0Space
        (Path (Buffer := Buffer) (Server := Server) T) := {
      t0 := fun x y hxy => by
          apply j1EDist_eq_zero_imp_eq hT
          have hd : dist x y = 0 := Metric.inseparable_iff.mp hxy
          change (j1EDist x y).toReal = 0 at hd
          rcases (ENNReal.toReal_eq_zero_iff (j1EDist x y)).mp hd with
            hzero | htop
          · exact hzero
          · exact False.elim
              ((ne_of_lt ((j1EDist_le_one x y).trans_lt
                ENNReal.one_lt_top)) htop) }
    exact hDcompact.isClosed
  refine ⟨D, hDcompact, ?_⟩
  have hmap :
      calendarPathLaw N T (K : Nat) = mu.map g := by
    unfold calendarPathLaw
    exact Measure.map_congr hf.ae_eq_mk
  rw [hmap]
  change (mu.map g) (Dᶜ) <= eta
  rw [Measure.map_apply_of_aemeasurable hg.aemeasurable
    hDclosed.measurableSet.compl]
  apply (measure_mono ?_).trans hAcompl
  intro omega homega
  change g omega ∉ D at homega
  change omega ∉ A
  intro homegaA
  exact homega ⟨omega, homegaA, rfl⟩

end StateDepMOR.PoissonSamplePath


open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set

namespace StateDepMOR
namespace PoissonUpperAssembly

universe u

variable {X : Type u} [MeasurableSpace X]

/-- A common hypothesis for probability and subprobability laws. -/
def MassLeOne (mu : Nat -> Measure X) : Prop :=
  forall K, mu K Set.univ <= 1

theorem scaledLogMass_nonpos_of_mass_le_one
    (mu : Nat -> Measure X) (hmass : MassLeOne mu)
    (event : Set X) (K : Nat) :
    scaledLogMass mu event K <= 0 := by
  unfold scaledLogMass
  apply EReal.div_nonpos_of_nonpos_of_nonneg
  next =>
    apply ENNReal.log_le_zero_iff.mpr
    exact (measure_mono (subset_univ event)).trans (hmass (K + 1))
  next => positivity

theorem limsup_scaledLogMass_nonpos_of_mass_le_one
    (mu : Nat -> Measure X) (hmass : MassLeOne mu)
    (event : Set X) :
    limsup (scaledLogMass mu event) atTop <= 0 := by
  calc
    limsup (scaledLogMass mu event) atTop <=
        limsup (fun _ : Nat => (0 : EReal)) atTop := by
      apply limsup_le_limsup
      next =>
        exact Eventually.of_forall
          (scaledLogMass_nonpos_of_mass_le_one mu hmass event)
      next => exact Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le)
      next =>
        exact Filter.isBoundedUnder_of_eventually_le
          (Eventually.of_forall fun _ => le_rfl)
    _ = 0 := limsup_const (0 : EReal)

theorem scaledLogMass_mono
    (mu : Nat -> Measure X) {A B : Set X} (hAB : A <= B) (K : Nat) :
    scaledLogMass mu A K <= scaledLogMass mu B K := by
  unfold scaledLogMass
  apply EReal.div_le_div_right_of_nonneg (by positivity)
  exact ENNReal.log_le_log (measure_mono hAB)

private theorem log_two_div_tendsto_zero :
    Tendsto
      (fun K : Nat => ENNReal.log (2 : ENNReal) / ((K + 1 : Nat) : EReal))
      atTop (nhds 0) := by
  have h :=
    EReal.tendsto_const_div_atTop_nhds_zero_nat
      (C := ENNReal.log (2 : ENNReal)) (by simp) (by simp)
  change Tendsto
    (Function.comp
      (fun n : Nat => ENNReal.log (2 : ENNReal) / (n : EReal))
      (fun K : Nat => K + 1)) atTop (nhds 0)
  exact h.comp (tendsto_add_atTop_nat 1)

private theorem scaledLogMass_union_pointwise
    (mu : Nat -> Measure X) (A B : Set X) (K : Nat) :
    scaledLogMass mu (Set.union A B) K <=
      ENNReal.log (2 : ENNReal) / ((K + 1 : Nat) : EReal) +
        max (scaledLogMass mu A K) (scaledLogMass mu B K) := by
  let a := mu (K + 1) A
  let b := mu (K + 1) B
  have hab : mu (K + 1) (Set.union A B) <=
      (2 : ENNReal) * max a b := by
    calc
      mu (K + 1) (Set.union A B) <= a + b := measure_union_le A B
      _ <= max a b + max a b :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = (2 : ENNReal) * max a b := by rw [two_mul]
  unfold scaledLogMass
  apply (EReal.div_le_div_right_of_nonneg (by positivity)
    (ENNReal.log_le_log hab)).trans_eq
  rw [ENNReal.log_mul_add, EReal.add_div_of_nonneg_right (by positivity)]
  congr 1
  rw [ENNReal.log_monotone.map_max]
  dsimp [a, b]
  rcases le_total
      (ENNReal.log (mu (K + 1) A))
      (ENNReal.log (mu (K + 1) B)) with h | h
  next =>
    rw [max_eq_right h, max_eq_right
      (EReal.div_le_div_right_of_nonneg (by positivity) h)]
  next =>
    rw [max_eq_left h, max_eq_left
      (EReal.div_le_div_right_of_nonneg (by positivity) h)]

/-- A finite union has no extra logarithmic cost.  This is the binary
form used by both finite-cover induction and exponential tightness. -/
theorem limsup_scaledLogMass_union_le_max
    (mu : Nat -> Measure X) (hmass : MassLeOne mu)
    (A B : Set X) :
    limsup (scaledLogMass mu (Set.union A B)) atTop <=
      max (limsup (scaledLogMass mu A) atTop)
        (limsup (scaledLogMass mu B) atTop) := by
  let e : Nat -> EReal :=
    fun K => ENNReal.log (2 : ENNReal) / ((K + 1 : Nat) : EReal)
  let m : Nat -> EReal :=
    fun K => max (scaledLogMass mu A K) (scaledLogMass mu B K)
  have he : Tendsto e atTop (nhds 0) := log_two_div_tendsto_zero
  have heL : limsup e atTop = 0 := he.limsup_eq
  have hmA :
      Filter.IsBoundedUnder (fun x y : EReal => x <= y) atTop
        (scaledLogMass mu A) :=
    Filter.isBoundedUnder_of_eventually_le
      (Eventually.of_forall
        (scaledLogMass_nonpos_of_mass_le_one mu hmass A))
  have hmB :
      Filter.IsBoundedUnder (fun x y : EReal => x <= y) atTop
        (scaledLogMass mu B) :=
    Filter.isBoundedUnder_of_eventually_le
      (Eventually.of_forall
        (scaledLogMass_nonpos_of_mass_le_one mu hmass B))
  have hmL :
      limsup m atTop =
        max (limsup (scaledLogMass mu A) atTop)
          (limsup (scaledLogMass mu B) atTop) := by
    exact limsup_max
  have hpoint : forall K, scaledLogMass mu (Set.union A B) K <= e K + m K :=
    scaledLogMass_union_pointwise mu A B
  calc
    limsup (scaledLogMass mu (Set.union A B)) atTop <=
        limsup (e + m) atTop := by
      apply limsup_le_limsup
      next => exact Eventually.of_forall hpoint
      next => exact Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le)
      next =>
        exact Filter.isBoundedUnder_of_eventually_le
          (Eventually.of_forall fun _ => le_top)
    _ <= limsup e atTop + limsup m atTop := by
      apply EReal.limsup_add_le
      next =>
        left
        rw [heL]
        simp
      next =>
        left
        rw [heL]
        simp
    _ = max (limsup (scaledLogMass mu A) atTop)
          (limsup (scaledLogMass mu B) atTop) := by
      rw [heL, zero_add, hmL]

theorem limsup_scaledLogMass_mono
    (mu : Nat -> Measure X) (hmass : MassLeOne mu)
    {A B : Set X} (hAB : A <= B) :
    limsup (scaledLogMass mu A) atTop <=
      limsup (scaledLogMass mu B) atTop := by
  apply limsup_le_limsup
  next => exact Eventually.of_forall (scaledLogMass_mono mu hAB)
  next => exact Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le)
  next =>
    exact Filter.isBoundedUnder_of_eventually_le
      (Eventually.of_forall
        (scaledLogMass_nonpos_of_mass_le_one mu hmass B))

section FiniteUnion

variable {Index : Type*} [DecidableEq Index]

def finiteUnion (s : Finset Index) (U : Index -> Set X) : Set X :=
  {x | exists i, Membership.mem s i /\ Membership.mem (U i) x}

omit [MeasurableSpace X] [DecidableEq Index] in
@[simp]
theorem finiteUnion_empty (U : Index -> Set X) :
    finiteUnion ({} : Finset Index) U = ({} : Set X) := by
  ext x
  change Iff
    (exists i, Membership.mem ({} : Finset Index) i /\
      Membership.mem (U i) x) False
  exact Finset.exists_mem_empty_iff (fun i => Membership.mem (U i) x)

omit [MeasurableSpace X] in
@[simp]
theorem finiteUnion_insert (i : Index) (s : Finset Index)
    (U : Index -> Set X) :
    finiteUnion (insert i s) U = Set.union (U i) (finiteUnion s U) := by
  ext x
  change
    Iff (exists j, Membership.mem (insert i s) j /\
      Membership.mem (U j) x)
      (Membership.mem (U i) x \/ exists j, Membership.mem s j /\
        Membership.mem (U j) x)
  aesop

/-- A finite union of events with a common logarithmic upper bound has the
same bound. -/
theorem limsup_scaledLogMass_finiteUnion_le
    (mu : Nat -> Measure X) (hmass : MassLeOne mu)
    (s : Finset Index) (U : Index -> Set X) (z : EReal)
    (hU : forall i, Membership.mem s i ->
      limsup (scaledLogMass mu (U i)) atTop <= z) :
    limsup (scaledLogMass mu (finiteUnion s U)) atTop <= z := by
  induction s using Finset.induction_on with
  | empty =>
      have hset : finiteUnion ({} : Finset Index) U = ({} : Set X) :=
        finiteUnion_empty U
      rw [hset]
      have hempty :
          scaledLogMass mu ({} : Set X) =
            fun _ : Nat => (Bot.bot : EReal) := by
        funext K
        unfold scaledLogMass
        rw [measure_empty, ENNReal.log_zero]
        exact EReal.bot_div_of_pos_ne_top (by positivity)
          (EReal.natCast_ne_top (K + 1))
      rw [hempty, limsup_const_bot]
      exact bot_le
  | @insert i s hi ih =>
      rw [finiteUnion_insert]
      exact (limsup_scaledLogMass_union_le_max mu hmass (U i)
        (finiteUnion s U)).trans
          (max_le
            (hU i (Finset.mem_insert_self i s))
            (ih (fun j hj => hU j (Finset.mem_insert_of_mem hj))))

end FiniteUnion

omit [MeasurableSpace X] in
theorem rateInf_mono_event
    (I : X -> ENNReal) {A B : Set X} (hAB : A <= B) :
    rateInf I B <= rateInf I A := by
  unfold rateInf
  apply le_sInf
  intro y hy
  choose x hx hEq using hy
  subst y
  exact sInf_le (Exists.intro x (And.intro (hAB hx) rfl))

section Topological

variable [TopologicalSpace X]

/-- Genuine-open pointwise upper estimates at every real level strictly
below the ENNReal rate. -/
def OpenLocalUpper
    (mu : Nat -> Measure X) (I : X -> ENNReal) : Prop :=
  forall x (c : Real), (c : EReal) < (I x : EReal) ->
    exists U : Set X, IsOpen U /\ Membership.mem U x /\
      limsup (scaledLogMass mu U) atTop <= -(c : EReal)

/-- It is enough to prove local estimates at nonnegative levels.  Negative
levels follow from the subprobability bound, with the whole space as a
genuine open neighborhood. -/
theorem openLocalUpper_of_nonnegative
    (mu : Nat -> Measure X) (I : X -> ENNReal)
    (hmass : MassLeOne mu)
    (hlocal : forall x c, 0 <= c -> ENNReal.ofReal c < I x ->
      exists U : Set X, IsOpen U /\ Membership.mem U x /\
        limsup (scaledLogMass mu U) atTop <= -(c : EReal)) :
    OpenLocalUpper mu I := by
  intro x c hc
  by_cases hc0 : 0 <= c
  next =>
    apply hlocal x c hc0
    apply EReal.coe_ennreal_lt_coe_ennreal_iff.mp
    simpa [EReal.coe_ennreal_ofReal, max_eq_left hc0] using hc
  next =>
    apply Exists.intro Set.univ
    apply And.intro isOpen_univ
    apply And.intro (Set.mem_univ x)
    exact
      (limsup_scaledLogMass_nonpos_of_mass_le_one
        mu hmass Set.univ).trans
          (EReal.neg_nonneg.mpr
            (EReal.coe_nonpos.mpr (le_of_not_ge hc0)))

/-- Compact upper bound at a strict real level below the compact-set
`rateInf`.  The proof is the finite-open-cover argument. -/
theorem compact_upper_bound_at_real_level
    (mu : Nat -> Measure X) (I : X -> ENNReal)
    (hmass : MassLeOne mu) (hlocal : OpenLocalUpper mu I)
    (C : Set X) (hC : IsCompact C) (c : Real)
    (hc : (c : EReal) < (rateInf I C : EReal)) :
    limsup (scaledLogMass mu C) atTop <= -(c : EReal) := by
  classical
  have hpoint : forall x : C, (c : EReal) < (I x : EReal) := by
    intro x
    have hrate : rateInf I C <= I x := by
      unfold rateInf
      exact sInf_le
        (Exists.intro x (And.intro x.property rfl))
    exact hc.trans_le
      (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hrate)
  choose U hUopen hxU hUbound using
    fun x : C => hlocal x c (hpoint x)
  have hcover : C <= Set.iUnion U := by
    intro x hx
    exact Set.mem_iUnion.2
      (Exists.intro (Subtype.mk x hx) (hxU (Subtype.mk x hx)))
  choose s hs using hC.elim_finite_subcover U hUopen hcover
  have hCsub : C <= finiteUnion s U := by
    intro x hx
    choose i hi using Set.mem_iUnion.1 (hs hx)
    choose his hxi using Set.mem_iUnion.1 hi
    exact Exists.intro i (And.intro his hxi)
  exact (limsup_scaledLogMass_mono mu hmass hCsub).trans
    (limsup_scaledLogMass_finiteUnion_le
      mu hmass s U (-(c : EReal))
      (fun i _ => hUbound i))

/-- Exact compact-set upper bound with the repository's `EReal` and
`rateInf` conventions.  In particular, if the infimum is infinite, the
right side is `bot`. -/
theorem compact_upper_bound
    (mu : Nat -> Measure X) (I : X -> ENNReal)
    (hmass : MassLeOne mu) (hlocal : OpenLocalUpper mu I)
    (C : Set X) (hC : IsCompact C) :
    limsup (scaledLogMass mu C) atTop <=
      -(rateInf I C : EReal) := by
  by_contra hle
  have hlt :
      -(rateInf I C : EReal) <
        limsup (scaledLogMass mu C) atTop :=
    lt_of_not_ge hle
  choose y hry hyL using EReal.exists_between_coe_real hlt
  have hc : ((-y : Real) : EReal) < (rateInf I C : EReal) := by
    have hneg := EReal.neg_lt_neg_iff.mpr hry
    simpa using hneg
  have hbound :=
    compact_upper_bound_at_real_level
      mu I hmass hlocal C hC (-y) hc
  have hbound' :
      limsup (scaledLogMass mu C) atTop <= (y : EReal) := by
    simpa using hbound
  exact (not_le_of_gt hyL) hbound'

/-- Exponential tightness at every real level. -/
def ExponentiallyTight (mu : Nat -> Measure X) : Prop :=
  forall L : Real, exists C : Set X, IsCompact C /\
    limsup (scaledLogMass mu C.compl) atTop <= -(L : EReal)

/-- Exponential tightness and exact compact upper bounds imply the exact
upper bound for every closed set.  This is topology-generic, so it applies
directly when the topology is J1. -/
theorem closed_upper_bound_of_exponential_tightness
    (mu : Nat -> Measure X) (I : X -> ENNReal)
    (hmass : MassLeOne mu) (htight : ExponentiallyTight mu)
    (hcompact : forall C : Set X, IsCompact C ->
      limsup (scaledLogMass mu C) atTop <=
        -(rateInf I C : EReal))
    (F : Set X) (hF : IsClosed F) :
    limsup (scaledLogMass mu F) atTop <=
      -(rateInf I F : EReal) := by
  by_contra hle
  have hlt :
      -(rateInf I F : EReal) <
        limsup (scaledLogMass mu F) atTop :=
    lt_of_not_ge hle
  choose y hry hyL using EReal.exists_between_coe_real hlt
  choose C hC htail using htight (-y)
  have hFC : IsCompact (Set.inter F C) :=
    hC.inter_left hF
  have hcompactFC := hcompact (Set.inter F C) hFC
  have hrate :
      rateInf I F <= rateInf I (Set.inter F C) :=
    rateInf_mono_event I inter_subset_left
  have hrateE :
      (rateInf I F : EReal) <=
        (rateInf I (Set.inter F C) : EReal) :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr hrate
  have hcompactY :
      limsup (scaledLogMass mu (Set.inter F C)) atTop <= (y : EReal) :=
    hcompactFC.trans
      ((EReal.neg_le_neg_iff.mpr hrateE).trans hry.le)
  have htailY :
      limsup (scaledLogMass mu C.compl) atTop <= (y : EReal) := by
    simpa using htail
  have hFsub : F <= Set.union (Set.inter F C) C.compl := by
    intro x hx
    by_cases hxC : Membership.mem C x
    next => exact Or.inl (And.intro hx hxC)
    next => exact Or.inr hxC
  have hfinal :
      limsup (scaledLogMass mu F) atTop <= (y : EReal) :=
    (limsup_scaledLogMass_mono mu hmass hFsub).trans
      ((limsup_scaledLogMass_union_le_max
          mu hmass (Set.inter F C) C.compl).trans
        (max_le hcompactY htailY))
  exact (not_le_of_gt hyL) hfinal

/-- Full closed-set assembly from the two probabilistic inputs: genuine-open
local estimates and exponential tightness. -/
theorem closed_upper_bound
    (mu : Nat -> Measure X) (I : X -> ENNReal)
    (hmass : MassLeOne mu)
    (hlocal : OpenLocalUpper mu I)
    (htight : ExponentiallyTight mu)
    (F : Set X) (hF : IsClosed F) :
    limsup (scaledLogMass mu F) atTop <=
      -(rateInf I F : EReal) :=
  closed_upper_bound_of_exponential_tightness
    mu I hmass htight
    (fun C hC => compact_upper_bound mu I hmass hlocal C hC)
    F hF

end Topological

end PoissonUpperAssembly
end StateDepMOR


open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory ProbabilityTheory Set

namespace StateDepMOR
namespace PoissonUpperFinal

universe u v

open PoissonSamplePath
open PoissonPolygonalBridge

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

set_option maxRecDepth 10000
set_option maxHeartbeats 1200000

noncomputable def positiveArray {T : Real} (P : ActionPartition T)
    (z : PoissonPolygonalBridge.Coord
      (Buffer := Buffer) (Server := Server) P -> Real) :
    PoissonPolygonalBridge.NonnegativeArray
      (Buffer := Buffer) (Server := Server) P :=
  ⟨fun a => max (z a) 0, fun a => le_max_right _ _⟩

noncomputable def polygonalize {T : Real} (P : ActionPartition T)
    (z : PoissonPolygonalBridge.Coord
      (Buffer := Buffer) (Server := Server) P -> Real) :
    Path (Buffer := Buffer) (Server := Server) T :=
  polygonalPath P (positiveArray P z)

theorem continuous_positiveArray {T : Real} (P : ActionPartition T) :
    Continuous
      (positiveArray (Buffer := Buffer) (Server := Server) P) := by
  apply continuous_induced_rng.mpr
  fun_prop

theorem continuous_polygonalize {T : Real} (P : ActionPartition T) :
    Continuous
      (polygonalize (Buffer := Buffer) (Server := Server) P) :=
  (continuous_polygonalPath P).comp (continuous_positiveArray P)

theorem polygonalize_eq_of_nonnegative {T : Real}
    (P : ActionPartition T)
    (z : PoissonPolygonalBridge.Coord
      (Buffer := Buffer) (Server := Server) P -> Real)
    (hz : forall a, 0 <= z a) :
    polygonalize P z = polygonalPath P ⟨z, hz⟩ := by
  change polygonalPath P (positiveArray P z) =
    polygonalPath P ⟨z, hz⟩
  congr 1
  apply Subtype.ext
  funext a
  simp [positiveArray, max_eq_left (hz a)]

def coordinateTail {Coord : Type*} (eta : Real) :
    Set (Coord -> Real) :=
  {z | exists a, eta < z a}

theorem scaledLaw_coordinateTail_mass_le
    {Coord : Type*} [Fintype Coord]
    (q : Coord -> NNReal) (K : Nat) (hK : 0 < K)
    (eta theta qmax : Real) (htheta : 0 <= theta)
    (hq : forall a, (q a : Real) <= qmax) :
    PoissonFiniteArray.scaledLaw q K (coordinateTail eta) <=
      ENNReal.ofReal
        (((Fintype.card Coord + 1 : Nat) : Real) *
          Real.exp ((K : Real) *
            (-theta * eta + qmax * (Real.exp theta - 1)))) := by
  classical
  have hevent : MeasurableSet (coordinateTail (Coord := Coord) eta) := by
    have hopen : IsOpen
        (⋃ a : Coord, {z : Coord -> Real | eta < z a}) :=
      isOpen_iUnion fun a : Coord =>
        isOpen_lt
          (continuous_const : Continuous (fun _ : Coord -> Real => eta))
          (continuous_apply a)
    simpa only [coordinateTail, Set.setOf_exists] using hopen.measurableSet
  rw [PoissonFiniteArray.scaledLaw,
    Measure.map_apply (by fun_prop) hevent]
  have hpre :
      PoissonFiniteArray.scale K ⁻¹' coordinateTail eta <=
        ⋃ a : Coord, {n | (K : Real) * eta <= (n a : Real)} := by
    intro n hn
    rcases hn with ⟨a, ha⟩
    apply Set.mem_iUnion_of_mem a
    have hKr : (0 : Real) < K := by exact_mod_cast hK
    unfold PoissonFiniteArray.scale at ha
    simpa [mul_comm] using ((lt_div_iff₀ hKr).mp ha).le
  calc
    PoissonFiniteArray.countLaw q K
        (PoissonFiniteArray.scale K ⁻¹' coordinateTail eta) <=
        PoissonFiniteArray.countLaw q K
          (⋃ a : Coord, {n | (K : Real) * eta <= (n a : Real)}) :=
      measure_mono hpre
    _ <= ∑ a : Coord,
        PoissonFiniteArray.countLaw q K
          {n | (K : Real) * eta <= (n a : Real)} :=
      measure_iUnion_fintype_le _ _
    _ <= ∑ _a : Coord,
        ENNReal.ofReal
          (Real.exp ((K : Real) *
            (-theta * eta + qmax * (Real.exp theta - 1)))) := by
      apply Finset.sum_le_sum
      intro a ha
      refine (PoissonFiniteArray.countLaw_coordinate_upper_tail
        q K a eta theta htheta).trans ?_
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hexp : 0 <= Real.exp theta - 1 :=
        sub_nonneg.mpr (Real.one_le_exp htheta)
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg K)
      simpa only [add_comm] using
        add_le_add_left
          (mul_le_mul_of_nonneg_right (hq a) hexp) (-theta * eta)
    _ <= ENNReal.ofReal
        (((Fintype.card Coord + 1 : Nat) : Real) *
          Real.exp ((K : Real) *
            (-theta * eta + qmax * (Real.exp theta - 1)))) := by
      rw [Finset.sum_const, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      gcongr
      exact_mod_cast Nat.le_add_right (Fintype.card Coord) 1

theorem coordinateTail_upper_bound
    {Coord : Type*} [Fintype Coord]
    (q : Coord -> NNReal) (eta theta qmax : Real)
    (htheta : 0 <= theta)
    (hq : forall a, (q a : Real) <= qmax) :
    limsup
        (scaledLogMass (PoissonFiniteArray.scaledLaw q)
          (coordinateTail eta)) atTop <=
      -((theta * eta - qmax * (Real.exp theta - 1) : Real) : EReal) := by
  apply PoissonFiniteArray.limsup_of_subexponential_bound
    (mu := PoissonFiniteArray.scaledLaw q)
    (event := coordinateTail eta)
    (A := fun _ => (Fintype.card Coord + 1 : Nat))
    (c := theta * eta - qmax * (Real.exp theta - 1))
  · intro K hK
    positivity
  · intro K hK
    convert scaledLaw_coordinateTail_mass_le
      q K hK eta theta qmax htheta hq using 1
    congr 3
    ring
  · exact tendsto_const_div_atTop_nhds_zero_nat _

theorem exists_uniform_partition_coordinateTail_upper
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (eta : Real) (heta : 0 < eta) (L : Real) :
    exists n : Nat,
      let P := uniformActionPartition T hT n
      limsup
          (scaledLogMass
            (PoissonFiniteArray.scaledLaw (partitionIntensity N P))
            (coordinateTail
              (Coord := PartitionCoord
                (Buffer := Buffer) (Server := Server) P) eta)) atTop <=
        -(L : EReal) := by
  classical
  let Phi : Real := ∑ j : Server, ∑ k : Buffer, N.phi j k
  have hPhi : 0 <= Phi := by
    dsimp [Phi]
    apply Finset.sum_nonneg
    intro j hj
    exact Finset.sum_nonneg fun k hk => N.phi_nonneg j k
  let theta : Real := (max L 0 + 2) / eta
  have htheta : 0 < theta := by
    dsimp [theta]
    positivity
  let B : Real := T * Phi * (Real.exp theta - 1)
  have hB : 0 <= B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg hT.le hPhi)
      (sub_nonneg.mpr (Real.one_le_exp htheta.le))
  obtain ⟨n, hn⟩ := exists_nat_ge B
  let P := uniformActionPartition T hT n
  let qmax : Real := T / (n + 1 : Nat) * Phi
  have hq (a : PartitionCoord
      (Buffer := Buffer) (Server := Server) P) :
      (partitionIntensity N P a : Real) <= qmax := by
    have hphi :
        N.phi a.1.1 a.1.2 <= Phi := by
      dsimp [Phi]
      exact
        (Finset.single_le_sum
          (fun k _ => N.phi_nonneg a.1.1 k) (Finset.mem_univ a.1.2)).trans
        (Finset.single_le_sum
          (fun j _ => Finset.sum_nonneg fun k _ => N.phi_nonneg j k)
          (Finset.mem_univ a.1.1))
    have hw : P.width a.2 = T / (n + 1 : Nat) := by
      dsimp [P, uniformActionPartition, ActionPartition.width,
        ActionPartition.left, ActionPartition.right]
      field_simp
      norm_num
    unfold partitionIntensity
    rw [NNReal.coe_mul,
      Real.coe_toNNReal _ (P.width_pos a.2).le,
      Real.coe_toNNReal _ (N.phi_nonneg a.1.1 a.1.2), hw]
    exact mul_le_mul_of_nonneg_left hphi (div_nonneg hT.le (by positivity))
  have hsmall : qmax * (Real.exp theta - 1) <= 1 := by
    have hden : (0 : Real) < (n + 1 : Nat) := by positivity
    have hn' : B <= (n : Real) := by exact_mod_cast hn
    dsimp [qmax, B] at *
    calc
      T / (n + 1 : Nat) * Phi * (Real.exp theta - 1) =
          B / (n + 1 : Nat) := by
        dsimp [B]
        field_simp
      _ <= (n : Real) / (n + 1 : Nat) :=
        div_le_div_of_nonneg_right hn' hden.le
      _ <= 1 := by
        rw [div_le_one hden]
        norm_num
  have hcost :
      L <= theta * eta - qmax * (Real.exp theta - 1) := by
    have hthetaEta : theta * eta = max L 0 + 2 := by
      dsimp [theta]
      field_simp
    rw [hthetaEta]
    linarith [le_max_left L 0]
  refine ⟨n, ?_⟩
  dsimp only
  exact
    (coordinateTail_upper_bound
      (partitionIntensity N P) eta theta qmax htheta.le hq).trans
      (EReal.neg_le_neg_iff.mpr (EReal.coe_le_coe_iff.mpr hcost))

theorem pathPartitionArray_eq
    {T : Real} (hT : 0 <= T) (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T) :
    PoissonPolygonalBridge.pathPartitionArray hT P x =
      PoissonSamplePath.pathPartitionArray hT P x := by
  rfl

theorem calendarPath_regular_start_zero
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega) (j : Server) (k : Buffer) :
    calendarPath N T K omega ⟨0, le_rfl, hT⟩ j k = 0 := by
  rw [show calendarPath N T K omega ⟨0, le_rfl, hT⟩ j k =
      calendarInputFunction N T K omega ⟨0, le_rfl, hT⟩ j k by
    exact congrFun (congrFun (congrFun
      (calendarPath_toFun_eq N T K omega hregular)
      ⟨0, le_rfl, hT⟩) j) k]
  simp [calendarInputFunction, Network.calendarScaledInput,
    Network.calendarTokenCount, Network.coordinateOperationalTime]

theorem calendarPath_regular_coordinate_monotone
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (omega : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : IsRegularSample omega) (j : Server) (k : Buffer) :
    Monotone (fun t : Horizon T => calendarPath N T K omega t j k) := by
  simpa only [calendarPath_toFun_eq N T K omega hregular,
    calendarInputFunction] using
    calendarScaledInput_monotone N T K omega hregular.2 j k

theorem maximumPartitionIncrement_le
    {T eta : Real} (hT : 0 <= T) (P : ActionPartition T)
    (x : Path (Buffer := Buffer) (Server := Server) T)
    (heta : 0 <= eta)
    (hcoord : forall a,
      PoissonPolygonalBridge.pathPartitionArray hT P x a <= eta) :
    maximumPartitionIncrement hT P x <= eta := by
  unfold maximumPartitionIncrement
  apply Finset.max'_le
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and] at hy
  rcases hy with rfl | ⟨a, rfl⟩
  · exact heta
  · exact hcoord a

theorem calendarPathLaw_le_polygonal_union
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (K : Nat) (P : ActionPartition T) (eta : Real) (heta : 0 < eta)
    (F : Set (Path (Buffer := Buffer) (Server := Server) T))
    (hF : MeasurableSet F) :
    calendarPathLaw N T K F <=
      PoissonFiniteArray.scaledLaw (partitionIntensity N P)
        (positiveSize K)
        ((polygonalize P) ⁻¹' Metric.cthickening eta F ∪
          coordinateTail eta) := by
  let speed : PNat := positiveSize K
  let raw : Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server) ->
      PartitionCoord (Buffer := Buffer) (Server := Server) P -> Real :=
    fun omega =>
      PoissonSamplePath.pathPartitionArray hT.le P
        (calendarPath N T speed omega)
  have htarget : MeasurableSet
      ((polygonalize P) ⁻¹' Metric.cthickening eta F ∪
        coordinateTail eta) := by
    apply MeasurableSet.union
    · exact Metric.isClosed_cthickening.measurableSet.preimage
        (continuous_polygonalize P).measurable
    · unfold coordinateTail
      have hopen : IsOpen
          (⋃ a : PartitionCoord
              (Buffer := Buffer) (Server := Server) P,
            {z : PartitionCoord
                (Buffer := Buffer) (Server := Server) P -> Real |
              eta < z a}) :=
        isOpen_iUnion fun a =>
          isOpen_lt
            (continuous_const : Continuous
              (fun _ : PartitionCoord
                (Buffer := Buffer) (Server := Server) P -> Real => eta))
            (continuous_apply a)
      simpa only [Set.setOf_exists] using hopen.measurableSet
  rw [calendarPathLaw_apply N hT K hF]
  calc
    N.calendarPoissonMeasure
        (calendarPath N T speed ⁻¹' F) <=
        N.calendarPoissonMeasure
          (raw ⁻¹'
            ((polygonalize P) ⁻¹' Metric.cthickening eta F ∪
              coordinateTail eta)) := by
      apply MeasureTheory.measure_mono_ae
      filter_upwards [regularSample_ae N] with omega hregular
      intro homega
      let x := calendarPath N T speed omega
      have hmono : forall j k,
          Monotone (fun t : Horizon T => x t j k) :=
        calendarPath_regular_coordinate_monotone
          N T speed omega hregular
      have hzero : forall j k,
          x ⟨0, le_rfl, hT.le⟩ j k = 0 :=
        calendarPath_regular_start_zero
          N hT.le speed omega hregular
      let z :=
        PoissonPolygonalBridge.pathPartitionArray hT.le P x
      by_cases htail : z ∈ coordinateTail eta
      · exact Or.inr (by simpa [raw, x, z, pathPartitionArray_eq] using htail)
      · left
        have hcoord : forall a, z a <= eta := by
          intro a
          exact le_of_not_gt fun ha =>
            htail ⟨a, ha⟩
        have hmax : maximumPartitionIncrement hT.le P x <= eta :=
          maximumPartitionIncrement_le hT.le P x heta.le hcoord
        have hj1 :
            j1EDist x (interpolatedPath hT.le P x hmono) <=
              ENNReal.ofReal eta :=
          (j1EDist_interpolatedPath_le hT P x hmono hzero).trans
            (ENNReal.ofReal_le_ofReal hmax)
        have hinterp :
            interpolatedPath hT.le P x hmono = polygonalize P z := by
          unfold interpolatedPath
          symm
          exact polygonalize_eq_of_nonnegative P z
            (pathPartitionArray_nonneg hT.le P x hmono)
        apply Metric.mem_cthickening_of_edist_le
          (polygonalize P z) x eta F homega
        rw [← hinterp, edist_comm]
        exact hj1
    _ = PoissonFiniteArray.scaledLaw (partitionIntensity N P)
          speed
          ((polygonalize P) ⁻¹' Metric.cthickening eta F ∪
            coordinateTail eta) := by
      exact (calendarPath_partitionArray_hasLaw
        N hT.le speed P).measure_eq htarget

theorem calendarPathLaw_massLeOne
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) :
    PoissonUpperAssembly.MassLeOne (calendarPathLaw N T) := by
  intro K
  letI := calendarPathLaw_isProbabilityMeasure N hT K
  simp

theorem scaledLaw_massLeOne
    {Coord : Type*} [Fintype Coord] (q : Coord -> NNReal) :
    PoissonUpperAssembly.MassLeOne
      (PoissonFiniteArray.scaledLaw q) := by
  intro K
  unfold PoissonFiniteArray.scaledLaw
  rw [Measure.map_apply_of_aemeasurable (by fun_prop) MeasurableSet.univ]
  simp

theorem calendarPathLaw_closed_upper_at_real_level
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (F : Set (Path (Buffer := Buffer) (Server := Server) T))
    (hF : IsClosed F) (c : Real)
    (hc : (c : EReal) <
      (rateInf
        (fun x : Path (Buffer := Buffer) (Server := Server) T =>
          poissonPathRate N T (asMatrix T x)) F : EReal)) :
    limsup (scaledLogMass (calendarPathLaw N T) F) atTop <=
      -(c : EReal) := by
  let I : Path (Buffer := Buffer) (Server := Server) T -> ENNReal :=
    fun x => poissonPathRate N T (asMatrix T x)
  by_cases hc0 : 0 <= c
  · let S : Set (Path (Buffer := Buffer) (Server := Server) T) :=
      {x | I x <= ENNReal.ofReal c}
    have hScompact : IsCompact S := by
      exact isCompact_poissonPathRate_sublevel N hT c
    have hdisj : Disjoint S F := by
      rw [Set.disjoint_left]
      intro x hxS hxF
      have hrate : rateInf I F <= I x := by
        unfold rateInf
        exact sInf_le ⟨x, hxF, rfl⟩
      have hcx : (c : EReal) < (I x : EReal) :=
        hc.trans_le (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hrate)
      have hxle : (I x : EReal) <= (c : EReal) := by
        have := EReal.coe_ennreal_le_coe_ennreal_iff.mpr hxS
        simpa [EReal.coe_ennreal_ofReal, max_eq_left hc0] using this
      exact (not_lt_of_ge hxle) hcx
    obtain ⟨eta, heta, hsep⟩ :=
      hdisj.exists_cthickenings hScompact hF
    obtain ⟨n, htail⟩ :=
      exists_uniform_partition_coordinateTail_upper
        N hT eta heta c
    let P := uniformActionPartition T hT n
    let q : PartitionCoord
        (Buffer := Buffer) (Server := Server) P -> NNReal :=
      partitionIntensity N P
    let B : Set (PartitionCoord
        (Buffer := Buffer) (Server := Server) P -> Real) :=
      (polygonalize P) ⁻¹' Metric.cthickening eta F
    let tail : Set (PartitionCoord
        (Buffer := Buffer) (Server := Server) P -> Real) :=
      coordinateTail eta
    have hBclosed : IsClosed B := by
      exact Metric.isClosed_cthickening.preimage (continuous_polygonalize P)
    have hrateB :
        ENNReal.ofReal c <=
          rateInf (PoissonFiniteArray.action q) B := by
      unfold rateInf
      apply le_sInf
      intro y hy
      rcases hy with ⟨z, hzB, rfl⟩
      by_cases htop :
          PoissonFiniteArray.action q z = (Top.top : ENNReal)
      · simp [htop]
      have hadm : PoissonFiniteArray.Admissible q z :=
        PoissonFiniteArray.admissible_of_action_ne_top q z htop
      have hpolyRate :
          I (polygonalize P z) = PoissonFiniteArray.action q z := by
        rw [polygonalize_eq_of_nonnegative P z
          (fun a => (hadm a).1)]
        exact poissonPathRate_polygonal N hT P z hadm
      by_contra hle
      have hlt :
          PoissonFiniteArray.action q z < ENNReal.ofReal c :=
        lt_of_not_ge hle
      have hpolyS : polygonalize P z ∈ S := by
        change I (polygonalize P z) <= ENNReal.ofReal c
        rw [hpolyRate]
        exact hlt.le
      have hleft :
          polygonalize P z ∈ Metric.cthickening eta S :=
        Metric.self_subset_cthickening S hpolyS
      exact Set.disjoint_left.mp hsep hleft hzB
    have hBupper :
        limsup
            (scaledLogMass (PoissonFiniteArray.scaledLaw q) B) atTop <=
          -(c : EReal) := by
      refine (PoissonFiniteArray.closed_upper_bound q B hBclosed).trans ?_
      apply EReal.neg_le_neg_iff.mpr
      have hcoe :
          ((ENNReal.ofReal c : ENNReal) : EReal) <=
            (rateInf (PoissonFiniteArray.action q) B : EReal) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.mpr hrateB
      simpa [EReal.coe_ennreal_ofReal, max_eq_left hc0] using hcoe
    have htail' :
        limsup
            (scaledLogMass (PoissonFiniteArray.scaledLaw q) tail) atTop <=
          -(c : EReal) := by
      simpa only [P, q, tail] using htail
    have hunion :
        limsup
            (scaledLogMass (PoissonFiniteArray.scaledLaw q) (B ∪ tail))
            atTop <= -(c : EReal) := by
      exact
        (PoissonUpperAssembly.limsup_scaledLogMass_union_le_max
          (PoissonFiniteArray.scaledLaw q) (scaledLaw_massLeOne q)
          B tail).trans (max_le hBupper htail')
    have hpoint (K : Nat) :
        scaledLogMass (calendarPathLaw N T) F K <=
          scaledLogMass (PoissonFiniteArray.scaledLaw q) (B ∪ tail) K := by
      unfold scaledLogMass
      apply EReal.div_le_div_right_of_nonneg (by positivity)
      apply ENNReal.log_le_log
      simpa only [P, q, B, tail, positiveSize_succ_val] using
        calendarPathLaw_le_polygonal_union
          N hT (K + 1) P eta heta F hF.measurableSet
    exact
      (limsup_le_limsup
        (Eventually.of_forall hpoint)
        (Filter.isCoboundedUnder_le_of_le atTop fun _ => bot_le)
        (Filter.isBoundedUnder_of_eventually_le
          (Eventually.of_forall
            (PoissonUpperAssembly.scaledLogMass_nonpos_of_mass_le_one
              (PoissonFiniteArray.scaledLaw q)
              (scaledLaw_massLeOne q) (B ∪ tail))))).trans hunion
  · exact
      (PoissonUpperAssembly.limsup_scaledLogMass_nonpos_of_mass_le_one
        (calendarPathLaw N T) (calendarPathLaw_massLeOne N hT) F).trans
        (EReal.neg_nonneg.mpr
          (EReal.coe_nonpos.mpr (le_of_not_ge hc0)))

theorem calendarPathLaw_closed_upper_bound
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (F : Set (Path (Buffer := Buffer) (Server := Server) T))
    (hF : IsClosed F) :
    limsup (scaledLogMass (calendarPathLaw N T) F) atTop <=
      -(rateInf
        (fun x : Path (Buffer := Buffer) (Server := Server) T =>
          poissonPathRate N T (asMatrix T x)) F : EReal) := by
  by_contra hle
  have hlt :
      -(rateInf
          (fun x : Path (Buffer := Buffer) (Server := Server) T =>
            poissonPathRate N T (asMatrix T x)) F : EReal) <
        limsup (scaledLogMass (calendarPathLaw N T) F) atTop :=
    lt_of_not_ge hle
  obtain ⟨y, hry, hyL⟩ := EReal.exists_between_coe_real hlt
  have hc :
      ((-y : Real) : EReal) <
        (rateInf
          (fun x : Path (Buffer := Buffer) (Server := Server) T =>
            poissonPathRate N T (asMatrix T x)) F : EReal) := by
    have hneg := EReal.neg_lt_neg_iff.mpr hry
    simpa using hneg
  have hbound :=
    calendarPathLaw_closed_upper_at_real_level
      N hT F hF (-y) hc
  have hbound' :
      limsup (scaledLogMass (calendarPathLaw N T) F) atTop <=
        (y : EReal) := by
    simpa using hbound
  exact (not_le_of_gt hyL) hbound'

theorem concreteSamplePathLDPStatement
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) :
    PoissonSamplePath.ConcreteSamplePathLDPStatement N T := by
  rw [PoissonSamplePath.ConcreteSamplePathLDPStatement,
    PaperStatements.SamplePathLDPStatement]
  refine ⟨hT, ?_⟩
  let I : Path (Buffer := Buffer) (Server := Server) T -> ENNReal :=
    fun x => poissonPathRate N T (asMatrix T x)
  refine ⟨isCompact_poissonPathRate_sublevel N hT, ?_⟩
  intro event hevent
  refine ⟨?_, ?_, ?_⟩
  · calc
      -(rateInf I (interior event) : EReal) <=
          liminf
            (scaledLogMass (calendarPathLaw N T) (interior event)) atTop :=
        calendarPath_open_lower_bound N hT
          (interior event) isOpen_interior
      _ <= liminf (scaledLogMass (calendarPathLaw N T) event) atTop := by
        apply liminf_le_liminf
        · exact Eventually.of_forall fun K =>
            EReal.div_le_div_right_of_nonneg (by positivity)
              (ENNReal.log_le_log (measure_mono interior_subset))
        · exact Filter.isBoundedUnder_of
            ⟨(Bot.bot : EReal), fun _ => bot_le⟩
        · exact Filter.isCoboundedUnder_ge_of_le atTop
            (PoissonUpperAssembly.scaledLogMass_nonpos_of_mass_le_one
              (calendarPathLaw N T) (calendarPathLaw_massLeOne N hT) event)
  · exact liminf_le_limsup
      (Filter.isBoundedUnder_of_eventually_le
        (Eventually.of_forall
          (PoissonUpperAssembly.scaledLogMass_nonpos_of_mass_le_one
            (calendarPathLaw N T) (calendarPathLaw_massLeOne N hT) event)))
      (Filter.isBoundedUnder_of
        ⟨(Bot.bot : EReal), fun _ => bot_le⟩)
  · calc
      limsup (scaledLogMass (calendarPathLaw N T) event) atTop <=
          limsup
            (scaledLogMass (calendarPathLaw N T) (closure event)) atTop := by
        apply limsup_le_limsup
        · exact Eventually.of_forall fun K =>
            EReal.div_le_div_right_of_nonneg (by positivity)
              (ENNReal.log_le_log (measure_mono subset_closure))
        · exact Filter.isCoboundedUnder_le_of_le atTop fun _ => bot_le
        · exact Filter.isBoundedUnder_of_eventually_le
            (Eventually.of_forall
              (PoissonUpperAssembly.scaledLogMass_nonpos_of_mass_le_one
                (calendarPathLaw N T) (calendarPathLaw_massLeOne N hT)
                (closure event)))
      _ <= -(rateInf I (closure event) : EReal) :=
        calendarPathLaw_closed_upper_bound
          N hT (closure event) isClosed_closure

end PoissonUpperFinal
end StateDepMOR

namespace StateDepMOR.PoissonSamplePath

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

theorem calendarPathLaw_closed_upper_bound
    (N : Network Buffer Server) {T : Real} (hT : 0 < T)
    (F : Set (Path (Buffer := Buffer) (Server := Server) T))
    (hF : IsClosed F) :
    limsup (scaledLogMass (calendarPathLaw N T) F) atTop <=
      -(rateInf
        (fun x : Path (Buffer := Buffer) (Server := Server) T =>
          poissonPathRate N T (asMatrix T x)) F : EReal) :=
  PoissonUpperFinal.calendarPathLaw_closed_upper_bound N hT F hF

theorem concreteSamplePathLDP
    (N : Network Buffer Server) {T : Real} (hT : 0 < T) :
    ConcreteSamplePathLDPStatement N T :=
  PoissonUpperFinal.concreteSamplePathLDPStatement N hT

end StateDepMOR.PoissonSamplePath
