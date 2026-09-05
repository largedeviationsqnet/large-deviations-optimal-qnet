import StateDepMOR.EventEpochExecution
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.StrongLaw

/-!
# Calendar-time marked Poisson execution

This module constructs the paper's continuous-time primitive from independent
unit-rate exponential interarrival sequences.  For system size `K`, coordinate
`(j,k)` is evaluated at operational time `K * phi j k * t`.  Queue and
allocation paths are driven by the finite merge of all coordinate arrivals up
to calendar time `t`.

Mathlib currently has no bundled Poisson-process or renewal-counting-process
API.  The construction below therefore exposes the interarrivals, renewal
epochs, generalized inverse, chronological merge, and queue recursion
directly.
-/

open Filter MeasureTheory ProbabilityTheory Set

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer]

namespace Network

variable (N : Network Buffer Server)

/-- One canonical unit-rate clock, represented by its interarrival times. -/
abbrev UnitRateClockPath := Nat -> Real

/-- One independent unit-rate clock for every marked token coordinate. -/
abbrev CalendarPoissonSample :=
  Server -> Buffer -> UnitRateClockPath

noncomputable instance unitExpIsProbabilityMeasure :
    IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure zero_lt_one

/-- The identity is integrable under the unit-rate exponential law. -/
theorem unitExp_integrable :
    Integrable (fun x : Real => x) (expMeasure 1) := by
  rw [expMeasure, gammaMeasure]
  have hpdf : Measurable (gammaPDF 1 1) := by
    exact (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [integrable_withDensity_iff
    hpdf (by simp [gammaPDF])]
  have hpos :
      IntegrableOn (fun x : Real => x * Real.exp (-x)) (Ioi 0) := by
    convert Real.GammaIntegral_convergent (s := (2 : Real)) (by norm_num) using 1
    ext x
    norm_num [Real.rpow_one, mul_comm]
  have hindicator :
      Integrable
        ((Ioi (0 : Real)).indicator
          (fun x : Real => x * Real.exp (-x))) :=
    hpos.integrable_indicator measurableSet_Ioi
  apply hindicator.congr
  filter_upwards [] with x
  by_cases hx : 0 < x
  · simp [gammaPDF, gammaPDFReal, hx.le, hx, Real.Gamma_one,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  · have hx' : x <= 0 := le_of_not_gt hx
    rcases hx'.eq_or_lt with rfl | hxneg
    · simp [gammaPDF, gammaPDFReal]
    · simp [gammaPDF, gammaPDFReal, not_le_of_gt hxneg, hx]

/-- A unit-rate exponential random variable has mean one. -/
theorem unitExp_integral :
    integral (expMeasure 1) (fun x : Real => x) = 1 := by
  rw [expMeasure, gammaMeasure]
  have hpdf : Measurable (gammaPDF 1 1) := by
    exact (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul
    hpdf (by simp [gammaPDF])]
  have heq :
      (fun x : Real => (gammaPDF 1 1 x).toReal • x) =
        (Ioi (0 : Real)).indicator
          (fun x : Real => x ^ ((2 : Real) - 1) * Real.exp (-(1 * x))) := by
    funext x
    by_cases hx : 0 < x
    · norm_num [gammaPDF, gammaPDFReal, hx, hx.le, Real.Gamma_one,
        Real.rpow_one, mul_comm,
        ENNReal.toReal_ofReal (Real.exp_pos _).le]
    · have hx' : x <= 0 := le_of_not_gt hx
      rcases hx'.eq_or_lt with rfl | hxneg
      · simp [gammaPDF, gammaPDFReal]
      · simp [gammaPDF, gammaPDFReal, not_le_of_gt hxneg, hx]
  rw [heq, integral_indicator measurableSet_Ioi,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (by norm_num)]
  norm_num [Real.Gamma_nat_eq_factorial]

/-- Law of one IID sequence of unit-rate exponential interarrivals. -/
noncomputable def unitRateClockMeasure : Measure UnitRateClockPath :=
  Measure.infinitePi (fun _ : Nat => expMeasure 1)

noncomputable instance unitRateClockMeasure_isProbabilityMeasure :
    IsProbabilityMeasure unitRateClockMeasure := by
  unfold unitRateClockMeasure
  infer_instance

/-- Independent product law of all marked-token coordinate clocks. -/
noncomputable def calendarPoissonMeasure :
    Measure (CalendarPoissonSample (Buffer := Buffer) (Server := Server)) :=
  let _ := N
  Measure.pi fun _ : Server =>
    Measure.pi fun _ : Buffer => unitRateClockMeasure

noncomputable instance calendarPoissonMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (N.calendarPoissonMeasure) := by
  unfold calendarPoissonMeasure
  infer_instance

/-- The `r`-th interarrival time of coordinate `(j,k)`. -/
def clockInterarrival
    (j : Server) (k : Buffer) (r : Nat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) :
    Real :=
  omega j k r

/-- Every interarrival coordinate has the unit-rate exponential law. -/
theorem clockInterarrival_map
    (j : Server) (k : Buffer) (r : Nat) :
    N.calendarPoissonMeasure.map (clockInterarrival j k r) =
      expMeasure 1 := by
  classical
  unfold calendarPoissonMeasure clockInterarrival unitRateClockMeasure
  change
    Measure.map
      ((Function.eval r) ∘ (Function.eval k) ∘ (Function.eval j))
      (Measure.pi fun _ : Server =>
        Measure.pi fun _ : Buffer =>
          Measure.infinitePi fun _ : Nat => expMeasure 1) = _
  rw [← Measure.map_map (measurable_pi_apply r)
      ((measurable_pi_apply k).comp (measurable_pi_apply j))]
  rw [← Measure.map_map (measurable_pi_apply k) (measurable_pi_apply j)]
  rw [Measure.pi_map_eval]
  simp only [measure_univ, Finset.prod_const_one, one_smul]
  rw [Measure.pi_map_eval]
  simp only [measure_univ, Finset.prod_const_one, one_smul]
  exact Measure.infinitePi_map_eval
    (fun _ : Nat => expMeasure 1) r

/-- Projection to one complete marked clock has the canonical IID clock law. -/
theorem coordinateClock_map (j : Server) (k : Buffer) :
    N.calendarPoissonMeasure.map
        (fun omega : CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) => omega j k) =
      unitRateClockMeasure := by
  classical
  unfold calendarPoissonMeasure unitRateClockMeasure
  change
    Measure.map
        ((Function.eval k) ∘ (Function.eval j))
        (Measure.pi fun _ : Server =>
          Measure.pi fun _ : Buffer =>
            Measure.infinitePi fun _ : Nat => expMeasure 1) =
      Measure.infinitePi fun _ : Nat => expMeasure 1
  rw [← Measure.map_map (measurable_pi_apply k) (measurable_pi_apply j)]
  rw [Measure.pi_map_eval]
  simp only [measure_univ, Finset.prod_const_one, one_smul]
  rw [Measure.pi_map_eval]
  simp

/-- Within each marked coordinate, the interarrival sequence is independent. -/
theorem coordinateInterarrival_iIndep (j : Server) (k : Buffer) :
    iIndepFun
      (fun r : Nat =>
        fun omega : CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) => omega j k r)
      N.calendarPoissonMeasure := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]
  change
    N.calendarPoissonMeasure.map
        (fun omega : CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) => omega j k) =
      Measure.infinitePi
        (fun r : Nat =>
          N.calendarPoissonMeasure.map (clockInterarrival j k r))
  rw [N.coordinateClock_map]
  unfold unitRateClockMeasure
  congr 1
  funext r
  exact (N.clockInterarrival_map j k r).symm

/-- Coordinate clock paths are mutually independent. -/
theorem coordinateClock_iIndep :
    iIndepFun
      (fun p : Sigma (fun _ : Server => Buffer) =>
        fun omega : CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) => omega p.1 p.2)
      N.calendarPoissonMeasure := by
  classical
  unfold calendarPoissonMeasure
  refine iIndepFun_uncurry
    (P := Measure.pi fun _ : Server =>
      Measure.pi fun _ : Buffer => unitRateClockMeasure)
    (X := fun j k omega => omega j k) (by fun_prop) ?_ ?_
  · exact iIndepFun_pi
      (X := fun _ (clock : Buffer -> UnitRateClockPath) => clock)
      fun _ => Measurable.aemeasurable (by fun_prop)
  · intro j
    rw [iIndepFun_iff_map_fun_eq_pi_map
      (fun _ => Measurable.aemeasurable (by fun_prop))]
    have hleft :
        Measure.map
            (fun omega : CalendarPoissonSample
              (Buffer := Buffer) (Server := Server) => omega j)
            (Measure.pi fun _ : Server =>
              Measure.pi fun _ : Buffer => unitRateClockMeasure) =
          Measure.pi fun _ : Buffer => unitRateClockMeasure := by
      rw [Measure.pi_map_eval]
      simp
    rw [hleft]
    congr 1
    funext k
    change unitRateClockMeasure =
      Measure.map
        ((Function.eval k) ∘ (Function.eval j))
        (Measure.pi fun _ : Server =>
          Measure.pi fun _ : Buffer => unitRateClockMeasure)
    rw [← Measure.map_map (measurable_pi_apply k) (measurable_pi_apply j)]
    rw [Measure.pi_map_eval]
    simp only [measure_univ, Finset.prod_const_one, one_smul]
    rw [Measure.pi_map_eval]
    simp

/-- Epoch of the `n`-th renewal, with epoch zero equal to zero. -/
def renewalEpoch (clock : UnitRateClockPath) (n : Nat) : Real :=
  ∑ r ∈ Finset.range n, clock r

@[simp]
theorem renewalEpoch_zero (clock : UnitRateClockPath) :
    renewalEpoch clock 0 = 0 := by
  simp [renewalEpoch]

theorem renewalEpoch_succ (clock : UnitRateClockPath) (n : Nat) :
    renewalEpoch clock (n + 1) = renewalEpoch clock n + clock n := by
  simp [renewalEpoch, Finset.sum_range_succ]

/-- The renewal epochs of one marked coordinate obey the strong law on the
outer product space. -/
theorem renewalEpoch_ratio_tendsto_ae (j : Server) (k : Buffer) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      Tendsto
        (fun n : Nat =>
          renewalEpoch (omega j k) n / (n : Real))
        atTop (nhds 1) := by
  let X : Nat ->
      CalendarPoissonSample (Buffer := Buffer) (Server := Server) -> Real :=
    fun r omega => omega j k r
  have hXmap (r : Nat) :
      N.calendarPoissonMeasure.map (X r) = expMeasure 1 := by
    exact N.clockInterarrival_map j k r
  have hXintegrable : Integrable (X 0) N.calendarPoissonMeasure := by
    have hbase :
        Integrable (fun x : Real => x)
          (N.calendarPoissonMeasure.map (X 0)) := by
      rw [hXmap]
      exact unitExp_integrable
    have hcomp := hbase.comp_measurable (by fun_prop)
    simpa [Function.comp_def] using hcomp
  have hXindep : Pairwise ((fun r s => IndepFun (X r) (X s)
      N.calendarPoissonMeasure)) := by
    intro r s hrs
    exact (N.coordinateInterarrival_iIndep j k).indepFun hrs
  have hXident : forall r, IdentDistrib (X r) (X 0)
      N.calendarPoissonMeasure N.calendarPoissonMeasure := by
    intro r
    refine ⟨by fun_prop, by fun_prop, ?_⟩
    rw [hXmap r, hXmap 0]
  have hmean :
      integral N.calendarPoissonMeasure (X 0) = 1 := by
    calc
      integral N.calendarPoissonMeasure (X 0) =
          integral (N.calendarPoissonMeasure.map (X 0))
            (fun x : Real => x) := by
              rw [integral_map (by fun_prop) (by fun_prop)]
      _ = integral (expMeasure 1) (fun x : Real => x) := by rw [hXmap]
      _ = 1 := unitExp_integral
  have hstrong :=
    strong_law_ae_real X hXintegrable hXindep hXident
  simpa only [X, renewalEpoch, hmean] using hstrong

/-- One common probability-one event carries the renewal strong law for every
marked coordinate. -/
theorem all_renewalEpoch_ratio_tendsto_ae :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      forall j k,
        Tendsto
          (fun n : Nat =>
            renewalEpoch (omega j k) n / (n : Real))
          atTop (nhds 1) := by
  rw [ae_all_iff]
  intro j
  rw [ae_all_iff]
  intro k
  exact N.renewalEpoch_ratio_tendsto_ae j k

/-- Generalized inverse of renewal epochs.

For positive operational time `s`, this is one less than the first epoch
strictly after `s`.  The fallback value on a path whose epochs never cross
`s` keeps the process total on the entire canonical sample space. -/
noncomputable def unitPoissonCount
    (clock : UnitRateClockPath) (s : Real) : Nat := by
  classical
  exact if hs : 0 < s /\ Exists (fun n => s < renewalEpoch clock n) then
      Nat.find hs.2 - 1
    else
      0

theorem unitPoissonCount_eq_find
    (clock : UnitRateClockPath) {s : Real} (hs : 0 < s)
    (hexists : Exists (fun n => s < renewalEpoch clock n)) :
    unitPoissonCount clock s = Nat.find hexists - 1 := by
  classical
  simp [unitPoissonCount, hs, hexists]

theorem one_le_find_renewal_crossing
    (clock : UnitRateClockPath) {s : Real} (hs : 0 < s)
    (hexists : Exists (fun n => s < renewalEpoch clock n)) :
    1 <= Nat.find hexists := by
  apply Nat.one_le_iff_ne_zero.mpr
  intro hzero
  have hcross := Nat.find_spec hexists
  rw [hzero, renewalEpoch_zero] at hcross
  linarith

theorem unitPoissonCount_add_one
    (clock : UnitRateClockPath) {s : Real} (hs : 0 < s)
    (hexists : Exists (fun n => s < renewalEpoch clock n)) :
    unitPoissonCount clock s + 1 = Nat.find hexists := by
  rw [unitPoissonCount_eq_find clock hs hexists]
  exact Nat.sub_add_cancel (one_le_find_renewal_crossing clock hs hexists)

/-- The last counted renewal epoch is no later than the operational time. -/
theorem renewalEpoch_count_le
    (clock : UnitRateClockPath) {s : Real} (hs : 0 < s)
    (hexists : Exists (fun n => s < renewalEpoch clock n)) :
    renewalEpoch clock (unitPoissonCount clock s) <= s := by
  have hfind := one_le_find_renewal_crossing clock hs hexists
  have hlt :
      unitPoissonCount clock s < Nat.find hexists := by
    rw [unitPoissonCount_eq_find clock hs hexists]
    omega
  exact le_of_not_gt (Nat.find_min hexists hlt)

/-- The first uncounted renewal epoch is strictly after the operational time. -/
theorem lt_renewalEpoch_count_add_one
    (clock : UnitRateClockPath) {s : Real} (hs : 0 < s)
    (hexists : Exists (fun n => s < renewalEpoch clock n)) :
    s < renewalEpoch clock (unitPoissonCount clock s + 1) := by
  rw [unitPoissonCount_add_one clock hs hexists]
  exact Nat.find_spec hexists

/-- Deterministic inversion of the renewal strong law. -/
theorem unitPoissonCount_ratio_tendsto
    (clock : UnitRateClockPath)
    (hEpoch :
      Tendsto
        (fun n : Nat => renewalEpoch clock n / (n : Real))
        atTop (nhds 1))
    {s : Nat -> Real} (hsTop : Tendsto s atTop atTop) :
    Tendsto
      (fun r => (unitPoissonCount clock (s r) : Real) / s r)
      atTop (nhds 1) := by
  have hepochTop :
      Tendsto (fun n : Nat => renewalEpoch clock n) atTop atTop := by
    have hprod :=
      hEpoch.pos_mul_atTop zero_lt_one tendsto_natCast_atTop_atTop
    apply hprod.congr'
    filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
    simp [Nat.ne_of_gt hn]
  have hcross (r : Nat) :
      Exists (fun n => s r < renewalEpoch clock n) :=
    (hepochTop.eventually_gt_atTop (s r)).exists
  let c : Nat -> Nat := fun r => unitPoissonCount clock (s r)
  have hsPos : ∀ᶠ r in atTop, 0 < s r :=
    hsTop.eventually_gt_atTop 0
  have hcTop : Tendsto c atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    let B : Real :=
      ∑ n ∈ Finset.range (b + 1), |renewalEpoch clock n|
    filter_upwards [hsTop.eventually_gt_atTop B, hsPos] with r hrB hrs
    by_contra hcb
    have hclt : c r < b := Nat.lt_of_not_ge hcb
    have hadd :
        c r + 1 = Nat.find (hcross r) := by
      exact unitPoissonCount_add_one clock hrs (hcross r)
    have hfind_le : Nat.find (hcross r) <= b := by omega
    have hmem : Nat.find (hcross r) ∈ Finset.range (b + 1) := by
      simp only [Finset.mem_range]
      omega
    have habs_le :
        |renewalEpoch clock (Nat.find (hcross r))| <= B := by
      dsimp only [B]
      exact Finset.single_le_sum
        (fun n _ => abs_nonneg (renewalEpoch clock n)) hmem
    have hvalue_le :
        renewalEpoch clock (Nat.find (hcross r)) <= B :=
      le_trans (le_abs_self _) habs_le
    have hvalue_gt :
        s r < renewalEpoch clock (Nat.find (hcross r)) :=
      Nat.find_spec (hcross r)
    linarith
  have hcSuccTop : Tendsto (fun r => c r + 1) atTop atTop :=
    tendsto_atTop_mono (fun r => Nat.le_add_right (c r) 1) hcTop
  have hratioC :
      Tendsto
        (fun r => renewalEpoch clock (c r) / (c r : Real))
        atTop (nhds 1) :=
    hEpoch.comp hcTop
  have hratioSucc :
      Tendsto
        (fun r =>
          renewalEpoch clock (c r + 1) / ((c r + 1 : Nat) : Real))
        atTop (nhds 1) :=
    hEpoch.comp hcSuccTop
  have hcPos : ∀ᶠ r in atTop, 0 < c r :=
    hcTop.eventually_gt_atTop 0
  have hratioCPos : ∀ᶠ r in atTop,
      0 < renewalEpoch clock (c r) / (c r : Real) :=
    hratioC.eventually (Ioi_mem_nhds zero_lt_one)
  have hratioSuccPos : ∀ᶠ r in atTop,
      0 < renewalEpoch clock (c r + 1) / ((c r + 1 : Nat) : Real) :=
    hratioSucc.eventually (Ioi_mem_nhds zero_lt_one)
  have hlower :
      Tendsto
        (fun r =>
          (renewalEpoch clock (c r + 1) /
              ((c r + 1 : Nat) : Real))⁻¹ -
            (s r)⁻¹)
        atTop (nhds 1) := by
    convert (hratioSucc.inv₀ one_ne_zero).sub
      (hsTop.inv_tendsto_atTop) using 1 <;> norm_num
  have hupper :
      Tendsto
        (fun r =>
          (renewalEpoch clock (c r) / (c r : Real))⁻¹)
        atTop (nhds 1) := by
    simpa using hratioC.inv₀ one_ne_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [hsPos, hratioSuccPos] with r hrs hratioSr
    change
      (renewalEpoch clock (c r + 1) /
            ((c r + 1 : Nat) : Real))⁻¹ -
          (s r)⁻¹ <= (c r : Real) / s r
    have hs_lt_epoch :
        s r < renewalEpoch clock (c r + 1) :=
      lt_renewalEpoch_count_add_one clock hrs (hcross r)
    have hsuccReal : 0 < ((c r + 1 : Nat) : Real) := by positivity
    have hepochSuccPos : 0 < renewalEpoch clock (c r + 1) := by
      rcases div_pos_iff.mp hratioSr with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_lt_of_ge hsuccReal.le) hneg.2)
    have hdiv :
        ((c r + 1 : Nat) : Real) /
            renewalEpoch clock (c r + 1) <
          ((c r + 1 : Nat) : Real) / s r := by
      exact (div_lt_div_iff₀ hepochSuccPos hrs).2
        (mul_lt_mul_of_pos_left hs_lt_epoch hsuccReal)
    calc
      (renewalEpoch clock (c r + 1) /
              ((c r + 1 : Nat) : Real))⁻¹ -
            (s r)⁻¹ =
          ((c r + 1 : Nat) : Real) /
              renewalEpoch clock (c r + 1) - 1 / s r := by
                field_simp
      _ <= ((c r + 1 : Nat) : Real) / s r - 1 / s r :=
        (sub_le_sub_right hdiv.le _)
      _ = (c r : Real) / s r := by
        push_cast
        ring
  · filter_upwards [hsPos, hcPos, hratioCPos] with
        r hrs hcr hratioCr
    change
      (c r : Real) / s r <=
        (renewalEpoch clock (c r) / (c r : Real))⁻¹
    have hepoch_le :
        renewalEpoch clock (c r) <= s r :=
      renewalEpoch_count_le clock hrs (hcross r)
    have hcReal : 0 < (c r : Real) := by exact_mod_cast hcr
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hrs hratioCr).2
    calc
      (c r : Real) *
          (renewalEpoch clock (c r) / (c r : Real)) =
          renewalEpoch clock (c r) := by
            field_simp [ne_of_gt hcReal]
      _ <= s r := hepoch_le
      _ = 1 * s r := by ring

@[simp]
theorem unitPoissonCount_of_nonpos
    (clock : UnitRateClockPath) {s : Real} (hs : s <= 0) :
    unitPoissonCount clock s = 0 := by
  simp [unitPoissonCount, not_lt_of_ge hs]

/-- Operational time used by the paper for coordinate `(j,k)`. -/
def coordinateOperationalTime
    (K : PNat) (t : Real) (j : Server) (k : Buffer) : Real :=
  ((K : Nat) : Real) * N.phi j k * max t 0

/-- Calendar-time token count
`N_{jk}(K * phi[j,k] * max(t,0))`. -/
noncomputable def calendarTokenCount
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) : Nat :=
  unitPoissonCount (omega j k) (N.coordinateOperationalTime K t j k)

@[simp]
theorem calendarTokenCount_of_phi_eq_zero
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer)
    (hphi : N.phi j k = 0) :
    N.calendarTokenCount K omega t j k = 0 := by
  simp [calendarTokenCount, coordinateOperationalTime, hphi,
    unitPoissonCount]

@[simp]
theorem calendarTokenCount_of_nonpos
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    {t : Real} (ht : t <= 0) (j : Server) (k : Buffer) :
    N.calendarTokenCount K omega t j k = 0 := by
  simp [calendarTokenCount, coordinateOperationalTime, max_eq_right ht,
    unitPoissonCount]

/-- Fluid-scaled primitive input. -/
noncomputable def calendarScaledInput
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) : Real :=
  (N.calendarTokenCount K omega t j k : Real) / ((K : Nat) : Real)

private theorem calendar_pnatVal_strictMono
    {K : Nat -> PNat} (hK : StrictMono K) :
    StrictMono (fun r => (K r : Nat)) := by
  intro r q hrq
  exact hK hrq

/-- On the common renewal strong-law event, every fixed-time coordinate has
the paper's nominal calendar-time fluid limit. -/
theorem calendarScaledInput_tendsto
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (homega :
      forall j k,
        Tendsto
          (fun n : Nat =>
            renewalEpoch (omega j k) n / (n : Real))
          atTop (nhds 1))
    (K : Nat -> PNat) (hK : StrictMono K)
    (t : Real) (ht : 0 <= t) (j : Server) (k : Buffer) :
    Tendsto
      (fun r => N.calendarScaledInput (K r) omega t j k)
      atTop (nhds (N.phi j k * t)) := by
  rcases ht.eq_or_lt with rfl | htpos
  · simp [calendarScaledInput]
  rcases (N.phi_nonneg j k).eq_or_lt with hphi | hphi
  · have hphi0 : N.phi j k = 0 := hphi.symm
    simp [calendarScaledInput, hphi0]
  have hKval :
      Tendsto (fun r => (K r : Nat)) atTop atTop :=
    (calendar_pnatVal_strictMono hK).tendsto_atTop
  have hKreal :
      Tendsto (fun r => ((K r : Nat) : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hKval
  have hoperational :
      Tendsto
        (fun r =>
          N.coordinateOperationalTime (K r) t j k)
        atTop atTop := by
    simpa [coordinateOperationalTime, max_eq_left htpos.le, mul_assoc] using
      hKreal.atTop_mul_const (mul_pos hphi htpos)
  have hcountRatio :=
    unitPoissonCount_ratio_tendsto (omega j k) (homega j k)
      hoperational
  have hscaled :=
    hcountRatio.mul_const (N.phi j k * t)
  convert hscaled using 1
  · funext r
    simp only [calendarScaledInput, calendarTokenCount,
      coordinateOperationalTime, max_eq_left htpos.le]
    have hKpos : 0 < ((K r : Nat) : Real) := by positivity
    have hrate : 0 < N.phi j k * t := mul_pos hphi htpos
    field_simp [ne_of_gt hKpos, ne_of_gt hrate]
  · simp

/-- A coordinate-local arrival record `(j,k,r)`, where `r` is zero based. -/
abbrev CalendarEvent := (Server × Buffer) × Nat

/-- Calendar time of one coordinate-local arrival. -/
noncomputable def calendarEventTime
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (event : CalendarEvent (Buffer := Buffer) (Server := Server)) : Real :=
  renewalEpoch (omega event.1.1 event.1.2) (event.2 + 1) /
    (((K : Nat) : Real) * N.phi event.1.1 event.1.2)

/-- All coordinate-local records counted by time `t`, before chronological
sorting. -/
noncomputable def rawCalendarEvents
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    List (CalendarEvent (Buffer := Buffer) (Server := Server)) := by
  classical
  exact Finset.univ.toList.flatMap fun j =>
    Finset.univ.toList.flatMap fun k =>
      (Finset.range (N.calendarTokenCount K omega t j k)).toList.map
        fun r => ((j, k), r)

/-- Finite chronological merge of all marked coordinate arrivals. -/
noncomputable def chronologicalCalendarEvents
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    List (CalendarEvent (Buffer := Buffer) (Server := Server)) := by
  classical
  exact (N.rawCalendarEvents K omega t).insertionSort
    fun a b => N.calendarEventTime K omega a <=
      N.calendarEventTime K omega b

/-- Marked token list in actual calendar-time order. -/
noncomputable def calendarTokenPrefix
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  (N.chronologicalCalendarEvents K omega t).map fun event => event.1

/-- Queue state obtained by processing every token up to calendar time `t`,
starting from an arbitrary state with `K` jobs. -/
noncomputable def calendarScaledQueueStateFrom
    (U : N.DeterministicPolicySequence)
    (K : PNat)
    (x0 : JobState Buffer (K : Nat))
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (i : Buffer) : Real :=
  (N.runTokens (U K) x0
      (N.calendarTokenPrefix K omega t) i : Real) /
    ((K : Nat) : Real)

/-- Queue state for the canonical initial condition used by the bundled
calendar execution. -/
noncomputable def calendarScaledQueueState
    (U : N.DeterministicPolicySequence)
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (i : Buffer) : Real :=
  N.calendarScaledQueueStateFrom U K (N.eventInitialState K) omega t i

/-- Cumulative allocation obtained from the same chronological token list. -/
noncomputable def calendarScaledAllocation
    (U : N.DeterministicPolicySequence)
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (i : Buffer) (j : Server) (k : Buffer) : Real :=
  (N.runAllocationCount (U K) (N.eventInitialState K)
      (N.calendarTokenPrefix K omega t) i j k : Real) /
    ((K : Nat) : Real)

/-- Concrete calendar-time stochastic execution driven by independent
unit-rate renewal clocks and the paper's `K * phi[j,k]` time changes. -/
noncomputable def calendarPoissonExecution :
    N.ScaledStochasticExecution
      (CalendarPoissonSample (Buffer := Buffer) (Server := Server)) where
  probability :=
    (show ProbabilityMeasure
      (CalendarPoissonSample (Buffer := Buffer) (Server := Server)) from
      ⟨N.calendarPoissonMeasure, inferInstance⟩)
  input := fun K omega t j k =>
    N.calendarScaledInput K omega t j k
  state := fun U K omega t i =>
    N.calendarScaledQueueState U K omega t i
  allocation := fun U K omega t i j k =>
    N.calendarScaledAllocation U K omega t i j k

private theorem calendar_uniformlyOnIcc_tendsto_at
    {Index : Type*} {T : Real}
    {f : Nat -> Real -> Index -> Real}
    {g : Real -> Index -> Real}
    (h : UniformlyOnIcc T f g)
    {t : Real} (ht : t ∈ Icc (0 : Real) T) (i : Index) :
    Tendsto (fun r => f r t i) atTop (nhds (g t i)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨r0, hr0⟩ := h epsilon hepsilon
  refine ⟨r0, fun r hr => ?_⟩
  simpa only [Real.dist_eq] using hr0 r hr t ht i

/-- The actual calendar-time marked Poisson execution satisfies the paper's
almost-sure nominal subsequential-input clause. -/
theorem calendarPoissonExecution_subsequentialInput :
    N.PoissonSubsequentialInputReadback N.calendarPoissonExecution := by
  intro T hT U K hK A X
  change
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      N.calendarPoissonExecution.PairConvergesOn
          T U K omega (A omega) (X omega) ->
        N.IsNominalFluidInput T (A omega)
  filter_upwards [N.all_renewalEpoch_ratio_tendsto_ae] with omega homega
  intro hconverges
  intro t ht j k
  have hcandidate :
      Tendsto
        (fun r =>
          N.calendarScaledInput (K r) omega t j k)
        atTop (nhds (A omega t j k)) := by
    exact calendar_uniformlyOnIcc_tendsto_at
      hconverges.1 ht (j, k)
  have hnominal :
      Tendsto
        (fun r =>
          N.calendarScaledInput (K r) omega t j k)
        atTop (nhds (N.phi j k * t)) :=
    N.calendarScaledInput_tendsto omega homega K hK t ht.1 j k
  exact tendsto_nhds_unique hcandidate hnominal

end Network

end StateDepMOR
