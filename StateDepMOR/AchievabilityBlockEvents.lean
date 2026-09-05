import StateDepMOR.AchievabilityBoundProof

/-!
# Return-failure block events for achievability

This module closes the gap between failure to be near `alpha` at a sampled
block endpoint and the all-time persistence event used in the paper. A fluid
path ending above `rho` either never visits the `delta` sublevel, in which
case the persistence estimate applies, or it visits that sublevel and later
pays for an upward Lyapunov change of at least `rho - delta`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : StateDepMOR.Network Buffer Server)

private theorem return_lAlphaAmbient_le_one_of_nonneg
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (x : Buffer -> Real) (hx : forall i, 0 <= x i) :
    Lyapunov.LAlphaAmbient (fun i => alpha i) x <= 1 := by
  have hmin :
      0 <= Lyapunov.minCoordinate (fun i => x i / alpha i) := by
    unfold Lyapunov.minCoordinate
    apply Finset.le_inf' Finset.univ_nonempty
    intro i _hi
    exact div_nonneg (hx i) (halpha i).le
  unfold Lyapunov.LAlphaAmbient
  linarith

private theorem continuous_returnLAlphaAmbient
    (alpha : Simplex Buffer) :
    Continuous
      (fun x : Buffer -> Real =>
        Lyapunov.LAlphaAmbient (fun i => alpha i) x) := by
  unfold Lyapunov.LAlphaAmbient Lyapunov.minCoordinate
  fun_prop

/-! ## Finite and fluid endpoint return-failure events -/

/-- At physical size `n + 1`, the calendar inputs under which some initial
queue state ends strictly above Lyapunov level `rho`. The initial state is
unrestricted. -/
def finiteCalendarReturnFailureEvent
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (rho H : Real) (n : Nat) :
    Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H) :=
  {path | exists
      (z : JobState Buffer (n.succPNat : Nat))
      (omega : StateDepMOR.Network.CalendarPoissonSample
        (Buffer := Buffer) (Server := Server)),
      StateDepMOR.PoissonSamplePath.IsRegularSample omega /\
      StateDepMOR.PoissonSamplePath.calendarPath
          N H n.succPNat omega = path /\
      rho <
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U n.succPNat z omega H i)}

/-- Fluid inputs admitting some execution whose endpoint is at or above
`rho`. This is the closed envelope of
`finiteCalendarReturnFailureEvent`. -/
def fluidReturnFailureInputSet
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (rho H : Real) :
    Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H) :=
  {path | exists (x0 : Simplex Buffer)
      (s : N.FluidModelSolution U H x0
        (StateDepMOR.PoissonSamplePath.asMatrix H path)),
      rho <= Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X H)}

/-- Every finite-action point in the varying-size return-failure outer limit
admits a fluid execution ending at or above `rho`. -/
theorem finiteCalendarReturnFailure_outerLimit_subset
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {rho H : Real} (hH : 0 < H)
    {path : StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H}
    (hpath :
      path ∈ varyingEventOuterLimit
        (finiteCalendarReturnFailureEvent N alpha U rho H))
    (hfinite :
      Ne
        (poissonPathRate N H
          (StateDepMOR.PoissonSamplePath.asMatrix H path))
        (Top.top : ENNReal)) :
    path ∈ fluidReturnFailureInputSet N alpha U rho H := by
  classical
  obtain
      ⟨Kindex, hKindex, approximatingPath, hmem, htendsto⟩ :=
    exists_strictMono_event_sequence_tendsto_of_mem_outerLimit
      (finiteCalendarReturnFailureEvent N alpha U rho H) hpath
  have hwitness (n : Nat) :
      exists
        (z : JobState Buffer ((Kindex n).succPNat : Nat))
        (omega : StateDepMOR.Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server)),
        StateDepMOR.PoissonSamplePath.IsRegularSample omega /\
        StateDepMOR.PoissonSamplePath.calendarPath
            N H (Kindex n).succPNat omega = approximatingPath n /\
        rho <
          Lyapunov.LAlphaAmbient (fun i => alpha i)
            (fun i =>
              N.totalCalendarScaledQueueStateFrom
                U (Kindex n).succPNat z omega H i) :=
    hmem n
  choose z omega hregular hcalendar hend using hwitness
  let K : Nat -> PNat := fun n => (Kindex n).succPNat
  have hK : StrictMono K := by
    intro m n hmn
    exact Nat.succPNat_strictMono (hKindex hmn)
  have hJ1 :
      Tendsto
        (fun n =>
          StateDepMOR.PoissonSamplePath.calendarPath
            N H (K n) (omega n))
        atTop (nhds path) := by
    apply htendsto.congr'
    exact Eventually.of_forall fun n => by
      simpa only [K] using (hcalendar n).symm
  obtain ⟨q, hq, x0, X, s, _hinitial, hqueue, hsX⟩ :=
    StateDepMOR.Network.exists_triangular_calendar_fluid_limit
      N U H hH K hK z omega path hregular hJ1 hfinite
  have hqueueH :
      Tendsto
        (fun r i =>
          N.totalCalendarScaledQueueStateFrom
            U (K (q r)) (z (q r)) (omega (q r)) H i)
        atTop (nhds (X H)) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hqueue epsilon hepsilon
    refine ⟨r0, fun r hr => ?_⟩
    simpa [Real.dist_eq] using
      hr0 r hr H ⟨hH.le, le_rfl⟩ i
  have hL :
      Tendsto
        (fun r =>
          Lyapunov.LAlphaAmbient (fun i => alpha i)
            (fun i =>
              N.totalCalendarScaledQueueStateFrom
                U (K (q r)) (z (q r)) (omega (q r)) H i))
        atTop
        (nhds
          (Lyapunov.LAlphaAmbient (fun i => alpha i) (X H))) :=
    (continuous_returnLAlphaAmbient alpha).continuousAt.tendsto.comp hqueueH
  have hendLimit :
      rho <= Lyapunov.LAlphaAmbient (fun i => alpha i) (X H) :=
    ge_of_tendsto' hL fun r => (hend (q r)).le
  refine ⟨x0, s, ?_⟩
  simpa only [hsX] using hendLimit

/-! ## Excursions that hit the boundary before a common endpoint -/

/-- At physical size `n + 1`, some initial state below `rho` reaches the
queue boundary at some time in `[0,H]`. This common-horizon event contains
boundary endpoints observed at every shorter block horizon. -/
def finiteCalendarExcursionHitEvent
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (rho H : Real) (n : Nat) :
    Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H) :=
  {path | exists
      (z : JobState Buffer (n.succPNat : Nat))
      (omega : StateDepMOR.Network.CalendarPoissonSample
        (Buffer := Buffer) (Server := Server)),
      StateDepMOR.PoissonSamplePath.IsRegularSample omega /\
      StateDepMOR.PoissonSamplePath.calendarPath
          N H n.succPNat omega = path /\
      Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U n.succPNat z omega 0 i) <= rho /\
      exists t, t ∈ Icc (0 : Real) H /\
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U n.succPNat z omega t i) = 1}

/-- The outer limit of the common-horizon hit events consists of genuine
fluid excursions from level at most `rho` to the boundary. -/
theorem finiteCalendarExcursionHit_outerLimit_subset
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    {rho H : Real} (hrho : rho < 1) (hH : 0 < H)
    {path : StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H}
    (hpath :
      path ∈ varyingEventOuterLimit
        (finiteCalendarExcursionHitEvent N alpha U rho H))
    (hfinite :
      Ne
        (poissonPathRate N H
          (StateDepMOR.PoissonSamplePath.asMatrix H path))
        (Top.top : ENNReal)) :
    path ∈ fluidExcursionInputSet N alpha U rho H := by
  classical
  obtain
      ⟨Kindex, hKindex, approximatingPath, hmem, htendsto⟩ :=
    exists_strictMono_event_sequence_tendsto_of_mem_outerLimit
      (finiteCalendarExcursionHitEvent N alpha U rho H) hpath
  have hwitness (n : Nat) :
      exists
        (z : JobState Buffer ((Kindex n).succPNat : Nat))
        (omega : StateDepMOR.Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server))
        (hitTime : Real),
        StateDepMOR.PoissonSamplePath.IsRegularSample omega /\
        StateDepMOR.PoissonSamplePath.calendarPath
            N H (Kindex n).succPNat omega = approximatingPath n /\
        Lyapunov.LAlphaAmbient (fun i => alpha i)
            (fun i =>
              N.totalCalendarScaledQueueStateFrom
                U (Kindex n).succPNat z omega 0 i) <= rho /\
        hitTime ∈ Icc (0 : Real) H /\
        Lyapunov.LAlphaAmbient (fun i => alpha i)
            (fun i =>
              N.totalCalendarScaledQueueStateFrom
                U (Kindex n).succPNat z omega hitTime i) = 1 := by
    obtain ⟨z, omega, hregular, hcalendar, hstart, t, ht, hhit⟩ :=
      hmem n
    exact ⟨z, omega, t, hregular, hcalendar, hstart, ht, hhit⟩
  choose z omega hitTime hregular hcalendar hstart hhitTime hhit
    using hwitness
  let K : Nat -> PNat := fun n => (Kindex n).succPNat
  have hK : StrictMono K := by
    intro m n hmn
    exact Nat.succPNat_strictMono (hKindex hmn)
  have hJ1 :
      Tendsto
        (fun n =>
          StateDepMOR.PoissonSamplePath.calendarPath
            N H (K n) (omega n))
        atTop (nhds path) := by
    apply htendsto.congr'
    exact Eventually.of_forall fun n => by
      simpa only [K] using (hcalendar n).symm
  obtain ⟨x0, s, tau, htau, hs, htauHit, hbefore⟩ :=
    StateDepMOR.Network.exists_triangular_calendar_fluid_excursion
      N U alpha halpha rho H hrho hH K hK z omega path hitTime
        hhitTime hregular hJ1 hfinite hstart hhit
  exact ⟨x0, s, tau, htau, hs, htauHit, hbefore⟩

/-- A common-horizon boundary-hit event has the fixed-target excursion
exponent `c * (1-rho)`. -/
theorem finiteCalendarExcursionHit_varying_upper
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    {rho T H c d : Real}
    (hT : 0 < T) (hTH : T <= H)
    (hrho : rho < 1) (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (hd : 0 <= d) (hdcost : d < c * (1 - rho)) :
    limsup
        (scaledLogVaryingMass
          (StateDepMOR.PoissonSamplePath.calendarPathLaw N H)
          (finiteCalendarExcursionHitEvent N alpha U rho H))
        atTop <=
      -(d : EReal) := by
  have hH : 0 < H := hT.trans_le hTH
  let I :
      StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H -> ENNReal :=
    fun path =>
      poissonPathRate N H
        (StateDepMOR.PoissonSamplePath.asMatrix H path)
  letI : MetricSpace
      (StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H) :=
    StateDepMOR.PoissonSamplePath.pathMetricSpace H hH
  letI : T0Space
      (StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H) :=
    { t0 := fun x y hxy =>
        StateDepMOR.PoissonSamplePath.j1EDist_eq_zero_imp_eq
          hH hxy.edist_eq_zero }
  have hcompact :
      IsCompact {path | I path <= ENNReal.ofReal d} := by
    simpa only [I] using
      StateDepMOR.PoissonSamplePath.isCompact_poissonPathRate_sublevel
        N hH d
  have houter :
      Disjoint
        (varyingEventOuterLimit
          (finiteCalendarExcursionHitEvent N alpha U rho H))
        {path | I path <= ENNReal.ofReal d} := by
    rw [Set.disjoint_left]
    intro path hpathOuter hpathLevel
    have hfinite : Ne (I path) (Top.top : ENNReal) :=
      ne_of_lt (hpathLevel.trans_lt ENNReal.ofReal_lt_top)
    have hfluid :
        path ∈ fluidExcursionInputSet N alpha U rho H :=
      finiteCalendarExcursionHit_outerLimit_subset
        N alpha halpha U hrho hH hpathOuter hfinite
    have hlower :
        ENNReal.ofReal (c * (1 - rho)) <= I path :=
      fluidExcursionInputSet_action_lower_fixed_target_horizon
        N alpha U hT hTH hrho hcpos hc hfluid
    have hstrict :
        ENNReal.ofReal d <
          ENNReal.ofReal (c * (1 - rho)) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd).2 hdcost
    exact (not_lt_of_ge hpathLevel) (hstrict.trans_le hlower)
  have hupper :=
    varyingEvent_closed_upper_at_ennreal_level
      (StateDepMOR.PoissonSamplePath.calendarPathLaw N H)
      (finiteCalendarExcursionHitEvent N alpha U rho H)
      I (ENNReal.ofReal d)
      (StateDepMOR.PoissonUpperFinal.calendarPathLaw_massLeOne N hH)
      hcompact
      (fun F hF =>
        StateDepMOR.PoissonSamplePath.calendarPathLaw_closed_upper_bound
          N hH F hF)
      houter
  simpa [EReal.coe_ennreal_ofReal, max_eq_left hd] using hupper

/-! ## Cost of a later upward excursion -/

/-- On a fluid path with observation horizon `H >= T`, an upward Lyapunov
change from at most `delta` to at least `rho` costs at least
`c * (rho - delta)` for every positive `c < gammaAB_T`.

Unlike the boundary-excursion lemma, this interval may start after time zero.
At a point with `L_alpha = 1`, differentiability and the simplex upper bound
force the derivative to be zero, so the local `gammaAB_T` inequality is only
needed where `L_alpha < 1`. -/
theorem poissonPathRate_ge_upward_change_cost_fixed_target_horizon
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    {T H : Real} {x0 : Simplex Buffer}
    {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (delta rho c start finish : Real)
    (hT : 0 < T) (hTH : T <= H)
    (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (hstart : start ∈ Icc (0 : Real) H)
    (hfinish : finish ∈ Icc (0 : Real) H)
    (htime : start <= finish)
    (hdeltarho : delta <= rho)
    (hlow :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X start) <= delta)
    (hhigh :
      rho <=
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X finish)) :
    ENNReal.ofReal (c * (rho - delta)) <= poissonPathRate N H A := by
  let g : Real -> Real :=
    fun t => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t)
  have hgacH : AbsolutelyContinuousOnInterval g 0 H :=
    Lyapunov.LAlphaAmbient_comp_absolutelyContinuous
      (fun i => alpha i) s.X s.state_ac
  have hsub : Icc start finish <= Icc (0 : Real) H :=
    Icc_subset_Icc hstart.1 hfinish.2
  have hgac :
      AbsolutelyContinuousOnInterval g start finish := by
    apply hgacH.mono
    simpa only [uIcc_of_le htime, uIcc_of_le s.horizon_pos.le] using hsub
  by_cases hrateTop : poissonPathRate N H A = (Top.top : ENNReal)
  · rw [hrateTop]
    exact le_top
  have hrateFinite :
      Ne (poissonPathRate N H A) (Top.top : ENNReal) := hrateTop
  let cost : Real -> Real :=
    fun t => (N.localRate (pathDerivative A t)).toReal
  have hcostIntH : IntegrableOn cost (Icc (0 : Real) H) volume :=
    finiteAction_localRate_toReal_integrableOn N H A hrateFinite
  have hcostInt : IntegrableOn cost (Icc start finish) volume :=
    hcostIntH.mono_set hsub
  have hregularH :
      Filter.Eventually
        (fun t => IsRegularPoint N alpha s t)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
    FluidModelSolution.isRegularPoint_ae alpha s
  have hregular :
      Filter.Eventually
        (fun t => IsRegularPoint N alpha s t)
        (MeasureTheory.ae (volume.restrict (Icc start finish))) :=
    ae_restrict_of_ae_restrict_of_subset hsub hregularH
  have hlocalFiniteH :
      Filter.Eventually
        (fun t =>
          N.localRate (pathDerivative A t) < (Top.top : ENNReal))
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
    finiteAction_localRate_lt_top_ae N H A hrateFinite
  have hlocalFinite :
      Filter.Eventually
        (fun t =>
          N.localRate (pathDerivative A t) < (Top.top : ENNReal))
        (MeasureTheory.ae (volume.restrict (Icc start finish))) :=
    ae_restrict_of_ae_restrict_of_subset hsub hlocalFiniteH
  have hpoint :
      Filter.Eventually
        (fun t => c * deriv g t <= cost t)
        (MeasureTheory.ae (volume.restrict (Icc start finish))) := by
    filter_upwards
      [ae_restrict_mem measurableSet_Icc, hregular,
        hlocalFinite] with t ht hreg hfiniteLocal
    by_cases hpositive : 0 < deriv g t
    · have hinterior : g t < 1 := by
        have hle :
            g t <= 1 := by
          exact return_lAlphaAmbient_le_one_of_nonneg
            alpha halpha (s.X t)
              (s.state_in_simplex t
                ⟨hreg.1.1.le, hreg.1.2.le⟩).1
        apply lt_of_le_of_ne hle
        intro heq
        have hlocal : IsLocalMax g t := by
          filter_upwards
            [Icc_mem_nhds hreg.1.1 hreg.1.2] with r hr
          change g r <= g t
          rw [heq]
          exact return_lAlphaAmbient_le_one_of_nonneg
            alpha halpha (s.X r) (s.state_in_simplex r hr).1
        have hzero :
            deriv g t = 0 :=
          hlocal.hasDerivAt_eq_zero hreg.2.2.2.2.hasDerivAt
        linarith
      exact
        mul_lyapunovDrift_le_localRate_toReal_atTime_fixedHorizon
          N alpha U s c t hT hTH hc hreg hinterior hpositive
            hfiniteLocal.ne
    · have hderiv : deriv g t <= 0 := le_of_not_gt hpositive
      exact (mul_nonpos_of_nonneg_of_nonpos hcpos.le hderiv).trans
        ENNReal.toReal_nonneg
  have hgDerivInt :
      IntegrableOn (fun t => deriv g t) (Icc start finish) volume := by
    have hint := hgac.intervalIntegrable_deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le htime] at hint
    exact hint
  have hint :
      integral (volume.restrict (Icc start finish))
          (fun t => c * deriv g t) <=
        integral (volume.restrict (Icc start finish)) cost :=
    integral_mono_ae (hgDerivInt.const_mul c) hcostInt hpoint
  have hderivIntegral :
      integral (volume.restrict (Icc start finish))
          (fun t => deriv g t) =
        g finish - g start := by
    rw [integral_Icc_eq_integral_Ioc,
      <- intervalIntegral.integral_of_le htime,
      hgac.integral_deriv_eq_sub]
  rw [integral_const_mul, hderivIntegral] at hint
  have hincrease : rho - delta <= g finish - g start := by
    dsimp only [g] at *
    linarith
  have htarget :
      c * (rho - delta) <=
        integral (volume.restrict (Icc start finish)) cost :=
    (mul_le_mul_of_nonneg_left hincrease hcpos.le).trans hint
  have hcostNonneg :
      Filter.Eventually
        (fun t => 0 <= cost t)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hcostMono :
      integral (volume.restrict (Icc start finish)) cost <=
        integral (volume.restrict (Icc (0 : Real) H)) cost :=
    setIntegral_mono_set hcostIntH hcostNonneg
      (Filter.Eventually.of_forall fun _ ht => hsub ht)
  have hvalid :
      IsAbsolutelyContinuousMatrixPath H A /\
        forall j k, A 0 j k = 0 :=
    poissonPathRate_ne_top_implies_valid N H A hrateFinite
  have hglobal :
      integral (volume.restrict (Icc (0 : Real) H)) cost =
        (poissonPathRate N H A).toReal := by
    have hlt :
        Filter.Eventually
          (fun t =>
            N.localRate (pathDerivative A t) < (Top.top : ENNReal))
          (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
      finiteAction_localRate_lt_top_ae N H A hrateFinite
    rw [integral_toReal
      (measurable_localRate_general N A).aemeasurable hlt]
    rw [poissonPathRate, if_pos hvalid]
  have hreal :
      c * (rho - delta) <= (poissonPathRate N H A).toReal :=
    htarget.trans (hcostMono.trans_eq hglobal)
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hrateFinite).mp
  rw [ENNReal.toReal_ofReal]
  · exact hreal
  · exact mul_nonneg hcpos.le (sub_nonneg.mpr hdeltarho)

/-! ## Return-failure action and probability bounds -/

/-- A return-failure path either stays above `delta` for the whole block or
contains a later upward change from `delta` to `rho`. Consequently its action
is bounded below by the minimum of the persistence cost and the upward-change
cost. -/
theorem exists_fluidReturnFailureInputSet_action_lower
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative : NegativeDriftCondition (N := N) alpha U)
    {T c delta rho : Real}
    (hT : 0 < T) (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (hdelta : 0 < delta) (hdeltarho : delta < rho) :
    exists a : Real, 0 < a /\ exists b : Real,
      forall (H : Real), T <= H ->
      forall path : StateDepMOR.PoissonSamplePath.Path
          (Buffer := Buffer) (Server := Server) H,
        path ∈ fluidReturnFailureInputSet N alpha U rho H ->
        ENNReal.ofReal
            (min (c * (rho - delta)) (a * H - b)) <=
          poissonPathRate N H
            (StateDepMOR.PoissonSamplePath.asMatrix H path) := by
  obtain ⟨a, ha, b, hpersistent⟩ :=
    persistentFluidInputClosed_action_linear_lower
      N alpha halpha U hnegative (rho := (1 : Real)) hdelta
  refine ⟨a, ha, b, ?_⟩
  intro H hTH path hpath
  have hH : 0 < H := hT.trans_le hTH
  obtain ⟨x0, s, hend⟩ := hpath
  let A : MatrixPath Server Buffer :=
    StateDepMOR.PoissonSamplePath.asMatrix H path
  let g : Real -> Real :=
    fun t => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t)
  by_cases hdip :
      exists t, t ∈ Icc (0 : Real) H /\ g t <= delta
  · obtain ⟨t, ht, htlow⟩ := hdip
    have hup :
        ENNReal.ofReal (c * (rho - delta)) <=
          poissonPathRate N H A := by
      exact poissonPathRate_ge_upward_change_cost_fixed_target_horizon
        N alpha halpha U s delta rho c t H hT hTH hcpos hc ht
          ⟨hH.le, le_rfl⟩ ht.2 hdeltarho.le htlow hend
    exact
      (ENNReal.ofReal_le_ofReal
        (min_le_left (c * (rho - delta)) (a * H - b))).trans hup
  · have hband :
        forall t, t ∈ Icc (0 : Real) H ->
          delta <= g t /\ g t <= 1 := by
      intro t ht
      constructor
      · exact le_of_not_gt fun hlt =>
          hdip ⟨t, ht, hlt.le⟩
      · exact return_lAlphaAmbient_le_one_of_nonneg
          alpha halpha (s.X t) (s.state_in_simplex t ht).1
    have hpersistentDatum :
        IsPersistentFluidInputClosed
          N alpha U delta 1 H A := by
      refine ⟨x0, s, ?_, ?_⟩
      · exact (hband 0 ⟨le_rfl, hH.le⟩).2
      · exact hband
    have hlower :
        ENNReal.ofReal (a * H - b) <= poissonPathRate N H A :=
      hpersistent H A hpersistentDatum
    exact
      (ENNReal.ofReal_le_ofReal
        (min_le_right (c * (rho - delta)) (a * H - b))).trans hlower

/-- The endpoint return-failure event has a varying-size J1 upper bound. Its
exponent is the smaller of a fixed upward-excursion cost and an affine
persistence cost. -/
theorem exists_finiteCalendarReturnFailure_varying_upper
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative : NegativeDriftCondition (N := N) alpha U)
    {T c delta rho : Real}
    (hT : 0 < T) (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (hdelta : 0 < delta) (hdeltarho : delta < rho) :
    exists a : Real, 0 < a /\ exists b : Real,
      forall (H : Real), T <= H ->
      forall d : Real, 0 <= d ->
        d < c * (rho - delta) ->
        d < a * H - b ->
        limsup
            (scaledLogVaryingMass
              (StateDepMOR.PoissonSamplePath.calendarPathLaw N H)
              (finiteCalendarReturnFailureEvent N alpha U rho H))
            atTop <=
          -(d : EReal) := by
  obtain ⟨a, ha, b, hlower⟩ :=
    exists_fluidReturnFailureInputSet_action_lower
      N alpha halpha U hnegative hT hcpos hc hdelta hdeltarho
  refine ⟨a, ha, b, ?_⟩
  intro H hTH d hd hdExcursion hdPersistence
  have hH : 0 < H := hT.trans_le hTH
  let I :
      StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H -> ENNReal :=
    fun path =>
      poissonPathRate N H
        (StateDepMOR.PoissonSamplePath.asMatrix H path)
  letI : MetricSpace
      (StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H) :=
    StateDepMOR.PoissonSamplePath.pathMetricSpace H hH
  letI : T0Space
      (StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H) :=
    { t0 := fun x y hxy =>
        StateDepMOR.PoissonSamplePath.j1EDist_eq_zero_imp_eq
          hH hxy.edist_eq_zero }
  have hcompact :
      IsCompact {path | I path <= ENNReal.ofReal d} := by
    simpa only [I] using
      StateDepMOR.PoissonSamplePath.isCompact_poissonPathRate_sublevel
        N hH d
  have houter :
      Disjoint
        (varyingEventOuterLimit
          (finiteCalendarReturnFailureEvent N alpha U rho H))
        {path | I path <= ENNReal.ofReal d} := by
    rw [Set.disjoint_left]
    intro path hpathOuter hpathLevel
    have hfinite : Ne (I path) (Top.top : ENNReal) :=
      ne_of_lt (hpathLevel.trans_lt ENNReal.ofReal_lt_top)
    have hfluid :
        path ∈ fluidReturnFailureInputSet N alpha U rho H :=
      finiteCalendarReturnFailure_outerLimit_subset
        N alpha U hH hpathOuter hfinite
    have hlowerPath :
        ENNReal.ofReal
            (min (c * (rho - delta)) (a * H - b)) <= I path :=
      hlower H hTH path hfluid
    have hdmin :
        d < min (c * (rho - delta)) (a * H - b) :=
      lt_min hdExcursion hdPersistence
    have hstrict :
        ENNReal.ofReal d <
          ENNReal.ofReal
            (min (c * (rho - delta)) (a * H - b)) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd).2 hdmin
    exact (not_lt_of_ge hpathLevel)
      (hstrict.trans_le hlowerPath)
  have hupper :=
    varyingEvent_closed_upper_at_ennreal_level
      (StateDepMOR.PoissonSamplePath.calendarPathLaw N H)
      (finiteCalendarReturnFailureEvent N alpha U rho H)
      I (ENNReal.ofReal d)
      (StateDepMOR.PoissonUpperFinal.calendarPathLaw_massLeOne N hH)
      hcompact
      (fun F hF =>
        StateDepMOR.PoissonSamplePath.calendarPathLaw_closed_upper_bound
          N hH F hF)
      houter
  simpa [EReal.coe_ennreal_ofReal, max_eq_left hd] using hupper

end StateDepMOR.PaperStatements.Network
