import StateDepMOR.AchievabilityBlockEvents
import StateDepMOR.AchievabilityCalendarLaw
import StateDepMOR.AchievabilityKernelSemigroup
import StateDepMOR.AchievabilityRateAlgebra

/-!
# Unconditional achievability assembly

This module joins the finite stationary-chain reduction to the uniform
sample-path large-deviation estimates.  Calendar endpoint events are compared
with the size-dependent J1 events directly, including for events that need
not be measurable.
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

private theorem totalCalendarTokenPrefix_zero
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    N.totalCalendarTokenPrefix K omega 0 = [] := by
  classical
  have hraw : N.totalRawCalendarEvents K omega 0 = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro event hevent
    simp [StateDepMOR.Network.totalRawCalendarEvents,
      StateDepMOR.Network.rawCalendarEvents] at hevent
  unfold StateDepMOR.Network.totalCalendarTokenPrefix
    StateDepMOR.Network.totalChronologicalCalendarEvents
  rw [hraw]
  rfl

private theorem totalCalendarScaledQueueStateFrom_zero
    (U : N.DeterministicPolicySequence)
    (K : PNat) (x : JobState Buffer (K : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    (fun i =>
      N.totalCalendarScaledQueueStateFrom U K x omega 0 i) =
      fun i => normalizedQueueState K x i := by
  funext i
  simp [StateDepMOR.Network.totalCalendarScaledQueueStateFrom,
    totalCalendarTokenPrefix_zero N, normalizedQueueState,
    StateDepMOR.Network.runTokens]

private theorem totalCalendarScaledQueueStateFrom_eq_normalizedEndpoint
    (U : N.DeterministicPolicySequence)
    (K : PNat) (x : JobState Buffer (K : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (t : Real)
    (hraw :
      forall (U : N.DeterministicPolicySequence) (K : PNat)
        (x : JobState Buffer (K : Nat)) (t : Real) (i : Buffer),
        N.totalCalendarScaledQueueStateFrom U K x omega t i =
          N.calendarScaledQueueStateFrom U K x omega t i) :
    (fun i =>
      N.totalCalendarScaledQueueStateFrom U K x omega t i) =
      fun i => normalizedQueueState K
        (calendarBlockEndpoint N K (U K) x omega t) i := by
  funext i
  rw [hraw U K x t i]
  rfl

/-- An arbitrary calendar-path event has mapped-law mass at least the mass
of its literal preimage. No measurability of the event is required. -/
theorem calendarPath_preimage_le_calendarPathLaw
    {H : Real} (hH : 0 < H) (K : PNat)
    (F : Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H)) :
    N.calendarPoissonMeasure
        {omega |
          Membership.mem F
            (StateDepMOR.PoissonSamplePath.calendarPath N H K omega)} <=
      StateDepMOR.PoissonSamplePath.calendarPathLaw N H (K : Nat) F := by
  change
    N.calendarPoissonMeasure
        ((StateDepMOR.PoissonSamplePath.calendarPath N H K) ⁻¹' F) <=
      StateDepMOR.PoissonSamplePath.calendarPathLaw N H (K : Nat) F
  unfold StateDepMOR.PoissonSamplePath.calendarPathLaw
  rw [positiveSize_pnat_val K]
  exact Measure.le_map_apply
    (StateDepMOR.PoissonSamplePath.calendarPath_aemeasurable N hH K) F

/-- An endpoint event at time `t` is bounded by any calendar-path event on
the possibly longer horizon `H` that contains it almost surely. Neither
event is required to be measurable. -/
theorem calendarBlockEndpointEvent_le_calendarPathLaw_ae
    {t H : Real} (hH : 0 < H)
    (K : PNat) (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat))
    (Target : JobState Buffer (K : Nat) -> Prop)
    (F : Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H))
    (hcontain :
      Filter.Eventually
        (fun omega =>
          Target (calendarBlockEndpoint N K U x omega t) ->
            Membership.mem F
              (StateDepMOR.PoissonSamplePath.calendarPath N H K omega))
        (MeasureTheory.ae N.calendarPoissonMeasure)) :
    N.calendarPoissonMeasure
        {omega | Target (calendarBlockEndpoint N K U x omega t)} <=
      StateDepMOR.PoissonSamplePath.calendarPathLaw N H (K : Nat) F := by
  calc
    N.calendarPoissonMeasure
        {omega | Target (calendarBlockEndpoint N K U x omega t)} <=
        N.calendarPoissonMeasure
          {omega |
            Membership.mem F
              (StateDepMOR.PoissonSamplePath.calendarPath N H K omega)} := by
      apply measure_mono_ae
      filter_upwards [hcontain] with omega homega htarget
      exact homega htarget
    _ <= StateDepMOR.PoissonSamplePath.calendarPathLaw
        N H (K : Nat) F :=
      calendarPath_preimage_le_calendarPathLaw N hH K F

/-- Failure to end in the finite near-alpha set is contained almost surely
in the size-dependent return-failure input event. -/
theorem calendarBlockEndpoint_notNear_measure_le_returnFailure
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (rho : Real) {H : Real} (hH : 0 < H)
    (n : Nat)
    (x : JobState Buffer (n.succPNat : Nat)) :
    N.calendarPoissonMeasure
        {omega |
          Not (Lyapunov.LAlpha alpha
            (normalizedQueueState n.succPNat
              (calendarBlockEndpoint
                N n.succPNat (U n.succPNat) x omega H)) <= rho)} <=
      StateDepMOR.PoissonSamplePath.calendarPathLaw N H (n + 1)
        (finiteCalendarReturnFailureEvent N alpha U rho H n) := by
  apply calendarBlockEndpointEvent_le_calendarPathLaw_ae
    N hH n.succPNat (U n.succPNat) x
      (fun y => Not
        (Lyapunov.LAlpha alpha
          (normalizedQueueState n.succPNat y) <= rho))
      (finiteCalendarReturnFailureEvent N alpha U rho H n)
  filter_upwards
    [StateDepMOR.PoissonSamplePath.regularSample_ae N,
      @totalCalendarScaledQueueStateFrom_eq_raw_ae
        Buffer Server _ _ _ _ _ _
        (LinearOrder.lift'
          (Fintype.equivFin Buffer)
          (Fintype.equivFin Buffer).injective) N] with
      omega hregular hraw hnotNear
  refine ⟨x, omega, hregular, rfl, ?_⟩
  rw [totalCalendarScaledQueueStateFrom_eq_normalizedEndpoint
    N U n.succPNat x omega H hraw]
  change rho <
    Lyapunov.LAlpha alpha
      (normalizedQueueState n.succPNat
        (calendarBlockEndpoint
          N n.succPNat (U n.succPNat) x omega H))
  exact lt_of_not_ge hnotNear

/-- Real-valued form of the one-block return-failure containment. -/
theorem calendarBlockEndpoint_notNear_real_le_returnFailure
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (rho : Real) {H : Real} (hH : 0 < H)
    (n : Nat)
    (x : JobState Buffer (n.succPNat : Nat)) :
    N.calendarPoissonMeasure.real
        {omega |
          Not (Lyapunov.LAlpha alpha
            (normalizedQueueState n.succPNat
              (calendarBlockEndpoint
                N n.succPNat (U n.succPNat) x omega H)) <= rho)} <=
      (StateDepMOR.PoissonSamplePath.calendarPathLaw N H (n + 1)).real
        (finiteCalendarReturnFailureEvent N alpha U rho H n) := by
  letI : IsProbabilityMeasure
      (StateDepMOR.PoissonSamplePath.calendarPathLaw N H (n + 1)) :=
    StateDepMOR.PoissonSamplePath.calendarPathLaw_isProbabilityMeasure
      N hH (n + 1)
  exact ENNReal.toReal_mono
    (measure_ne_top
      (StateDepMOR.PoissonSamplePath.calendarPathLaw N H (n + 1))
      (finiteCalendarReturnFailureEvent N alpha U rho H n))
    (calendarBlockEndpoint_notNear_measure_le_returnFailure
      N alpha U rho hH n x)

/-- A boundary endpoint reached from the finite near-alpha set at any time
inside a common horizon is contained almost surely in the corresponding
common-horizon excursion event. -/
theorem calendarBlockEndpoint_boundary_measure_le_excursionHit
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (rho : Real) {t Hstar : Real} (hHstar : 0 < Hstar)
    (ht : Membership.mem (Set.Icc (0 : Real) Hstar) t)
    (n : Nat)
    (x : JobState Buffer (n.succPNat : Nat))
    (hnear :
      Lyapunov.LAlpha alpha
        (normalizedQueueState n.succPNat x) <= rho) :
    N.calendarPoissonMeasure
        {omega |
          StateDepMOR.Achievability.Network.IsQueueBoundary
            (calendarBlockEndpoint
              N n.succPNat (U n.succPNat) x omega t)} <=
      StateDepMOR.PoissonSamplePath.calendarPathLaw N Hstar (n + 1)
        (finiteCalendarExcursionHitEvent
          N alpha U rho Hstar n) := by
  apply calendarBlockEndpointEvent_le_calendarPathLaw_ae
    N hHstar n.succPNat (U n.succPNat) x
      StateDepMOR.Achievability.Network.IsQueueBoundary
      (finiteCalendarExcursionHitEvent N alpha U rho Hstar n)
  filter_upwards
    [StateDepMOR.PoissonSamplePath.regularSample_ae N,
      @totalCalendarScaledQueueStateFrom_eq_raw_ae
        Buffer Server _ _ _ _ _ _
        (LinearOrder.lift'
          (Fintype.equivFin Buffer)
          (Fintype.equivFin Buffer).injective) N] with
      omega hregular hraw hboundary
  refine ⟨x, omega, hregular, rfl, ?_, t, ht, ?_⟩
  · rw [totalCalendarScaledQueueStateFrom_zero
      N U n.succPNat x omega]
    exact hnear
  · rw [totalCalendarScaledQueueStateFrom_eq_normalizedEndpoint
      N U n.succPNat x omega t hraw]
    exact lAlpha_normalizedQueueState_eq_one_of_boundary
      alpha halpha n.succPNat
        (calendarBlockEndpoint
          N n.succPNat (U n.succPNat) x omega t)
        hboundary

/-- Real-valued form of the common-horizon boundary-hit containment. -/
theorem calendarBlockEndpoint_boundary_real_le_excursionHit
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (rho : Real) {t Hstar : Real} (hHstar : 0 < Hstar)
    (ht : Membership.mem (Set.Icc (0 : Real) Hstar) t)
    (n : Nat)
    (x : JobState Buffer (n.succPNat : Nat))
    (hnear :
      Lyapunov.LAlpha alpha
        (normalizedQueueState n.succPNat x) <= rho) :
    N.calendarPoissonMeasure.real
        {omega |
          StateDepMOR.Achievability.Network.IsQueueBoundary
            (calendarBlockEndpoint
              N n.succPNat (U n.succPNat) x omega t)} <=
      (StateDepMOR.PoissonSamplePath.calendarPathLaw
        N Hstar (n + 1)).real
        (finiteCalendarExcursionHitEvent
          N alpha U rho Hstar n) := by
  letI : IsProbabilityMeasure
      (StateDepMOR.PoissonSamplePath.calendarPathLaw
        N Hstar (n + 1)) :=
    StateDepMOR.PoissonSamplePath.calendarPathLaw_isProbabilityMeasure
      N hHstar (n + 1)
  exact ENNReal.toReal_mono
    (measure_ne_top
      (StateDepMOR.PoissonSamplePath.calendarPathLaw
        N Hstar (n + 1))
      (finiteCalendarExcursionHitEvent
        N alpha U rho Hstar n))
    (calendarBlockEndpoint_boundary_measure_le_excursionHit
      N alpha halpha U rho hHstar ht n x hnear)

/-! ## Real event-mass families and their logarithmic rates -/

/-- Real mass of a size-dependent calendar-path event, indexed by positive
system sizes. The predecessor adapter makes physical size `n + 1`
correspond exactly to event index `n`. -/
noncomputable def calendarVaryingEventMass
    (H : Real)
    (event : Nat -> Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H))
    (K : PNat) : Real :=
  (StateDepMOR.PoissonSamplePath.calendarPathLaw N H (K : Nat)
    (event K.natPred)).toReal

theorem calendarVaryingEventMass_nonnegative
    (H : Real)
    (event : Nat -> Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H))
    (K : PNat) :
    0 <= calendarVaryingEventMass N H event K :=
  ENNReal.toReal_nonneg

theorem calendarVaryingEventMass_le_one
    {H : Real} (hH : 0 < H)
    (event : Nat -> Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H))
    (K : PNat) :
    calendarVaryingEventMass N H event K <= 1 := by
  letI : IsProbabilityMeasure
      (StateDepMOR.PoissonSamplePath.calendarPathLaw N H (K : Nat)) :=
    StateDepMOR.PoissonSamplePath.calendarPathLaw_isProbabilityMeasure
      N hH (K : Nat)
  exact measureReal_le_one

/-- Taking real values of a probability event family loses no mass when it
is embedded back into `ENNReal`, so its scaled-log limsup is bounded by the
varying-event limsup used by the LDP. -/
theorem limsup_scaledLog_calendarVaryingEventMass_le
    {H : Real} (hH : 0 < H)
    (event : Nat -> Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H)) :
    limsup
        (scaledLogLossPNat
          (calendarVaryingEventMass N H event)) atTop <=
      limsup
        (scaledLogVaryingMass
          (StateDepMOR.PoissonSamplePath.calendarPathLaw N H)
          event) atTop := by
  apply limsup_scaledLogLossPNat_le_limsup_scaledLogVaryingMass
  intro n
  have hne :
      Ne
        (StateDepMOR.PoissonSamplePath.calendarPathLaw N H (n + 1)
          (event n))
        (Top.top : ENNReal) := by
    haveI : IsProbabilityMeasure
        (StateDepMOR.PoissonSamplePath.calendarPathLaw N H (n + 1)) :=
      StateDepMOR.PoissonSamplePath.calendarPathLaw_isProbabilityMeasure
        N hH (n + 1)
    exact measure_ne_top
      (StateDepMOR.PoissonSamplePath.calendarPathLaw N H (n + 1))
      (event n)
  unfold calendarVaryingEventMass
  simp only [Nat.natPred_succPNat, Nat.succPNat_coe]
  rw [ENNReal.ofReal_toReal hne]

/-- Real-mass version of the common-horizon excursion upper bound. -/
theorem calendarExcursionHitMass_limsup_le
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    {rho T H c d : Real}
    (hT : 0 < T) (hTH : T <= H)
    (hrho : rho < 1) (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (hd : 0 <= d) (hdcost : d < c * (1 - rho)) :
    limsup
        (scaledLogLossPNat
          (calendarVaryingEventMass N H
            (finiteCalendarExcursionHitEvent
              N alpha U rho H))) atTop <=
      -(d : EReal) := by
  have hH : 0 < H := hT.trans_le hTH
  exact
    (limsup_scaledLog_calendarVaryingEventMass_le N hH
      (finiteCalendarExcursionHitEvent N alpha U rho H)).trans
      (finiteCalendarExcursionHit_varying_upper
        N alpha halpha U hT hTH hrho hcpos hc hd hdcost)

/-- Real-mass version of the endpoint return-failure upper bound. -/
theorem calendarReturnFailureMass_limsup_le
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative : NegativeDriftCondition (N := N) alpha U)
    {T c delta rho a b H e : Real}
    (hT : 0 < T) (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (hdelta : 0 < delta) (hdeltarho : delta < rho)
    (haction :
      forall (H : Real), T <= H ->
      forall d : Real, 0 <= d ->
        d < c * (rho - delta) ->
        d < a * H - b ->
        limsup
            (scaledLogVaryingMass
              (StateDepMOR.PoissonSamplePath.calendarPathLaw N H)
              (finiteCalendarReturnFailureEvent N alpha U rho H))
            atTop <=
          -(d : EReal))
    (hTH : T <= H) (he : 0 <= e)
    (heExcursion : e < c * (rho - delta))
    (hePersistence : e < a * H - b) :
    limsup
        (scaledLogLossPNat
          (calendarVaryingEventMass N H
            (finiteCalendarReturnFailureEvent
              N alpha U rho H))) atTop <=
      -(e : EReal) := by
  have hH : 0 < H := hT.trans_le hTH
  exact
    (limsup_scaledLog_calendarVaryingEventMass_le N hH
      (finiteCalendarReturnFailureEvent N alpha U rho H)).trans
      (haction H hTH e he heExcursion hePersistence)

end StateDepMOR.PaperStatements.Network
