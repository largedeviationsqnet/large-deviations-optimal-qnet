import StateDepMOR.FluidExistenceProof
import StateDepMOR.FluidAttraction
import StateDepMOR.HallCriticalEquality
import StateDepMOR.InitialPerformance
import StateDepMOR.PoissonSamplePathLDP
import StateDepMOR.PaperStatements

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace StateDepMOR.Achievability

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

variable (N : StateDepMOR.Network Buffer Server)

/-! ## The concrete minimizing stationary execution -/

/-- The minimizing invariant PMF is stationary at every deterministic event
epoch. -/
theorem minimumInvariantPMF_nStep_stationary
    {K : Nat} (U : N.DeterministicStationaryPolicy K) (n : Nat) :
    N.nStepLaw U (N.minimumInvariantPMF U) n =
      N.minimumInvariantPMF U :=
  N.nStepLaw_eq_of_isInvariant U (N.minimumInvariantPMF U)
    (N.minimumInvariantPMF_isInvariant U) n

/-- Its Cesaro occupation PMF is exactly the same minimizing invariant PMF. -/
theorem minimumInvariantPMF_occupation_stationary
    {K : Nat} (U : N.DeterministicStationaryPolicy K) (n : Nat) :
    N.occupationPMF U (N.minimumInvariantPMF U) n =
      N.minimumInvariantPMF U :=
  N.occupationPMF_eq_of_isInvariant U (N.minimumInvariantPMF U)
    (N.minimumInvariantPMF_isInvariant U) n

/-- Exact cumulative-waste identity for the stationary minimum-PMF
execution. -/
theorem minimumInvariantPMF_expectedTrajectoryWaste
    {K : Nat} (U : N.DeterministicStationaryPolicy K) (n : Nat) :
    N.expectedTrajectoryWaste U (N.minimumInvariantPMF U) n =
      (n : Real) * N.minimumInvariantLoss U := by
  rw [N.expectedTrajectoryWaste_eq_mul_stationary_of_invariant
    U (N.minimumInvariantPMF U)
    (N.minimumInvariantPMF_isInvariant U) n]
  rw [N.minimumInvariantLoss_eq_stationaryOneStepWaste U]

/-- Event-epoch evolution stopped after an independent random number of
steps. -/
noncomputable def poissonizedStepLaw
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (countLaw : PMF Nat) :
    PMF (JobState Buffer K) :=
  countLaw.bind fun n => N.nStepLaw U pi n

/-- Every invariant PMF remains invariant after an arbitrary independent
random number of event-epoch transitions. -/
theorem poissonizedStepLaw_eq_of_isInvariant
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (countLaw : PMF Nat)
    (hinvariant : N.IsInvariantPMF U pi) :
    poissonizedStepLaw N U pi countLaw = pi := by
  unfold poissonizedStepLaw
  rw [show
    (fun n => N.nStepLaw U pi n) = (fun _n : Nat => pi) by
      funext n
      exact N.nStepLaw_eq_of_isInvariant U pi hinvariant n]
  simp

/-- In particular, the minimizing invariant PMF is unchanged by every
independent Poissonization law. -/
theorem minimumInvariantPMF_poissonized_stationary
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (countLaw : PMF Nat) :
    poissonizedStepLaw N U (N.minimumInvariantPMF U) countLaw =
      N.minimumInvariantPMF U :=
  poissonizedStepLaw_eq_of_isInvariant N U
    (N.minimumInvariantPMF U) countLaw
    (N.minimumInvariantPMF_isInvariant U)

/-- The minimizing invariant PMFs form an explicit initial-law family. -/
noncomputable def minimumInvariantInitialLaw
    (U : N.DeterministicPolicySequence) : N.InitialLawFamily where
  law := fun K => N.minimumInvariantPMF (U K)

@[simp]
theorem minimumInvariantInitialLaw_apply
    (U : N.DeterministicPolicySequence) (K : PNat) :
    (minimumInvariantInitialLaw N U).law K =
      N.minimumInvariantPMF (U K) :=
  rfl

theorem minimumInvariantInitialLaw_isInvariant
    (U : N.DeterministicPolicySequence) (K : PNat) :
    N.IsInvariantPMF (U K) ((minimumInvariantInitialLaw N U).law K) :=
  N.minimumInvariantPMF_isInvariant (U K)

theorem minimumInvariantInitialLaw_CesaroLimit
    (U : N.DeterministicPolicySequence) (K : PNat) :
    N.initialCesaroLimitLaw U (minimumInvariantInitialLaw N U) K =
      N.minimumInvariantPMF (U K) := by
  exact N.initialCesaroLimitLaw_eq_of_isInvariant
    U (minimumInvariantInitialLaw N U) K
      (minimumInvariantInitialLaw_isInvariant N U K)

theorem minimumInvariantInitialLaw_longRunLoss
    (U : N.DeterministicPolicySequence) (K : PNat) :
    N.initialLongRunLoss U (minimumInvariantInitialLaw N U) K =
      N.minimumInvariantLossFamily U K := by
  rw [N.initialLongRunLoss_eq_of_isInvariant
    U (minimumInvariantInitialLaw N U) K
      (minimumInvariantInitialLaw_isInvariant N U K)]
  exact (N.minimumInvariantLoss_eq_stationaryOneStepWaste (U K)).symm

/-! ## Non-idling boundary occupation -/

/-- The finite queue boundary: at least one queue is empty. -/
def IsQueueBoundary {K : Nat} (x : JobState Buffer K) : Prop :=
  exists i, x i = 0

noncomputable instance isQueueBoundaryDecidable {K : Nat}
    (x : JobState Buffer K) : Decidable (IsQueueBoundary x) :=
  Classical.dec _

/-- A non-idling policy can waste only at a boundary state. -/
theorem isQueueBoundary_of_waste
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (hnonidle : N.IsNonIdling U)
    (x : JobState Buffer K)
    (jk : StateDepMOR.Network.TokenType
      (Buffer := Buffer) (Server := Server))
    (hwaste : N.wasteIndicator U x jk = 1) :
    IsQueueBoundary x := by
  have hnone : U x jk.1 jk.2 = none := by
    by_contra h
    simp [StateDepMOR.Network.wasteIndicator, h] at hwaste
  obtain ⟨i, hi⟩ := N.server_has_neighbor jk.1
  exact ⟨i, (hnonidle x jk.1 jk.2).1 hnone i hi⟩

/-- Interior states have zero one-step waste under a non-idling policy. -/
theorem oneStepWaste_eq_zero_of_not_boundary
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (hnonidle : N.IsNonIdling U)
    (x : JobState Buffer K)
    (hx : Not (IsQueueBoundary x)) :
    N.oneStepWaste U x = 0 := by
  unfold StateDepMOR.Network.oneStepWaste
  apply Finset.sum_eq_zero
  intro jk _hjk
  have hne : Not (U x jk.1 jk.2 = none) := by
    intro hnone
    obtain ⟨i, hi⟩ := N.server_has_neighbor jk.1
    exact hx ⟨i, (hnonidle x jk.1 jk.2).1 hnone i hi⟩
  simp [StateDepMOR.Network.wasteIndicator, hne]

/-- Exact stationary decomposition: all stationary waste is carried by the
finite queue boundary. -/
theorem stationaryOneStepWaste_eq_boundary_sum
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (hnonidle : N.IsNonIdling U)
    (pi : PMF (JobState Buffer K)) :
    N.stationaryOneStepWaste U pi =
      Finset.sum (Finset.univ.filter IsQueueBoundary) fun x =>
        (pi x).toReal * N.oneStepWaste U x := by
  classical
  unfold StateDepMOR.Network.stationaryOneStepWaste
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _hxuniv hxnot
  have hx : Not (IsQueueBoundary x) := by
    simpa using hxnot
  rw [oneStepWaste_eq_zero_of_not_boundary N U hnonidle x hx]
  simp

/-- Boundary occupation mass of a finite queue law. -/
noncomputable def boundaryMass {K : Nat}
    (pi : PMF (JobState Buffer K)) : Real :=
  Finset.sum (Finset.univ.filter IsQueueBoundary) fun x =>
    (pi x).toReal

theorem stationaryOneStepWaste_le_boundaryMass
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (hnonidle : N.IsNonIdling U)
    (pi : PMF (JobState Buffer K)) :
    N.stationaryOneStepWaste U pi <= boundaryMass pi := by
  rw [stationaryOneStepWaste_eq_boundary_sum N U hnonidle pi]
  unfold boundaryMass
  apply Finset.sum_le_sum
  intro x _hx
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left
      (N.oneStepWaste_le_one U x) ENNReal.toReal_nonneg

theorem minimumInvariantLoss_eq_boundary_sum
    (U : N.DeterministicPolicySequence)
    (hnonidle : N.IsNonIdlingSequence U) (K : PNat) :
    N.minimumInvariantLossFamily U K =
      Finset.sum (Finset.univ.filter IsQueueBoundary) fun x =>
        (N.minimumInvariantPMF (U K) x).toReal *
          N.oneStepWaste (U K) x := by
  change N.minimumInvariantLoss (U K) = _
  rw [N.minimumInvariantLoss_eq_stationaryOneStepWaste]
  exact stationaryOneStepWaste_eq_boundary_sum N
    (U K) (hnonidle K) (N.minimumInvariantPMF (U K))

theorem minimumInvariantLoss_le_boundaryMass
    (U : N.DeterministicPolicySequence)
    (hnonidle : N.IsNonIdlingSequence U) (K : PNat) :
    N.minimumInvariantLossFamily U K <=
      boundaryMass (N.minimumInvariantPMF (U K)) := by
  change N.minimumInvariantLoss (U K) <= _
  rw [N.minimumInvariantLoss_eq_stationaryOneStepWaste]
  exact stationaryOneStepWaste_le_boundaryMass N
    (U K) (hnonidle K) (N.minimumInvariantPMF (U K))

/-! ## Arbitrary-initial calendar execution -/

/-- The totalized independent-clock calendar execution works from every
deterministic family of finite initial states and satisfies all three clauses
of the concrete fluid existence-and-consistency readback. -/
theorem arbitraryInitial_calendar_fluidModelExistenceAndConsistency
    [Nonempty Buffer] [Nonempty Server]
    (initial : forall K : PNat, JobState Buffer (K : Nat)) :
    N.FluidModelExistenceAndConsistencyReadback
      (N.calendarPoissonExecutionFrom initial) :=
  N.calendarPoissonExecutionFrom_fluidModelExistenceAndConsistency initial

/-- The repaired boundary-inclusive negative-drift condition supplies the
uniform deterministic return estimate used by the stopping-cycle argument. -/
theorem negativeDrift_uniform_nominal_attraction
    [Nonempty Buffer] [Nonempty Server]
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative :
      PaperStatements.Network.NegativeDriftCondition
        (N := N) alpha U) :
    exists eta, 0 < eta /\
      forall (T : Real) (x0 : Simplex Buffer)
        (A : MatrixPath Server Buffer)
        (s : N.FluidModelSolution U T x0 A),
        s.IsFluidLimit ->
        forall t, t ∈ Icc (0 : Real) T ->
          1 / eta <= t -> s.X t = fun i => alpha i :=
  StateDepMOR.PaperStatements.Network.FluidModelSolution.eq_alpha_of_nominal_negativeDrift
    alpha halpha hnegative

end Network

/-! ## Genuine positive-horizon Poisson J1 exports -/

namespace PoissonJ1

open StateDepMOR.PoissonSamplePath

variable [Nonempty Buffer]

theorem calendarPath_aemeasurable_export
    (N : StateDepMOR.Network Buffer Server)
    {T : Real} (hT : 0 < T) (K : PNat) :
    AEMeasurable (calendarPath N T K) N.calendarPoissonMeasure :=
  calendarPath_aemeasurable N hT K

theorem calendarPathLaw_probability_export
    (N : StateDepMOR.Network Buffer Server)
    {T : Real} (hT : 0 < T) (K : Nat) :
    IsProbabilityMeasure (calendarPathLaw N T K) :=
  calendarPathLaw_isProbabilityMeasure N hT K

theorem calendarPath_partitionIncrements_hasLaw_export
    (N : StateDepMOR.Network Buffer Server)
    {T : Real} (K : PNat) (n : Nat)
    (t : Fin (n + 1) -> Horizon T)
    (ht0 : 0 <= (t 0 : Real))
    (ht : Monotone (fun q => (t q : Real))) :
    HasLaw
      (fun omega : StateDepMOR.Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server) =>
        pathPartitionIncrements t (calendarPath N T K omega))
      (Measure.map
        (StateDepMOR.Network.scaleCalendarIncrementVector
          (Buffer := Buffer) (Server := Server) K (n := n))
        (StateDepMOR.Network.calendarIncrementProductLaw N K n
          (fun q => (t q : Real)) ht))
      N.calendarPoissonMeasure :=
  calendarPath_partitionIncrements_hasLaw N K n t ht0 ht

end PoissonJ1

end StateDepMOR.Achievability
