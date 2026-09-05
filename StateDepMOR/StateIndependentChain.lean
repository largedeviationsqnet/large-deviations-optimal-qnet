import StateDepMOR.StateIndependentPrimitives
import StateDepMOR.FiniteQueueStationarity
import StateDepMOR.FiniteQueueBalance
import StateDepMOR.Asymptotics

/-!
# Concrete state-independent finite queue chain

This module gives a stochastic execution to
`PaperStatements.FixedGraphStateIndependentPolicy`.  At each event epoch it
first draws a marked service token from the rate network's `tokenLaw`, then
draws an action from the policy PMF indexed by the token type.  The action PMF
does not receive the queue state or any history.  Its push-forward through the
queue update is therefore a stationary Markov kernel at each fixed `K`.

The waste indicator follows Definition 2 exactly: `none` wastes the token, as
does selecting an empty buffer; selecting a nonempty buffer moves one job to
the token destination.  The compatibility support condition remains part of
the repaired policy type.

The performance definitions implement the repaired minimum-recurrent-class
convention by minimizing stationary waste over all invariant PMFs of the
finite chain.  The minimum is attained.  Proposition 3 is stated directly in
terms of this loss below, with no abstract execution or externally supplied
loss data.
-/

open scoped ENNReal
open Filter Set

noncomputable section

namespace StateDepMOR
namespace StateIndependentChain

open PaperStatements

universe u v w

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-! ## One event epoch -/

/-- A token together with the independently sampled policy action conditional
on that token type.  This law has no queue-state argument. -/
noncomputable def epochLaw
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    PMF (Prod (Prod Server Buffer) (Option Buffer)) :=
  PMF.ofFintype
    (fun event =>
      N.tokenLaw event.1 *
        (U.distribution K event.1.1 event.1.2) event.2)
    (by
      rw [Fintype.sum_prod_type]
      calc
        Finset.univ.sum (fun jk =>
            Finset.univ.sum (fun action =>
              N.tokenLaw jk *
                (U.distribution K jk.1 jk.2) action)) =
            Finset.univ.sum (fun jk =>
              N.tokenLaw jk *
                Finset.univ.sum (fun action =>
                  (U.distribution K jk.1 jk.2) action)) := by
          apply Finset.sum_congr rfl
          intro jk _
          exact
            (Finset.mul_sum Finset.univ
              (fun action =>
                (U.distribution K jk.1 jk.2) action)
              (N.tokenLaw jk)).symm
        _ = Finset.univ.sum (fun jk => N.tokenLaw jk * 1) := by
          apply Finset.sum_congr rfl
          intro jk _
          congr 1
          simpa only [tsum_fintype] using
            (U.distribution K jk.1 jk.2).tsum_coe
        _ = 1 := by
          simp only [mul_one]
          simpa only [tsum_fintype] using N.tokenLaw.tsum_coe)

/-- The joint atom is the token mass times its conditional action mass. -/
@[simp]
theorem epochLaw_apply
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (jk : Prod Server Buffer)
    (action : Option Buffer) :
    epochLaw G N U K (jk, action) =
      N.tokenLaw jk * (U.distribution K jk.1 jk.2) action := by
  rfl

/-- Real-valued form of the joint atom formula. -/
@[simp]
theorem epochLaw_toReal
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (jk : Prod Server Buffer)
    (action : Option Buffer) :
    (epochLaw G N U K (jk, action)).toReal =
      (N.tokenLaw jk).toReal *
        ((U.distribution K jk.1 jk.2) action).toReal := by
  rw [epochLaw_apply, ENNReal.toReal_mul]

/-- Applying an action to one marked token.  The action `none`, or a selected
empty source buffer, leaves the state unchanged. -/
def queueStep {K : Nat}
    (x : JobState Buffer K)
    (jk : Prod Server Buffer)
    (action : Option Buffer) :
    JobState Buffer K :=
  match action with
  | none => x
  | some i =>
      if h : 0 < x i then
        x.moveJob i jk.2 h
      else
        x

/-- Exact per-event waste indicator from Definition 2. -/
def wasteIndicator {K : Nat}
    (x : JobState Buffer K)
    (action : Option Buffer) : Real :=
  match action with
  | none => 1
  | some i => if x i = 0 then 1 else 0

/-- The concrete one-step transition kernel on queue states. -/
noncomputable def transitionPMF
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (x : JobState Buffer (K : Nat)) :
    PMF (JobState Buffer (K : Nat)) :=
  (epochLaw G N U K).map fun event =>
    queueStep x event.1 event.2

/-- Every conditional action PMF is normalized. -/
theorem actionDistribution_normalized
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k : Buffer) :
    Finset.univ.sum
      (fun action => ((U.distribution K j k) action).toReal) = 1 :=
  PMF.sum_toReal (U.distribution K j k)

/-- Under the same compatibility graph, every action with nonzero mass is
compatible with the token's origin server. -/
theorem compatible_of_action_ne_zero
    (G N : Network Buffer Server)
    (hgraph : SameCompatibility G N)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k i : Buffer)
    (hmass : Ne ((U.distribution K j k) (some i)) 0) :
    N.compatible i j := by
  apply (hgraph i j).mp
  exact U.compatible_support K j k (some i)
    ((PMF.mem_support_iff (U.distribution K j k) (some i)).2 hmass)

/-- A positive-queue action with nonzero policy mass is a legal queue action
whenever the rate network has the policy's fixed compatibility graph. -/
theorem action_isLegal_of_ne_zero {Kjobs : Nat}
    (G N : Network Buffer Server)
    (hgraph : SameCompatibility G N)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (x : JobState Buffer Kjobs)
    (j : Server) (k i : Buffer)
    (hmass : Ne ((U.distribution K j k) (some i)) 0)
    (hx : 0 < x i) :
    N.IsLegalAction x j (some i) :=
  And.intro
    (compatible_of_action_ne_zero G N hgraph U K j k i hmass)
    hx

/-- The token/action event law is normalized. -/
theorem epochLaw_normalized
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    Finset.univ.sum
      (fun event => ((epochLaw G N U K) event).toReal) = 1 :=
  PMF.sum_toReal (epochLaw G N U K)

/-- The one-step queue transition probabilities sum to one. -/
theorem transitionPMF_normalized
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (x : JobState Buffer (K : Nat)) :
    Finset.univ.sum
      (fun y => ((transitionPMF G N U K x) y).toReal) = 1 :=
  PMF.sum_toReal (transitionPMF G N U K x)

@[simp]
theorem queueStep_total_jobs {K : Nat}
    (x : JobState Buffer K)
    (jk : Prod Server Buffer)
    (action : Option Buffer) :
    Finset.univ.sum (fun i => queueStep x jk action i) = K :=
  (queueStep x jk action).total_jobs

theorem wasteIndicator_eq_one_iff {K : Nat}
    (x : JobState Buffer K) (action : Option Buffer) :
    wasteIndicator x action = 1 <->
      action = none \/
        exists i, action = some i /\ x i = 0 := by
  cases action with
  | none =>
      simp [wasteIndicator]
  | some i =>
      by_cases h : x i = 0 <;> simp [wasteIndicator, h]

theorem wasteIndicator_nonneg {K : Nat}
    (x : JobState Buffer K) (action : Option Buffer) :
    0 <= wasteIndicator x action := by
  cases action with
  | none =>
      simp [wasteIndicator]
  | some i =>
      by_cases h : x i = 0 <;> simp [wasteIndicator, h]

theorem wasteIndicator_le_one {K : Nat}
    (x : JobState Buffer K) (action : Option Buffer) :
    wasteIndicator x action <= 1 := by
  cases action with
  | none =>
      simp [wasteIndicator]
  | some i =>
      by_cases h : x i = 0 <;> simp [wasteIndicator, h]

/-- Conditional expected waste at one event epoch from state `x`. -/
noncomputable def oneStepWaste
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (x : JobState Buffer (K : Nat)) : Real :=
  Finset.univ.sum fun jk =>
    (N.tokenLaw jk).toReal *
      Finset.univ.sum fun action =>
        ((U.distribution K jk.1 jk.2) action).toReal *
          wasteIndicator x action

/-- The displayed double sum is exactly expectation of the waste indicator
under the token/action law used by the transition kernel. -/
theorem oneStepWaste_eq_epochExpectation
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (x : JobState Buffer (K : Nat)) :
    oneStepWaste G N U K x =
      Finset.univ.sum (fun event =>
        ((epochLaw G N U K) event).toReal *
          wasteIndicator x event.2) := by
  rw [Fintype.sum_prod_type]
  unfold oneStepWaste
  apply Finset.sum_congr rfl
  intro jk _
  rw [Finset.mul_sum]
  simp only [epochLaw_toReal, mul_assoc]

theorem oneStepWaste_nonneg
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (x : JobState Buffer (K : Nat)) :
    0 <= oneStepWaste G N U K x := by
  apply Finset.sum_nonneg
  intro jk _
  apply mul_nonneg ENNReal.toReal_nonneg
  apply Finset.sum_nonneg
  intro action _
  exact mul_nonneg ENNReal.toReal_nonneg
    (wasteIndicator_nonneg x action)

theorem oneStepWaste_le_one
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (x : JobState Buffer (K : Nat)) :
    oneStepWaste G N U K x <= 1 := by
  calc
    oneStepWaste G N U K x <=
        Finset.univ.sum (fun jk => (N.tokenLaw jk).toReal * 1) := by
      apply Finset.sum_le_sum
      intro jk _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      calc
        Finset.univ.sum (fun action =>
            ((U.distribution K jk.1 jk.2) action).toReal *
              wasteIndicator x action) <=
            Finset.univ.sum (fun action =>
              ((U.distribution K jk.1 jk.2) action).toReal * 1) := by
          apply Finset.sum_le_sum
          intro action _
          exact mul_le_mul_of_nonneg_left
            (wasteIndicator_le_one x action) ENNReal.toReal_nonneg
        _ = 1 := by
          simpa only [mul_one] using
            actionDistribution_normalized G U K jk.1 jk.2
    _ = 1 := by
      simpa only [mul_one] using PMF.sum_toReal N.tokenLaw

/-! ## Invariant laws and stationary waste -/

/-- Invariance for the concrete state-independent queue kernel. -/
def IsInvariantPMF
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat))) : Prop :=
  pi.bind (transitionPMF G N U K) = pi

/-- Stationary expected waste per service-token epoch. -/
noncomputable def stationaryOneStepWaste
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat))) : Real :=
  Finset.univ.sum fun x =>
    (pi x).toReal * oneStepWaste G N U K x

/-- Every fixed-`K` concrete state-independent chain has an invariant PMF. -/
theorem exists_invariantPMF
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    exists pi : PMF (JobState Buffer (K : Nat)),
      IsInvariantPMF G N U K pi := by
  exact @FiniteMarkovChain.exists_invariant_pmf
    (JobState Buffer (K : Nat))
    (JobState.instFintype (K : Nat))
    (JobState.instNonempty (K : Nat))
    (transitionPMF G N U K)

/-- A canonical invariant law for the concrete chain. -/
noncomputable def invariantPMF
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    PMF (JobState Buffer (K : Nat)) :=
  Classical.choose (exists_invariantPMF G N U K)

theorem invariantPMF_isInvariant
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    IsInvariantPMF G N U K (invariantPMF G N U K) :=
  Classical.choose_spec (exists_invariantPMF G N U K)

theorem stationaryOneStepWaste_nonneg
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat))) :
    0 <= stationaryOneStepWaste G N U K pi := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg ENNReal.toReal_nonneg
    (oneStepWaste_nonneg G N U K x)

theorem stationaryOneStepWaste_le_one
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat))) :
    stationaryOneStepWaste G N U K pi <= 1 := by
  calc
    stationaryOneStepWaste G N U K pi <=
        Finset.univ.sum (fun x => (pi x).toReal * 1) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (oneStepWaste_le_one G N U K x) ENNReal.toReal_nonneg
    _ = 1 := by
      simpa only [mul_one] using PMF.sum_toReal pi

/-! ## Stationary coordinate balance -/

/-- Indicator that a token has destination `i`. -/
def destinationIndicator (i k : Buffer) : Real :=
  if k = i then 1 else 0

/-- Indicator that an action selects source buffer `i`. -/
def selectedSourceIndicator (i : Buffer) : Option Buffer -> Real
  | none => 0
  | some src => if src = i then 1 else 0

/-- Nominal coordinate-flow bookkeeping before queue availability is
enforced.  An explicit `none` action contributes no selected-source term. -/
def nominalCoordinateIncrement
    (i : Buffer)
    (event : Prod (Prod Server Buffer) (Option Buffer)) : Real :=
  destinationIndicator i event.1.2 -
    selectedSourceIndicator i event.2

/-- The coordinate change actually executed by the finite queue chain. -/
def actualCoordinateIncrement {K : Nat}
    (x : JobState Buffer K)
    (i : Buffer)
    (event : Prod (Prod Server Buffer) (Option Buffer)) : Real :=
  match event.2 with
  | none => 0
  | some src =>
      if 0 < x src then nominalCoordinateIncrement i event else 0

/-- On every coordinate, the absolute discrepancy between nominal and
executed movement is bounded by the exact waste indicator. -/
theorem abs_nominal_sub_actual_le_waste {K : Nat}
    (x : JobState Buffer K)
    (i : Buffer)
    (event : Prod (Prod Server Buffer) (Option Buffer)) :
    |nominalCoordinateIncrement i event -
        actualCoordinateIncrement x i event| <=
      wasteIndicator x event.2 := by
  rcases event with ⟨jk, action⟩
  cases action with
  | none =>
      by_cases hdest : jk.2 = i <;>
        simp [nominalCoordinateIncrement, actualCoordinateIncrement,
          destinationIndicator, selectedSourceIndicator, wasteIndicator,
          hdest]
  | some src =>
      by_cases hsource : 0 < x src
      · have hactual :
            actualCoordinateIncrement x i (jk, some src) =
              nominalCoordinateIncrement i (jk, some src) := by
          simp [actualCoordinateIncrement, hsource]
        rw [hactual, sub_self, abs_zero]
        exact wasteIndicator_nonneg x (some src)
      · have hempty : x src = 0 := Nat.eq_zero_of_not_pos hsource
        have hactual :
            actualCoordinateIncrement x i (jk, some src) = 0 := by
          simp [actualCoordinateIncrement, hsource]
        have hwaste : wasteIndicator x (some src) = 1 := by
          simp [wasteIndicator, hempty]
        rw [hactual, sub_zero, hwaste]
        by_cases hdest : jk.2 = i <;>
          by_cases hsrc : src = i <;>
            simp [nominalCoordinateIncrement, actualCoordinateIncrement,
              destinationIndicator, selectedSourceIndicator, hdest, hsrc]

/-- The executable increment agrees with the queue-state coordinate change. -/
theorem actualCoordinateIncrement_eq_jobsIn {K : Nat}
    (x : JobState Buffer K)
    (i : Buffer)
    (event : Prod (Prod Server Buffer) (Option Buffer)) :
    actualCoordinateIncrement x i event =
      JobState.jobsIn (queueStep x event.1 event.2) {i} -
        JobState.jobsIn x {i} := by
  rcases event with ⟨jk, action⟩
  cases action with
  | none =>
      simp [actualCoordinateIncrement, queueStep]
  | some src =>
      by_cases hsource : 0 < x src
      · have hmove :=
          JobState.jobsIn_moveJob x src jk.2 hsource ({i} : Finset Buffer)
        rw [show queueStep x jk (some src) =
            x.moveJob src jk.2 hsource by
          simp [queueStep, hsource]]
        change
          (if 0 < x src then
              nominalCoordinateIncrement i (jk, some src)
            else 0) =
            JobState.jobsIn (x.moveJob src jk.2 hsource) {i} -
              JobState.jobsIn x {i}
        rw [if_pos hsource]
        simpa [nominalCoordinateIncrement, destinationIndicator,
          selectedSourceIndicator] using hmove.symm
      · simp [actualCoordinateIncrement, queueStep, hsource]

/-- Invariance transports the expectation of every real queue-state
observable through one concrete randomized transition. -/
theorem stationary_expectation
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat)))
    (hpi : IsInvariantPMF G N U K pi)
    (g : JobState Buffer (K : Nat) -> Real) :
    Finset.univ.sum (fun x =>
        (pi x).toReal *
          Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
              g (queueStep x event.1 event.2))) =
      Finset.univ.sum (fun x => (pi x).toReal * g x) := by
  have hinvariant := congrArg
    (fun p : PMF (JobState Buffer (K : Nat)) =>
      Finset.univ.sum (fun x => (p x).toReal * g x)) hpi
  rw [PMF.sum_bind_real] at hinvariant
  simpa only [transitionPMF, PMF.sum_map_real] using hinvariant

/-- Every coordinate has zero expected executed drift under an invariant
queue law. -/
theorem stationary_actualCoordinateIncrement_eq_zero
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat)))
    (hpi : IsInvariantPMF G N U K pi)
    (i : Buffer) :
    Finset.univ.sum (fun x =>
      (pi x).toReal *
        Finset.univ.sum (fun event =>
          ((epochLaw G N U K) event).toReal *
            actualCoordinateIncrement x i event)) = 0 := by
  have hstationary :=
    stationary_expectation G N U K pi hpi
      (fun x => JobState.jobsIn x ({i} : Finset Buffer))
  simp_rw [actualCoordinateIncrement_eq_jobsIn]
  calc
    Finset.univ.sum (fun x =>
        (pi x).toReal *
          Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
              (JobState.jobsIn (queueStep x event.1 event.2) {i} -
                JobState.jobsIn x {i}))) =
        Finset.univ.sum (fun x =>
          (pi x).toReal *
              Finset.univ.sum (fun event =>
                ((epochLaw G N U K) event).toReal *
                  JobState.jobsIn (queueStep x event.1 event.2) {i}) -
            (pi x).toReal * JobState.jobsIn x {i}) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [<- mul_sub]
      congr 1
      calc
        Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
              (JobState.jobsIn (queueStep x event.1 event.2) {i} -
                JobState.jobsIn x {i})) =
            Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                  JobState.jobsIn (queueStep x event.1 event.2) {i} -
                ((epochLaw G N U K) event).toReal *
                  JobState.jobsIn x {i}) := by
          apply Finset.sum_congr rfl
          intro event _
          ring
        _ = Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                JobState.jobsIn (queueStep x event.1 event.2) {i}) -
            Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                JobState.jobsIn x {i}) := by
          rw [Finset.sum_sub_distrib]
        _ = Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                JobState.jobsIn (queueStep x event.1 event.2) {i}) -
            JobState.jobsIn x {i} := by
          rw [<- Finset.sum_mul, PMF.sum_toReal]
          simp
    _ = Finset.univ.sum (fun x =>
          (pi x).toReal *
            Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                JobState.jobsIn (queueStep x event.1 event.2) {i})) -
        Finset.univ.sum (fun x =>
          (pi x).toReal * JobState.jobsIn x {i}) := by
      rw [Finset.sum_sub_distrib]
    _ = 0 := sub_eq_zero.mpr hstationary

/-! ## Nominal flow residual -/

/-- Conditional probability that a type-`(j,k)` token nominally selects
source buffer `i`. -/
noncomputable def sourceSelectionProbability
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k i : Buffer) : Real :=
  ((U.distribution K j k) (some i)).toReal

/-- Nominal inflow minus nominal selected outflow at one buffer.  This is the
linear flow-balance residual used in Proposition 3, Part 2. -/
noncomputable def nominalFlowResidual
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (i : Buffer) : Real :=
  Finset.univ.sum fun jk : Prod Server Buffer =>
    N.phi jk.1 jk.2 *
      (destinationIndicator i jk.2 -
        sourceSelectionProbability G U K jk.1 jk.2 i)

/-- The conditional expectation of the selected-source indicator is exactly
the corresponding action atom. -/
theorem expected_selectedSourceIndicator
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k i : Buffer) :
    Finset.univ.sum (fun action =>
        ((U.distribution K j k) action).toReal *
          selectedSourceIndicator i action) =
      sourceSelectionProbability G U K j k i := by
  classical
  rw [Finset.sum_eq_single (some i)]
  · simp [selectedSourceIndicator, sourceSelectionProbability]
  · intro action _ haction
    cases action with
    | none =>
        simp [selectedSourceIndicator]
    | some src =>
        have hsrc : Not (src = i) := by
          intro h
          apply haction
          simp [h]
        simp [selectedSourceIndicator, hsrc]
  · intro h
    exact (h (Finset.mem_univ (some i))).elim

/-- Conditional expected nominal coordinate drift for a fixed token type. -/
theorem expected_nominalCoordinateIncrement
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (jk : Prod Server Buffer) (i : Buffer) :
    Finset.univ.sum (fun action =>
        ((U.distribution K jk.1 jk.2) action).toReal *
          nominalCoordinateIncrement i (jk, action)) =
      destinationIndicator i jk.2 -
        sourceSelectionProbability G U K jk.1 jk.2 i := by
  unfold nominalCoordinateIncrement
  calc
    Finset.univ.sum (fun action =>
        ((U.distribution K jk.1 jk.2) action).toReal *
          (destinationIndicator i jk.2 -
            selectedSourceIndicator i action)) =
        Finset.univ.sum (fun action =>
          destinationIndicator i jk.2 *
              ((U.distribution K jk.1 jk.2) action).toReal -
            ((U.distribution K jk.1 jk.2) action).toReal *
              selectedSourceIndicator i action) := by
      apply Finset.sum_congr rfl
      intro action _
      ring
    _ =
        destinationIndicator i jk.2 *
            Finset.univ.sum (fun action =>
              ((U.distribution K jk.1 jk.2) action).toReal) -
          Finset.univ.sum (fun action =>
            ((U.distribution K jk.1 jk.2) action).toReal *
              selectedSourceIndicator i action) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = destinationIndicator i jk.2 -
        sourceSelectionProbability G U K jk.1 jk.2 i := by
      rw [actionDistribution_normalized G U K,
        expected_selectedSourceIndicator G U K]
      ring

/-- The explicit phi-linear residual is the expected nominal increment under
the same token/action law that defines the queue kernel. -/
theorem nominalFlowResidual_eq_epochExpectation
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (i : Buffer) :
    nominalFlowResidual G N U K i =
      Finset.univ.sum (fun event =>
        ((epochLaw G N U K) event).toReal *
          nominalCoordinateIncrement i event) := by
  rw [Fintype.sum_prod_type]
  unfold nominalFlowResidual
  apply Finset.sum_congr rfl
  intro jk _
  calc
    N.phi jk.1 jk.2 *
        (destinationIndicator i jk.2 -
          sourceSelectionProbability G U K jk.1 jk.2 i) =
      N.phi jk.1 jk.2 *
        Finset.univ.sum (fun action =>
          ((U.distribution K jk.1 jk.2) action).toReal *
            nominalCoordinateIncrement i (jk, action)) := by
      rw [expected_nominalCoordinateIncrement G U K]
    _ = Finset.univ.sum (fun action =>
        ((epochLaw G N U K) (jk, action)).toReal *
          nominalCoordinateIncrement i (jk, action)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro action _
      rw [epochLaw_toReal, N.tokenLaw_toReal]
      ring

/-- At a fixed queue state, exact expected waste bounds the discrepancy
between nominal and executed coordinate drift. -/
theorem abs_nominalFlowResidual_sub_expectedActual_le_oneStepWaste
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (x : JobState Buffer (K : Nat))
    (i : Buffer) :
    |nominalFlowResidual G N U K i -
        Finset.univ.sum (fun event =>
          ((epochLaw G N U K) event).toReal *
            actualCoordinateIncrement x i event)| <=
      oneStepWaste G N U K x := by
  rw [nominalFlowResidual_eq_epochExpectation,
    oneStepWaste_eq_epochExpectation]
  calc
    |Finset.univ.sum (fun event =>
          ((epochLaw G N U K) event).toReal *
            nominalCoordinateIncrement i event) -
        Finset.univ.sum (fun event =>
          ((epochLaw G N U K) event).toReal *
            actualCoordinateIncrement x i event)| =
      |Finset.univ.sum (fun event =>
        ((epochLaw G N U K) event).toReal *
          (nominalCoordinateIncrement i event -
            actualCoordinateIncrement x i event))| := by
      congr 1
      calc
        Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                nominalCoordinateIncrement i event) -
            Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                actualCoordinateIncrement x i event) =
          Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
                nominalCoordinateIncrement i event -
              ((epochLaw G N U K) event).toReal *
                actualCoordinateIncrement x i event) :=
            (Finset.sum_sub_distrib
              (fun event =>
                ((epochLaw G N U K) event).toReal *
                  nominalCoordinateIncrement i event)
              (fun event =>
                ((epochLaw G N U K) event).toReal *
                  actualCoordinateIncrement x i event)).symm
        _ = Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
              (nominalCoordinateIncrement i event -
                actualCoordinateIncrement x i event)) := by
          apply Finset.sum_congr rfl
          intro event _
          ring
    _ <= Finset.univ.sum (fun event =>
        |((epochLaw G N U K) event).toReal *
          (nominalCoordinateIncrement i event -
            actualCoordinateIncrement x i event)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun event =>
        ((epochLaw G N U K) event).toReal *
          |nominalCoordinateIncrement i event -
            actualCoordinateIncrement x i event|) := by
      apply Finset.sum_congr rfl
      intro event _
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ <= Finset.univ.sum (fun event =>
        ((epochLaw G N U K) event).toReal *
          wasteIndicator x event.2) := by
      apply Finset.sum_le_sum
      intro event _
      exact mul_le_mul_of_nonneg_left
        (abs_nominal_sub_actual_le_waste x i event)
        ENNReal.toReal_nonneg

/-- Under every invariant PMF, stationary expected waste dominates the
absolute nominal flow imbalance at every buffer. -/
theorem abs_nominalFlowResidual_le_stationaryOneStepWaste
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat)))
    (hpi : IsInvariantPMF G N U K pi)
    (i : Buffer) :
    |nominalFlowResidual G N U K i| <=
      stationaryOneStepWaste G N U K pi := by
  let actualExpectation :
      JobState Buffer (K : Nat) -> Real :=
    fun x =>
      Finset.univ.sum (fun event =>
        ((epochLaw G N U K) event).toReal *
          actualCoordinateIncrement x i event)
  have hactual :
      Finset.univ.sum (fun x =>
        (pi x).toReal * actualExpectation x) = 0 := by
    exact stationary_actualCoordinateIncrement_eq_zero
      G N U K pi hpi i
  have hrepresentation :
      nominalFlowResidual G N U K i =
        Finset.univ.sum (fun x =>
          (pi x).toReal *
            (nominalFlowResidual G N U K i -
              actualExpectation x)) := by
    calc
      nominalFlowResidual G N U K i =
          Finset.univ.sum (fun x =>
            (pi x).toReal * nominalFlowResidual G N U K i) := by
        rw [<- Finset.sum_mul, PMF.sum_toReal, one_mul]
      _ = Finset.univ.sum (fun x =>
            (pi x).toReal * nominalFlowResidual G N U K i) -
          Finset.univ.sum (fun x =>
            (pi x).toReal * actualExpectation x) := by
        rw [hactual, sub_zero]
      _ = Finset.univ.sum (fun x =>
          (pi x).toReal *
            (nominalFlowResidual G N U K i -
              actualExpectation x)) := by
        rw [<- Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
  rw [hrepresentation]
  calc
    |Finset.univ.sum (fun x =>
        (pi x).toReal *
          (nominalFlowResidual G N U K i -
            actualExpectation x))| <=
      Finset.univ.sum (fun x =>
        |(pi x).toReal *
          (nominalFlowResidual G N U K i -
            actualExpectation x)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun x =>
        (pi x).toReal *
          |nominalFlowResidual G N U K i -
            actualExpectation x|) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    _ <= Finset.univ.sum (fun x =>
        (pi x).toReal * oneStepWaste G N U K x) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (abs_nominalFlowResidual_sub_expectedActual_le_oneStepWaste
          G N U K x i)
        ENNReal.toReal_nonneg

/-! ## Compact finite-kernel minimization -/

section FiniteKernelMinimization

variable {A : Type w} [Fintype A] [Nonempty A]

private def pmfSimplex (pi : PMF A) : stdSimplex Real A :=
  Subtype.mk
    (fun x => (pi x).toReal)
    (And.intro
      (fun _ => ENNReal.toReal_nonneg)
      (PMF.sum_toReal pi))

private def simplexPMF (p : stdSimplex Real A) : PMF A :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p x)) (by
    rw [(ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ)
      (fun x _ => stdSimplex.zero_le p x)).symm]
    rw [stdSimplex.sum_eq_one]
    simp)

@[simp]
private theorem pmfSimplex_apply
    (pi : PMF A) (x : A) :
    pmfSimplex pi x = (pi x).toReal :=
  rfl

@[simp]
private theorem simplexPMF_toReal
    (p : stdSimplex Real A) (x : A) :
    (simplexPMF p x).toReal = p x := by
  rw [simplexPMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (stdSimplex.zero_le p x)

private theorem bind_toReal
    (pi : PMF A) (P : A -> PMF A) (y : A) :
    ((pi.bind P) y).toReal =
      Finset.univ.sum
        (fun x => (pi x).toReal * (P x y).toReal) := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top (pi.apply_ne_top x)
      ((P x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul]

private def invariantSimplexSet (P : A -> PMF A) :
    Set (stdSimplex Real A) :=
  {p | forall y,
    Finset.univ.sum (fun x => p x * (P x y).toReal) = p y}

private theorem invariantSimplexSet_isClosed
    (P : A -> PMF A) :
    IsClosed (invariantSimplexSet P) := by
  rw [show invariantSimplexSet P =
      Set.iInter (fun y : A =>
        {p | Finset.univ.sum
          (fun x => p x * (P x y).toReal) = p y}) by
    ext p
    simp [invariantSimplexSet]]
  apply isClosed_iInter
  intro y
  apply isClosed_eq
  · apply continuous_finsetSum
    intro x _
    exact
      ((continuous_apply x).comp continuous_subtype_val).mul
        continuous_const
  · exact (continuous_apply y).comp continuous_subtype_val

private theorem pmfSimplex_mem_invariantSimplexSet
    (P : A -> PMF A)
    (pi : PMF A)
    (hpi : pi.bind P = pi) :
    invariantSimplexSet P (pmfSimplex pi) := by
  intro y
  change
    Finset.univ.sum
      (fun x => (pi x).toReal * (P x y).toReal) =
        (pi y).toReal
  rw [<- bind_toReal pi P y, hpi]

private theorem invariantSimplexSet_nonempty
    (P : A -> PMF A) :
    (invariantSimplexSet P).Nonempty := by
  obtain ⟨pi, hpi⟩ := FiniteMarkovChain.exists_invariant_pmf P
  exact ⟨pmfSimplex pi,
    pmfSimplex_mem_invariantSimplexSet P pi hpi⟩

private theorem invariantSimplexSet_isCompact
    (P : A -> PMF A) :
    IsCompact (invariantSimplexSet P) := by
  simpa only [Set.univ_inter] using
    isCompact_univ.inter_right (invariantSimplexSet_isClosed P)

private def simplexCost
    (cost : A -> Real)
    (p : stdSimplex Real A) : Real :=
  Finset.univ.sum fun x => p x * cost x

private theorem simplexCost_continuous
    (cost : A -> Real) :
    Continuous (simplexCost cost) := by
  unfold simplexCost
  apply continuous_finsetSum
  intro x _
  exact
    ((continuous_apply x).comp continuous_subtype_val).mul
      continuous_const

private theorem simplexCost_pmfSimplex
    (cost : A -> Real) (pi : PMF A) :
    simplexCost cost (pmfSimplex pi) =
      Finset.univ.sum (fun x => (pi x).toReal * cost x) :=
  rfl

private theorem simplexPMF_isInvariant
    (P : A -> PMF A)
    (p : stdSimplex Real A)
    (hp : invariantSimplexSet P p) :
    (simplexPMF p).bind P = simplexPMF p := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (((simplexPMF p).bind P).apply_ne_top y)
    ((simplexPMF p).apply_ne_top y)).mp
  rw [bind_toReal, simplexPMF_toReal]
  simp_rw [simplexPMF_toReal]
  exact hp y

private theorem expectedCost_simplexPMF
    (cost : A -> Real)
    (p : stdSimplex Real A) :
    Finset.univ.sum
        (fun x => (simplexPMF p x).toReal * cost x) =
      simplexCost cost p := by
  unfold simplexCost
  simp only [simplexPMF_toReal]

private theorem exists_minimizingInvariantPMFForKernel
    (P : A -> PMF A) (cost : A -> Real) :
    exists pi : PMF A,
      pi.bind P = pi /\
      forall pi' : PMF A,
        pi'.bind P = pi' ->
        Finset.univ.sum (fun x => (pi x).toReal * cost x) <=
          Finset.univ.sum (fun x => (pi' x).toReal * cost x) := by
  obtain ⟨p, hp, hminimum⟩ :=
    (invariantSimplexSet_isCompact P).exists_isMinOn
      (invariantSimplexSet_nonempty P)
      (simplexCost_continuous cost).continuousOn
  let pi := simplexPMF p
  refine ⟨pi, simplexPMF_isInvariant P p hp, ?_⟩
  intro pi' hpi'
  rw [show Finset.univ.sum
      (fun x => (pi x).toReal * cost x) =
        simplexCost cost p by
    exact expectedCost_simplexPMF cost p]
  rw [<- simplexCost_pmfSimplex cost pi']
  exact hminimum
    (pmfSimplex_mem_invariantSimplexSet P pi' hpi')

end FiniteKernelMinimization

/-- The minimum stationary waste is attained by an invariant PMF. -/
theorem exists_minimizingInvariantPMF
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    exists pi : PMF (JobState Buffer (K : Nat)),
      IsInvariantPMF G N U K pi /\
      forall pi' : PMF (JobState Buffer (K : Nat)),
        IsInvariantPMF G N U K pi' ->
        stationaryOneStepWaste G N U K pi <=
          stationaryOneStepWaste G N U K pi' := by
  simpa only [IsInvariantPMF, stationaryOneStepWaste] using
    exists_minimizingInvariantPMFForKernel
      (transitionPMF G N U K)
      (oneStepWaste G N U K)

/-! ## Minimum invariant loss and concrete performance -/

/-- Stationary losses generated by invariant PMFs of the finite chain. -/
def invariantLossSet
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) : Set Real :=
  {r | exists pi : PMF (JobState Buffer (K : Nat)),
    IsInvariantPMF G N U K pi /\
      r = stationaryOneStepWaste G N U K pi}

theorem invariantLossSet_nonempty
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    (invariantLossSet G N U K).Nonempty := by
  obtain ⟨pi, hpi⟩ := exists_invariantPMF G N U K
  exact ⟨stationaryOneStepWaste G N U K pi, pi, hpi, rfl⟩

theorem invariantLossSet_nonnegative
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    {r : Real}
    (hr : invariantLossSet G N U K r) :
    0 <= r := by
  obtain ⟨pi, _, rfl⟩ := hr
  exact stationaryOneStepWaste_nonneg G N U K pi

theorem invariantLossSet_le_one
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    {r : Real}
    (hr : invariantLossSet G N U K r) :
    r <= 1 := by
  obtain ⟨pi, _, rfl⟩ := hr
  exact stationaryOneStepWaste_le_one G N U K pi

theorem invariantLossSet_bddBelow
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    BddBelow (invariantLossSet G N U K) :=
  ⟨0, fun _ hr => invariantLossSet_nonnegative G N U K hr⟩

/-- Minimum stationary event-epoch loss over invariant queue laws. -/
noncomputable def minimumInvariantLoss
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) : Real :=
  sInf (invariantLossSet G N U K)

theorem minimumInvariantLoss_nonnegative
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    0 <= minimumInvariantLoss G N U K := by
  unfold minimumInvariantLoss
  apply le_csInf (invariantLossSet_nonempty G N U K)
  intro r hr
  exact invariantLossSet_nonnegative G N U K hr

theorem minimumInvariantLoss_le_stationaryOneStepWaste
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat)))
    (hpi : IsInvariantPMF G N U K pi) :
    minimumInvariantLoss G N U K <=
      stationaryOneStepWaste G N U K pi := by
  unfold minimumInvariantLoss
  apply csInf_le (invariantLossSet_bddBelow G N U K)
  exact ⟨pi, hpi, rfl⟩

theorem exists_minimumInvariantLossPMF
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    exists pi : PMF (JobState Buffer (K : Nat)),
      IsInvariantPMF G N U K pi /\
      minimumInvariantLoss G N U K =
        stationaryOneStepWaste G N U K pi := by
  obtain ⟨pi, hpi, hminimum⟩ :=
    exists_minimizingInvariantPMF G N U K
  refine ⟨pi, hpi, le_antisymm
    (minimumInvariantLoss_le_stationaryOneStepWaste
      G N U K pi hpi) ?_⟩
  unfold minimumInvariantLoss
  apply le_csInf (invariantLossSet_nonempty G N U K)
  intro r hr
  obtain ⟨pi', hpi', rfl⟩ := hr
  exact hminimum pi' hpi'

/-- A canonical minimizing invariant PMF, selected after attainment. -/
noncomputable def minimumInvariantPMF
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    PMF (JobState Buffer (K : Nat)) :=
  Classical.choose (exists_minimumInvariantLossPMF G N U K)

theorem minimumInvariantPMF_isInvariant
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    IsInvariantPMF G N U K
      (minimumInvariantPMF G N U K) :=
  (Classical.choose_spec
    (exists_minimumInvariantLossPMF G N U K)).1

theorem minimumInvariantLoss_eq_stationaryOneStepWaste
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    minimumInvariantLoss G N U K =
      stationaryOneStepWaste G N U K
        (minimumInvariantPMF G N U K) :=
  (Classical.choose_spec
    (exists_minimumInvariantLossPMF G N U K)).2

/-- The minimum-recurrent-class loss still dominates every nominal
coordinate flow imbalance. -/
theorem abs_nominalFlowResidual_le_minimumInvariantLoss
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (i : Buffer) :
    |nominalFlowResidual G N U K i| <=
      minimumInvariantLoss G N U K := by
  rw [minimumInvariantLoss_eq_stationaryOneStepWaste]
  exact abs_nominalFlowResidual_le_stationaryOneStepWaste
    G N U K (minimumInvariantPMF G N U K)
    (minimumInvariantPMF_isInvariant G N U K) i

theorem minimumInvariantLoss_le_one
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    minimumInvariantLoss G N U K <= 1 := by
  obtain ⟨pi, hpi⟩ := exists_invariantPMF G N U K
  exact
    (minimumInvariantLoss_le_stationaryOneStepWaste
      G N U K pi hpi).trans
      (stationaryOneStepWaste_le_one G N U K pi)

/-- Minimum invariant loss at every positive system size. -/
noncomputable def minimumInvariantLossFamily
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) : Real :=
  minimumInvariantLoss G N U K

theorem minimumInvariantLossFamily_nonnegative
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    0 <= minimumInvariantLossFamily G N U K :=
  minimumInvariantLoss_nonnegative G N U K

theorem minimumInvariantLossFamily_le_one
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) :
    minimumInvariantLossFamily G N U K <= 1 :=
  minimumInvariantLoss_le_one G N U K

/-! ## Fixed-policy flow imbalance -/

/-- Under the repaired Part 2 hypothesis, every selected-source probability
is independent of system size. -/
theorem sourceSelectionProbability_eq_of_isKIndependent
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (hfixed : U.IsKIndependent)
    (K L : PNat) (j : Server) (k i : Buffer) :
    sourceSelectionProbability G U K j k i =
      sourceSelectionProbability G U L j k i := by
  obtain ⟨distribution0, hdistribution⟩ := hfixed
  unfold sourceSelectionProbability
  rw [hdistribution K j k, hdistribution L j k]

/-- Consequently, the nominal flow residual is independent of system size. -/
theorem nominalFlowResidual_eq_of_isKIndependent
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (hfixed : U.IsKIndependent)
    (K L : PNat) (i : Buffer) :
    nominalFlowResidual G N U K i =
      nominalFlowResidual G N U L i := by
  unfold nominalFlowResidual
  apply Finset.sum_congr rfl
  intro jk _
  rw [sourceSelectionProbability_eq_of_isKIndependent
    G U hfixed K L jk.1 jk.2 i]

/-- An incompatible source buffer has zero selection probability under the
fixed compatibility support condition. -/
theorem sourceSelectionProbability_eq_zero_of_incompatible
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k i : Buffer)
    (hincompatible : Not (G.compatible i j)) :
    sourceSelectionProbability G U K j k i = 0 := by
  have hmass : (U.distribution K j k) (some i) = 0 := by
    by_contra hne
    exact hincompatible
      (U.compatible_support K j k (some i)
        ((PMF.mem_support_iff (U.distribution K j k) (some i)).2 hne))
  unfold sourceSelectionProbability
  rw [hmass]
  exact ENNReal.toReal_zero

/-- The incompatible witness coordinate has coefficient exactly one in its
own buffer-flow residual. -/
theorem incompatible_witness_coefficient
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k : Buffer)
    (hincompatible : Not (G.compatible k j)) :
    destinationIndicator k k -
        sourceSelectionProbability G U K j k k = 1 := by
  rw [sourceSelectionProbability_eq_zero_of_incompatible
    G U K j k k hincompatible]
  simp [destinationIndicator]

/-- A nonzero fixed nominal flow residual gives a uniform positive lower
bound on minimum invariant loss, hence a strictly positive liminf. -/
theorem positive_liminf_of_nominalFlowResidual_ne_zero
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (hfixed : U.IsKIndependent)
    (K0 : PNat) (i : Buffer)
    (hresidual : Not (nominalFlowResidual G N U K0 i = 0)) :
    0 < liminf (minimumInvariantLossFamily G N U) atTop := by
  have hlower :
      |nominalFlowResidual G N U K0 i| <=
        liminf (minimumInvariantLossFamily G N U) atTop := by
    apply le_liminf_of_le
      (isCoboundedUnder_ge_of_le (x := 1) atTop
        (minimumInvariantLossFamily_le_one G N U))
    exact Filter.Eventually.of_forall (fun K => by
      rw [nominalFlowResidual_eq_of_isKIndependent
        G N U hfixed K0 K i]
      exact abs_nominalFlowResidual_le_minimumInvariantLoss
        G N U K i)
  exact (abs_pos.mpr hresidual).trans_le hlower

/-! ## Support-preserving rate perturbations -/

/-- Move a fraction `t` of the token law toward one marked token.  The
hypotheses `0 <= t < 1` preserve nonnegativity and every positive server
rate. -/
def pointMassPerturbation
    (N : Network Buffer Server)
    (j0 : Server) (k0 : Buffer)
    (t : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    Network Buffer Server where
  compatible := N.compatible
  compatibleDecidable := N.compatibleDecidable
  buffer_has_neighbor := N.buffer_has_neighbor
  server_has_neighbor := N.server_has_neighbor
  phi j k :=
    (1 - t) * N.phi j k +
      t * if j = j0 /\ k = k0 then 1 else 0
  phi_nonneg j k := by
    apply add_nonneg
    · exact mul_nonneg (sub_nonneg.mpr ht1.le)
        (N.phi_nonneg j k)
    · apply mul_nonneg ht0
      split <;> norm_num
  server_rate_pos j := by
    have hfactor : 0 < 1 - t := sub_pos.mpr ht1
    calc
      0 < (1 - t) * Finset.univ.sum (fun k => N.phi j k) :=
        mul_pos hfactor (N.server_rate_pos j)
      _ <= Finset.univ.sum (fun k =>
          (1 - t) * N.phi j k +
            t * if j = j0 /\ k = k0 then 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k _
        exact le_add_of_nonneg_right
          (mul_nonneg ht0 (by positivity))
  total_rate := by
    rw [<- Fintype.sum_prod_type']
    simp_rw [Finset.sum_add_distrib]
    rw [<- Finset.mul_sum, Fintype.sum_prod_type, N.total_rate]
    have hpoint :
        Finset.univ.sum (fun jk : Prod Server Buffer =>
          if jk.1 = j0 /\ jk.2 = k0 then (1 : Real) else 0) = 1 := by
      rw [Finset.sum_eq_single (j0, k0)]
      · simp
      · intro jk _ hjk
        have hcond : Not (jk.1 = j0 /\ jk.2 = k0) := by
          intro h
          apply hjk
          ext
          · exact h.1
          · exact h.2
        simp [hcond]
      · intro h
        exact (h (Finset.mem_univ (j0, k0))).elim
    rw [<- Finset.mul_sum, hpoint]
    ring

@[simp]
theorem pointMassPerturbation_phi
    (N : Network Buffer Server)
    (j0 : Server) (k0 : Buffer)
    (t : Real) (ht0 : 0 <= t) (ht1 : t < 1)
    (j : Server) (k : Buffer) :
    (pointMassPerturbation N j0 k0 t ht0 ht1).phi j k =
      (1 - t) * N.phi j k +
        t * if j = j0 /\ k = k0 then 1 else 0 :=
  rfl

theorem pointMassPerturbation_sameCompatibility
    (N : Network Buffer Server)
    (j0 : Server) (k0 : Buffer)
    (t : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    SameCompatibility N
      (pointMassPerturbation N j0 k0 t ht0 ht1) := by
  intro i j
  rfl

/-- Perturbing toward a token already in `S` preserves exact support. -/
theorem pointMassPerturbation_hasRateSupport
    (N : Network Buffer Server)
    (S : Set (Prod Server Buffer))
    (hS : HasRateSupport N S)
    (j0 : Server) (k0 : Buffer)
    (hwitness : (j0, k0) ∈ S)
    (t : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    HasRateSupport
      (pointMassPerturbation N j0 k0 t ht0 ht1) S := by
  intro j k
  constructor
  · intro hpositive
    by_contra hnotS
    have hnotphi : Not (0 < N.phi j k) := by
      intro hphi
      exact hnotS ((hS j k).mp hphi)
    have hzero : N.phi j k = 0 :=
      le_antisymm (le_of_not_gt hnotphi) (N.phi_nonneg j k)
    have hne : Not (j = j0 /\ k = k0) := by
      intro h
      exact hnotS (by simpa [h.1, h.2] using hwitness)
    rw [pointMassPerturbation_phi, hzero, mul_zero,
      zero_add, if_neg hne, mul_zero] at hpositive
    exact (lt_irrefl 0 hpositive).elim
  · intro hmem
    have hphi : 0 < N.phi j k := (hS j k).mpr hmem
    have hfactor : 0 < 1 - t := sub_pos.mpr ht1
    calc
      0 < (1 - t) * N.phi j k := mul_pos hfactor hphi
      _ <= (pointMassPerturbation N j0 k0 t ht0 ht1).phi j k := by
        rw [pointMassPerturbation_phi]
        exact le_add_of_nonneg_right
          (mul_nonneg ht0 (by positivity))

theorem pointMassPerturbation_inSupportClass
    (base N : Network Buffer Server)
    (S : Set (Prod Server Buffer))
    (hN : InSupportClass base N S)
    (j0 : Server) (k0 : Buffer)
    (hwitness : (j0, k0) ∈ S)
    (t : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    InSupportClass base
      (pointMassPerturbation N j0 k0 t ht0 ht1) S := by
  refine ⟨fun i j => (hN.1 i j).trans
      (pointMassPerturbation_sameCompatibility
        N j0 k0 t ht0 ht1 i j),
    pointMassPerturbation_hasRateSupport
      N S hN.2 j0 k0 hwitness t ht0 ht1⟩

private theorem network_phi_le_one
    (N : Network Buffer Server) (j : Server) (k : Buffer) :
    N.phi j k <= 1 := by
  calc
    N.phi j k <= Finset.univ.sum
        (fun p : Prod Server Buffer => N.phi p.1 p.2) := by
      exact Finset.single_le_sum
        (fun p _ => N.phi_nonneg p.1 p.2)
        (Finset.mem_univ (j, k))
    _ = 1 := by
      rw [Fintype.sum_prod_type, N.total_rate]

/-- The perturbation moves every rate coordinate by at most `t`. -/
theorem pointMassPerturbation_rateDistance_le
    (N : Network Buffer Server)
    (j0 : Server) (k0 : Buffer)
    (t : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    rateDistance N
      (pointMassPerturbation N j0 k0 t ht0 ht1) <= t := by
  unfold rateDistance
  apply Finset.sup'_le
  intro p _
  rw [pointMassPerturbation_phi]
  have hphi0 := N.phi_nonneg p.1 p.2
  have hphi1 := network_phi_le_one N p.1 p.2
  split
  · rw [mul_one]
    have heq :
        N.phi p.1 p.2 -
            ((1 - t) * N.phi p.1 p.2 + t) =
          t * (N.phi p.1 p.2 - 1) := by
      ring
    rw [heq, abs_mul, abs_of_nonneg ht0,
      abs_of_nonpos (sub_nonpos.mpr hphi1)]
    nlinarith
  · rw [mul_zero, add_zero]
    have heq :
        N.phi p.1 p.2 - (1 - t) * N.phi p.1 p.2 =
          t * N.phi p.1 p.2 := by
      ring
    rw [heq, abs_mul, abs_of_nonneg ht0,
      abs_of_nonneg hphi0]
    exact mul_le_of_le_one_right ht0 hphi1

/-- The residual is affine under the point-mass perturbation. -/
theorem nominalFlowResidual_pointMassPerturbation
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (i : Buffer)
    (j0 : Server) (k0 : Buffer)
    (t : Real) (ht0 : 0 <= t) (ht1 : t < 1) :
    nominalFlowResidual G
        (pointMassPerturbation N j0 k0 t ht0 ht1) U K i =
      (1 - t) * nominalFlowResidual G N U K i +
        t * (destinationIndicator i k0 -
          sourceSelectionProbability G U K j0 k0 i) := by
  unfold nominalFlowResidual
  calc
    Finset.univ.sum (fun jk : Prod Server Buffer =>
        ((1 - t) * N.phi jk.1 jk.2 +
            t * if jk.1 = j0 /\ jk.2 = k0 then 1 else 0) *
          (destinationIndicator i jk.2 -
            sourceSelectionProbability G U K jk.1 jk.2 i)) =
      Finset.univ.sum (fun jk : Prod Server Buffer =>
          (1 - t) *
            (N.phi jk.1 jk.2 *
              (destinationIndicator i jk.2 -
                sourceSelectionProbability G U K jk.1 jk.2 i)) +
        if jk = (j0, k0) then
          t * (destinationIndicator i jk.2 -
            sourceSelectionProbability G U K jk.1 jk.2 i)
        else 0) := by
      apply Finset.sum_congr rfl
      intro jk _
      by_cases h : jk = (j0, k0)
      · simp [h]
        ring
      · have hp : Not (jk.1 = j0 /\ jk.2 = k0) := by
          simpa [Prod.ext_iff] using h
        simp [h, hp]
        ring
    _ = (1 - t) *
          Finset.univ.sum (fun jk : Prod Server Buffer =>
            N.phi jk.1 jk.2 *
              (destinationIndicator i jk.2 -
                sourceSelectionProbability G U K jk.1 jk.2 i)) +
        t * (destinationIndicator i k0 -
          sourceSelectionProbability G U K j0 k0 i) := by
      rw [Finset.sum_add_distrib, <- Finset.mul_sum]
      congr 1
      rw [Finset.sum_eq_single (j0, k0)]
      · simp
      · intro jk _ hne
        simp [hne]
      · intro h
        exact (h (Finset.mem_univ (j0, k0))).elim

/-! ## The open dense nonzero-residual set -/

theorem sourceSelectionProbability_nonneg
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k i : Buffer) :
    0 <= sourceSelectionProbability G U K j k i :=
  ENNReal.toReal_nonneg

theorem sourceSelectionProbability_le_one
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k i : Buffer) :
    sourceSelectionProbability G U K j k i <= 1 := by
  have h := (ENNReal.toReal_le_toReal
    ((U.distribution K j k).apply_ne_top (some i))
    (by simp : Ne (1 : ENNReal) (⊤ : ENNReal))).2
      ((U.distribution K j k).coe_le_one (some i))
  simpa [sourceSelectionProbability] using h

/-- Every destination-minus-selection coefficient lies in `[-1,1]`. -/
theorem abs_flowCoefficient_le_one
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (jk : Prod Server Buffer) (i : Buffer) :
    |destinationIndicator i jk.2 -
        sourceSelectionProbability G U K jk.1 jk.2 i| <= 1 := by
  have hprob0 :=
    sourceSelectionProbability_nonneg G U K jk.1 jk.2 i
  have hprob1 :=
    sourceSelectionProbability_le_one G U K jk.1 jk.2 i
  by_cases hdest : jk.2 = i
  · rw [destinationIndicator, if_pos hdest,
      abs_of_nonneg (sub_nonneg.mpr hprob1)]
    linarith
  · rw [destinationIndicator, if_neg hdest, zero_sub, abs_neg,
      abs_of_nonneg hprob0]
    exact hprob1

theorem rateDistance_nonnegative
    (N N' : Network Buffer Server) :
    0 <= rateDistance N N' := by
  let p : Prod Server Buffer :=
    Classical.choice (inferInstance : Nonempty (Prod Server Buffer))
  exact (abs_nonneg (N.phi p.1 p.2 - N'.phi p.1 p.2)).trans
    (Finset.le_sup'
      (fun q : Prod Server Buffer =>
        |N.phi q.1 q.2 - N'.phi q.1 q.2|)
      (Finset.mem_univ p))

theorem abs_phi_sub_le_rateDistance
    (N N' : Network Buffer Server)
    (jk : Prod Server Buffer) :
    |N.phi jk.1 jk.2 - N'.phi jk.1 jk.2| <=
      rateDistance N N' := by
  exact Finset.le_sup'
    (fun q : Prod Server Buffer =>
      |N.phi q.1 q.2 - N'.phi q.1 q.2|)
    (Finset.mem_univ jk)

@[simp]
theorem rateDistance_self (N : Network Buffer Server) :
    rateDistance N N = 0 := by
  unfold rateDistance
  simp

/-- The nominal residual is Lipschitz in the matrix sup distance, with the
finite token-alphabet cardinality as a sufficient constant. -/
theorem abs_nominalFlowResidual_sub_le_rateDistance
    (G N N' : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (i : Buffer) :
    |nominalFlowResidual G N U K i -
        nominalFlowResidual G N' U K i| <=
      (Fintype.card (Prod Server Buffer) : Real) *
        rateDistance N N' := by
  unfold nominalFlowResidual
  calc
    |Finset.univ.sum (fun jk : Prod Server Buffer =>
          N.phi jk.1 jk.2 *
            (destinationIndicator i jk.2 -
              sourceSelectionProbability G U K jk.1 jk.2 i)) -
        Finset.univ.sum (fun jk : Prod Server Buffer =>
          N'.phi jk.1 jk.2 *
            (destinationIndicator i jk.2 -
              sourceSelectionProbability G U K jk.1 jk.2 i))| =
      |Finset.univ.sum (fun jk : Prod Server Buffer =>
        (N.phi jk.1 jk.2 - N'.phi jk.1 jk.2) *
          (destinationIndicator i jk.2 -
            sourceSelectionProbability G U K jk.1 jk.2 i))| := by
      congr 1
      calc
        Finset.univ.sum (fun jk : Prod Server Buffer =>
              N.phi jk.1 jk.2 *
                (destinationIndicator i jk.2 -
                  sourceSelectionProbability G U K jk.1 jk.2 i)) -
            Finset.univ.sum (fun jk : Prod Server Buffer =>
              N'.phi jk.1 jk.2 *
                (destinationIndicator i jk.2 -
                  sourceSelectionProbability G U K jk.1 jk.2 i)) =
          Finset.univ.sum (fun jk : Prod Server Buffer =>
            N.phi jk.1 jk.2 *
                (destinationIndicator i jk.2 -
                  sourceSelectionProbability G U K jk.1 jk.2 i) -
              N'.phi jk.1 jk.2 *
                (destinationIndicator i jk.2 -
                  sourceSelectionProbability G U K jk.1 jk.2 i)) :=
            (Finset.sum_sub_distrib
              (fun jk : Prod Server Buffer =>
                N.phi jk.1 jk.2 *
                  (destinationIndicator i jk.2 -
                    sourceSelectionProbability G U K jk.1 jk.2 i))
              (fun jk : Prod Server Buffer =>
                N'.phi jk.1 jk.2 *
                  (destinationIndicator i jk.2 -
                    sourceSelectionProbability G U K jk.1 jk.2 i))).symm
        _ = Finset.univ.sum (fun jk : Prod Server Buffer =>
            (N.phi jk.1 jk.2 - N'.phi jk.1 jk.2) *
              (destinationIndicator i jk.2 -
                sourceSelectionProbability G U K jk.1 jk.2 i)) := by
          apply Finset.sum_congr rfl
          intro jk _
          ring
    _ <= Finset.univ.sum (fun jk : Prod Server Buffer =>
        |(N.phi jk.1 jk.2 - N'.phi jk.1 jk.2) *
          (destinationIndicator i jk.2 -
            sourceSelectionProbability G U K jk.1 jk.2 i)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.univ.sum (fun _ : Prod Server Buffer =>
        rateDistance N N') := by
      apply Finset.sum_le_sum
      intro jk _
      rw [abs_mul]
      calc
        |N.phi jk.1 jk.2 - N'.phi jk.1 jk.2| *
            |destinationIndicator i jk.2 -
              sourceSelectionProbability G U K jk.1 jk.2 i| <=
          rateDistance N N' * 1 := by
            exact mul_le_mul
              (abs_phi_sub_le_rateDistance N N' jk)
              (abs_flowCoefficient_le_one G U K jk i)
              (abs_nonneg _)
              (rateDistance_nonnegative N N')
        _ = rateDistance N N' := mul_one _
    _ = (Fintype.card (Prod Server Buffer) : Real) *
        rateDistance N N' := by
      simp [nsmul_eq_mul]

/-- Networks whose selected coordinate has nonzero nominal imbalance. -/
def nonzeroNominalFlowResidualSet
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (i : Buffer) :
    Set (Network Buffer Server) :=
  {N | Not (nominalFlowResidual G N U K i = 0)}

/-- The nonzero-residual set is relatively open in every fixed support
class. -/
theorem nonzeroNominalFlowResidualSet_isRelativelyOpen
    (base : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy base)
    (K : PNat) (i : Buffer)
    (S : Set (Prod Server Buffer)) :
    IsRelativelyOpenInSupportClass base S
      (nonzeroNominalFlowResidualSet base U K i) := by
  intro N hnonzero _
  change Not (nominalFlowResidual base N U K i = 0) at hnonzero
  let card : Real := Fintype.card (Prod Server Buffer)
  have hcard : 0 < card := by
    dsimp [card]
    exact_mod_cast Fintype.card_pos
  let epsilon :=
    |nominalFlowResidual base N U K i| / (2 * card)
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos (abs_pos.mpr hnonzero)
      (mul_pos (by norm_num) hcard)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro N' _ hdistance
  change Not (nominalFlowResidual base N' U K i = 0)
  intro hzero
  have hbound :=
    abs_nominalFlowResidual_sub_le_rateDistance
      base N N' U K i
  rw [hzero, sub_zero] at hbound
  have hscaled :
      card * rateDistance N N' <
        card * epsilon :=
    mul_lt_mul_of_pos_left hdistance hcard
  have hcard_epsilon :
      card * epsilon =
        |nominalFlowResidual base N U K i| / 2 := by
    dsimp [epsilon]
    field_simp
  rw [hcard_epsilon] at hscaled
  have hhalf :
      |nominalFlowResidual base N U K i| / 2 <
        |nominalFlowResidual base N U K i| := by
    linarith [abs_pos.mpr hnonzero]
  exact (not_lt_of_ge hbound) (hscaled.trans hhalf)

/-- At an incompatible supported token, the nonzero-residual set is dense in
the exact support class. -/
theorem nonzeroNominalFlowResidualSet_isDense
    (base : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy base)
    (K : PNat)
    (S : Set (Prod Server Buffer))
    (j0 : Server) (k0 : Buffer)
    (hwitness : (j0, k0) ∈ S)
    (hincompatible : Not (base.compatible k0 j0)) :
    IsDenseInSupportClass base S
      (nonzeroNominalFlowResidualSet base U K k0) := by
  intro N hN epsilon hepsilon
  by_cases hresidual :
      nominalFlowResidual base N U K k0 = 0
  · let t : Real := min (epsilon / 2) (1 / 2)
    have htpos : 0 < t := by
      dsimp [t]
      exact lt_min (half_pos hepsilon) (by norm_num)
    have ht0 : 0 <= t := htpos.le
    have ht1 : t < 1 := by
      exact (min_le_right (epsilon / 2) (1 / 2)).trans_lt
        (by norm_num)
    have htepsilon : t < epsilon := by
      exact (min_le_left (epsilon / 2) (1 / 2)).trans_lt
        (half_lt_self hepsilon)
    let N' := pointMassPerturbation N j0 k0 t ht0 ht1
    refine ⟨N',
      pointMassPerturbation_inSupportClass
        base N S hN j0 k0 hwitness t ht0 ht1,
      ?_, ?_⟩
    · change Not (nominalFlowResidual base N' U K k0 = 0)
      dsimp [N']
      rw [nominalFlowResidual_pointMassPerturbation,
        hresidual,
        incompatible_witness_coefficient
          base U K j0 k0 hincompatible]
      simp only [mul_zero, zero_add, mul_one]
      exact ne_of_gt htpos
    · exact
        (pointMassPerturbation_rateDistance_le
          N j0 k0 t ht0 ht1).trans_lt htepsilon
  · exact ⟨N, hN, hresidual, by
      simpa using hepsilon⟩

/-- Fully concrete proof of the repaired second clause of Proposition 3.
No claim about Part 1 is made here. -/
theorem stateIndependentNoExponent_part2
    (base : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy base)
    (hfixed : U.IsKIndependent)
    (S : Set (Prod Server Buffer))
    (_hcovers : SupportCoversEveryServer S)
    (hlimited : SupportHasLimitedFlexibility base S) :
    exists C : Set (Network Buffer Server),
      IsRelativelyOpenInSupportClass base S C /\
        IsDenseInSupportClass base S C /\
        forall N, N ∈ C -> InSupportClass base N S ->
          0 < liminf
            (minimumInvariantLossFamily base N U) atTop := by
  obtain ⟨j0, k0, hwitness, hincompatible⟩ := hlimited
  let K0 : PNat := 1
  let C :=
    nonzeroNominalFlowResidualSet base U K0 k0
  refine ⟨C,
    nonzeroNominalFlowResidualSet_isRelativelyOpen
      base U K0 k0 S,
    nonzeroNominalFlowResidualSet_isDense
      base U K0 S j0 k0 hwitness hincompatible,
    ?_⟩
  intro N hN _
  change Not (nominalFlowResidual base N U K0 k0 = 0) at hN
  exact positive_liminf_of_nominalFlowResidual_ne_zero
    base N U hfixed K0 k0 hN

/-! ## Proposition 3, Part 1: stationary second moments -/

/-- The executed increment is the real queue-coordinate difference. -/
theorem actualCoordinateIncrement_eq_coordinate_sub {K : Nat}
    (x : JobState Buffer K)
    (i : Buffer)
    (event : Prod (Prod Server Buffer) (Option Buffer)) :
    actualCoordinateIncrement x i event =
      (queueStep x event.1 event.2 i : Real) - (x i : Real) := by
  simpa [JobState.jobsIn] using
    actualCoordinateIncrement_eq_jobsIn x i event

/-- Stationarity makes the expected one-step change of every real observable
equal to zero. -/
theorem stationary_observableChange_eq_zero
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat)))
    (hpi : IsInvariantPMF G N U K pi)
    (g : JobState Buffer (K : Nat) -> Real) :
    Finset.univ.sum (fun x =>
      (pi x).toReal *
        Finset.univ.sum (fun event =>
          ((epochLaw G N U K) event).toReal *
            (g (queueStep x event.1 event.2) - g x))) = 0 := by
  have hstationary :=
    stationary_expectation G N U K pi hpi g
  calc
    Finset.univ.sum (fun x =>
        (pi x).toReal *
          Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
              (g (queueStep x event.1 event.2) - g x))) =
      Finset.univ.sum (fun x =>
        (pi x).toReal *
            Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                g (queueStep x event.1 event.2)) -
          (pi x).toReal * g x) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [<- mul_sub]
      congr 1
      calc
        Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
              (g (queueStep x event.1 event.2) - g x)) =
          Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
                g (queueStep x event.1 event.2) -
              ((epochLaw G N U K) event).toReal * g x) := by
            apply Finset.sum_congr rfl
            intro event _
            ring
        _ = Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                g (queueStep x event.1 event.2)) -
            Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal * g x) :=
          Finset.sum_sub_distrib
            (fun event =>
              ((epochLaw G N U K) event).toReal *
                g (queueStep x event.1 event.2))
            (fun event =>
              ((epochLaw G N U K) event).toReal * g x)
        _ = Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                g (queueStep x event.1 event.2)) -
            g x := by
          rw [<- Finset.sum_mul, PMF.sum_toReal]
          simp
    _ = Finset.univ.sum (fun x =>
          (pi x).toReal *
            Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                g (queueStep x event.1 event.2))) -
        Finset.univ.sum (fun x => (pi x).toReal * g x) := by
      rw [Finset.sum_sub_distrib]
    _ = 0 := sub_eq_zero.mpr hstationary

/-- Squared nominal movement can exceed squared executed movement only on a
wasted event, by at most one. -/
theorem nominalCoordinateIncrement_sq_le_actual_sq_add_waste {K : Nat}
    (x : JobState Buffer K)
    (i : Buffer)
    (event : Prod (Prod Server Buffer) (Option Buffer)) :
    (nominalCoordinateIncrement i event) ^ 2 <=
      (actualCoordinateIncrement x i event) ^ 2 +
        wasteIndicator x event.2 := by
  rcases event with ⟨jk, action⟩
  cases action with
  | none =>
      by_cases hdest : jk.2 = i <;>
        simp [nominalCoordinateIncrement, actualCoordinateIncrement,
          destinationIndicator, selectedSourceIndicator, wasteIndicator,
          hdest]
  | some src =>
      by_cases hsource : 0 < x src
      · simp [actualCoordinateIncrement, wasteIndicator, hsource,
          Nat.ne_of_gt hsource]
      · have hempty : x src = 0 := Nat.eq_zero_of_not_pos hsource
        by_cases hdest : jk.2 = i
        · by_cases hsrc : src = i
          · subst src
            simp [nominalCoordinateIncrement, actualCoordinateIncrement,
              destinationIndicator, selectedSourceIndicator, wasteIndicator,
              hempty, hdest]
          · simp [nominalCoordinateIncrement, actualCoordinateIncrement,
              destinationIndicator, selectedSourceIndicator, wasteIndicator,
              hsource, hempty, hdest, hsrc]
        · by_cases hsrc : src = i
          · subst src
            simp [nominalCoordinateIncrement, actualCoordinateIncrement,
              destinationIndicator, selectedSourceIndicator, wasteIndicator,
              hempty, hdest]
          · simp [nominalCoordinateIncrement, actualCoordinateIncrement,
              destinationIndicator, selectedSourceIndicator, wasteIndicator,
              hsource, hempty, hdest, hsrc]

/-- Pointwise second-moment inequality.  The potential change is the change
of the squared queue coordinate; all nominal/executed discrepancy is charged
to exact waste. -/
theorem nominal_sq_le_coordinate_sq_change_add_waste {K : Nat}
    (x : JobState Buffer K)
    (i : Buffer)
    (event : Prod (Prod Server Buffer) (Option Buffer)) :
    (nominalCoordinateIncrement i event) ^ 2 <=
      (queueStep x event.1 event.2 i : Real) ^ 2 -
          (x i : Real) ^ 2 -
        2 * (x i : Real) * nominalCoordinateIncrement i event +
        (2 * (K : Real) + 1) * wasteIndicator x event.2 := by
  let z := nominalCoordinateIncrement i event
  let a := actualCoordinateIncrement x i event
  let q : Real := x i
  let q' : Real := queueStep x event.1 event.2 i
  let w := wasteIndicator x event.2
  have hsq : z ^ 2 <= a ^ 2 + w :=
    nominalCoordinateIncrement_sq_le_actual_sq_add_waste x i event
  have hdiff : |z - a| <= w :=
    abs_nominal_sub_actual_le_waste x i event
  have hdiff_le : z - a <= w :=
    (le_abs_self (z - a)).trans hdiff
  have hq0 : 0 <= q := by
    dsimp [q]
    positivity
  have hqK : q <= (K : Real) := by
    dsimp [q]
    exact_mod_cast x.coordinate_le i
  have hw0 : 0 <= w := wasteIndicator_nonneg x event.2
  have hmul1 : q * (z - a) <= q * w :=
    mul_le_mul_of_nonneg_left hdiff_le hq0
  have hmul2 : q * w <= (K : Real) * w :=
    mul_le_mul_of_nonneg_right hqK hw0
  have ha : a = q' - q := by
    exact actualCoordinateIncrement_eq_coordinate_sub x i event
  dsimp [z, a, q, q', w] at *
  nlinarith

/-- Expected squared nominal increment of one coordinate under the
state-independent event law. -/
noncomputable def nominalSquaredIncrement
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (i : Buffer) : Real :=
  Finset.univ.sum fun event =>
    ((epochLaw G N U K) event).toReal *
      (nominalCoordinateIncrement i event) ^ 2

/-- For an incompatible type `(j,k)`, conditional nominal squared movement
of coordinate `k` is exactly one. -/
theorem incompatible_token_conditional_nominal_sq_eq_one
    (G : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k : Buffer)
    (hincompatible : Not (G.compatible k j)) :
    Finset.univ.sum (fun action =>
      ((U.distribution K j k) action).toReal *
        (nominalCoordinateIncrement k ((j, k), action)) ^ 2) = 1 := by
  calc
    Finset.univ.sum (fun action =>
        ((U.distribution K j k) action).toReal *
          (nominalCoordinateIncrement k ((j, k), action)) ^ 2) =
      Finset.univ.sum (fun action =>
        ((U.distribution K j k) action).toReal *
          (1 - selectedSourceIndicator k action)) := by
      apply Finset.sum_congr rfl
      intro action _
      cases action with
      | none =>
          simp [nominalCoordinateIncrement, destinationIndicator,
            selectedSourceIndicator]
      | some src =>
          by_cases hsrc : src = k <;>
            simp [nominalCoordinateIncrement, destinationIndicator,
              selectedSourceIndicator, hsrc]
    _ = Finset.univ.sum (fun action =>
          ((U.distribution K j k) action).toReal) -
        Finset.univ.sum (fun action =>
          ((U.distribution K j k) action).toReal *
            selectedSourceIndicator k action) := by
      calc
        Finset.univ.sum (fun action =>
            ((U.distribution K j k) action).toReal *
              (1 - selectedSourceIndicator k action)) =
          Finset.univ.sum (fun action =>
            ((U.distribution K j k) action).toReal -
              ((U.distribution K j k) action).toReal *
                selectedSourceIndicator k action) := by
            apply Finset.sum_congr rfl
            intro action _
            ring
        _ = _ :=
          Finset.sum_sub_distrib
            (fun action =>
              ((U.distribution K j k) action).toReal)
            (fun action =>
              ((U.distribution K j k) action).toReal *
                selectedSourceIndicator k action)
    _ = 1 := by
      rw [actionDistribution_normalized G U K,
        expected_selectedSourceIndicator G U K,
        sourceSelectionProbability_eq_zero_of_incompatible
          G U K j k k hincompatible]
      ring

/-- A positive-rate incompatible token contributes its full rate to nominal
quadratic variation. -/
theorem phi_le_nominalSquaredIncrement
    (G N : Network Buffer Server)
    (hgraph : SameCompatibility G N)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k : Buffer)
    (hincompatible : Not (N.compatible k j)) :
    N.phi j k <= nominalSquaredIncrement G N U K k := by
  have hbase : Not (G.compatible k j) := by
    intro h
    exact hincompatible ((hgraph k j).mp h)
  unfold nominalSquaredIncrement
  rw [Fintype.sum_prod_type]
  calc
    N.phi j k =
        N.phi j k *
          Finset.univ.sum (fun action =>
            ((U.distribution K j k) action).toReal *
              (nominalCoordinateIncrement k ((j, k), action)) ^ 2) := by
      rw [incompatible_token_conditional_nominal_sq_eq_one
        G U K j k hbase, mul_one]
    _ <= Finset.univ.sum (fun jk : Prod Server Buffer =>
        Finset.univ.sum (fun action =>
          ((epochLaw G N U K) (jk, action)).toReal *
            (nominalCoordinateIncrement k (jk, action)) ^ 2)) := by
      have hselected :
          N.phi j k *
              Finset.univ.sum (fun action =>
                ((U.distribution K j k) action).toReal *
                  (nominalCoordinateIncrement
                    k ((j, k), action)) ^ 2) =
            Finset.univ.sum (fun action =>
              ((epochLaw G N U K) ((j, k), action)).toReal *
                (nominalCoordinateIncrement
                  k ((j, k), action)) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro action _
        rw [epochLaw_toReal, N.tokenLaw_toReal]
        ring
      rw [hselected]
      let f : Prod Server Buffer -> Real := fun jk =>
        Finset.univ.sum (fun action =>
          ((epochLaw G N U K) (jk, action)).toReal *
            (nominalCoordinateIncrement k (jk, action)) ^ 2)
      change f (j, k) <= Finset.univ.sum f
      exact Finset.single_le_sum
        (fun jk _ => by
          apply Finset.sum_nonneg
          intro action _
          exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
        (Finset.mem_univ (j, k))

/-- Conditional expected change of the squared queue coordinate. -/
noncomputable def expectedCoordinateSquareChange
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (x : JobState Buffer (K : Nat))
    (i : Buffer) : Real :=
  Finset.univ.sum fun event =>
    ((epochLaw G N U K) event).toReal *
      ((queueStep x event.1 event.2 i : Real) ^ 2 -
        (x i : Real) ^ 2)

/-- The pointwise second-moment inequality averaged over one independent
token/action draw. -/
theorem nominalSquaredIncrement_le_expectedSquareChange
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (x : JobState Buffer (K : Nat))
    (i : Buffer) :
    nominalSquaredIncrement G N U K i <=
      expectedCoordinateSquareChange G N U K x i -
        2 * (x i : Real) * nominalFlowResidual G N U K i +
        (2 * (((K : Nat) : Real)) + 1) *
          oneStepWaste G N U K x := by
  rw [nominalFlowResidual_eq_epochExpectation,
    oneStepWaste_eq_epochExpectation]
  unfold nominalSquaredIncrement expectedCoordinateSquareChange
  calc
    Finset.univ.sum (fun event =>
        ((epochLaw G N U K) event).toReal *
          (nominalCoordinateIncrement i event) ^ 2) <=
      Finset.univ.sum (fun event =>
        ((epochLaw G N U K) event).toReal *
          ((queueStep x event.1 event.2 i : Real) ^ 2 -
              (x i : Real) ^ 2 -
            2 * (x i : Real) * nominalCoordinateIncrement i event +
            (2 * (((K : Nat) : Real)) + 1) *
              wasteIndicator x event.2)) := by
      apply Finset.sum_le_sum
      intro event _
      exact mul_le_mul_of_nonneg_left
        (nominal_sq_le_coordinate_sq_change_add_waste x i event)
        ENNReal.toReal_nonneg
    _ = Finset.univ.sum (fun event =>
          ((epochLaw G N U K) event).toReal *
            ((queueStep x event.1 event.2 i : Real) ^ 2 -
              (x i : Real) ^ 2)) -
        2 * (x i : Real) *
          Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
              nominalCoordinateIncrement i event) +
        (2 * (((K : Nat) : Real)) + 1) *
          Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
              wasteIndicator x event.2) := by
      calc
        Finset.univ.sum (fun event =>
            ((epochLaw G N U K) event).toReal *
              ((queueStep x event.1 event.2 i : Real) ^ 2 -
                  (x i : Real) ^ 2 -
                2 * (x i : Real) *
                  nominalCoordinateIncrement i event +
                (2 * (((K : Nat) : Real)) + 1) *
                  wasteIndicator x event.2)) =
          Finset.univ.sum (fun event =>
              ((epochLaw G N U K) event).toReal *
                ((queueStep x event.1 event.2 i : Real) ^ 2 -
                  (x i : Real) ^ 2) -
              (2 * (x i : Real)) *
                (((epochLaw G N U K) event).toReal *
                  nominalCoordinateIncrement i event) +
              (2 * (((K : Nat) : Real)) + 1) *
                (((epochLaw G N U K) event).toReal *
                  wasteIndicator x event.2)) := by
            apply Finset.sum_congr rfl
            intro event _
            ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            <- Finset.mul_sum, <- Finset.mul_sum]

/-- Stationarity cancels the expected squared-coordinate potential change. -/
theorem stationary_expectedCoordinateSquareChange_eq_zero
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat)))
    (hpi : IsInvariantPMF G N U K pi)
    (i : Buffer) :
    Finset.univ.sum (fun x =>
      (pi x).toReal *
        expectedCoordinateSquareChange G N U K x i) = 0 := by
  exact stationary_observableChange_eq_zero G N U K pi hpi
    (fun x => (x i : Real) ^ 2)

/-- Mean queue length at one coordinate under a PMF. -/
noncomputable def stationaryCoordinateMean
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat)))
    (i : Buffer) : Real :=
  Finset.univ.sum fun x => (pi x).toReal * (x i : Real)

theorem stationaryCoordinateMean_nonneg
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat)))
    (i : Buffer) :
    0 <= stationaryCoordinateMean K pi i := by
  unfold stationaryCoordinateMean
  apply Finset.sum_nonneg
  intro x _
  positivity

theorem stationaryCoordinateMean_le
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat)))
    (i : Buffer) :
    stationaryCoordinateMean K pi i <= (((K : Nat) : Real)) := by
  unfold stationaryCoordinateMean
  calc
    Finset.univ.sum (fun x =>
        (pi x).toReal * (x i : Real)) <=
      Finset.univ.sum (fun x =>
        (pi x).toReal * (((K : Nat) : Real))) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact_mod_cast x.coordinate_le i
    _ = (((K : Nat) : Real)) := by
      rw [<- Finset.sum_mul, PMF.sum_toReal, one_mul]

/-- Under every invariant PMF, nominal quadratic variation is bounded by
`(4K+1)` times exact stationary waste. -/
theorem nominalSquaredIncrement_le_stationaryOneStepWaste_mul
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat)
    (pi : PMF (JobState Buffer (K : Nat)))
    (hpi : IsInvariantPMF G N U K pi)
    (i : Buffer) :
    nominalSquaredIncrement G N U K i <=
      (4 * (((K : Nat) : Real)) + 1) *
        stationaryOneStepWaste G N U K pi := by
  let V := nominalSquaredIncrement G N U K i
  let r := nominalFlowResidual G N U K i
  let Q := stationaryCoordinateMean K pi i
  let W := stationaryOneStepWaste G N U K pi
  let Kre : Real := (K : Nat)
  have havg :
      V <= -2 * r * Q + (2 * Kre + 1) * W := by
    calc
      V = Finset.univ.sum (fun x =>
          (pi x).toReal * V) := by
        rw [<- Finset.sum_mul, PMF.sum_toReal, one_mul]
      _ <= Finset.univ.sum (fun x =>
          (pi x).toReal *
            (expectedCoordinateSquareChange G N U K x i -
              2 * (x i : Real) * r +
              (2 * Kre + 1) * oneStepWaste G N U K x)) := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        exact nominalSquaredIncrement_le_expectedSquareChange
          G N U K x i
      _ = Finset.univ.sum (fun x =>
            (pi x).toReal *
              expectedCoordinateSquareChange G N U K x i) -
          2 * r * Q +
          (2 * Kre + 1) * W := by
        dsimp [Q, W, stationaryCoordinateMean,
          stationaryOneStepWaste]
        calc
          Finset.univ.sum (fun x =>
              (pi x).toReal *
                (expectedCoordinateSquareChange G N U K x i -
                  2 * (x i : Real) * r +
                  (2 * Kre + 1) * oneStepWaste G N U K x)) =
            Finset.univ.sum (fun x =>
                (pi x).toReal *
                  expectedCoordinateSquareChange G N U K x i -
                (2 * r) * ((pi x).toReal * (x i : Real)) +
                (2 * Kre + 1) *
                  ((pi x).toReal * oneStepWaste G N U K x)) := by
              apply Finset.sum_congr rfl
              intro x _
              ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              <- Finset.mul_sum, <- Finset.mul_sum]
      _ = -2 * r * Q + (2 * Kre + 1) * W := by
        rw [stationary_expectedCoordinateSquareChange_eq_zero
          G N U K pi hpi i]
        ring
  have hQ0 : 0 <= Q :=
    stationaryCoordinateMean_nonneg K pi i
  have hQK : Q <= Kre :=
    stationaryCoordinateMean_le K pi i
  have hW0 : 0 <= W :=
    stationaryOneStepWaste_nonneg G N U K pi
  have hrW : |r| <= W :=
    abs_nominalFlowResidual_le_stationaryOneStepWaste
      G N U K pi hpi i
  have hdrift : -2 * r * Q <= 2 * Kre * W := by
    calc
      -2 * r * Q = 2 * Q * (-r) := by ring
      _ <= 2 * Q * |r| := by
        exact mul_le_mul_of_nonneg_left (neg_le_abs r)
          (mul_nonneg (by norm_num) hQ0)
      _ <= 2 * Kre * |r| := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQK (by norm_num))
          (abs_nonneg r)
      _ <= 2 * Kre * W := by
        exact mul_le_mul_of_nonneg_left hrW
          (mul_nonneg (by norm_num) (hQ0.trans hQK))
  dsimp [V, r, Q, W, Kre] at havg ⊢
  calc
    nominalSquaredIncrement G N U K i <=
        -2 * nominalFlowResidual G N U K i *
            stationaryCoordinateMean K pi i +
          (2 * (((K : Nat) : Real)) + 1) *
            stationaryOneStepWaste G N U K pi :=
      havg
    _ <= 2 * (((K : Nat) : Real)) *
            stationaryOneStepWaste G N U K pi +
          (2 * (((K : Nat) : Real)) + 1) *
            stationaryOneStepWaste G N U K pi :=
      by linarith
    _ = (4 * (((K : Nat) : Real)) + 1) *
        stationaryOneStepWaste G N U K pi := by
      ring

/-- The incompatible token rate is bounded by `(4K+1)` times the selected
minimum invariant loss. -/
theorem phi_le_minimumInvariantLoss_mul
    (G N : Network Buffer Server)
    (hgraph : SameCompatibility G N)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k : Buffer)
    (hincompatible : Not (N.compatible k j)) :
    N.phi j k <=
      (4 * (((K : Nat) : Real)) + 1) *
        minimumInvariantLoss G N U K := by
  calc
    N.phi j k <= nominalSquaredIncrement G N U K k :=
      phi_le_nominalSquaredIncrement
        G N hgraph U K j k hincompatible
    _ <= (4 * (((K : Nat) : Real)) + 1) *
        stationaryOneStepWaste G N U K
          (minimumInvariantPMF G N U K) :=
      nominalSquaredIncrement_le_stationaryOneStepWaste_mul
        G N U K (minimumInvariantPMF G N U K)
        (minimumInvariantPMF_isInvariant G N U K) k
    _ = (4 * (((K : Nat) : Real)) + 1) *
        minimumInvariantLoss G N U K := by
      rw [minimumInvariantLoss_eq_stationaryOneStepWaste]

/-- Explicit finite-`K` lower bound supplied by any incompatible positive-rate
token.  This is stronger than the polynomial bound printed in Part 1. -/
theorem minimumInvariantLoss_ge_phi_div
    (G N : Network Buffer Server)
    (hgraph : SameCompatibility G N)
    (U : FixedGraphStateIndependentPolicy G)
    (K : PNat) (j : Server) (k : Buffer)
    (hincompatible : Not (N.compatible k j)) :
    N.phi j k / (4 * (((K : Nat) : Real)) + 1) <=
      minimumInvariantLoss G N U K := by
  have hden : 0 < 4 * (((K : Nat) : Real)) + 1 := by
    positivity
  apply (div_le_iff₀ hden).2
  simpa [mul_comm] using
    phi_le_minimumInvariantLoss_mul
      G N hgraph U K j k hincompatible

/-- Repaired Proposition 3, Part 1: every stationary state-independent policy
on a limited-flexibility network has loss `Omega(1/K^2)`.  The proof actually
establishes the stronger explicit `Omega(1/K)` bound above. -/
theorem minimumInvariantLossFamily_isOmegaOneDivSq
    (G N : Network Buffer Server)
    (hgraph : SameCompatibility G N)
    (hlimited : N.HasLimitedFlexibility)
    (U : FixedGraphStateIndependentPolicy G) :
    IsOmegaOneDivSq (minimumInvariantLossFamily G N U) := by
  obtain ⟨j, k, hincompatible, hphi⟩ := hlimited
  refine ⟨N.phi j k / 5, div_pos hphi (by norm_num), ?_⟩
  exact Filter.Eventually.of_forall (fun K => by
    let Kre : Real := (K : Nat)
    have hK : 1 <= Kre := by
      dsimp [Kre]
      exact_mod_cast K.pos
    have hK0 : 0 <= Kre := le_trans (by norm_num) hK
    have hKsq : Kre <= Kre ^ 2 := by
      have hprod : 0 <= Kre * (Kre - 1) :=
        mul_nonneg hK0 (sub_nonneg.mpr hK)
      nlinarith
    have hden :
        4 * Kre + 1 <= 5 * Kre ^ 2 := by
      nlinarith
    calc
      (N.phi j k / 5) / (K : Real) ^ 2 =
          N.phi j k / (5 * Kre ^ 2) := by
        dsimp [Kre]
        ring
      _ <= N.phi j k / (4 * Kre + 1) := by
        apply div_le_div_of_nonneg_left
          (N.phi_nonneg j k)
          (by positivity)
          hden
      _ <= minimumInvariantLossFamily G N U K := by
        exact minimumInvariantLoss_ge_phi_div
          G N hgraph U K j k hincompatible)

/-- The repaired throughput-loss exponent for the concrete randomized
state-independent chain. -/
noncomputable def minimumInvariantThroughputLossExponent
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G) : EReal :=
  negativeLimsupLogRate (minimumInvariantLossFamily G N U)

theorem minimumInvariantThroughputLossExponent_eq_zero_of_isOmegaOneDivSq
    (G N : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy G)
    (hOmega :
      IsOmegaOneDivSq (minimumInvariantLossFamily G N U)) :
    minimumInvariantThroughputLossExponent G N U = 0 := by
  unfold minimumInvariantThroughputLossExponent negativeLimsupLogRate
  exact negative_limsup_log_rate_eq_zero_of_isOmegaOneDivSq
    (minimumInvariantLossFamily G N U)
    (minimumInvariantLossFamily_nonnegative G N U)
    (minimumInvariantLossFamily_le_one G N U)
    hOmega

end StateIndependentChain

namespace PaperStatements

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-- Proposition `prop:state_ind_no_exp`, with all stochastic and loss data
supplied by `StateIndependentChain`.

Part 1 has the authorized limited-flexibility repair.  Part 2 has the
authorized fixed, `K`-independent policy repair and the support-level
limited-flexibility repair needed to exclude destination-serving ample
supports. -/
noncomputable def StateIndependentNoExponentStatement
    (base : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy base) : Prop :=
  (forall N, SameCompatibility base N ->
      N.HasLimitedFlexibility ->
      IsOmegaOneDivSq
          (StateIndependentChain.minimumInvariantLossFamily base N U) /\
        StateIndependentChain.minimumInvariantThroughputLossExponent
          base N U = 0) /\
    (U.IsKIndependent ->
      forall S : Set (Prod Server Buffer),
        SupportCoversEveryServer S ->
        SupportHasLimitedFlexibility base S ->
        exists C : Set (Network Buffer Server),
          IsRelativelyOpenInSupportClass base S C /\
            IsDenseInSupportClass base S C /\
            forall N, N ∈ C -> InSupportClass base N S ->
              0 < liminf
                (StateIndependentChain.minimumInvariantLossFamily base N U)
                atTop)

/-- Unconditional concrete proof of repaired Proposition 3 for the randomized
stationary state-independent chain. -/
theorem stateIndependentNoExponent
    (base : Network Buffer Server)
    (U : FixedGraphStateIndependentPolicy base) :
    StateIndependentNoExponentStatement base U := by
  constructor
  · intro N hgraph hlimited
    have hOmega :=
      StateIndependentChain.minimumInvariantLossFamily_isOmegaOneDivSq
        base N hgraph hlimited U
    exact ⟨hOmega,
      StateIndependentChain.minimumInvariantThroughputLossExponent_eq_zero_of_isOmegaOneDivSq
        base N U hOmega⟩
  · intro hfixed S hcovers hlimited
    exact StateIndependentChain.stateIndependentNoExponent_part2
      base U hfixed S hcovers hlimited

end PaperStatements
end StateDepMOR
