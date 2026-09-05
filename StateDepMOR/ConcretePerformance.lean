import StateDepMOR.FiniteQueueStationarity

/-!
# Concrete finite-chain performance

This module defines stationary throughput loss from invariant laws of the
finite event-epoch queue chain. Unlike `PerformanceSemantics`, the loss is
not an unconstrained field: it is the stationary expected one-step waste.
-/

open scoped BigOperators ENNReal

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

variable (N : Network Buffer Server)

/-- A policy family containing one deterministic stationary policy for each
positive system size. -/
abbrev SystemSizePolicyFamily := N.DeterministicPolicySequence

/-- A selected invariant event-epoch law for every positive system size under
one policy family. The invariance field checks each selected PMF against the
transition PMF from `FiniteQueueChain`. -/
structure InvariantLawWitnessFamily (U : N.SystemSizePolicyFamily) where
  law : forall K : PNat, PMF (JobState Buffer (K : Nat))
  isInvariant : forall K : PNat, N.IsInvariantPMF (U K) (law K)

theorem oneStepWaste_mem_Icc {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K) :
    Set.Mem (Set.Icc (0 : Real) 1) (N.oneStepWaste U x) :=
  And.intro (N.oneStepWaste_nonneg U x) (N.oneStepWaste_le_one U x)

theorem stationaryOneStepWaste_mem_Icc {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (law : PMF (JobState Buffer K)) :
    Set.Mem (Set.Icc (0 : Real) 1) (N.stationaryOneStepWaste U law) :=
  And.intro (N.stationaryOneStepWaste_nonneg U law)
    (N.stationaryOneStepWaste_le_one U law)

/-- The concrete stationary loss for a policy family and selected invariant
laws. -/
noncomputable def stationaryLoss (U : N.SystemSizePolicyFamily)
    (laws : N.InvariantLawWitnessFamily U) (K : PNat) : Real :=
  N.stationaryOneStepWaste (U K) (laws.law K)

omit [DecidableEq Server] in
@[simp]
theorem stationaryLoss_eq_stationaryOneStepWaste
    (U : N.SystemSizePolicyFamily)
    (laws : N.InvariantLawWitnessFamily U) (K : PNat) :
    N.stationaryLoss U laws K =
      N.stationaryOneStepWaste (U K) (laws.law K) :=
  rfl

omit [DecidableEq Server] in
theorem stationaryLoss_law_isInvariant
    (U : N.SystemSizePolicyFamily)
    (laws : N.InvariantLawWitnessFamily U) (K : PNat) :
    N.IsInvariantPMF (U K) (laws.law K) :=
  laws.isInvariant K

theorem stationaryLoss_nonneg
    (U : N.SystemSizePolicyFamily)
    (laws : N.InvariantLawWitnessFamily U) (K : PNat) :
    0 <= N.stationaryLoss U laws K :=
  N.stationaryOneStepWaste_nonneg (U K) (laws.law K)

theorem stationaryLoss_le_one
    (U : N.SystemSizePolicyFamily)
    (laws : N.InvariantLawWitnessFamily U) (K : PNat) :
    N.stationaryLoss U laws K <= 1 :=
  N.stationaryOneStepWaste_le_one (U K) (laws.law K)

theorem stationaryLoss_mem_Icc
    (U : N.SystemSizePolicyFamily)
    (laws : N.InvariantLawWitnessFamily U) (K : PNat) :
    Set.Mem (Set.Icc (0 : Real) 1) (N.stationaryLoss U laws K) :=
  And.intro (N.stationaryLoss_nonneg U laws K)
    (N.stationaryLoss_le_one U laws K)

/-- Readback as the invariant-state average of the `phi`-weighted waste
indicators. -/
theorem stationaryLoss_eq_weightedWaste
    (U : N.SystemSizePolicyFamily)
    (laws : N.InvariantLawWitnessFamily U) (K : PNat) :
    N.stationaryLoss U laws K =
      Finset.univ.sum (fun x =>
        ((laws.law K) x).toReal *
          Finset.univ.sum (fun jk =>
            N.phi jk.1 jk.2 * N.wasteIndicator (U K) x jk)) := by
  rw [stationaryLoss, stationaryOneStepWaste]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [oneStepWaste]
  apply Finset.sum_congr rfl
  intro jk _
  rw [N.tokenLaw_toReal]

end Network

/-- Concrete performance semantics obtained by selecting invariant finite-chain
laws. Its loss is derived, rather than supplied independently. -/
structure ConcretePerformance (N : Network Buffer Server) where
  invariantLaws : forall U : N.SystemSizePolicyFamily,
    N.InvariantLawWitnessFamily U

namespace ConcretePerformance

variable {N : Network Buffer Server}

/-- Concrete performance obtained without any external stationary-law
witnesses, using the invariant PMFs constructed for each finite chain. -/
noncomputable def canonical (N : Network Buffer Server) :
    ConcretePerformance N where
  invariantLaws U :=
    { law := fun K => N.invariantPMF (U K)
      isInvariant := fun K => N.invariantPMF_isInvariant (U K) }

/-- Stationary event-epoch waste for the invariant law selected by `P`. -/
noncomputable def loss (P : ConcretePerformance N)
    (U : N.SystemSizePolicyFamily) (K : PNat) : Real :=
  N.stationaryLoss U (P.invariantLaws U) K

omit [DecidableEq Server] in
@[simp]
theorem loss_eq_stationaryOneStepWaste (P : ConcretePerformance N)
    (U : N.SystemSizePolicyFamily) (K : PNat) :
    P.loss U K = N.stationaryOneStepWaste
      (U K) ((P.invariantLaws U).law K) :=
  rfl

omit [DecidableEq Server] in
theorem selectedLaw_isInvariant (P : ConcretePerformance N)
    (U : N.SystemSizePolicyFamily) (K : PNat) :
    N.IsInvariantPMF (U K) ((P.invariantLaws U).law K) :=
  (P.invariantLaws U).isInvariant K

theorem loss_nonneg (P : ConcretePerformance N)
    (U : N.SystemSizePolicyFamily) (K : PNat) :
    0 <= P.loss U K :=
  N.stationaryLoss_nonneg U (P.invariantLaws U) K

theorem loss_le_one (P : ConcretePerformance N)
    (U : N.SystemSizePolicyFamily) (K : PNat) :
    P.loss U K <= 1 :=
  N.stationaryLoss_le_one U (P.invariantLaws U) K

theorem loss_mem_Icc (P : ConcretePerformance N)
    (U : N.SystemSizePolicyFamily) (K : PNat) :
    Set.Mem (Set.Icc (0 : Real) 1) (P.loss U K) :=
  And.intro (P.loss_nonneg U K) (P.loss_le_one U K)

/-- Compatibility bridge for existing logarithmic-rate definitions. The loss
field of the result is fixed to the concrete finite-chain loss. -/
noncomputable def toPerformanceSemantics (P : ConcretePerformance N) :
    PerformanceSemantics N where
  loss := P.loss
  loss_nonneg := P.loss_nonneg
  loss_le_one := P.loss_le_one

@[simp]
theorem toPerformanceSemantics_loss (P : ConcretePerformance N)
    (U : N.SystemSizePolicyFamily) (K : PNat) :
    P.toPerformanceSemantics.loss U K = P.loss U K :=
  rfl

end ConcretePerformance

end StateDepMOR
