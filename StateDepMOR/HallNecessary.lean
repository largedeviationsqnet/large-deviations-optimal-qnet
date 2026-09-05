import StateDepMOR.HallFailureCuts
import StateDepMOR.InitialPerformance
import StateDepMOR.HallCriticalEquality
import StateDepMOR.MinInvariantPerformance
import StateDepMOR.PaperStatements

/-!
# Necessity of complete resource pooling

This module combines the strict and critical Hall-cut branches into the
exact Proposition 2 readback.
-/

namespace StateDepMOR.PaperStatements

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-- Critical Hall equality forces polynomial minimum-invariant loss. -/
theorem minimumInvariantLoss_isOmegaOneDivSq_of_critical_cut
    (N : StateDepMOR.Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset) :
    IsOmegaOneDivSq (N.minimumInvariantLossFamily U) := by
  let laws : N.InvariantLawWitnessFamily U :=
    { law := fun K => N.minimumInvariantPMF (U K)
      isInvariant := fun K => N.minimumInvariantPMF_isInvariant (U K) }
  have hloss :
      N.minimumInvariantLossFamily U = N.stationaryLoss U laws := by
    funext K
    exact N.minimumInvariantLoss_eq_stationaryOneStepWaste (U K)
  rw [hloss]
  exact N.stationaryLoss_isOmegaOneDivSq_of_critical_cut
    U laws jset hlimited hcritical

/-- Critical Hall equality gives zero exponent under the repaired
minimum-recurrent-class convention. -/
theorem minimumInvariantThroughputLossExponent_eq_zero_of_critical_cut
    (N : StateDepMOR.Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset) :
    N.minimumInvariantPerformance.throughputLossExponent U = 0 := by
  exact N.minimumInvariantPerformance
    |>.throughputLossExponent_eq_zero_of_isOmegaOneDivSq U
      (minimumInvariantLoss_isOmegaOneDivSq_of_critical_cut
        N U jset hlimited hcritical)

/-- Exact concrete-chain proof of repaired Proposition 2 for every
deterministic stationary policy sequence. -/
theorem hallNecessaryStatement_proved
    (N : StateDepMOR.Network Buffer Server) :
    HallNecessaryStatement N := by
  intro hcrp U
  obtain ⟨J, hJ, hstrict | hcritical⟩ :=
    N.exists_strict_or_critical_cut_of_not_hasCRP hcrp
  · exact N.minimumInvariantThroughputLossExponent_eq_zero_of_strict_cutImbalance
      U J hstrict
  · exact minimumInvariantThroughputLossExponent_eq_zero_of_critical_cut
      N U J hJ hcritical

end StateDepMOR.PaperStatements
