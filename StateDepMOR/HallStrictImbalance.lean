import StateDepMOR.Asymptotics
import StateDepMOR.ConcretePerformance
import StateDepMOR.FiniteQueueBalance

/-!
# Strict Hall imbalance

The strict case `lambda_J < mu_J` of Proposition 2 follows from stationary
cut balance. The critical equality case requires the separate random-walk
argument from the paper.
-/

open scoped ENNReal
open Filter

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace ConcretePerformance

variable {N : Network Buffer Server}

/-- A strict Hall imbalance gives a positive constant lower bound on the
concrete stationary loss at every system size. -/
theorem loss_ge_of_strict_cutImbalance
    (P : ConcretePerformance N) (U : N.SystemSizePolicyFamily)
    (jset : Finset Server)
    (hstrict : N.netArrivalRate jset < N.netServiceRate jset)
    (K : PNat) :
    N.netServiceRate jset - N.netArrivalRate jset <= P.loss U K := by
  exact N.stationaryOneStepWaste_ge_netImbalance
    (U K) ((P.invariantLaws U).law K)
    ((P.invariantLaws U).isInvariant K) jset

/-- The concrete loss is `Omega(1 / K^2)` in the strict-imbalance case
(in fact it is bounded below by a positive constant). -/
theorem loss_isOmegaOneDivSq_of_strict_cutImbalance
    (P : ConcretePerformance N) (U : N.SystemSizePolicyFamily)
    (jset : Finset Server)
    (hstrict : N.netArrivalRate jset < N.netServiceRate jset) :
    IsOmegaOneDivSq (P.loss U) := by
  let c := N.netServiceRate jset - N.netArrivalRate jset
  have hc : 0 < c := sub_pos.mpr hstrict
  refine ⟨c, hc, Filter.Eventually.of_forall ?_⟩
  intro K
  have hK : (1 : Real) <= (K : Real) := by
    exact_mod_cast PNat.pos K
  have hKsq : (1 : Real) <= (K : Real) ^ 2 := by
    nlinarith
  have hKsqPos : 0 < (K : Real) ^ 2 := lt_of_lt_of_le zero_lt_one hKsq
  calc
    c / (K : Real) ^ 2 <= c := by
      apply (div_le_iff₀ hKsqPos).2
      nlinarith
    _ <= P.loss U K :=
      P.loss_ge_of_strict_cutImbalance U jset hstrict K

/-- Every policy family has zero throughput-loss exponent when some cut has
strictly more net demand than net supply. -/
theorem throughputLossExponent_eq_zero_of_strict_cutImbalance
    (P : ConcretePerformance N) (U : N.SystemSizePolicyFamily)
    (jset : Finset Server)
    (hstrict : N.netArrivalRate jset < N.netServiceRate jset) :
    P.toPerformanceSemantics.throughputLossExponent U = 0 := by
  exact
    P.toPerformanceSemantics.throughputLossExponent_eq_zero_of_isOmegaOneDivSq
      U (P.loss_isOmegaOneDivSq_of_strict_cutImbalance U jset hstrict)

end ConcretePerformance

end StateDepMOR
