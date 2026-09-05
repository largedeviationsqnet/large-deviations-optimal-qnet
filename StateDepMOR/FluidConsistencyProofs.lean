import StateDepMOR.FluidConsistency

/-!
# Consequences of fluid existence and stochastic consistency

This file proves the logical assembly following the fluid-limit definition:
the stochastic extension clause and the nominal Poisson-input clause together
make every convergent stochastic subsequence a fluid limit.
-/

open Filter MeasureTheory Set

namespace StateDepMOR.Network

universe u v w

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

/-- The second and third clauses of `lem:fms-existence` imply the paragraph
following the definition of a fluid limit. -/
theorem everyStochasticSubsequentialLimitIsFluidLimit
    (N : Network Buffer Server)
    {Omega : Type w} [MeasurableSpace Omega]
    (xi : N.ScaledStochasticExecution Omega)
    (hextension : N.StochasticFluidExtensionReadback xi)
    (hnominal : N.PoissonSubsequentialInputReadback xi) :
    N.EveryStochasticSubsequentialLimitIsFluidLimit xi := by
  intro T hT x0 U K hK A X
  have hnominal_ae := hnominal T hT U K hK A X
  filter_upwards [hnominal_ae] with omega homega
  intro hX0 hA hconverges
  obtain ⟨q, hq, s, hsX, _hallocation⟩ :=
    hextension T hT x0 U K hK omega (A omega) (X omega)
      hX0 hA hconverges
  exact ⟨s, hsX, homega hconverges⟩

/-- Packaged form using the single three-clause readback. -/
theorem FluidModelExistenceAndConsistencyReadback.everyLimitIsFluid
    (N : Network Buffer Server)
    {Omega : Type w} [MeasurableSpace Omega]
    (xi : N.ScaledStochasticExecution Omega)
    (h : N.FluidModelExistenceAndConsistencyReadback xi) :
    N.EveryStochasticSubsequentialLimitIsFluidLimit xi :=
  everyStochasticSubsequentialLimitIsFluidLimit N xi h.2.1 h.2.2

end StateDepMOR.Network
