import StateDepMOR.GammaOptimizer
import StateDepMOR.SMWSteepestDescentProofs
import StateDepMOR.SMWNegativeDriftProofs
import StateDepMOR.FluidResting

/-!
# Concrete critical-subset remark

This module proves the repaired, fully mathematical readback of
`rem:critical-subset`. The informal strategy language is replaced by the
exact cut optimizer, tilted-rate, path-action, SMW drift, and nominal-fluid
attraction statements used by the paper.
-/

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]
variable [LinearOrder Buffer]

theorem criticalSubsetRemarkStatement_proved
    (N : StateDepMOR.Network Buffer Server) :
    CriticalSubsetRemarkStatement (N := N) := by
  intro hflex hcrp alpha halpha
  have hoptimizer :=
    explicitGammaOptimizerStatement N hflex hcrp alpha halpha
  refine ⟨hoptimizer.1, ?_,
    N.smwPolicy_nonIdling alpha halpha,
    smwPolicy_steepestDescentCondition N alpha halpha, ?_⟩
  · intro J hJ
    dsimp only
    let f := tiltedRate (N := N) N.phi J
    have hservice : 0 < N.netServiceRate J := hJ.1.2
    have harrival : 0 < N.netArrivalRate J :=
      hservice.trans (hcrp J hJ.1)
    have hgap :
        0 < N.netArrivalRate J - N.netServiceRate J :=
      sub_pos.mpr (hcrp J hJ.1)
    have hattains :
        AttainsGammaCB (N := N) alpha f :=
      hoptimizer.2 J hJ
    have hgamma :
        gammaCB (N := N) alpha =
          (N.cutExponentTerm alpha J : EReal) := by
      calc
        gammaCB (N := N) alpha =
            (N.explicitExponent alpha : EReal) :=
          explicitGammaEquality N alpha halpha hflex hcrp
        _ = (N.cutExponentTerm alpha J : EReal) := by
          rw [cutExponentTerm_eq_explicitExponent_of_minimizing
            N alpha hflex J hJ]
    refine ⟨hattains,
      cutGap_tiltedRate N J hservice harrival,
      hgap,
      localRate_tiltedRate N J hservice harrival,
      hgamma, ?_⟩
    intro T _hT
    exact poissonPathRate_linearMatrixPath N T f
  · intro hconnected
    refine ⟨
      smwNegativeDriftStatement_proved
        N hconnected hflex hcrp alpha halpha, ?_⟩
    exact smwFluidSolution_eq_alpha_after_uniform_time
      N hconnected hflex hcrp alpha halpha

end StateDepMOR.PaperStatements.Network
