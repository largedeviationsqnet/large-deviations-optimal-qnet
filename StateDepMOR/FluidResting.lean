import StateDepMOR.FluidAttraction
import StateDepMOR.SMWNegativeDriftProofs

/-!
# Finite-time resting state of nominal SMW fluid solutions

This module combines the repaired boundary-inclusive SMW drift theorem with
the absolutely continuous attraction argument.  It proves the deterministic
fluid statement underlying the paper's resting-state discussion.
-/

open Set

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]
variable [LinearOrder Buffer]

/-- Under the paper's three network assumptions, every nominal fluid solution
for `SMW(alpha)` reaches `alpha` by one common finite time and remains there. -/
theorem smwFluidSolution_eq_alpha_after_uniform_time
    (N : StateDepMOR.Network Buffer Server)
    (hconnected : N.IsConnected)
    (hflex : N.HasLimitedFlexibility)
    (hcrp : N.HasCRP)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior) :
    exists T0, 0 < T0 /\
      forall (T : Real) (x0 : Simplex Buffer)
        (A : MatrixPath Server Buffer)
        (s : N.FluidModelSolution (N.smwPolicy alpha halpha) T x0 A),
        s.IsFluidLimit ->
        forall t, t ∈ Icc T0 T -> s.X t = fun i => alpha i := by
  have hnegative :
      NegativeDriftCondition (N := N) alpha (N.smwPolicy alpha halpha) :=
    smwNegativeDriftStatement_proved N hconnected hflex hcrp alpha halpha
  obtain ⟨eta, heta, hattraction⟩ :=
    FluidModelSolution.eq_alpha_of_nominal_negativeDrift
      alpha halpha hnegative
  refine ⟨1 / eta, div_pos zero_lt_one heta, ?_⟩
  intro T x0 A s hnominal t ht
  exact hattraction T x0 A s hnominal t
    ⟨(div_pos zero_lt_one heta).le.trans ht.1, ht.2⟩ ht.1

end StateDepMOR.PaperStatements.Network
