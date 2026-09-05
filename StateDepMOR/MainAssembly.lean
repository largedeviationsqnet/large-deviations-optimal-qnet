import StateDepMOR.GammaOptimizer
import StateDepMOR.SMWSteepestDescentProofs
import StateDepMOR.SMWNegativeDriftProofs
import StateDepMOR.TightConverseProof

/-!
# Deterministic assembly for the main theorem

This module identifies the real and extended-real forms of the optimized SMW
exponent and assembles the final paper theorem from its proved stochastic
component statements.
-/

open Set

namespace StateDepMOR.PaperStatements

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-- The `EReal` supremum in the paper statement is the coercion of the
real-valued cut supremum used by the finite cut analysis. -/
theorem smwExponentSup_eq_coe_best
    (N : StateDepMOR.Network Buffer Server)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    smwExponentSup N = (N.bestSMWExponent : EReal) := by
  let S : Set Real := N.interiorExponentSet
  have hSne : S.Nonempty := N.interiorExponentSet_nonempty
  have hSbdd : BddAbove S := N.interiorExponentSet_bddAbove hflex hcrp
  have hset :
      {q : EReal | exists alpha : Simplex Buffer,
        alpha.IsInterior /\ q = (N.explicitExponent alpha : EReal)} =
        (fun r : Real => (r : EReal)) '' S := by
    ext q
    constructor
    · rintro ⟨alpha, halpha, rfl⟩
      exact ⟨N.explicitExponent alpha, ⟨alpha, halpha, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨alpha, halpha, rfl⟩, rfl⟩
      exact ⟨alpha, halpha, rfl⟩
  rw [smwExponentSup, hset]
  change
    (sSup ((fun r : Real => WithBot.some (WithTop.some r)) '' S) :
      WithBot (WithTop Real)) =
      WithBot.some (WithTop.some N.bestSMWExponent)
  let STop : Set (WithTop Real) :=
    (fun r : Real => (r : WithTop Real)) '' S
  have hSTop_nonempty : STop.Nonempty := hSne.image _
  have hSTop_bdd : BddAbove STop := OrderTop.bddAbove _
  have hwb :
      WithBot.some (sSup STop : WithTop Real) =
        (sSup ((fun r : WithTop Real => WithBot.some r) '' STop) :
          WithBot (WithTop Real)) := by
    exact WithBot.coe_sSup' hSTop_nonempty hSTop_bdd
  have himage :
      (fun r : Real => WithBot.some (WithTop.some r)) '' S =
        (fun r : WithTop Real => WithBot.some r) '' STop := by
    ext q
    simp only [STop, Set.mem_image]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(r : WithTop Real), ⟨r, hr, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [himage, ← hwb]
  have htop : ((sSup S : Real) : WithTop Real) = sSup STop := by
    simpa only [STop] using WithTop.coe_sSup' hSbdd
  rw [← htop]
  simp only [S, StateDepMOR.Network.bestSMWExponent]

/-- The real near-supremum lemma gives exactly the extended-real
"arbitrarily close" conclusion used in the main theorem. -/
theorem exists_interior_explicitExponent_close
    (N : StateDepMOR.Network Buffer Server)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists alpha : Simplex Buffer, alpha.IsInterior /\
      smwExponentSup N <
        (N.explicitExponent alpha : EReal) + (epsilon : EReal) := by
  obtain ⟨alpha, halpha, hclose⟩ :=
    N.exists_interior_exponent_gt_best_sub epsilon hepsilon
  refine ⟨alpha, halpha, ?_⟩
  rw [smwExponentSup_eq_coe_best N hflex hcrp]
  rw [← EReal.coe_add]
  exact EReal.coe_lt_coe_iff.mpr (sub_lt_iff_lt_add.mp hclose)

/-- Deterministic assembly of the main theorem from the concrete
achievability and resting-point lemmas. -/
theorem mainTightStatement_of_componentStatements
    (N : StateDepMOR.Network Buffer Server) [LinearOrder Buffer]
    (hachievability : AchievabilityBoundStatement N)
    (hresting : FluidRestingPointStatement N) :
    MainTightStatement N := by
  intro hconnected hflex hcrp
  have hfixed :
      forall (alpha : Simplex Buffer) (halpha : alpha.IsInterior),
        N.minimumInvariantPerformance.throughputLossExponent
            (N.smwPolicy alpha halpha) =
          (N.explicitExponent alpha : EReal) /\
        0 < N.explicitExponent alpha := by
    intro alpha halpha
    have htight :=
      tightConverseStatement_of_componentStatements
        N hachievability hresting alpha (N.smwPolicy alpha halpha)
    have hperformance :
        N.minimumInvariantPerformance.throughputLossExponent
            (N.smwPolicy alpha halpha) =
          Network.gammaCB (N := N) alpha :=
      htight halpha
        (N.smwPolicy_nonIdling alpha halpha)
        (Network.smwPolicy_steepestDescentCondition N alpha halpha)
        (Network.smwNegativeDriftStatement_proved
          N hconnected hflex hcrp alpha halpha)
    exact ⟨hperformance.trans
      (Network.explicitGammaEquality N alpha halpha hflex hcrp),
      N.explicitExponent_pos halpha hflex hcrp⟩
  refine ⟨hfixed, ?_, ?_⟩
  · intro U
    calc
      N.minimumInvariantPerformance.throughputLossExponent U =
          negativeLimsupLogRate (N.minimumInvariantLossFamily U) := rfl
      _ <= negativeLiminfLogRate (N.minimumInvariantLossFamily U) :=
        negativeLimsupLogRate_le_negativeLiminfLogRate
          (N.minimumInvariantLossFamily U)
      _ <= Network.gammaCBSup (N := N) :=
        N.pointwiseConverseStatement U
      _ = smwExponentSup N :=
        Network.gammaCBSup_eq_smwExponentSup N hflex hcrp
  · intro epsilon hepsilon
    obtain ⟨alpha, halpha, hclose⟩ :=
      exists_interior_explicitExponent_close
        N hflex hcrp epsilon hepsilon
    refine ⟨alpha, halpha, ?_⟩
    rw [(hfixed alpha halpha).1]
    exact hclose

/-- The unconditional repaired main theorem. -/
theorem mainTightStatement
    (N : StateDepMOR.Network Buffer Server) [LinearOrder Buffer] :
    MainTightStatement N :=
  mainTightStatement_of_componentStatements
    N
    (Network.achievabilityBoundStatement_proved N)
    N.fluidRestingPointStatement

#print axioms mainTightStatement

end StateDepMOR.PaperStatements
