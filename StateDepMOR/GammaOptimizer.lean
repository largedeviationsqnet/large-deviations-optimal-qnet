import StateDepMOR.GammaLowerBound

/-!
# Optimizer for the explicit fixed-state exponent

This module proves the optimizer clause of the paper's explicit-gamma lemma.
For every minimizing limited cut, its exponential tilt is a feasible
candidate whose cost-to-drift ratio equals `gammaCB`.
-/

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

private theorem tiltedRate_vAlpha_lower_bound
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hcrp : N.HasCRP)
    (J : Finset Server) (hJ : N.IsLimitedSet J) :
    (N.netArrivalRate J - N.netServiceRate J) /
        N.cutMass alpha J <=
      vAlpha (N := N) alpha (tiltedRate N N.phi J) := by
  have harrival : 0 < N.netArrivalRate J :=
    hJ.2.trans (hcrp J hJ)
  have hbound :=
    cutGap_div_cutMass_le_vAlpha
      N alpha halpha (tiltedRate N N.phi J)
      (tiltedRate_nonnegative N J hJ.2 harrival) J hJ
  rwa [cutGap_tiltedRate N J hJ.2 harrival] at hbound

private theorem tiltedRate_vAlpha_pos
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hcrp : N.HasCRP)
    (J : Finset Server) (hJ : N.IsLimitedSet J) :
    0 < vAlpha (N := N) alpha (tiltedRate N N.phi J) := by
  have hgap : 0 < N.netArrivalRate J - N.netServiceRate J := by
    linarith [hcrp J hJ]
  have hmass : 0 < N.cutMass alpha J :=
    N.cutMass_pos halpha hJ
  exact (div_pos hgap hmass).trans_le
    (tiltedRate_vAlpha_lower_bound N alpha halpha hcrp J hJ)

private theorem tiltedRate_ratio_le_cutExponentTerm
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hcrp : N.HasCRP)
    (J : Finset Server) (hJ : N.IsLimitedSet J) :
    (N.localRate (tiltedRate N N.phi J) : EReal) /
        (vAlpha (N := N) alpha (tiltedRate N N.phi J) : EReal) <=
      (N.cutExponentTerm alpha J : EReal) := by
  let service := N.netServiceRate J
  let arrival := N.netArrivalRate J
  let mass := N.cutMass alpha J
  let value := vAlpha (N := N) alpha (tiltedRate N N.phi J)
  have hservice : 0 < service := hJ.2
  have hstrict : service < arrival := hcrp J hJ
  have harrival : 0 < arrival := hservice.trans hstrict
  have hmass : 0 < mass := N.cutMass_pos halpha hJ
  have hgap : 0 < arrival - service := sub_pos.2 hstrict
  have hlog : 0 < Real.log (arrival / service) :=
    Real.log_pos ((one_lt_div hservice).2 hstrict)
  have hvalueLower : (arrival - service) / mass <= value :=
    tiltedRate_vAlpha_lower_bound N alpha halpha hcrp J hJ
  have hvalue : 0 < value :=
    (div_pos hgap hmass).trans_le hvalueLower
  have hreal :
      ((arrival - service) * Real.log (arrival / service)) / value <=
        mass * Real.log (arrival / service) := by
    apply (div_le_iff₀ hvalue).2
    have hgap_le : arrival - service <= value * mass :=
      (div_le_iff₀ hmass).1 hvalueLower
    nlinarith
  rw [localRate_tiltedRate N J hservice harrival]
  rw [EReal.coe_ennreal_ofReal]
  rw [max_eq_left (mul_nonneg hgap.le hlog.le)]
  rw [← EReal.coe_div]
  change
    ((((arrival - service) * Real.log (arrival / service)) / value : Real) :
        EReal) <=
      ((mass * Real.log (arrival / service) : Real) : EReal)
  exact EReal.coe_le_coe_iff.2 hreal

theorem cutExponentTerm_eq_explicitExponent_of_minimizing
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer)
    (hflex : N.HasLimitedFlexibility)
    (J : Finset Server)
    (hJ : IsMinimizingCut (N := N) alpha J) :
    N.cutExponentTerm alpha J = N.explicitExponent alpha := by
  classical
  apply le_antisymm
  · have hsets := N.limitedSets_nonempty hflex
    rw [StateDepMOR.Network.explicitExponent, dif_pos hsets]
    obtain ⟨J', hJ'mem, hminimum⟩ :=
      Finset.exists_mem_eq_inf' hsets (N.cutExponentTerm alpha)
    rw [hminimum]
    exact hJ.2 J' ((N.mem_limitedSets J').1 hJ'mem)
  · exact N.explicitExponent_le_cutExponentTerm hflex alpha hJ.1

/-- Limited flexibility makes the finite family of cut-exponent terms
nonempty, so an actual minimizing cut exists. -/
theorem exists_minimizingCut
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer)
    (hflex : N.HasLimitedFlexibility) :
    exists J, IsMinimizingCut (N := N) alpha J := by
  classical
  have hsets := N.limitedSets_nonempty hflex
  choose J hJmem hJeq using
    Finset.exists_mem_eq_inf' hsets (N.cutExponentTerm alpha)
  refine Exists.intro J
    (And.intro ((N.mem_limitedSets J).1 hJmem) ?_)
  intro J' hJ'
  rw [hJeq.symm]
  exact Finset.inf'_le (N.cutExponentTerm alpha)
    ((N.mem_limitedSets J').2 hJ')

/-- The optimizer clause of `lem:explicit_gamma`: every minimizing cut tilt
attains the infimum defining `gammaCB`. -/
theorem explicitGammaOptimizerStatement
    (N : StateDepMOR.Network Buffer Server)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    ExplicitGammaOptimizerStatement (N := N) := by
  intro alpha halpha
  constructor
  · exact exists_minimizingCut N alpha hflex
  intro J hJ
  have hservice : 0 < N.netServiceRate J := hJ.1.2
  have harrival : 0 < N.netArrivalRate J :=
    hservice.trans (hcrp J hJ.1)
  have hnonnegative :
      IsNonnegativeRate (tiltedRate N N.phi J) :=
    tiltedRate_nonnegative N J hservice harrival
  have hvalue :
      0 < vAlpha (N := N) alpha (tiltedRate N N.phi J) :=
    tiltedRate_vAlpha_pos N alpha halpha hcrp J hJ.1
  refine And.intro hnonnegative (And.intro hvalue ?_)
  have hgamma_le :
      gammaCB (N := N) alpha <=
        (N.localRate (tiltedRate N N.phi J) : EReal) /
          (vAlpha (N := N) alpha (tiltedRate N N.phi J) : EReal) := by
    apply sInf_le
    exact Exists.intro (tiltedRate N N.phi J)
      (And.intro hnonnegative (And.intro hvalue rfl))
  apply le_antisymm
  · calc
      (N.localRate (tiltedRate N N.phi J) : EReal) /
            (vAlpha (N := N) alpha
              (tiltedRate N N.phi J) : EReal) <=
          (N.cutExponentTerm alpha J : EReal) :=
        tiltedRate_ratio_le_cutExponentTerm
          N alpha halpha hcrp J hJ.1
      _ = (N.explicitExponent alpha : EReal) := by
        rw [cutExponentTerm_eq_explicitExponent_of_minimizing
          N alpha hflex J hJ]
      _ = gammaCB (N := N) alpha :=
        (explicitGammaEquality N alpha halpha hflex hcrp).symm
  · exact hgamma_le

/-- A minimizing cut and its tilted rate jointly witness attainment of the
fixed-state converse exponent. -/
theorem exists_minimizingCut_attainingGammaCB
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    exists J,
      IsMinimizingCut (N := N) alpha J /\
      AttainsGammaCB (N := N) alpha (tiltedRate (N := N) N.phi J) := by
  have hoptimizer := explicitGammaOptimizerStatement N hflex hcrp alpha halpha
  let J := hoptimizer.1.choose
  have hJ := hoptimizer.1.choose_spec
  exact Exists.intro J (And.intro hJ (hoptimizer.2 J hJ))

/-- Pointwise explicit-gamma equality identifies the two interior-state
suprema used by the universal converse and the main theorem. -/
theorem gammaCBSup_eq_smwExponentSup
    (N : StateDepMOR.Network Buffer Server)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    gammaCBSup (N := N) = smwExponentSup N := by
  unfold gammaCBSup smwExponentSup
  apply congrArg sSup
  apply Set.ext
  intro q
  constructor
  · intro hq
    let alpha := hq.choose
    have halpha := hq.choose_spec
    refine Exists.intro alpha (And.intro halpha.1 ?_)
    calc
      q = gammaCB (N := N) alpha := halpha.2
      _ = (N.explicitExponent alpha : EReal) :=
        explicitGammaEquality N alpha halpha.1 hflex hcrp
  · intro hq
    let alpha := hq.choose
    have halpha := hq.choose_spec
    refine Exists.intro alpha (And.intro halpha.1 ?_)
    calc
      q = (N.explicitExponent alpha : EReal) := halpha.2
      _ = gammaCB (N := N) alpha :=
        (explicitGammaEquality N alpha halpha.1 hflex hcrp).symm

end StateDepMOR.PaperStatements.Network
