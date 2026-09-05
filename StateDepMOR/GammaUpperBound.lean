import StateDepMOR.GammaTiltCost

/-!
# Explicit cut upper bound on gammaCB

The exponential tilt of any limited cut is feasible for the variational
definition of `gammaCB`. Its cost-to-drift ratio is at most the displayed
cut term. Taking a minimizing cut gives the explicit upper bound.
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
  have hlog : 0 < Real.log (arrival / service) := by
    exact Real.log_pos ((one_lt_div hservice).2 hstrict)
  have hvalueLower : (arrival - service) / mass <= value := by
    exact tiltedRate_vAlpha_lower_bound N alpha halpha hcrp J hJ
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

/-- Every limited cut supplies the corresponding explicit upper bound on
`gammaCB`. -/
theorem gammaCB_le_cutExponentTerm
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hcrp : N.HasCRP)
    (J : Finset Server) (hJ : N.IsLimitedSet J) :
    gammaCB (N := N) alpha <=
      (N.cutExponentTerm alpha J : EReal) := by
  have hservice : 0 < N.netServiceRate J := hJ.2
  have harrival : 0 < N.netArrivalRate J :=
    hservice.trans (hcrp J hJ)
  have hnonnegative :=
    tiltedRate_nonnegative N J hservice harrival
  have hvalue :=
    tiltedRate_vAlpha_pos N alpha halpha hcrp J hJ
  calc
    gammaCB (N := N) alpha <=
        (N.localRate (tiltedRate N N.phi J) : EReal) /
          (vAlpha (N := N) alpha (tiltedRate N N.phi J) : EReal) := by
      apply sInf_le
      exact ⟨tiltedRate N N.phi J, hnonnegative, hvalue, rfl⟩
    _ <= (N.cutExponentTerm alpha J : EReal) :=
      tiltedRate_ratio_le_cutExponentTerm
        N alpha halpha hcrp J hJ

/-- The easy direction of the explicit-gamma equality. -/
theorem gammaCB_le_explicitExponent
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    gammaCB (N := N) alpha <= (N.explicitExponent alpha : EReal) := by
  classical
  have hsets := N.limitedSets_nonempty hflex
  rw [StateDepMOR.Network.explicitExponent, dif_pos hsets]
  obtain ⟨J, hJmem, hminimum⟩ :=
    Finset.exists_mem_eq_inf' hsets (N.cutExponentTerm alpha)
  rw [hminimum]
  exact gammaCB_le_cutExponentTerm
    N alpha halpha hcrp J ((N.mem_limitedSets J).1 hJmem)

end StateDepMOR.PaperStatements.Network
