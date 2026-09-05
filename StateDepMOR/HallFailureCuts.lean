import StateDepMOR.Network

/-!
# Cut extraction from failure of CRP

Failure of the strict Hall condition produces one limited cut whose net arrival
rate is at most its net service rate.  This is the finite logical split used by
the two branches of Proposition 2.
-/

namespace StateDepMOR.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

theorem exists_limitedSet_of_not_hasCRP
    (N : Network Buffer Server) (hcrp : Not N.HasCRP) :
    exists J : Finset Server,
      N.IsLimitedSet J /\
      N.netArrivalRate J <= N.netServiceRate J := by
  unfold HasCRP at hcrp
  push Not at hcrp
  exact hcrp

theorem exists_strict_or_critical_cut_of_not_hasCRP
    (N : Network Buffer Server) (hcrp : Not N.HasCRP) :
    exists J : Finset Server,
      N.IsLimitedSet J /\
      (N.netArrivalRate J < N.netServiceRate J \/
        N.netArrivalRate J = N.netServiceRate J) := by
  obtain ⟨J, hJ, hle⟩ := N.exists_limitedSet_of_not_hasCRP hcrp
  exact ⟨J, hJ, lt_or_eq_of_le hle⟩

end StateDepMOR.Network
