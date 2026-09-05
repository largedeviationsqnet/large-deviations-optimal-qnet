import StateDepMOR.AchievabilityFinal
import StateDepMOR.Asymptotics

/-!
# Asymptotic rate transfer for achievability

This module bridges the `Nat` indexing used by `scaledLogMass` and the
positive-natural indexing used by the paper's throughput-loss exponent.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace StateDepMOR.PaperStatements.Network

universe w

/-- A pointwise probability bound transfers to the corresponding scaled
logarithmic bound. -/
theorem scaledLogLossPNat_le_scaledLogMass
    {Path : Type w} [MeasurableSpace Path]
    (loss : PNat -> Real) (mu : Nat -> Measure Path) (event : Set Path)
    (hbound : forall K : PNat,
      ENNReal.ofReal (loss K) <= mu (K : Nat) event)
    (n : Nat) :
    scaledLogLossPNat loss n.succPNat <=
      scaledLogMass mu event n := by
  have hlog :
      ENNReal.log (ENNReal.ofReal (loss n.succPNat)) <=
        ENNReal.log (mu (n + 1) event) := by
    apply ENNReal.log_le_log
    simpa only [Nat.succPNat_coe, Nat.succ_eq_add_one] using
      hbound n.succPNat
  unfold scaledLogLossPNat scaledLogMass
  have hden :
      (0 : EReal) <= ((((n + 1 : Nat) : Real)) : EReal) := by
    positivity
  have hdiv := EReal.div_le_div_right_of_nonneg hden hlog
  change
    ENNReal.log (ENNReal.ofReal (loss n.succPNat)) /
        ((((n + 1 : Nat) : Real)) : EReal) <=
      ENNReal.log (mu (n + 1) event) / ((n + 1 : Nat) : EReal)
  rw [<- EReal.coe_coe_eq_natCast (n + 1)]
  exact hdiv

/-- Any finite-system event-mass domination transfers to a `limsup`
inequality at the paper's exponential speed. -/
theorem limsup_scaledLogLossPNat_le_limsup_scaledLogMass
    {Path : Type w} [MeasurableSpace Path]
    (loss : PNat -> Real) (mu : Nat -> Measure Path) (event : Set Path)
    (hbound : forall K : PNat,
      ENNReal.ofReal (loss K) <= mu (K : Nat) event) :
    limsup (scaledLogLossPNat loss) atTop <=
      limsup (scaledLogMass mu event) atTop := by
  rw [<- StateDepMOR.limsup_comp_succPNat
    (scaledLogLossPNat loss)]
  exact limsup_le_limsup
    (Eventually.of_forall
      (scaledLogLossPNat_le_scaledLogMass loss mu event hbound))

end StateDepMOR.PaperStatements.Network
