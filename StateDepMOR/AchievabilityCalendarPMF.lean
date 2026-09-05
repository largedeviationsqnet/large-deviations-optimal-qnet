import StateDepMOR.AchievabilityCalendarBridge

open MeasureTheory ProbabilityTheory

namespace StateDepMOR.PaperStatements.Network

/-- Point mass of the positive-horizon calendar block count law. -/
theorem calendarBlockCountLaw_apply_toReal
    (K : PNat) {H : Real} (hH : 0 <= H) (n : Nat) :
    (calendarBlockCountLaw K H n).toReal =
      Real.exp (-(((K : Nat) : Real) * H)) *
        (((K : Nat) : Real) * H) ^ n / n.factorial := by
  rw [calendarBlockCountLaw, Measure.toPMF_apply]
  change
    (ProbabilityTheory.poissonMeasure
      (calendarBlockCountParameter K H)).real {n} = _
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  have hparameter :
      ((calendarBlockCountParameter K H : NNReal) : Real) =
        ((K : Nat) : Real) * H := by
    change ((K : Nat) : Real) * max H 0 =
      ((K : Nat) : Real) * H
    rw [max_eq_left hH]
  rw [hparameter]

end StateDepMOR.PaperStatements.Network
