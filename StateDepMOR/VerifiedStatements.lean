import StateDepMOR.PaperStatements
import StateDepMOR.Asymptotics
import StateDepMOR.NegativeDrift
import StateDepMOR.MainTheorem

/-!
# Checked paper-facing statements

Links the exact proposition readbacks to the portions proved in Lean.
-/

open scoped BigOperators

namespace StateDepMOR.PaperStatements

universe u

variable {Buffer : Type u}
variable [Fintype Buffer] [DecidableEq Buffer] [Nonempty Buffer]

omit [DecidableEq Buffer] in
/-- Definition `defn:lyap_func`, including the declared `[0,1]` range. -/
theorem lyapunovDefinitionStatement_proved (α x : Simplex Buffer) :
    LyapunovDefinitionStatement α x := by
  intro hα
  constructor
  · intro y
    exact Lyapunov.LAlphaAmbient_readback (fun i => α i) y
  · constructor
    · exact Lyapunov.LAlpha_nonnegative α x hα
    · rw [Lyapunov.LAlpha, Lyapunov.LAlphaAmbient]
      have hmin :
          0 ≤ Lyapunov.minCoordinate (fun i => x i / α i) := by
        unfold Lyapunov.minCoordinate
        apply Finset.le_inf' Finset.univ_nonempty
        intro i hi
        exact div_nonneg (x.nonneg i) (hα i).le
      linarith

omit [DecidableEq Buffer] in
/-- Exact readback of `lem:key_property_lyap`. -/
theorem keyLyapunovPropertiesStatement_proved :
    KeyLyapunovPropertiesStatement (Buffer := Buffer) := by
  constructor
  · intro α hα c hc Δx hsum hmem hmemScaled
    exact Lyapunov.LAlpha_centered_scale_invariance
      α hα c hc Δx hsum hmem hmemScaled
  · intro α hα Δx Δx' hsum hsum' hmemSum hmem hmem'
    exact Lyapunov.LAlpha_centered_subadditivity
      α hα Δx Δx' hsum hsum' hmemSum hmem hmem'

omit [DecidableEq Buffer] in
/-- Exact readback of Appendix lemma `lem:tech_lems`. -/
theorem technicalLyapunovLemmaStatement_proved :
    TechnicalLyapunovLemmaStatement (Buffer := Buffer) := by
  intro α x y hα
  exact ⟨Lyapunov.LAlpha_nonnegative α x hα,
    Lyapunov.LAlpha_eq_zero_iff α x hα,
    Lyapunov.LAlpha_lipschitz α x y hα⟩

end StateDepMOR.PaperStatements
