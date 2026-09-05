import StateDepMOR.FiniteQueueChain
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.StrongLaw

/-!
# IID marked token sequence

This module constructs the canonical event-epoch token sequence as a
countable product of the finite PMF `N.tokenLaw`. It proves coordinate laws,
mutual independence, and simultaneous almost-sure convergence of every
empirical token frequency.

This is an event-epoch model. It does not construct Poisson event times or a
continuous-time counting process.
-/

open MeasureTheory ProbabilityTheory

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

/-- The finite marked-token alphabet carries the discrete measurable space.
This named instance is activated only within this module to avoid changing
measurable-space inference for unrelated product types. -/
@[instance_reducible]
def tokenTypeMeasurableSpace :
    MeasurableSpace (TokenType (Buffer := Buffer) (Server := Server)) :=
  Top.top

attribute [local instance] tokenTypeMeasurableSpace

/-- Infinite zero-based event-epoch token paths. -/
abbrev TokenPath (_N : Network Buffer Server) :=
  Nat -> TokenType (Buffer := Buffer) (Server := Server)

variable (N : Network Buffer Server)

/-- The countable product of the marked-token one-step law. -/
noncomputable def tokenPathMeasure : Measure N.TokenPath :=
  Measure.infinitePi (fun _ : Nat => N.tokenLaw.toMeasure)

noncomputable instance tokenPathMeasure_isProbabilityMeasure :
    IsProbabilityMeasure N.tokenPathMeasure := by
  unfold tokenPathMeasure
  infer_instance

/-- The token observed at zero-based event epoch `r`. -/
def tokenAt (r : Nat) (omega : N.TokenPath) :
    TokenType (Buffer := Buffer) (Server := Server) :=
  omega r

omit [DecidableEq Buffer] [DecidableEq Server] in
theorem tokenAt_measurable (r : Nat) : Measurable (N.tokenAt r) :=
  measurable_pi_apply r

omit [DecidableEq Buffer] [DecidableEq Server] in
@[simp]
theorem tokenAt_map (r : Nat) :
    N.tokenPathMeasure.map (N.tokenAt r) = N.tokenLaw.toMeasure := by
  unfold tokenPathMeasure tokenAt
  exact Measure.infinitePi_map_eval
    (fun _ : Nat => N.tokenLaw.toMeasure) r

omit [DecidableEq Buffer] [DecidableEq Server] in
theorem tokenAt_hasLaw (r : Nat) :
    HasLaw (N.tokenAt r) N.tokenLaw.toMeasure N.tokenPathMeasure := by
  unfold tokenPathMeasure tokenAt
  exact (measurePreserving_eval_infinitePi
    (fun _ : Nat => N.tokenLaw.toMeasure) r).hasLaw

omit [DecidableEq Buffer] [DecidableEq Server] in
theorem tokenAt_identDistrib (r s : Nat) :
    IdentDistrib (N.tokenAt r) (N.tokenAt s)
      N.tokenPathMeasure N.tokenPathMeasure :=
  (N.tokenAt_hasLaw r).identDistrib (N.tokenAt_hasLaw s)

omit [DecidableEq Buffer] [DecidableEq Server] in
theorem tokenAt_iIndep :
    iIndepFun N.tokenAt N.tokenPathMeasure := by
  unfold tokenPathMeasure tokenAt
  exact iIndepFun_infinitePi
    (P := fun _ : Nat => N.tokenLaw.toMeasure)
    (X := fun _ token => token)
    (fun _ => measurable_id)

omit [DecidableEq Buffer] [DecidableEq Server] in
theorem tokenAt_indepFun {r s : Nat} (hrs : Not (r = s)) :
    IndepFun (N.tokenAt r) (N.tokenAt s) N.tokenPathMeasure :=
  N.tokenAt_iIndep.indepFun hrs

omit [DecidableEq Buffer] [DecidableEq Server] in
/-- Exact coordinate mass under the original marked-token PMF. -/
theorem tokenAt_probability (r : Nat)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    N.tokenPathMeasure {omega | N.tokenAt r omega = jk} =
      N.tokenLaw jk := by
  calc
    N.tokenPathMeasure {omega | N.tokenAt r omega = jk} =
        N.tokenLaw.toMeasure {token | token = jk} :=
      (N.tokenAt_hasLaw r).measure_eq
        (p := fun token => token = jk) MeasurableSpace.measurableSet_top
    _ = N.tokenLaw jk := by
      rw [Set.ofPred_eq_eq_singleton]
      exact PMF.toMeasure_apply_singleton N.tokenLaw jk
        MeasurableSpace.measurableSet_top

/-- Source readback of the coordinate mass as the corresponding `phi` entry. -/
theorem tokenAt_probability_eq_phi (r : Nat)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    N.tokenPathMeasure {omega | N.tokenAt r omega = jk} =
      ENNReal.ofReal (N.phi jk.1 jk.2) := by
  rw [N.tokenAt_probability r jk, N.tokenLaw_apply jk]

/-- The real indicator applied to one marked-token value. -/
def tokenIndicatorValue (_N : Network Buffer Server)
    (jk token : TokenType (Buffer := Buffer) (Server := Server)) : Real :=
  if token = jk then 1 else 0

theorem tokenIndicatorValue_measurable
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    Measurable (N.tokenIndicatorValue jk) :=
  Measurable.of_discrete

/-- The indicator process for one fixed marked-token type. -/
def tokenIndicator
    (jk : TokenType (Buffer := Buffer) (Server := Server))
    (r : Nat) (omega : N.TokenPath) : Real :=
  N.tokenIndicatorValue jk (N.tokenAt r omega)

theorem tokenIndicator_measurable
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (r : Nat) :
    Measurable (N.tokenIndicator jk r) :=
  (N.tokenIndicatorValue_measurable jk).comp (N.tokenAt_measurable r)

theorem tokenIndicator_iIndep
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    iIndepFun (N.tokenIndicator jk) N.tokenPathMeasure := by
  have h := N.tokenAt_iIndep.comp
    (fun _ : Nat => N.tokenIndicatorValue jk)
    (fun _ => N.tokenIndicatorValue_measurable jk)
  change
    iIndepFun
      (fun r omega => N.tokenIndicatorValue jk (N.tokenAt r omega))
      N.tokenPathMeasure
  exact h

theorem tokenIndicator_identDistrib
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (r : Nat) :
    IdentDistrib (N.tokenIndicator jk r) (N.tokenIndicator jk 0)
      N.tokenPathMeasure N.tokenPathMeasure := by
  have h := (N.tokenAt_identDistrib r 0).comp
    (N.tokenIndicatorValue_measurable jk)
  change
    IdentDistrib
      (fun omega => N.tokenIndicatorValue jk (N.tokenAt r omega))
      (fun omega => N.tokenIndicatorValue jk (N.tokenAt 0 omega))
      N.tokenPathMeasure N.tokenPathMeasure
  exact h

theorem tokenIndicator_integrable
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (r : Nat) :
    Integrable (N.tokenIndicator jk r) N.tokenPathMeasure := by
  apply Integrable.of_bound
    (N.tokenIndicator_measurable jk r).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun omega => by
    by_cases h : N.tokenAt r omega = jk
    <;> simp [tokenIndicator, tokenIndicatorValue, h])

theorem tokenIndicator_integral
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    integral N.tokenPathMeasure (N.tokenIndicator jk 0) =
      (N.tokenLaw jk).toReal := by
  have h0 := N.tokenAt_hasLaw 0
  have hmap := h0.integral_comp
    (N.tokenIndicatorValue_measurable jk).aestronglyMeasurable
  calc
    integral N.tokenPathMeasure (N.tokenIndicator jk 0) =
        integral N.tokenLaw.toMeasure (N.tokenIndicatorValue jk) := by
      change
        integral N.tokenPathMeasure
          (fun omega => N.tokenIndicatorValue jk (N.tokenAt 0 omega)) =
        integral N.tokenLaw.toMeasure (N.tokenIndicatorValue jk)
      exact hmap
    _ = (N.tokenLaw jk).toReal := by
      rw [PMF.integral_eq_sum]
      simp [tokenIndicatorValue]

/-- The fraction of the first `n` event epochs carrying token type `jk`.
At `n = 0`, Lean's real division convention gives value zero. -/
noncomputable def empiricalFrequency
    (jk : TokenType (Buffer := Buffer) (Server := Server))
    (n : Nat) (omega : N.TokenPath) : Real :=
  (Finset.range n).sum (fun r => N.tokenIndicator jk r omega) / (n : Real)

/-- Pointwise strong law for one marked-token type. -/
theorem empiricalFrequency_tendsto_ae
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    Filter.Eventually
      (fun omega =>
        Filter.Tendsto (fun n => N.empiricalFrequency jk n omega)
          Filter.atTop (nhds (N.tokenLaw jk).toReal))
      (ae N.tokenPathMeasure) := by
  have h := strong_law_ae_real
    (N.tokenIndicator jk)
    (N.tokenIndicator_integrable jk 0)
    (fun r s hrs => (N.tokenIndicator_iIndep jk).indepFun hrs)
    (N.tokenIndicator_identDistrib jk)
  simpa only [empiricalFrequency, N.tokenIndicator_integral jk] using h

/-- Source readback of the strong law: empirical type frequencies converge
almost surely to the corresponding `phi` entry. -/
theorem empiricalFrequency_tendsto_phi_ae
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    Filter.Eventually
      (fun omega =>
        Filter.Tendsto (fun n => N.empiricalFrequency jk n omega)
          Filter.atTop (nhds (N.phi jk.1 jk.2)))
      (ae N.tokenPathMeasure) := by
  simpa only [N.tokenLaw_toReal jk] using
    N.empiricalFrequency_tendsto_ae jk

/-- Simultaneous almost-sure empirical-frequency convergence for every marked
token type. Finiteness of the alphabet gives one common conull event. -/
theorem all_empiricalFrequencies_tendsto_phi_ae :
    Filter.Eventually
      (fun omega =>
        forall jk : TokenType (Buffer := Buffer) (Server := Server),
          Filter.Tendsto (fun n => N.empiricalFrequency jk n omega)
            Filter.atTop (nhds (N.phi jk.1 jk.2)))
      (ae N.tokenPathMeasure) := by
  apply MeasureTheory.ae_all_iff.mpr
  intro jk
  exact N.empiricalFrequency_tendsto_phi_ae jk

end Network

end StateDepMOR
