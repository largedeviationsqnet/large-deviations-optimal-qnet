import StateDepMOR.ConverseProofs
import StateDepMOR.SMWSteepestDescentProofs
import StateDepMOR.AchievabilityStatement
import StateDepMOR.FluidRestingProof

/-!
# Deterministic bridge for the fixed-state converse

The repaired local forward-directional steepest-descent condition bounds
every positive `gammaAB` datum by the controller-independent value `vAlpha`.
This supplies the deterministic inequality `gammaCB <= gammaAB`; the
remaining direction is stochastic.
-/

open scoped ENNReal Topology
open Filter Set

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

theorem localRightDirectionalValue_le_centered
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (x drift : Buffer -> Real) :
    localRightDirectionalValue alpha x drift <=
      Lyapunov.LAlphaAmbient (fun i => alpha i)
        ((fun i => alpha i) + drift) := by
  rw [localRightDirectionalValue,
    Lyapunov.LAlphaAmbient_centered
      (fun i => alpha i) drift (fun i => ne_of_gt (halpha i))]
  apply neg_le_neg
  unfold Lyapunov.minCoordinate
  apply Finset.le_inf' (minimumScaledBuffers_nonempty alpha x)
  intro i hi
  exact Finset.inf'_le
    (fun q => drift q / alpha q) (Finset.mem_univ i)

private def fluidStateSimplex
    {N : StateDepMOR.Network Buffer Server}
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) : Simplex Buffer where
  val := s.X t
  nonneg := (s.state_in_simplex t ht).1
  sum_eq_one := (s.state_in_simplex t ht).2

private theorem positive_lyapunovDrift_state_ne_alpha
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence}
    {T : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (hpositive : 0 < lyapunovDrift alpha s.X t) :
    Not (s.X t = (fun i => alpha i)) := by
  intro hstate
  let g : Real -> Real :=
    fun r => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X r)
  have hgzero : g t = 0 := by
    dsimp [g]
    rw [hstate]
    have hcentered := Lyapunov.LAlphaAmbient_centered
      (fun i => alpha i) (0 : Buffer -> Real)
      (fun i => ne_of_gt (halpha i))
    simpa [Lyapunov.minCoordinate] using hcentered
  have hlocal : IsLocalMin g t := by
    filter_upwards
      [Icc_mem_nhds hregular.1.1 hregular.1.2] with r hr
    rw [hgzero]
    let xr : Simplex Buffer := fluidStateSimplex s r hr
    have hnonneg : 0 <= Lyapunov.LAlpha alpha xr :=
      Lyapunov.LAlpha_nonnegative alpha xr halpha
    simpa only [g, Lyapunov.LAlpha, xr, fluidStateSimplex] using hnonneg
  have hgderiv :
      HasDerivAt g (lyapunovDrift alpha s.X t) t :=
    hregular.2.2.2.2.hasDerivAt
  have hzero : lyapunovDrift alpha s.X t = 0 :=
    hlocal.hasDerivAt_eq_zero hgderiv
  exact (ne_of_gt hpositive) hzero

theorem isGammaABDatum_drift_le_vAlpha
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hsteep : SteepestDescentCondition (N := N) alpha U)
    {T : Real} {f : Server -> Buffer -> Real} {v : Real}
    (hdatum : IsGammaABDatum N U alpha T f v) :
    v <= vAlpha (N := N) alpha f := by
  rcases hdatum with
    ⟨hv, x0, A, s, t, hregular, hf, hL, hdrift⟩
  have hpositive : 0 < lyapunovDrift alpha s.X t := by
    rw [hdrift]
    exact hv
  have hstate : Not (s.X t = (fun i => alpha i)) :=
    positive_lyapunovDrift_state_ne_alpha
      N alpha halpha s t hregular hpositive
  have hlocal :=
    hsteep T x0 A s t hregular hstate hL
  rw [<- hdrift, <- hf]
  unfold vAlpha
  apply le_csInf
  · exact (noWasteDriftSet_nonempty
      N (pathDerivative A t)).image _
  · intro value hvalue
    obtain ⟨drift, hdriftSet, rfl⟩ := hvalue
    exact (hlocal drift hdriftSet).trans
      (localRightDirectionalValue_le_centered
        alpha halpha (s.X t) drift)

theorem isGammaABDatum_rate_nonnegative
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (T : Real) (f : Server -> Buffer -> Real) (v : Real)
    (hdatum : IsGammaABDatum N U alpha T f v) :
    IsNonnegativeRate f := by
  obtain ⟨_hv, x0, A, s, t, hregular, hf, _hL, _hdrift⟩ := hdatum
  rw [<- hf]
  intro j k
  unfold pathDerivative
  rw [<- derivWithin_of_mem_nhds
    (Icc_mem_nhds hregular.1.1 hregular.1.2)]
  exact (s.input_valid.2.1 j k).derivWithin_nonneg

private theorem gammaCB_le_candidateRatio
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer)
    (f : Server -> Buffer -> Real)
    (hf : IsNonnegativeRate f)
    (hvAlpha : 0 < vAlpha (N := N) alpha f) :
    gammaCB (N := N) alpha <=
      (N.localRate f : EReal) / (vAlpha (N := N) alpha f : EReal) := by
  unfold gammaCB
  apply sInf_le
  exact ⟨f, hf, hvAlpha, rfl⟩

private theorem candidateRatio_le_of_le
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    {v w : Real} (hv : 0 < v) (hvw : v <= w) :
    (N.localRate f : EReal) / (w : EReal) <=
      (N.localRate f : EReal) / (v : EReal) := by
  have hw : 0 < w := hv.trans_le hvw
  by_cases htop : N.localRate f = (Top.top : ENNReal)
  · rw [htop]
    simp only [EReal.coe_ennreal_top]
    rw [EReal.top_div_of_pos_ne_top
      (EReal.coe_pos.2 hw) (EReal.coe_ne_top _)]
    rw [EReal.top_div_of_pos_ne_top
      (EReal.coe_pos.2 hv) (EReal.coe_ne_top _)]
  · rw [<- EReal.coe_ennreal_toReal htop]
    rw [<- EReal.coe_div, <- EReal.coe_div, EReal.coe_le_coe_iff]
    exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg hv hvw

private theorem gammaCB_le_gammaABCandidate
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer)
    (f : Server -> Buffer -> Real) (v : Real)
    (hf : IsNonnegativeRate f)
    (hv : 0 < v)
    (hvvAlpha : v <= vAlpha (N := N) alpha f) :
    gammaCB (N := N) alpha <=
      (N.localRate f : EReal) / (v : EReal) := by
  have hvAlpha : 0 < vAlpha (N := N) alpha f :=
    hv.trans_le hvvAlpha
  exact (gammaCB_le_candidateRatio N alpha f hf hvAlpha).trans
    (candidateRatio_le_of_le N f hv hvvAlpha)

theorem gammaCB_le_gammaAB_of_steepestDescent
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hsteep : SteepestDescentCondition (N := N) alpha U)
    (T : Real) :
    gammaCB (N := N) alpha <= gammaAB (N := N) U alpha T := by
  unfold gammaAB
  apply le_sInf
  intro q hq
  obtain ⟨f, v, hdatum, rfl⟩ := hq
  exact gammaCB_le_gammaABCandidate N alpha f v
    (isGammaABDatum_rate_nonnegative N alpha U T f v hdatum)
    hdatum.1
    (isGammaABDatum_drift_le_vAlpha
      N alpha halpha U hsteep hdatum)

end StateDepMOR.PaperStatements.Network

namespace StateDepMOR.PaperStatements

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-- Deterministic assembly of Proposition 4 from its two stochastic component
lemmas. The unconditional export applies this theorem only after those
components have concrete proofs. -/
theorem tightConverseStatement_of_componentStatements
    (N : StateDepMOR.Network Buffer Server)
    (hachievability : AchievabilityBoundStatement N)
    (hresting : FluidRestingPointStatement N)
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence) :
    TightConverseStatement N alpha U := by
  intro halpha hnonidle hsteep hnegative
  have hach :=
    hachievability alpha halpha U hnonidle hnegative
  have hgammaAB :
      Network.gammaAB (N := N) U alpha 1 <=
        negativeLimsupLogRate (N.minimumInvariantLossFamily U) :=
    hach 1 zero_lt_one
  have hlower :
      Network.gammaCB (N := N) alpha <=
        negativeLimsupLogRate (N.minimumInvariantLossFamily U) :=
    (Network.gammaCB_le_gammaAB_of_steepestDescent
      N alpha halpha U hsteep 1).trans hgammaAB
  have hupper :
      negativeLimsupLogRate (N.minimumInvariantLossFamily U) <=
        Network.gammaCB (N := N) alpha :=
    (negativeLimsupLogRate_le_negativeLiminfLogRate
      (N.minimumInvariantLossFamily U)).trans
        (hresting alpha halpha U hnegative)
  rw [<- negativeLimsupLogRate_minimumInvariantLossFamily N U]
  exact le_antisymm hupper hlower

/-- The unconditional repaired Proposition 4, assembled from the concrete
achievability and fluid-resting theorems. -/
theorem tightConverseStatement
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence) :
    TightConverseStatement N alpha U :=
  tightConverseStatement_of_componentStatements
    N
    (Network.achievabilityBoundStatement_proved N)
    N.fluidRestingPointStatement
    alpha U

#print axioms tightConverseStatement

end StateDepMOR.PaperStatements
