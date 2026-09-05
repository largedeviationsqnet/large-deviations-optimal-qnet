import StateDepMOR.Network
import StateDepMOR.Policy
import StateDepMOR.LargeDeviations
import StateDepMOR.FluidModel
import StateDepMOR.FluidConsistency
import StateDepMOR.Lyapunov
import StateDepMOR.CutAnalysis
import StateDepMOR.MinInvariantPerformance
import StateDepMOR.StateIndependentChain
import StateDepMOR.PoissonProcessExecution

/-!
# Source-faithful paper statements

This file is a specification ledger for every active formal environment in
`StateDep_MOR.tex` and its active recursive input, `Appendices.tex`.  Deep
claims are definitions of propositions, rather than axioms.  In particular,
declaring one of the `...Statement` definitions does not assert that it is
true.
-/

open scoped BigOperators ENNReal Topology
open Filter MeasureTheory Set

namespace StateDepMOR
namespace PaperStatements

universe u v w

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-! ## Common definitions -/

@[simp]
theorem negativeLimsupLogRate_minimumInvariantLossFamily
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) :
    negativeLimsupLogRate (N.minimumInvariantLossFamily U) =
      N.minimumInvariantPerformance.throughputLossExponent U :=
  rfl

namespace Network

variable (N : Network Buffer Server)

/-- Componentwise nonnegative time-invariant service-token rates. -/
def IsNonnegativeRate (f : Server → Buffer → ℝ) : Prop :=
  ∀ j k, 0 ≤ f j k

/-- Net drain pressure across a server cut for a candidate rate matrix. -/
def cutGap (f : Server -> Buffer -> Real) (J : Finset Server) : Real :=
  (Finset.sum J (fun j => Finset.sum Finset.univ (fun k => f j k))) -
    Finset.sum Finset.univ (fun j =>
      Finset.sum (N.neighborhood J) (fun k => f j k))

/-- `v_alpha(f)`, using the explicit ambient extension of `L_alpha` required
because `alpha + Delta x` need not belong to the simplex. -/
noncomputable def vAlpha (α : Simplex Buffer)
    (f : Server → Buffer → ℝ) : ℝ :=
  sInf
    ((fun Δx =>
      Lyapunov.LAlphaAmbient (fun i => α i)
        ((fun i => α i) + Δx)) '' N.noWasteDriftSet f)

/-- Equation (22), the fixed-state converse exponent
`gamma_CB(alpha)`. -/
noncomputable def gammaCB (α : Simplex Buffer) : EReal :=
  sInf {q : EReal |
    ∃ f : Server → Buffer → ℝ,
      IsNonnegativeRate f ∧
      0 < vAlpha (N := N) α f ∧
      q = (N.localRate f : EReal) / (vAlpha (N := N) α f : EReal)}

/-- A rate matrix attains the infimum defining `gamma_CB(alpha)`. -/
def AttainsGammaCB (α : Simplex Buffer)
    (f : Server → Buffer → ℝ) : Prop :=
  IsNonnegativeRate f ∧
    0 < vAlpha (N := N) α f ∧
    (N.localRate f : EReal) / (vAlpha (N := N) α f : EReal) =
      gammaCB (N := N) α

/-- A full fluid solution is regular at `t` exactly when all paths named in
the paper's definition, including `L_alpha(X)`, are differentiable there.
The source defines regular points only for `t in (0,T)`. -/
def IsRegularPoint {U : N.DeterministicPolicySequence} {T : ℝ}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (α : Simplex Buffer) (s : N.FluidModelSolution U T x0 A)
    (t : ℝ) : Prop :=
  t ∈ Set.Ioo (0 : ℝ) T ∧
    (∀ j k, DifferentiableAt ℝ (fun r => A r j k) t) ∧
    (∀ i, DifferentiableAt ℝ (fun r => s.X r i) t) ∧
    (∀ i j k, DifferentiableAt ℝ (fun r => s.E r i j k) t) ∧
    DifferentiableAt ℝ
      (fun r =>
        Lyapunov.LAlphaAmbient (fun i => α i) (s.X r)) t

/-- `dot L_alpha(X(t))`. -/
noncomputable def lyapunovDrift (α : Simplex Buffer)
    (X : StateDepMOR.Network.FluidStatePath Buffer) (t : ℝ) : ℝ :=
  deriv
    (fun r => Lyapunov.LAlphaAmbient (fun i => α i) (X r)) t

/-- The ball `B(phi, epsilon)` in Proposition 4. -/
def RateNearPhi (f : Server → Buffer → ℝ) (ε : ℝ) : Prop :=
  IsNonnegativeRate f ∧ ∀ j k, |f j k - N.phi j k| < ε

/-- `S_1(X)`: buffers of minimum scaled queue length. -/
noncomputable def minimumScaledBuffers (alpha : Simplex Buffer)
    (x : Buffer -> Real) : Finset Buffer :=
  Finset.univ.filter fun i =>
    forall k, x i / alpha i <= x k / alpha k

theorem minimumScaledBuffers_nonempty
    (alpha : Simplex Buffer) (x : Buffer -> Real) :
    (minimumScaledBuffers alpha x).Nonempty := by
  classical
  obtain ⟨k, _, hk⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun i => x i / alpha i)
  refine ⟨k, ?_⟩
  simp only [minimumScaledBuffers, Finset.mem_filter, Finset.mem_univ,
    true_and]
  intro i
  rw [<- hk]
  exact Finset.inf'_le _ (Finset.mem_univ i)

/-- The forward directional derivative of `L_alpha` at `x` in direction
`drift`. Only buffers attaining the current minimum scaled state can control
this right derivative. -/
noncomputable def localRightDirectionalValue
    (alpha : Simplex Buffer) (x drift : Buffer -> Real) : Real :=
  -((minimumScaledBuffers alpha x).inf'
    (minimumScaledBuffers_nonempty alpha x)
    (fun i => drift i / alpha i))

/-- The repaired steepest-descent clause in Proposition 4.

The comparison is local and forward in time: every vector in
`noWasteDriftSet` is induced by a feasible scheduling distribution at the
current state and input rate. It does not require extending that one-time
choice to a two-sided regular fluid history. -/
noncomputable def SteepestDescentCondition
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence) : Prop :=
  forall (T : Real) (x0 : Simplex Buffer) (A : MatrixPath Server Buffer)
    (s : N.FluidModelSolution U T x0 A) (t : Real),
    IsRegularPoint N alpha s t ->
    Not (s.X t = (fun i => alpha i)) ->
    Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1 ->
    forall drift : Buffer -> Real,
      drift ∈ N.noWasteDriftSet (pathDerivative A t) ->
      lyapunovDrift alpha s.X t <=
        localRightDirectionalValue alpha (s.X t) drift

/-- The uniform near-nominal negative-drift clause in Proposition 4. -/
noncomputable def NegativeDriftCondition
    (α : Simplex Buffer) (U : N.DeterministicPolicySequence) : Prop :=
  ∃ η > 0, ∃ ε > 0,
    ∀ (T : ℝ) (x0 : Simplex Buffer) (A : MatrixPath Server Buffer)
      (s : N.FluidModelSolution U T x0 A) (t : ℝ),
      IsRegularPoint N α s t →
      RateNearPhi (N := N) (pathDerivative A t) ε →
      0 < Lyapunov.LAlphaAmbient (fun i => α i) (s.X t) →
      Lyapunov.LAlphaAmbient (fun i => α i) (s.X t) ≤ 1 →
      lyapunovDrift α s.X t ≤ -η

/-- Local positive-drift data used in `gamma_AB(alpha)`. -/
def IsGammaABDatum (U : N.DeterministicPolicySequence)
    (α : Simplex Buffer) (T : ℝ) (f : Server → Buffer → ℝ)
    (v : ℝ) : Prop :=
  0 < v ∧ ∃ (x0 : Simplex Buffer) (A : MatrixPath Server Buffer)
    (s : N.FluidModelSolution U T x0 A) (t : ℝ),
    IsRegularPoint N α s t ∧
    pathDerivative A t = f ∧
    Lyapunov.LAlphaAmbient (fun i => α i) (s.X t) < 1 ∧
    lyapunovDrift α s.X t = v

/-- The policy-specific achievability exponent `gamma_AB(alpha)` for the
fixed horizon appearing in Lemma `lem:lower_bound_vj`. -/
noncomputable def gammaAB (U : N.DeterministicPolicySequence)
    (α : Simplex Buffer) (T : ℝ) : EReal :=
  sInf {q : EReal | ∃ f : Server → Buffer → ℝ, ∃ v : ℝ,
    IsGammaABDatum N U α T f v ∧
    q = (N.localRate f : EReal) / (v : EReal)}

/-- Uniform return to `alpha` for every nominal fluid solution under `U`. -/
def UniformNominalFluidAttraction
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence) : Prop :=
  exists T0, 0 < T0 /\
    forall (T : Real) (x0 : Simplex Buffer)
      (A : MatrixPath Server Buffer)
      (s : N.FluidModelSolution U T x0 A),
      s.IsFluidLimit ->
      forall t, t ∈ Set.Icc T0 T ->
        s.X t = fun i => alpha i

end Network

/-! ## Assumptions and definitions -/

/-- Readback of Assumption `asm:connectivity`. -/
abbrev ConnectivityAssumption (N : Network Buffer Server) : Prop :=
  N.IsConnected

/-- Readback of Assumption `asm:non_trivial`. -/
abbrev LimitedFlexibilityAssumption (N : Network Buffer Server) : Prop :=
  N.HasLimitedFlexibility

/-- Readback of Assumption `asm:strict_hall`. -/
abbrev CompleteResourcePoolingAssumption (N : Network Buffer Server) : Prop :=
  N.HasCRP

/-- Readback of the SMW definition, including the highest-index tie break. -/
abbrev SMWDefinition (N : Network Buffer Server) [LinearOrder Buffer]
    (α : Simplex Buffer) (U : N.DeterministicPolicySequence) : Prop :=
  N.IsSMWPolicy α U

/-- Readback type for Definition `def:FSP`. -/
abbrev FluidModelSolutionDefinition (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (T : ℝ) (x0 : Simplex Buffer)
    (A : MatrixPath Server Buffer) :=
  N.FluidModelSolution U T x0 A

/-- Readback of Definition "Fluid limits". -/
abbrev FluidLimitDefinition (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : ℝ} {x0 : Simplex Buffer}
    {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A) : Prop :=
  s.IsFluidLimit

/-- Repaired readback of Definition `defn:lyap_func`: the algebraic formula
is defined on the ambient vector space, while its simplex restriction has
range `[0,1]`. -/
def LyapunovDefinitionStatement (α x : Simplex Buffer) : Prop :=
  α.IsInterior →
    (∀ y : Buffer → ℝ,
      Lyapunov.LAlphaAmbient (fun i => α i) y =
        1 - Finset.univ.inf' Finset.univ_nonempty (fun i => y i / α i)) ∧
    Lyapunov.LAlpha α x ∈ Set.Icc (0 : ℝ) 1

/-! ## Active remarks -/

/-- The calendar-time Euclidean distance at time `T`, maximized over all
initial states in `Omega_K`, from Remark `rem:SMW-converges-to-w`.  The
`sSup` is the exact finite-state maximum written without requiring an
auxiliary `Fintype` instance for `JobState`. -/
noncomputable def worstInitialSMWDistance
    [LinearOrder Buffer] (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (K : PNat) (T : Real)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) : Real :=
  sSup {d : Real | exists x0 : JobState Buffer (K : Nat),
    d = Real.sqrt
      (Finset.univ.sum fun i =>
        (N.calendarScaledQueueStateFrom
            (N.smwPolicy alpha halpha) K x0 omega T i - alpha i) ^ 2)}

/-- Proposition-valued readback of Remark `rem:SMW-converges-to-w`.

The quantifier order makes `T0(alpha)` independent of `K`, preserves the
maximum over every finite initial state, and places the `K`-limsup equality
inside the almost-sure modality of the independent calendar-time Poisson
clocks.
-/
noncomputable def SMWConvergesToWRemarkStatement
    [LinearOrder Buffer] (N : Network Buffer Server) : Prop :=
  N.IsConnected -> N.HasLimitedFlexibility -> N.HasCRP ->
    forall (alpha : Simplex Buffer) (halpha : alpha.IsInterior),
      exists T0, 0 < T0 /\
        forall T, T0 < T ->
          Filter.Eventually
            (fun omega =>
              limsup
                (fun K : PNat =>
                  worstInitialSMWDistance N alpha halpha K T omega)
                atTop = 0)
            (MeasureTheory.ae N.calendarPoissonMeasure)

/-! ## Fact and propositions -/

/-- `fact:sample_path_ldp`. `Path` is the cadlag matrix path space with its
Skorokhod `J1` topology, `mu` is the law of the scaled independent Poisson
paths, and `asMatrix` reads such a path as its matrix-valued trajectory. -/
def SamplePathLDPStatement
    (N : Network Buffer Server) (T : ℝ)
    (Path : Type w) [TopologicalSpace Path] [MeasurableSpace Path]
    [BorelSpace Path]
    (μ : ℕ → MeasureTheory.Measure Path)
    (asMatrix : Path → MatrixPath Server Buffer) : Prop :=
  0 < T ∧
    IsGoodLDP Path μ (fun A => poissonPathRate N T (asMatrix A))

/-- Proposition `prop:NT-is-necessary`, evaluated under the repaired
minimum-recurrent-class convention. -/
def AmpleFlexibilityNecessaryStatement
    (N : Network Buffer Server) : Prop :=
  N.IsConnected ->
    (forall j k, 0 < N.phi j k -> N.compatible k j) ->
    forall K : PNat, Fintype.card Server <= (K : Nat) ->
      exists U : N.DeterministicPolicySequence,
        N.minimumInvariantLossFamily U K = 0

/-- Proposition `prop:hall_is_necessary`, evaluated under the repaired
minimum-recurrent-class convention. -/
noncomputable def HallNecessaryStatement
    (N : Network Buffer Server) : Prop :=
  Not N.HasCRP ->
    forall U : N.DeterministicPolicySequence,
      N.minimumInvariantPerformance.throughputLossExponent U = 0

/-- Proposition `prop:tight_converse`. -/
noncomputable def TightConverseStatement
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence) : Prop :=
  alpha.IsInterior ->
    N.IsNonIdlingSequence U ->
    Network.SteepestDescentCondition (N := N) alpha U ->
    Network.NegativeDriftCondition (N := N) alpha U ->
    N.minimumInvariantPerformance.throughputLossExponent U =
      Network.gammaCB (N := N) alpha

/-! ## Lemmas -/

/-- Lemma `lem:fms-existence`, including deterministic existence,
subsequential consistency, and the almost-sure nominal Poisson input clause. -/
def FluidModelExistenceAndConsistencyStatement
    (N : Network Buffer Server) {Ω : Type w} [MeasurableSpace Ω]
    (ξ : N.ScaledStochasticExecution Ω) : Prop :=
  N.FluidModelExistenceAndConsistencyReadback ξ

/-- Lemma `lem:key_property_lyap`, preserving all printed hypotheses. -/
def KeyLyapunovPropertiesStatement : Prop :=
  (∀ (α : Simplex Buffer), α.IsInterior →
    ∀ (c : ℝ), 0 < c → ∀ Δx : Buffer → ℝ,
      (∑ i, Δx i) = 0 →
      Lyapunov.IsSimplexVector ((fun i => α i) + Δx) →
      Lyapunov.IsSimplexVector ((fun i => α i) + c • Δx) →
      Lyapunov.LAlphaAmbient (fun i => α i) ((fun i => α i) + c • Δx) =
        c * Lyapunov.LAlphaAmbient (fun i => α i) ((fun i => α i) + Δx)) ∧
  (∀ (α : Simplex Buffer), α.IsInterior →
    ∀ Δx Δx' : Buffer → ℝ,
      (∑ i, Δx i) = 0 → (∑ i, Δx' i) = 0 →
      Lyapunov.IsSimplexVector ((fun i => α i) + Δx + Δx') →
      Lyapunov.IsSimplexVector ((fun i => α i) + Δx) →
      Lyapunov.IsSimplexVector ((fun i => α i) + Δx') →
      Lyapunov.LAlphaAmbient (fun i => α i) ((fun i => α i) + Δx + Δx') ≤
        Lyapunov.LAlphaAmbient (fun i => α i) ((fun i => α i) + Δx) +
          Lyapunov.LAlphaAmbient (fun i => α i) ((fun i => α i) + Δx'))

namespace Network

variable (N : Network Buffer Server)

/-- `S_2(X,dot X)`: members of `S_1` with minimum scaled derivative. -/
noncomputable def minimumDerivativeBuffers (α : Simplex Buffer)
    (x xdot : Buffer → ℝ) : Finset Buffer :=
  (minimumScaledBuffers α x).filter fun i =>
    ∀ k ∈ minimumScaledBuffers α x, xdot i / α i ≤ xdot k / α k

/-- The displayed lower bound in Lemma `lem:lyapunov_derivative`. -/
noncomputable def steepestDescentLowerBound
    (α : Simplex Buffer) (A : MatrixPath Server Buffer)
    (X : StateDepMOR.Network.FluidStatePath Buffer) (t : ℝ) : ℝ :=
  let S₂ := minimumDerivativeBuffers α (X t)
    (fun i => deriv (fun r => X r i) t);
  -(1 / ∑ i ∈ S₂, α i) *
    ((∑ j, ∑ k ∈ S₂, deriv (fun r => A r j k) t) -
      (∑ j ∈ Finset.univ.filter (fun j => N.buffersOf j ⊆ S₂),
        ∑ k, deriv (fun r => A r j k) t))

/-- Lemma `lem:lyapunov_derivative`.

The repaired source uses the fluid-scaled input path `dot bar A` and the
open regular-time domain `(0,T)`.
-/
noncomputable def LyapunovDerivativeStatement [LinearOrder Buffer] : Prop :=
  ∀ (α : Simplex Buffer), α.IsInterior →
  ∀ (U : N.DeterministicPolicySequence), N.IsNonIdlingSequence U →
  ∀ (T : ℝ) (x0 : Simplex Buffer) (A : MatrixPath Server Buffer)
    (s : N.FluidModelSolution U T x0 A) (t : ℝ),
    t ∈ Set.Ioo (0 : ℝ) T →
    IsRegularPoint N α s t →
    s.X t ≠ (fun i => α i) →
    Lyapunov.LAlphaAmbient (fun i => α i) (s.X t) < 1 →
    let S₂ := minimumDerivativeBuffers α (s.X t)
      (fun i => deriv (fun r => s.X r i) t);
    (∀ k ∈ S₂,
      lyapunovDrift α s.X t =
        -deriv (fun r => s.X r k) t / α k) ∧
    steepestDescentLowerBound (N := N) α A s.X t ≤
      lyapunovDrift α s.X t ∧
    (N.IsSMWPolicy α U →
      lyapunovDrift α s.X t =
        steepestDescentLowerBound (N := N) α A s.X t)

/-- Lemma `lem:lyapunov_derivative_fluid`. -/
noncomputable def SMWNegativeDriftStatement [LinearOrder Buffer] : Prop :=
  N.IsConnected → N.HasLimitedFlexibility → N.HasCRP →
    ∀ (α : Simplex Buffer) (hα : α.IsInterior),
      NegativeDriftCondition (N := N) α (N.smwPolicy α hα)

/-- A cut attaining the minimum in the explicit exponent. -/
def IsMinimizingCut (α : Simplex Buffer) (J : Finset Server) : Prop :=
  N.IsLimitedSet J ∧
    ∀ J', N.IsLimitedSet J' →
      N.cutExponentTerm α J ≤ N.cutExponentTerm α J'

/-- The exponentially tilted rate matrix in repaired Lemma
`lem:explicit_gamma`. -/
noncomputable def tiltedRate (hatPhi : Server → Buffer → ℝ)
    (J : Finset Server) : Server → Buffer → ℝ :=
  fun j k =>
    if j ∈ J ∧ k ∉ N.neighborhood J then
      hatPhi j k * N.netArrivalRate J / N.netServiceRate J
    else if j ∉ J ∧ k ∈ N.neighborhood J then
      hatPhi j k * N.netServiceRate J / N.netArrivalRate J
    else
      hatPhi j k

/-- The exact exponent equality in `lem:explicit_gamma`. -/
noncomputable def ExplicitGammaEqualityStatement : Prop :=
  ∀ (α : Simplex Buffer), α.IsInterior →
    gammaCB (N := N) α = (N.explicitExponent α : EReal)

/-- Repaired optimizer clause, using the network primitive `phi`. -/
noncomputable def ExplicitGammaOptimizerStatement : Prop :=
  forall (alpha : Simplex Buffer), alpha.IsInterior ->
    (exists J, IsMinimizingCut (N := N) alpha J) /\
    forall J, IsMinimizingCut (N := N) alpha J ->
      AttainsGammaCB (N := N) alpha (tiltedRate (N := N) N.phi J)

/-- Repaired concrete readback of Remark `rem:critical-subset`.

The source repair retains the exact optimizer, drain, action, SMW
steepest-descent, and nominal-fluid attraction claims. It removes only the
undefined strategy-language predicates that were not mathematical
statements. -/
noncomputable def CriticalSubsetRemarkStatement [LinearOrder Buffer] : Prop :=
  N.HasLimitedFlexibility ->
  N.HasCRP ->
  forall (alpha : Simplex Buffer) (halpha : alpha.IsInterior),
    (exists J : Finset Server, IsMinimizingCut (N := N) alpha J) /\
    (forall J : Finset Server, IsMinimizingCut (N := N) alpha J ->
      let f := tiltedRate (N := N) N.phi J
      AttainsGammaCB (N := N) alpha f /\
      cutGap N f J =
        N.netArrivalRate J - N.netServiceRate J /\
      0 < N.netArrivalRate J - N.netServiceRate J /\
      N.localRate f =
        ENNReal.ofReal
          ((N.netArrivalRate J - N.netServiceRate J) *
            Real.log (N.netArrivalRate J / N.netServiceRate J)) /\
      gammaCB (N := N) alpha =
        (N.cutExponentTerm alpha J : EReal) /\
      forall T : Real, 0 < T ->
        poissonPathRate N T (linearMatrixPath f) =
          N.localRate f * ENNReal.ofReal T) /\
    N.IsNonIdlingSequence (N.smwPolicy alpha halpha) /\
    SteepestDescentCondition
      (N := N) alpha (N.smwPolicy alpha halpha) /\
    (N.IsConnected ->
      NegativeDriftCondition
        (N := N) alpha (N.smwPolicy alpha halpha) /\
      UniformNominalFluidAttraction
        (N := N) alpha (N.smwPolicy alpha halpha))

/-- Supremum of the fixed-state converse exponents over the relative
interior, used in `lem:point_wise_converse`. -/
noncomputable def gammaCBSup : EReal :=
  sSup {q : EReal | ∃ α : Simplex Buffer,
    α.IsInterior ∧ q = gammaCB (N := N) α}

end Network

/-- Lemma `lem:point_wise_converse`.

No network assumptions are added, although the printed appendix proof invokes
limited flexibility to construct a finite-cost draining direction.
-/
noncomputable def PointwiseConverseStatement
    (N : Network Buffer Server) : Prop :=
  forall U : N.DeterministicPolicySequence,
    negativeLiminfLogRate (N.minimumInvariantLossFamily U) <=
      Network.gammaCBSup (N := N)

/-- Lemma `lem:tech_lems`. -/
def TechnicalLyapunovLemmaStatement : Prop :=
  ∀ (α x y : Simplex Buffer), α.IsInterior →
    0 ≤ Lyapunov.LAlpha α x ∧
    (Lyapunov.LAlpha α x = 0 ↔ x = α) ∧
    |Lyapunov.LAlpha α x - Lyapunov.LAlpha α y| ≤
      (1 / Lyapunov.minCoordinate (fun i => α i)) *
        Lyapunov.maxCoordinateDistance (fun i => x i) (fun i => y i)

/-- Lemma `lem:lower_bound_vj`, preserving its `-limsup` achievability rate
for every fixed positive horizon. -/
noncomputable def AchievabilityBoundStatement
    (N : Network Buffer Server) : Prop :=
  forall (alpha : Simplex Buffer), alpha.IsInterior ->
  forall (U : N.DeterministicPolicySequence),
    N.IsNonIdlingSequence U ->
    Network.NegativeDriftCondition (N := N) alpha U ->
    forall T, T > 0 ->
      Network.gammaAB (N := N) U alpha T <=
        negativeLimsupLogRate (N.minimumInvariantLossFamily U)

/-- Lemma `lem:fluid_resting_point`, preserving its stronger `-liminf`
converse rate. -/
noncomputable def FluidRestingPointStatement
    (N : Network Buffer Server) : Prop :=
  forall (alpha : Simplex Buffer), alpha.IsInterior ->
  forall (U : N.DeterministicPolicySequence),
    Network.NegativeDriftCondition (N := N) alpha U ->
    negativeLiminfLogRate (N.minimumInvariantLossFamily U) <=
      Network.gammaCB (N := N) alpha

/-! ## Main theorem -/

/-- The supremum `bar gamma` over explicit SMW exponents. -/
noncomputable def smwExponentSup (N : Network Buffer Server) : EReal :=
  sSup {q : EReal | ∃ α : Simplex Buffer,
    α.IsInterior ∧ q = (N.explicitExponent α : EReal)}

/-- Theorem `thm:main_tight`.

The final conjunct records exactly the source's "arbitrarily close"
conclusion.  It does not assert that the supremum over the open relative
interior is attained, despite the theorem's informal title.
-/
noncomputable def MainTightStatement
    (N : Network Buffer Server) [LinearOrder Buffer] : Prop :=
  N.IsConnected -> N.HasLimitedFlexibility -> N.HasCRP ->
    (forall (alpha : Simplex Buffer) (halpha : alpha.IsInterior),
      N.minimumInvariantPerformance.throughputLossExponent
          (N.smwPolicy alpha halpha) =
        (N.explicitExponent alpha : EReal) /\
      0 < N.explicitExponent alpha) /\
    (forall U : N.DeterministicPolicySequence,
      N.minimumInvariantPerformance.throughputLossExponent U <=
        smwExponentSup N) /\
    (forall epsilon : Real, 0 < epsilon ->
      exists (alpha : Simplex Buffer) (halpha : alpha.IsInterior),
        smwExponentSup N <
          N.minimumInvariantPerformance.throughputLossExponent
              (N.smwPolicy alpha halpha) +
            (epsilon : EReal))

end PaperStatements
end StateDepMOR
