import StateDepMOR.Policy
import StateDepMOR.LargeDeviations
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Deterministic fluid model

Typed definitions for equations (13)--(20) of `StateDep_MOR.tex`.  The
policy correspondence is the paper's intersection of closed convex hulls.
-/

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

variable (N : Network Buffer Server)

/-- Raw real vector representing a probability distribution on service
actions. -/
abbrev ActionVector (Buffer : Type u) := Option Buffer → ℝ

/-- Membership in the probability simplex `Δ(𝓘_{j'})`.  Compatibility of
positive-mass buffer actions is imposed separately by the policy
correspondence. -/
def IsActionDistribution (p : ActionVector Buffer) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- Unit mass `q^a` on a service action. -/
def actionDirac (a : N.ServiceAction) : ActionVector Buffer :=
  fun b => if b = a then 1 else 0

omit [DecidableEq Server] in
@[simp]
theorem actionDirac_self (a : N.ServiceAction) : actionDirac N a a = 1 := by
  simp [actionDirac]

omit [DecidableEq Server] in
theorem actionDirac_isDistribution (a : N.ServiceAction) :
    IsActionDistribution (actionDirac N a) := by
  constructor
  · intro b
    simp only [actionDirac]
    split_ifs <;> norm_num
  · classical
    simp [actionDirac]

/-- Coordinatewise version of the `ℓ∞` neighborhood in equation
`eq:fluid-policy-correspondence`. -/
def IsNearNormalizedState {K : ℕ} (z : JobState Buffer K)
    (x : Buffer → ℝ) (ε : ℝ) : Prop :=
  ∀ i, |(z i : ℝ) / K - x i| < ε

/-- `𝒫^U_{j'k}(x)` from equation `eq:fluid-policy-correspondence`.

For positive `ε`, the real inequality `ε⁻¹ ≤ K` is equivalent to
`K ≥ ⌈ε⁻¹⌉`, and avoids an irrelevant coercion through `Nat.ceil`.
-/
noncomputable def fluidPolicyCorrespondence
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer → ℝ) : Set (ActionVector Buffer) :=
  ⋂ ε : {ε : ℝ // 0 < ε},
    closure (convexHull ℝ
      {q | ∃ K : ℕ+, ∃ z : JobState Buffer (K : ℕ),
        ε.1⁻¹ ≤ (K : ℝ) ∧
        IsNearNormalizedState z x ε.1 ∧
        q = actionDirac N (U K z j k)})

/-- A componentwise absolutely continuous, nondecreasing input path starting
at zero, as fixed in Definition `def:FSP`. -/
def IsFluidInput (T : ℝ) (A : MatrixPath Server Buffer) : Prop :=
  (∀ j k, AbsolutelyContinuousOnInterval (fun t => A t j k) 0 T) ∧
  (∀ j k, MonotoneOn (fun t => A t j k) (Set.Icc 0 T)) ∧
  (∀ j k, A 0 j k = 0)

/-- Queue-length paths at fluid scale. -/
abbrev FluidStatePath (Buffer : Type u) := ℝ → Buffer → ℝ

/-- Cumulative allocation paths.  Values at incompatible `(i,j)` pairs are
required to be zero in `FluidModelSolution`. -/
abbrev FluidAllocationPath (Buffer : Type u) (Server : Type v) :=
  ℝ → Buffer → Server → Buffer → ℝ

/-- Time-dependent action fractions `p_{j'k}(t)`. -/
abbrev FluidActionFractions (Buffer : Type u) (Server : Type v) :=
  ℝ → Server → Buffer → Option Buffer → ℝ

/-- A raw state vector belongs to the probability simplex `Ω`. -/
def IsFluidState (x : Buffer → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- Definition `def:FSP` (fluid-model solution).

The fields follow the source quantifiers: absolute continuity and initial
conditions, simplex-valued states, measurable action fractions, policy
correspondence and allocation equations almost everywhere, and exact queue
balance at every time in `[0,T]`.
-/
structure FluidModelSolution
    (U : N.DeterministicPolicySequence) (T : ℝ) (x0 : Simplex Buffer)
    (A : MatrixPath Server Buffer) where
  horizon_pos : 0 < T
  input_valid : IsFluidInput T A
  X : FluidStatePath Buffer
  E : FluidAllocationPath Buffer Server
  p : FluidActionFractions Buffer Server
  state_ac : ∀ i, AbsolutelyContinuousOnInterval (fun t => X t i) 0 T
  allocation_ac :
    ∀ i j k, AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T
  state_initial : ∀ i, X 0 i = x0 i
  allocation_initial : ∀ i j k, E 0 i j k = 0
  allocation_incompatible :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i j k, ¬N.compatible i j → E t i j k = 0
  state_in_simplex : ∀ t ∈ Set.Icc (0 : ℝ) T, IsFluidState (X t)
  fractions_measurable : ∀ j k a, Measurable (fun t => p t j k a)
  fractions_in_simplex :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j k, IsActionDistribution (p t j k)
  fractions_incompatible :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j k i,
      ¬N.compatible i j → p t j k (some i) = 0
  policy_rule :
    ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) T), ∀ j k,
      (fun a => p t j k a) ∈ fluidPolicyCorrespondence N U j k (X t)
  allocation_rule :
    ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) T), ∀ i j k,
      N.compatible i j →
        deriv (fun s => E s i j k) t =
          deriv (fun s => A s j k) t * p t j k (some i)
  balance :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ i,
      X t i = x0 i
        + (∑ j, ∑ l ∈ N.buffersOf j, E t l j i)
        - (∑ j ∈ N.serversOf i, ∑ k, E t i j k)

/-- The projection `(A,X)` called a fluid sample path (FSP) in
Definition `def:FSP`. -/
def IsFluidSamplePath
    (U : N.DeterministicPolicySequence) (T : ℝ) (x0 : Simplex Buffer)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer) : Prop :=
  ∃ s : FluidModelSolution N U T x0 A, s.X = X

/-- Definition "Fluid limits": the input is the nominal path `φ t`. -/
def FluidModelSolution.IsFluidLimit
    {U : N.DeterministicPolicySequence} {T : ℝ} {x0 : Simplex Buffer}
    {A : MatrixPath Server Buffer}
    (_s : FluidModelSolution N U T x0 A) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j k, A t j k = N.phi j k * t

/-- The set `𝒳_f` in equation `eq:fluid_control_polytope`.

This makes explicit the intended quantifier obscured by the TeX: for each
server `j`, `(d i j)_{i∈∂j}` is a probability distribution.
-/
def noWasteDriftSet (f : Server → Buffer → ℝ) : Set (Buffer → ℝ) :=
  {v | ∃ d : Buffer → Server → ℝ,
    (∀ i j, 0 ≤ d i j) ∧
    (∀ j, ∑ i ∈ N.buffersOf j, d i j = 1) ∧
    ∀ i, v i =
      (∑ j, f j i)
      - (∑ j ∈ N.serversOf i, d i j * ∑ k, f j k)}

/-- First, deterministic part of `lem:fms-existence`: existence for every
admissible prescribed input.  Kept as a proposition so its long analytical
proof is not silently introduced as an axiom. -/
def FluidModelExistenceStatement : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer),
    IsFluidInput T A → Nonempty (FluidModelSolution N U T x0 A)

end Network

end StateDepMOR
