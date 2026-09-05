import StateDepMOR.FluidModel
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Existence and stochastic consistency of the fluid model

Exact proposition-valued readbacks of the three clauses of
`lem:fms-existence` in `StateDep_MOR.tex`.  This file does not assert those
analytical claims as axioms.  It supplies the smallest stochastic interface
needed to state them precisely.
-/

open Filter MeasureTheory Set

namespace StateDepMOR

universe u v w

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

/-- Uniform convergence on `[0,T]`, coordinate by coordinate over a finite
coordinate type.  The epsilon quantifiers make the topology in the paper
explicit rather than relying on a bundled path-space topology. -/
def UniformlyOnIcc {ι : Type*} (T : ℝ)
    (f : ℕ → ℝ → ι → ℝ) (g : ℝ → ι → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∃ r₀, ∀ r, r₀ ≤ r →
    ∀ t ∈ Icc (0 : ℝ) T, ∀ i, |f r t i - g t i| < ε

namespace Network

/-- Generic sample-wise scaled paths of a stochastic execution.

The interface intentionally records no stochastic dynamics: those belong to
the model-specific construction.  The primitive input is shared by all
policies, while state and allocation paths are explicitly indexed by the
policy that generates them. -/
structure ScaledStochasticExecution
    (N : Network Buffer Server) (Ω : Type w)
    [MeasurableSpace Ω] where
  probability : ProbabilityMeasure Ω
  input : ℕ+ → Ω → MatrixPath Server Buffer
  state :
    N.DeterministicPolicySequence → ℕ+ → Ω → FluidStatePath Buffer
  allocation :
    N.DeterministicPolicySequence → ℕ+ → Ω →
      FluidAllocationPath Buffer Server

variable {N : Network Buffer Server}

/-- Explicit uniform convergence of the policy-independent scaled input and
the state paths generated under `U`, along the strictly increasing job-count
subsequence `K`. -/
def ScaledStochasticExecution.PairConvergesOn
    {Ω : Type w} [MeasurableSpace Ω]
    (ξ : N.ScaledStochasticExecution Ω) (T : ℝ)
    (U : N.DeterministicPolicySequence)
    (K : ℕ → ℕ+) (ω : Ω)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer) : Prop :=
  UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) => ξ.input (K r) ω t jk.1 jk.2)
      (fun t (jk : Server × Buffer) => A t jk.1 jk.2) ∧
    UniformlyOnIcc T
      (fun r t i => ξ.state U (K r) ω t i)
      X

/-- Explicit uniform convergence of scaled allocations along a further
subsequence `r ↦ q r` of the original job-count subsequence. -/
def ScaledStochasticExecution.AllocationConvergesOn
    {Ω : Type w} [MeasurableSpace Ω]
    (ξ : N.ScaledStochasticExecution Ω) (T : ℝ)
    (U : N.DeterministicPolicySequence)
    (K : ℕ → ℕ+) (q : ℕ → ℕ) (ω : Ω)
    (E : FluidAllocationPath Buffer Server) : Prop :=
  UniformlyOnIcc T
    (fun r t (ijk : Buffer × Server × Buffer) =>
      ξ.allocation U (K (q r)) ω t ijk.1 ijk.2.1 ijk.2.2)
    (fun t (ijk : Buffer × Server × Buffer) =>
      E t ijk.1 ijk.2.1 ijk.2.2)

/-- The nominal input equation (21), on the full horizon `[0,T]`. -/
def IsNominalFluidInput (N : Network Buffer Server) (T : ℝ)
    (A : MatrixPath Server Buffer) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) T, ∀ j k, A t j k = N.phi j k * t

/-- First clause of `lem:fms-existence`: deterministic existence for every
prescribed positive horizon, initial simplex state, stationary policy, and
absolutely continuous componentwise nondecreasing input starting at zero.

The quantifier order follows the paper. -/
def DeterministicFluidModelExistenceReadback (N : Network Buffer Server) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer),
    IsFluidInput T A → Nonempty (FluidModelSolution N U T x0 A)

/-- Second clause of `lem:fms-existence`: any sample path whose scaled input
and state converge uniformly along a strictly increasing job-count
subsequence, with absolutely continuous limiting input and limiting initial
state `x0`, has a further allocation subsequence extending the pair to a
fluid-model solution.

Both `K` and `q` are explicitly `StrictMono`; `q` selects a further
subsequence from the already selected job counts `K`.  Since uniform
convergence includes `t = 0`, the premise `X 0 = x0` also states convergence
of the scaled initial states to `x0`. -/
def StochasticFluidExtensionReadback
    (N : Network Buffer Server) {Ω : Type w} [MeasurableSpace Ω]
    (ξ : N.ScaledStochasticExecution Ω) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (K : ℕ → ℕ+), StrictMono K →
    ∀ (ω : Ω) (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer),
      (∀ i, X 0 i = x0 i) →
      IsAbsolutelyContinuousMatrixPath T A →
      ξ.PairConvergesOn T U K ω A X →
      ∃ q : ℕ → ℕ, StrictMono q ∧
        ∃ s : FluidModelSolution N U T x0 A,
          s.X = X ∧ ξ.AllocationConvergesOn T U K q ω s.E

/-- Third clause of `lem:fms-existence`: for an execution built from the
paper's Poisson primitives, every uniformly convergent stochastic
subsequence has nominal input almost surely.

The proposition is deliberately phrased for possibly sample-dependent limit
paths `A` and `X`.  Thus "almost surely" applies after the universal choices
of horizon, job-count subsequence, and candidate random limits. -/
def PoissonSubsequentialInputReadback
    (N : Network Buffer Server) {Ω : Type w} [MeasurableSpace Ω]
    (ξ : N.ScaledStochasticExecution Ω) : Prop :=
  ∀ (T : ℝ), 0 < T →
    ∀ (U : N.DeterministicPolicySequence),
    ∀ (K : ℕ → ℕ+), StrictMono K →
    ∀ (A : Ω → MatrixPath Server Buffer)
      (X : Ω → FluidStatePath Buffer),
      ∀ᵐ ω ∂(ξ.probability : Measure Ω),
        ξ.PairConvergesOn T U K ω (A ω) (X ω) →
          N.IsNominalFluidInput T (A ω)

/-- Single proposition mirroring all three clauses of
`lem:fms-existence`.  It remains a specification, not an axiom or an
unproved theorem. -/
def FluidModelExistenceAndConsistencyReadback
    (N : Network Buffer Server) {Ω : Type w} [MeasurableSpace Ω]
    (ξ : N.ScaledStochasticExecution Ω) : Prop :=
  DeterministicFluidModelExistenceReadback N ∧
    StochasticFluidExtensionReadback N ξ ∧
    PoissonSubsequentialInputReadback N ξ

/-- Readback of the paragraph after the fluid-limit definition: almost
surely, every uniformly convergent stochastic subsequence with absolutely
continuous input and limiting initial state `x0` extends to a fluid-model
solution under the generating policy whose input is nominal.

This is one-way containment only; it does not claim that every deterministic
fluid limit is generated by a stochastic subsequence. -/
def EveryStochasticSubsequentialLimitIsFluidLimit
    (N : Network Buffer Server) {Ω : Type w} [MeasurableSpace Ω]
    (ξ : N.ScaledStochasticExecution Ω) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (K : ℕ → ℕ+), StrictMono K →
    ∀ (A : Ω → MatrixPath Server Buffer)
      (X : Ω → FluidStatePath Buffer),
      ∀ᵐ ω ∂(ξ.probability : Measure Ω),
        (∀ i, X ω 0 i = x0 i) →
        IsAbsolutelyContinuousMatrixPath T (A ω) →
        ξ.PairConvergesOn T U K ω (A ω) (X ω) →
          ∃ s : FluidModelSolution N U T x0 (A ω),
            s.X = X ω ∧ s.IsFluidLimit

end Network

end StateDepMOR
