import StateDepMOR.Network
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Poisson sample-path large deviations

This module formalizes the local rate in equations (5)--(7) and expands the
meaning of a good LDP. Mathlib does not currently supply the paper's
finite-dimensional cadlag path space with its Skorokhod `J₁` topology, so the
LDP predicate is generic in a topological measurable path type.
-/

open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set

namespace StateDepMOR

universe u v w

/-- One-coordinate Poisson relative-entropy cost, including every convention
stated after equation `eq:kl_divergence`.

* negative candidate rates have infinite cost;
* if the nominal rate is zero, only candidate rate zero has finite cost;
* when `nominal > 0`, Lean's `0 * log 0 = 0` realizes the paper's convention.
-/
noncomputable def poissonCost (nominal candidate : ℝ) : ℝ≥0∞ :=
  if candidate < 0 then ⊤
  else if nominal = 0 then
    if candidate = 0 then 0 else ⊤
  else
    ENNReal.ofReal
      (candidate * Real.log (candidate / nominal) - candidate + nominal)

@[simp]
theorem poissonCost_of_candidate_neg {nominal candidate : ℝ} (h : candidate < 0) :
    poissonCost nominal candidate = ⊤ := by
  simp [poissonCost, h]

@[simp]
theorem poissonCost_zero_zero : poissonCost 0 0 = 0 := by
  simp [poissonCost]

@[simp]
theorem poissonCost_zero_of_pos {candidate : ℝ} (h : 0 < candidate) :
    poissonCost 0 candidate = ⊤ := by
  simp [poissonCost, not_lt_of_ge h.le, h.ne']

theorem poissonCost_of_nominal_pos {nominal candidate : ℝ}
    (hn : 0 < nominal) (hc : 0 ≤ candidate) :
    poissonCost nominal candidate =
      ENNReal.ofReal
        (candidate * Real.log (candidate / nominal) - candidate + nominal) := by
  simp [poissonCost, not_lt.mpr hc, hn.ne']

namespace Network

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]

/-- `Λ*(f)` from equation `eq:kl_divergence`. -/
noncomputable def localRate (N : Network Buffer Server)
    (f : Server → Buffer → ℝ) : ℝ≥0∞ :=
  ∑ j, ∑ k, poissonCost (N.phi j k) (f j k)

end Network

/-- Matrix-valued paths used by the rate function. -/
abbrev MatrixPath (Server : Type v) (Buffer : Type u) :=
  ℝ → Server → Buffer → ℝ

/-- Componentwise absolute continuity on `[0,T]`. -/
def IsAbsolutelyContinuousMatrixPath {Server : Type v} {Buffer : Type u}
    (T : ℝ) (A : MatrixPath Server Buffer) : Prop :=
  ∀ j k, AbsolutelyContinuousOnInterval (fun t => A t j k) 0 T

/-- The componentwise derivative of a matrix path. -/
noncomputable def pathDerivative {Server : Type v} {Buffer : Type u}
    (A : MatrixPath Server Buffer) (t : ℝ) : Server → Buffer → ℝ :=
  fun j k => deriv (fun s => A s j k) t

/-- `I_T(A)` in equation `eq:ld_rate`.

The Lebesgue integral is expressed as a nonnegative integral because the
Poisson cost is extended-nonnegative-valued.
-/
noncomputable def poissonPathRate
    {Buffer : Type u} {Server : Type v}
    [Fintype Buffer] [Fintype Server]
    (N : Network Buffer Server) (T : ℝ) (A : MatrixPath Server Buffer) : ℝ≥0∞ :=
  by
    classical
    exact
      if IsAbsolutelyContinuousMatrixPath T A ∧ (∀ j k, A 0 j k = 0) then
        ∫⁻ t in Set.Icc 0 T, N.localRate (pathDerivative A t)
      else
        ⊤

/-- A path with finite Poisson action is in the admissible path class and
starts at the zero matrix. -/
theorem poissonPathRate_ne_top_implies_valid
    {Buffer : Type u} {Server : Type v}
    [Fintype Buffer] [Fintype Server]
    (N : Network Buffer Server) (T : Real) (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A ≠ (⊤ : ENNReal)) :
    IsAbsolutelyContinuousMatrixPath T A /\
      forall j k, A 0 j k = 0 := by
  classical
  by_contra hvalid
  rw [poissonPathRate, if_neg hvalid] at hfinite
  exact hfinite rfl

/-- Every finite-cost path is componentwise continuous on its horizon. -/
theorem finiteCostPath_continuousOn
    {Buffer : Type u} {Server : Type v}
    [Fintype Buffer] [Fintype Server]
    (N : Network Buffer Server) {T : Real} (hT : 0 <= T)
    (A : MatrixPath Server Buffer)
    (hfinite : poissonPathRate N T A < (⊤ : ENNReal)) :
    forall j k, ContinuousOn (fun t => A t j k) (Set.Icc 0 T) := by
  intro j k
  have hac :=
    (poissonPathRate_ne_top_implies_valid N T A hfinite.ne).1 j k
  simpa only [Set.uIcc_of_le hT] using hac.continuousOn

/-- The constant-rate matrix path `A(t) = t f`. -/
def linearMatrixPath {Buffer : Type u} {Server : Type v}
    (f : Server -> Buffer -> Real) : MatrixPath Server Buffer :=
  fun t j k => t * f j k

theorem linearMatrixPath_absolutelyContinuous
    {Buffer : Type u} {Server : Type v}
    (f : Server -> Buffer -> Real) (T : Real) :
    IsAbsolutelyContinuousMatrixPath T (linearMatrixPath f) := by
  intro j k
  simpa [linearMatrixPath, smul_eq_mul, mul_comm] using
    (lipschitzWith_smul (f j k)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval (a := (0 : Real)) (b := T)

@[simp]
theorem pathDerivative_linearMatrixPath
    {Buffer : Type u} {Server : Type v}
    (f : Server -> Buffer -> Real) (t : Real) :
    pathDerivative (linearMatrixPath f) t = f := by
  funext j k
  exact (hasDerivAt_mul_const (x := t) (f j k)).deriv

/-- The action of a constant-rate path is its horizon times the local
Poisson rate. -/
theorem poissonPathRate_linearMatrixPath
    {Buffer : Type u} {Server : Type v}
    [Fintype Buffer] [Fintype Server]
    (N : Network Buffer Server) (T : Real)
    (f : Server -> Buffer -> Real) :
    poissonPathRate N T (linearMatrixPath f) =
      N.localRate f * ENNReal.ofReal T := by
  rw [poissonPathRate, if_pos]
  · simp_rw [pathDerivative_linearMatrixPath]
    rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
    simp
  · exact And.intro (linearMatrixPath_absolutelyContinuous f T)
      (by simp [linearMatrixPath])

/-- Infimum of a rate function over an event. The complete-lattice convention
gives `rateInf I ∅ = ∞`, as required in LDP bounds. -/
noncomputable def rateInf {Path : Type w} (I : Path → ℝ≥0∞) (event : Set Path) : ℝ≥0∞ :=
  sInf (I '' event)

/-- Scaled logarithmic mass with speed `K`, indexed by `K + 1` so that the
denominator is never zero. -/
noncomputable def scaledLogMass
    {Path : Type w} [MeasurableSpace Path]
    (μ : ℕ → Measure Path) (event : Set Path) (K : ℕ) : EReal :=
  ENNReal.log (μ (K + 1) event) / (K + 1 : ℕ)

/-- The inequalities and compact-level-set condition in
`fact:sample_path_ldp`.

Instantiating `Path` with cadlag matrix paths carrying the Skorokhod `J₁`
topology and `μ K` with the law of the scaled independent Poisson processes
gives exactly the paper's fact.
-/
def IsGoodLDP
    (Path : Type w) [TopologicalSpace Path] [MeasurableSpace Path] [BorelSpace Path]
    (μ : ℕ → Measure Path) (I : Path → ℝ≥0∞) : Prop :=
  (∀ c : ℝ, IsCompact {x | I x ≤ ENNReal.ofReal c}) ∧
    ∀ event : Set Path, MeasurableSet event →
      -(rateInf I (interior event) : EReal)
          ≤ liminf (scaledLogMass μ event) atTop ∧
      liminf (scaledLogMass μ event) atTop
          ≤ limsup (scaledLogMass μ event) atTop ∧
      limsup (scaledLogMass μ event) atTop
          ≤ -(rateInf I (closure event) : EReal)

end StateDepMOR
