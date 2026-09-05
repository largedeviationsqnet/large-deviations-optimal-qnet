import Mathlib

/-!
# Network primitives

Typed finite-network definitions corresponding to Sections 2--4 of
`StateDep_MOR.tex`.
-/

open scoped BigOperators

namespace StateDepMOR

universe u v

/-- The probability simplex on a finite type. -/
@[ext]
structure Simplex (ι : Type u) [Fintype ι] where
  val : ι → ℝ
  nonneg : ∀ i, 0 ≤ val i
  sum_eq_one : ∑ i, val i = 1

namespace Simplex

variable {ι : Type u} [Fintype ι]

instance : CoeFun (Simplex ι) fun _ => ι → ℝ :=
  ⟨Simplex.val⟩

/-- The paper's `relint(Ω)`: every coordinate is strictly positive. -/
def IsInterior (x : Simplex ι) : Prop :=
  ∀ i, 0 < x i

theorem eq_of_apply_eq {x y : Simplex ι} (h : ∀ i, x i = y i) : x = y := by
  ext i
  exact h i

/-- The uniform interior point of a nonempty finite simplex. -/
noncomputable def uniform [Nonempty ι] : Simplex ι where
  val _ := (Fintype.card ι : ℝ)⁻¹
  nonneg _ := by positivity
  sum_eq_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero :
        (Fintype.card ι : ℝ) ≠ 0)

theorem uniform_isInterior [Nonempty ι] : (uniform : Simplex ι).IsInterior := by
  intro i
  dsimp [uniform]
  positivity

end Simplex

/-- Compatibility graph and marked-Poisson service-token rates. -/
structure Network (Buffer : Type u) (Server : Type v)
    [Fintype Buffer] [Fintype Server] where
  compatible : Buffer → Server → Prop
  compatibleDecidable : DecidableRel compatible
  buffer_has_neighbor : ∀ i, ∃ j, compatible i j
  server_has_neighbor : ∀ j, ∃ i, compatible i j
  phi : Server → Buffer → ℝ
  phi_nonneg : ∀ j k, 0 ≤ phi j k
  server_rate_pos : ∀ j, 0 < ∑ k, phi j k
  total_rate : ∑ j, ∑ k, phi j k = 1

namespace Network

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

instance (N : Network Buffer Server) : DecidableRel N.compatible :=
  N.compatibleDecidable

/-- Buffers compatible with a server. This is `∂(j')` in the paper. -/
def buffersOf (N : Network Buffer Server) (j : Server) : Finset Buffer :=
  Finset.univ.filter fun i => N.compatible i j

/-- Servers compatible with a buffer. This is `∂(i)` in the paper. -/
def serversOf (N : Network Buffer Server) (i : Buffer) : Finset Server :=
  Finset.univ.filter fun j => N.compatible i j

/-- The buffer neighborhood `∂(J)` of a set of servers. -/
def neighborhood (N : Network Buffer Server) (J : Finset Server) : Finset Buffer :=
  Finset.univ.filter fun i => ∃ j ∈ J, N.compatible i j

omit [DecidableEq Buffer] [DecidableEq Server] in
@[simp]
theorem mem_buffersOf (N : Network Buffer Server) (i : Buffer) (j : Server) :
    i ∈ N.buffersOf j ↔ N.compatible i j := by
  simp [buffersOf]

omit [DecidableEq Buffer] [DecidableEq Server] in
@[simp]
theorem mem_serversOf (N : Network Buffer Server) (i : Buffer) (j : Server) :
    j ∈ N.serversOf i ↔ N.compatible i j := by
  simp [serversOf]

omit [DecidableEq Buffer] [DecidableEq Server] in
@[simp]
theorem mem_neighborhood (N : Network Buffer Server) (J : Finset Server) (i : Buffer) :
    i ∈ N.neighborhood J ↔ ∃ j ∈ J, N.compatible i j := by
  simp [neighborhood]

/-- A positive-rate service token can move a job from `src` to `dst`. -/
def TokenStep (N : Network Buffer Server) (src dst : Buffer) : Prop :=
  ∃ j, N.compatible src j ∧ 0 < N.phi j dst

/-- Assumption `asm:connectivity`.

`ReflTransGen` adds the trivial path when the endpoints agree; for distinct
endpoints this is exactly the finite positive-rate token sequence printed in
the paper.
-/
def IsConnected (N : Network Buffer Server) : Prop :=
  ∀ src dst, Relation.ReflTransGen N.TokenStep src dst

/-- Assumption `asm:non_trivial` (limited flexibility). -/
def HasLimitedFlexibility (N : Network Buffer Server) : Prop :=
  ∃ j k, ¬N.compatible k j ∧ 0 < N.phi j k

/-- `μ_J`, the net service rate out of `∂(J)`. -/
def netServiceRate (N : Network Buffer Server) (J : Finset Server) : ℝ :=
  ∑ j ∈ J, ∑ k ∈ Finset.univ.filter (fun k => k ∉ N.neighborhood J), N.phi j k

/-- `λ_J`, the optimistic net arrival rate into `∂(J)`. -/
def netArrivalRate (N : Network Buffer Server) (J : Finset Server) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => j ∉ J), ∑ k ∈ N.neighborhood J, N.phi j k

/-- A proper server cut with positive net service rate; this is membership in
the paper's family `𝒥`. -/
def IsLimitedSet (N : Network Buffer Server) (J : Finset Server) : Prop :=
  J ≠ Finset.univ ∧ 0 < N.netServiceRate J

/-- The finite family `𝒥`. -/
noncomputable def limitedSets (N : Network Buffer Server) : Finset (Finset Server) :=
  by
    classical
    exact Finset.univ.filter N.IsLimitedSet

omit [DecidableEq Server] in
@[simp]
theorem mem_limitedSets (N : Network Buffer Server) (J : Finset Server) :
    J ∈ N.limitedSets ↔ N.IsLimitedSet J := by
  classical
  simp [limitedSets]

/-- Assumption `asm:strict_hall` (complete resource pooling). -/
def HasCRP (N : Network Buffer Server) : Prop :=
  ∀ J, N.IsLimitedSet J → N.netServiceRate J < N.netArrivalRate J

/-- `B_J = 1_{∂(J)}ᵀ α`. -/
def cutMass (N : Network Buffer Server) (α : Simplex Buffer)
    (J : Finset Server) : ℝ :=
  ∑ i ∈ N.neighborhood J, α i

/-- The cut term in equation (8): `B_J log(λ_J / μ_J)`. -/
noncomputable def cutExponentTerm (N : Network Buffer Server) (α : Simplex Buffer)
    (J : Finset Server) : ℝ :=
  N.cutMass α J * Real.log (N.netArrivalRate J / N.netServiceRate J)

/-- The explicit fixed-state exponent from Theorem 1.

The source assumptions make `𝒥` nonempty. The fallback value makes this a
total Lean term even for primitives outside the paper's assumptions.
-/
noncomputable def explicitExponent (N : Network Buffer Server)
    (α : Simplex Buffer) : ℝ :=
  if h : N.limitedSets.Nonempty then
    N.limitedSets.inf' h (N.cutExponentTerm α)
  else
    0

/-- Exponents generated by interior SMW scaling vectors. -/
def interiorExponentSet (N : Network Buffer Server) : Set ℝ :=
  {r | ∃ α : Simplex Buffer, α.IsInterior ∧ r = N.explicitExponent α}

/-- `bar γ = sup_{α ∈ relint(Ω)} γ(α)` from Theorem 1. -/
noncomputable def bestSMWExponent (N : Network Buffer Server) : ℝ :=
  sSup N.interiorExponentSet

end Network

end StateDepMOR
