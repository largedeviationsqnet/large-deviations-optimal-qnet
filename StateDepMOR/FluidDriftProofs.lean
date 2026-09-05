import StateDepMOR.PaperStatements
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Deterministic Lyapunov drift

This file isolates the part of Lemma `lem:lyapunov_derivative` that follows
from the current `FluidModelSolution` and `IsRegularPoint` definitions.

The derivative identity is unconditional.  The displayed drift bound and
its SMW equality reduce algebraically to an aggregate cut-flow relation.
The final theorem records the precise obstruction to obtaining that
pointwise relation directly from `FluidModelSolution.allocation_rule`: an
almost-everywhere derivative identity need not hold at a specified regular
time.
-/

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

private theorem minCoordinate_eq_of_forall_le
    (f : Buffer → ℝ) (k : Buffer)
    (hk : ∀ i, f k ≤ f i) :
    Lyapunov.minCoordinate f = f k := by
  apply le_antisymm
  · exact Finset.inf'_le f (Finset.mem_univ k)
  · unfold Lyapunov.minCoordinate
    apply Finset.le_inf' Finset.univ_nonempty
    intro i _
    exact hk i

private theorem lyapunov_difference_nonnegative
    (α : Simplex Buffer)
    (X : StateDepMOR.Network.FluidStatePath Buffer)
    (k : Buffer) (r : ℝ) :
    0 ≤ Lyapunov.LAlphaAmbient (fun i => α i) (X r) -
      (1 - X r k / α k) := by
  unfold Lyapunov.LAlphaAmbient
  have hmin :
      Lyapunov.minCoordinate (fun i => X r i / α i) ≤ X r k / α k :=
    Finset.inf'_le _ (Finset.mem_univ k)
  change
    0 ≤ (1 - Lyapunov.minCoordinate (fun i => X r i / α i)) -
      (1 - X r k / α k)
  linarith

/-- The first displayed identity in Lemma `lem:lyapunov_derivative`.

This is slightly stronger than the paper-facing statement: neither
`X(t) ≠ α` nor `Lα(X(t)) < 1` is needed.  The proof observes that
`Lα(X(r)) - (1 - X_k(r) / α_k)` has a global minimum of zero at every
currently minimum scaled buffer `k`, and applies Fermat's theorem.
-/
theorem lyapunovDrift_eq_neg_deriv_div_of_mem_minimumScaledBuffers
    (N : Network Buffer Server)
    (α : Simplex Buffer) (hα : α.IsInterior)
    {U : N.DeterministicPolicySequence} {T : ℝ}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A) (t : ℝ)
    (hregular : IsRegularPoint N α s t)
    (k : Buffer) (hk : k ∈ minimumScaledBuffers α (s.X t)) :
    lyapunovDrift α s.X t =
      -deriv (fun r => s.X r k) t / α k := by
  classical
  have hαk : α k ≠ 0 := ne_of_gt (hα k)
  have hkmin : ∀ i, s.X t k / α k ≤ s.X t i / α i := by
    simpa [minimumScaledBuffers] using (Finset.mem_filter.1 hk).2
  have hvalue :
      Lyapunov.LAlphaAmbient (fun i => α i) (s.X t) -
          (1 - s.X t k / α k) = 0 := by
    unfold Lyapunov.LAlphaAmbient
    rw [minCoordinate_eq_of_forall_le _ k hkmin]
    ring
  let gap : ℝ → ℝ := fun r =>
    Lyapunov.LAlphaAmbient (fun i => α i) (s.X r) -
      (1 - s.X r k / α k)
  have hlocal : IsLocalMin gap t := by
    show ∀ᶠ r in nhds t, gap t ≤ gap r
    apply Filter.Eventually.of_forall
    intro r
    change
      Lyapunov.LAlphaAmbient (fun i => α i) (s.X t) -
          (1 - s.X t k / α k) ≤
        Lyapunov.LAlphaAmbient (fun i => α i) (s.X r) -
          (1 - s.X r k / α k)
    rw [hvalue]
    exact lyapunov_difference_nonnegative α s.X k r
  have hL :
      HasDerivAt
        (fun r => Lyapunov.LAlphaAmbient (fun i => α i) (s.X r))
        (lyapunovDrift α s.X t) t := by
    exact hregular.2.2.2.2.hasDerivAt
  have hX :
      HasDerivAt (fun r => s.X r k) (deriv (fun r => s.X r k) t) t :=
    (hregular.2.2.1 k).hasDerivAt
  have hgap' :
      HasDerivAt
        (fun r =>
          Lyapunov.LAlphaAmbient (fun i => α i) (s.X r) -
            (1 - s.X r k / α k))
        (lyapunovDrift α s.X t -
          (0 - deriv (fun r => s.X r k) t / α k)) t := by
    exact hL.sub
      ((hasDerivAt_const t (1 : ℝ)).sub (hX.div_const (α k)))
  have hgap : HasDerivAt gap
      (lyapunovDrift α s.X t -
        (0 - deriv (fun r => s.X r k) t / α k)) t := by
    simpa only [gap] using hgap'
  have hzero := hlocal.hasDerivAt_eq_zero hgap
  field_simp [hαk] at hzero ⊢
  linarith

/-- Exact first conjunct of `LyapunovDerivativeStatement`. -/
theorem lyapunovDerivative_first_clause
    (N : Network Buffer Server)
    (α : Simplex Buffer) (hα : α.IsInterior)
    {U : N.DeterministicPolicySequence} {T : ℝ}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A) (t : ℝ)
    (hregular : IsRegularPoint N α s t) :
    let S₂ := minimumDerivativeBuffers α (s.X t)
      (fun i => deriv (fun r => s.X r i) t)
    ∀ k ∈ S₂,
      lyapunovDrift α s.X t =
        -deriv (fun r => s.X r k) t / α k := by
  classical
  dsimp
  intro k hk
  apply lyapunovDrift_eq_neg_deriv_div_of_mem_minimumScaledBuffers
    N α hα s t hregular k
  exact (Finset.mem_filter.1 hk).1

private theorem minimumDerivativeBuffers_nonempty
    (α : Simplex Buffer) (x xdot : Buffer → ℝ) :
    (minimumDerivativeBuffers α x xdot).Nonempty := by
  classical
  have hscaled : (minimumScaledBuffers α x).Nonempty := by
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf'
      Finset.univ_nonempty (fun i => x i / α i)
    refine ⟨k, ?_⟩
    simp only [minimumScaledBuffers, Finset.mem_filter, Finset.mem_univ,
      true_and]
    intro i
    rw [← hk]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨k, hkS, hk⟩ := Finset.exists_mem_eq_inf'
    hscaled (fun i => xdot i / α i)
  refine ⟨k, ?_⟩
  simp only [minimumDerivativeBuffers, Finset.mem_filter]
  refine ⟨hkS, ?_⟩
  intro i hi
  rw [← hk]
  exact Finset.inf'_le _ hi

private theorem sum_alpha_minimumDerivativeBuffers_pos
    (α : Simplex Buffer) (hα : α.IsInterior)
    (x xdot : Buffer → ℝ) :
    0 < ∑ i ∈ minimumDerivativeBuffers α x xdot, α i := by
  classical
  exact Finset.sum_pos
    (fun i _ => hα i)
    (minimumDerivativeBuffers_nonempty α x xdot)

/-- Algebraic core of the lower-bound clause.

The remaining analytic/model-specific obligation is exactly `hflow`: the
aggregate derivative of the queues in `S₂` is at most the cut inflow minus
the forced cut outflow.
-/
theorem steepestDescentLowerBound_le_of_cutFlow
    (N : Network Buffer Server)
    (α : Simplex Buffer) (hα : α.IsInterior)
    {U : N.DeterministicPolicySequence} {T : ℝ}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A) (t : ℝ)
    (hregular : IsRegularPoint N α s t)
    (hflow :
      let S₂ := minimumDerivativeBuffers α (s.X t)
        (fun i => deriv (fun r => s.X r i) t)
      ∑ i ∈ S₂, deriv (fun r => s.X r i) t ≤
        (∑ j, ∑ k ∈ S₂, deriv (fun r => A r j k) t) -
          (∑ j ∈ Finset.univ.filter (fun j => N.buffersOf j ⊆ S₂),
            ∑ k, deriv (fun r => A r j k) t)) :
    steepestDescentLowerBound (N := N) α A s.X t ≤
      lyapunovDrift α s.X t := by
  classical
  let S₂ := minimumDerivativeBuffers α (s.X t)
    (fun i => deriv (fun r => s.X r i) t)
  let D :=
    (∑ j, ∑ k ∈ S₂, deriv (fun r => A r j k) t) -
      (∑ j ∈ Finset.univ.filter (fun j => N.buffersOf j ⊆ S₂),
        ∑ k, deriv (fun r => A r j k) t)
  have hsumpos : 0 < ∑ i ∈ S₂, α i :=
    sum_alpha_minimumDerivativeBuffers_pos α hα _ _
  obtain ⟨k, hk⟩ := minimumDerivativeBuffers_nonempty α (s.X t)
    (fun i => deriv (fun r => s.X r i) t)
  have hkdrift := lyapunovDerivative_first_clause N α hα s t hregular k hk
  have hsame :
      ∀ i ∈ S₂,
        deriv (fun r => s.X r i) t / α i =
          deriv (fun r => s.X r k) t / α k := by
    intro i hi
    have hiDrift := lyapunovDerivative_first_clause N α hα s t hregular i hi
    apply neg_injective
    simpa only [neg_div] using hiDrift.symm.trans hkdrift
  have hsum :
      ∑ i ∈ S₂, deriv (fun r => s.X r i) t =
        (∑ i ∈ S₂, α i) *
          (deriv (fun r => s.X r k) t / α k) := by
    calc
      ∑ i ∈ S₂, deriv (fun r => s.X r i) t =
          ∑ i ∈ S₂, α i *
            (deriv (fun r => s.X r k) t / α k) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [← hsame i hi]
              field_simp [ne_of_gt (hα i)]
      _ = (∑ i ∈ S₂, α i) *
          (deriv (fun r => s.X r k) t / α k) := by
            rw [Finset.sum_mul]
  change (∑ i ∈ S₂, deriv (fun r => s.X r i) t) ≤ D at hflow
  change -(1 / ∑ i ∈ S₂, α i) * D ≤ lyapunovDrift α s.X t
  rw [hsum] at hflow
  rw [hkdrift]
  have hdiv :
      deriv (fun r => s.X r k) t / α k ≤
        D / (∑ i ∈ S₂, α i) := by
    exact (le_div_iff₀ hsumpos).2 (by simpa [mul_comm] using hflow)
  simpa [div_eq_mul_inv, mul_comm] using neg_le_neg hdiv

/-- Algebraic core of the SMW equality clause.  It requires equality in the
same aggregate cut-flow relation isolated above. -/
theorem lyapunovDrift_eq_steepestDescentLowerBound_of_cutFlowEq
    (N : Network Buffer Server)
    (α : Simplex Buffer) (hα : α.IsInterior)
    {U : N.DeterministicPolicySequence} {T : ℝ}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A) (t : ℝ)
    (hregular : IsRegularPoint N α s t)
    (hflow :
      let S₂ := minimumDerivativeBuffers α (s.X t)
        (fun i => deriv (fun r => s.X r i) t)
      ∑ i ∈ S₂, deriv (fun r => s.X r i) t =
        (∑ j, ∑ k ∈ S₂, deriv (fun r => A r j k) t) -
          (∑ j ∈ Finset.univ.filter (fun j => N.buffersOf j ⊆ S₂),
            ∑ k, deriv (fun r => A r j k) t)) :
    lyapunovDrift α s.X t =
      steepestDescentLowerBound (N := N) α A s.X t := by
  classical
  apply le_antisymm
  · let S₂ := minimumDerivativeBuffers α (s.X t)
      (fun i => deriv (fun r => s.X r i) t)
    let D :=
      (∑ j, ∑ k ∈ S₂, deriv (fun r => A r j k) t) -
        (∑ j ∈ Finset.univ.filter (fun j => N.buffersOf j ⊆ S₂),
          ∑ k, deriv (fun r => A r j k) t)
    have hsumpos : 0 < ∑ i ∈ S₂, α i :=
      sum_alpha_minimumDerivativeBuffers_pos α hα _ _
    obtain ⟨k, hk⟩ := minimumDerivativeBuffers_nonempty α (s.X t)
      (fun i => deriv (fun r => s.X r i) t)
    have hkdrift := lyapunovDerivative_first_clause N α hα s t hregular k hk
    have hsame :
        ∀ i ∈ S₂,
          deriv (fun r => s.X r i) t / α i =
            deriv (fun r => s.X r k) t / α k := by
      intro i hi
      have hiDrift := lyapunovDerivative_first_clause N α hα s t hregular i hi
      apply neg_injective
      simpa only [neg_div] using hiDrift.symm.trans hkdrift
    have hsum :
        ∑ i ∈ S₂, deriv (fun r => s.X r i) t =
          (∑ i ∈ S₂, α i) *
            (deriv (fun r => s.X r k) t / α k) := by
      calc
        ∑ i ∈ S₂, deriv (fun r => s.X r i) t =
            ∑ i ∈ S₂, α i *
              (deriv (fun r => s.X r k) t / α k) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [← hsame i hi]
                field_simp [ne_of_gt (hα i)]
        _ = (∑ i ∈ S₂, α i) *
            (deriv (fun r => s.X r k) t / α k) := by
              rw [Finset.sum_mul]
    change (∑ i ∈ S₂, deriv (fun r => s.X r i) t) = D at hflow
    change lyapunovDrift α s.X t ≤ -(1 / ∑ i ∈ S₂, α i) * D
    rw [hkdrift, ← hflow, hsum]
    field_simp [ne_of_gt hsumpos]
    exact le_rfl
  · exact steepestDescentLowerBound_le_of_cutFlow
      N α hα s t hregular hflow.le

/-- A compiled counterexample to pointwise specialization of the
almost-everywhere allocation equation.

Both paths are differentiable at `t = 1/2`, and the allocation-shaped
derivative equation holds almost everywhere on `[0,1]`, but it fails at
that regular time because the measurable action fraction may be changed on
a null singleton.  Thus `FluidModelSolution.allocation_rule` and
`IsRegularPoint` alone do not expose the pointwise equation used by the
paper's proof.
-/
theorem ae_allocation_rule_not_pointwise :
    let A : ℝ → ℝ := fun r => r
    let E : ℝ → ℝ := fun _ => 0
    let p : ℝ → ℝ := fun r => if r = (2 : ℝ)⁻¹ then 1 else 0
    (∀ᵐ r ∂volume.restrict (Set.Icc (0 : ℝ) 1),
      deriv E r = deriv A r * p r) ∧
    DifferentiableAt ℝ A (2 : ℝ)⁻¹ ∧
    DifferentiableAt ℝ E (2 : ℝ)⁻¹ ∧
    deriv E (2 : ℝ)⁻¹ ≠
      deriv A (2 : ℝ)⁻¹ * p (2 : ℝ)⁻¹ := by
  dsimp
  constructor
  · apply ae_restrict_of_ae
    filter_upwards [volume.ae_ne (2 : ℝ)⁻¹] with r hr
    simp [hr]
  constructor
  · fun_prop
  constructor
  · fun_prop
  · norm_num

end StateDepMOR.PaperStatements.Network
