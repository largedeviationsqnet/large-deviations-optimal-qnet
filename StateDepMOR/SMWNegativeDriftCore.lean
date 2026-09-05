import StateDepMOR.FluidAllocationBounds
import StateDepMOR.NegativeDrift

/-!
# Finite-cut core of SMW negative drift

This module proves the algebraic step from the SMW cut-flow equality to the
uniform negative-drift bound.  The separate analytic task is to establish that
equality from the fluid policy correspondence.
-/

open scoped BigOperators
open Set

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

theorem buffer_nontrivial_of_limited
    (N : Network Buffer Server) (hflex : N.HasLimitedFlexibility) :
    Nontrivial Buffer := by
  obtain ⟨j, k, hkj, _⟩ := hflex
  obtain ⟨i, hij⟩ := N.server_has_neighbor j
  exact nontrivial_of_ne k i (fun hki => hkj (hki ▸ hij))

theorem minimumDerivativeBuffers_nonempty
    (alpha : Simplex Buffer) (x xdot : Buffer -> Real) :
    (minimumDerivativeBuffers alpha x xdot).Nonempty := by
  classical
  have hscaled : (minimumScaledBuffers alpha x).Nonempty := by
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf'
      Finset.univ_nonempty (fun i => x i / alpha i)
    refine ⟨k, ?_⟩
    simp only [minimumScaledBuffers, Finset.mem_filter, Finset.mem_univ,
      true_and]
    intro i
    rw [← hk]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨k, hkS, hk⟩ := Finset.exists_mem_eq_inf'
    hscaled (fun i => xdot i / alpha i)
  refine ⟨k, ?_⟩
  simp only [minimumDerivativeBuffers, Finset.mem_filter]
  refine ⟨hkS, ?_⟩
  intro i hi
  rw [← hk]
  exact Finset.inf'_le _ hi

theorem minimumDerivativeBuffers_ne_univ_of_LAlpha_pos
    (alpha x : Simplex Buffer) (hAlpha : alpha.IsInterior)
    (xdot : Buffer -> Real) (hL : 0 < Lyapunov.LAlpha alpha x) :
    Not (minimumDerivativeBuffers alpha (fun i => x i) xdot = Finset.univ) := by
  classical
  intro hS
  have hall :
      forall i k, x i / alpha i <= x k / alpha k := by
    intro i k
    have hiS :
        i ∈ minimumDerivativeBuffers alpha (fun q => x q) xdot := by
      rw [hS]
      simp
    have hiMin :
        i ∈ minimumScaledBuffers alpha (fun q => x q) :=
      (Finset.mem_filter.1 hiS).1
    exact (Finset.mem_filter.1 hiMin).2 k
  have hratio :
      forall i k, x i / alpha i = x k / alpha k := by
    intro i k
    exact le_antisymm (hall i k) (hall k i)
  let i0 : Buffer := Classical.choice (inferInstance : Nonempty Buffer)
  let c : Real := x i0 / alpha i0
  have hx : forall i, x i = c * alpha i := by
    intro i
    apply (div_eq_iff (ne_of_gt (hAlpha i))).1
    exact hratio i i0
  have hc : c = 1 := by
    have hsum :
        (1 : Real) = c * 1 := by
      calc
        (1 : Real) = Finset.univ.sum (fun i => x i) := x.sum_eq_one.symm
        _ = Finset.univ.sum (fun i => c * alpha i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hx i
        _ = c * Finset.univ.sum (fun i => alpha i) := by
          rw [Finset.mul_sum]
        _ = c * 1 := by rw [alpha.sum_eq_one]
    linarith
  have hxa : x = alpha := by
    apply Simplex.eq_of_apply_eq
    intro i
    rw [hx i, hc, one_mul]
  have hzero := (Lyapunov.LAlpha_eq_zero_iff alpha x hAlpha).2 hxa
  linarith

theorem sum_alpha_minimumDerivativeBuffers_le_one
    (alpha : Simplex Buffer) (x xdot : Buffer -> Real) :
    (∑ i ∈ minimumDerivativeBuffers alpha x xdot, alpha i) <= 1 := by
  calc
    (∑ i ∈ minimumDerivativeBuffers alpha x xdot, alpha i) <=
        ∑ i, alpha i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp
      · intro i hi hnot
        exact alpha.nonneg i
    _ = 1 := alpha.sum_eq_one

theorem steepestDescentLowerBound_eq_neg_cutDrift
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (A : MatrixPath Server Buffer)
    (X : StateDepMOR.Network.FluidStatePath Buffer) (t : Real) :
    let S := minimumDerivativeBuffers alpha (X t)
      (fun i => deriv (fun r => X r i) t)
    steepestDescentLowerBound (N := N) alpha A X t =
      -(1 / ∑ i ∈ S, alpha i) * N.cutDrift S (pathDerivative A t) := by
  rfl

/-- Once the SMW cut-flow equality is known, the finite Hall gap yields the
uniform negative-drift estimate, including when `LAlpha = 1`. -/
theorem lyapunovDrift_le_neg_half_gap_of_eq_steepest
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (hAlpha : alpha.IsInterior)
    (g0 epsilon : Real) (hg0 : 0 < g0)
    (hgap :
      forall (f : Server -> Buffer -> Real),
        (forall j k, |f j k - N.phi j k| < epsilon) ->
        forall S : Finset Buffer, S.Nonempty ->
          Not (S = Finset.univ) -> g0 / 2 <= N.cutDrift S f)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (hL : 0 < Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t))
    (heq :
      lyapunovDrift alpha s.X t =
        steepestDescentLowerBound (N := N) alpha A s.X t)
    (hf :
      forall j k,
        |pathDerivative A t j k - N.phi j k| < epsilon) :
    lyapunovDrift alpha s.X t <=
      -(g0 / 2) := by
  classical
  let S := minimumDerivativeBuffers alpha (s.X t)
    (fun i => deriv (fun r => s.X r i) t)
  have htIcc : t ∈ Set.Icc (0 : Real) T :=
    ⟨hregular.1.1.le, hregular.1.2.le⟩
  let xt : Simplex Buffer :=
    { val := s.X t
      nonneg := (s.state_in_simplex t htIcc).1
      sum_eq_one := (s.state_in_simplex t htIcc).2 }
  have hSnonempty : S.Nonempty :=
    minimumDerivativeBuffers_nonempty alpha (s.X t)
      (fun i => deriv (fun r => s.X r i) t)
  have hSproper : Not (S = Finset.univ) := by
    apply minimumDerivativeBuffers_ne_univ_of_LAlpha_pos
      alpha xt hAlpha (fun i => deriv (fun r => s.X r i) t)
    exact hL
  have hsumpos : 0 < ∑ i ∈ S, alpha i :=
    Finset.sum_pos (fun i _ => hAlpha i) hSnonempty
  have hsumle : (∑ i ∈ S, alpha i) <= 1 :=
    sum_alpha_minimumDerivativeBuffers_le_one alpha (s.X t)
      (fun i => deriv (fun r => s.X r i) t)
  have hcut :
      g0 / 2 <= N.cutDrift S (pathDerivative A t) := by
    exact hgap (pathDerivative A t) hf S hSnonempty hSproper
  have hcutNonneg : 0 <= N.cutDrift S (pathDerivative A t) := by
    have : 0 < g0 / 2 := half_pos hg0
    linarith
  have hinv : 1 <= 1 / (∑ i ∈ S, alpha i) := by
    exact (one_le_div₀ hsumpos).2 hsumle
  have hscale :
      N.cutDrift S (pathDerivative A t) <=
        (1 / ∑ i ∈ S, alpha i) *
          N.cutDrift S (pathDerivative A t) := by
    simpa using mul_le_mul_of_nonneg_right hinv hcutNonneg
  rw [heq, steepestDescentLowerBound_eq_neg_cutDrift]
  have htotal :
      g0 / 2 <=
        (1 / ∑ i ∈ S, alpha i) *
          N.cutDrift S (pathDerivative A t) :=
    hcut.trans hscale
  linarith

end StateDepMOR.PaperStatements.Network
