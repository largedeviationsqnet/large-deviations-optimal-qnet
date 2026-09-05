import StateDepMOR.FluidSMWProofs
import StateDepMOR.SMWNegativeDriftCore

/-!
# SMW steepest descent

This module proves the actual `sInf`-valued steepest-descent condition.
The comparison uses the SMW solution's derivative-minimizing cut as a fixed
test cut for every regular non-idling competitor at the same state.
-/

open scoped BigOperators
open Set

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]
variable [LinearOrder Buffer]

private theorem noWaste_sum_le_cutDrift
    (N : Network Buffer Server)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (S : Finset Buffer)
    {drift : Buffer -> Real}
    (hdrift : drift ∈ N.noWasteDriftSet f) :
    Finset.sum S drift <= N.cutDrift S f := by
  classical
  obtain ⟨d, hdnonneg, hdsum, hdriftEq⟩ := hdrift
  let row : Server -> Real :=
    fun j => Finset.sum Finset.univ (fun k => f j k)
  have hrow (j : Server) : 0 <= row j :=
    Finset.sum_nonneg (fun k _ => hf j k)
  have hservice :
      Finset.sum
          (Finset.univ.filter (fun j => N.buffersOf j <= S))
          (fun j => row j) <=
        Finset.sum S (fun i =>
          Finset.sum (N.serversOf i) (fun j => d i j * row j)) := by
    calc
      Finset.sum
          (Finset.univ.filter (fun j => N.buffersOf j <= S))
          (fun j => row j) =
          Finset.sum
            (Finset.univ.filter (fun j => N.buffersOf j <= S))
            (fun j => Finset.sum S (fun i =>
              if N.compatible i j then d i j * row j else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjsub : N.buffersOf j <= S :=
          (Finset.mem_filter.1 hj).2
        rw [show
            Finset.sum S (fun i =>
                if N.compatible i j then d i j * row j else 0) =
              Finset.sum (N.buffersOf j)
                (fun i => d i j * row j) by
          rw [<- Finset.sum_subset hjsub]
          · apply Finset.sum_congr rfl
            intro i hi
            rw [if_pos ((N.mem_buffersOf i j).1 hi)]
          · intro i hiS hiBuffer
            rw [if_neg]
            intro hij
            exact hiBuffer ((N.mem_buffersOf i j).2 hij)]
        rw [<- Finset.sum_mul, hdsum j, one_mul]
      _ <= Finset.sum Finset.univ (fun j =>
            Finset.sum S (fun i =>
              if N.compatible i j then d i j * row j else 0)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _)
        intro j _ _
        apply Finset.sum_nonneg
        intro i _
        split_ifs
        · exact mul_nonneg (hdnonneg i j) (hrow j)
        · exact le_rfl
      _ = Finset.sum S (fun i =>
            Finset.sum Finset.univ (fun j =>
              if N.compatible i j then d i j * row j else 0)) := by
        rw [Finset.sum_comm]
      _ = Finset.sum S (fun i =>
            Finset.sum (N.serversOf i) (fun j => d i j * row j)) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [StateDepMOR.Network.serversOf, Finset.sum_filter]
  simp_rw [hdriftEq, Finset.sum_sub_distrib]
  have harrivals :
      Finset.sum S (fun i =>
          Finset.sum Finset.univ (fun j => f j i)) =
        Finset.sum Finset.univ (fun j =>
          Finset.sum S (fun i => f j i)) := by
    rw [Finset.sum_comm]
  rw [harrivals]
  unfold StateDepMOR.Network.cutDrift
  change
    Finset.sum Finset.univ (fun j => Finset.sum S (fun i => f j i)) -
        Finset.sum S (fun i =>
          Finset.sum (N.serversOf i) (fun j => d i j * row j)) <=
      Finset.sum Finset.univ (fun j => Finset.sum S (fun i => f j i)) -
        Finset.sum
          (Finset.univ.filter (fun j => N.buffersOf j <= S))
          (fun j => row j)
  linarith

private theorem inputRate_nonnegative
    (N : Network Buffer Server) (alpha : Simplex Buffer)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A) (t : Real)
    (hregular : IsRegularPoint N alpha s t) :
    forall j k, 0 <= pathDerivative A t j k := by
  intro j k
  unfold pathDerivative
  rw [<- derivWithin_of_mem_nhds
    (Icc_mem_nhds hregular.1.1 hregular.1.2)]
  exact (s.input_valid.2.1 j k).derivWithin_nonneg

private theorem smw_drift_le_localRightDirectionalValue
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {T : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution (N.smwPolicy alpha halpha) T x0 A)
    (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (hL : Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1)
    (drift : Buffer -> Real)
    (hdrift : drift ∈ N.noWasteDriftSet (pathDerivative A t)) :
    lyapunovDrift alpha s.X t <=
      localRightDirectionalValue alpha (s.X t) drift := by
  classical
  let S1 := minimumScaledBuffers alpha (s.X t)
  let S2 := minimumDerivativeBuffers alpha (s.X t)
    (fun i => deriv (fun r => s.X r i) t)
  let mass : Real := Finset.sum S2 (fun i => alpha i)
  have hS2nonempty : S2.Nonempty :=
    minimumDerivativeBuffers_nonempty alpha (s.X t)
      (fun i => deriv (fun r => s.X r i) t)
  have hmass : 0 < mass := by
    dsimp [mass]
    exact Finset.sum_pos (fun i _ => halpha i) hS2nonempty
  have hS2sub : S2 <= S1 := by
    intro i hi
    exact (Finset.mem_filter.1 hi).1
  have hratio (i : Buffer) (hi : i ∈ S2) :
      (S1.inf' (minimumScaledBuffers_nonempty alpha (s.X t))
          (fun q => drift q / alpha q)) <=
        drift i / alpha i :=
    Finset.inf'_le _ (hS2sub hi)
  have hweighted :
      mass *
          (S1.inf' (minimumScaledBuffers_nonempty alpha (s.X t))
            (fun q => drift q / alpha q)) <=
        Finset.sum S2 drift := by
    calc
      mass *
          (S1.inf' (minimumScaledBuffers_nonempty alpha (s.X t))
            (fun q => drift q / alpha q)) =
          Finset.sum S2 (fun i =>
            alpha i *
              (S1.inf' (minimumScaledBuffers_nonempty alpha (s.X t))
                (fun q => drift q / alpha q))) := by
        dsimp [mass]
        rw [Finset.sum_mul]
      _ <= Finset.sum S2 (fun i => alpha i * (drift i / alpha i)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hratio i hi) (halpha i).le
      _ = Finset.sum S2 drift := by
        apply Finset.sum_congr rfl
        intro i _
        field_simp [ne_of_gt (halpha i)]
  have hcut :
      Finset.sum S2 drift <= N.cutDrift S2 (pathDerivative A t) :=
    noWaste_sum_le_cutDrift N (pathDerivative A t)
      (inputRate_nonnegative N alpha s t hregular) S2 hdrift
  have hminimum_le :
      (S1.inf' (minimumScaledBuffers_nonempty alpha (s.X t))
        (fun q => drift q / alpha q)) <=
        N.cutDrift S2 (pathDerivative A t) / mass := by
    apply (le_div_iff₀ hmass).2
    simpa [mul_comm] using hweighted.trans hcut
  have hsmw :
      lyapunovDrift alpha s.X t =
        steepestDescentLowerBound (N := N) alpha A s.X t :=
    smw_lyapunovDrift_eq_steepestDescentLowerBound
      N alpha halpha (N.smwPolicy_nonIdling alpha halpha)
      (N.smwPolicy_isSMW alpha halpha) s t hregular hL
  rw [hsmw, steepestDescentLowerBound_eq_neg_cutDrift]
  change
    -(1 / mass) * N.cutDrift S2 (pathDerivative A t) <=
      -(S1.inf' (minimumScaledBuffers_nonempty alpha (s.X t))
        (fun q => drift q / alpha q))
  have hneg := neg_le_neg hminimum_le
  field_simp [ne_of_gt hmass] at hneg ⊢
  nlinarith

/-- SMW minimizes the local forward Lyapunov derivative over every feasible
no-waste scheduling direction at the same state and input rate. -/
theorem smwPolicy_steepestDescentCondition
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior) :
    SteepestDescentCondition (N := N) alpha (N.smwPolicy alpha halpha) := by
  intro T x0 A s t hregular _hstateNe hL drift hdrift
  exact smw_drift_le_localRightDirectionalValue
    N alpha halpha s t hregular hL drift hdrift

end StateDepMOR.PaperStatements.Network
