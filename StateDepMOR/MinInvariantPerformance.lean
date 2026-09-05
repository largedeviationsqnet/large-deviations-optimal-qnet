import StateDepMOR.FiniteQueueStationarity
import StateDepMOR.FiniteQueueBalance
import StateDepMOR.Asymptotics

/-!
# Minimum recurrent-class performance

The appendix evaluates a policy in a recurrent class with minimum stationary
waste. This module makes that convention concrete by taking the infimum over
all invariant PMFs of the finite event-epoch chain. No invariant law or loss
value is supplied as external semantic data.
-/

namespace StateDepMOR

open scoped BigOperators ENNReal

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

variable (N : Network Buffer Server)

private noncomputable def pmfSimplex
    (_N : Network Buffer Server) {K : Nat}
    (pi : PMF (JobState Buffer K)) :
    stdSimplex Real (JobState Buffer K) :=
  ⟨fun x => (pi x).toReal,
    ⟨fun x => ENNReal.toReal_nonneg,
      PMF.sum_toReal pi⟩⟩

private noncomputable def simplexPMF
    (_N : Network Buffer Server) {K : Nat}
    (p : stdSimplex Real (JobState Buffer K)) :
    PMF (JobState Buffer K) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p x)) (by
    rw [(ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ)
      (fun x _ => stdSimplex.zero_le p x)).symm]
    rw [stdSimplex.sum_eq_one]
    simp)

@[simp]
private theorem pmfSimplex_apply {K : Nat}
    (pi : PMF (JobState Buffer K)) (x : JobState Buffer K) :
    N.pmfSimplex pi x = (pi x).toReal :=
  rfl

@[simp]
private theorem simplexPMF_toReal {K : Nat}
    (p : stdSimplex Real (JobState Buffer K))
    (x : JobState Buffer K) :
    (N.simplexPMF p x).toReal = p x := by
  rw [simplexPMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (stdSimplex.zero_le p x)

private theorem bind_toReal {K : Nat}
    (pi : PMF (JobState Buffer K))
    (U : N.DeterministicStationaryPolicy K)
    (y : JobState Buffer K) :
    ((pi.bind (N.transitionPMF U)) y).toReal =
      Finset.sum Finset.univ (fun x =>
        (pi x).toReal * (N.transitionPMF U x y).toReal) := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top (pi.apply_ne_top x)
      ((N.transitionPMF U x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul]

/-- Invariant laws represented inside the compact real probability
simplex. -/
private def invariantSimplexSet {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    Set (stdSimplex Real (JobState Buffer K)) :=
  {p | forall y,
    Finset.sum Finset.univ (fun x =>
      p x * (N.transitionPMF U x y).toReal) = p y}

private theorem invariantSimplexSet_isClosed {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    IsClosed (N.invariantSimplexSet U) := by
  rw [show N.invariantSimplexSet U =
      Set.iInter (fun y : JobState Buffer K =>
        {p | Finset.sum Finset.univ (fun x =>
          p x * (N.transitionPMF U x y).toReal) = p y}) by
    ext p
    simp [invariantSimplexSet]]
  apply isClosed_iInter
  intro y
  apply isClosed_eq
  · apply continuous_finsetSum
    intro x hx
    exact
      ((continuous_apply x).comp continuous_subtype_val).mul
        continuous_const
  · exact (continuous_apply y).comp continuous_subtype_val

private theorem pmfSimplex_mem_invariantSimplexSet {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K))
    (hpi : N.IsInvariantPMF U pi) :
    N.pmfSimplex pi ∈ N.invariantSimplexSet U := by
  intro y
  change
    Finset.sum Finset.univ (fun x =>
      (pi x).toReal * (N.transitionPMF U x y).toReal) =
      (pi y).toReal
  rw [← N.bind_toReal pi U y, hpi]

private theorem invariantSimplexSet_nonempty {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    (N.invariantSimplexSet U).Nonempty := by
  obtain ⟨pi, hpi⟩ := N.exists_invariantPMF U
  exact ⟨N.pmfSimplex pi,
    N.pmfSimplex_mem_invariantSimplexSet U pi hpi⟩

private theorem invariantSimplexSet_isCompact {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    IsCompact (N.invariantSimplexSet U) := by
  simpa only [Set.univ_inter] using
    isCompact_univ.inter_right (N.invariantSimplexSet_isClosed U)

private noncomputable def simplexWaste {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (p : stdSimplex Real (JobState Buffer K)) : Real :=
  Finset.sum Finset.univ (fun x => p x * N.oneStepWaste U x)

private theorem simplexWaste_continuous {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    Continuous (N.simplexWaste U) := by
  unfold simplexWaste
  apply continuous_finsetSum
  intro x hx
  exact
    ((continuous_apply x).comp continuous_subtype_val).mul
      continuous_const

private theorem simplexWaste_pmfSimplex {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) :
    N.simplexWaste U (N.pmfSimplex pi) =
      N.stationaryOneStepWaste U pi :=
  rfl

private theorem simplexPMF_isInvariant {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (p : stdSimplex Real (JobState Buffer K))
    (hp : p ∈ N.invariantSimplexSet U) :
    N.IsInvariantPMF U (N.simplexPMF p) := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (((N.simplexPMF p).bind (N.transitionPMF U)).apply_ne_top y)
    ((N.simplexPMF p).apply_ne_top y)).mp
  rw [N.bind_toReal, N.simplexPMF_toReal]
  simp_rw [N.simplexPMF_toReal]
  exact hp y

private theorem stationaryOneStepWaste_simplexPMF {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (p : stdSimplex Real (JobState Buffer K)) :
    N.stationaryOneStepWaste U (N.simplexPMF p) =
      N.simplexWaste U p := by
  unfold stationaryOneStepWaste simplexWaste
  simp only [N.simplexPMF_toReal]

/-- The minimum over invariant laws is attained by an invariant PMF. -/
theorem exists_minimizingInvariantPMF {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    exists pi : PMF (JobState Buffer K),
      N.IsInvariantPMF U pi /\
      (forall pi' : PMF (JobState Buffer K),
        N.IsInvariantPMF U pi' ->
        N.stationaryOneStepWaste U pi <=
          N.stationaryOneStepWaste U pi') := by
  obtain ⟨p, hp, hminimum⟩ :=
    (N.invariantSimplexSet_isCompact U).exists_isMinOn
      (N.invariantSimplexSet_nonempty U)
      (N.simplexWaste_continuous U).continuousOn
  let pi := N.simplexPMF p
  refine ⟨pi, N.simplexPMF_isInvariant U p hp, ?_⟩
  intro pi' hpi'
  rw [show N.stationaryOneStepWaste U pi =
      N.simplexWaste U p by
    exact N.stationaryOneStepWaste_simplexPMF U p]
  rw [← N.simplexWaste_pmfSimplex U pi']
  exact hminimum
    (N.pmfSimplex_mem_invariantSimplexSet U pi' hpi')

/-- Stationary waste values generated by invariant laws of one finite queue
chain. -/
def invariantLossSet {K : Nat}
    (U : N.DeterministicStationaryPolicy K) : Set Real :=
  {r | exists pi : PMF (JobState Buffer K),
    N.IsInvariantPMF U pi /\
      r = N.stationaryOneStepWaste U pi}

theorem invariantLossSet_nonempty {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    (N.invariantLossSet U).Nonempty := by
  obtain ⟨pi, hpi⟩ := N.exists_invariantPMF U
  exact ⟨N.stationaryOneStepWaste U pi, pi, hpi, rfl⟩

theorem invariantLossSet_nonnegative {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    {r : Real} (hr : r ∈ N.invariantLossSet U) :
    0 <= r := by
  obtain ⟨pi, hpi, rfl⟩ := hr
  exact N.stationaryOneStepWaste_nonneg U pi

theorem invariantLossSet_le_one {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    {r : Real} (hr : r ∈ N.invariantLossSet U) :
    r <= 1 := by
  obtain ⟨pi, hpi, rfl⟩ := hr
  exact N.stationaryOneStepWaste_le_one U pi

theorem invariantLossSet_bddBelow {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    BddBelow (N.invariantLossSet U) :=
  ⟨0, fun r hr => N.invariantLossSet_nonnegative U hr⟩

/-- Minimum stationary event-epoch waste among all invariant laws. -/
noncomputable def minimumInvariantLoss {K : Nat}
    (U : N.DeterministicStationaryPolicy K) : Real :=
  sInf (N.invariantLossSet U)

theorem minimumInvariantLoss_nonnegative {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    0 <= N.minimumInvariantLoss U := by
  unfold minimumInvariantLoss
  apply le_csInf (N.invariantLossSet_nonempty U)
  intro r hr
  exact N.invariantLossSet_nonnegative U hr

theorem minimumInvariantLoss_le_stationaryOneStepWaste {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K))
    (hpi : N.IsInvariantPMF U pi) :
    N.minimumInvariantLoss U <=
      N.stationaryOneStepWaste U pi := by
  unfold minimumInvariantLoss
  apply csInf_le (N.invariantLossSet_bddBelow U)
  exact ⟨pi, hpi, rfl⟩

theorem exists_minimumInvariantLossPMF {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    exists pi : PMF (JobState Buffer K),
      N.IsInvariantPMF U pi /\
      N.minimumInvariantLoss U =
        N.stationaryOneStepWaste U pi := by
  obtain ⟨pi, hpi, hminimum⟩ :=
    N.exists_minimizingInvariantPMF U
  refine ⟨pi, hpi, le_antisymm
    (N.minimumInvariantLoss_le_stationaryOneStepWaste U pi hpi) ?_⟩
  unfold minimumInvariantLoss
  apply le_csInf (N.invariantLossSet_nonempty U)
  intro r hr
  obtain ⟨pi', hpi', rfl⟩ := hr
  exact hminimum pi' hpi'

/-- A canonical minimizing invariant law, selected only after existence and
attainment have been proved. -/
noncomputable def minimumInvariantPMF {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    PMF (JobState Buffer K) :=
  Classical.choose (N.exists_minimumInvariantLossPMF U)

theorem minimumInvariantPMF_isInvariant {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    N.IsInvariantPMF U (N.minimumInvariantPMF U) :=
  (Classical.choose_spec (N.exists_minimumInvariantLossPMF U)).1

theorem minimumInvariantLoss_eq_stationaryOneStepWaste {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    N.minimumInvariantLoss U =
      N.stationaryOneStepWaste U (N.minimumInvariantPMF U) :=
  (Classical.choose_spec (N.exists_minimumInvariantLossPMF U)).2

theorem minimumInvariantLoss_le_one {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    N.minimumInvariantLoss U <= 1 := by
  obtain ⟨pi, hpi⟩ := N.exists_invariantPMF U
  exact (N.minimumInvariantLoss_le_stationaryOneStepWaste U pi hpi).trans
    (N.stationaryOneStepWaste_le_one U pi)

/-- Minimum stationary loss for a policy sequence at every positive system
size. -/
noncomputable def minimumInvariantLossFamily
    (U : N.DeterministicPolicySequence) (K : PNat) : Real :=
  N.minimumInvariantLoss (U K)

theorem minimumInvariantLossFamily_nonnegative
    (U : N.DeterministicPolicySequence) (K : PNat) :
    0 <= N.minimumInvariantLossFamily U K :=
  N.minimumInvariantLoss_nonnegative (U K)

theorem minimumInvariantLossFamily_le_one
    (U : N.DeterministicPolicySequence) (K : PNat) :
    N.minimumInvariantLossFamily U K <= 1 :=
  N.minimumInvariantLoss_le_one (U K)

/-- Fully derived performance semantics using the minimum-loss invariant
class at every `K`. -/
noncomputable def minimumInvariantPerformance :
    PerformanceSemantics N where
  loss := N.minimumInvariantLossFamily
  loss_nonneg := N.minimumInvariantLossFamily_nonnegative
  loss_le_one := N.minimumInvariantLossFamily_le_one

@[simp]
theorem minimumInvariantPerformance_loss
    (U : N.DeterministicPolicySequence) (K : PNat) :
    N.minimumInvariantPerformance.loss U K =
      N.minimumInvariantLoss (U K) :=
  rfl

/-- Every invariant law obeys the stationary cut imbalance, so the minimum
over invariant laws does too. -/
theorem minimumInvariantLoss_ge_cutImbalance {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (J : Finset Server) :
    N.netServiceRate J - N.netArrivalRate J <=
      N.minimumInvariantLoss U := by
  unfold minimumInvariantLoss
  apply le_csInf (N.invariantLossSet_nonempty U)
  intro r hr
  obtain ⟨pi, hpi, rfl⟩ := hr
  exact N.stationaryOneStepWaste_ge_netImbalance U pi hpi J

theorem minimumInvariantLoss_isOmegaOneDivSq_of_strict_cutImbalance
    (U : N.DeterministicPolicySequence)
    (J : Finset Server)
    (hstrict : N.netArrivalRate J < N.netServiceRate J) :
    IsOmegaOneDivSq (N.minimumInvariantLossFamily U) := by
  let c := N.netServiceRate J - N.netArrivalRate J
  have hc : 0 < c := sub_pos.2 hstrict
  refine ⟨c, hc, Filter.Eventually.of_forall ?_⟩
  intro K
  have hK : (1 : Real) <= (K : Real) := by
    exact_mod_cast PNat.pos K
  have hKsq : (1 : Real) <= (K : Real) ^ 2 := by
    nlinarith
  have hKsqPos : 0 < (K : Real) ^ 2 :=
    zero_lt_one.trans_le hKsq
  calc
    c / (K : Real) ^ 2 <= c := by
      apply (div_le_iff₀ hKsqPos).2
      nlinarith
    _ <= N.minimumInvariantLoss (U K) :=
      N.minimumInvariantLoss_ge_cutImbalance (U K) J

theorem minimumInvariantThroughputLossExponent_eq_zero_of_strict_cutImbalance
    (U : N.DeterministicPolicySequence)
    (J : Finset Server)
    (hstrict : N.netArrivalRate J < N.netServiceRate J) :
    N.minimumInvariantPerformance.throughputLossExponent U = 0 := by
  exact
    N.minimumInvariantPerformance
      |>.throughputLossExponent_eq_zero_of_isOmegaOneDivSq U
        (N.minimumInvariantLoss_isOmegaOneDivSq_of_strict_cutImbalance
          U J hstrict)

end Network

end StateDepMOR
