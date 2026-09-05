import StateDepMOR.FluidConsistency
import StateDepMOR.FiniteQueueTrajectories
import StateDepMOR.EventEpochExecution
import StateDepMOR.PoissonProcessExecution
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fin.Tuple.Take

/-!
# Deterministic fluid-model existence

This file addresses the deterministic clause of `lem:fms-existence` using
the current `Network.FluidModelSolution` structure.
-/

open scoped BigOperators Topology
open Filter MeasureTheory Set

set_option maxHeartbeats 800000

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

namespace Network

/-- Coordinatewise floors used to approximate a simplex point by a queue
state with an exact integer population. -/
private noncomputable def floorJobs
    (x : Simplex Buffer) (K : Nat) (i : Buffer) : Nat :=
  Nat.floor ((K : Real) * x i)

private theorem sum_floorJobs_le (x : Simplex Buffer) (K : Nat) :
    (Finset.univ.sum fun i => floorJobs x K i) <= K := by
  have hterm (i : Buffer) :
      ((floorJobs x K i : Nat) : Real) <= (K : Real) * x i := by
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) (x.nonneg i))
  have hreal :
      ((Finset.univ.sum fun i => floorJobs x K i : Nat) : Real) <= K := by
    calc
      ((Finset.univ.sum fun i => floorJobs x K i : Nat) : Real) =
          Finset.univ.sum (fun i => ((floorJobs x K i : Nat) : Real)) := by
            exact Nat.cast_sum (f := fun i => floorJobs x K i) Finset.univ
      _ <= Finset.univ.sum (fun i => (K : Real) * x i) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = (K : Real) * Finset.univ.sum (fun i => x i) := by
        rw [Finset.mul_sum]
      _ = K := by rw [x.sum_eq_one, mul_one]
  exact_mod_cast hreal

/-- Put the rounding remainder into one fixed buffer. -/
private noncomputable def roundedJobs
    (x : Simplex Buffer) (K : Nat) (i0 : Buffer) :
    Buffer -> Nat :=
  Function.update (floorJobs x K) i0
    (floorJobs x K i0 +
      (K - Finset.univ.sum fun i => floorJobs x K i))

private theorem sum_roundedJobs (x : Simplex Buffer) (K : Nat) (i0 : Buffer) :
    Finset.univ.sum (roundedJobs x K i0) = K := by
  classical
  let base : Buffer -> Nat := floorJobs x K
  let remainder := K - Finset.univ.sum base
  have hbase : Finset.univ.sum base <= K := sum_floorJobs_le x K
  have hsum :=
    Finset.sum_erase_add Finset.univ base (Finset.mem_univ i0)
  unfold roundedJobs
  change
    Finset.univ.sum (Function.update base i0 (base i0 + remainder)) = K
  rw [Finset.sum_update_of_mem (Finset.mem_univ i0)]
  simp only [Finset.sdiff_singleton_eq_erase]
  calc
    base i0 + remainder + (Finset.univ.erase i0).sum base =
        ((Finset.univ.erase i0).sum base + base i0) + remainder := by
          omega
    _ = Finset.univ.sum base + remainder := by rw [hsum]
    _ = K := Nat.add_sub_of_le hbase

private noncomputable def roundedState
    (x : Simplex Buffer) (K : Nat) (i0 : Buffer) :
    JobState Buffer K where
  jobs := roundedJobs x K i0
  total_jobs := sum_roundedJobs x K i0

private theorem roundingRemainder_le_card (x : Simplex Buffer) (K : Nat) :
    K - Finset.univ.sum (fun i => floorJobs x K i) <=
      Fintype.card Buffer := by
  let S := Finset.univ.sum fun i => floorJobs x K i
  have hsumlt :
      (K : Real) <
        (S : Real) + Fintype.card Buffer := by
    calc
      (K : Real) =
          Finset.univ.sum (fun i => (K : Real) * x i) := by
            rw [<- Finset.mul_sum, x.sum_eq_one, mul_one]
      _ < Finset.univ.sum
          (fun i => ((floorJobs x K i : Nat) : Real) + 1) := by
            apply Finset.sum_lt_sum
            · intro i _
              exact le_of_lt (Nat.lt_floor_add_one ((K : Real) * x i))
            · let i0 : Buffer :=
                Classical.choice (inferInstance : Nonempty Buffer)
              refine ⟨i0, Finset.mem_univ _, ?_⟩
              exact Nat.lt_floor_add_one ((K : Real) * x i0)
      _ = (S : Real) + Fintype.card Buffer := by
            rw [Finset.sum_add_distrib]
            simp [S, Nat.cast_sum]
  have hnat : K < S + Fintype.card Buffer := by
    exact_mod_cast hsumlt
  omega

private theorem roundedState_error_bound
    (x : Simplex Buffer) (K : Nat) (hK : 0 < K) (i0 i : Buffer) :
    abs (((roundedState x K i0 i : Nat) : Real) / K - x i) <
      (((Fintype.card Buffer : Nat) : Real) + 1) / (K : Real) := by
  classical
  let b : Nat := floorJobs x K i
  let r : Nat := K - Finset.univ.sum (fun q => floorJobs x K q)
  have hb_le : (b : Real) <= (K : Real) * x i := by
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) (x.nonneg i))
  have hlt_b : (K : Real) * x i < (b : Real) + 1 :=
    Nat.lt_floor_add_one ((K : Real) * x i)
  have hr : r <= Fintype.card Buffer :=
    roundingRemainder_le_card x K
  have hb_jobs :
      b <= roundedState x K i0 i := by
    by_cases hi : i = i0
    · subst i
      simp [roundedState, roundedJobs, b, r]
    · simp [roundedState, roundedJobs, b, hi]
  have hjobs_le :
      roundedState x K i0 i <= b + r := by
    by_cases hi : i = i0
    · subst i
      simp [roundedState, roundedJobs, b, r]
    · simp [roundedState, roundedJobs, b, hi]
  have hdiff_lower :
      -1 < ((roundedState x K i0 i : Nat) : Real) - (K : Real) * x i := by
    have hb_jobs_real :
        (b : Real) <= ((roundedState x K i0 i : Nat) : Real) := by
      exact_mod_cast hb_jobs
    linarith
  have hdiff_upper :
      ((roundedState x K i0 i : Nat) : Real) - (K : Real) * x i <=
        (Fintype.card Buffer : Real) := by
    have hjobs_le_real :
        ((roundedState x K i0 i : Nat) : Real) <= (b : Real) + r := by
      exact_mod_cast hjobs_le
    have hrreal : (r : Real) <= Fintype.card Buffer := by
      exact_mod_cast hr
    linarith
  have habs :
      abs (((roundedState x K i0 i : Nat) : Real) - (K : Real) * x i) <
        (Fintype.card Buffer : Real) + 1 := by
    rw [abs_lt]
    constructor
    · have hc : 0 <= (Fintype.card Buffer : Real) := Nat.cast_nonneg _
      linarith
    · linarith
  have hKreal : 0 < (K : Real) := Nat.cast_pos.mpr hK
  rw [show
      ((roundedState x K i0 i : Nat) : Real) / K - x i =
        (((roundedState x K i0 i : Nat) : Real) - (K : Real) * x i) / K by
      field_simp]
  rw [abs_div, abs_of_pos hKreal]
  exact div_lt_div_of_pos_right habs hKreal

/-- Every simplex point has arbitrarily large normalized integer queue-state
approximations. -/
private theorem exists_near_normalized_state
    (x : Simplex Buffer) (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists K : PNat, exists z : JobState Buffer (K : Nat),
      epsilon ^ (-1 : Int) <= (K : Real) /\
      IsNearNormalizedState z x epsilon := by
  let c : Real := (Fintype.card Buffer : Real) + 1
  obtain ⟨K : Nat, hKlarge⟩ :=
    exists_nat_gt (max (epsilon ^ (-1 : Int)) (c / epsilon))
  have hKpos : 0 < K := by
    have hnonneg : 0 <= epsilon ^ (-1 : Int) := by positivity
    exact_mod_cast lt_of_le_of_lt hnonneg (lt_of_le_of_lt (le_max_left _ _) hKlarge)
  let Kp : PNat := ⟨K, hKpos⟩
  let i0 : Buffer := Classical.choice (inferInstance : Nonempty Buffer)
  let z : JobState Buffer K := roundedState x K i0
  refine ⟨Kp, z, ?_, ?_⟩
  · exact le_of_lt (lt_of_le_of_lt (le_max_left _ _) hKlarge)
  · intro i
    have hbound := roundedState_error_bound x K hKpos i0 i
    have hcpos : 0 < c := by
      dsimp [c]
      positivity
    have hKc : c / epsilon < (K : Real) :=
      lt_of_le_of_lt (le_max_right _ _) hKlarge
    have hratio : c / (K : Real) < epsilon := by
      apply (div_lt_iff₀ (Nat.cast_pos.mpr hKpos)).2
      apply (div_lt_iff₀ hepsilon).1 at hKc
      nlinarith
    exact hbound.trans hratio

/-- At every simplex state, each typewise policy correspondence contains a
Dirac action that recurs along arbitrarily accurate finite-state
approximations. -/
private theorem exists_actionDirac_mem_fluidPolicyCorrespondence
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Simplex Buffer) :
    exists a : N.ServiceAction,
      (forall i, a = some i -> N.compatible i j) /\
      N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x := by
  classical
  let epsilon : Nat -> Real := fun n => 1 / ((n : Real) + 1)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp [epsilon]
    positivity
  have happrox :
      forall n : Nat, exists K : PNat,
        exists z : JobState Buffer (K : Nat),
          (epsilon n) ^ (-1 : Int) <= (K : Real) /\
          IsNearNormalizedState z x (epsilon n) := by
    intro n
    exact exists_near_normalized_state x (epsilon n) (hepsilon n)
  choose K z hK hnear using happrox
  let action : Nat -> N.ServiceAction := fun n => U (K n) (z n) j k
  have hfrequent :
      ∃ a : N.ServiceAction, ∃ᶠ n in atTop, action n = a := by
    rw [<- Filter.frequently_exists]
    exact Frequently.of_forall fun n => ⟨action n, rfl⟩
  obtain ⟨a, ha⟩ := hfrequent
  have hone : forall i, a = some i -> N.compatible i j := by
    intro i hai
    obtain ⟨n, _hn, hna⟩ := Filter.frequently_atTop.mp ha 0
    have hlegal := (U (K n)).legal (z n) j k
    have haction : U (K n) (z n) j k = some i := by
      change action n = some i
      rw [hna, hai]
    rw [haction] at hlegal
    exact hlegal.1
  refine ⟨a, hone, ?_⟩
  unfold fluidPolicyCorrespondence
  rw [Set.mem_iInter]
  intro e
  obtain ⟨m : Nat, hm⟩ := exists_nat_one_div_lt e.property
  obtain ⟨n, hmn, hna⟩ := Filter.frequently_atTop.mp ha m
  have hepsilon_le : epsilon n <= 1 / ((m : Real) + 1) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hmn 1
  have hsmall : epsilon n < e.1 := hepsilon_le.trans_lt hm
  apply subset_closure
  apply subset_convexHull Real
  refine ⟨K n, z n, ?_, ?_, ?_⟩
  · have hinv : e.1⁻¹ <= (epsilon n)⁻¹ :=
      (inv_le_inv₀ e.property (hepsilon n)).2 (le_of_lt hsmall)
    exact hinv.trans (by simpa [zpow_neg_one] using hK n)
  · intro i
    exact (hnear n i).trans hsmall
  · change N.actionDirac a = N.actionDirac (action n)
    rw [hna]

/-- The fluid policy correspondence is nonempty at every simplex state. -/
theorem fluidPolicyCorrespondence_nonempty
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Simplex Buffer) :
    (N.fluidPolicyCorrespondence U j k x).Nonempty := by
  obtain ⟨a, _ha, hmem⟩ :=
    exists_actionDirac_mem_fluidPolicyCorrespondence N U j k x
  exact ⟨N.actionDirac a, hmem⟩

/-- Every vector admitted by the fluid policy correspondence is a probability
distribution on actions. -/
theorem fluidPolicyCorrespondence_isActionDistribution
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real)
    (q : ActionVector Buffer)
    (hq : q ∈ N.fluidPolicyCorrespondence U j k x) :
    IsActionDistribution q := by
  classical
  let e : {r : Real // 0 < r} := ⟨1, one_pos⟩
  have hqe :
      q ∈ closure (convexHull Real
        {r | exists K : PNat, exists z : JobState Buffer (K : Nat),
          e.1⁻¹ <= (K : Real) /\
          IsNearNormalizedState z x e.1 /\
          r = N.actionDirac (U K z j k)}) := by
    exact Set.mem_iInter.mp hq e
  constructor
  · intro a
    let H : Set (ActionVector Buffer) := {r | 0 <= r a}
    have hHclosed : IsClosed H :=
      isClosed_le continuous_const (continuous_apply a)
    have hHconvex : Convex Real H := by
      intro r hr s hs c d hc hd hcd
      change 0 <= (c • r + d • s) a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg hc hr) (mul_nonneg hd hs)
    have hbase :
        {r | exists K : PNat, exists z : JobState Buffer (K : Nat),
          e.1⁻¹ <= (K : Real) /\
          IsNearNormalizedState z x e.1 /\
          r = N.actionDirac (U K z j k)} <= H := by
      intro r hr
      obtain ⟨K, z, _hK, _hz, rfl⟩ := hr
      exact (N.actionDirac_isDistribution (U K z j k)).1 a
    exact
      closure_minimal (convexHull_min hbase hHconvex) hHclosed hqe
  · let H : Set (ActionVector Buffer) := {r | (Finset.univ.sum r) = 1}
    have hHclosed : IsClosed H := by
      exact isClosed_eq (continuous_finset_sum _ fun a _ => continuous_apply a)
        continuous_const
    have hHconvex : Convex Real H := by
      intro r hr s hs c d hc hd hcd
      change Finset.univ.sum r = 1 at hr
      change Finset.univ.sum s = 1 at hs
      change Finset.univ.sum (c • r + d • s) = 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, <- Finset.mul_sum, hr, hs]
      linarith
    have hbase :
        {r | exists K : PNat, exists z : JobState Buffer (K : Nat),
          e.1⁻¹ <= (K : Real) /\
          IsNearNormalizedState z x e.1 /\
          r = N.actionDirac (U K z j k)} <= H := by
      intro r hr
      obtain ⟨K, z, _hK, _hz, rfl⟩ := hr
      exact (N.actionDirac_isDistribution (U K z j k)).2
    exact
      closure_minimal (convexHull_min hbase hHconvex) hHclosed hqe

/-- Incompatible source actions have zero mass throughout the fluid policy
correspondence. -/
theorem fluidPolicyCorrespondence_incompatible
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k i : Buffer) (x : Buffer -> Real)
    (q : ActionVector Buffer)
    (hq : q ∈ N.fluidPolicyCorrespondence U j k x)
    (hij : Not (N.compatible i j)) :
    q (some i) = 0 := by
  classical
  let e : {r : Real // 0 < r} := ⟨1, one_pos⟩
  let H : Set (ActionVector Buffer) := {r | r (some i) = 0}
  have hHclosed : IsClosed H :=
    isClosed_eq (continuous_apply (some i)) continuous_const
  have hHconvex : Convex Real H := by
    exact convex_hyperplane (LinearMap.proj (some i)).isLinear 0
  have hbase :
      {r | exists K : PNat, exists z : JobState Buffer (K : Nat),
        e.1⁻¹ <= (K : Real) /\
        IsNearNormalizedState z x e.1 /\
        r = N.actionDirac (U K z j k)} <= H := by
    intro r hr
    obtain ⟨K, z, _hK, _hz, rfl⟩ := hr
    have hne : Not (some i = U K z j k) := by
      intro heq
      have hlegal := (U K).legal z j k
      rw [<- heq] at hlegal
      exact hij hlegal.1
    simp [H, actionDirac, hne]
  unfold fluidPolicyCorrespondence at hq
  have hqe := Set.mem_iInter.mp hq e
  exact closure_minimal (convexHull_min hbase hHconvex) hHclosed hqe

/-- The fluid policy correspondence is convex. -/
theorem fluidPolicyCorrespondence_convex
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) :
    Convex Real (N.fluidPolicyCorrespondence U j k x) := by
  unfold fluidPolicyCorrespondence
  exact convex_iInter fun _ => (convex_convexHull Real _).closure

/-- Graph of one typewise fluid policy correspondence. -/
def fluidPolicyCorrespondenceGraph
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    Set ((Buffer -> Real) × ActionVector Buffer) :=
  {xp | xp.2 ∈ N.fluidPolicyCorrespondence U j k xp.1}

/-- The fluid policy correspondence has a closed graph. -/
theorem fluidPolicyCorrespondenceGraph_isClosed
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    IsClosed (N.fluidPolicyCorrespondenceGraph U j k) := by
  rw [<- isSeqClosed_iff_isClosed]
  intro s xp hs hsxp
  rcases xp with ⟨x, p⟩
  have hx :
      Tendsto (fun n => (s n).1) atTop (nhds x) :=
    hsxp.fst_nhds
  have hp :
      Tendsto (fun n => (s n).2) atTop (nhds p) :=
    hsxp.snd_nhds
  unfold fluidPolicyCorrespondenceGraph at hs ⊢
  simp only [Set.mem_setOf_eq] at hs ⊢
  unfold fluidPolicyCorrespondence
  rw [Set.mem_iInter]
  intro e
  let d : {epsilon : Real // 0 < epsilon} :=
    ⟨e.1 / 2, half_pos e.property⟩
  have hcoord :
      forall i : Buffer,
        ∀ᶠ n in atTop, abs ((s n).1 i - x i) < d.1 := by
    intro i
    have hi :
        Tendsto (fun n => (s n).1 i) atTop (nhds (x i)) :=
      tendsto_pi_nhds.mp hx i
    simpa [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hi d.1 d.property)
  have hall :
      ∀ᶠ n in atTop, forall i : Buffer,
        abs ((s n).1 i - x i) < d.1 :=
    Filter.eventually_all.mpr hcoord
  have hfixed :
      ∀ᶠ n in atTop,
        (s n).2 ∈ closure (convexHull Real
          {q | exists K : PNat, exists z : JobState Buffer (K : Nat),
            e.1⁻¹ <= (K : Real) /\
            IsNearNormalizedState z x e.1 /\
            q = actionDirac N (U K z j k)}) := by
    filter_upwards [hall] with n hn
    have hnd :
        (s n).2 ∈ closure (convexHull Real
          {q | exists K : PNat, exists z : JobState Buffer (K : Nat),
            d.1⁻¹ <= (K : Real) /\
            IsNearNormalizedState z (s n).1 d.1 /\
            q = actionDirac N (U K z j k)}) := by
      have hsn := hs n
      unfold fluidPolicyCorrespondence at hsn
      exact Set.mem_iInter.mp hsn d
    apply closure_mono (convexHull_mono ?_) hnd
    rintro q ⟨K, z, hK, hnear, hq⟩
    refine ⟨K, z, ?_, ?_, hq⟩
    · have hed : d.1 <= e.1 := by
        dsimp [d]
        linarith [e.property]
      exact ((inv_le_inv₀ e.property d.property).2 hed).trans hK
    · intro i
      calc
        abs ((z i : Real) / (K : Nat) - x i) =
            abs (((z i : Real) / (K : Nat) - (s n).1 i) +
              ((s n).1 i - x i)) := by ring_nf
        _ <= abs ((z i : Real) / (K : Nat) - (s n).1 i) +
            abs ((s n).1 i - x i) := abs_add_le _ _
        _ < d.1 + d.1 := add_lt_add (hnear i) (hn i)
        _ = e.1 := by
          dsimp [d]
          ring
  exact isClosed_closure.mem_of_tendsto hp hfixed

private theorem actionDirac_feasibleSet_isClosed
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (a : N.ServiceAction) :
    IsClosed {x : Buffer -> Real |
      N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x} := by
  let f : (Buffer -> Real) ->
      (Buffer -> Real) × ActionVector Buffer :=
    fun x => (x, N.actionDirac a)
  have hf : Continuous f := continuous_id.prodMk continuous_const
  exact (N.fluidPolicyCorrespondenceGraph_isClosed U j k).preimage hf

/-- Number of feasible pure actions at a state. -/
noncomputable def feasiblePureActionMass
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) : Real := by
  classical
  exact ∑ a : N.ServiceAction,
    if N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x then 1 else 0

/-- Sum of all feasible pure action vectors at a state. -/
noncomputable def feasiblePureActionSum
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) :
    ActionVector Buffer := by
  classical
  exact fun b =>
    ∑ a : N.ServiceAction,
      if N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x then
        N.actionDirac a b
      else 0

/-- An explicit measurable selector obtained by averaging feasible pure
actions. -/
noncomputable def measurableFluidPolicySelector
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) :
    ActionVector Buffer := by
  classical
  exact
    if N.feasiblePureActionMass U j k x = 0 then
      N.actionDirac none
    else
      (N.feasiblePureActionMass U j k x)⁻¹ •
        N.feasiblePureActionSum U j k x

private theorem feasiblePureActionMass_measurable
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    Measurable (N.feasiblePureActionMass U j k) := by
  classical
  unfold feasiblePureActionMass
  apply Finset.measurable_fun_sum
  intro a _ha
  apply Measurable.ite
  · exact (actionDirac_feasibleSet_isClosed N U j k a).measurableSet
  · exact measurable_const
  · exact measurable_const

private theorem feasiblePureActionSum_coordinate_measurable
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (b : Option Buffer) :
    Measurable (fun x => N.feasiblePureActionSum U j k x b) := by
  classical
  unfold feasiblePureActionSum
  apply Finset.measurable_fun_sum
  intro a _ha
  apply Measurable.ite
  · exact (actionDirac_feasibleSet_isClosed N U j k a).measurableSet
  · exact measurable_const
  · exact measurable_const

/-- The explicit finite-action selector is globally Borel measurable. -/
theorem measurableFluidPolicySelector_measurable
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    Measurable (N.measurableFluidPolicySelector U j k) := by
  rw [measurable_pi_iff]
  intro b
  unfold measurableFluidPolicySelector
  simp only [ite_apply, Pi.smul_apply, smul_eq_mul]
  apply Measurable.ite
  · exact measurableSet_eq_fun
      (feasiblePureActionMass_measurable N U j k) measurable_const
  · exact measurable_const
  · exact (feasiblePureActionMass_measurable N U j k).inv.mul
      (feasiblePureActionSum_coordinate_measurable N U j k b)

private theorem feasiblePureActionMass_pos
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real)
    (hx : IsFluidState x) :
    0 < N.feasiblePureActionMass U j k x := by
  classical
  let sx : Simplex Buffer :=
    { val := x
      nonneg := hx.1
      sum_eq_one := hx.2 }
  obtain ⟨a, _hcompat, hpure⟩ :=
    exists_actionDirac_mem_fluidPolicyCorrespondence N U j k sx
  have hpure' :
      N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x := by
    simpa [sx] using hpure
  unfold feasiblePureActionMass
  calc
    0 < (1 : Real) := zero_lt_one
    _ = if N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x
        then (1 : Real) else 0 := (if_pos hpure').symm
    _ <= ∑ q : N.ServiceAction,
        if N.actionDirac q ∈ N.fluidPolicyCorrespondence U j k x
        then 1 else 0 := by
      simpa using Finset.single_le_sum
        (s := (Finset.univ : Finset N.ServiceAction))
        (f := fun q =>
          if N.actionDirac q ∈ N.fluidPolicyCorrespondence U j k x
          then (1 : Real) else 0)
        (fun q _hq => by split_ifs <;> norm_num)
        (Finset.mem_univ a)

/-- At every fluid state, the explicit selector belongs to the policy
correspondence. -/
theorem measurableFluidPolicySelector_mem
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real)
    (hx : IsFluidState x) :
    N.measurableFluidPolicySelector U j k x ∈
      N.fluidPolicyCorrespondence U j k x := by
  classical
  let s : Finset N.ServiceAction :=
    Finset.univ.filter fun a =>
      N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x
  have hs : s.Nonempty := by
    let sx : Simplex Buffer :=
      { val := x
        nonneg := hx.1
        sum_eq_one := hx.2 }
    obtain ⟨a, _hcompat, ha⟩ :=
      exists_actionDirac_mem_fluidPolicyCorrespondence N U j k sx
    refine ⟨a, ?_⟩
    simp [s, sx] at ha ⊢
    exact ha
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  have hmass :
      N.feasiblePureActionMass U j k x = (s.card : Real) := by
    unfold feasiblePureActionMass
    rw [<- Finset.sum_filter]
    change (∑ _a ∈ s, (1 : Real)) = (s.card : Real)
    simp
  have hmass_ne : Ne (N.feasiblePureActionMass U j k x) 0 := by
    rw [hmass]
    exact_mod_cast Nat.ne_of_gt hcard
  have hsum :
      N.feasiblePureActionSum U j k x =
        ∑ a ∈ s, N.actionDirac a := by
    funext b
    unfold feasiblePureActionSum
    rw [<- Finset.sum_filter]
    rw [Finset.sum_apply]
  have hweights :
      ∑ _a ∈ s, ((s.card : Real)⁻¹) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hcard)
  have havg :
      (∑ a ∈ s, (s.card : Real)⁻¹ • N.actionDirac a) ∈
        N.fluidPolicyCorrespondence U j k x := by
    apply (N.fluidPolicyCorrespondence_convex U j k x).sum_mem
    · intro a ha
      positivity
    · exact hweights
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
  rw [measurableFluidPolicySelector, if_neg hmass_ne, hmass, hsum]
  simpa only [Finset.smul_sum] using havg

theorem measurableFluidPolicySelector_isActionDistribution
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real)
    (hx : IsFluidState x) :
    IsActionDistribution (N.measurableFluidPolicySelector U j k x) :=
  fluidPolicyCorrespondence_isActionDistribution N U j k x _
    (N.measurableFluidPolicySelector_mem U j k x hx)

theorem measurableFluidPolicySelector_incompatible
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k i : Buffer) (x : Buffer -> Real)
    (hx : IsFluidState x) (hi : Not (N.compatible i j)) :
    N.measurableFluidPolicySelector U j k x (some i) = 0 :=
  fluidPolicyCorrespondence_incompatible N U j k i x _
    (N.measurableFluidPolicySelector_mem U j k x hx) hi

/-! ### Compactness helpers -/

/-- A path controlled by finitely many absolutely continuous real paths is
absolutely continuous. -/
private theorem absolutelyContinuousOnInterval_of_dist_le_finset
    {X Y : Type*} [PseudoMetricSpace X]
    {f : Real -> X} {g : Y -> Real -> Real} {s : Finset Y}
    {a b : Real}
    (hg : forall j, j ∈ s ->
      AbsolutelyContinuousOnInterval (g j) a b)
    (hdom : forall x, x ∈ uIcc a b ->
      forall y, y ∈ uIcc a b ->
      dist (f x) (f y) <=
        s.sum (fun j => dist (g j x) (g j y))) :
    AbsolutelyContinuousOnInterval f a b := by
  unfold AbsolutelyContinuousOnInterval at hg
  unfold AbsolutelyContinuousOnInterval
  have hcontrols :
      Tendsto
        (fun E : Nat × (Nat -> Real × Real) =>
          s.sum (fun j =>
            (Finset.range E.1).sum
              (fun i => dist (g j (E.2 i).1) (g j (E.2 i).2))))
        (Min.min AbsolutelyContinuousOnInterval.totalLengthFilter
          (principal (AbsolutelyContinuousOnInterval.disjWithin a b)))
        (nhds 0) := by
    simpa using tendsto_finsetSum s (fun j hj => hg j hj)
  apply squeeze_zero'
    (Eventually.of_forall
      (fun E : Nat × (Nat -> Real × Real) =>
        Finset.sum_nonneg (fun i hi => dist_nonneg)))
    ?_ hcontrols
  rw [eventually_inf_principal]
  filter_upwards with E hE
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  exact hdom _ (hE.1 i hi).1 _ (hE.1 i hi).2

/-- An increment bound passes to a limit when both the path and its finite
family of control paths converge uniformly. -/
private theorem dist_le_finset_of_uniform_limits
    {X Y : Type*} [PseudoMetricSpace X]
    {f : Nat -> Real -> X} {limit : Real -> X}
    {g : Nat -> Y -> Real -> Real} {control : Y -> Real -> Real}
    {s : Finset Y} {a b : Real}
    (hfconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall t, t ∈ uIcc a b ->
          dist (f n t) (limit t) < epsilon)
    (hgconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j, j ∈ s ->
          forall t, t ∈ uIcc a b ->
            dist (g n j t) (control j t) < epsilon)
    (hdom : forall n, forall x, x ∈ uIcc a b ->
      forall y, y ∈ uIcc a b ->
        dist (f n x) (f n y) <=
          s.sum (fun j => dist (g n j x) (g n j y)))
    {x y : Real} (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
    dist (limit x) (limit y) <=
      s.sum (fun j => dist (control j x) (control j y)) := by
  have hpointF (t : Real) (ht : t ∈ uIcc a b) :
      Tendsto (fun n => f n t) atTop (nhds (limit t)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := hfconv epsilon hepsilon
    exact ⟨n0, fun n hn => hn0 n hn t ht⟩
  have hpointG (j : Y) (hj : j ∈ s)
      (t : Real) (ht : t ∈ uIcc a b) :
      Tendsto (fun n => g n j t) atTop (nhds (control j t)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := hgconv epsilon hepsilon
    exact ⟨n0, fun n hn => hn0 n hn j hj t ht⟩
  have hleft :
      Tendsto (fun n => dist (f n x) (f n y)) atTop
        (nhds (dist (limit x) (limit y))) :=
    (hpointF x hx).dist (hpointF y hy)
  have hright :
      Tendsto
        (fun n => s.sum (fun j => dist (g n j x) (g n j y)))
        atTop
        (nhds (s.sum (fun j =>
          dist (control j x) (control j y)))) := by
    apply tendsto_finsetSum
    intro j hj
    exact (hpointG j hj x hx).dist (hpointG j hj y hy)
  exact le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall (fun n => hdom n x hx y hy))

/-- Uniform limits controlled by uniformly converging finite absolutely
continuous controls are absolutely continuous. -/
private theorem absolutelyContinuousOnInterval_of_uniform_limits_finset
    {X Y : Type*} [PseudoMetricSpace X]
    {f : Nat -> Real -> X} {limit : Real -> X}
    {g : Nat -> Y -> Real -> Real} {control : Y -> Real -> Real}
    {s : Finset Y} {a b : Real}
    (hfconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall t, t ∈ uIcc a b ->
          dist (f n t) (limit t) < epsilon)
    (hgconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j, j ∈ s ->
          forall t, t ∈ uIcc a b ->
            dist (g n j t) (control j t) < epsilon)
    (hac : forall j, j ∈ s ->
      AbsolutelyContinuousOnInterval (control j) a b)
    (hdom : forall n, forall x, x ∈ uIcc a b ->
      forall y, y ∈ uIcc a b ->
        dist (f n x) (f n y) <=
          s.sum (fun j => dist (g n j x) (g n j y))) :
    AbsolutelyContinuousOnInterval limit a b := by
  apply absolutelyContinuousOnInterval_of_dist_le_finset hac
  intro x hx y hy
  exact dist_le_finset_of_uniform_limits
    hfconv hgconv hdom hx hy

/-! ### Exact finite-token identities -/

private theorem runTokens_append {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (xs ys : List (TokenType (Buffer := Buffer) (Server := Server))) :
    N.runTokens U x (xs ++ ys) =
      N.runTokens U (N.runTokens U x xs) ys := by
  induction xs generalizing x with
  | nil => simp [runTokens]
  | cons jk xs ih =>
      simp only [List.cons_append, runTokens]
      exact ih (N.queueStep U x jk)

private theorem runAllocationCount_append {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (xs ys : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer) :
    N.runAllocationCount U x (xs ++ ys) i j k =
      N.runAllocationCount U x xs i j k +
        N.runAllocationCount U (N.runTokens U x xs) ys i j k := by
  induction xs generalizing x with
  | nil => simp [runAllocationCount, runTokens]
  | cons jk xs ih =>
      simp only [List.cons_append, runAllocationCount, runTokens]
      rw [ih]
      omega

private theorem runAllocationCount_incompatible {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    N.runAllocationCount U x tokens i j k = 0 := by
  induction tokens generalizing x with
  | nil => rfl
  | cons jk rest ih =>
      simp only [runAllocationCount]
      have hne :
          Not (U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k) := by
        rintro ⟨haction, hj, _⟩
        have hlegal := U.legal x jk.1 jk.2
        rw [haction] at hlegal
        exact hij (hj ▸ hlegal.1)
      simp [hne, ih (N.queueStep U x jk)]

private theorem runAllocationCount_le_count {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer) :
    N.runAllocationCount U x tokens i j k <= tokens.count (j, k) := by
  induction tokens generalizing x with
  | nil => simp [runAllocationCount]
  | cons jk rest ih =>
      have htail := ih (N.queueStep U x jk)
      by_cases hmatch : jk = (j, k)
      · subst jk
        simp only [runAllocationCount, List.count_cons, beq_self_eq_true,
          if_true]
        by_cases haction : U x j k = some i
        · simp only [haction, true_and, if_true]
          omega
        · simp only [haction, false_and, if_false, zero_add]
          omega
      · have hbeq : (jk == (j, k)) = false :=
          beq_eq_false_iff_ne.mpr hmatch
        have halloc :
            Not (U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k) := by
          rintro ⟨_, hj, hk⟩
          exact hmatch (Prod.ext hj hk)
        simp only [runAllocationCount, List.count_cons, hbeq, if_false,
          halloc, zero_add]
        exact htail

private theorem oneStep_incoming {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun q : Buffer =>
        if U x jk.1 jk.2 = some q /\ jk.1 = j /\ jk.2 = i
        then (1 : Real) else 0) =
      match U x jk.1 jk.2 with
      | none => 0
      | some _ => if jk.2 = i then 1 else 0 := by
  classical
  cases haction : U x jk.1 jk.2 with
  | none => simp [haction]
  | some q =>
      by_cases hki : jk.2 = i
      · subst i
        rw [Finset.sum_eq_single jk.1]
        · rw [Finset.sum_eq_single q]
          · simp [haction]
          · intro b _ hb
            have hb' : q ≠ b := Ne.symm hb
            simp [haction, hb']
          · simp
        · intro s _ hs
          have hs' : jk.1 ≠ s := Ne.symm hs
          simp [haction, hs']
        · simp
      · simp only [haction, hki, if_false]
        apply Finset.sum_eq_zero
        intro s _
        apply Finset.sum_eq_zero
        intro q' _
        simp [hki]

private theorem oneStep_outgoing {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        if U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k
        then (1 : Real) else 0) =
      if U x jk.1 jk.2 = some i then 1 else 0 := by
  classical
  by_cases hi : U x jk.1 jk.2 = some i
  · rw [Finset.sum_eq_single jk.1]
    · rw [Finset.sum_eq_single jk.2]
      · simp [hi]
      · intro k _ hk
        have hk' : jk.2 ≠ k := Ne.symm hk
        simp [hi, hk']
      · simp
    · intro j _ hj
      have hj' : jk.1 ≠ j := Ne.symm hj
      simp [hi, hj']
    · simp
  · simp [hi]

private theorem queueStep_coordinate_sub {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    ((N.queueStep U x jk i : Nat) : Real) - (x i : Real) =
      (match U x jk.1 jk.2 with
        | none => 0
        | some _ => if jk.2 = i then 1 else 0) -
      (if U x jk.1 jk.2 = some i then 1 else 0) := by
  have h := N.jobsIn_queueStep_sub U x ({i} : Finset Buffer) jk
  cases haction : U x jk.1 jk.2 with
  | none => simpa [JobState.jobsIn, cutChange, haction] using h
  | some q =>
      by_cases hqi : q = i
      · subst q
        simpa [JobState.jobsIn, cutChange, haction] using h
      · simpa [JobState.jobsIn, cutChange, haction, hqi] using h

/-- Exact queue balance along an arbitrary finite token list. -/
theorem runTokens_runAllocationCount_balance {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) :
    ((N.runTokens U x tokens i : Nat) : Real) - (x i : Real) =
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          (N.runAllocationCount U x tokens q j i : Nat)) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (N.runAllocationCount U x tokens i j k : Nat)) := by
  classical
  induction tokens generalizing x with
  | nil => simp [runTokens, runAllocationCount]
  | cons jk rest ih =>
      let xnext := N.queueStep U x jk
      have htail := ih xnext
      have hstep := queueStep_coordinate_sub N U x jk i
      have hin := oneStep_incoming N U x jk i
      have hout := oneStep_outgoing N U x jk i
      simp only [runTokens, runAllocationCount, Nat.cast_add,
        Finset.sum_add_distrib]
      change
        ((N.runTokens U xnext rest i : Nat) : Real) - (x i : Real) = _
      change
        ((N.runTokens U xnext rest i : Nat) : Real) -
            ((xnext i : Nat) : Real) = _ at htail
      change ((xnext i : Nat) : Real) - (x i : Real) = _ at hstep
      rw [show
        ((N.runTokens U xnext rest i : Nat) : Real) - (x i : Real) =
          (((N.runTokens U xnext rest i : Nat) : Real) -
            ((xnext i : Nat) : Real)) +
          (((xnext i : Nat) : Real) - (x i : Real)) by ring]
      rw [htail, hstep, <- hin, <- hout]
      push_cast
      ring

private theorem oneStep_total {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        Finset.univ.sum fun i : Buffer =>
          if U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k
          then 1 else 0) <= 1 := by
  classical
  cases haction : U x jk.1 jk.2 with
  | none => simp [haction]
  | some q =>
      rw [Finset.sum_eq_single jk.1]
      · rw [Finset.sum_eq_single jk.2]
        · rw [Finset.sum_eq_single q]
          · simp [haction]
          · intro i _ hi
            have hi' : q ≠ i := Ne.symm hi
            simp [haction, hi']
          · simp
        · intro k _ hk
          have hk' : jk.2 ≠ k := Ne.symm hk
          simp [haction, hk']
        · simp
      · intro j _ hj
        have hj' : jk.1 ≠ j := Ne.symm hj
        simp [haction, hj']
      · simp

private theorem sum_runAllocationCount_le_length {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        Finset.univ.sum fun i : Buffer =>
          N.runAllocationCount U x tokens i j k) <= tokens.length := by
  classical
  induction tokens generalizing x with
  | nil => simp [runAllocationCount]
  | cons jk rest ih =>
      simp only [runAllocationCount, Finset.sum_add_distrib,
        List.length_cons]
      have htail := ih (N.queueStep U x jk)
      have hone := oneStep_total N U x jk
      omega

private theorem runTokens_l1_le_two_mul_length {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    (Finset.univ.sum fun i : Buffer =>
      abs (((N.runTokens U x tokens i : Nat) : Real) - (x i : Real))) <=
      2 * tokens.length := by
  classical
  let incoming : Buffer -> Real := fun i =>
    Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun q : Buffer =>
        (N.runAllocationCount U x tokens q j i : Nat)
  let outgoing : Buffer -> Real := fun i =>
    Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        (N.runAllocationCount U x tokens i j k : Nat)
  have hcoord (i : Buffer) :
      abs (((N.runTokens U x tokens i : Nat) : Real) - (x i : Real)) <=
        incoming i + outgoing i := by
    rw [runTokens_runAllocationCount_balance N U x tokens i]
    push_cast
    change abs (incoming i - outgoing i) <= incoming i + outgoing i
    rw [abs_sub_le_iff]
    have hin0 : 0 <= incoming i := by
      dsimp [incoming]
      positivity
    have hout0 : 0 <= outgoing i := by
      dsimp [outgoing]
      positivity
    constructor <;> linarith
  calc
    (Finset.univ.sum fun i : Buffer =>
        abs (((N.runTokens U x tokens i : Nat) : Real) - (x i : Real))) <=
        Finset.univ.sum fun i : Buffer => incoming i + outgoing i :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = 2 * (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer =>
            Finset.univ.sum fun i : Buffer =>
              ((N.runAllocationCount U x tokens i j k : Nat) : Real)) := by
      have hin :
          (Finset.univ.sum fun i : Buffer => incoming i) =
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer =>
                Finset.univ.sum fun i : Buffer =>
                  ((N.runAllocationCount U x tokens i j k : Nat) : Real)) := by
        dsimp [incoming]
        rw [Finset.sum_comm]
      have hout :
          (Finset.univ.sum fun i : Buffer => outgoing i) =
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer =>
                Finset.univ.sum fun i : Buffer =>
                  ((N.runAllocationCount U x tokens i j k : Nat) : Real)) := by
        dsimp [outgoing]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      rw [Finset.sum_add_distrib, hin, hout]
      ring
    _ <= 2 * tokens.length := by
      exact_mod_cast Nat.mul_le_mul_left 2
        (sum_runAllocationCount_le_length N U x tokens)

private theorem runTokens_batch_l1_le_two_mul_length {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (pre batch :
      List (TokenType (Buffer := Buffer) (Server := Server))) :
    (Finset.univ.sum fun i : Buffer =>
      abs (((N.runTokens U x (pre ++ batch) i : Nat) : Real) -
        ((N.runTokens U x pre i : Nat) : Real))) <=
      2 * batch.length := by
  rw [runTokens_append]
  exact runTokens_l1_le_two_mul_length N U
    (N.runTokens U x pre) batch

/-! ### Finite prescribed-input approximations -/

private noncomputable def gridTime
    (T : Real) (K : PNat) (l : Nat) : Real :=
  T * ((min l (K : Nat) : Nat) : Real) / (K : Nat)

private noncomputable def gridInputCount
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) (j : Server) (k : Buffer) : Nat :=
  Nat.floor (((K : Nat) : Real) * A (gridTime T K l) j k)

private noncomputable def gridTokenBatch
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  (Finset.univ :
      Finset (TokenType (Buffer := Buffer) (Server := Server))).toList.flatMap
    fun jk =>
      List.replicate
        (gridInputCount T A K (l + 1) jk.1 jk.2 -
          gridInputCount T A K l jk.1 jk.2)
        jk

private noncomputable def gridTokenPrefix
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) : Nat ->
      List (TokenType (Buffer := Buffer) (Server := Server))
  | 0 => []
  | l + 1 =>
      gridTokenPrefix T A K l ++ gridTokenBatch T A K l

private theorem gridTime_mem_Icc
    {T : Real} (hT : 0 < T) (K : PNat) (l : Nat) :
    gridTime T K l ∈ Icc (0 : Real) T := by
  unfold gridTime
  have hK : 0 < ((K : Nat) : Real) := by
    exact_mod_cast K.property
  have hmin : min l (K : Nat) <= (K : Nat) := min_le_right _ _
  constructor
  · positivity
  · apply (div_le_iff₀ hK).2
    have hcast : ((min l (K : Nat) : Nat) : Real) <= (K : Nat) := by
      exact_mod_cast hmin
    nlinarith

private theorem gridTime_mono
    {T : Real} (hT : 0 < T) (K : PNat) {l m : Nat} (hlm : l <= m) :
    gridTime T K l <= gridTime T K m := by
  unfold gridTime
  have hK : 0 < ((K : Nat) : Real) := by
    exact_mod_cast K.property
  apply (div_le_div_iff_of_pos_right hK).2
  apply mul_le_mul_of_nonneg_left
  · exact_mod_cast min_le_min hlm (le_refl (K : Nat))
  · exact hT.le

private theorem gridInputCount_mono
    {T : Real} (hT : 0 < T) {A : MatrixPath Server Buffer}
    (hA : IsFluidInput T A) (K : PNat) {l m : Nat} (hlm : l <= m)
    (j : Server) (k : Buffer) :
    gridInputCount T A K l j k <= gridInputCount T A K m j k := by
  unfold gridInputCount
  apply Nat.floor_mono
  apply mul_le_mul_of_nonneg_left
  · exact hA.2.1 j k
      (gridTime_mem_Icc hT K l) (gridTime_mem_Icc hT K m)
      (gridTime_mono hT K hlm)
  · exact Nat.cast_nonneg _

private theorem gridInputCount_zero
    {T : Real} {A : MatrixPath Server Buffer}
    (hA : IsFluidInput T A) (K : PNat) (j : Server) (k : Buffer) :
    gridInputCount T A K 0 j k = 0 := by
  unfold gridInputCount gridTime
  simp [hA.2.2 j k]

private theorem count_flatMap_replicate_of_nodup
    {Alpha : Type*} [BEq Alpha] [LawfulBEq Alpha]
    (n : Alpha -> Nat) (xs : List Alpha) (hxs : xs.Nodup)
    (a : Alpha) :
    (xs.flatMap fun b => List.replicate (n b) b).count a =
      if a ∈ xs then n a else 0 := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
      have hb : b ∉ xs := List.nodup_cons.mp hxs |>.1
      have htail : xs.Nodup := List.nodup_cons.mp hxs |>.2
      simp only [List.flatMap_cons, List.count_append, List.count_replicate]
      rw [ih htail]
      by_cases hab : a = b
      · subst a
        simp [hb]
      · have hba : b ≠ a := Ne.symm hab
        simp [hab, hba]

private theorem gridTokenBatch_count
    {T : Real} (hT : 0 < T) {A : MatrixPath Server Buffer}
    (hA : IsFluidInput T A) (K : PNat) (l : Nat)
    (j : Server) (k : Buffer) :
    (gridTokenBatch T A K l).count (j, k) =
      gridInputCount T A K (l + 1) j k -
        gridInputCount T A K l j k := by
  classical
  unfold gridTokenBatch
  simpa using
    count_flatMap_replicate_of_nodup
      (fun jk : Server × Buffer =>
        gridInputCount T A K (l + 1) jk.1 jk.2 -
          gridInputCount T A K l jk.1 jk.2)
      (Finset.univ.toList) (Finset.nodup_toList _) (j, k)

private theorem gridTokenPrefix_count
    {T : Real} (hT : 0 < T) {A : MatrixPath Server Buffer}
    (hA : IsFluidInput T A) (K : PNat) (l : Nat)
    (j : Server) (k : Buffer) :
    (gridTokenPrefix T A K l).count (j, k) =
      gridInputCount T A K l j k := by
  induction l with
  | zero =>
      simp [gridTokenPrefix, gridInputCount_zero hA K j k]
  | succ l ih =>
      rw [gridTokenPrefix, List.count_append, ih,
        gridTokenBatch_count hT hA K l j k]
      exact Nat.add_sub_of_le
        (gridInputCount_mono hT hA K (Nat.le_succ l) j k)

private theorem gridTokenBatch_length
    {T : Real} (hT : 0 < T) {A : MatrixPath Server Buffer}
    (hA : IsFluidInput T A) (K : PNat) (l : Nat) :
    (gridTokenBatch T A K l).length =
      Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (gridInputCount T A K (l + 1) j k -
            gridInputCount T A K l j k) := by
  classical
  let d : Server × Buffer -> Nat := fun jk =>
    gridInputCount T A K (l + 1) jk.1 jk.2 -
      gridInputCount T A K l jk.1 jk.2
  calc
    (gridTokenBatch T A K l).length =
        Finset.univ.sum d := by
      simp [gridTokenBatch, d]
    _ = Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (gridInputCount T A K (l + 1) j k -
            gridInputCount T A K l j k) := by
      have hprod :
          (Finset.univ : Finset (Server × Buffer)) =
            (Finset.univ : Finset Server).product
              (Finset.univ : Finset Buffer) := by
        ext jk
        simp
      rw [hprod]
      simpa [d] using
        Finset.sum_product
          (Finset.univ : Finset Server)
          (Finset.univ : Finset Buffer) d

private noncomputable def gridQueueState
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) : JobState Buffer (K : Nat) :=
  let i0 : Buffer := Classical.choice (inferInstance : Nonempty Buffer)
  N.runTokens (U K) (roundedState x0 K i0)
    (gridTokenPrefix T A K l)

private noncomputable def gridAllocationCount
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) : Nat :=
  let i0 : Buffer := Classical.choice (inferInstance : Nonempty Buffer)
  N.runAllocationCount (U K) (roundedState x0 K i0)
    (gridTokenPrefix T A K l) i j k

private theorem gridAllocationCount_incompatible
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (K : PNat) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    gridAllocationCount N T x0 U A K l i j k = 0 := by
  unfold gridAllocationCount
  exact runAllocationCount_incompatible N _ _ _ i j k hij

private theorem gridAllocationCount_le_input
    (N : Network Buffer Server)
    {T : Real} (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {A : MatrixPath Server Buffer} (hA : IsFluidInput T A)
    (K : PNat) (l : Nat) (i : Buffer) (j : Server) (k : Buffer) :
    gridAllocationCount N T x0 U A K l i j k <=
      gridInputCount T A K l j k := by
  unfold gridAllocationCount
  calc
    N.runAllocationCount (U K)
        (roundedState x0 (K : Nat)
          (Classical.choice (inferInstance : Nonempty Buffer)))
        (gridTokenPrefix T A K l) i j k <=
        (gridTokenPrefix T A K l).count (j, k) :=
      runAllocationCount_le_count N _ _ _ i j k
    _ = gridInputCount T A K l j k :=
      gridTokenPrefix_count hT hA K l j k

private theorem gridQueueState_isFluidState
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (K : PNat) (l : Nat) :
    IsFluidState
      (fun i => (gridQueueState N T x0 U A K l i : Real) / (K : Nat)) := by
  constructor
  · intro i
    positivity
  · rw [<- Finset.sum_div]
    have hsum :
        Finset.univ.sum
          (fun i => (gridQueueState N T x0 U A K l i : Nat)) =
            (K : Nat) :=
      (gridQueueState N T x0 U A K l).total_jobs
    rw [show
      Finset.univ.sum
          (fun i => ((gridQueueState N T x0 U A K l i : Nat) : Real)) =
        ((Finset.univ.sum
          (fun i => (gridQueueState N T x0 U A K l i : Nat)) : Nat) :
            Real) by
              exact (Nat.cast_sum
                (f := fun i =>
                  (gridQueueState N T x0 U A K l i : Nat))
                Finset.univ).symm]
    rw [hsum]
    exact div_self (by exact_mod_cast K.ne_zero)

private theorem gridQueueState_scaled_balance
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (K : PNat) (l : Nat)
    (i : Buffer) :
    ((gridQueueState N T x0 U A K l i : Nat) : Real) / (K : Nat) =
      ((roundedState x0 (K : Nat)
        (Classical.choice (inferInstance : Nonempty Buffer)) i : Nat) :
          Real) / (K : Nat) +
      ((Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          (gridAllocationCount N T x0 U A K l q j i : Real)) /
            (K : Nat)) -
      ((Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (gridAllocationCount N T x0 U A K l i j k : Real)) /
            (K : Nat)) := by
  let i0 : Buffer := Classical.choice (inferInstance : Nonempty Buffer)
  have hbalance :=
    runTokens_runAllocationCount_balance N (U K)
      (roundedState x0 (K : Nat) i0)
      (gridTokenPrefix T A K l) i
  unfold gridQueueState gridAllocationCount
  dsimp only
  change
    ((N.runTokens (U K) (roundedState x0 (K : Nat) i0)
        (gridTokenPrefix T A K l) i : Nat) : Real) / (K : Nat) = _
  change
    ((N.runTokens (U K) (roundedState x0 (K : Nat) i0)
        (gridTokenPrefix T A K l) i : Nat) : Real) -
      ((roundedState x0 (K : Nat) i0 i : Nat) : Real) = _ at hbalance
  have hK : ((K : Nat) : Real) ≠ 0 := by
    exact_mod_cast K.ne_zero
  dsimp [i0] at hbalance ⊢
  push_cast at hbalance
  simp_rw [div_eq_mul_inv]
  linear_combination (((K : Nat) : Real)⁻¹) * hbalance

private theorem gridAllocationCount_succ_sub_le
    (N : Network Buffer Server)
    {T : Real} (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {A : MatrixPath Server Buffer} (hA : IsFluidInput T A)
    (K : PNat) (l : Nat) (i : Buffer) (j : Server) (k : Buffer) :
    gridAllocationCount N T x0 U A K (l + 1) i j k -
        gridAllocationCount N T x0 U A K l i j k <=
      gridInputCount T A K (l + 1) j k -
        gridInputCount T A K l j k := by
  let i0 : Buffer := Classical.choice (inferInstance : Nonempty Buffer)
  have happend :=
    runAllocationCount_append N (U K)
      (roundedState x0 (K : Nat) i0)
      (gridTokenPrefix T A K l) (gridTokenBatch T A K l) i j k
  have htail :=
    runAllocationCount_le_count N (U K)
      (N.runTokens (U K) (roundedState x0 (K : Nat) i0)
        (gridTokenPrefix T A K l))
      (gridTokenBatch T A K l) i j k
  unfold gridAllocationCount
  change
    N.runAllocationCount (U K) (roundedState x0 (K : Nat) i0)
      (gridTokenPrefix T A K l ++ gridTokenBatch T A K l) i j k -
      N.runAllocationCount (U K) (roundedState x0 (K : Nat) i0)
        (gridTokenPrefix T A K l) i j k <= _ 
  rw [happend, Nat.add_sub_cancel_left]
  rw [gridTokenBatch_count hT hA K l j k] at htail
  exact htail

private theorem gridQueueState_succ_l1_le
    (N : Network Buffer Server)
    {T : Real} (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {A : MatrixPath Server Buffer} (hA : IsFluidInput T A)
    (K : PNat) (l : Nat) :
    (Finset.univ.sum fun i : Buffer =>
      abs (((gridQueueState N T x0 U A K (l + 1) i : Nat) : Real) -
        ((gridQueueState N T x0 U A K l i : Nat) : Real))) <=
      2 * (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (gridInputCount T A K (l + 1) j k -
            gridInputCount T A K l j k)) := by
  let i0 : Buffer := Classical.choice (inferInstance : Nonempty Buffer)
  have hrun :=
    runTokens_batch_l1_le_two_mul_length N (U K)
      (roundedState x0 (K : Nat) i0)
      (gridTokenPrefix T A K l) (gridTokenBatch T A K l)
  unfold gridQueueState
  rw [gridTokenPrefix.eq_def]
  change
    (Finset.univ.sum fun i : Buffer =>
      abs (((N.runTokens (U K) (roundedState x0 (K : Nat) i0)
        (gridTokenPrefix T A K l ++ gridTokenBatch T A K l) i :
          Nat) : Real) -
        ((N.runTokens (U K) (roundedState x0 (K : Nat) i0)
          (gridTokenPrefix T A K l) i : Nat) : Real))) <= _
  rw [gridTokenBatch_length hT hA K l] at hrun
  exact hrun

/-- Standard compactly supported hat weight for polygonal interpolation. -/
private def hatWeight (r : Real) (l : Nat) : Real :=
  max 0 (1 - abs (r - l))

private noncomputable def polygonalInterpolate
    (K : PNat) (values : Nat -> Real) (t T : Real) : Real :=
  Finset.sum (Finset.range ((K : Nat) + 1)) fun l =>
    hatWeight (((K : Nat) : Real) * t / T) l * values l

private theorem continuous_hatWeight (l : Nat) :
    Continuous (fun r : Real => hatWeight r l) := by
  unfold hatWeight
  fun_prop

private theorem continuous_polygonalInterpolate
    (K : PNat) (values : Nat -> Real) (T : Real) :
    Continuous (fun t => polygonalInterpolate K values t T) := by
  unfold polygonalInterpolate
  apply continuous_finset_sum
  intro l hl
  apply Continuous.mul
  · apply (continuous_hatWeight l).comp
    fun_prop
  · exact continuous_const

private theorem hatWeight_eq_zero_of_one_le_abs
    {r : Real} {l : Nat} (h : 1 <= abs (r - l)) :
    hatWeight r l = 0 := by
  unfold hatWeight
  rw [max_eq_left]
  linarith

private theorem sum_hatWeight_eq_one
    (K : PNat) {r : Real}
    (hr0 : 0 <= r) (hrK : r <= (K : Nat)) :
    Finset.sum (Finset.range ((K : Nat) + 1)) (hatWeight r) = 1 := by
  classical
  let n : Nat := Nat.floor r
  have hn_le : (n : Real) <= r := Nat.floor_le hr0
  have hr_lt : r < (n : Real) + 1 := Nat.lt_floor_add_one r
  by_cases heq : r = (K : Nat)
  · subst r
    rw [Finset.sum_eq_single (K : Nat)]
    · simp [hatWeight]
    · intro l hl hlne
      have hlK : l < (K : Nat) + 1 := Finset.mem_range.mp hl
      have hl_le : l <= (K : Nat) := by omega
      have hgap : (1 : Real) <= abs (((K : Nat) : Real) - l) := by
        rw [abs_of_nonneg]
        · have hcast : (l : Real) + 1 <= (K : Nat) := by
            exact_mod_cast (show l + 1 <= (K : Nat) by omega)
          linarith
        · have hcast : (l : Real) <= (K : Nat) := by
            exact_mod_cast hl_le
          linarith
      exact hatWeight_eq_zero_of_one_le_abs hgap
    · simp
  · have hrKlt : r < (K : Nat) := lt_of_le_of_ne hrK heq
    have hnK : n < (K : Nat) := (Nat.floor_lt hr0).2 hrKlt
    have hsubset :
        ({n, n + 1} : Finset Nat) <=
          Finset.range ((K : Nat) + 1) := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact Finset.mem_range.mpr (by omega)
      · exact Finset.mem_range.mpr (by omega)
    have hzero :
        forall l, l ∈ Finset.range ((K : Nat) + 1) ->
          l ∉ ({n, n + 1} : Finset Nat) -> hatWeight r l = 0 := by
      intro l hl hlpair
      have hln : Not (l = n) := by
        intro h
        apply hlpair
        simp [h]
      have hln1 : Not (l = n + 1) := by
        intro h
        apply hlpair
        simp [h]
      have hgap : (1 : Real) <= abs (r - l) := by
        by_cases hlt : l < n
        · have hcast : (l : Real) + 1 <= n := by
            exact_mod_cast (show l + 1 <= n by omega)
          rw [abs_of_nonneg]
          · linarith
          · linarith
        · have hnlt : n + 1 < l := by omega
          have hcast : (n : Real) + 2 <= l := by
            exact_mod_cast (show n + 2 <= l by omega)
          rw [abs_of_nonpos]
          · linarith
          · linarith
      exact hatWeight_eq_zero_of_one_le_abs hgap
    rw [<- Finset.sum_subset hsubset hzero]
    rw [Finset.sum_pair (by omega : Not (n = n + 1))]
    have hleft_nonneg : 0 <= 1 - abs (r - (n : Real)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hn_le)]
      linarith
    have hright_nonneg :
        0 <= 1 - abs (r - ((n + 1 : Nat) : Real)) := by
      rw [abs_of_nonpos]
      · norm_num at *
        linarith
      · norm_num at *
        linarith
    simp only [hatWeight, max_eq_right hleft_nonneg,
      max_eq_right hright_nonneg]
    rw [abs_of_nonneg (sub_nonneg.mpr hn_le), abs_of_nonpos]
    · norm_num at *
      ring
    · norm_num at *
      linarith

private theorem hatWeight_nonnegative (r : Real) (l : Nat) :
    0 <= hatWeight r l :=
  le_max_left _ _

private theorem polygonalInterpolate_bounds
    (K : PNat) (values : Nat -> Real) {t T lower upper : Real}
    (hT : 0 < T) (ht : t ∈ Set.Icc (0 : Real) T)
    (hlower : forall l, l < (K : Nat) + 1 -> lower <= values l)
    (hupper : forall l, l < (K : Nat) + 1 -> values l <= upper) :
    polygonalInterpolate K values t T ∈ Set.Icc lower upper := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) ht.1)
      (le_of_lt hT)
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hsum :
      Finset.sum (Finset.range ((K : Nat) + 1)) (hatWeight r) = 1 :=
    sum_hatWeight_eq_one K hr0 hrK
  constructor
  · calc
      lower = Finset.sum (Finset.range ((K : Nat) + 1))
          (fun l => hatWeight r l * lower) := by
            rw [<- Finset.sum_mul, hsum, one_mul]
      _ <= polygonalInterpolate K values t T := by
            unfold polygonalInterpolate
            apply Finset.sum_le_sum
            intro l hl
            apply mul_le_mul_of_nonneg_left
            · exact hlower l (Finset.mem_range.mp hl)
            · exact hatWeight_nonnegative r l
  · calc
      polygonalInterpolate K values t T <=
          Finset.sum (Finset.range ((K : Nat) + 1))
            (fun l => hatWeight r l * upper) := by
              unfold polygonalInterpolate
              apply Finset.sum_le_sum
              intro l hl
              apply mul_le_mul_of_nonneg_left
              · exact hupper l (Finset.mem_range.mp hl)
              · exact hatWeight_nonnegative r l
      _ = upper := by rw [<- Finset.sum_mul, hsum, one_mul]

private noncomputable def polygonalQueuePath
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer)
    (K : PNat) : FluidStatePath Buffer :=
  fun t i =>
    polygonalInterpolate K
      (fun l => (gridQueueState N T x0 U A K l i : Real) / (K : Nat))
      t T

private noncomputable def polygonalAllocationPath
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer)
    (K : PNat) : FluidAllocationPath Buffer Server :=
  fun t i j k =>
    polygonalInterpolate K
      (fun l =>
        (gridAllocationCount N T x0 U A K l i j k : Real) / (K : Nat))
      t T

private noncomputable def polygonalInputPath
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) : MatrixPath Server Buffer :=
  fun t j k =>
    polygonalInterpolate K
      (fun l => (gridInputCount T A K l j k : Real) / (K : Nat))
      t T

private theorem continuous_polygonalQueuePath
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (K : PNat) (i : Buffer) :
    Continuous (fun t => polygonalQueuePath N T x0 U A K t i) :=
  continuous_polygonalInterpolate K _ T

private theorem continuous_polygonalAllocationPath
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (K : PNat)
    (i : Buffer) (j : Server) (k : Buffer) :
    Continuous (fun t =>
      polygonalAllocationPath N T x0 U A K t i j k) :=
  continuous_polygonalInterpolate K _ T

private theorem continuous_polygonalInputPath
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) (j : Server) (k : Buffer) :
    Continuous (fun t => polygonalInputPath T A K t j k) :=
  continuous_polygonalInterpolate K _ T

private theorem polygonalQueuePath_isFluidState
    (N : Network Buffer Server)
    {T : Real} (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (K : PNat)
    {t : Real} (ht : t ∈ Icc (0 : Real) T) :
    IsFluidState (polygonalQueuePath N T x0 U A K t) := by
  have hcoord (l : Nat) (hl : l < (K : Nat) + 1) (i : Buffer) :
      ((gridQueueState N T x0 U A K l i : Nat) : Real) /
          (K : Nat) ∈ Icc (0 : Real) 1 := by
    constructor
    · positivity
    · apply (div_le_one (by exact_mod_cast K.property)).2
      exact_mod_cast (gridQueueState N T x0 U A K l).coordinate_le i
  constructor
  · intro i
    exact (polygonalInterpolate_bounds K _ hT ht
      (fun l hl => (hcoord l hl i).1)
      (fun l hl => (hcoord l hl i).2)).1
  · let r : Real := ((K : Nat) : Real) * t / T
    have hr0 : 0 <= r := by
      dsimp [r]
      exact div_nonneg
        (mul_nonneg (Nat.cast_nonneg _) ht.1) hT.le
    have hrK : r <= (K : Nat) := by
      dsimp [r]
      apply (div_le_iff₀ hT).2
      nlinarith [ht.2]
    have hweights :
        Finset.sum (Finset.range ((K : Nat) + 1)) (hatWeight r) = 1 :=
      sum_hatWeight_eq_one K hr0 hrK
    unfold polygonalQueuePath polygonalInterpolate
    simp only
    change
      Finset.univ.sum
        (fun i =>
          Finset.sum (Finset.range ((K : Nat) + 1))
            (fun l =>
              hatWeight r l *
                (((gridQueueState N T x0 U A K l i : Nat) : Real) /
                  (K : Nat)))) = 1
    simp_rw [<- mul_div_assoc]
    rw [Finset.sum_comm]
    calc
      (Finset.range ((K : Nat) + 1)).sum
          (fun l =>
            Finset.univ.sum
              (fun i =>
                hatWeight r l *
                  ((gridQueueState N T x0 U A K l i : Nat) : Real) /
                    (K : Nat))) =
          (Finset.range ((K : Nat) + 1)).sum (hatWeight r) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [show
              Finset.univ.sum
                  (fun i =>
                    hatWeight r l *
                      ((gridQueueState N T x0 U A K l i : Nat) : Real) /
                        (K : Nat)) =
                hatWeight r l *
                  Finset.univ.sum
                    (fun i =>
                      ((gridQueueState N T x0 U A K l i : Nat) : Real) /
                        (K : Nat)) by
              simp_rw [mul_div_assoc]
              exact (Finset.mul_sum _ _ _).symm]
            rw [(gridQueueState_isFluidState N T x0 U A K l).2, mul_one]
      _ = 1 := hweights

private theorem polygonalAllocationPath_incompatible
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (K : PNat)
    (t : Real) (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    polygonalAllocationPath N T x0 U A K t i j k = 0 := by
  unfold polygonalAllocationPath polygonalInterpolate
  apply Finset.sum_eq_zero
  intro l hl
  simp only
  rw [gridAllocationCount_incompatible N T x0 U A K l i j k hij]
  simp

private theorem polygonalQueuePath_balance
    (N : Network Buffer Server)
    {T : Real} (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (K : PNat)
    {t : Real} (ht : t ∈ Icc (0 : Real) T) (i : Buffer) :
    polygonalQueuePath N T x0 U A K t i =
      ((roundedState x0 (K : Nat)
        (Classical.choice (inferInstance : Nonempty Buffer)) i : Nat) :
          Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          polygonalAllocationPath N T x0 U A K t q j i) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          polygonalAllocationPath N T x0 U A K t i j k) := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) ht.1) hT.le
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hweights :
      Finset.sum (Finset.range ((K : Nat) + 1)) (hatWeight r) = 1 :=
    sum_hatWeight_eq_one K hr0 hrK
  unfold polygonalQueuePath polygonalAllocationPath
  unfold polygonalInterpolate
  simp only
  change
    Finset.sum (Finset.range ((K : Nat) + 1))
        (fun l => hatWeight r l *
          (((gridQueueState N T x0 U A K l i : Nat) : Real) /
            (K : Nat))) =
      ((roundedState x0 (K : Nat)
        (Classical.choice (inferInstance : Nonempty Buffer)) i : Nat) :
          Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          Finset.sum (Finset.range ((K : Nat) + 1))
            (fun l => hatWeight r l *
              ((gridAllocationCount N T x0 U A K l q j i : Real) /
                (K : Nat)))) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          Finset.sum (Finset.range ((K : Nat) + 1))
            (fun l => hatWeight r l *
              ((gridAllocationCount N T x0 U A K l i j k : Real) /
                (K : Nat))))
  simp_rw [gridQueueState_scaled_balance N T x0 U A K]
  simp only [mul_sub, mul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show
    Finset.sum (Finset.range ((K : Nat) + 1))
        (fun l =>
          hatWeight r l *
            (((roundedState x0 (K : Nat)
              (Classical.choice (inferInstance : Nonempty Buffer)) i :
                Nat) : Real) / (K : Nat))) =
      ((roundedState x0 (K : Nat)
        (Classical.choice (inferInstance : Nonempty Buffer)) i : Nat) :
          Real) / (K : Nat) by
    rw [<- Finset.sum_mul, hweights, one_mul]]
  congr 1
  · simp_rw [Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
  · simp_rw [Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]

private theorem hatWeight_nat_ne {l q : Nat} (hql : q ≠ l) :
    hatWeight (l : Real) q = 0 := by
  have hgap : (1 : Real) <= abs ((l : Real) - q) := by
    rcases lt_or_gt_of_ne (Ne.symm hql) with hlq | hql'
    · rw [abs_of_nonpos]
      · have hcast : (l : Real) + 1 <= q := by
          exact_mod_cast (show l + 1 <= q by omega)
        linarith
      · apply sub_nonpos.mpr
        exact_mod_cast (show l <= q by omega)
    · rw [abs_of_nonneg]
      · have hcast : (q : Real) + 1 <= l := by
          exact_mod_cast (show q + 1 <= l by omega)
        linarith
      · apply sub_nonneg.mpr
        exact_mod_cast (show q <= l by omega)
  exact hatWeight_eq_zero_of_one_le_abs hgap

private theorem polygonalInterpolate_grid
    (K : PNat) (values : Nat -> Real) (T : Real) (hT : 0 < T)
    (l : Nat) (hl : l <= (K : Nat)) :
    polygonalInterpolate K values
      (T * (l : Real) / (K : Nat)) T = values l := by
  have hscale :
      ((K : Nat) : Real) * (T * (l : Real) / (K : Nat)) / T =
        (l : Real) := by
    have hK : ((K : Nat) : Real) ≠ 0 := by positivity
    field_simp
  unfold polygonalInterpolate
  rw [hscale, Finset.sum_eq_single l]
  · simp [hatWeight]
  · intro q hq hql
    simp [hatWeight_nat_ne hql]
  · simp only [Finset.mem_range]
    omega

private theorem gridTime_eq_gridPoint
    (T : Real) (K : PNat) (l : Nat) (hl : l <= (K : Nat)) :
    gridTime T K l = T * (l : Real) / (K : Nat) := by
  simp [gridTime, Nat.min_eq_left hl]

private theorem gridInputCount_approx
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat) (l : Nat)
    (j : Server) (k : Buffer) :
    abs ((gridInputCount T A K l j k : Real) / (K : Nat) -
      A (gridTime T K l) j k) < 1 / (K : Nat) := by
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hnonneg : 0 <= A (gridTime T K l) j k := by
    have hzero := hA.2.2 j k
    rw [<- hzero]
    exact hA.2.1 j k
      (by exact ⟨le_rfl, hT.le⟩)
      (gridTime_mem_Icc hT K l)
      (gridTime_mem_Icc hT K l).1
  have hlo :
      ((gridInputCount T A K l j k : Nat) : Real) <=
        (K : Real) * A (gridTime T K l) j k :=
    Nat.floor_le (mul_nonneg hK.le hnonneg)
  have hhi :
      (K : Real) * A (gridTime T K l) j k <
        (gridInputCount T A K l j k : Real) + 1 :=
    Nat.lt_floor_add_one _
  rw [show
    (gridInputCount T A K l j k : Real) / (K : Nat) -
        A (gridTime T K l) j k =
      ((gridInputCount T A K l j k : Real) -
        (K : Real) * A (gridTime T K l) j k) / (K : Nat) by
          field_simp]
  rw [abs_div, abs_of_pos hK]
  apply (div_lt_iff₀ hK).2
  rw [abs_lt]
  have hone : 1 / (K : Real) * (K : Real) = 1 := by field_simp
  rw [hone]
  constructor <;> linarith

private theorem hatWeight_ne_zero_distance
    (K : PNat) {T t : Real} (hT : 0 < T)
    {l : Nat} (hl : l < (K : Nat) + 1)
    (hw : hatWeight (((K : Nat) : Real) * t / T) l ≠ 0) :
    abs (gridTime T K l - t) <= T / (K : Nat) := by
  have hlK : l <= (K : Nat) := by omega
  rw [gridTime_eq_gridPoint T K l hlK]
  have habs :
      abs (((K : Nat) : Real) * t / T - l) < 1 := by
    by_contra h
    exact hw (hatWeight_eq_zero_of_one_le_abs (le_of_not_gt h))
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [show T * (l : Real) / (K : Nat) - t =
      (T * (l : Real) - t * (K : Nat)) / (K : Nat) by
        field_simp <;> ring]
  rw [abs_div, abs_of_pos hK]
  apply (div_le_iff₀ hK).2
  rw [div_mul_cancel₀ T (ne_of_gt hK), abs_le]
  rw [abs_lt] at habs
  have hu : ((K : Nat) : Real) * t / T < (l : Real) + 1 := by
    linarith
  have hlo : (l : Real) - 1 <
      ((K : Nat) : Real) * t / T := by linarith
  have hupper := (div_lt_iff₀ hT).1 hu
  have hlower := (lt_div_iff₀ hT).1 hlo
  constructor <;> push_cast at * <;> nlinarith

private theorem polygonalInputPath_uniform_error
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat)
    (j : Server) (k : Buffer) (eta : Real)
    (hosc : forall s, s ∈ Icc (0 : Real) T ->
      forall t, t ∈ Icc (0 : Real) T ->
        abs (s - t) <= T / (K : Nat) ->
        abs (A s j k - A t j k) <= eta)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    abs (polygonalInputPath T A K t j k - A t j k) <=
      eta + 1 / (K : Nat) := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) ht.1) hT.le
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hsum :
      Finset.sum (Finset.range ((K : Nat) + 1)) (hatWeight r) = 1 :=
    sum_hatWeight_eq_one K hr0 hrK
  have hterm (l : Nat) (hl : l ∈ Finset.range ((K : Nat) + 1)) :
      abs (hatWeight r l *
        ((gridInputCount T A K l j k : Real) / (K : Nat) -
          A t j k)) <=
        hatWeight r l * (eta + 1 / (K : Nat)) := by
    by_cases hw : hatWeight r l = 0
    · simp [hw]
    · rw [abs_mul, abs_of_nonneg (hatWeight_nonnegative r l)]
      apply mul_le_mul_of_nonneg_left _ (hatWeight_nonnegative r l)
      have hdist := hatWeight_ne_zero_distance K hT
        (Finset.mem_range.mp hl) hw
      have hosc' := hosc (gridTime T K l)
        (gridTime_mem_Icc hT K l) t ht hdist
      have happ := gridInputCount_approx T hT A hA K l j k
      calc
        abs ((gridInputCount T A K l j k : Real) / (K : Nat) -
            A t j k) <=
            abs ((gridInputCount T A K l j k : Real) / (K : Nat) -
              A (gridTime T K l) j k) +
            abs (A (gridTime T K l) j k - A t j k) := by
              simpa only [sub_add_sub_cancel] using
                abs_add_le
                  ((gridInputCount T A K l j k : Real) / (K : Nat) -
                    A (gridTime T K l) j k)
                  (A (gridTime T K l) j k - A t j k)
        _ <= 1 / (K : Nat) + eta := add_le_add (le_of_lt happ) hosc'
        _ = eta + 1 / (K : Nat) := add_comm _ _
  rw [show polygonalInputPath T A K t j k - A t j k =
      Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
        hatWeight r l *
          ((gridInputCount T A K l j k : Real) / (K : Nat) -
            A t j k)) by
      unfold polygonalInputPath polygonalInterpolate
      dsimp [r]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, <- Finset.sum_mul, hsum, one_mul]]
  calc
    abs (Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
        hatWeight r l *
          ((gridInputCount T A K l j k : Real) / (K : Nat) -
            A t j k))) <=
        Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
          abs (hatWeight r l *
            ((gridInputCount T A K l j k : Real) / (K : Nat) -
              A t j k))) := Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
          hatWeight r l * (eta + 1 / (K : Nat))) :=
      Finset.sum_le_sum hterm
    _ = eta + 1 / (K : Nat) := by
      rw [<- Finset.sum_mul, hsum, one_mul]

private theorem polygonalInputPath_uniform_convergence
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) :
    forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j k t, t ∈ Icc (0 : Real) T ->
          abs (polygonalInputPath T A
            ⟨n + 1, by omega⟩ t j k - A t j k) < epsilon := by
  let Avec : Real -> Server -> Buffer -> Real := fun t j k => A t j k
  have hcont : ContinuousOn Avec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro j
    rw [continuousOn_pi]
    intro k
    simpa [uIcc_of_le hT.le] using (hA.1 j k).continuousOn
  have huc : UniformContinuousOn Avec (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  have hrecip :
      Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1))
        atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmesh :
      Tendsto (fun n : Nat => T / ((n : Real) + 1))
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hrecip
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp huc (epsilon / 2) (by positivity)
  obtain ⟨nRecip, hnRecip⟩ :=
    Metric.tendsto_atTop.mp hrecip (epsilon / 2) (by positivity)
  obtain ⟨nMesh, hnMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh delta hdelta
  refine ⟨max nRecip nMesh, fun n hn j k t ht => ?_⟩
  have hnR : nRecip <= n := (le_max_left _ _).trans hn
  have hnM : nMesh <= n := (le_max_right _ _).trans hn
  have hrecipSmall :
      (1 : Real) / ((n : Real) + 1) < epsilon / 2 := by
    have h := hnRecip n hnR
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (by positivity : 0 <= (1 : Real) / ((n : Real) + 1))] at h
    exact h
  have hmeshSmall : T / ((n : Real) + 1) < delta := by
    have h := hnMesh n hnM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at h
    exact h
  let K : PNat := ⟨n + 1, by omega⟩
  have hosc :
      forall s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T ->
          abs (s - t) <= T / (K : Nat) ->
          abs (A s j k - A t j k) <= epsilon / 2 := by
    intro s hs t ht' hst
    have hdistTime : dist s t < delta := by
      rw [Real.dist_eq]
      exact hst.trans_lt
        (by simpa [K, Nat.cast_add, Nat.cast_one] using hmeshSmall)
    have hvec := hdeltaWorks s hs t ht' hdistTime
    have hj : dist (Avec s j) (Avec t j) <= dist (Avec s) (Avec t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s) (Avec t) <= dist (Avec s) (Avec t)) j
    have hk : dist (Avec s j k) (Avec t j k) <=
        dist (Avec s j) (Avec t j) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s j) (Avec t j) <=
          dist (Avec s j) (Avec t j)) k
    simpa [Avec, Real.dist_eq] using
      (hk.trans hj).trans (le_of_lt hvec)
  have herr :=
    polygonalInputPath_uniform_error T hT A hA K j k
      (epsilon / 2) hosc t ht
  have hrecipK : (1 : Real) / (K : Nat) < epsilon / 2 := by
    simpa [K, Nat.cast_add, Nat.cast_one] using hrecipSmall
  change abs (polygonalInputPath T A K t j k - A t j k) < epsilon
  exact herr.trans_lt (by linarith)

private def existenceClamp01 (r : Real) : Real :=
  min 1 (max 0 r)

private theorem existenceClamp01_monotone : Monotone existenceClamp01 := by
  intro a b hab
  simp only [existenceClamp01]
  exact min_le_min le_rfl (max_le_max le_rfl hab)

private theorem existenceClamp01_of_nonpos {r : Real} (hr : r <= 0) :
    existenceClamp01 r = 0 := by
  simp [existenceClamp01, max_eq_left hr]

private theorem existenceClamp01_of_one_le {r : Real} (hr : 1 <= r) :
    existenceClamp01 r = 1 := by
  rw [existenceClamp01, max_eq_right (le_trans zero_le_one hr),
    min_eq_left hr]

private noncomputable def existenceRampInterpolate
    (K : PNat) (values : Nat -> Real) (t T : Real) : Real :=
  values 0 +
    Finset.sum (Finset.range (K : Nat)) fun l =>
      (values (l + 1) - values l) *
        existenceClamp01 (((K : Nat) : Real) * t / T - l)

private theorem existenceRampInterpolate_grid
    (K : PNat) (values : Nat -> Real) (T : Real) (hT : 0 < T)
    (l : Nat) (hl : l <= (K : Nat)) :
    existenceRampInterpolate K values
      (T * (l : Real) / (K : Nat)) T = values l := by
  have hscale :
      ((K : Nat) : Real) * (T * (l : Real) / (K : Nat)) / T =
        (l : Real) := by
    have hK : ((K : Nat) : Real) ≠ 0 := by positivity
    field_simp
  unfold existenceRampInterpolate
  rw [hscale]
  have hbefore :
      Finset.sum (Finset.range l) (fun q =>
        (values (q + 1) - values q) *
          existenceClamp01 ((l : Real) - q)) =
        Finset.sum (Finset.range l) (fun q =>
          values (q + 1) - values q) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hq : q < l := Finset.mem_range.mp hq
    have hone : (1 : Real) <= (l : Real) - q := by
      have hcast : (q : Real) + 1 <= l := by
        exact_mod_cast (show q + 1 <= l by omega)
      linarith
    rw [existenceClamp01_of_one_le hone, mul_one]
  have hafter :
      forall q, q ∈ Finset.range (K : Nat) ->
        q ∉ Finset.range l ->
        (values (q + 1) - values q) *
          existenceClamp01 ((l : Real) - q) = 0 := by
    intro q hq hnot
    have hlq : l <= q := by
      simpa only [Finset.mem_range, not_lt] using hnot
    have hcast : (l : Real) <= q := by exact_mod_cast hlq
    have hnonpos : (l : Real) - q <= 0 := sub_nonpos.mpr hcast
    rw [existenceClamp01_of_nonpos hnonpos, mul_zero]
  rw [<- Finset.sum_subset (Finset.range_mono hl) hafter, hbefore]
  rw [Finset.sum_range_sub]
  ring

private theorem polygonalInterpolate_eq_ramp
    (K : PNat) (values : Nat -> Real) {t T : Real}
    (hT : 0 < T) (ht : t ∈ Icc (0 : Real) T) :
    polygonalInterpolate K values t T =
      existenceRampInterpolate K values t T := by
  classical
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) ht.1) hT.le
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  by_cases heq : r = (K : Nat)
  · have htT : t = T := by
      dsimp [r] at heq
      have hdiv := (div_eq_iff (ne_of_gt hT)).1 heq
      have hK : (0 : Real) < (K : Nat) := by positivity
      nlinarith
    subst t
    simpa using
      (polygonalInterpolate_grid K values T hT (K : Nat) le_rfl).trans
        (existenceRampInterpolate_grid K values T hT
          (K : Nat) le_rfl).symm
  · let n : Nat := Nat.floor r
    let theta : Real := r - n
    have hrKlt : r < (K : Nat) := lt_of_le_of_ne hrK heq
    have hnK : n < (K : Nat) := (Nat.floor_lt hr0).2 hrKlt
    have hn_le : (n : Real) <= r := Nat.floor_le hr0
    have hr_lt : r < (n : Real) + 1 := Nat.lt_floor_add_one r
    have htheta0 : 0 <= theta := by dsimp [theta]; linarith
    have htheta1 : theta <= 1 := by dsimp [theta]; linarith
    have hpair :
        ({n, n + 1} : Finset Nat) <=
          Finset.range ((K : Nat) + 1) := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    have hhatZero :
        forall l, l ∈ Finset.range ((K : Nat) + 1) ->
          l ∉ ({n, n + 1} : Finset Nat) -> hatWeight r l = 0 := by
      intro l hl hlpair
      apply hatWeight_eq_zero_of_one_le_abs
      by_cases hlt : l < n
      · rw [abs_of_nonneg]
        · have hcast : (l : Real) + 1 <= n := by
            exact_mod_cast (show l + 1 <= n by omega)
          linarith
        · have hcast : (l : Real) <= n := by
            exact_mod_cast (show l <= n by omega)
          linarith
      · have hnlt : n + 1 < l := by
          have hneN : l ≠ n := by
            intro h
            exact hlpair (by simp [h])
          have hneN1 : l ≠ n + 1 := by
            intro h
            exact hlpair (by simp [h])
          omega
        rw [abs_of_nonpos]
        · have hcast : (n : Real) + 2 <= l := by
            exact_mod_cast (show n + 2 <= l by omega)
          linarith
        · have hcast : (n : Real) + 1 <= l := by
            exact_mod_cast (show n + 1 <= l by omega)
          linarith
    have hhat :
        polygonalInterpolate K values t T =
          (1 - theta) * values n + theta * values (n + 1) := by
      unfold polygonalInterpolate
      change
        Finset.sum (Finset.range ((K : Nat) + 1))
          (fun l => hatWeight r l * values l) = _
      rw [<- Finset.sum_subset hpair]
      · rw [Finset.sum_pair (by omega : n ≠ n + 1)]
        have hnabs : abs (r - (n : Real)) = theta := by
          rw [abs_of_nonneg (sub_nonneg.mpr hn_le)]
        have hn1abs :
            abs (r - ((n + 1 : Nat) : Real)) = 1 - theta := by
          rw [abs_of_nonpos]
          · dsimp [theta]
            push_cast
            ring
          · push_cast
            linarith
        rw [show hatWeight r n = 1 - theta by
          simp [hatWeight, hnabs,
            max_eq_right (by linarith : 0 <= 1 - theta)]]
        rw [show hatWeight r (n + 1) = theta by
          unfold hatWeight
          rw [hn1abs]
          have hsimp : 1 - (1 - theta) = theta := by ring
          rw [hsimp, max_eq_right htheta0]]
      · intro l hl hlpair
        rw [hhatZero l hl hlpair, zero_mul]
    have hrange :
        Finset.range (n + 1) <= Finset.range (K : Nat) :=
      Finset.range_mono (by omega)
    have hrampZero :
        forall l, l ∈ Finset.range (K : Nat) ->
          l ∉ Finset.range (n + 1) ->
          (values (l + 1) - values l) *
            existenceClamp01 (r - l) = 0 := by
      intro l hlK hln
      have hnl : n + 1 <= l := by
        simpa only [Finset.mem_range, not_lt] using hln
      have hcast : (n : Real) + 1 <= l := by exact_mod_cast hnl
      have hnonpos : r - (l : Real) <= 0 := by linarith
      rw [existenceClamp01_of_nonpos hnonpos, mul_zero]
    have hbefore :
        Finset.sum (Finset.range n) (fun l =>
          (values (l + 1) - values l) * existenceClamp01 (r - l)) =
        Finset.sum (Finset.range n) (fun l =>
          values (l + 1) - values l) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hln : l < n := Finset.mem_range.mp hl
      have hcast : (l : Real) + 1 <= n := by
        exact_mod_cast (show l + 1 <= n by omega)
      have hone : (1 : Real) <= r - l := by linarith
      rw [existenceClamp01_of_one_le hone, mul_one]
    have hthetaClamp : existenceClamp01 (r - n) = theta := by
      dsimp [existenceClamp01]
      rw [max_eq_right htheta0, min_eq_right htheta1]
    have htel :
        values 0 +
          Finset.sum (Finset.range n)
            (fun l => values (l + 1) - values l) = values n := by
      induction n with
      | zero => simp
      | succ n ih =>
          simp only [Finset.sum_range_succ]
          linarith
    have hramp :
        existenceRampInterpolate K values t T =
          (1 - theta) * values n + theta * values (n + 1) := by
      unfold existenceRampInterpolate
      change values 0 +
        Finset.sum (Finset.range (K : Nat)) (fun l =>
          (values (l + 1) - values l) *
            existenceClamp01 (r - l)) = _
      rw [<- Finset.sum_subset hrange hrampZero]
      rw [Finset.sum_range_succ, hbefore, hthetaClamp]
      rw [<- add_assoc, htel]
      ring
    rw [hhat, hramp]

private theorem polygonal_increment_domination_ordered
    {J : Type*} [Fintype J]
    (K : PNat) (values : Nat -> Real) (control : J -> Nat -> Real)
    {s t T : Real} (hT : 0 < T)
    (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (hst : s <= t)
    (hcontrol : forall j l, l < (K : Nat) ->
      control j l <= control j (l + 1))
    (hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun j => control j (l + 1) - control j l)) :
    dist (polygonalInterpolate K values s T)
        (polygonalInterpolate K values t T) <=
      Finset.univ.sum (fun j =>
        dist (polygonalInterpolate K (control j) s T)
          (polygonalInterpolate K (control j) t T)) := by
  classical
  rw [polygonalInterpolate_eq_ramp K values hT hs,
    polygonalInterpolate_eq_ramp K values hT ht]
  simp_rw [polygonalInterpolate_eq_ramp K _ hT hs,
    polygonalInterpolate_eq_ramp K _ hT ht]
  let d : Nat -> Real := fun l =>
      existenceClamp01 (((K : Nat) : Real) * t / T - l) -
        existenceClamp01 (((K : Nat) : Real) * s / T - l)
  have hd (l : Nat) : 0 <= d l := by
    dsimp [d]
    apply sub_nonneg.mpr
    apply existenceClamp01_monotone
    apply sub_le_sub_right
    apply div_le_div_of_nonneg_right _ hT.le
    exact mul_le_mul_of_nonneg_left hst (by positivity)
  have hv :
      existenceRampInterpolate K values t T -
          existenceRampInterpolate K values s T =
        Finset.sum (Finset.range (K : Nat)) (fun l =>
          (values (l + 1) - values l) * d l) := by
    unfold existenceRampInterpolate
    dsimp [d]
    rw [add_sub_add_left_eq_sub, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hc (j : J) :
      existenceRampInterpolate K (control j) t T -
          existenceRampInterpolate K (control j) s T =
        Finset.sum (Finset.range (K : Nat)) (fun l =>
          (control j (l + 1) - control j l) * d l) := by
    unfold existenceRampInterpolate
    dsimp [d]
    rw [add_sub_add_left_eq_sub, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  simp only [Real.dist_eq]
  rw [abs_sub_comm (existenceRampInterpolate K values s T), hv]
  calc
    abs (Finset.sum (Finset.range (K : Nat)) (fun l =>
        (values (l + 1) - values l) * d l)) <=
        Finset.sum (Finset.range (K : Nat)) (fun l =>
          abs ((values (l + 1) - values l) * d l)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (Finset.range (K : Nat)) (fun l =>
          (Finset.univ.sum (fun j =>
            control j (l + 1) - control j l)) * d l) := by
      apply Finset.sum_le_sum
      intro l hl
      rw [abs_mul, abs_of_nonneg (hd l)]
      exact mul_le_mul_of_nonneg_right
        (hstep l (Finset.mem_range.mp hl)) (hd l)
    _ = Finset.univ.sum (fun j =>
          Finset.sum (Finset.range (K : Nat)) (fun l =>
            (control j (l + 1) - control j l) * d l)) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = Finset.univ.sum (fun j =>
          abs (existenceRampInterpolate K (control j) s T -
            existenceRampInterpolate K (control j) t T)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_sub_comm, hc]
      rw [abs_of_nonneg]
      apply Finset.sum_nonneg
      intro l hl
      exact mul_nonneg
        (sub_nonneg.mpr (hcontrol j l (Finset.mem_range.mp hl))) (hd l)

private theorem polygonal_increment_domination
    {J : Type*} [Fintype J]
    (K : PNat) (values : Nat -> Real) (control : J -> Nat -> Real)
    {s t T : Real} (hT : 0 < T)
    (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (hcontrol : forall j l, l < (K : Nat) ->
      control j l <= control j (l + 1))
    (hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun j => control j (l + 1) - control j l)) :
    dist (polygonalInterpolate K values s T)
        (polygonalInterpolate K values t T) <=
      Finset.univ.sum (fun j =>
        dist (polygonalInterpolate K (control j) s T)
          (polygonalInterpolate K (control j) t T)) := by
  rcases le_total s t with hst | hts
  · exact polygonal_increment_domination_ordered
      K values control hT hs ht hst hcontrol hstep
  · have h := polygonal_increment_domination_ordered
      K values control hT ht hs hts hcontrol hstep
    simpa [dist_comm] using h

private theorem gridTokenBatch_scaled_length
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat) (l : Nat) :
    ((gridTokenBatch T A K l).length : Real) / (K : Nat) =
      Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          ((gridInputCount T A K (l + 1) j k : Real) / (K : Nat) -
            (gridInputCount T A K l j k : Real) / (K : Nat)) := by
  classical
  rw [gridTokenBatch_length hT hA]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_sub
    (gridInputCount_mono hT hA K (Nat.le_succ l) j k)]
  ring

private theorem gridTokenBatch_scaled_length_uniform_zero
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) :
    forall epsilon, 0 < epsilon ->
      exists K0 : Nat, forall K : PNat, K0 <= (K : Nat) ->
        forall l, l < (K : Nat) ->
          ((gridTokenBatch T A K l).length : Real) / (K : Nat) <
            epsilon := by
  let B : Real -> Real := fun t =>
    Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer => A t j k
  have hBcont : ContinuousOn B (Icc (0 : Real) T) := by
    apply continuousOn_finset_sum
    intro j hj
    apply continuousOn_finset_sum
    intro k hk
    simpa [B, uIcc_of_le hT.le] using (hA.1 j k).continuousOn
  have hBuc : UniformContinuousOn B (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hBcont
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hmodulus⟩ :=
    Metric.uniformContinuousOn_iff.mp hBuc
      (epsilon / 2) (by positivity)
  let C : Real :=
    ((Fintype.card Server : Nat) : Real) *
      (Fintype.card Buffer : Nat)
  obtain ⟨K0, hK0⟩ :=
    exists_nat_gt (max (T / delta) (4 * C / epsilon))
  refine ⟨K0, fun K hKK l hl => ?_⟩
  have hK0real : (K0 : Real) <= (K : Nat) := by exact_mod_cast hKK
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hmesh : T / (K : Nat) < delta := by
    have hraw : T / delta < (K : Real) :=
      (lt_of_le_of_lt (le_max_left _ _) hK0).trans_le hK0real
    apply (div_lt_iff₀ hK).2
    apply (div_lt_iff₀ hdelta).1 at hraw
    nlinarith
  have hround : 2 * C / (K : Nat) < epsilon / 2 := by
    have hraw : 4 * C / epsilon < (K : Real) :=
      (lt_of_le_of_lt (le_max_right _ _) hK0).trans_le hK0real
    have hC : 0 <= C := by dsimp [C]; positivity
    apply (div_lt_iff₀ hK).2
    apply (div_lt_iff₀ hepsilon).1 at hraw
    nlinarith
  let s := gridTime T K l
  let u := gridTime T K (l + 1)
  have hs : s ∈ Icc (0 : Real) T := gridTime_mem_Icc hT K l
  have hu : u ∈ Icc (0 : Real) T := gridTime_mem_Icc hT K (l + 1)
  have hsu : dist s u < delta := by
    rw [Real.dist_eq, abs_of_nonpos
      (sub_nonpos.mpr (gridTime_mono hT K (Nat.le_succ l)))]
    rw [gridTime_eq_gridPoint T K l (Nat.le_of_lt hl),
      gridTime_eq_gridPoint T K (l + 1) (by omega)]
    have : T * ((l + 1 : Nat) : Real) / (K : Nat) -
        T * (l : Real) / (K : Nat) = T / (K : Nat) := by
      push_cast
      ring
    rw [show
      -(T * (l : Real) / (K : Nat) -
          T * ((l + 1 : Nat) : Real) / (K : Nat)) =
        T * ((l + 1 : Nat) : Real) / (K : Nat) -
          T * (l : Real) / (K : Nat) by ring]
    rw [this]
    exact hmesh
  have hBclose : abs (B u - B s) < epsilon / 2 := by
    have hm := hmodulus s hs u hu hsu
    simpa [Real.dist_eq, abs_sub_comm] using hm
  have happ (r : Nat) :
      abs
        ((Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer =>
              (gridInputCount T A K r j k : Real) / (K : Nat)) -
          B (gridTime T K r)) <= C / (K : Nat) := by
    rw [show
      (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer =>
            (gridInputCount T A K r j k : Real) / (K : Nat)) -
          B (gridTime T K r) =
        Finset.univ.sum (fun j : Server =>
          Finset.univ.sum fun k : Buffer =>
            ((gridInputCount T A K r j k : Real) / (K : Nat) -
              A (gridTime T K r) j k)) by
      dsimp [B]
      simp_rw [Finset.sum_sub_distrib]]
    calc
      abs (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer =>
            ((gridInputCount T A K r j k : Real) / (K : Nat) -
              A (gridTime T K r) j k)) <=
          Finset.univ.sum (fun j : Server =>
            abs (Finset.univ.sum fun k : Buffer =>
              ((gridInputCount T A K r j k : Real) / (K : Nat) -
                A (gridTime T K r) j k))) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum (fun _j : Server =>
            Finset.univ.sum fun _k : Buffer =>
              (1 : Real) / (K : Nat)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun k hk =>
            (gridInputCount_approx T hT A hA K r j k).le)
      _ = C / (K : Nat) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [C]
        push_cast
        ring
  rw [gridTokenBatch_scaled_length T hT A hA K l]
  let P : Nat -> Real := fun r =>
    Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        (gridInputCount T A K r j k : Real) / (K : Nat)
  have hPs := happ l
  have hPu := happ (l + 1)
  simp_rw [Finset.sum_sub_distrib]
  change P (l + 1) - P l < epsilon
  have hidentity :
      P (l + 1) - P l =
        (P (l + 1) - B u) + (B u - B s) + (B s - P l) := by
    dsimp [s, u]
    ring
  rw [hidentity]
  calc
    (P (l + 1) - B u) + (B u - B s) + (B s - P l) <=
        abs (P (l + 1) - B u) + abs (B u - B s) +
          abs (B s - P l) := by
      gcongr <;> apply le_abs_self
    _ <= C / (K : Nat) + epsilon / 2 + C / (K : Nat) := by
      have hPs' : abs (B s - P l) <= C / (K : Nat) := by
        simpa [P, s, abs_sub_comm] using hPs
      have hPu' : abs (P (l + 1) - B u) <= C / (K : Nat) := by
        simpa [P, u] using hPu
      linarith
    _ < epsilon := by
      calc
        C / (K : Nat) + epsilon / 2 + C / (K : Nat) =
            2 * C / (K : Nat) + epsilon / 2 := by ring
        _ < epsilon / 2 + epsilon / 2 := by linarith
        _ = epsilon := by ring

private theorem gridAllocationCount_step_le_input_sum
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (x0 : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (hA : IsFluidInput T A)
    (K : PNat) (l : Nat) (i : Buffer) (j : Server) (k : Buffer) :
    abs ((gridAllocationCount N T x0 U A K (l + 1) i j k : Real) /
          (K : Nat) -
        (gridAllocationCount N T x0 U A K l i j k : Real) /
          (K : Nat)) <=
      Finset.univ.sum fun j' : Server =>
        Finset.univ.sum fun k' : Buffer =>
          ((gridInputCount T A K (l + 1) j' k' : Real) / (K : Nat) -
            (gridInputCount T A K l j' k' : Real) / (K : Nat)) := by
  let z := roundedState x0 (K : Nat)
    (Classical.choice (inferInstance : Nonempty Buffer))
  have hmono :
      gridAllocationCount N T x0 U A K l i j k <=
        gridAllocationCount N T x0 U A K (l + 1) i j k := by
    let i0 : Buffer := Classical.choice
      (inferInstance : Nonempty Buffer)
    change
      N.runAllocationCount (U K) (roundedState x0 (K : Nat) i0)
          (gridTokenPrefix T A K l) i j k <=
        N.runAllocationCount (U K) (roundedState x0 (K : Nat) i0)
          (gridTokenPrefix T A K l ++ gridTokenBatch T A K l) i j k
    rw [runAllocationCount_append]
    omega
  have hnat :
      gridAllocationCount N T x0 U A K (l + 1) i j k -
          gridAllocationCount N T x0 U A K l i j k <=
        (gridTokenBatch T A K l).length := by
    have htail :=
      runAllocationCount_le_count N (U K)
        (N.runTokens (U K) z (gridTokenPrefix T A K l))
        (gridTokenBatch T A K l) i j k
    dsimp [z] at htail
    unfold gridAllocationCount
    rw [show gridTokenPrefix T A K (l + 1) =
      gridTokenPrefix T A K l ++ gridTokenBatch T A K l by rfl]
    rw [runAllocationCount_append, Nat.add_sub_cancel_left]
    exact htail.trans (List.count_le_length)
  have hreal :
      (gridAllocationCount N T x0 U A K (l + 1) i j k : Real) -
          (gridAllocationCount N T x0 U A K l i j k : Real) <=
        (gridTokenBatch T A K l).length := by
    rw [<- Nat.cast_sub hmono]
    exact_mod_cast hnat
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [<- gridTokenBatch_scaled_length T hT A hA K l]
  rw [<- sub_div, abs_div, abs_of_pos hK,
    abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmono))]
  exact (div_le_div_iff_of_pos_right hK).2 hreal

private theorem gridQueueState_step_le_two_input_sum
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (x0 : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (hA : IsFluidInput T A)
    (K : PNat) (l : Nat) (i : Buffer) :
    abs ((gridQueueState N T x0 U A K (l + 1) i : Real) / (K : Nat) -
        (gridQueueState N T x0 U A K l i : Real) / (K : Nat)) <=
      2 * (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          ((gridInputCount T A K (l + 1) j k : Real) / (K : Nat) -
            (gridInputCount T A K l j k : Real) / (K : Nat))) := by
  let z := roundedState x0 (K : Nat)
    (Classical.choice (inferInstance : Nonempty Buffer))
  have htotal :=
    runTokens_batch_l1_le_two_mul_length N (U K) z
      (gridTokenPrefix T A K l) (gridTokenBatch T A K l)
  have hcoord :
      abs (((gridQueueState N T x0 U A K (l + 1) i : Nat) : Real) -
        ((gridQueueState N T x0 U A K l i : Nat) : Real)) <=
          2 * (gridTokenBatch T A K l).length := by
    unfold gridQueueState
    rw [show gridTokenPrefix T A K (l + 1) =
      gridTokenPrefix T A K l ++ gridTokenBatch T A K l by rfl]
    exact (Finset.single_le_sum
      (fun q _ => abs_nonneg
        (((N.runTokens (U K) z
          (gridTokenPrefix T A K l ++ gridTokenBatch T A K l) q :
            Nat) : Real) -
          (N.runTokens (U K) z (gridTokenPrefix T A K l) q : Real)))
      (Finset.mem_univ i)).trans htotal
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [<- gridTokenBatch_scaled_length T hT A hA K l]
  rw [<- sub_div, abs_div, abs_of_pos hK]
  calc
    abs ((gridQueueState N T x0 U A K (l + 1) i : Real) -
        (gridQueueState N T x0 U A K l i : Real)) / (K : Nat) <=
        (2 * (gridTokenBatch T A K l).length : Real) / (K : Nat) :=
      (div_le_div_iff_of_pos_right hK).2 hcoord
    _ = 2 * (((gridTokenBatch T A K l).length : Real) /
        (K : Nat)) := by ring

private theorem polygonalAllocationPath_increment_domination
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (x0 : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (hA : IsFluidInput T A)
    (K : PNat) (i : Buffer) (j : Server) (k : Buffer)
    {s t : Real} (hs : s ∈ Icc (0 : Real) T)
    (ht : t ∈ Icc (0 : Real) T) :
    dist (polygonalAllocationPath N T x0 U A K s i j k)
        (polygonalAllocationPath N T x0 U A K t i j k) <=
      Finset.univ.sum (fun jk : Server × Buffer =>
        dist (polygonalInputPath T A K s jk.1 jk.2)
          (polygonalInputPath T A K t jk.1 jk.2)) := by
  let values : Nat -> Real := fun l =>
    (gridAllocationCount N T x0 U A K l i j k : Real) / (K : Nat)
  let control : Server × Buffer -> Nat -> Real := fun jk l =>
    (gridInputCount T A K l jk.1 jk.2 : Real) / (K : Nat)
  have hcontrol : forall jk l, l < (K : Nat) ->
      control jk l <= control jk (l + 1) := by
    intro jk l hl
    dsimp [control]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast
      (gridInputCount_mono hT hA K (Nat.le_succ l) jk.1 jk.2)
  have hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun jk =>
          control jk (l + 1) - control jk l) := by
    intro l hl
    have h :=
      gridAllocationCount_step_le_input_sum
        N T hT x0 U A hA K l i j k
    let d : Server × Buffer -> Real := fun jk =>
      control jk (l + 1) - control jk l
    have hprod :
        (Finset.univ : Finset (Server × Buffer)) =
          (Finset.univ : Finset Server).product
            (Finset.univ : Finset Buffer) := by
      ext jk
      simp
    have hsum :
        Finset.univ.sum d =
          Finset.univ.sum (fun j' : Server =>
            Finset.univ.sum fun k' : Buffer =>
              (gridInputCount T A K (l + 1) j' k' : Real) / (K : Nat) -
                (gridInputCount T A K l j' k' : Real) / (K : Nat)) := by
      rw [hprod]
      simpa [d, control] using
        (Finset.sum_product
          (Finset.univ : Finset Server)
          (Finset.univ : Finset Buffer) d)
    dsimp [values]
    change _ <= Finset.univ.sum d
    rw [hsum]
    exact h
  exact polygonal_increment_domination K values control hT hs ht
    hcontrol hstep

private theorem polygonalAllocationPath_increment_matching
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (x0 : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (hA : IsFluidInput T A)
    (K : PNat) (i : Buffer) (j : Server) (k : Buffer)
    {s t : Real} (hs : s ∈ Icc (0 : Real) T)
    (ht : t ∈ Icc (0 : Real) T) :
    dist (polygonalAllocationPath N T x0 U A K s i j k)
        (polygonalAllocationPath N T x0 U A K t i j k) <=
      dist (polygonalInputPath T A K s j k)
        (polygonalInputPath T A K t j k) := by
  let values : Nat -> Real := fun l =>
    (gridAllocationCount N T x0 U A K l i j k : Real) / (K : Nat)
  let control : Unit -> Nat -> Real := fun _ l =>
    (gridInputCount T A K l j k : Real) / (K : Nat)
  have hcontrol : forall q l, l < (K : Nat) ->
      control q l <= control q (l + 1) := by
    intro q l hl
    dsimp [control]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast
      (gridInputCount_mono hT hA K (Nat.le_succ l) j k)
  have hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun q =>
          control q (l + 1) - control q l) := by
    intro l hl
    simp only [Finset.univ_unique, Finset.sum_singleton]
    dsimp [values, control]
    have hmono :
        gridAllocationCount N T x0 U A K l i j k <=
          gridAllocationCount N T x0 U A K (l + 1) i j k := by
      let i0 : Buffer := Classical.choice
        (inferInstance : Nonempty Buffer)
      change
        N.runAllocationCount (U K) (roundedState x0 (K : Nat) i0)
            (gridTokenPrefix T A K l) i j k <=
          N.runAllocationCount (U K) (roundedState x0 (K : Nat) i0)
            (gridTokenPrefix T A K l ++ gridTokenBatch T A K l) i j k
      rw [runAllocationCount_append]
      omega
    have hnat :=
      gridAllocationCount_succ_sub_le N hT x0 U hA K l i j k
    have hinputmono :
        gridInputCount T A K l j k <=
          gridInputCount T A K (l + 1) j k :=
      gridInputCount_mono hT hA K (Nat.le_succ l) j k
    have hK : (0 : Real) < (K : Nat) := by positivity
    rw [<- sub_div, <- sub_div, abs_div, abs_of_pos hK,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmono))]
    apply div_le_div_of_nonneg_right _ hK.le
    calc
      (gridAllocationCount N T x0 U A K (l + 1) i j k : Real) -
          gridAllocationCount N T x0 U A K l i j k =
        (gridAllocationCount N T x0 U A K (l + 1) i j k -
          gridAllocationCount N T x0 U A K l i j k : Nat) := by
            rw [Nat.cast_sub hmono]
      _ <=
          (gridInputCount T A K (l + 1) j k -
            gridInputCount T A K l j k : Nat) := by
              exact_mod_cast hnat
      _ =
          (gridInputCount T A K (l + 1) j k : Real) -
            gridInputCount T A K l j k := by
              rw [Nat.cast_sub hinputmono]
  have h := polygonal_increment_domination
    K values control hT hs ht hcontrol hstep
  simpa [values, control, polygonalAllocationPath, polygonalInputPath] using h

private theorem polygonalQueuePath_increment_domination
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (x0 : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (hA : IsFluidInput T A)
    (K : PNat) (i : Buffer)
    {s t : Real} (hs : s ∈ Icc (0 : Real) T)
    (ht : t ∈ Icc (0 : Real) T) :
    dist (polygonalQueuePath N T x0 U A K s i)
        (polygonalQueuePath N T x0 U A K t i) <=
      Finset.univ.sum (fun jk : (Server × Buffer) × Fin 2 =>
        dist (polygonalInputPath T A K s jk.1.1 jk.1.2)
          (polygonalInputPath T A K t jk.1.1 jk.1.2)) := by
  let values : Nat -> Real := fun l =>
    (gridQueueState N T x0 U A K l i : Real) / (K : Nat)
  let control : (Server × Buffer) × Fin 2 -> Nat -> Real := fun jk l =>
    (gridInputCount T A K l jk.1.1 jk.1.2 : Real) / (K : Nat)
  have hcontrol : forall jk l, l < (K : Nat) ->
      control jk l <= control jk (l + 1) := by
    intro jk l hl
    dsimp [control]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast
      (gridInputCount_mono hT hA K (Nat.le_succ l) jk.1.1 jk.1.2)
  have hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun jk =>
          control jk (l + 1) - control jk l) := by
    intro l hl
    have h :=
      gridQueueState_step_le_two_input_sum N T hT x0 U A hA K l i
    let d : Server × Buffer -> Real := fun jk =>
      (gridInputCount T A K (l + 1) jk.1 jk.2 : Real) / (K : Nat) -
        (gridInputCount T A K l jk.1 jk.2 : Real) / (K : Nat)
    have hprod :
        (Finset.univ : Finset (Server × Buffer)) =
          (Finset.univ : Finset Server).product
            (Finset.univ : Finset Buffer) := by
      ext jk
      simp
    have hsum :
        Finset.univ.sum d =
          Finset.univ.sum (fun j : Server =>
            Finset.univ.sum fun k : Buffer =>
              (gridInputCount T A K (l + 1) j k : Real) / (K : Nat) -
                (gridInputCount T A K l j k : Real) / (K : Nat)) := by
      rw [hprod]
      simpa [d] using Finset.sum_product
        (Finset.univ : Finset Server)
        (Finset.univ : Finset Buffer) d
    have hdup :
        Finset.univ.sum (fun jk : (Server × Buffer) × Fin 2 =>
          control jk (l + 1) - control jk l) =
          2 * Finset.univ.sum d := by
      rw [show
        (Finset.univ : Finset ((Server × Buffer) × Fin 2)) =
          (Finset.univ : Finset (Server × Buffer)).product
            (Finset.univ : Finset (Fin 2)) by ext jk; simp]
      rw [show
        Finset.sum
            ((Finset.univ : Finset (Server × Buffer)).product
              (Finset.univ : Finset (Fin 2)))
            (fun jk => control jk (l + 1) - control jk l) =
          Finset.univ.sum (fun ab : Server × Buffer =>
            Finset.univ.sum (fun z : Fin 2 =>
              control (ab, z) (l + 1) - control (ab, z) l)) by
        exact Finset.sum_product _ _ _]
      simp [control, d, <- Finset.mul_sum]
      ring
    dsimp [values]
    rw [hdup, hsum]
    exact h
  exact polygonal_increment_domination K values control hT hs ht
    hcontrol hstep

private theorem exists_uniformly_convergent_subsequence_controlled
    {X J : Type*} [MetricSpace X] [ProperSpace X] [Fintype J]
    {f : Nat -> Real -> X} {g : Nat -> J -> Real -> Real}
    {control : J -> Real -> Real} {a b M : Real} {center : X}
    (hf : forall n, ContinuousOn (f n) (Icc a b))
    (hbound : forall n t, t ∈ Icc a b -> dist (f n t) center <= M)
    (hcontrol : forall j, ContinuousOn (control j) (Icc a b))
    (hgconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j t, t ∈ Icc a b ->
          dist (g n j t) (control j t) < epsilon)
    (hdom : forall n x, x ∈ Icc a b ->
      forall y, y ∈ Icc a b ->
        dist (f n x) (f n y) <=
          Finset.univ.sum (fun j => dist (g n j x) (g n j y))) :
    exists q : Nat -> Nat, StrictMono q /\
      exists limit : Real -> X,
        ContinuousOn limit (Icc a b) /\
        forall epsilon, 0 < epsilon ->
          exists n0, forall n, n0 <= n ->
            forall t, t ∈ Icc a b ->
              dist (f (q n) t) (limit t) < epsilon := by
  let D := Icc a b
  letI : CompactSpace D :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let F : Nat -> BoundedContinuousFunction D X := fun n =>
    BoundedContinuousFunction.mkOfCompact
      (ContinuousMap.mk
        (fun t : D => f n t.1)
        ((hf n).domRestrict))
  have hcontrols :
      UniformEquicontinuous
        (fun j : J => fun t : D => control j t.1) := by
    rw [uniformEquicontinuous_finite]
    intro j
    exact CompactSpace.uniformContinuous_of_continuous
      ((hcontrol j).domRestrict)
  have hfamily :
      UniformEquicontinuous (fun n : Nat => fun t : D => f n t.1) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro epsilon hepsilon
    let C : Real := (Fintype.card J : Real) + 1
    have hC : 0 < C := by
      dsimp [C]
      positivity
    let eta : Real := epsilon / (8 * C)
    have heta : 0 < eta := by
      dsimp [eta]
      positivity
    obtain ⟨N0, hN0⟩ := hgconv eta heta
    have hprefix :
        UniformEquicontinuous
          (fun n : Fin N0 => fun t : D => f n.1 t.1) := by
      rw [uniformEquicontinuous_finite]
      intro n
      exact CompactSpace.uniformContinuous_of_continuous
        ((hf n.1).domRestrict)
    obtain ⟨deltaControl, hdeltaControl, hdeltaControlWorks⟩ :=
      (Metric.uniformEquicontinuous_iff.mp hcontrols)
        (epsilon / (4 * C)) (by positivity)
    obtain ⟨deltaPrefix, hdeltaPrefix, hdeltaPrefixWorks⟩ :=
      (Metric.uniformEquicontinuous_iff.mp hprefix)
        epsilon hepsilon
    refine ⟨min deltaControl deltaPrefix,
      lt_min hdeltaControl hdeltaPrefix, ?_⟩
    intro x y hxy n
    have hxyControl : dist x y < deltaControl :=
      hxy.trans_le (min_le_left _ _)
    have hxyPrefix : dist x y < deltaPrefix :=
      hxy.trans_le (min_le_right _ _)
    by_cases hn : N0 <= n
    · have hterm (j : J) :
          dist (g n j x.1) (g n j y.1) <= epsilon / C := by
        have hxapprox := hN0 n hn j x.1 x.2
        have hyapprox := hN0 n hn j y.1 y.2
        have hmiddle := hdeltaControlWorks x y hxyControl j
        apply le_of_lt
        calc
          dist (g n j x.1) (g n j y.1)
              <= dist (g n j x.1) (control j x.1) +
                  dist (control j x.1) (control j y.1) +
                  dist (control j y.1) (g n j y.1) := by
                calc
                  _ <= dist (g n j x.1) (control j x.1) +
                      dist (control j x.1) (g n j y.1) :=
                    dist_triangle _ _ _
                  _ <= dist (g n j x.1) (control j x.1) +
                      (dist (control j x.1) (control j y.1) +
                        dist (control j y.1) (g n j y.1)) := by
                    have htri :=
                      dist_triangle (control j x.1) (control j y.1)
                        (g n j y.1)
                    linarith
                  _ = _ := by ring
          _ < eta + epsilon / (4 * C) + eta := by
                have hyapprox' :
                    dist (control j y.1) (g n j y.1) < eta := by
                  simpa [dist_comm] using hyapprox
                gcongr
          _ <= epsilon / C := by
                dsimp [eta]
                have h8C : 0 < 8 * C := by positivity
                have h4C : 0 < 4 * C := by positivity
                field_simp
                linarith
      have hcard_lt : (Fintype.card J : Real) / C < 1 := by
        apply (div_lt_one hC).2
        dsimp [C]
        linarith
      calc
        dist (f n x.1) (f n y.1)
            <= Finset.univ.sum
                (fun j => dist (g n j x.1) (g n j y.1)) :=
              hdom n x.1 x.2 y.1 y.2
        _ <= Finset.univ.sum (fun _ : J => epsilon / C) :=
              Finset.sum_le_sum (fun j _ => hterm j)
        _ = (Fintype.card J : Real) * (epsilon / C) := by simp
        _ = epsilon * ((Fintype.card J : Real) / C) := by ring
        _ < epsilon * 1 :=
              mul_lt_mul_of_pos_left hcard_lt hepsilon
        _ = epsilon := by ring
    · have hnlt : n < N0 := Nat.lt_of_not_ge hn
      exact hdeltaPrefixWorks x y hxyPrefix ⟨n, hnlt⟩
  let S : Set (BoundedContinuousFunction D X) := range F
  have hcompact : IsCompact (closure S) := by
    apply BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall center M) (isCompact_closedBall center M) S
    · intro p t hp
      obtain ⟨n, rfl⟩ := hp
      exact hbound n t.1 t.2
    · let index : S -> Nat := fun p => Classical.choose p.2
      have hindex (p : S) : F (index p) = p.1 :=
        Classical.choose_spec p.2
      intro t
      rw [Metric.equicontinuousAt_iff]
      intro epsilon hepsilon
      let hnat := hfamily.equicontinuous t
      rw [Metric.equicontinuousAt_iff] at hnat
      obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
        hnat epsilon hepsilon
      refine ⟨delta, hdelta, fun x hx p => ?_⟩
      rw [show p.1 t = F (index p) t by rw [hindex]]
      rw [show p.1 x = F (index p) x by rw [hindex]]
      exact hdeltaWorks x hx (index p)
  obtain ⟨limitB, _hlimit_mem, q, hqmono, hqconv⟩ :=
    hcompact.tendsto_subseq
      (fun n => subset_closure
        (show F n ∈ S from mem_range_self n))
  let limit : Real -> X := fun t =>
    if ht : t ∈ Icc a b then
      limitB (show D from ⟨t, ht⟩)
    else center
  refine ⟨q, hqmono, limit, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq :
        (Icc a b).domRestrict limit = fun t : D => limitB t := by
      funext t
      exact dif_pos t.2
    rw [heq]
    exact limitB.continuous
  · intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ :=
      Metric.tendsto_atTop.mp hqconv epsilon hepsilon
    refine ⟨n0, fun n hn t ht => ?_⟩
    have hdist := BoundedContinuousFunction.dist_coe_le_dist
      (f := F (q n)) (g := limitB) (show D from ⟨t, ht⟩)
    have hlt := lt_of_le_of_lt hdist (by
      simpa [Function.comp_apply] using hn0 n hn)
    have hlimit :
        limit t = limitB (show D from ⟨t, ht⟩) :=
      dif_pos ht
    rw [hlimit]
    exact hlt

private theorem polygonalAllocationPath_nonneg_le
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (x0 : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (hA : IsFluidInput T A)
    (K : PNat) (t : Real) (ht : t ∈ Icc (0 : Real) T)
    (i : Buffer) (j : Server) (k : Buffer) :
    0 <= polygonalAllocationPath N T x0 U A K t i j k /\
      polygonalAllocationPath N T x0 U A K t i j k <= A T j k := by
  apply polygonalInterpolate_bounds K _ hT ht
  · intro l hl
    positivity
  · intro l hl
    have halloc :=
      gridAllocationCount_le_input N hT x0 U hA K l i j k
    have hfloor :
        (gridInputCount T A K l j k : Real) <=
          (K : Real) * A (gridTime T K l) j k := by
      apply Nat.floor_le
      have hnonneg : 0 <= A (gridTime T K l) j k := by
        rw [<- hA.2.2 j k]
        exact hA.2.1 j k ⟨le_rfl, hT.le⟩
          (gridTime_mem_Icc hT K l) (gridTime_mem_Icc hT K l).1
      exact mul_nonneg (Nat.cast_nonneg _) hnonneg
    have htime :
        A (gridTime T K l) j k <= A T j k :=
      hA.2.1 j k (gridTime_mem_Icc hT K l) ⟨hT.le, le_rfl⟩
        (gridTime_mem_Icc hT K l).2
    have hK : (0 : Real) < (K : Nat) := by positivity
    calc
      (gridAllocationCount N T x0 U A K l i j k : Real) / (K : Nat)
          <= (gridInputCount T A K l j k : Real) / (K : Nat) := by
            exact div_le_div_of_nonneg_right
              (by exact_mod_cast halloc) hK.le
      _ <= A (gridTime T K l) j k := by
            apply (div_le_iff₀ hK).2
            simpa only [Nat.cast_ofNat, mul_comm] using hfloor
      _ <= A T j k := htime

private theorem polygonalAllocationPath_zero
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (x0 : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (K : PNat)
    (i : Buffer) (j : Server) (k : Buffer) :
    polygonalAllocationPath N T x0 U A K 0 i j k = 0 := by
  unfold polygonalAllocationPath
  have hgrid := polygonalInterpolate_grid K
    (fun l =>
      (gridAllocationCount N T x0 U A K l i j k : Real) / (K : Nat))
    T hT 0 (Nat.zero_le _)
  simpa [gridAllocationCount, gridTokenPrefix, runAllocationCount] using hgrid

private theorem roundedState_scaled_tendsto
    (x0 : Simplex Buffer) (i : Buffer) :
    Tendsto
      (fun n : Nat =>
        ((roundedState x0 (n + 1)
          (Classical.choice (inferInstance : Nonempty Buffer)) i : Nat) :
            Real) / (n + 1 : Nat))
      atTop (nhds (x0 i)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let C : Real := (Fintype.card Buffer : Real) + 1
  have hrecip :
      Tendsto
        (fun n : Nat => C / ((n : Real) + 1))
        atTop (nhds 0) := by
    have hC : Tendsto (fun _ : Nat => C) atTop (nhds C) :=
      tendsto_const_nhds
    have hInv :
        Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1))
          atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [div_eq_mul_inv] using hC.mul hInv
  obtain ⟨n0, hn0⟩ :=
    Metric.tendsto_atTop.mp hrecip epsilon hepsilon
  refine ⟨n0, fun n hn => ?_⟩
  have hb := roundedState_error_bound x0 (n + 1)
    (by omega) (Classical.choice (inferInstance : Nonempty Buffer)) i
  have hc := hn0 n hn
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (by positivity :
      0 <= C / ((n : Real) + 1))] at hc
  rw [Real.dist_eq]
  exact lt_trans hb (by
    simpa [C, Nat.cast_add, Nat.cast_one] using hc)

private theorem measurableFluidPolicySelector_comp
    {Time : Type*} [MeasurableSpace Time]
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Time -> Buffer -> Real)
    (hX : forall i, Measurable (fun t => X t i))
    (a : Option Buffer) :
    Measurable
      (fun t => N.measurableFluidPolicySelector U j k (X t) a) := by
  exact
    (measurable_pi_iff.mp
      (N.measurableFluidPolicySelector_measurable U j k) a).comp
      (measurable_pi_lambda X hX)

def fluidPolicyEpsilonCorrespondence
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (epsilon : Real) : Set (ActionVector Buffer) :=
  closure (convexHull Real
    {q | exists K : PNat, exists z : JobState Buffer (K : Nat),
      epsilon⁻¹ <= (K : Real) /\
      IsNearNormalizedState z x epsilon /\
      q = N.actionDirac (U K z j k)})

private theorem fluidPolicyEpsilonCorrespondence_isClosed
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (epsilon : Real) :
    IsClosed (N.fluidPolicyEpsilonCorrespondence U j k x epsilon) :=
  isClosed_closure

private theorem mem_fluidPolicyCorrespondence_iff_epsilon
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (q : ActionVector Buffer) :
    q ∈ N.fluidPolicyCorrespondence U j k x <->
      forall epsilon : {r : Real // 0 < r},
        q ∈ N.fluidPolicyEpsilonCorrespondence U j k x epsilon.1 := by
  unfold fluidPolicyCorrespondence fluidPolicyEpsilonCorrespondence
  rw [Set.mem_iInter]

private theorem weightedActionAverage_mem_epsilon
    {I : Type*} (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    (s : Finset I) (weight : I -> Real)
    (K : I -> PNat)
    (z : (r : I) -> JobState Buffer (K r : Nat))
    (hweight_nonneg : forall r, r ∈ s -> 0 <= weight r)
    (hweight_sum : Finset.sum s weight = 1)
    (hK : forall r, r ∈ s -> epsilon⁻¹ <= ((K r : Nat) : Real))
    (hz : forall r, r ∈ s -> IsNearNormalizedState (z r) x epsilon) :
    (Finset.sum s fun r =>
      (weight r) • N.actionDirac (U (K r) (z r) j k)) ∈
        N.fluidPolicyEpsilonCorrespondence U j k x epsilon := by
  apply subset_closure
  apply (convex_convexHull Real _).sum_mem hweight_nonneg hweight_sum
  intro r hr
  apply subset_convexHull Real
  exact ⟨K r, z r, hK r hr, hz r hr, rfl⟩

noncomputable def finiteDifferenceRatio
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t h : Real) : ActionVector Buffer :=
  fun a => (E (t + h) a - E t a) / (A (t + h) - A t)

private theorem derivativeRatio_mem_closed
    {C : Set (ActionVector Buffer)}
    (hC : IsClosed C)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t Adot : Real) (Edot : ActionVector Buffer)
    (hA : HasDerivAt A Adot t)
    (hE : forall a, HasDerivAt (fun s => E s a) (Edot a) t)
    (hAdot : 0 < Adot)
    (hmem : Filter.Eventually
      (fun h => finiteDifferenceRatio A E t h ∈ C)
      (nhdsWithin 0 (Ioi 0))) :
    (fun a => Edot a / Adot) ∈ C := by
  have htendsto :
      Tendsto (finiteDifferenceRatio A E t)
        (nhdsWithin 0 (Ioi 0)) (nhds (fun a => Edot a / Adot)) := by
    let slopeRatio : Real -> ActionVector Buffer :=
      fun h a =>
        (h⁻¹ * (E (t + h) a - E t a)) /
          (h⁻¹ * (A (t + h) - A t))
    have hslope :
        Tendsto slopeRatio (nhdsWithin 0 (Ioi 0))
          (nhds (fun a => Edot a / Adot)) := by
      rw [tendsto_pi_nhds]
      intro a
      exact ((hE a).tendsto_slope_zero_right).div
        hA.tendsto_slope_zero_right (ne_of_gt hAdot)
    apply hslope.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    funext a
    have hh0 : h ≠ 0 := ne_of_gt hh
    dsimp [slopeRatio, finiteDifferenceRatio]
    field_simp
  exact hC.mem_of_tendsto htendsto hmem

private theorem closed_mem_of_finiteDifferenceRatio_limit
    {C : Set (ActionVector Buffer)}
    (hC : IsClosed C)
    (Aseq : Nat -> Real -> Real) (A : Real -> Real)
    (Eseq : Nat -> Real -> ActionVector Buffer)
    (E : Real -> ActionVector Buffer)
    (s t : Real)
    (hAs : Tendsto (fun n => Aseq n s) atTop (nhds (A s)))
    (hAt : Tendsto (fun n => Aseq n t) atTop (nhds (A t)))
    (hEs : forall a,
      Tendsto (fun n => Eseq n s a) atTop (nhds (E s a)))
    (hEt : forall a,
      Tendsto (fun n => Eseq n t a) atTop (nhds (E t a)))
    (hden : A t - A s ≠ 0)
    (hmem : Filter.Eventually
      (fun n => (fun a => (Eseq n t a - Eseq n s a) /
          (Aseq n t - Aseq n s)) ∈ C) atTop) :
    (fun a => (E t a - E s a) / (A t - A s)) ∈ C := by
  apply hC.mem_of_tendsto _ hmem
  rw [tendsto_pi_nhds]
  intro a
  exact ((hEt a).sub (hEs a)).div (hAt.sub hAs) hden

private theorem derivativeRatio_mem_fluidPolicyCorrespondence
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t Adot : Real) (Edot : ActionVector Buffer)
    (hA : HasDerivAt A Adot t)
    (hE : forall a, HasDerivAt (fun s => E s a) (Edot a) t)
    (hAdot : 0 < Adot)
    (hfinite : forall epsilon : {r : Real // 0 < r},
      Filter.Eventually
        (fun h => finiteDifferenceRatio A E t h ∈
          N.fluidPolicyEpsilonCorrespondence U j k x epsilon.1)
        (nhdsWithin 0 (Ioi 0))) :
    (fun a => Edot a / Adot) ∈
      N.fluidPolicyCorrespondence U j k x := by
  rw [N.mem_fluidPolicyCorrespondence_iff_epsilon]
  intro epsilon
  exact derivativeRatio_mem_closed
    (N.fluidPolicyEpsilonCorrespondence_isClosed U j k x epsilon.1)
    A E t Adot Edot hA hE hAdot (hfinite epsilon)

private theorem hasDerivAt_eq_zero_of_increment_domination
    (A E : Real -> Real) (t Edot : Real)
    (hA : HasDerivAt A 0 t)
    (hE : HasDerivAt E Edot t)
    (hdom : forall s u, s <= u ->
      0 <= E u - E s /\ E u - E s <= A u - A s) :
    Edot = 0 := by
  have hsqueeze :
      Tendsto (fun h => h⁻¹ * (E (t + h) - E t))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hA.tendsto_slope_zero_right
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact mul_nonneg (inv_nonneg.mpr hh.le)
        (hdom t (t + h) (le_add_of_nonneg_right hh.le)).1
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact mul_le_mul_of_nonneg_left
        (hdom t (t + h) (le_add_of_nonneg_right hh.le)).2
        (inv_nonneg.mpr hh.le)
  exact tendsto_nhds_unique hE.tendsto_slope_zero_right hsqueeze

private theorem hasDerivAt_eq_zero_of_increment_domination_Icc
    (A E : Real -> Real) (T t Edot : Real)
    (ht : t ∈ Ioo (0 : Real) T)
    (hA : HasDerivAt A 0 t)
    (hE : HasDerivAt E Edot t)
    (hdom : forall s, s ∈ Icc (0 : Real) T ->
      forall u, u ∈ Icc (0 : Real) T ->
        dist (E s) (E u) <= dist (A s) (A u)) :
    Edot = 0 := by
  have hsmall :
      Filter.Eventually (fun h : Real => t + h ∈ Icc (0 : Real) T)
        (nhdsWithin 0 (Ioi 0)) := by
    have hevent :
        Filter.Eventually (fun h : Real => h < T - t)
          (nhdsWithin 0 (Ioi 0)) :=
      mem_nhdsWithin_of_mem_nhds
        (t := Ioi (0 : Real))
        (Iio_mem_nhds (sub_pos.mpr ht.2))
    filter_upwards [self_mem_nhdsWithin, hevent] with h hh hhT
    exact ⟨(add_pos ht.1 hh).le, (by
      calc
        t + h < t + (T - t) := add_lt_add_right hhT t
        _ = T := by ring : t + h < T).le⟩
  have hbound :
      Filter.Eventually
        (fun h =>
          abs (h⁻¹ * (E (t + h) - E t)) <=
            abs (h⁻¹ * (A (t + h) - A t)))
        (nhdsWithin 0 (Ioi 0)) := by
    filter_upwards [hsmall] with h hth
    have hd := hdom t ⟨ht.1.le, ht.2.le⟩ (t + h) hth
    change abs (E t - E (t + h)) <=
      abs (A t - A (t + h)) at hd
    calc
      abs (h⁻¹ * (E (t + h) - E t)) =
          abs h⁻¹ * abs (E t - E (t + h)) := by
            rw [abs_mul, abs_sub_comm]
      _ <= abs h⁻¹ * abs (A t - A (t + h)) :=
        mul_le_mul_of_nonneg_left hd (abs_nonneg h⁻¹)
      _ = abs (h⁻¹ * (A (t + h) - A t)) := by
        rw [abs_mul, abs_sub_comm]
  have hEabs :
      Tendsto
        (fun h => abs (h⁻¹ * (E (t + h) - E t)))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    apply squeeze_zero'
      (Eventually.of_forall fun h =>
        abs_nonneg (h⁻¹ * (E (t + h) - E t)))
      hbound
    simpa using hA.tendsto_slope_zero_right.abs
  have hEdotAbs :
      Tendsto
        (fun h => abs (h⁻¹ * (E (t + h) - E t)))
        (nhdsWithin 0 (Ioi 0)) (nhds (abs Edot)) :=
    hE.tendsto_slope_zero_right.abs
  have hz : abs Edot = 0 :=
    tendsto_nhds_unique hEdotAbs hEabs
  exact abs_eq_zero.mp hz

noncomputable def verifiedPatchedFluidPolicy
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) : ActionVector Buffer := by
  classical
  let q : ActionVector Buffer :=
    fun a => deriv (fun s => E s a) t / deriv A t
  exact if q ∈ N.fluidPolicyCorrespondence U j k (X t) then q
    else N.measurableFluidPolicySelector U j k (X t)

private theorem verifiedPatchedFluidPolicy_measurable
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (hX : forall i, Measurable (fun t => X t i))
    (a : Option Buffer) :
    Measurable
      (fun t => N.verifiedPatchedFluidPolicy U j k X A E t a) := by
  classical
  let q : Real -> ActionVector Buffer :=
    fun t a => deriv (fun s => E s a) t / deriv A t
  have hq : Measurable q := by
    rw [measurable_pi_iff]
    intro b
    exact (measurable_deriv (fun s => E s b)).div (measurable_deriv A)
  have hpair : Measurable (fun t => (X t, q t)) :=
    (measurable_pi_lambda X hX).prodMk hq
  have hcondition :
      MeasurableSet {t |
        q t ∈ N.fluidPolicyCorrespondence U j k (X t)} := by
    have hgraph :=
      (N.fluidPolicyCorrespondenceGraph_isClosed U j k).measurableSet.preimage
        hpair
    change MeasurableSet {t |
      q t ∈ N.fluidPolicyCorrespondence U j k (X t)} at hgraph
    exact hgraph
  dsimp [q] at hcondition
  unfold verifiedPatchedFluidPolicy
  simp only [ite_apply]
  apply Measurable.ite hcondition
  · exact (measurable_deriv (fun s => E s a)).div (measurable_deriv A)
  · exact measurableFluidPolicySelector_comp N U j k X hX a

private theorem verifiedPatchedFluidPolicy_mem
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) (hstate : IsFluidState (X t)) :
    N.verifiedPatchedFluidPolicy U j k X A E t ∈
      N.fluidPolicyCorrespondence U j k (X t) := by
  classical
  let q : ActionVector Buffer :=
    fun a => deriv (fun s => E s a) t / deriv A t
  by_cases hq : q ∈ N.fluidPolicyCorrespondence U j k (X t)
  · simpa [verifiedPatchedFluidPolicy, q, hq] using hq
  · simp only [verifiedPatchedFluidPolicy, q, if_neg hq]
    exact N.measurableFluidPolicySelector_mem U j k (X t) hstate

private def edgeProgress (r : Real) (l : Nat) : Real :=
  max 0 (min 1 (r - l))

private theorem edgeProgress_mono {r q : Real} (hrq : r <= q) (l : Nat) :
    edgeProgress r l <= edgeProgress q l := by
  unfold edgeProgress
  exact max_le_max le_rfl (min_le_min le_rfl (sub_le_sub_right hrq _))

private def edgeWindowWeight {I : Type*} (edge : I -> Nat)
    (s t : Real) (i : I) : Real :=
  edgeProgress t (edge i) - edgeProgress s (edge i)

private theorem edgeWindowWeight_nonneg {I : Type*} (edge : I -> Nat)
    {s t : Real} (hst : s <= t) (i : I) :
    0 <= edgeWindowWeight edge s t i :=
  sub_nonneg.mpr (edgeProgress_mono hst (edge i))

private def finiteActionInputInterpolate {I : Type*}
    (ids : Finset I) (edge : I -> Nat) (r : Real) : Real :=
  Finset.sum ids fun i => edgeProgress r (edge i)

private def finiteActionVectorInterpolate {I : Type*}
    (N : Network Buffer Server)
    (ids : Finset I) (edge : I -> Nat) (action : I -> Option Buffer)
    (r : Real) : ActionVector Buffer :=
  fun a =>
    Finset.sum ids fun i =>
      edgeProgress r (edge i) * N.actionDirac (action i) a

private theorem finiteActionInputInterpolate_increment {I : Type*}
    (ids : Finset I) (edge : I -> Nat) (s t : Real) :
    finiteActionInputInterpolate ids edge t -
        finiteActionInputInterpolate ids edge s =
      Finset.sum ids (edgeWindowWeight edge s t) := by
  rw [finiteActionInputInterpolate, finiteActionInputInterpolate,
    <- Finset.sum_sub_distrib]
  rfl

private theorem finiteActionVectorInterpolate_increment {I : Type*}
    (N : Network Buffer Server)
    (ids : Finset I) (edge : I -> Nat) (action : I -> Option Buffer)
    (s t : Real) (a : Option Buffer) :
    finiteActionVectorInterpolate N ids edge action t a -
        finiteActionVectorInterpolate N ids edge action s a =
      Finset.sum ids fun i =>
        edgeWindowWeight edge s t i * N.actionDirac (action i) a := by
  rw [finiteActionVectorInterpolate, finiteActionVectorInterpolate,
    <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold edgeWindowWeight
  ring

private theorem finiteActionInterpolate_ratio_mem_epsilon
    {I : Type*} (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    (ids : Finset I) (edge : I -> Nat)
    (K : I -> PNat)
    (z : (r : I) -> JobState Buffer (K r : Nat))
    {s t : Real} (hst : s <= t)
    (hpos :
      0 < finiteActionInputInterpolate ids edge t -
        finiteActionInputInterpolate ids edge s)
    (hK : forall r, r ∈ ids ->
      0 < edgeWindowWeight edge s t r ->
        epsilon⁻¹ <= ((K r : Nat) : Real))
    (hz : forall r, r ∈ ids ->
      0 < edgeWindowWeight edge s t r ->
        IsNearNormalizedState (z r) x epsilon) :
    (fun a =>
      (finiteActionVectorInterpolate N ids edge
            (fun r => U (K r) (z r) j k) t a -
          finiteActionVectorInterpolate N ids edge
            (fun r => U (K r) (z r) j k) s a) /
        (finiteActionInputInterpolate ids edge t -
          finiteActionInputInterpolate ids edge s)) ∈
      N.fluidPolicyEpsilonCorrespondence U j k x epsilon := by
  classical
  let used := ids.filter fun r => 0 < edgeWindowWeight edge s t r
  have hused_subset : used ⊆ ids := Finset.filter_subset _ _
  have hzero (r : I) (hr : r ∈ ids) (hru : r ∉ used) :
      edgeWindowWeight edge s t r = 0 := by
    apply le_antisymm
    · apply not_lt.mp
      intro hp
      exact hru (Finset.mem_filter.mpr ⟨hr, hp⟩)
    · exact edgeWindowWeight_nonneg edge hst r
  have hweight_sum :
      Finset.sum used (fun r =>
        edgeWindowWeight edge s t r /
          (finiteActionInputInterpolate ids edge t -
            finiteActionInputInterpolate ids edge s)) = 1 := by
    rw [Finset.sum_subset hused_subset]
    · rw [<- Finset.sum_div, <- finiteActionInputInterpolate_increment]
      exact div_self (ne_of_gt hpos)
    · intro r hr hru
      rw [hzero r hr hru, zero_div]
  have hvector :
      (fun a =>
        (finiteActionVectorInterpolate N ids edge
              (fun r => U (K r) (z r) j k) t a -
            finiteActionVectorInterpolate N ids edge
              (fun r => U (K r) (z r) j k) s a) /
          (finiteActionInputInterpolate ids edge t -
            finiteActionInputInterpolate ids edge s)) =
        Finset.sum used fun r =>
          (edgeWindowWeight edge s t r /
            (finiteActionInputInterpolate ids edge t -
              finiteActionInputInterpolate ids edge s)) •
            N.actionDirac (U (K r) (z r) j k) := by
    funext a
    rw [finiteActionVectorInterpolate_increment, Finset.sum_apply,
      Finset.sum_div]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_subset hused_subset]
    · apply Finset.sum_congr rfl
      intro r hr
      exact mul_div_right_comm _ _ _
    · intro r hr hru
      simp [hzero r hr hru]
  rw [hvector]
  apply weightedActionAverage_mem_epsilon N U j k x epsilon used
    (fun r => edgeWindowWeight edge s t r /
      (finiteActionInputInterpolate ids edge t -
        finiteActionInputInterpolate ids edge s)) K z
  · intro r hr
    exact div_nonneg (edgeWindowWeight_nonneg edge hst r) hpos.le
  · exact hweight_sum
  · intro r hr
    exact hK r (hused_subset hr) (Finset.mem_filter.mp hr).2
  · intro r hr
    exact hz r (hused_subset hr) (Finset.mem_filter.mp hr).2

private def empiricalPreActionStates {K : Nat}
    (N : Network Buffer Server) (U : N.DeterministicStationaryPolicy K) :
    JobState Buffer K ->
      List (TokenType (Buffer := Buffer) (Server := Server)) ->
      Server -> Buffer -> List (JobState Buffer K)
  | _, [], _, _ => []
  | z, jk :: rest, j, k =>
      if jk = (j, k) then
        z :: empiricalPreActionStates N U (N.queueStep U z jk) rest j k
      else
        empiricalPreActionStates N U (N.queueStep U z jk) rest j k

private theorem empiricalPreActionStates_length {K : Nat}
    (N : Network Buffer Server) (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) :
    (empiricalPreActionStates N U z tokens j k).length =
      tokens.count (j, k) := by
  induction tokens generalizing z with
  | nil => simp [empiricalPreActionStates]
  | cons jk rest ih =>
      by_cases hm : jk = (j, k)
      · subst jk
        simp [empiricalPreActionStates, ih]
      · simp [empiricalPreActionStates, hm, ih]

private theorem empiricalPreActionStates_mem_dist_le {K : Nat}
    (N : Network Buffer Server)
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) {y : JobState Buffer K}
    (hy : y ∈ empiricalPreActionStates N U z tokens j k)
    (i : Buffer) :
    abs ((y i : Real) - (z i : Real)) <= 2 * tokens.length := by
  induction tokens generalizing z with
  | nil =>
      simp [empiricalPreActionStates] at hy
  | cons jk rest ih =>
      have hstep :
          abs (((N.queueStep U z jk i : Nat) : Real) - (z i : Real)) <=
            2 := by
        have hrun :=
          runTokens_l1_le_two_mul_length N U z [jk]
        have hcoord :=
          Finset.single_le_sum
            (fun q _ => abs_nonneg
              (((N.runTokens U z [jk] q : Nat) : Real) - (z q : Real)))
            (Finset.mem_univ i)
        exact hcoord.trans (by simpa using hrun)
      by_cases hm : jk = (j, k)
      · subst jk
        rw [empiricalPreActionStates, if_pos rfl] at hy
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · simp only [sub_self, abs_zero]
          exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
        · have htail := ih (N.queueStep U z (j, k)) hy
          calc
            abs ((y i : Real) - (z i : Real)) <=
                abs ((y i : Real) -
                  (N.queueStep U z (j, k) i : Real)) +
                abs ((N.queueStep U z (j, k) i : Real) -
                  (z i : Real)) := abs_sub_le _ _ _
            _ <= 2 * rest.length + 2 := add_le_add htail hstep
            _ = 2 * ((j, k) :: rest).length := by simp; ring
      · rw [empiricalPreActionStates, if_neg hm] at hy
        have htail := ih (N.queueStep U z jk) hy
        calc
          abs ((y i : Real) - (z i : Real)) <=
              abs ((y i : Real) -
                (N.queueStep U z jk i : Real)) +
              abs ((N.queueStep U z jk i : Real) -
                (z i : Real)) := abs_sub_le _ _ _
          _ <= 2 * rest.length + 2 := add_le_add htail hstep
          _ = 2 * (jk :: rest).length := by simp; ring

private def empiricalActionCount {K : Nat}
    (N : Network Buffer Server) (U : N.DeterministicStationaryPolicy K) :
    JobState Buffer K ->
      List (TokenType (Buffer := Buffer) (Server := Server)) ->
      Server -> Buffer -> ActionVector Buffer
  | _, [], _, _ => 0
  | z, jk :: rest, j, k =>
      (if jk = (j, k) then N.actionDirac (U z jk.1 jk.2) else 0) +
        empiricalActionCount N U (N.queueStep U z jk) rest j k

private theorem empiricalActionCount_eq_preAction_sum {K : Nat}
    (N : Network Buffer Server) (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) :
    empiricalActionCount N U z tokens j k =
      ((empiricalPreActionStates N U z tokens j k).map
        (fun y => N.actionDirac (U y j k))).sum := by
  induction tokens generalizing z with
  | nil => simp [empiricalActionCount, empiricalPreActionStates]
  | cons jk rest ih =>
      by_cases hm : jk = (j, k)
      · subst jk
        simp [empiricalActionCount, empiricalPreActionStates, ih]
      · simp [empiricalActionCount, empiricalPreActionStates, hm, ih]

private theorem empiricalActionCount_some_eq_runAllocationCount {K : Nat}
    (N : Network Buffer Server) (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer) :
    empiricalActionCount N U z tokens j k (some i) =
      (N.runAllocationCount U z tokens i j k : Real) := by
  induction tokens generalizing z with
  | nil => simp [empiricalActionCount, runAllocationCount]
  | cons jk rest ih =>
      by_cases hm : jk = (j, k)
      · subst jk
        by_cases ha : U z j k = some i
        · simp [empiricalActionCount, runAllocationCount,
            actionDirac, ha, ih]
        · have ha' : some i ≠ U z j k := fun h => ha h.symm
          simp [empiricalActionCount, runAllocationCount,
            actionDirac, ha, ha', ih]
      · have halloc :
          ¬(U z jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k) := by
          rintro ⟨_, hj, hk⟩
          exact hm (Prod.ext hj hk)
        simp [empiricalActionCount, runAllocationCount,
          hm, halloc, ih]

private noncomputable def gridPreActionStates
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (K : PNat) (j : Server) (k : Buffer) (l : Fin (K : Nat)) :
    List (JobState Buffer (K : Nat)) :=
  empiricalPreActionStates N (U K)
    (gridQueueState N T x0 U A K l.val)
    (gridTokenBatch T A K l.val) j k

private abbrev GridActionOccurrence
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (K : PNat) (j : Server) (k : Buffer) :=
  Sigma fun l : Fin (K : Nat) =>
    Fin (gridPreActionStates N T x0 U A K j k l).length

private noncomputable def polygonalActionPath
    (N : Network Buffer Server)
    (T : Real) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (K : PNat) (j : Server) (k : Buffer)
    (t : Real) : ActionVector Buffer :=
  let states := gridPreActionStates N T x0 U A K j k
  let ids := (Finset.univ :
    Finset (GridActionOccurrence N T x0 U A K j k))
  fun a =>
    finiteActionVectorInterpolate N ids (fun q => q.1.val)
      (fun q => U K ((states q.1).get q.2) j k)
      (((K : Nat) : Real) * t / T) a / (K : Nat)

private theorem edgeProgress_eq_clamp (r : Real) (l : Nat) :
    edgeProgress r l = existenceClamp01 (r - l) := by
  unfold edgeProgress existenceClamp01
  rcases le_total (r - l) 0 with h | h
  · simp [max_eq_left h, min_eq_right (le_trans h zero_le_one)]
  · by_cases h1 : r - l <= 1
    · simp [max_eq_right h, min_eq_right h1]
    · have h1' : 1 <= r - l := le_of_not_ge h1
      simp [max_eq_right h, min_eq_left h1']

private theorem edgeProgress_le_one (r : Real) (l : Nat) :
    edgeProgress r l <= 1 := by
  unfold edgeProgress
  exact max_le (by norm_num) (min_le_left _ _)

private theorem edgeProgress_pos_imp (r : Real) (l : Nat)
    (h : 0 < edgeProgress r l) :
    (l : Real) < r := by
  unfold edgeProgress at h
  have hm : 0 < min 1 (r - (l : Real)) := by
    rcases max_cases (0 : Real) (min 1 (r - (l : Real))) with heq | heq
    · rw [heq.1] at h
      exact (lt_irrefl 0 h).elim
    · simpa [heq.1] using h
  exact sub_pos.mp ((lt_min_iff.mp hm).2)

private theorem edgeProgress_lt_one_imp (r : Real) (l : Nat)
    (h : edgeProgress r l < 1) :
    r < (l : Real) + 1 := by
  by_contra hn
  have hr : 1 <= r - (l : Real) := by linarith
  unfold edgeProgress at h
  rw [min_eq_left hr, max_eq_right zero_le_one] at h
  exact (lt_irrefl 1 h)

private theorem used_edge_gridTime_close
    (T : Real) (hT : 0 < T) (K : PNat)
    {t h : Real} (hh : 0 < h) (l : Fin (K : Nat))
    (hused :
      0 <
        edgeProgress (((K : Nat) : Real) * (t + h) / T) l.val -
          edgeProgress (((K : Nat) : Real) * t / T) l.val) :
    abs (gridTime T K l.val - t) <
      h + T / (K : Nat) := by
  let r0 : Real := ((K : Nat) : Real) * t / T
  let r1 : Real := ((K : Nat) : Real) * (t + h) / T
  have hp : edgeProgress r0 l.val < edgeProgress r1 l.val :=
    sub_pos.mp hused
  have hr1pos : 0 < edgeProgress r1 l.val :=
    lt_of_le_of_lt (le_max_left (0 : Real) _) hp
  have hr0lt : edgeProgress r0 l.val < 1 :=
    hp.trans_le (edgeProgress_le_one r1 l.val)
  have hlr1 := edgeProgress_pos_imp r1 l.val hr1pos
  have hr0l := edgeProgress_lt_one_imp r0 l.val hr0lt
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hgrid :
      gridTime T K l.val = T * (l.val : Real) / (K : Nat) := by
    unfold gridTime
    rw [Nat.min_eq_left (Nat.le_of_lt l.isLt)]
  have hlower : t - T / (K : Nat) < gridTime T K l.val := by
    dsimp [r0] at hr0l
    rw [hgrid]
    apply (lt_div_iff₀ hK).2
    apply (div_lt_iff₀ hT).1 at hr0l
    rw [sub_mul, div_mul_cancel₀ T (ne_of_gt hK)]
    nlinarith
  have hupper : gridTime T K l.val < t + h := by
    dsimp [r1] at hlr1
    rw [hgrid]
    apply (div_lt_iff₀ hK).2
    apply (lt_div_iff₀ hT).1 at hlr1
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith [div_pos hT hK]

private theorem polygonalInputPath_eq_actionInput
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat)
    (j : Server) (k : Buffer) (t : Real)
    (ht : t ∈ Icc (0 : Real) T) :
    polygonalInputPath T A K t j k =
      finiteActionInputInterpolate
        (Finset.univ :
          Finset (GridActionOccurrence N T x0 U A K j k))
        (fun q => q.1.val) (((K : Nat) : Real) * t / T) /
          (K : Nat) := by
  let states := gridPreActionStates N T x0 U A K j k
  let r : Real := ((K : Nat) : Real) * t / T
  unfold polygonalInputPath
  rw [polygonalInterpolate_eq_ramp K _ hT ht]
  change existenceRampInterpolate K
      (fun l => (gridInputCount T A K l j k : Real) / (K : Nat))
      t T = _
  unfold existenceRampInterpolate
  change (gridInputCount T A K 0 j k : Real) / (K : Nat) + _ = _
  rw [gridInputCount_zero hA K j k]
  simp only [Nat.cast_zero, zero_div, zero_add]
  unfold finiteActionInputInterpolate
  rw [Fintype.sum_sigma]
  simp_rw [edgeProgress_eq_clamp]
  rw [show
    Finset.univ.sum (fun l : Fin (K : Nat) =>
      Finset.univ.sum (fun _q : Fin (states l).length =>
        existenceClamp01 (r - (l.val : Real)))) =
      Finset.univ.sum (fun l : Fin (K : Nat) =>
        ((states l).length : Real) *
          existenceClamp01 (r - (l.val : Real))) by simp]
  rw [Finset.sum_range, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro l hl
  change
    ((gridInputCount T A K (l.val + 1) j k : Real) / (K : Nat) -
        (gridInputCount T A K l.val j k : Real) / (K : Nat)) *
        existenceClamp01 (r - l.val) =
      (((states l).length : Real) *
        existenceClamp01 (r - l.val)) / (K : Nat)
  rw [show (states l).length =
      gridInputCount T A K (l.val + 1) j k -
        gridInputCount T A K l.val j k by
    dsimp [states, gridPreActionStates]
    rw [empiricalPreActionStates_length,
      gridTokenBatch_count hT hA]]
  rw [Nat.cast_sub
    (gridInputCount_mono hT hA K (Nat.le_succ l.val) j k)]
  ring

private theorem gridPreAction_sum_some
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Fin (K : Nat))
    (i : Buffer) (j : Server) (k : Buffer) :
    ((gridPreActionStates N T x0 U A K j k l).map
      (fun y => N.actionDirac (U K y j k))).sum (some i) =
      (gridAllocationCount N T x0 U A K (l.val + 1) i j k : Real) -
        (gridAllocationCount N T x0 U A K l.val i j k : Real) := by
  let z := gridQueueState N T x0 U A K l.val
  let batch := gridTokenBatch T A K l.val
  have hemp := congrFun
    (empiricalActionCount_eq_preAction_sum N (U K) z batch j k)
    (some i)
  rw [empiricalActionCount_some_eq_runAllocationCount] at hemp
  change
    ((empiricalPreActionStates N (U K) z batch j k).map
      (fun y => N.actionDirac (U K y j k))).sum (some i) = _
  rw [<- hemp]
  dsimp [z, batch]
  have happ :=
    runAllocationCount_append N (U K)
      (roundedState x0 (K : Nat)
        (Classical.choice (inferInstance : Nonempty Buffer)))
      (gridTokenPrefix T A K l.val)
      (gridTokenBatch T A K l.val) i j k
  unfold gridAllocationCount
  unfold gridQueueState
  push_cast
  rw [show gridTokenPrefix T A K (l.val + 1) =
    gridTokenPrefix T A K l.val ++ gridTokenBatch T A K l.val by rfl]
  rw [happ]
  rw [Nat.cast_add]
  ring

private theorem polygonalActionPath_some
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (K : PNat) (i : Buffer) (j : Server) (k : Buffer)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    polygonalActionPath N T x0 U A K j k t (some i) =
      polygonalAllocationPath N T x0 U A K t i j k := by
  let states := gridPreActionStates N T x0 U A K j k
  let r : Real := ((K : Nat) : Real) * t / T
  unfold polygonalActionPath finiteActionVectorInterpolate
  dsimp only
  rw [Fintype.sum_sigma]
  simp_rw [edgeProgress_eq_clamp]
  rw [show
    Finset.univ.sum (fun l : Fin (K : Nat) =>
      Finset.univ.sum (fun q : Fin (states l).length =>
        existenceClamp01 (r - (l.val : Real)) *
          N.actionDirac (U K ((states l).get q) j k) (some i))) =
      Finset.univ.sum (fun l : Fin (K : Nat) =>
        (((states l).map
          (fun y => N.actionDirac (U K y j k))).sum (some i)) *
            existenceClamp01 (r - (l.val : Real))) by
    apply Finset.sum_congr rfl
    intro l hl
    have hsum :
        ((states l).map
          (fun y => N.actionDirac (U K y j k))).sum =
          Finset.univ.sum (fun q : Fin (states l).length =>
            N.actionDirac (U K ((states l).get q) j k)) := by
      rw [<- List.sum_ofFn]
      change _ = (List.ofFn
        ((fun y => N.actionDirac (U K y j k)) ∘
          (states l).get)).sum
      rw [<- List.map_ofFn, List.ofFn_get]
    rw [hsum, Finset.sum_apply]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    ring]
  rw [Finset.sum_div]
  unfold polygonalAllocationPath
  rw [polygonalInterpolate_eq_ramp K _ hT ht]
  unfold existenceRampInterpolate
  change _ =
    (gridAllocationCount N T x0 U A K 0 i j k : Real) / (K : Nat) + _
  rw [show
    (gridAllocationCount N T x0 U A K 0 i j k : Real) / (K : Nat) = 0 by
      simp [gridAllocationCount, gridTokenPrefix, runAllocationCount]]
  rw [zero_add]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro l hl
  rw [gridPreAction_sum_some N T hT x0 U A K l i j k]
  ring

private theorem polygonalActionPath_sum
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat)
    (j : Server) (k : Buffer) (t : Real)
    (ht : t ∈ Icc (0 : Real) T) :
    Finset.univ.sum (polygonalActionPath N T x0 U A K j k t) =
      polygonalInputPath T A K t j k := by
  rw [polygonalInputPath_eq_actionInput N T hT x0 U A hA K j k t ht]
  unfold polygonalActionPath finiteActionVectorInterpolate
  dsimp only
  change
    Finset.univ.sum (fun a =>
      (Finset.univ.sum (fun q :
          GridActionOccurrence N T x0 U A K j k =>
        edgeProgress (((K : Nat) : Real) * t / T) q.1.val *
          N.actionDirac
            (U K ((gridPreActionStates N T x0 U A K j k q.1).get q.2)
              j k) a)) / (K : Nat)) = _
  rw [<- Finset.sum_div]
  unfold finiteActionInputInterpolate
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [<- Finset.mul_sum]
  rw [(N.actionDirac_isDistribution
    (U K ((gridPreActionStates N T x0 U A K j k q.1).get q.2) j k)).2]
  rw [mul_one]

private theorem polygonalActionPath_none
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat)
    (j : Server) (k : Buffer) (t : Real)
    (ht : t ∈ Icc (0 : Real) T) :
    polygonalActionPath N T x0 U A K j k t none =
      polygonalInputPath T A K t j k -
        Finset.univ.sum (fun i : Buffer =>
          polygonalAllocationPath N T x0 U A K t i j k) := by
  have hsum :=
    polygonalActionPath_sum N T hT x0 U A hA K j k t ht
  have hsome (i : Buffer) :=
    polygonalActionPath_some N T hT x0 U A K i j k t ht
  rw [show
    Finset.univ.sum (polygonalActionPath N T x0 U A K j k t) =
      polygonalActionPath N T x0 U A K j k t none +
        Finset.univ.sum (fun i : Buffer =>
          polygonalActionPath N T x0 U A K j k t (some i)) by
    rw [Fintype.sum_option]] at hsum
  simp_rw [hsome] at hsum
  linarith

private theorem finiteDifferenceRatio_polygonalAction_mem_epsilon
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat)
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    (t h : Real) (ht : t ∈ Icc (0 : Real) T)
    (hth : t + h ∈ Icc (0 : Real) T) (hh : 0 < h)
    (hpos :
      0 < polygonalInputPath T A K (t + h) j k -
        polygonalInputPath T A K t j k)
    (hK : epsilon⁻¹ <= (K : Real))
    (hnear : forall l
      (y : JobState Buffer (K : Nat)),
      y ∈ gridPreActionStates N T x0 U A K j k l ->
      0 < edgeProgress (((K : Nat) : Real) * (t + h) / T) l.val -
        edgeProgress (((K : Nat) : Real) * t / T) l.val ->
      IsNearNormalizedState y x epsilon) :
    finiteDifferenceRatio
        (fun s => polygonalInputPath T A K s j k)
        (polygonalActionPath N T x0 U A K j k) t h ∈
      N.fluidPolicyEpsilonCorrespondence U j k x epsilon := by
  classical
  let states := gridPreActionStates N T x0 U A K j k
  let ids := (Finset.univ :
    Finset (GridActionOccurrence N T x0 U A K j k))
  let edge : GridActionOccurrence N T x0 U A K j k -> Nat :=
    fun q => q.1.val
  let r0 : Real := ((K : Nat) : Real) * t / T
  let r1 : Real := ((K : Nat) : Real) * (t + h) / T
  have hr : r0 <= r1 := by
    dsimp [r0, r1]
    apply (div_le_div_iff_of_pos_right hT).2
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hraw :
      0 < finiteActionInputInterpolate ids edge r1 -
        finiteActionInputInterpolate ids edge r0 := by
    rw [show finiteActionInputInterpolate ids edge r1 =
        (K : Real) * polygonalInputPath T A K (t + h) j k by
      rw [polygonalInputPath_eq_actionInput
        N T hT x0 U A hA K j k (t + h) hth]
      dsimp [ids, edge, r1]
      field_simp]
    rw [show finiteActionInputInterpolate ids edge r0 =
        (K : Real) * polygonalInputPath T A K t j k by
      rw [polygonalInputPath_eq_actionInput
        N T hT x0 U A hA K j k t ht]
      dsimp [ids, edge, r0]
      field_simp]
    nlinarith [show (0 : Real) < (K : Nat) by positivity]
  have hm := finiteActionInterpolate_ratio_mem_epsilon
    N U j k x epsilon ids edge (fun _ => K)
      (fun q => (states q.1).get q.2) hr hraw
      (by intro q hq hw; simpa using hK)
      (by
        intro q hq hw
        apply hnear q.1 ((states q.1).get q.2)
          (List.get_mem (states q.1) q.2)
        simpa [edgeWindowWeight, edge, r0, r1] using hw)
  convert hm using 1
  funext a
  unfold finiteDifferenceRatio
  change
    (polygonalActionPath N T x0 U A K j k (t + h) a -
        polygonalActionPath N T x0 U A K j k t a) /
      (polygonalInputPath T A K (t + h) j k -
        polygonalInputPath T A K t j k) = _
  rw [show polygonalInputPath T A K (t + h) j k =
      finiteActionInputInterpolate ids edge r1 / (K : Nat) by
    exact polygonalInputPath_eq_actionInput
      N T hT x0 U A hA K j k (t + h) hth]
  rw [show polygonalInputPath T A K t j k =
      finiteActionInputInterpolate ids edge r0 / (K : Nat) by
    exact polygonalInputPath_eq_actionInput
      N T hT x0 U A hA K j k t ht]
  dsimp [polygonalActionPath, states, ids, edge, r0, r1]
  field_simp

/-
private theorem eventually_gridPreActionStates_near
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (polygonalAllocationPath N T x0 U A
              ⟨q n + 1, by omega⟩ t i j k)
            (E t i j k) < epsilon)
    (X : FluidStatePath Buffer)
    (hXeq : X = fun t i =>
      x0 i +
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun l : Buffer => E t l j i) -
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer => E t i j k))
    (t : Real) (ht : t ∈ Ioo (0 : Real) T)
    (hXcontinuous : ContinuousAt X t)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun h =>
        Filter.Eventually
          (fun n =>
            forall j k (l : Fin (q n + 1))
              (y : JobState Buffer (q n + 1)),
              y ∈ gridPreActionStates N T x0 U A
                ⟨q n + 1, by omega⟩ j k l ->
              0 <
                edgeProgress
                    (((q n + 1 : Nat) : Real) * (t + h) / T) l.val -
                  edgeProgress
                    (((q n + 1 : Nat) : Real) * t / T) l.val ->
              IsNearNormalizedState y (X t) epsilon)
          atTop)
      (nhdsWithin 0 (Ioi 0)) := by
  obtain ⟨eta, heta, hXclose⟩ :=
    Metric.continuousAt_iff.mp hXcontinuous
      (epsilon / 3) (by positivity)
  obtain ⟨nQ, hnQ⟩ :=
    polygonalQueuePath_uniform_convergence_of_allocationLimit
      N T hT x0 U A q hq E hconv (epsilon / 3) (by positivity)
  obtain ⟨Kbatch, hKbatch⟩ :=
    gridTokenBatch_scaled_length_uniform_zero T hT A hA
      (epsilon / 6) (by positivity)
  obtain ⟨Kmesh, hKmesh⟩ :=
    exists_nat_gt (3 * T / eta)
  let n0 := max nQ (max Kbatch Kmesh)
  have hwindow : 0 < min (eta / 3) (T - t) := by
    exact lt_min (div_pos heta (by norm_num)) (sub_pos.mpr ht.2)
  have hsmallEventually :
      Filter.Eventually
        (fun h : Real => h < min (eta / 3) (T - t))
        (nhdsWithin 0 (Ioi 0)) :=
    mem_nhdsWithin_of_mem_nhds
      (t := Ioi (0 : Real))
      (Iio_mem_nhds hwindow)
  filter_upwards [self_mem_nhdsWithin, hsmallEventually]
    with h hh hsmall
  have hhpos : 0 < h := hh
  have hhEta : h < eta / 3 := hsmall.1
  refine Filter.eventually_atTop.mpr ⟨n0, fun n hn j k l y hy hused => ?_⟩
  let K : PNat := ⟨q n + 1, by omega⟩
  have hnQ' : nQ <= n := (le_max_left _ _).trans hn
  have hnBatch : Kbatch <= (K : Nat) := by
    dsimp [K, n0] at hn ⊢
    have : Kbatch <= n :=
      (le_max_left Kbatch Kmesh).trans
        ((le_max_right nQ (max Kbatch Kmesh)).trans hn)
    exact this.trans (by omega)
  have hnMesh : Kmesh <= (K : Nat) := by
    dsimp [K, n0] at hn ⊢
    have : Kmesh <= n :=
      (le_max_right Kbatch Kmesh).trans
        ((le_max_right nQ (max Kbatch Kmesh)).trans hn)
    exact this.trans (by omega)
  have hmesh : T / (K : Nat) < eta / 3 := by
    have hKmeshReal : (Kmesh : Real) <= (K : Nat) := by
      exact_mod_cast hnMesh
    have hraw : 3 * T / eta < (K : Real) :=
      hKmesh.trans_le hKmeshReal
    have hKpos : (0 : Real) < (K : Nat) := by positivity
    apply (div_lt_iff₀ hKpos).2
    apply (div_lt_iff₀ heta).1 at hraw
    nlinarith
  have hlclose :
      abs (gridTime T K l.val - t) < eta := by
    exact (used_edge_gridTime_close T hT K hhpos l hused).trans
      (by linarith)
  have hgridmem : gridTime T K l.val ∈ Icc (0 : Real) T :=
    gridTime_mem_Icc hT K l.val
  have hqueue (i : Buffer) :
      abs
        (polygonalQueuePath N T x0 U A K
            (gridTime T K l.val) i -
          X (gridTime T K l.val) i) < epsilon / 3 := by
    rw [hXeq]
    exact hnQ n hnQ' i (gridTime T K l.val) hgridmem
  have hXvector :
      dist (X (gridTime T K l.val)) (X t) < epsilon / 3 := by
    apply hXclose
    simpa only [Real.dist_eq] using hlclose
  have hXcoord (i : Buffer) :
      abs (X (gridTime T K l.val) i - X t i) < epsilon / 3 := by
    have hle :
        dist (X (gridTime T K l.val) i) (X t i) <=
          dist (X (gridTime T K l.val)) (X t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (X (gridTime T K l.val)) (X t) <= _) i
    rw [Real.dist_eq] at hle
    exact hle.trans_lt hXvector
  have hbatch :
      ((gridTokenBatch T A K l.val).length : Real) / (K : Nat) <
        epsilon / 6 :=
    hKbatch K hnBatch l.val l.isLt
  intro i
  have hyraw :=
    empiricalPreActionStates_mem_dist_le N (U K)
      (gridQueueState N T x0 U A K l.val)
      (gridTokenBatch T A K l.val) j k hy i
  have hygrid :
      abs
        ((y i : Real) / (K : Nat) -
          (gridQueueState N T x0 U A K l.val i : Real) / (K : Nat)) <
        epsilon / 3 := by
    have hKpos : (0 : Real) < (K : Nat) := by positivity
    rw [<- sub_div, abs_div, abs_of_pos hKpos]
    exact (div_lt_div_of_pos_right hyraw hKpos).trans_lt (by
      calc
        (2 * (gridTokenBatch T A K l.val).length : Real) / (K : Nat) =
            2 * (((gridTokenBatch T A K l.val).length : Real) /
              (K : Nat)) := by ring
        _ < 2 * (epsilon / 6) := by gcongr
        _ = epsilon / 3 := by ring)
  have hgridEq :
      polygonalQueuePath N T x0 U A K (gridTime T K l.val) i =
        (gridQueueState N T x0 U A K l.val i : Real) / (K : Nat) := by
    unfold polygonalQueuePath
    rw [gridTime_eq_gridPoint T K l.val (Nat.le_of_lt l.isLt)]
    exact polygonalInterpolate_grid K _ T hT l.val
      (Nat.le_of_lt l.isLt)
  rw [<- hgridEq] at hygrid
  calc
    abs ((y i : Real) / (q n + 1) - X t i) <=
        abs ((y i : Real) / (K : Nat) -
          polygonalQueuePath N T x0 U A K
            (gridTime T K l.val) i) +
        abs (polygonalQueuePath N T x0 U A K
            (gridTime T K l.val) i -
          X (gridTime T K l.val) i) +
        abs (X (gridTime T K l.val) i - X t i) := by
      dsimp [K]
      have h1 := abs_sub_le
        ((y i : Real) / ((q n + 1 : Nat) : Real))
        (polygonalQueuePath N T x0 U A
          ⟨q n + 1, by omega⟩ (gridTime T
            ⟨q n + 1, by omega⟩ l.val) i)
        (X t i)
      have h2 := abs_sub_le
        (polygonalQueuePath N T x0 U A
          ⟨q n + 1, by omega⟩ (gridTime T
            ⟨q n + 1, by omega⟩ l.val) i)
        (X (gridTime T ⟨q n + 1, by omega⟩ l.val) i)
        (X t i)
      linarith
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by
      linarith [hygrid, hqueue i, hXcoord i]
    _ = epsilon := by ring
-/

private theorem exists_polygonalAllocation_limit
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) :
    exists q : Nat -> Nat, StrictMono q /\
      exists E : FluidAllocationPath Buffer Server,
        (forall i j k, ContinuousOn (fun t => E t i j k)
          (Icc (0 : Real) T)) /\
        forall epsilon, 0 < epsilon ->
          exists n0, forall n, n0 <= n ->
            forall i j k t, t ∈ Icc (0 : Real) T ->
              dist
                (polygonalAllocationPath N T x0 U A
                  ⟨q n + 1, by omega⟩ t i j k)
                (E t i j k) < epsilon := by
  let f : Nat -> Real -> (Buffer × Server × Buffer -> Real) :=
    fun n t ijk =>
      polygonalAllocationPath N T x0 U A
        ⟨n + 1, by omega⟩ t ijk.1 ijk.2.1 ijk.2.2
  let g : Nat -> (Server × Buffer) -> Real -> Real :=
    fun n jk t =>
      polygonalInputPath T A ⟨n + 1, by omega⟩ t jk.1 jk.2
  let control : (Server × Buffer) -> Real -> Real :=
    fun jk t => A t jk.1 jk.2
  let M : Real :=
    Finset.univ.sum (fun jk : Server × Buffer => A T jk.1 jk.2)
  have hM : 0 <= M := by
    apply Finset.sum_nonneg
    intro jk hjk
    rw [<- hA.2.2 jk.1 jk.2]
    exact hA.2.1 jk.1 jk.2 ⟨le_rfl, hT.le⟩
      ⟨hT.le, le_rfl⟩ hT.le
  have hf (n : Nat) :
      ContinuousOn (f n) (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro ijk
    exact (continuous_polygonalAllocationPath N T x0 U A
      ⟨n + 1, by omega⟩ ijk.1 ijk.2.1 ijk.2.2).continuousOn
  have hbound (n : Nat) (t : Real) (ht : t ∈ Icc (0 : Real) T) :
      dist (f n t) (0 : Buffer × Server × Buffer -> Real) <= M := by
    apply (dist_pi_le_iff hM).2
    intro ijk
    have hb := polygonalAllocationPath_nonneg_le
      N T hT x0 U A hA ⟨n + 1, by omega⟩ t ht
        ijk.1 ijk.2.1 ijk.2.2
    have hcoord :
        A T ijk.2.1 ijk.2.2 <= M := by
      dsimp [M]
      exact Finset.single_le_sum
        (s := (Finset.univ : Finset (Server × Buffer)))
        (f := fun jk : Server × Buffer => A T jk.1 jk.2)
        (by
          intro jk hjk
          rw [<- hA.2.2 jk.1 jk.2]
          exact hA.2.1 jk.1 jk.2 ⟨le_rfl, hT.le⟩
            ⟨hT.le, le_rfl⟩ hT.le)
        (Finset.mem_univ (ijk.2.1, ijk.2.2))
    simpa [f, Real.dist_eq, abs_of_nonneg hb.1] using hb.2.trans hcoord
  have hcontrol (jk : Server × Buffer) :
      ContinuousOn (control jk) (Icc (0 : Real) T) := by
    simpa [control, uIcc_of_le hT.le] using
      (hA.1 jk.1 jk.2).continuousOn
  have hgconv :
      forall epsilon, 0 < epsilon ->
        exists n0, forall n, n0 <= n ->
          forall jk t, t ∈ Icc (0 : Real) T ->
            dist (g n jk t) (control jk t) < epsilon := by
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ :=
      polygonalInputPath_uniform_convergence T hT A hA epsilon hepsilon
    refine ⟨n0, fun n hn jk t ht => ?_⟩
    simpa [g, control, Real.dist_eq] using hn0 n hn jk.1 jk.2 t ht
  have hdom (n : Nat) (s : Real) (hs : s ∈ Icc (0 : Real) T)
      (t : Real) (ht : t ∈ Icc (0 : Real) T) :
      dist (f n s) (f n t) <=
        Finset.univ.sum (fun jk =>
          dist (g n jk s) (g n jk t)) := by
    apply (dist_pi_le_iff
      (Finset.sum_nonneg (fun _ _ => dist_nonneg))).2
    intro ijk
    exact polygonalAllocationPath_increment_domination
      N T hT x0 U A hA ⟨n + 1, by omega⟩
        ijk.1 ijk.2.1 ijk.2.2 hs ht
  obtain ⟨q, hq, limit, hlimit_cont, hconv⟩ :=
    exists_uniformly_convergent_subsequence_controlled
      (f := f) (g := g) (control := control)
      (center := (0 : Buffer × Server × Buffer -> Real))
      hf hbound hcontrol hgconv hdom
  let E : FluidAllocationPath Buffer Server :=
    fun t i j k => limit t (i, j, k)
  refine ⟨q, hq, E, ?_, ?_⟩
  · intro i j k
    exact (continuousOn_pi.mp hlimit_cont) (i, j, k)
  · intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := hconv epsilon hepsilon
    refine ⟨n0, fun n hn i j k t ht => ?_⟩
    have hall := hn0 n hn t ht
    exact lt_of_le_of_lt
      ((dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (f (q n) t) (limit t) <= _) (i, j, k))
      hall

private theorem allocationLimit_properties
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (polygonalAllocationPath N T x0 U A
              ⟨q n + 1, by omega⟩ t i j k)
            (E t i j k) < epsilon) :
    (forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T) /\
    (forall i j k, E 0 i j k = 0) /\
    (forall t, t ∈ Icc (0 : Real) T -> forall i j k,
      ¬N.compatible i j -> E t i j k = 0) /\
    (forall i j k, forall s, s ∈ Icc (0 : Real) T ->
      forall t, t ∈ Icc (0 : Real) T ->
        dist (E s i j k) (E t i j k) <=
          dist (A s j k) (A t j k)) := by
  have hinput :
      forall epsilon, 0 < epsilon ->
        exists n0, forall n, n0 <= n ->
          forall j k t, t ∈ Icc (0 : Real) T ->
            dist
              (polygonalInputPath T A ⟨q n + 1, by omega⟩ t j k)
              (A t j k) < epsilon := by
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ :=
      polygonalInputPath_uniform_convergence T hT A hA epsilon hepsilon
    refine ⟨n0, fun n hn j k t ht => ?_⟩
    have hqn : n0 <= q n := hn.trans (hq.id_le n)
    simpa [Real.dist_eq] using hn0 (q n) hqn j k t ht
  have hac : forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T := by
    intro i j k
    apply absolutelyContinuousOnInterval_of_uniform_limits_finset
      (X := Real) (Y := Unit)
      (f := fun n t =>
        polygonalAllocationPath N T x0 U A
          ⟨q n + 1, by omega⟩ t i j k)
      (limit := fun t => E t i j k)
      (g := fun n _ t =>
        polygonalInputPath T A ⟨q n + 1, by omega⟩ t j k)
      (control := fun _ t => A t j k)
      (s := Finset.univ)
    · intro epsilon hepsilon
      obtain ⟨n0, hn0⟩ := hconv epsilon hepsilon
      exact ⟨n0, fun n hn t ht => hn0 n hn i j k t
        (by simpa [uIcc_of_le hT.le] using ht)⟩
    · intro epsilon hepsilon
      obtain ⟨n0, hn0⟩ := hinput epsilon hepsilon
      exact ⟨n0, fun n hn z hz t ht => hn0 n hn j k t
        (by simpa [uIcc_of_le hT.le] using ht)⟩
    · intro z hz
      exact hA.1 j k
    · intro n s hs t ht
      simp only [Finset.univ_unique, Finset.sum_singleton]
      exact polygonalAllocationPath_increment_matching
        N T hT x0 U A hA ⟨q n + 1, by omega⟩ i j k
        (by simpa [uIcc_of_le hT.le] using hs)
        (by simpa [uIcc_of_le hT.le] using ht)
  have hzero : forall i j k, E 0 i j k = 0 := by
    intro i j k
    have htend :
        Tendsto
          (fun n => polygonalAllocationPath N T x0 U A
            ⟨q n + 1, by omega⟩ 0 i j k)
          atTop (nhds (E 0 i j k)) := by
      rw [Metric.tendsto_atTop]
      intro epsilon hepsilon
      obtain ⟨n0, hn0⟩ := hconv epsilon hepsilon
      exact ⟨n0, fun n hn => hn0 n hn i j k 0 ⟨le_rfl, hT.le⟩⟩
    have hz :
        (fun n => polygonalAllocationPath N T x0 U A
          ⟨q n + 1, by omega⟩ 0 i j k) = fun _ => 0 := by
      funext n
      exact polygonalAllocationPath_zero N T hT x0 U A
        ⟨q n + 1, by omega⟩ i j k
    rw [hz] at htend
    exact tendsto_nhds_unique htend tendsto_const_nhds
  have hincompat :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i j k, ¬N.compatible i j -> E t i j k = 0 := by
    intro t ht i j k hij
    have htend :
        Tendsto
          (fun n => polygonalAllocationPath N T x0 U A
            ⟨q n + 1, by omega⟩ t i j k)
          atTop (nhds (E t i j k)) := by
      rw [Metric.tendsto_atTop]
      intro epsilon hepsilon
      obtain ⟨n0, hn0⟩ := hconv epsilon hepsilon
      exact ⟨n0, fun n hn => hn0 n hn i j k t ht⟩
    have hz :
        (fun n => polygonalAllocationPath N T x0 U A
          ⟨q n + 1, by omega⟩ t i j k) = fun _ => 0 := by
      funext n
      exact polygonalAllocationPath_incompatible
        N T x0 U A ⟨q n + 1, by omega⟩ t i j k hij
    rw [hz] at htend
    exact tendsto_nhds_unique htend tendsto_const_nhds
  have hdom :
      forall i j k, forall s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T ->
          dist (E s i j k) (E t i j k) <=
            dist (A s j k) (A t j k) := by
    intro i j k s hs t ht
    simpa only [Finset.univ_unique, Finset.sum_singleton] using
      (dist_le_finset_of_uniform_limits
        (X := Real) (Y := Unit)
        (a := 0) (b := T)
        (f := fun n t =>
          polygonalAllocationPath N T x0 U A
            ⟨q n + 1, by omega⟩ t i j k)
        (limit := fun t => E t i j k)
        (g := fun n _ t =>
          polygonalInputPath T A ⟨q n + 1, by omega⟩ t j k)
        (control := fun _ t => A t j k)
        (s := Finset.univ)
        (by
          intro epsilon hepsilon
          obtain ⟨n0, hn0⟩ := hconv epsilon hepsilon
          exact ⟨n0, fun n hn t ht => hn0 n hn i j k t
            (by simpa [uIcc_of_le hT.le] using ht)⟩)
        (by
          intro epsilon hepsilon
          obtain ⟨n0, hn0⟩ := hinput epsilon hepsilon
          exact ⟨n0, fun n hn z hz t ht => hn0 n hn j k t
            (by simpa [uIcc_of_le hT.le] using ht)⟩)
        (by
          intro n s hs t ht
          simp only [Finset.univ_unique, Finset.sum_singleton]
          exact polygonalAllocationPath_increment_matching
            N T hT x0 U A hA ⟨q n + 1, by omega⟩ i j k
            (by simpa [uIcc_of_le hT.le] using hs)
            (by simpa [uIcc_of_le hT.le] using ht))
        (by simpa [uIcc_of_le hT.le] using hs)
        (by simpa [uIcc_of_le hT.le] using ht))
  exact ⟨hac, hzero, hincompat, hdom⟩

private theorem polygonalQueuePath_tendsto_of_allocationLimit
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (polygonalAllocationPath N T x0 U A
              ⟨q n + 1, by omega⟩ t i j k)
            (E t i j k) < epsilon)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) (i : Buffer) :
    Tendsto
      (fun n =>
        polygonalQueuePath N T x0 U A
          ⟨q n + 1, by omega⟩ t i)
      atTop
      (nhds
        (x0 i +
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun l : Buffer => E t l j i) -
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer => E t i j k))) := by
  have hE (a : Buffer) (j : Server) (k : Buffer) :
      Tendsto
        (fun n =>
          polygonalAllocationPath N T x0 U A
            ⟨q n + 1, by omega⟩ t a j k)
        atTop (nhds (E t a j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := hconv epsilon hepsilon
    exact ⟨n0, fun n hn => hn0 n hn a j k t ht⟩
  have hrounded :
      Tendsto
        (fun n =>
          ((roundedState x0 (q n + 1)
            (Classical.choice (inferInstance : Nonempty Buffer)) i : Nat) :
              Real) / (q n + 1 : Nat))
        atTop (nhds (x0 i)) := by
    exact (roundedState_scaled_tendsto x0 i).comp hq.tendsto_atTop
  have hincoming :
      Tendsto
        (fun n =>
          Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun l : Buffer =>
              polygonalAllocationPath N T x0 U A
                ⟨q n + 1, by omega⟩ t l j i)
        atTop
        (nhds
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun l : Buffer => E t l j i)) := by
    apply tendsto_finsetSum
    intro j hj
    apply tendsto_finsetSum
    intro l hl
    exact hE l j i
  have houtgoing :
      Tendsto
        (fun n =>
          Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer =>
              polygonalAllocationPath N T x0 U A
                ⟨q n + 1, by omega⟩ t i j k)
        atTop
        (nhds
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer => E t i j k)) := by
    apply tendsto_finsetSum
    intro j hj
    apply tendsto_finsetSum
    intro k hk
    exact hE i j k
  refine (hrounded.add hincoming |>.sub houtgoing).congr' ?_
  exact Eventually.of_forall fun n =>
    (polygonalQueuePath_balance N hT x0 U A
      ⟨q n + 1, by omega⟩ ht i).symm

private theorem polygonalQueuePath_uniform_convergence_of_allocationLimit
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (polygonalAllocationPath N T x0 U A
              ⟨q n + 1, by omega⟩ t i j k)
            (E t i j k) < epsilon) :
    let X : FluidStatePath Buffer := fun t i =>
      x0 i +
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun l : Buffer => E t l j i) -
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer => E t i j k)
    forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall i t, t ∈ Icc (0 : Real) T ->
          abs
            (polygonalQueuePath N T x0 U A
                ⟨q n + 1, by omega⟩ t i -
              X t i) < epsilon := by
  dsimp only
  intro epsilon hepsilon
  let D : Real :=
    1 + 2 * ((Fintype.card Server : Nat) : Real) *
      (Fintype.card Buffer : Nat)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  let delta := epsilon / D
  have hdelta : 0 < delta := div_pos hepsilon hD
  obtain ⟨nE, hnE⟩ := hconv delta hdelta
  have hrounded :
      Tendsto
        (fun n i =>
          ((roundedState x0 (q n + 1)
            (Classical.choice (inferInstance : Nonempty Buffer)) i : Nat) :
              Real) / (q n + 1 : Nat))
        atTop (nhds (fun i => x0 i)) := by
    rw [tendsto_pi_nhds]
    intro i
    exact (roundedState_scaled_tendsto x0 i).comp hq.tendsto_atTop
  have hroundedEventually :
      forall i, Filter.Eventually
        (fun n =>
          abs
            (((roundedState x0 (q n + 1)
              (Classical.choice (inferInstance : Nonempty Buffer)) i :
                Nat) : Real) / (q n + 1 : Nat) - x0 i) < delta)
        atTop := by
    intro i
    have hi := tendsto_pi_nhds.mp hrounded i
    obtain ⟨n0, hn0⟩ := Metric.tendsto_atTop.mp hi delta hdelta
    exact Filter.eventually_atTop.mpr
      ⟨n0, fun n hn => by simpa only [Real.dist_eq] using hn0 n hn⟩
  have hroundedAll :
      Filter.Eventually
        (fun n => forall i,
          abs
            (((roundedState x0 (q n + 1)
              (Classical.choice (inferInstance : Nonempty Buffer)) i :
                Nat) : Real) / (q n + 1 : Nat) - x0 i) < delta)
        atTop := by
    simpa only [eventually_all] using hroundedEventually
  obtain ⟨nR, hnR⟩ := (eventually_atTop.1 hroundedAll)
  refine ⟨max nE nR, fun n hn i t ht => ?_⟩
  have hnE' : nE <= n := (le_max_left _ _).trans hn
  have hnR' : nR <= n := (le_max_right _ _).trans hn
  have hr := hnR n hnR' i
  have hcoord (a : Buffer) (j : Server) (k : Buffer) :
      abs
        (polygonalAllocationPath N T x0 U A
            ⟨q n + 1, by omega⟩ t a j k -
          E t a j k) < delta := by
    simpa only [Real.dist_eq] using hnE n hnE' a j k t ht
  have hin :
      abs
        ((Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun l : Buffer =>
              polygonalAllocationPath N T x0 U A
                ⟨q n + 1, by omega⟩ t l j i) -
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun l : Buffer => E t l j i)) <=
        ((Fintype.card Server : Nat) : Real) *
          (Fintype.card Buffer : Nat) * delta := by
    rw [<- Finset.sum_sub_distrib]
    simp_rw [<- Finset.sum_sub_distrib]
    calc
      abs (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun l : Buffer =>
            (polygonalAllocationPath N T x0 U A
                ⟨q n + 1, by omega⟩ t l j i - E t l j i)) <=
          Finset.univ.sum (fun j : Server =>
            abs (Finset.univ.sum fun l : Buffer =>
              (polygonalAllocationPath N T x0 U A
                  ⟨q n + 1, by omega⟩ t l j i - E t l j i))) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum (fun _j : Server =>
            Finset.univ.sum fun _l : Buffer => delta) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun l hl => (hcoord l j i).le)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.cast_ofNat]; ring
  have hout :
      abs
        ((Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer =>
              polygonalAllocationPath N T x0 U A
                ⟨q n + 1, by omega⟩ t i j k) -
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer => E t i j k)) <=
        ((Fintype.card Server : Nat) : Real) *
          (Fintype.card Buffer : Nat) * delta := by
    rw [<- Finset.sum_sub_distrib]
    simp_rw [<- Finset.sum_sub_distrib]
    calc
      abs (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer =>
            (polygonalAllocationPath N T x0 U A
                ⟨q n + 1, by omega⟩ t i j k - E t i j k)) <=
          Finset.univ.sum (fun j : Server =>
            abs (Finset.univ.sum fun k : Buffer =>
              (polygonalAllocationPath N T x0 U A
                  ⟨q n + 1, by omega⟩ t i j k - E t i j k))) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum (fun _j : Server =>
            Finset.univ.sum fun _k : Buffer => delta) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun k hk => (hcoord i j k).le)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.cast_ofNat]; ring
  rw [polygonalQueuePath_balance N hT x0 U A
    ⟨q n + 1, by omega⟩ ht i]
  let rd : Real :=
    ((roundedState x0 (q n + 1)
      (Classical.choice (inferInstance : Nonempty Buffer)) i : Nat) :
        Real) / (q n + 1 : Nat) - x0 i
  let id : Real :=
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun l : Buffer =>
        polygonalAllocationPath N T x0 U A
          ⟨q n + 1, by omega⟩ t l j i) -
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun l : Buffer => E t l j i)
  let od : Real :=
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        polygonalAllocationPath N T x0 U A
          ⟨q n + 1, by omega⟩ t i j k) -
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer => E t i j k)
  have htri :
      abs (rd + id - od) <= abs rd + abs id + abs od := by
    calc
      abs (rd + id - od) <= abs (rd + id) + abs od :=
        abs_sub _ _
      _ <= (abs rd + abs id) + abs od :=
        by simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (abs_add_le rd id) (abs od)
      _ = _ := by ring
  dsimp only [rd, id, od] at htri
  calc
    abs
        (((((roundedState x0 (q n + 1)
          (Classical.choice (inferInstance : Nonempty Buffer)) i : Nat) :
            Real) / (q n + 1 : Nat) +
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun l : Buffer =>
              polygonalAllocationPath N T x0 U A
                ⟨q n + 1, by omega⟩ t l j i) -
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer =>
              polygonalAllocationPath N T x0 U A
                ⟨q n + 1, by omega⟩ t i j k)) -
          (x0 i +
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun l : Buffer => E t l j i) -
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer => E t i j k)))) =
        abs
          (((((roundedState x0 (q n + 1)
            (Classical.choice (inferInstance : Nonempty Buffer)) i : Nat) :
              Real) / (q n + 1 : Nat) - x0 i) +
            ((Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun l : Buffer =>
                  polygonalAllocationPath N T x0 U A
                    ⟨q n + 1, by omega⟩ t l j i) -
              (Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun l : Buffer => E t l j i)) -
            ((Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun k : Buffer =>
                  polygonalAllocationPath N T x0 U A
                    ⟨q n + 1, by omega⟩ t i j k) -
              (Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun k : Buffer => E t i j k)))) := by ring
    _ <= _ := htri
    _ < delta +
          ((Fintype.card Server : Nat) : Real) *
            (Fintype.card Buffer : Nat) * delta +
          ((Fintype.card Server : Nat) : Real) *
            (Fintype.card Buffer : Nat) * delta := by linarith
    _ = epsilon := by
      dsimp [delta, D]
      field_simp
      ring

private theorem eventually_gridPreActionStates_near
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (polygonalAllocationPath N T x0 U A
              ⟨q n + 1, by omega⟩ t i j k)
            (E t i j k) < epsilon)
    (X : FluidStatePath Buffer)
    (hXeq : X = fun t i =>
      x0 i +
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun l : Buffer => E t l j i) -
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer => E t i j k))
    (t : Real) (ht : t ∈ Ioo (0 : Real) T)
    (hXcontinuous : ContinuousAt X t)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun h =>
        Filter.Eventually
          (fun n =>
            forall j k (l : Fin (q n + 1))
              (y : JobState Buffer (q n + 1)),
              y ∈ gridPreActionStates N T x0 U A
                ⟨q n + 1, by omega⟩ j k l ->
              0 <
                edgeProgress
                    (((q n + 1 : Nat) : Real) * (t + h) / T) l.val -
                  edgeProgress
                    (((q n + 1 : Nat) : Real) * t / T) l.val ->
              IsNearNormalizedState y (X t) epsilon)
          atTop)
      (nhdsWithin 0 (Ioi 0)) := by
  obtain ⟨eta, heta, hXclose⟩ :=
    Metric.continuousAt_iff.mp hXcontinuous
      (epsilon / 3) (by positivity)
  obtain ⟨nQ, hnQ⟩ :=
    polygonalQueuePath_uniform_convergence_of_allocationLimit
      N T hT x0 U A q hq E hconv (epsilon / 3) (by positivity)
  obtain ⟨Kbatch, hKbatch⟩ :=
    gridTokenBatch_scaled_length_uniform_zero T hT A hA
      (epsilon / 6) (by positivity)
  obtain ⟨Kmesh, hKmesh⟩ :=
    exists_nat_gt (3 * T / eta)
  let n0 := max nQ (max Kbatch Kmesh)
  have hwindow : 0 < min (eta / 3) (T - t) := by
    exact lt_min (div_pos heta (by norm_num)) (sub_pos.mpr ht.2)
  have hsmallEventually :
      Filter.Eventually
        (fun h : Real => h < min (eta / 3) (T - t))
        (nhdsWithin 0 (Ioi 0)) :=
    mem_nhdsWithin_of_mem_nhds
      (t := Ioi (0 : Real))
      (Iio_mem_nhds hwindow)
  filter_upwards [self_mem_nhdsWithin, hsmallEventually]
    with h hh hsmall
  have hhpos : 0 < h := hh
  have hhEta : h < eta / 3 :=
    hsmall.trans_le (min_le_left _ _)
  refine Filter.eventually_atTop.mpr ⟨n0, fun n hn j k l y hy hused => ?_⟩
  let K : PNat := ⟨q n + 1, by omega⟩
  have hnQ' : nQ <= n := (le_max_left _ _).trans hn
  have hnBatch : Kbatch <= (K : Nat) := by
    dsimp [K, n0] at hn ⊢
    have hn' : Kbatch <= n :=
      (le_max_left Kbatch Kmesh).trans
        ((le_max_right nQ (max Kbatch Kmesh)).trans hn)
    exact hn'.trans ((hq.id_le n).trans (Nat.le_succ _))
  have hnMesh : Kmesh <= (K : Nat) := by
    dsimp [K, n0] at hn ⊢
    have hn' : Kmesh <= n :=
      (le_max_right Kbatch Kmesh).trans
        ((le_max_right nQ (max Kbatch Kmesh)).trans hn)
    exact hn'.trans ((hq.id_le n).trans (Nat.le_succ _))
  have hmesh : T / (K : Nat) < eta / 3 := by
    have hKmeshReal : (Kmesh : Real) <= (K : Nat) := by
      exact_mod_cast hnMesh
    have hraw : 3 * T / eta < (K : Real) :=
      hKmesh.trans_le hKmeshReal
    have hKpos : (0 : Real) < (K : Nat) := by positivity
    apply (div_lt_iff₀ hKpos).2
    apply (div_lt_iff₀ heta).1 at hraw
    nlinarith
  have hlclose :
      abs (gridTime T K l.val - t) < eta := by
    exact (used_edge_gridTime_close T hT K hhpos l hused).trans
      (by linarith)
  have hgridmem : gridTime T K l.val ∈ Icc (0 : Real) T :=
    gridTime_mem_Icc hT K l.val
  have hqueue (i : Buffer) :
      abs
        (polygonalQueuePath N T x0 U A K
            (gridTime T K l.val) i -
          X (gridTime T K l.val) i) < epsilon / 3 := by
    rw [hXeq]
    exact hnQ n hnQ' i (gridTime T K l.val) hgridmem
  have hXvector :
      dist (X (gridTime T K l.val)) (X t) < epsilon / 3 := by
    apply hXclose
    simpa only [Real.dist_eq] using hlclose
  have hXcoord (i : Buffer) :
      abs (X (gridTime T K l.val) i - X t i) < epsilon / 3 := by
    have hle :
        dist (X (gridTime T K l.val) i) (X t i) <=
          dist (X (gridTime T K l.val)) (X t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (X (gridTime T K l.val)) (X t) <= _) i
    rw [Real.dist_eq] at hle
    exact hle.trans_lt hXvector
  have hbatch :
      ((gridTokenBatch T A K l.val).length : Real) / (K : Nat) <
        epsilon / 6 :=
    hKbatch K hnBatch l.val l.isLt
  intro i
  have hyraw :=
    empiricalPreActionStates_mem_dist_le N (U K)
      (gridQueueState N T x0 U A K l.val)
      (gridTokenBatch T A K l.val) j k hy i
  have hygrid :
      abs
        ((y i : Real) / (K : Nat) -
          (gridQueueState N T x0 U A K l.val i : Real) / (K : Nat)) <
        epsilon / 3 := by
    have hKpos : (0 : Real) < (K : Nat) := by positivity
    rw [<- sub_div, abs_div, abs_of_pos hKpos]
    exact (div_le_div_of_nonneg_right hyraw hKpos.le).trans_lt (by
      calc
        (2 * (gridTokenBatch T A K l.val).length : Real) / (K : Nat) =
            2 * (((gridTokenBatch T A K l.val).length : Real) /
              (K : Nat)) := by ring
        _ < 2 * (epsilon / 6) := by gcongr
        _ = epsilon / 3 := by ring)
  have hgridEq :
      polygonalQueuePath N T x0 U A K (gridTime T K l.val) i =
        (gridQueueState N T x0 U A K l.val i : Real) / (K : Nat) := by
    unfold polygonalQueuePath
    rw [gridTime_eq_gridPoint T K l.val (Nat.le_of_lt l.isLt)]
    exact polygonalInterpolate_grid K _ T hT l.val
      (Nat.le_of_lt l.isLt)
  rw [<- hgridEq] at hygrid
  calc
    abs ((y i : Real) / ((q n + 1 : Nat) : Real) - X t i) <=
        abs ((y i : Real) / (K : Nat) -
          polygonalQueuePath N T x0 U A K
            (gridTime T K l.val) i) +
        abs (polygonalQueuePath N T x0 U A K
            (gridTime T K l.val) i -
          X (gridTime T K l.val) i) +
        abs (X (gridTime T K l.val) i - X t i) := by
      dsimp [K]
      have h1 := abs_sub_le
        ((y i : Real) / ((q n + 1 : Nat) : Real))
        (polygonalQueuePath N T x0 U A
          ⟨q n + 1, by omega⟩ (gridTime T
            ⟨q n + 1, by omega⟩ l.val) i)
        (X t i)
      have h2 := abs_sub_le
        (polygonalQueuePath N T x0 U A
          ⟨q n + 1, by omega⟩ (gridTime T
            ⟨q n + 1, by omega⟩ l.val) i)
        (X (gridTime T ⟨q n + 1, by omega⟩ l.val) i)
        (X t i)
      linarith
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 := by
      linarith [hygrid, hqueue i, hXcoord i]
    _ = epsilon := by ring

private noncomputable def completedAllocationActionPath
    (A : MatrixPath Server Buffer)
    (E : FluidAllocationPath Buffer Server)
    (j : Server) (k : Buffer) (t : Real) :
    ActionVector Buffer
  | some i => E t i j k
  | none => A t j k - Finset.univ.sum fun i : Buffer => E t i j k

private theorem polygonalActionPath_tendsto_of_allocationLimit
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (polygonalAllocationPath N T x0 U A
              ⟨q n + 1, by omega⟩ t i j k)
            (E t i j k) < epsilon)
    (j : Server) (k : Buffer) (t : Real)
    (ht : t ∈ Icc (0 : Real) T) (a : Option Buffer) :
    Tendsto
      (fun n =>
        polygonalActionPath N T x0 U A
          ⟨q n + 1, by omega⟩ j k t a)
      atTop
      (nhds (completedAllocationActionPath A E j k t a)) := by
  have hE (i : Buffer) :
      Tendsto
        (fun n =>
          polygonalAllocationPath N T x0 U A
            ⟨q n + 1, by omega⟩ t i j k)
        atTop (nhds (E t i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := hconv epsilon hepsilon
    exact ⟨n0, fun n hn => hn0 n hn i j k t ht⟩
  cases a with
  | some i =>
      refine (hE i).congr' ?_
      exact Eventually.of_forall fun n => by
        simpa only using
          (polygonalActionPath_some N T hT x0 U A
            ⟨q n + 1, by omega⟩ i j k t ht).symm
  | none =>
      have hinput :
          Tendsto
            (fun n =>
              polygonalInputPath T A ⟨q n + 1, by omega⟩ t j k)
            atTop (nhds (A t j k)) := by
        rw [Metric.tendsto_atTop]
        intro epsilon hepsilon
        obtain ⟨n0, hn0⟩ :=
          polygonalInputPath_uniform_convergence
            T hT A hA epsilon hepsilon
        exact ⟨n0, fun n hn =>
          hn0 (q n) (hn.trans (hq.id_le n)) j k t ht⟩
      have hsum :
          Tendsto
            (fun n =>
              Finset.univ.sum fun i : Buffer =>
                polygonalAllocationPath N T x0 U A
                  ⟨q n + 1, by omega⟩ t i j k)
            atTop
            (nhds (Finset.univ.sum fun i : Buffer => E t i j k)) := by
        apply tendsto_finsetSum
        intro i hi
        exact hE i
      refine (hinput.sub hsum).congr' ?_
      exact Eventually.of_forall fun n => by
        simpa only using
          (polygonalActionPath_none N T hT x0 U A hA
            ⟨q n + 1, by omega⟩ j k t ht).symm

private theorem completedAllocation_derivativeRatio_mem
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (polygonalAllocationPath N T x0 U A
              ⟨q n + 1, by omega⟩ t i j k)
            (E t i j k) < epsilon)
    (X : FluidStatePath Buffer)
    (hXeq : X = fun t i =>
      x0 i +
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun l : Buffer => E t l j i) -
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer => E t i j k))
    (t : Real) (ht : t ∈ Ioo (0 : Real) T)
    (hXcontinuous : ContinuousAt X t)
    (j : Server) (k : Buffer) (Adot : Real)
    (Edot : ActionVector Buffer)
    (hAderiv : HasDerivAt (fun s => A s j k) Adot t)
    (hEderiv : forall a,
      HasDerivAt
        (fun s => completedAllocationActionPath A E j k s a)
        (Edot a) t)
    (hAdot : 0 < Adot) :
    (fun a => Edot a / Adot) ∈
      N.fluidPolicyCorrespondence U j k (X t) := by
  apply derivativeRatio_mem_fluidPolicyCorrespondence
    N U j k (X t) (fun s => A s j k)
      (completedAllocationActionPath A E j k)
      t Adot Edot hAderiv hEderiv hAdot
  intro epsilon
  have hnear :=
    eventually_gridPreActionStates_near
      N T hT x0 U A hA q hq E hconv X hXeq
        t ht hXcontinuous epsilon.1 epsilon.2
  have hslope :
      Tendsto
        (fun h => h⁻¹ * (A (t + h) j k - A t j k))
        (nhdsWithin 0 (Ioi 0)) (nhds Adot) :=
    hAderiv.tendsto_slope_zero_right
  have hslopePos :
      Filter.Eventually
        (fun h => 0 < h⁻¹ * (A (t + h) j k - A t j k))
        (nhdsWithin 0 (Ioi 0)) :=
    hslope.eventually_const_lt hAdot
  have hsmall :
      Filter.Eventually (fun h : Real => h < T - t)
        (nhdsWithin 0 (Ioi 0)) :=
    mem_nhdsWithin_of_mem_nhds
      (t := Ioi (0 : Real))
      (Iio_mem_nhds (sub_pos.mpr ht.2))
  filter_upwards [hnear, hslopePos, self_mem_nhdsWithin, hsmall]
    with h hnearN hslopeH hh hhT
  have hinc : 0 < A (t + h) j k - A t j k :=
    pos_of_mul_pos_right hslopeH (inv_nonneg.mpr hh.le)
  have hhpos : 0 < h := hh
  have htpos : 0 < t := ht.1
  have htT : t < T := ht.2
  have htIcc : t ∈ Icc (0 : Real) T := ⟨ht.1.le, ht.2.le⟩
  have hthIcc : t + h ∈ Icc (0 : Real) T :=
    ⟨by linarith, by linarith⟩
  have hinputAt (s : Real) (hs : s ∈ Icc (0 : Real) T) :
      Tendsto
        (fun n =>
          polygonalInputPath T A ⟨q n + 1, by omega⟩ s j k)
        atTop (nhds (A s j k)) := by
    rw [Metric.tendsto_atTop]
    intro delta hdelta
    obtain ⟨n0, hn0⟩ :=
      polygonalInputPath_uniform_convergence T hT A hA delta hdelta
    exact ⟨n0, fun n hn =>
      hn0 (q n) (hn.trans (hq.id_le n)) j k s hs⟩
  have hAs := hinputAt t htIcc
  have hAt := hinputAt (t + h) hthIcc
  have hEs (a : Option Buffer) :=
    polygonalActionPath_tendsto_of_allocationLimit
      N T hT x0 U A hA q hq E hconv j k t htIcc a
  have hEt (a : Option Buffer) :=
    polygonalActionPath_tendsto_of_allocationLimit
      N T hT x0 U A hA q hq E hconv j k (t + h) hthIcc a
  have hposN :
      Filter.Eventually
        (fun n =>
          0 <
            polygonalInputPath T A
                ⟨q n + 1, by omega⟩ (t + h) j k -
              polygonalInputPath T A
                ⟨q n + 1, by omega⟩ t j k)
        atTop :=
    (hAt.sub hAs).eventually_const_lt hinc
  have hqnat :
      Tendsto (fun n => q n + 1) atTop atTop := by
    exact Filter.tendsto_atTop_mono
      (fun n => Nat.le_succ (q n)) hq.tendsto_atTop
  have hqreal :
      Tendsto (fun n => (((q n + 1 : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hqnat
  have hlarge :
      Filter.Eventually
        (fun n => epsilon.1⁻¹ <= (((q n + 1 : Nat) : Real)))
        atTop :=
    hqreal (Filter.eventually_ge_atTop epsilon.1⁻¹)
  have hmem :
      Filter.Eventually
        (fun n =>
          finiteDifferenceRatio
              (fun s =>
                polygonalInputPath T A
                  ⟨q n + 1, by omega⟩ s j k)
              (polygonalActionPath N T x0 U A
                ⟨q n + 1, by omega⟩ j k)
              t h ∈
            N.fluidPolicyEpsilonCorrespondence
              U j k (X t) epsilon.1)
        atTop := by
    filter_upwards [hnearN, hposN, hlarge]
      with n hnNear hnPos hnLarge
    apply finiteDifferenceRatio_polygonalAction_mem_epsilon
      N T hT x0 U A hA ⟨q n + 1, by omega⟩
        j k (X t) epsilon.1 t h htIcc hthIcc hh hnPos hnLarge
    intro l y hy hused
    exact hnNear j k l y hy hused
  have hmem' :
      Filter.Eventually
        (fun n =>
          (fun a =>
            (polygonalActionPath N T x0 U A
                  ⟨q n + 1, by omega⟩ j k (t + h) a -
                polygonalActionPath N T x0 U A
                  ⟨q n + 1, by omega⟩ j k t a) /
              (polygonalInputPath T A
                  ⟨q n + 1, by omega⟩ (t + h) j k -
                polygonalInputPath T A
                  ⟨q n + 1, by omega⟩ t j k)) ∈
            N.fluidPolicyEpsilonCorrespondence
              U j k (X t) epsilon.1)
        atTop := by
    filter_upwards [hmem] with n hn
    exact hn
  apply closed_mem_of_finiteDifferenceRatio_limit
    (N.fluidPolicyEpsilonCorrespondence_isClosed
      U j k (X t) epsilon.1)
    (fun n s =>
      polygonalInputPath T A ⟨q n + 1, by omega⟩ s j k)
    (fun s => A s j k)
    (fun n s =>
      polygonalActionPath N T x0 U A
        ⟨q n + 1, by omega⟩ j k s)
    (completedAllocationActionPath A E j k)
    t (t + h) hAs hAt hEs hEt (ne_of_gt hinc)
  exact hmem'

private theorem absolutelyContinuousOnInterval_finset_sum
    {I : Type*} (s : Finset I) (f : I -> Real -> Real)
    {a b : Real}
    (hf : forall i, i ∈ s -> AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => s.sum fun i => f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (LipschitzWith.const (0 : Real)).lipschitzOnWith
          |>.absolutelyContinuousOnInterval
  | @insert i s hi ih =>
      have hai := hf i (Finset.mem_insert_self i s)
      have has : forall j, j ∈ s ->
          AbsolutelyContinuousOnInterval (f j) a b := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hfun :
          (fun t => Finset.sum (insert i s) fun j => f j t) =
            fun t => f i t + Finset.sum s fun j => f j t := by
        funext t
        rw [Finset.sum_insert hi]
      rw [hfun]
      have hsum := hai.add (ih has)
      unfold AbsolutelyContinuousOnInterval at hsum ⊢
      simpa only [Real.dist_eq, Pi.add_apply] using hsum

private theorem allocationBalanceState_properties
    (N : Network Buffer Server)
    (T : Real) (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (polygonalAllocationPath N T x0 U A
              ⟨q n + 1, by omega⟩ t i j k)
            (E t i j k) < epsilon)
    (hac : forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T)
    (hzero : forall i j k, E 0 i j k = 0)
    (hincompat :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i j k, ¬N.compatible i j -> E t i j k = 0) :
    let X : FluidStatePath Buffer := fun t i =>
      x0 i +
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun l : Buffer => E t l j i) -
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer => E t i j k)
    (forall i, AbsolutelyContinuousOnInterval (fun t => X t i) 0 T) /\
    (forall i, X 0 i = x0 i) /\
    (forall t, t ∈ Icc (0 : Real) T -> IsFluidState (X t)) /\
    (forall t, t ∈ Icc (0 : Real) T -> forall i,
      X t i = x0 i
        + (Finset.univ.sum fun j : Server =>
            Finset.sum (N.buffersOf j) fun l => E t l j i)
        - (Finset.sum (N.serversOf i) fun j =>
            Finset.univ.sum fun k : Buffer => E t i j k)) := by
  dsimp only
  have hstateAc : forall i,
      AbsolutelyContinuousOnInterval
        (fun t =>
          x0 i +
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun l : Buffer => E t l j i) -
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer => E t i j k))
        0 T := by
    intro i
    have hconst :
        AbsolutelyContinuousOnInterval (fun _ : Real => x0 i) 0 T :=
      (LipschitzWith.const (x0 i)).lipschitzOnWith
        |>.absolutelyContinuousOnInterval
    have hin :
        AbsolutelyContinuousOnInterval
          (fun t =>
            Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun l : Buffer => E t l j i)
          0 T := by
      apply absolutelyContinuousOnInterval_finset_sum
      intro j hj
      apply absolutelyContinuousOnInterval_finset_sum
      intro l hl
      exact hac l j i
    have hout :
        AbsolutelyContinuousOnInterval
          (fun t =>
            Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer => E t i j k)
          0 T := by
      apply absolutelyContinuousOnInterval_finset_sum
      intro j hj
      apply absolutelyContinuousOnInterval_finset_sum
      intro k hk
      exact hac i j k
    have hsum := (hconst.add hin).sub hout
    unfold AbsolutelyContinuousOnInterval at hsum ⊢
    simpa only [Real.dist_eq, Pi.add_apply, Pi.sub_apply] using hsum
  have hinitial : forall i,
      x0 i +
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun l : Buffer => E 0 l j i) -
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer => E 0 i j k) =
        x0 i := by
    intro i
    simp [hzero]
  have hsimplex :
      forall t, t ∈ Icc (0 : Real) T ->
        IsFluidState
          (fun i =>
            x0 i +
              (Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun l : Buffer => E t l j i) -
              (Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun k : Buffer => E t i j k)) := by
    intro t ht
    let X : Buffer -> Real := fun i =>
      x0 i +
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun l : Buffer => E t l j i) -
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer => E t i j k)
    have hqueue (i : Buffer) :
        Tendsto
          (fun n =>
            polygonalQueuePath N T x0 U A
              ⟨q n + 1, by omega⟩ t i)
          atTop (nhds (X i)) := by
      exact polygonalQueuePath_tendsto_of_allocationLimit
        N T hT x0 U A q hq E hconv t ht i
    constructor
    · intro i
      exact isClosed_Ici.mem_of_tendsto (hqueue i)
        (Eventually.of_forall fun n =>
          (polygonalQueuePath_isFluidState N hT x0 U A
            ⟨q n + 1, by omega⟩ ht).1 i)
    · have hsum :
          Tendsto
            (fun n =>
              Finset.univ.sum fun i : Buffer =>
                polygonalQueuePath N T x0 U A
                  ⟨q n + 1, by omega⟩ t i)
            atTop (nhds (Finset.univ.sum X)) := by
        apply tendsto_finsetSum
        intro i hi
        exact hqueue i
      have hone :
          (fun n =>
            Finset.univ.sum fun i : Buffer =>
              polygonalQueuePath N T x0 U A
                ⟨q n + 1, by omega⟩ t i) = fun _ => 1 := by
        funext n
        exact (polygonalQueuePath_isFluidState N hT x0 U A
          ⟨q n + 1, by omega⟩ ht).2
      rw [hone] at hsum
      exact tendsto_nhds_unique hsum tendsto_const_nhds
  refine ⟨hstateAc, hinitial, hsimplex, ?_⟩
  intro t ht i
  have hin (j : Server) :
      Finset.univ.sum (fun l : Buffer => E t l j i) =
        Finset.sum (N.buffersOf j) (fun l => E t l j i) := by
    simp only [buffersOf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlj : N.compatible l j
    · simp [hlj]
    · simp [hlj, hincompat t ht l j i hlj]
  have hout :
      Finset.univ.sum
          (fun j : Server => Finset.univ.sum fun k : Buffer => E t i j k) =
        Finset.sum (N.serversOf i)
          (fun j => Finset.univ.sum fun k : Buffer => E t i j k) := by
    simp only [serversOf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : N.compatible i j
    · simp [hij]
    · simp [hij, hincompat t ht i j]
  simp_rw [hin]
  rw [hout]

/-- Every admissible prescribed input has a fluid-model solution. -/
theorem fluidModelSolution_exists
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (x0 : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (A : MatrixPath Server Buffer) (hA : IsFluidInput T A) :
    Nonempty (N.FluidModelSolution U T x0 A) := by
  classical
  obtain ⟨q, hq, E, hEcontinuous, hconv⟩ :=
    exists_polygonalAllocation_limit N T hT x0 U A hA
  obtain ⟨hEac, hEzero, hEincompatible, hEdom⟩ :=
    allocationLimit_properties N T hT x0 U A hA q hq E hconv
  let X : FluidStatePath Buffer := fun t i =>
    x0 i +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun l : Buffer => E t l j i) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer => E t i j k)
  have hXeq : X = fun t i =>
      x0 i +
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun l : Buffer => E t l j i) -
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer => E t i j k) := rfl
  obtain ⟨hXac, hXzero, hXsimplex, hbalance⟩ :=
    allocationBalanceState_properties
      N T hT x0 U A q hq E hconv hEac hEzero hEincompatible
  let Xm : FluidStatePath Buffer :=
    (Icc (0 : Real) T).piecewise X (fun _ i => x0 i)
  have hXmEq (t : Real) (ht : t ∈ Icc (0 : Real) T) :
      Xm t = X t := by
    simp [Xm, ht]
  have hXmMeasurable (i : Buffer) :
      Measurable (fun t => Xm t i) := by
    have hm :
        Measurable
          ((Icc (0 : Real) T).piecewise
            (fun t => X t i) (fun _ => x0 i)) := by
      apply ContinuousOn.measurable_piecewise
      · have hc := (hXac i).continuousOn
        simpa [uIcc_of_le hT.le] using hc
      · exact continuousOn_const
      · exact measurableSet_Icc
    have heq :
        (fun t => Xm t i) =
          (Icc (0 : Real) T).piecewise
            (fun t => X t i) (fun _ => x0 i) := by
      funext t
      by_cases ht : t ∈ Icc (0 : Real) T <;> simp [Xm, ht]
    rw [heq]
    exact hm
  have hcompletedAc (j : Server) (k : Buffer) (a : Option Buffer) :
      AbsolutelyContinuousOnInterval
        (fun t => completedAllocationActionPath A E j k t a) 0 T := by
    cases a with
    | some i =>
        exact hEac i j k
    | none =>
        have hsum :
            AbsolutelyContinuousOnInterval
              (fun t => Finset.univ.sum fun i : Buffer => E t i j k)
              0 T := by
          apply absolutelyContinuousOnInterval_finset_sum
          intro i hi
          exact hEac i j k
        have hsub := (hA.1 j k).sub hsum
        unfold AbsolutelyContinuousOnInterval at hsub ⊢
        simpa only [completedAllocationActionPath, Real.dist_eq,
          Pi.sub_apply] using hsub
  let p : FluidActionFractions Buffer Server :=
    fun t j k =>
      N.verifiedPatchedFluidPolicy U j k Xm
        (fun s => A s j k)
        (completedAllocationActionPath A E j k) t
  have hXcontinuousAt (t : Real) (ht : t ∈ Ioo (0 : Real) T) :
      ContinuousAt X t := by
    rw [continuousAt_pi]
    intro i
    have hc := (hXac i).continuousOn
    rw [uIcc_of_le hT.le] at hc
    exact hc.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hinterior :
      Filter.Eventually (fun t : Real => t ∈ Ioo (0 : Real) T)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    rw [<- Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc :
        Ioo (0 : Real) T =ᵐ[volume] Icc (0 : Real) T)]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hAdiff (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => DifferentiableAt Real (fun s => A s j k) t)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(hA.1 j k).ae_differentiableAt] with t htDiff
    intro htRange
    exact htDiff (by simpa [uIcc_of_le hT.le] using htRange)
  have hCompletedDiff (j : Server) (k : Buffer) (a : Option Buffer) :
      Filter.Eventually
        (fun t => DifferentiableAt Real
          (fun s => completedAllocationActionPath A E j k s a) t)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(hcompletedAc j k a).ae_differentiableAt]
      with t htDiff
    intro htRange
    exact htDiff (by simpa [uIcc_of_le hT.le] using htRange)
  have hregular :
      Filter.Eventually
        (fun t =>
          t ∈ Ioo (0 : Real) T /\
          (forall j k,
            DifferentiableAt Real (fun s => A s j k) t) /\
          (forall j k a,
            DifferentiableAt Real
              (fun s => completedAllocationActionPath A E j k s a) t))
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    have hAall :
        Filter.Eventually
          (fun t => forall j k,
            DifferentiableAt Real (fun s => A s j k) t)
          (ae (volume.restrict (Icc (0 : Real) T))) := by
      rw [MeasureTheory.ae_all_iff]
      intro j
      rw [MeasureTheory.ae_all_iff]
      exact hAdiff j
    have hEall :
        Filter.Eventually
          (fun t => forall j k a,
            DifferentiableAt Real
              (fun s => completedAllocationActionPath A E j k s a) t)
          (ae (volume.restrict (Icc (0 : Real) T))) := by
      rw [MeasureTheory.ae_all_iff]
      intro j
      rw [MeasureTheory.ae_all_iff]
      intro k
      rw [MeasureTheory.ae_all_iff]
      exact hCompletedDiff j k
    filter_upwards [hinterior, hAall, hEall] with t ht hAt hEt
    exact ⟨ht, hAt, hEt⟩
  refine ⟨{
    horizon_pos := hT
    input_valid := hA
    X := X
    E := E
    p := p
    state_ac := hXac
    allocation_ac := hEac
    state_initial := hXzero
    allocation_initial := hEzero
    allocation_incompatible := hEincompatible
    state_in_simplex := hXsimplex
    fractions_measurable := ?_
    fractions_in_simplex := ?_
    fractions_incompatible := ?_
    policy_rule := ?_
    allocation_rule := ?_
    balance := hbalance
  }⟩
  · intro j k a
    exact verifiedPatchedFluidPolicy_measurable
      N U j k Xm (fun s => A s j k)
        (completedAllocationActionPath A E j k)
      hXmMeasurable
      a
  · intro t ht j k
    have hm :=
      verifiedPatchedFluidPolicy_mem N U j k Xm
        (fun s => A s j k)
        (completedAllocationActionPath A E j k)
        t (by simpa [hXmEq t ht] using hXsimplex t ht)
    exact fluidPolicyCorrespondence_isActionDistribution
      N U j k (Xm t)
      (N.verifiedPatchedFluidPolicy U j k Xm
        (fun s => A s j k)
        (completedAllocationActionPath A E j k) t) hm
  · intro t ht j k i hij
    have hm :=
      verifiedPatchedFluidPolicy_mem N U j k Xm
        (fun s => A s j k)
        (completedAllocationActionPath A E j k)
        t (by simpa [hXmEq t ht] using hXsimplex t ht)
    exact fluidPolicyCorrespondence_incompatible
      N U j k i (Xm t)
      (N.verifiedPatchedFluidPolicy U j k Xm
        (fun s => A s j k)
        (completedAllocationActionPath A E j k) t) hm hij
  · filter_upwards [hregular] with t htRegular
    rcases htRegular with ⟨ht, hAt, hEt⟩
    intro j k
    have htIcc : t ∈ Icc (0 : Real) T := ⟨ht.1.le, ht.2.le⟩
    have hm := verifiedPatchedFluidPolicy_mem N U j k Xm
        (fun s => A s j k)
        (completedAllocationActionPath A E j k)
        t (by simpa [hXmEq t htIcc] using hXsimplex t htIcc)
    simpa [hXmEq t htIcc] using hm
  · filter_upwards [hregular] with t htRegular
    intro i j k hij
    rcases htRegular with ⟨ht, hAt, hEt⟩
    have hAhas :=
      (hAt j k).hasDerivAt
    have hEhas (a : Option Buffer) :=
      (hEt j k a).hasDerivAt
    have hAnonneg : 0 <= deriv (fun s => A s j k) t := by
      rw [<- derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      exact (hA.2.1 j k).derivWithin_nonneg
    by_cases hpos : 0 < deriv (fun s => A s j k) t
    · have hmem :=
        completedAllocation_derivativeRatio_mem
          N T hT x0 U A hA q hq E hconv X hXeq
          t ht (hXcontinuousAt t ht) j k
          (deriv (fun s => A s j k) t)
          (fun a => deriv
            (fun s => completedAllocationActionPath A E j k s a) t)
          hAhas hEhas hpos
      change deriv (fun s => E s i j k) t =
        deriv (fun s => A s j k) t *
          N.verifiedPatchedFluidPolicy U j k Xm
            (fun s => A s j k)
            (completedAllocationActionPath A E j k) t (some i)
      have htIcc : t ∈ Icc (0 : Real) T := ⟨ht.1.le, ht.2.le⟩
      have hmemXm :
          (fun a => deriv
              (fun s => completedAllocationActionPath A E j k s a) t /
            deriv (fun s => A s j k) t) ∈
            N.fluidPolicyCorrespondence U j k (Xm t) := by
        simpa [hXmEq t htIcc] using hmem
      simp only [verifiedPatchedFluidPolicy, if_pos hmemXm]
      field_simp
      simpa only [completedAllocationActionPath]
    · have hAzero : deriv (fun s => A s j k) t = 0 :=
        le_antisymm (not_lt.mp hpos) hAnonneg
      have hEzeroDeriv :
          deriv (fun s => E s i j k) t = 0 := by
        apply hasDerivAt_eq_zero_of_increment_domination_Icc
          (fun s => A s j k) (fun s => E s i j k)
          T t (deriv (fun s => E s i j k) t) ht
        · simpa [hAzero] using hAhas
        · exact (hEt j k (some i)).hasDerivAt
        · intro s hs u hu
          exact hEdom i j k s hs u hu
      change deriv (fun s => E s i j k) t =
        deriv (fun s => A s j k) t *
          N.verifiedPatchedFluidPolicy U j k Xm
            (fun s => A s j k)
            (completedAllocationActionPath A E j k) t (some i)
      rw [hEzeroDeriv, hAzero, zero_mul]

/-- A complete fluid-model solution exists for the identically zero input.
This is the base case of the prescribed-input construction. -/
theorem fluidModelSolution_zeroInput
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (x0 : Simplex Buffer) (U : N.DeterministicPolicySequence) :
    Nonempty
      (N.FluidModelSolution U T x0
        (fun _t _j _k => 0)) := by
  classical
  have hchoice :
      forall j k, exists a : N.ServiceAction,
        (forall i, a = some i -> N.compatible i j) /\
        N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x0 :=
    fun j k =>
      exists_actionDirac_mem_fluidPolicyCorrespondence N U j k x0
  choose action hcompatible hpolicy using hchoice
  let X : FluidStatePath Buffer := fun _t i => x0 i
  let E : FluidAllocationPath Buffer Server := fun _t _i _j _k => 0
  let p : FluidActionFractions Buffer Server :=
    fun _t j k => N.actionDirac (action j k)
  refine ⟨{
    horizon_pos := hT
    input_valid := ?_
    X := X
    E := E
    p := p
    state_ac := ?_
    allocation_ac := ?_
    state_initial := ?_
    allocation_initial := ?_
    allocation_incompatible := ?_
    state_in_simplex := ?_
    fractions_measurable := ?_
    fractions_in_simplex := ?_
    fractions_incompatible := ?_
    policy_rule := ?_
    allocation_rule := ?_
    balance := ?_
  }⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro j k
      exact
        (LipschitzWith.const (0 : Real)).lipschitzOnWith
          |>.absolutelyContinuousOnInterval
    · intro j k
      exact monotoneOn_const
    · intro j k
      rfl
  · intro i
    exact
      (LipschitzWith.const (x0 i)).lipschitzOnWith
        |>.absolutelyContinuousOnInterval
  · intro i j k
    exact
      (LipschitzWith.const (0 : Real)).lipschitzOnWith
        |>.absolutelyContinuousOnInterval
  · intro i
    rfl
  · intro i j k
    rfl
  · intro t ht i j k hij
    rfl
  · intro t ht
    exact ⟨x0.nonneg, x0.sum_eq_one⟩
  · intro j k a
    exact measurable_const
  · intro t ht j k
    exact N.actionDirac_isDistribution (action j k)
  · intro t ht j k i hij
    have hne : Not (some i = action j k) := by
      intro heq
      exact hij (hcompatible j k i heq.symm)
    simp [p, actionDirac, hne]
  · exact Filter.Eventually.of_forall fun t j k => hpolicy j k
  · filter_upwards [] with t
    intro i j k hij
    simp [E]
  · intro t ht i
    simp [X, E]

/-- The prescribed-input existence statement holds for a policy sequence
that always wastes its service opportunities.  Unlike
`fluidModelSolution_zeroInput`, this permits every admissible input path. -/
theorem fluidModelSolution_of_alwaysNone
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A)
    (hU : forall K z j k, U K z j k = none) :
    Nonempty (N.FluidModelSolution U T x0 A) := by
  classical
  have hnone :
      forall j k,
        N.actionDirac none ∈ N.fluidPolicyCorrespondence U j k x0 := by
    intro j k
    unfold fluidPolicyCorrespondence
    rw [Set.mem_iInter]
    intro epsilon
    obtain ⟨K, z, hK, hz⟩ :=
      exists_near_normalized_state x0 epsilon.1 epsilon.2
    apply subset_closure
    apply subset_convexHull Real
    exact ⟨K, z, by simpa [zpow_neg_one] using hK, hz, by rw [hU]⟩
  let X : FluidStatePath Buffer := fun _t i => x0 i
  let E : FluidAllocationPath Buffer Server := fun _t _i _j _k => 0
  let p : FluidActionFractions Buffer Server :=
    fun _t _j _k => N.actionDirac none
  refine ⟨{
    horizon_pos := hT
    input_valid := hA
    X := X
    E := E
    p := p
    state_ac := ?_
    allocation_ac := ?_
    state_initial := ?_
    allocation_initial := ?_
    allocation_incompatible := ?_
    state_in_simplex := ?_
    fractions_measurable := ?_
    fractions_in_simplex := ?_
    fractions_incompatible := ?_
    policy_rule := ?_
    allocation_rule := ?_
    balance := ?_
  }⟩
  · intro i
    exact
      (LipschitzWith.const (x0 i)).lipschitzOnWith
        |>.absolutelyContinuousOnInterval
  · intro i j k
    exact
      (LipschitzWith.const (0 : Real)).lipschitzOnWith
        |>.absolutelyContinuousOnInterval
  · intro i
    rfl
  · intro i j k
    rfl
  · intro t ht i j k hij
    rfl
  · intro t ht
    exact ⟨x0.nonneg, x0.sum_eq_one⟩
  · intro j k a
    exact measurable_const
  · intro t ht j k
    exact N.actionDirac_isDistribution none
  · intro t ht j k i hij
    simp [p, actionDirac]
  · exact Filter.Eventually.of_forall fun t j k => hnone j k
  · filter_upwards [] with t
    intro i j k hij
    simp [E, p, actionDirac]
  · intro t ht i
    simp [X, E]

/-- The readback in `FluidConsistency` is definitionally the deterministic
existence specification in `FluidModel`. -/
theorem deterministicFluidModelExistenceReadback_iff
    (N : Network Buffer Server) :
    N.DeterministicFluidModelExistenceReadback <->
      N.FluidModelExistenceStatement :=
  Iff.rfl

/-- Unconditional deterministic fluid-model existence for every finite
state-dependent network. -/
theorem deterministicFluidModelExistence :
    forall N : Network Buffer Server,
      N.DeterministicFluidModelExistenceReadback := by
  intro N T hT x0 U A hA
  exact fluidModelSolution_exists N T hT x0 U A hA

end Network

end StateDepMOR
open ProbabilityTheory

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

namespace Network

/-! ### Generic interpolation aliases used by the calendar construction -/

private theorem calendar_polygonal_nonnegative
    (K : PNat) (values : Nat -> Real) (t T : Real)
    (hvalues : forall l, l < (K : Nat) + 1 -> 0 <= values l) :
    0 <= polygonalInterpolate K values t T := by
  unfold polygonalInterpolate
  apply Finset.sum_nonneg
  intro l hl
  exact mul_nonneg (hatWeight_nonnegative _ _)
    (hvalues l (Finset.mem_range.mp hl))

private theorem calendar_polygonal_const
    (K : PNat) (c t T : Real) (hT : 0 < T)
    (ht : t ∈ Icc (0 : Real) T) :
    polygonalInterpolate K (fun _ => c) t T = c := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) ht.1) hT.le
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  unfold polygonalInterpolate
  rw [<- Finset.sum_mul, sum_hatWeight_eq_one K hr0 hrK, one_mul]

private theorem calendar_polygonal_add
    (K : PNat) (a b : Nat -> Real) (t T : Real) :
    polygonalInterpolate K (fun l => a l + b l) t T =
      polygonalInterpolate K a t T +
        polygonalInterpolate K b t T := by
  simp only [polygonalInterpolate, mul_add, Finset.sum_add_distrib]

private theorem calendar_polygonal_sub
    (K : PNat) (a b : Nat -> Real) (t T : Real) :
    polygonalInterpolate K (fun l => a l - b l) t T =
      polygonalInterpolate K a t T -
        polygonalInterpolate K b t T := by
  simp only [polygonalInterpolate, mul_sub, Finset.sum_sub_distrib]

private theorem calendar_polygonal_sum
    {I : Type*} [Fintype I]
    (K : PNat) (a : Nat -> I -> Real) (t T : Real) :
    polygonalInterpolate K (fun l => Finset.univ.sum (a l)) t T =
      Finset.univ.sum (fun i =>
        polygonalInterpolate K (fun l => a l i) t T) := by
  classical
  unfold polygonalInterpolate
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem fi_polygonal_state_simplex
    (K : PNat) (x : Nat -> Buffer -> Real) {t T : Real}
    (hT : 0 < T) (ht : t ∈ Icc (0 : Real) T)
    (hx : forall l, l < (K : Nat) + 1 -> IsFluidState (x l)) :
    IsFluidState
      (fun i => polygonalInterpolate K (fun l => x l i) t T) := by
  constructor
  · intro i
    apply calendar_polygonal_nonnegative
    intro l hl
    exact (hx l hl).1 i
  · rw [<- calendar_polygonal_sum K x t T]
    rw [show
      polygonalInterpolate K (fun l => Finset.univ.sum (x l)) t T =
        polygonalInterpolate K (fun _ => (1 : Real)) t T by
          unfold polygonalInterpolate
          apply Finset.sum_congr rfl
          intro l hl
          dsimp only
          rw [(hx l (Finset.mem_range.mp hl)).2]]
    exact calendar_polygonal_const K 1 t T hT ht

private theorem calendar_polygonal_zero
    (K : PNat) (values : Nat -> Real) (t T : Real)
    (hzero : forall l, l < (K : Nat) + 1 -> values l = 0) :
    polygonalInterpolate K values t T = 0 := by
  unfold polygonalInterpolate
  apply Finset.sum_eq_zero
  intro l hl
  rw [hzero l (Finset.mem_range.mp hl), mul_zero]

private theorem fi_polygonal_allocation_incompatible
    (K : PNat) (e : Nat -> Buffer -> Server -> Buffer -> Real)
    (t T : Real) (i : Buffer) (j : Server) (k : Buffer)
    (hzero : forall l, l < (K : Nat) + 1 -> e l i j k = 0) :
    polygonalInterpolate K (fun l => e l i j k) t T = 0 :=
  calendar_polygonal_zero K _ t T hzero

private theorem fi_polygonal_initial
    (K : PNat) (values : Nat -> Real) (T : Real) (hT : 0 < T) :
    polygonalInterpolate K values 0 T = values 0 := by
  convert polygonalInterpolate_grid K values T hT 0 (Nat.zero_le _) using 1
  simp

private noncomputable def fi_polygonalStatePath
    (K : PNat) (x : Nat -> Buffer -> Real) (T : Real) :
    FluidStatePath Buffer :=
  fun t i => polygonalInterpolate K (fun l => x l i) t T

private noncomputable def fi_polygonalAllocationPath
    (K : PNat) (e : Nat -> Buffer -> Server -> Buffer -> Real) (T : Real) :
    FluidAllocationPath Buffer Server :=
  fun t i j k => polygonalInterpolate K (fun l => e l i j k) t T

private theorem calendar_polygonal_balance
    {J Q : Type*} [Fintype J] [Fintype Q]
    (K : PNat) (x : Nat -> Real) (x0 : Real)
    (incoming : Nat -> J -> Real) (outgoing : Nat -> Q -> Real)
    {t T : Real} (hT : 0 < T) (ht : t ∈ Icc (0 : Real) T)
    (hbalance : forall l, l < (K : Nat) + 1 ->
      x l = x0 + Finset.univ.sum (incoming l) -
        Finset.univ.sum (outgoing l)) :
    polygonalInterpolate K x t T =
      x0 +
        Finset.univ.sum (fun j =>
          polygonalInterpolate K (fun l => incoming l j) t T) -
        Finset.univ.sum (fun q =>
          polygonalInterpolate K (fun l => outgoing l q) t T) := by
  let rhs : Nat -> Real := fun l =>
    x0 + Finset.univ.sum (incoming l) - Finset.univ.sum (outgoing l)
  have hpoly :
      polygonalInterpolate K x t T =
        polygonalInterpolate K rhs t T := by
    unfold polygonalInterpolate
    apply Finset.sum_congr rfl
    intro l hl
    rw [hbalance l (Finset.mem_range.mp hl)]
  rw [hpoly]
  dsimp [rhs]
  rw [calendar_polygonal_sub, calendar_polygonal_add]
  rw [calendar_polygonal_const K x0 t T hT ht]
  rw [calendar_polygonal_sum, calendar_polygonal_sum]

private theorem fi_polygonal_paths_balance
    (K : PNat) (x : Nat -> Buffer -> Real)
    (e : Nat -> Buffer -> Server -> Buffer -> Real)
    (x0 : Buffer -> Real) {t T : Real} (hT : 0 < T)
    (ht : t ∈ Icc (0 : Real) T)
    (hbalance : forall l, l < (K : Nat) + 1 -> forall i,
      x l i = x0 i +
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun q : Buffer => e l q j i) -
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer => e l i j k))
    (i : Buffer) :
    fi_polygonalStatePath K x T t i = x0 i +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          fi_polygonalAllocationPath K e T t q j i) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          fi_polygonalAllocationPath K e T t i j k) := by
  unfold fi_polygonalStatePath fi_polygonalAllocationPath
  have h := calendar_polygonal_balance
    (J := Server) (Q := Server)
    K (fun l => x l i) (x0 i)
    (fun l j => Finset.univ.sum fun q : Buffer => e l q j i)
    (fun l j => Finset.univ.sum fun k : Buffer => e l i j k)
    hT ht (fun l hl => hbalance l hl i)
  simpa only [calendar_polygonal_sum] using h

private theorem calendar_exists_uniformly_convergent_subsequence_finite
    {I J : Type*} [Fintype I] [Fintype J]
    {f : Nat -> I -> Real -> Real}
    {g : Nat -> J -> Real -> Real}
    {control : J -> Real -> Real} {a b M : Real}
    (hf : forall n i, ContinuousOn (f n i) (Icc a b))
    (hbound : forall n i t, t ∈ Icc a b -> abs (f n i t) <= M)
    (hcontrol : forall j, ContinuousOn (control j) (Icc a b))
    (hgconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j t, t ∈ Icc a b ->
          dist (g n j t) (control j t) < epsilon)
    (hdom : forall n i x, x ∈ Icc a b ->
      forall y, y ∈ Icc a b ->
        dist (f n i x) (f n i y) <=
          Finset.univ.sum (fun j => dist (g n j x) (g n j y))) :
    exists q : Nat -> Nat, StrictMono q /\
      exists limit : I -> Real -> Real,
        (forall i, ContinuousOn (limit i) (Icc a b)) /\
        forall epsilon, 0 < epsilon ->
          exists n0, forall n, n0 <= n ->
            forall i t, t ∈ Icc a b ->
              dist (f (q n) i t) (limit i t) < epsilon := by
  let fPi : Nat -> Real -> (I -> Real) :=
    fun n t i => f n i t
  have hfPi (n : Nat) :
      ContinuousOn (fPi n) (Icc a b) := by
    rw [continuousOn_pi]
    exact hf n
  have hboundPi (n : Nat) (t : Real) (ht : t ∈ Icc a b) :
      dist (fPi n t) (0 : I -> Real) <= max M 0 := by
    apply (dist_pi_le_iff (le_max_right _ _)).2
    intro i
    have hi : dist (fPi n t i) 0 <= M := by
      simpa [fPi, Real.dist_eq] using hbound n i t ht
    exact hi.trans (le_max_left _ _)
  have hdomPi (n : Nat) (x : Real) (hx : x ∈ Icc a b)
      (y : Real) (hy : y ∈ Icc a b) :
      dist (fPi n x) (fPi n y) <=
        Finset.univ.sum (fun j => dist (g n j x) (g n j y)) := by
    apply (dist_pi_le_iff (Finset.sum_nonneg
      (fun _ _ => dist_nonneg))).2
    intro i
    exact hdom n i x hx y hy
  obtain ⟨q, hq, limitPi, hlimitPi, hconv⟩ :=
    exists_uniformly_convergent_subsequence_controlled
      (f := fPi) (g := g) (control := control)
      (center := (0 : I -> Real))
      hfPi hboundPi hcontrol hgconv hdomPi
  let limit : I -> Real -> Real := fun i t => limitPi t i
  refine ⟨q, hq, limit, ?_, ?_⟩
  · intro i
    exact (continuousOn_pi.mp hlimitPi) i
  · intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := hconv epsilon hepsilon
    refine ⟨n0, fun n hn i t ht => ?_⟩
    exact lt_of_le_of_lt
      ((dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (fPi (q n) t) (limitPi t) <= _) i)
      (hn0 n hn t ht)

variable (N : Network Buffer Server)

private abbrev BatchedOccurrence {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) :=
  Sigma fun l : Fin gridEdges => Fin (states l).length

private noncomputable def batchedInputInterpolate
    {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) (r : Real) : Real :=
  finiteActionInputInterpolate
    (Finset.univ : Finset (BatchedOccurrence states))
    (fun q => q.1.val) r

private noncomputable def batchedPolicyActionInterpolate
    {gridEdges : Nat} (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin gridEdges -> List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (r : Real) : ActionVector Buffer :=
  finiteActionVectorInterpolate N
    (Finset.univ : Finset (BatchedOccurrence states))
    (fun q => q.1.val)
    (fun q => U K ((states q.1).get q.2) j k) r

private theorem batchedInputInterpolate_eq_batch_sum
    {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) (r : Real) :
    batchedInputInterpolate states r =
      Finset.univ.sum fun l : Fin gridEdges =>
        Finset.univ.sum fun _q : Fin (states l).length =>
          edgeProgress r l.val := by
  classical
  unfold batchedInputInterpolate finiteActionInputInterpolate
  rw [Fintype.sum_sigma]

private theorem batchedPolicyActionInterpolate_eq_batch_sum
    {gridEdges : Nat} (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin gridEdges -> List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (r : Real) (a : Option Buffer) :
    batchedPolicyActionInterpolate N U K states j k r a =
      Finset.univ.sum fun l : Fin gridEdges =>
        Finset.univ.sum fun q : Fin (states l).length =>
          edgeProgress r l.val *
            N.actionDirac (U K ((states l).get q) j k) a := by
  classical
  unfold batchedPolicyActionInterpolate finiteActionVectorInterpolate
  rw [Fintype.sum_sigma]

private theorem batchedInputInterpolate_eq_cumulativeRamp
    {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) (values : Nat -> Real)
    (r : Real) (hzero : values 0 = 0)
    (hstep : forall l : Fin gridEdges,
      values (l.val + 1) - values l.val = (states l).length) :
    batchedInputInterpolate states r =
      values 0 +
        Finset.sum (Finset.range gridEdges) fun l =>
          (values (l + 1) - values l) * edgeProgress r l := by
  classical
  rw [batchedInputInterpolate_eq_batch_sum]
  rw [hzero, zero_add]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro l hl
  rw [hstep l]
  simp

private theorem edgeProgress_nonneg (r : Real) (l : Nat) :
    0 <= edgeProgress r l := by
  unfold edgeProgress
  exact le_max_left _ _

private theorem batchedPolicyActionInterpolate_ratio_mem_epsilon
    {gridEdges : Nat} (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin gridEdges -> List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    {s t : Real} (hst : s <= t)
    (hpos :
      0 < batchedInputInterpolate states t -
        batchedInputInterpolate states s)
    (hK : Inv.inv epsilon <= (K : Real))
    (hnear : forall l y, Membership.mem (states l) y ->
      0 < edgeProgress t l.val - edgeProgress s l.val ->
        IsNearNormalizedState y x epsilon) :
    Membership.mem
      (N.fluidPolicyEpsilonCorrespondence U j k x epsilon)
      (fun a =>
        (batchedPolicyActionInterpolate N U K states j k t a -
            batchedPolicyActionInterpolate N U K states j k s a) /
          (batchedInputInterpolate states t -
            batchedInputInterpolate states s)) := by
  classical
  apply finiteActionInterpolate_ratio_mem_epsilon
      N U j k x epsilon
      (Finset.univ : Finset (BatchedOccurrence states))
      (fun q => q.1.val) (fun _ => K)
      (fun q => (states q.1).get q.2)
  · exact hst
  · exact hpos
  · intro r hr hused
    simpa using hK
  · intro r hr hused
    exact hnear r.1 ((states r.1).get r.2)
      (List.get_mem (states r.1) r.2) hused

private noncomputable def scaledBatchedInputInterpolate
    {Z : Type*} (gridK : PNat)
    (states : Fin (gridK : Nat) -> List Z) (T t : Real) : Real :=
  batchedInputInterpolate states
      (((gridK : Nat) : Real) * t / T) /
    (gridK : Nat)

private noncomputable def scaledBatchedPolicyActionInterpolate
    (gridK : PNat) (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin (gridK : Nat) ->
      List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (T t : Real) : ActionVector Buffer :=
  fun a =>
    batchedPolicyActionInterpolate N U K states j k
        (((gridK : Nat) : Real) * t / T) a /
      (gridK : Nat)

private theorem finiteDifferenceRatio_scaledBatched_mem_epsilon
    (gridK : PNat) (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin (gridK : Nat) ->
      List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    (T t h : Real) (hT : 0 < T) (hh : 0 < h)
    (hpos :
      0 <
        scaledBatchedInputInterpolate gridK states T (t + h) -
          scaledBatchedInputInterpolate gridK states T t)
    (hK : Inv.inv epsilon <= (K : Real))
    (hnear : forall l y, Membership.mem (states l) y ->
      0 <
        edgeProgress (((gridK : Nat) : Real) * (t + h) / T) l.val -
          edgeProgress (((gridK : Nat) : Real) * t / T) l.val ->
        IsNearNormalizedState y x epsilon) :
    Membership.mem
      (N.fluidPolicyEpsilonCorrespondence U j k x epsilon)
      (finiteDifferenceRatio
        (scaledBatchedInputInterpolate gridK states T)
        (scaledBatchedPolicyActionInterpolate
          N gridK U K states j k T)
        t h) := by
  let r0 : Real := ((gridK : Nat) : Real) * t / T
  let r1 : Real := ((gridK : Nat) : Real) * (t + h) / T
  have hgrid : (0 : Real) < (gridK : Nat) := by positivity
  have hr : r0 <= r1 := by
    dsimp [r0, r1]
    apply (div_le_div_iff_of_pos_right hT).2
    exact mul_le_mul_of_nonneg_left (by linarith) hgrid.le
  have hscaled :
      scaledBatchedInputInterpolate gridK states T (t + h) -
          scaledBatchedInputInterpolate gridK states T t =
        (batchedInputInterpolate states r1 -
          batchedInputInterpolate states r0) / (gridK : Nat) := by
    dsimp [scaledBatchedInputInterpolate, r0, r1]
    ring
  have hraw :
      0 < batchedInputInterpolate states r1 -
        batchedInputInterpolate states r0 := by
    rw [hscaled] at hpos
    have hmul := mul_pos hpos hgrid
    rw [div_mul_cancel₀ _ (ne_of_gt hgrid)] at hmul
    exact hmul
  have hm :=
    batchedPolicyActionInterpolate_ratio_mem_epsilon
      N U K states j k x epsilon hr hraw hK hnear
  convert hm using 1
  funext a
  unfold finiteDifferenceRatio
  dsimp [scaledBatchedInputInterpolate,
    scaledBatchedPolicyActionInterpolate, r0, r1]
  field_simp

private theorem ae_derivativeRatio_mem_fluidPolicyCorrespondence
    {TimeMeasure : Measure Real}
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (hA : Filter.Eventually (fun t => DifferentiableAt Real A t)
      (ae TimeMeasure))
    (hE : forall a, Filter.Eventually
      (fun t => DifferentiableAt Real (fun s => E s a) t)
      (ae TimeMeasure))
    (hfinite : Filter.Eventually
      (fun t => 0 < deriv A t ->
        forall epsilon : {r : Real // 0 < r},
          Filter.Eventually
            (fun h =>
              finiteDifferenceRatio A E t h ∈
                N.fluidPolicyEpsilonCorrespondence
                  U j k (X t) epsilon.1)
            (nhdsWithin 0 (Ioi 0)))
      (ae TimeMeasure)) :
    Filter.Eventually
      (fun t => 0 < deriv A t ->
        (fun a => deriv (fun s => E s a) t / deriv A t) ∈
          N.fluidPolicyCorrespondence U j k (X t))
      (ae TimeMeasure) := by
  have hEall :
      Filter.Eventually
        (fun t => forall a, DifferentiableAt Real (fun s => E s a) t)
        (ae TimeMeasure) :=
    ae_all_iff.mpr hE
  filter_upwards [hA, hEall, hfinite] with t hAt hEt hft
  intro hpos
  exact derivativeRatio_mem_fluidPolicyCorrespondence
    N U j k (X t) A E t (deriv A t)
    (fun a => deriv (fun s => E s a) t)
    hAt.hasDerivAt (fun a => (hEt a).hasDerivAt) hpos (hft hpos)

private theorem verifiedPatchedFluidPolicy_isActionDistribution
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) (hstate : IsFluidState (X t)) :
    IsActionDistribution
      (N.verifiedPatchedFluidPolicy U j k X A E t) :=
  fluidPolicyCorrespondence_isActionDistribution N U j k (X t) _
    (verifiedPatchedFluidPolicy_mem N U j k X A E t hstate)

private theorem verifiedPatchedFluidPolicy_incompatible_zero
    (U : N.DeterministicPolicySequence) (j : Server) (k i : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) (hstate : IsFluidState (X t))
    (hi : Not (N.compatible i j)) :
    N.verifiedPatchedFluidPolicy U j k X A E t (some i) = 0 :=
  fluidPolicyCorrespondence_incompatible N U j k i (X t) _
    (verifiedPatchedFluidPolicy_mem N U j k X A E t hstate) hi

private theorem verifiedPatchedFluidPolicy_allocation_rule_ae
    {TimeMeasure : Measure Real}
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (hAnonneg : Filter.Eventually (fun t => 0 <= deriv A t)
      (ae TimeMeasure))
    (hpositive : Filter.Eventually
      (fun t => 0 < deriv A t ->
        (fun a => deriv (fun s => E s a) t / deriv A t) ∈
          N.fluidPolicyCorrespondence U j k (X t))
      (ae TimeMeasure))
    (hzero : Filter.Eventually
      (fun t => deriv A t = 0 ->
        forall a, deriv (fun s => E s a) t = 0)
      (ae TimeMeasure)) :
    Filter.Eventually
      (fun t => forall a,
        deriv (fun s => E s a) t =
          deriv A t *
            N.verifiedPatchedFluidPolicy U j k X A E t a)
      (ae TimeMeasure) := by
  classical
  filter_upwards [hAnonneg, hpositive, hzero] with t hnonneg hpt hzt
  intro a
  by_cases hpos : 0 < deriv A t
  · have hmem := hpt hpos
    simp only [verifiedPatchedFluidPolicy, if_pos hmem]
    field_simp
  · have hz : deriv A t = 0 :=
      le_antisymm (not_lt.mp hpos) hnonneg
    simp [verifiedPatchedFluidPolicy, hz, hzt hz a]

/-- A clock is usable when all interarrivals are positive and its renewal
epochs obey the unit-rate strong law. -/
def IsUsableUnitRateClock (clock : UnitRateClockPath) : Prop :=
  (forall r, 0 < clock r) /\
    Tendsto
      (fun n : Nat => renewalEpoch clock n / (n : Real))
      atTop (nhds 1)

/-- Replace an unusable clock by the deterministic unit clock. -/
noncomputable def totalUnitRateClock
    (clock : UnitRateClockPath) : UnitRateClockPath := by
  classical
  exact if IsUsableUnitRateClock clock then clock else fun _ => 1

@[simp]
theorem totalUnitRateClock_eq_self
    {clock : UnitRateClockPath} (hclock : IsUsableUnitRateClock clock) :
    totalUnitRateClock clock = clock := by
  simp [totalUnitRateClock, hclock]

theorem totalUnitRateClock_pos
    (clock : UnitRateClockPath) (r : Nat) :
    0 < totalUnitRateClock clock r := by
  classical
  by_cases h : IsUsableUnitRateClock clock
  · simpa [totalUnitRateClock, h] using h.1 r
  · simp [totalUnitRateClock, h]

theorem renewalEpoch_oneClock (n : Nat) :
    renewalEpoch (fun _ => (1 : Real)) n = n := by
  simp [renewalEpoch]

theorem totalUnitRateClock_ratio_tendsto
    (clock : UnitRateClockPath) :
    Tendsto
      (fun n : Nat =>
        renewalEpoch (totalUnitRateClock clock) n / (n : Real))
      atTop (nhds 1) := by
  classical
  by_cases h : IsUsableUnitRateClock clock
  · simpa [totalUnitRateClock, h] using h.2
  · have heq :
        (fun n : Nat =>
          renewalEpoch (totalUnitRateClock clock) n / (n : Real)) =ᶠ[atTop]
            fun _ => (1 : Real) := by
      filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
      simp [totalUnitRateClock, h, renewalEpoch_oneClock, Nat.ne_of_gt hn]
    exact tendsto_const_nhds.congr' heq.symm

theorem totalUnitRateClock_isUsable
    (clock : UnitRateClockPath) :
    IsUsableUnitRateClock (totalUnitRateClock clock) :=
  ⟨totalUnitRateClock_pos clock, totalUnitRateClock_ratio_tendsto clock⟩

theorem renewalEpoch_strictMono_totalUnitRateClock
    (clock : UnitRateClockPath) :
    StrictMono (renewalEpoch (totalUnitRateClock clock)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [renewalEpoch_succ]
  exact lt_add_of_pos_right _ (totalUnitRateClock_pos clock n)

theorem totalUnitRateClock_epoch_tendsto_atTop
    (clock : UnitRateClockPath) :
    Tendsto (renewalEpoch (totalUnitRateClock clock)) atTop atTop := by
  have hprod :=
    (totalUnitRateClock_ratio_tendsto clock).pos_mul_atTop
      zero_lt_one tendsto_natCast_atTop_atTop
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : Nat)] with n hn
  simp [Nat.ne_of_gt hn]

theorem totalUnitRateClock_crosses
    (clock : UnitRateClockPath) (s : Real) :
    Exists (fun n => s < renewalEpoch (totalUnitRateClock clock) n) :=
  ((totalUnitRateClock_epoch_tendsto_atTop clock).eventually_gt_atTop s).exists

/-- Totalize every marked clock in a calendar sample. -/
noncomputable def totalCalendarPoissonSample
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) :
    CalendarPoissonSample (Buffer := Buffer) (Server := Server) :=
  fun j k => totalUnitRateClock (omega j k)

theorem totalCalendarPoissonSample_pos
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) (r : Nat) :
    0 < totalCalendarPoissonSample omega j k r :=
  totalUnitRateClock_pos (omega j k) r

theorem totalCalendarPoissonSample_ratio_tendsto
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) :
    Tendsto
      (fun n : Nat =>
        renewalEpoch (totalCalendarPoissonSample omega j k) n / (n : Real))
      atTop (nhds 1) :=
  totalUnitRateClock_ratio_tendsto (omega j k)

theorem totalCalendarPoissonSample_epoch_strictMono
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) :
    StrictMono (renewalEpoch (totalCalendarPoissonSample omega j k)) :=
  renewalEpoch_strictMono_totalUnitRateClock (omega j k)

theorem totalCalendarPoissonSample_epoch_tendsto_atTop
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) :
    Tendsto
      (renewalEpoch (totalCalendarPoissonSample omega j k)) atTop atTop :=
  totalUnitRateClock_epoch_tendsto_atTop (omega j k)

theorem totalCalendarPoissonSample_crosses
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) (s : Real) :
    Exists
      (fun n => s < renewalEpoch (totalCalendarPoissonSample omega j k) n) :=
  totalUnitRateClock_crosses (omega j k) s

/-- Unit exponentials are strictly positive almost surely. -/
theorem unitExp_pos_ae_for_totalization :
    ∀ᵐ x ∂expMeasure 1, 0 < x := by
  rw [ae_iff]
  have hset : {a : Real | ¬ 0 < a} = Set.Iic 0 := by
    ext a
    simp
  rw [hset]
  change expMeasure 1 (Set.Iic 0) = 0
  rw [← ofReal_cdf]
  simp [cdf_expMeasure_eq]

theorem calendarInterarrival_pos_ae_for_totalization
    (j : Server) (k : Buffer) (r : Nat) :
    ∀ᵐ omega ∂N.calendarPoissonMeasure, 0 < omega j k r := by
  let f :
      CalendarPoissonSample (Buffer := Buffer) (Server := Server) -> Real :=
    fun omega => omega j k r
  have hf : AEMeasurable f N.calendarPoissonMeasure := by
    exact ((measurable_pi_apply r).comp
      ((measurable_pi_apply k).comp (measurable_pi_apply j))).aemeasurable
  apply ae_of_ae_map hf
  rw [show N.calendarPoissonMeasure.map f = expMeasure 1 by
    exact N.clockInterarrival_map j k r]
  exact unitExp_pos_ae_for_totalization

theorem all_calendarInterarrival_pos_ae_for_totalization :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      forall j k r, 0 < omega j k r := by
  rw [ae_all_iff]
  intro j
  rw [ae_all_iff]
  intro k
  rw [ae_all_iff]
  intro r
  exact N.calendarInterarrival_pos_ae_for_totalization j k r

theorem totalCalendarPoissonSample_ae_eq :
    totalCalendarPoissonSample =ᵐ[N.calendarPoissonMeasure]
      (id : CalendarPoissonSample (Buffer := Buffer) (Server := Server) ->
        CalendarPoissonSample (Buffer := Buffer) (Server := Server)) := by
  filter_upwards
    [N.all_calendarInterarrival_pos_ae_for_totalization,
      N.all_renewalEpoch_ratio_tendsto_ae] with omega hpos hslln
  funext j k
  exact totalUnitRateClock_eq_self ⟨hpos j k, hslln j k⟩

theorem totalCalendarPoissonSample_ae_eq_apply :
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      totalCalendarPoissonSample omega = omega := by
  filter_upwards [N.totalCalendarPoissonSample_ae_eq] with omega homega
  exact homega

theorem totalCalendarPoissonSample_aemeasurable :
    AEMeasurable
      (totalCalendarPoissonSample :
        CalendarPoissonSample (Buffer := Buffer) (Server := Server) ->
          CalendarPoissonSample (Buffer := Buffer) (Server := Server))
      N.calendarPoissonMeasure := by
  exact measurable_id.aemeasurable.congr
    N.totalCalendarPoissonSample_ae_eq.symm

theorem totalCalendarPoissonSample_map :
    N.calendarPoissonMeasure.map totalCalendarPoissonSample =
      N.calendarPoissonMeasure := by
  rw [Measure.map_congr N.totalCalendarPoissonSample_ae_eq]
  simp

/-- Totalized token count. -/
noncomputable def totalCalendarTokenCount
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) : Nat :=
  N.calendarTokenCount K (totalCalendarPoissonSample omega) t j k

/-- Totalized fluid-scaled primitive input. -/
noncomputable def totalCalendarScaledInput
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) : Real :=
  N.calendarScaledInput K (totalCalendarPoissonSample omega) t j k

theorem totalCalendarScaledInput_tendsto
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (K : Nat -> PNat) (hK : StrictMono K)
    (t : Real) (ht : 0 <= t) (j : Server) (k : Buffer) :
    Tendsto
      (fun r => N.totalCalendarScaledInput (K r) omega t j k)
      atTop (nhds (N.phi j k * t)) := by
  exact N.calendarScaledInput_tendsto
    (totalCalendarPoissonSample omega)
    (fun j k => totalCalendarPoissonSample_ratio_tendsto omega j k)
    K hK t ht j k

/-- Totalized calendar time of an event. -/
noncomputable def totalCalendarEventTime
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (event : CalendarEvent (Buffer := Buffer) (Server := Server)) : Real :=
  N.calendarEventTime K (totalCalendarPoissonSample omega) event

/-- Totalized unsorted event prefix. -/
noncomputable def totalRawCalendarEvents
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    List (CalendarEvent (Buffer := Buffer) (Server := Server)) :=
  N.rawCalendarEvents K (totalCalendarPoissonSample omega) t

/-- Totalized chronological event prefix. -/
noncomputable def totalCalendarEventTieKey
    (event : CalendarEvent (Buffer := Buffer) (Server := Server)) :
    Nat :=
  Nat.pair (Fintype.equivFin Server event.1.1).val
    (Nat.pair (Fintype.equivFin Buffer event.1.2).val event.2)

noncomputable def totalCalendarEventOrderKey
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (event : CalendarEvent (Buffer := Buffer) (Server := Server)) :
    Lex (Real × Nat) :=
  toLex (N.totalCalendarEventTime K omega event,
    totalCalendarEventTieKey event)

/-- Chronology with a horizon-independent deterministic tie-breaker. -/
noncomputable def totalChronologicalCalendarEvents
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    List (CalendarEvent (Buffer := Buffer) (Server := Server)) :=
  by
    classical
    exact (N.totalRawCalendarEvents K omega t).insertionSort fun a b =>
      N.totalCalendarEventOrderKey K omega a <=
        N.totalCalendarEventOrderKey K omega b

/-- Totalized chronological marked-token prefix. -/
noncomputable def totalCalendarTokenPrefix
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  (N.totalChronologicalCalendarEvents K omega t).map fun event => event.1

theorem totalChronologicalCalendarEvents_pairwise
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    (N.totalChronologicalCalendarEvents K omega t).Pairwise
      (fun a b =>
        N.totalCalendarEventTime K omega a <=
          N.totalCalendarEventTime K omega b) := by
  classical
  let r := fun a b : CalendarEvent (Buffer := Buffer) (Server := Server) =>
    N.totalCalendarEventOrderKey K omega a <=
      N.totalCalendarEventOrderKey K omega b
  letI : Std.Total r := ⟨fun a b => le_total
    (N.totalCalendarEventOrderKey K omega a)
    (N.totalCalendarEventOrderKey K omega b)⟩
  letI : IsTrans _ r := ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
  change (List.insertionSort r
    (N.totalRawCalendarEvents K omega t)).Pairwise _
  apply (List.pairwise_insertionSort r _).imp
  intro a b h
  change
    toLex (N.totalCalendarEventTime K omega a,
        totalCalendarEventTieKey a) <=
      toLex (N.totalCalendarEventTime K omega b,
        totalCalendarEventTieKey b) at h
  by_contra hnot
  have hba :
      N.totalCalendarEventTime K omega b <
        N.totalCalendarEventTime K omega a :=
    lt_of_not_ge hnot
  have hkey :
      toLex (N.totalCalendarEventTime K omega b,
          totalCalendarEventTieKey b) <
        toLex (N.totalCalendarEventTime K omega a,
          totalCalendarEventTieKey a) :=
    Prod.Lex.left _ _ hba
  exact (not_lt_of_ge h) hkey

theorem totalChronologicalCalendarEvents_perm_raw
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    List.Perm (N.totalChronologicalCalendarEvents K omega t)
      (N.totalRawCalendarEvents K omega t) := by
  classical
  unfold totalChronologicalCalendarEvents
  exact List.perm_insertionSort _ _

theorem totalChronologicalCalendarEvents_perm_original
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    List.Perm (N.totalChronologicalCalendarEvents K omega t)
      (N.chronologicalCalendarEvents K
        (totalCalendarPoissonSample omega) t) := by
  classical
  apply (N.totalChronologicalCalendarEvents_perm_raw K omega t).trans
  unfold totalRawCalendarEvents chronologicalCalendarEvents
  exact (List.perm_insertionSort _ _).symm

theorem mem_totalRawCalendarEvents_iff
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real)
    (event : CalendarEvent (Buffer := Buffer) (Server := Server)) :
    event ∈ N.totalRawCalendarEvents K omega t ↔
      event.2 <
        N.totalCalendarTokenCount K omega t event.1.1 event.1.2 := by
  classical
  simp only [totalRawCalendarEvents, rawCalendarEvents,
    totalCalendarTokenCount, List.mem_flatMap, Finset.mem_toList,
    Finset.mem_univ, true_and, List.mem_map, Finset.mem_range]
  constructor
  · rintro ⟨j, k, r, hr, rfl⟩
    exact hr
  · intro hr
    exact ⟨event.1.1, event.1.2, event.2, hr, by
      rcases event with ⟨⟨j, k⟩, r⟩
      rfl⟩

theorem mem_totalChronologicalCalendarEvents_iff
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real)
    (event : CalendarEvent (Buffer := Buffer) (Server := Server)) :
    event ∈ N.totalChronologicalCalendarEvents K omega t ↔
      event.2 <
        N.totalCalendarTokenCount K omega t event.1.1 event.1.2 := by
  rw [(N.totalChronologicalCalendarEvents_perm_raw K omega t).mem_iff]
  exact N.mem_totalRawCalendarEvents_iff K omega t event

theorem totalCalendarTokenPrefix_eq_marks
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    N.totalCalendarTokenPrefix K omega t =
      (N.totalChronologicalCalendarEvents K omega t).map
        (fun event => event.1) := by
  rfl

theorem totalCalendarEventTime_strictMono_coordinate
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer)
    (hphi : 0 < N.phi j k) :
    StrictMono
      (fun r =>
        N.totalCalendarEventTime K omega ((j, k), r)) := by
  intro r q hrq
  unfold totalCalendarEventTime calendarEventTime
  exact (div_lt_div_iff_of_pos_right (mul_pos (by positivity) hphi)).2
    (totalCalendarPoissonSample_epoch_strictMono omega j k
      (Nat.add_lt_add_right hrq 1))

theorem lt_totalCalendarTokenCount_iff_eventTime_le
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) (r : Nat)
    (hphi : 0 < N.phi j k) :
    r < N.totalCalendarTokenCount K omega t j k ↔
      N.totalCalendarEventTime K omega ((j, k), r) <= max t 0 := by
  let clock := totalCalendarPoissonSample omega j k
  let operational := N.coordinateOperationalTime K t j k
  have hdenom : 0 < ((K : Nat) : Real) * N.phi j k :=
    mul_pos (by positivity) hphi
  have hepochPos :
      0 < renewalEpoch clock (r + 1) := by
    have hmono :=
      totalCalendarPoissonSample_epoch_strictMono omega j k
        (Nat.zero_lt_succ r)
    simpa [clock] using hmono
  by_cases ht : 0 < t
  · have hmax : max t 0 = t := max_eq_left ht.le
    have hoperational :
        operational = (((K : Nat) : Real) * N.phi j k) * t := by
      simp [operational, coordinateOperationalTime, hmax]
    have hopPos : 0 < operational := by
      rw [hoperational]
      exact mul_pos hdenom ht
    have hcross :
        Exists (fun n => operational < renewalEpoch clock n) := by
      simpa [clock] using
        totalCalendarPoissonSample_crosses omega j k operational
    let count := unitPoissonCount clock operational
    have hcountLe :
        renewalEpoch clock count <= operational :=
      renewalEpoch_count_le clock hopPos hcross
    have hopenLt :
        operational < renewalEpoch clock (count + 1) :=
      lt_renewalEpoch_count_add_one clock hopPos hcross
    change r < count ↔ _
    rw [hmax]
    unfold totalCalendarEventTime calendarEventTime
    constructor
    · intro hr
      have hindex : r + 1 <= count := by omega
      have hepochLe :
          renewalEpoch clock (r + 1) <= renewalEpoch clock count :=
        (totalCalendarPoissonSample_epoch_strictMono omega j k).monotone
          hindex
      apply (div_le_iff₀ hdenom).2
      rw [mul_comm, ← hoperational]
      exact hepochLe.trans hcountLe
    · intro hevent
      have hepochLe : renewalEpoch clock (r + 1) <= operational := by
        rw [hoperational, mul_comm]
        exact (div_le_iff₀ hdenom).1 hevent
      have hepochLt :
          renewalEpoch clock (r + 1) <
            renewalEpoch clock (count + 1) :=
        hepochLe.trans_lt hopenLt
      have hindex : r + 1 < count + 1 :=
        (totalCalendarPoissonSample_epoch_strictMono omega j k).lt_iff_lt.mp
          hepochLt
      omega
  · have ht0 : t <= 0 := le_of_not_gt ht
    have hmax : max t 0 = 0 := max_eq_right ht0
    have hcount :
        N.totalCalendarTokenCount K omega t j k = 0 := by
      unfold totalCalendarTokenCount
      exact N.calendarTokenCount_of_nonpos
        K (totalCalendarPoissonSample omega) ht0 j k
    rw [hcount, hmax]
    constructor
    · omega
    · unfold totalCalendarEventTime calendarEventTime
      intro hevent
      change renewalEpoch clock (r + 1) /
          (((K : Nat) : Real) * N.phi j k) <= 0 at hevent
      exact False.elim ((not_le_of_gt (div_pos hepochPos hdenom)) hevent)

theorem totalCalendarTokenCount_mono
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    {s t : Real} (hst : s <= t) (j : Server) (k : Buffer) :
    N.totalCalendarTokenCount K omega s j k <=
      N.totalCalendarTokenCount K omega t j k := by
  rcases (N.phi_nonneg j k).eq_or_lt with hzero | hphi
  · have hphi0 : N.phi j k = 0 := hzero.symm
    simp [totalCalendarTokenCount, hphi0]
  · by_contra hnot
    have hlt :
        N.totalCalendarTokenCount K omega t j k <
          N.totalCalendarTokenCount K omega s j k := by omega
    have hold :=
      (N.lt_totalCalendarTokenCount_iff_eventTime_le
        K omega s j k (N.totalCalendarTokenCount K omega t j k) hphi).1 hlt
    have hmax : max s 0 <= max t 0 := max_le_max_right 0 hst
    have hnew :=
      (N.lt_totalCalendarTokenCount_iff_eventTime_le
        K omega t j k (N.totalCalendarTokenCount K omega t j k) hphi).2
        (hold.trans hmax)
    omega

theorem totalCalendarEventTieKey_injective :
    Function.Injective
      (totalCalendarEventTieKey :
        CalendarEvent (Buffer := Buffer) (Server := Server) ->
          Nat) := by
  rintro ⟨⟨j, k⟩, r⟩ ⟨⟨j', k'⟩, r'⟩ h
  simp only [totalCalendarEventTieKey, Nat.pair_eq_pair] at h
  rcases h with ⟨hjfin, hkfin, hr⟩
  have hj : j = j' :=
    (Fintype.equivFin Server).injective (Fin.ext hjfin)
  have hk : k = k' :=
    (Fintype.equivFin Buffer).injective (Fin.ext hkfin)
  subst j'
  subst k'
  subst r'
  rfl

theorem totalCalendarEventOrderKey_injective
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) :
    Function.Injective (N.totalCalendarEventOrderKey K omega) := by
  intro a b h
  apply totalCalendarEventTieKey_injective
  have h' := congrArg ofLex h
  exact congrArg Prod.snd h'

theorem totalRawCalendarEvents_nodup
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    (N.totalRawCalendarEvents K omega t).Nodup := by
  classical
  unfold totalRawCalendarEvents rawCalendarEvents
  apply List.nodup_flatMap.2
  constructor
  · intro j hj
    apply List.nodup_flatMap.2
    constructor
    · intro k hk
      exact (Finset.nodup_toList _).map fun r q h => by
        simpa using congrArg (fun event => event.2) h
    · apply (Finset.nodup_toList _).imp
      intro k q hkq
      rw [Function.onFun, List.disjoint_left]
      intro event heventk heventq
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_range] at heventk
      simp only [List.mem_map, Finset.mem_toList, Finset.mem_range] at heventq
      rcases heventk with ⟨r, hr, rfl⟩
      rcases heventq with ⟨u, hu, heq⟩
      exact hkq (by
        simpa using (congrArg (fun event => event.1.2) heq).symm)
  · apply (Finset.nodup_toList _).imp
    intro j q hjq
    rw [Function.onFun, List.disjoint_left]
    intro event heventj heventq
    simp only [List.mem_flatMap, Finset.mem_toList, Finset.mem_univ,
      true_and, List.mem_map, Finset.mem_range] at heventj heventq
    rcases heventj with ⟨k, r, hr, rfl⟩
    rcases heventq with ⟨l, u, hu, heq⟩
    exact hjq (by
      simpa using (congrArg (fun event => event.1.1) heq).symm)

theorem totalChronologicalCalendarEvents_pairwise_orderKey
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    (N.totalChronologicalCalendarEvents K omega t).Pairwise
      (fun a b =>
        N.totalCalendarEventOrderKey K omega a <=
          N.totalCalendarEventOrderKey K omega b) := by
  classical
  let r := fun a b : CalendarEvent (Buffer := Buffer) (Server := Server) =>
    N.totalCalendarEventOrderKey K omega a <=
      N.totalCalendarEventOrderKey K omega b
  letI : Std.Total r := ⟨fun a b => le_total
    (N.totalCalendarEventOrderKey K omega a)
    (N.totalCalendarEventOrderKey K omega b)⟩
  letI : IsTrans _ r := ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
  change (List.insertionSort r
    (N.totalRawCalendarEvents K omega t)).Pairwise r
  exact List.pairwise_insertionSort r _

theorem totalChronologicalCalendarEvents_nodup
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    (N.totalChronologicalCalendarEvents K omega t).Nodup :=
  (N.totalChronologicalCalendarEvents_perm_raw K omega t).nodup_iff.mpr
    (N.totalRawCalendarEvents_nodup K omega t)

private theorem eventTime_le_of_orderKey_le
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    {a b : CalendarEvent (Buffer := Buffer) (Server := Server)}
    (h :
      N.totalCalendarEventOrderKey K omega a <=
        N.totalCalendarEventOrderKey K omega b) :
    N.totalCalendarEventTime K omega a <=
      N.totalCalendarEventTime K omega b := by
  by_contra hnot
  have hba :
      N.totalCalendarEventTime K omega b <
        N.totalCalendarEventTime K omega a :=
    lt_of_not_ge hnot
  have hkey :
      toLex (N.totalCalendarEventTime K omega b,
          totalCalendarEventTieKey b) <
        toLex (N.totalCalendarEventTime K omega a,
          totalCalendarEventTieKey a) :=
    Prod.Lex.left _ _ hba
  exact (not_lt_of_ge h) hkey

private theorem list_eq_filter_append_filter_not
    {alpha : Type*} (p : alpha -> Prop) [DecidablePred p]
    (r : alpha -> alpha -> Prop) [DecidableRel r]
    (l : List alpha)
    (hpair : l.Pairwise r)
    (hdown :
      forall {a b}, a ∈ l -> b ∈ l -> r a b -> p b -> p a) :
    l = l.filter (fun a => decide (p a)) ++
      l.filter (fun a => decide (¬ p a)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.pairwise_cons] at hpair
      by_cases ha : p a
      · have hdownTail :
            forall {b c}, b ∈ l -> c ∈ l -> r b c -> p c -> p b := by
          intro b c hb hc hbc hpc
          exact hdown (List.mem_cons_of_mem a hb)
            (List.mem_cons_of_mem a hc) hbc hpc
        simpa [ha] using congrArg (List.cons a) (ih hpair.2 hdownTail)
      · have hnone : forall b, b ∈ l -> ¬ p b := by
          intro b hb hpb
          exact ha (hdown (List.mem_cons_self)
            (List.mem_cons_of_mem a hb) (hpair.1 b hb) hpb)
        have hpempty :
            l.filter (fun b => decide (p b)) = [] :=
          List.filter_eq_nil_iff.mpr fun b hb => by
            simp [hnone b hb]
        have hnself :
            l.filter (fun b => !decide (p b)) = l :=
          List.filter_eq_self.mpr fun b hb => by
            simp [hnone b hb]
        simp [ha, hpempty, hnself]

theorem totalChronologicalCalendarEvents_append
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    {s t : Real} (hst : s <= t) :
    exists suffix,
      N.totalChronologicalCalendarEvents K omega t =
        N.totalChronologicalCalendarEvents K omega s ++ suffix := by
  classical
  let old : CalendarEvent (Buffer := Buffer) (Server := Server) -> Prop :=
    fun event =>
      event.2 <
        N.totalCalendarTokenCount K omega s event.1.1 event.1.2
  let later := N.totalChronologicalCalendarEvents K omega t
  let earlier := N.totalChronologicalCalendarEvents K omega s
  have hcountMono (j : Server) (k : Buffer) :
      N.totalCalendarTokenCount K omega s j k <=
        N.totalCalendarTokenCount K omega t j k :=
    N.totalCalendarTokenCount_mono K omega hst j k
  have hmem (event : CalendarEvent (Buffer := Buffer) (Server := Server)) :
      event ∈ later.filter (fun event => decide (old event)) ↔
        event ∈ earlier := by
    rw [List.mem_filter]
    rw [show event ∈ later ↔
        event.2 <
          N.totalCalendarTokenCount K omega t event.1.1 event.1.2 by
      exact N.mem_totalChronologicalCalendarEvents_iff K omega t event]
    rw [show event ∈ earlier ↔
        event.2 <
          N.totalCalendarTokenCount K omega s event.1.1 event.1.2 by
      exact N.mem_totalChronologicalCalendarEvents_iff K omega s event]
    constructor
    · exact fun h => of_decide_eq_true h.2
    · intro hs
      exact ⟨hs.trans_le (hcountMono event.1.1 event.1.2),
        decide_eq_true hs⟩
  have hfilterEq :
      later.filter (fun event => decide (old event)) = earlier := by
    letI : Std.Antisymm
        (fun a b : CalendarEvent (Buffer := Buffer) (Server := Server) =>
          N.totalCalendarEventOrderKey K omega a <=
            N.totalCalendarEventOrderKey K omega b) :=
      ⟨fun a b hab hba =>
      N.totalCalendarEventOrderKey_injective K omega
        (le_antisymm hab hba)⟩
    have hperm : List.Perm
        (later.filter (fun event => decide (old event))) earlier :=
      (List.perm_ext_iff_of_nodup
        ((N.totalChronologicalCalendarEvents_nodup K omega t).filter _)
        (N.totalChronologicalCalendarEvents_nodup K omega s)).2 hmem
    exact List.Perm.eq_of_pairwise'
      (r := fun a b : CalendarEvent (Buffer := Buffer) (Server := Server) =>
        N.totalCalendarEventOrderKey K omega a <=
          N.totalCalendarEventOrderKey K omega b)
      ((N.totalChronologicalCalendarEvents_pairwise_orderKey K omega t).filter _)
      (N.totalChronologicalCalendarEvents_pairwise_orderKey K omega s)
      hperm
  have hdown :
      forall {a b}, a ∈ later -> b ∈ later ->
        N.totalCalendarEventOrderKey K omega a <=
          N.totalCalendarEventOrderKey K omega b ->
        old b -> old a := by
    intro a b ha hb hab hbold
    have hbphi : 0 < N.phi b.1.1 b.1.2 := by
      rcases (N.phi_nonneg b.1.1 b.1.2).eq_or_lt with hzero | hpos
      · have hphi0 : N.phi b.1.1 b.1.2 = 0 := hzero.symm
        simp [old, totalCalendarTokenCount, hphi0] at hbold
      · exact hpos
    have hbtime :
        N.totalCalendarEventTime K omega b <= max s 0 :=
      (N.lt_totalCalendarTokenCount_iff_eventTime_le
        K omega s b.1.1 b.1.2 b.2 hbphi).1 hbold
    have hatime :
        N.totalCalendarEventTime K omega a <= max s 0 :=
      (N.eventTime_le_of_orderKey_le K omega hab).trans hbtime
    have haphi : 0 < N.phi a.1.1 a.1.2 := by
      have hat :
          a.2 < N.totalCalendarTokenCount K omega t a.1.1 a.1.2 :=
        (N.mem_totalChronologicalCalendarEvents_iff K omega t a).1 ha
      rcases (N.phi_nonneg a.1.1 a.1.2).eq_or_lt with hzero | hpos
      · have hphi0 : N.phi a.1.1 a.1.2 = 0 := hzero.symm
        simp [totalCalendarTokenCount, hphi0] at hat
      · exact hpos
    exact
      (N.lt_totalCalendarTokenCount_iff_eventTime_le
        K omega s a.1.1 a.1.2 a.2 haphi).2 hatime
  have hsplit :
      later =
        later.filter (fun event => decide (old event)) ++
          later.filter (fun event => decide (¬ old event)) :=
    list_eq_filter_append_filter_not old
      (fun a b =>
        N.totalCalendarEventOrderKey K omega a <=
          N.totalCalendarEventOrderKey K omega b)
      later
      (N.totalChronologicalCalendarEvents_pairwise_orderKey K omega t)
      hdown
  refine ⟨later.filter (fun event => decide (¬ old event)), ?_⟩
  simpa [later, earlier, hfilterEq] using hsplit

theorem totalCalendarTokenPrefix_append
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    {s t : Real} (hst : s <= t) :
    exists suffix,
      N.totalCalendarTokenPrefix K omega t =
        N.totalCalendarTokenPrefix K omega s ++ suffix := by
  obtain ⟨suffix, hsuffix⟩ :=
    N.totalChronologicalCalendarEvents_append K omega hst
  refine ⟨suffix.map (fun event => event.1), ?_⟩
  simp [totalCalendarTokenPrefix, hsuffix]

/-- Totalized queue state from an arbitrary finite initial state. -/
noncomputable def totalCalendarScaledQueueStateFrom
    (U : N.DeterministicPolicySequence)
    (K : PNat)
    (x0 : JobState Buffer (K : Nat))
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (i : Buffer) : Real :=
  (N.runTokens (U K) x0
      (N.totalCalendarTokenPrefix K omega t) i : Real) /
    ((K : Nat) : Real)

/-- Totalized cumulative allocation from arbitrary finite initial states. -/
noncomputable def totalCalendarScaledAllocationFrom
    (initial : forall K : PNat, JobState Buffer (K : Nat))
    (U : N.DeterministicPolicySequence)
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (i : Buffer) (j : Server) (k : Buffer) : Real :=
  (N.runAllocationCount (U K) (initial K)
      (N.totalCalendarTokenPrefix K omega t) i j k : Real) /
    ((K : Nat) : Real)

/-- Calendar-time execution from arbitrary initial states, with every pathwise
observable driven by the totalized sample. -/
noncomputable def calendarPoissonExecutionFrom
    (initial : forall K : PNat, JobState Buffer (K : Nat)) :
    N.ScaledStochasticExecution
      (CalendarPoissonSample (Buffer := Buffer) (Server := Server)) where
  probability :=
    (show ProbabilityMeasure
      (CalendarPoissonSample (Buffer := Buffer) (Server := Server)) from
      ⟨N.calendarPoissonMeasure, inferInstance⟩)
  input := fun K omega t j k =>
    N.totalCalendarScaledInput K omega t j k
  state := fun U K omega t i =>
    N.totalCalendarScaledQueueStateFrom U K (initial K) omega t i
  allocation := fun U K omega t i j k =>
    N.totalCalendarScaledAllocationFrom initial U K omega t i j k

theorem totalCalendarScaledInput_ae_eq
    (K : PNat) (t : Real) (j : Server) (k : Buffer) :
    (fun omega => N.totalCalendarScaledInput K omega t j k) =ᵐ[
        N.calendarPoissonMeasure]
      fun omega => N.calendarScaledInput K omega t j k := by
  filter_upwards [N.totalCalendarPoissonSample_ae_eq_apply] with omega homega
  simp [totalCalendarScaledInput, homega]

theorem calendarPoissonExecutionFrom_subsequentialInput
    (initial : forall K : PNat, JobState Buffer (K : Nat)) :
    N.PoissonSubsequentialInputReadback
      (N.calendarPoissonExecutionFrom initial) := by
  intro T hT U K hK A X
  change
    ∀ᵐ omega ∂N.calendarPoissonMeasure,
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn
          T U K omega (A omega) (X omega) ->
        N.IsNominalFluidInput T (A omega)
  filter_upwards [] with omega
  intro hconverges
  intro t ht j k
  have hcandidate :
      Tendsto
        (fun r =>
          N.totalCalendarScaledInput (K r) omega t j k)
        atTop (nhds (A omega t j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hconverges.1 epsilon hepsilon
    refine ⟨r0, fun r hr => ?_⟩
    simpa only [calendarPoissonExecutionFrom, Real.dist_eq] using
      hr0 r hr t ht (j, k)
  have hnominal :
      Tendsto
        (fun r =>
          N.totalCalendarScaledInput (K r) omega t j k)
        atTop (nhds (N.phi j k * t)) :=
    N.totalCalendarScaledInput_tendsto omega K hK t ht.1 j k
  exact tendsto_nhds_unique hcandidate hnominal

noncomputable section

attribute [local instance] tokenTypeMeasurableSpace

variable (N : Network Buffer Server)
variable (initial : forall K : PNat, JobState Buffer (K : Nat))

private theorem pnat_val_strictMono
    {K : Nat -> PNat} (hK : StrictMono K) :
    StrictMono (fun r => (K r : Nat)) := by
  intro r s hrs
  exact hK hrs

private theorem pnat_val_tendsto_atTop
    {K : Nat -> PNat} (hK : StrictMono K) :
    Tendsto (fun r => (K r : Nat)) atTop atTop :=
  (pnat_val_strictMono hK).tendsto_atTop

private noncomputable def calendarScaledQueueStateFromInitial
    (U : N.DeterministicPolicySequence) (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (i : Buffer) : Real :=
  N.totalCalendarScaledQueueStateFrom U K (initial K) omega t i

private noncomputable def calendarScaledAllocationFromInitial
    (U : N.DeterministicPolicySequence) (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (i : Buffer) (j : Server) (k : Buffer) : Real :=
  N.totalCalendarScaledAllocationFrom initial U K omega t i j k

private theorem totalRawCalendarEvents_token_count
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) :
    ((N.totalRawCalendarEvents K omega t).map fun event => event.1).count
        (j, k) =
      N.totalCalendarTokenCount K omega t j k := by
  classical
  simp only [totalRawCalendarEvents, rawCalendarEvents,
    List.map_flatMap, List.map_map]
  simp [Function.comp_def]
  have hinner (a : Server) :
      List.count (j, k)
          (Finset.univ.toList.flatMap fun b =>
            List.replicate (N.totalCalendarTokenCount K omega t a b)
              (a, b)) =
        if a = j then N.totalCalendarTokenCount K omega t a k else 0 := by
    rw [List.count_flatMap]
    by_cases ha : a = j
    · subst a
      simp [List.count_replicate]
    · simp [List.count_replicate, ha]
  rw [List.count_flatMap]
  change (Finset.univ.toList.map (fun a => List.count (j, k)
    (Finset.univ.toList.flatMap fun b =>
      List.replicate (N.totalCalendarTokenCount K omega t a b)
        (a, b)))).sum =
      N.totalCalendarTokenCount K omega t j k
  simp_rw [hinner]
  simp

private theorem totalCalendarTokenPrefix_count
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) :
    (N.totalCalendarTokenPrefix K omega t).count (j, k) =
      N.totalCalendarTokenCount K omega t j k := by
  classical
  unfold totalCalendarTokenPrefix
  calc
    ((N.totalChronologicalCalendarEvents K omega t).map
        fun event => event.1).count (j, k) =
        ((N.totalRawCalendarEvents K omega t).map
          fun event => event.1).count (j, k) :=
      ((N.totalChronologicalCalendarEvents_perm_raw K omega t).map
        fun event => event.1).count_eq _
    _ = N.totalCalendarTokenCount K omega t j k :=
      totalRawCalendarEvents_token_count N K omega t j k

private theorem calendarScaledInput_eq_prefix_count
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (t : Real)
    (j : Server) (k : Buffer) :
    N.totalCalendarScaledInput K omega t j k =
      ((N.totalCalendarTokenPrefix K omega t).count (j, k) : Real) /
        (K : Nat) := by
  unfold totalCalendarScaledInput calendarScaledInput
  rw [totalCalendarTokenPrefix_count N]
  rfl

private theorem totalCalendarTokenPrefix_zero
    (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) :
    N.totalCalendarTokenPrefix K omega 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro jk hjk
  have hpositive :
      0 < (N.totalCalendarTokenPrefix K omega 0).count jk :=
    List.count_pos_iff.2 hjk
  rcases jk with ⟨j, k⟩
  rw [totalCalendarTokenPrefix_count N] at hpositive
  simpa [totalCalendarTokenCount] using hpositive

private def calendarGridTime (T : Real) (K : PNat) (l : Nat) : Real :=
  T * (l : Real) / (K : Nat)

private theorem calendarGridTime_zero (T : Real) (K : PNat) :
    calendarGridTime T K 0 = 0 := by
  simp [calendarGridTime]

private theorem calendarGridTime_succ_sub
    (T : Real) (K : PNat) (l : Nat) :
    calendarGridTime T K (l + 1) - calendarGridTime T K l =
      T / (K : Nat) := by
  unfold calendarGridTime
  push_cast
  ring

private theorem calendarGridTime_mem_Icc
    {T : Real} (hT : 0 < T) (K : PNat) {l : Nat}
    (hl : l <= (K : Nat)) :
    calendarGridTime T K l ∈ Icc (0 : Real) T := by
  have hK : (0 : Real) < (K : Nat) := by positivity
  constructor
  · exact div_nonneg
      (mul_nonneg hT.le (Nat.cast_nonneg l)) hK.le
  · apply (div_le_iff₀ hK).2
    have hl' : (l : Real) <= (K : Nat) := by exact_mod_cast hl
    nlinarith

private theorem calendarGridTime_mono
    {T : Real} (hT : 0 < T) (K : PNat) {l m : Nat}
    (hlm : l <= m) :
    calendarGridTime T K l <= calendarGridTime T K m := by
  unfold calendarGridTime
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlm) hT.le

private def calendarGridPrefix
    (T : Real) (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  N.totalCalendarTokenPrefix K omega (calendarGridTime T K l)

private def calendarGridBatch
  (T : Real) (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  (N.calendarGridPrefix T K omega (l + 1)).drop
    (N.calendarGridPrefix T K omega l).length

private theorem calendarGridPrefix_succ
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    N.calendarGridPrefix T K omega (l + 1) =
      N.calendarGridPrefix T K omega l ++
        N.calendarGridBatch T K omega l := by
  unfold calendarGridPrefix calendarGridBatch
  obtain ⟨suffix, hsuffix⟩ :=
    N.totalCalendarTokenPrefix_append K omega
      (calendarGridTime_mono hT K (Nat.le_succ l))
  change
    N.totalCalendarTokenPrefix K omega (calendarGridTime T K (l + 1)) =
      N.totalCalendarTokenPrefix K omega (calendarGridTime T K l) ++
        (N.totalCalendarTokenPrefix K omega
          (calendarGridTime T K (l + 1))).drop
            (N.totalCalendarTokenPrefix K omega
              (calendarGridTime T K l)).length
  rw [hsuffix, List.drop_left]

private theorem calendarGridBatch_length
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    (N.calendarGridBatch T K omega l).length =
      (N.calendarGridPrefix T K omega (l + 1)).length -
        (N.calendarGridPrefix T K omega l).length := by
  unfold calendarGridBatch
  rw [List.length_drop]

private theorem calendarGridBatch_count
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (j : Server) (k : Buffer) :
    (N.calendarGridBatch T K omega l).count (j, k) =
      (N.calendarGridPrefix T K omega (l + 1)).count (j, k) -
        (N.calendarGridPrefix T K omega l).count (j, k) := by
  have hp := calendarGridPrefix_succ N hT K omega l
  rw [hp, List.count_append, Nat.add_sub_cancel_left]

private def calendarGridState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    JobState Buffer (K : Nat) :=
  N.runTokens (U K) (initial K)
    (N.calendarGridPrefix T K omega l)

private def calendarGridAllocation
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) : Nat :=
  N.runAllocationCount (U K) (initial K)
    (N.calendarGridPrefix T K omega l) i j k

private def calendarGridInput
    (T : Real) (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (j : Server) (k : Buffer) : Nat :=
  (N.calendarGridPrefix T K omega l).count (j, k)

private noncomputable def calendarPolygonalState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) : FluidStatePath Buffer :=
  fun t i =>
    polygonalInterpolate K
      (fun l => (N.calendarGridState initial T U K omega l i : Real) / (K : Nat))
      t T

private noncomputable def calendarPolygonalAllocation
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) :
    FluidAllocationPath Buffer Server :=
  fun t i j k =>
    polygonalInterpolate K
      (fun l =>
        (N.calendarGridAllocation initial T U K omega l i j k : Real) / (K : Nat))
      t T

private noncomputable def calendarPolygonalInput
    (T : Real) (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) :
    MatrixPath Server Buffer :=
  fun t j k =>
    polygonalInterpolate K
      (fun l => (N.calendarGridInput T K omega l j k : Real) / (K : Nat))
      t T

private theorem continuous_calendarPolygonalState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    Continuous (fun t => N.calendarPolygonalState initial T U K omega t i) := by
  unfold calendarPolygonalState polygonalInterpolate hatWeight
  fun_prop

private theorem continuous_calendarPolygonalAllocation
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (i : Buffer) (j : Server) (k : Buffer) :
    Continuous
      (fun t => N.calendarPolygonalAllocation initial T U K omega t i j k) := by
  unfold calendarPolygonalAllocation polygonalInterpolate hatWeight
  fun_prop

private theorem continuous_calendarPolygonalInput
    (T : Real) (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) :
    Continuous (fun t => N.calendarPolygonalInput T K omega t j k) := by
  unfold calendarPolygonalInput polygonalInterpolate hatWeight
  fun_prop

private theorem calendarGridState_succ
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    N.calendarGridState initial T U K omega (l + 1) =
      N.runTokens (U K) (N.calendarGridState initial T U K omega l)
        (N.calendarGridBatch T K omega l) := by
  unfold calendarGridState
  rw [calendarGridPrefix_succ N hT K omega l]
  exact runTokens_append N _ _ _ _

private theorem calendarGridAllocation_succ
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    N.calendarGridAllocation initial T U K omega (l + 1) i j k =
      N.calendarGridAllocation initial T U K omega l i j k +
        N.runAllocationCount (U K)
          (N.calendarGridState initial T U K omega l)
          (N.calendarGridBatch T K omega l) i j k := by
  unfold calendarGridAllocation calendarGridState
  rw [calendarGridPrefix_succ N hT K omega l]
  exact runAllocationCount_append N _ _ _ _ _ _ _

private theorem calendarGridInput_mono
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) {l m : Nat} (hlm : l <= m)
    (j : Server) (k : Buffer) :
    N.calendarGridInput T K omega l j k <=
      N.calendarGridInput T K omega m j k := by
  unfold calendarGridInput calendarGridPrefix
  obtain ⟨suffix, hprefix⟩ :=
    N.totalCalendarTokenPrefix_append K omega
      (calendarGridTime_mono hT K hlm)
  rw [hprefix, List.count_append]
  omega

private theorem calendarGridInput_succ_sub
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) (j : Server) (k : Buffer) :
    N.calendarGridInput T K omega (l + 1) j k -
        N.calendarGridInput T K omega l j k =
      (N.calendarGridBatch T K omega l).count (j, k) := by
  exact (calendarGridBatch_count N hT K omega l j k).symm

private theorem allTokenCounts_sum
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    (Finset.univ.sum fun jk : Server × Buffer => tokens.count jk) =
      tokens.length := by
  classical
  induction tokens with
  | nil =>
      simp
  | cons a tokens ih =>
      simp only [List.count_cons, List.length_cons]
      rw [Finset.sum_add_distrib, ih]
      have hone :
          Finset.univ.sum
              (fun jk : Server × Buffer =>
                if a == jk then 1 else 0) = 1 := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro b hb hba
          have hab : Not (a = b) := Ne.symm hba
          simp [hab]
        · simp
      rw [hone]

private theorem calendarGridInput_sum
    (T : Real) (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        N.calendarGridInput T K omega l j k) =
      (N.calendarGridPrefix T K omega l).length := by
  classical
  let tokens := N.calendarGridPrefix T K omega l
  calc
    (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          N.calendarGridInput T K omega l j k) =
        Finset.univ.sum fun jk : Server × Buffer =>
          tokens.count jk := by
      have hprod :
          (Finset.univ : Finset (Server × Buffer)) =
            (Finset.univ : Finset Server).product
              (Finset.univ : Finset Buffer) := by
        ext jk
        simp
      rw [hprod]
      simpa [tokens, calendarGridInput] using
        (Finset.sum_product
          (Finset.univ : Finset Server)
          (Finset.univ : Finset Buffer)
          (fun jk : Server × Buffer => tokens.count jk)).symm
    _ = tokens.length := allTokenCounts_sum (Buffer := Buffer)
      (Server := Server) tokens

private theorem calendarGridBatch_length_eq_input_sum
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    (N.calendarGridBatch T K omega l).length =
      Finset.univ.sum (fun jk : Server × Buffer =>
          N.calendarGridInput T K omega (l + 1) jk.1 jk.2 -
          N.calendarGridInput T K omega l jk.1 jk.2) := by
  classical
  rw [<- allTokenCounts_sum (Buffer := Buffer) (Server := Server)
    (N.calendarGridBatch T K omega l)]
  apply Finset.sum_congr rfl
  intro jk hjk
  exact (calendarGridInput_succ_sub N hT K omega l jk.1 jk.2).symm

private theorem calendarGridState_isFluidState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    IsFluidState (fun i =>
      (N.calendarGridState initial T U K omega l i : Real) / (K : Nat)) := by
  constructor
  · intro i
    positivity
  · rw [<- Finset.sum_div]
    rw [show
      Finset.univ.sum
          (fun i => ((N.calendarGridState initial T U K omega l i : Nat) : Real)) =
        ((K : Nat) : Real) by
      exact_mod_cast (N.calendarGridState initial T U K omega l).total_jobs]
    exact div_self (by positivity)

private theorem calendarGridAllocation_incompatible
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    N.calendarGridAllocation initial T U K omega l i j k = 0 := by
  unfold calendarGridAllocation
  exact runAllocationCount_incompatible N _ _ _ _ _ _ hij

private theorem calendarGridAllocation_le_input
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    N.calendarGridAllocation initial T U K omega l i j k <=
      N.calendarGridInput T K omega l j k := by
  unfold calendarGridAllocation calendarGridInput
  exact runAllocationCount_le_count N _ _ _ _ _ _

private theorem calendarGrid_balance
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat) (i : Buffer) :
    (N.calendarGridState initial T U K omega l i : Real) / (K : Nat) =
      (initial K i : Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          (N.calendarGridAllocation initial T U K omega l q j i : Real) /
            (K : Nat)) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (N.calendarGridAllocation initial T U K omega l i j k : Real) /
            (K : Nat)) := by
  have h := runTokens_runAllocationCount_balance N (U K)
    (initial K) (N.calendarGridPrefix T K omega l) i
  unfold calendarGridState calendarGridAllocation
  have hK : ((K : Nat) : Real) ≠ 0 := by positivity
  push_cast at h
  simp_rw [← Finset.sum_div]
  field_simp [hK]
  linarith

private theorem calendarPolygonalState_in_simplex
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    IsFluidState (N.calendarPolygonalState initial T U K omega t) := by
  exact fi_polygonal_state_simplex K _ hT ht
    (fun l _ => calendarGridState_isFluidState N initial T U K omega l)

private theorem calendarPolygonalAllocation_incompatible
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (t : Real)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    N.calendarPolygonalAllocation initial T U K omega t i j k = 0 := by
  unfold calendarPolygonalAllocation
  apply fi_polygonal_allocation_incompatible
    (e := fun l i j k =>
      (N.calendarGridAllocation initial T U K omega l i j k : Real) / (K : Nat))
  intro l hl
  rw [calendarGridAllocation_incompatible N initial T U K omega l i j k hij]
  simp

private theorem calendarPolygonalState_initial
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    N.calendarPolygonalState initial T U K omega 0 i =
      (initial K i : Real) / (K : Nat) := by
  rw [calendarPolygonalState, fi_polygonal_initial K _ T hT]
  unfold calendarGridState calendarGridPrefix
  rw [calendarGridTime_zero, totalCalendarTokenPrefix_zero N]
  simp [runTokens]

private theorem calendarPolygonalAllocation_initial
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (i : Buffer) (j : Server) (k : Buffer) :
    N.calendarPolygonalAllocation initial T U K omega 0 i j k = 0 := by
  rw [calendarPolygonalAllocation, fi_polygonal_initial K _ T hT]
  unfold calendarGridAllocation calendarGridPrefix
  rw [calendarGridTime_zero, totalCalendarTokenPrefix_zero N]
  simp [runAllocationCount]

private theorem calendarPolygonal_balance
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) (i : Buffer) :
    N.calendarPolygonalState initial T U K omega t i =
      (initial K i : Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          N.calendarPolygonalAllocation initial T U K omega t q j i) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          N.calendarPolygonalAllocation initial T U K omega t i j k) := by
  unfold calendarPolygonalState calendarPolygonalAllocation
  change
    fi_polygonalStatePath K
        (fun l i =>
          (N.calendarGridState initial T U K omega l i : Real) / (K : Nat))
        T t i =
      (initial K i : Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          fi_polygonalAllocationPath K
            (fun l i j k =>
              (N.calendarGridAllocation initial T U K omega l i j k : Real) /
                (K : Nat))
            T t q j i) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          fi_polygonalAllocationPath K
            (fun l i j k =>
              (N.calendarGridAllocation initial T U K omega l i j k : Real) /
                (K : Nat))
            T t i j k)
  exact fi_polygonal_paths_balance
    (K := K)
    (x := fun l i =>
      (N.calendarGridState initial T U K omega l i : Real) / (K : Nat))
    (e := fun l i j k =>
      (N.calendarGridAllocation initial T U K omega l i j k : Real) / (K : Nat))
    (x0 := fun i => (initial K i : Real) / (K : Nat))
    hT ht (fun l _ i => calendarGrid_balance N initial T U K omega l i) i

private def calendarIntervalBatch
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (s t : Real) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  (N.totalCalendarTokenPrefix K omega t).drop
    (N.totalCalendarTokenPrefix K omega s).length

private theorem calendarTokenPrefix_interval
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t) :
    N.totalCalendarTokenPrefix K omega t =
      N.totalCalendarTokenPrefix K omega s ++
        N.calendarIntervalBatch K omega s t := by
  unfold calendarIntervalBatch
  obtain ⟨suffix, hsuffix⟩ :=
    N.totalCalendarTokenPrefix_append K omega hst
  rw [hsuffix, List.drop_left]

private theorem calendarIntervalBatch_count
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t)
    (j : Server) (k : Buffer) :
    (N.calendarIntervalBatch K omega s t).count (j, k) =
      (N.totalCalendarTokenPrefix K omega t).count (j, k) -
        (N.totalCalendarTokenPrefix K omega s).count (j, k) := by
  rw [calendarTokenPrefix_interval N K omega hst, List.count_append,
    Nat.add_sub_cancel_left]

private theorem calendarIntervalBatch_length
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t) :
    (N.calendarIntervalBatch K omega s t).length =
      (N.totalCalendarTokenPrefix K omega t).length -
        (N.totalCalendarTokenPrefix K omega s).length := by
  unfold calendarIntervalBatch
  rw [List.length_drop]

private theorem calendarScaledInput_mono
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t)
    (j : Server) (k : Buffer) :
    N.totalCalendarScaledInput K omega s j k <=
      N.totalCalendarScaledInput K omega t j k := by
  rw [calendarScaledInput_eq_prefix_count N,
    calendarScaledInput_eq_prefix_count N]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    (show
      (N.totalCalendarTokenPrefix K omega s).count (j, k) <=
        (N.totalCalendarTokenPrefix K omega t).count (j, k) by
      rw [calendarTokenPrefix_interval N K omega hst, List.count_append]
      omega)

private theorem calendarIntervalBatch_scaled_length
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t) :
    ((N.calendarIntervalBatch K omega s t).length : Real) / (K : Nat) =
      Finset.univ.sum (fun jk : Server × Buffer =>
        N.totalCalendarScaledInput K omega t jk.1 jk.2 -
          N.totalCalendarScaledInput K omega s jk.1 jk.2) := by
  rw [show
    (N.calendarIntervalBatch K omega s t).length =
      Finset.univ.sum (fun jk : Server × Buffer =>
        (N.calendarIntervalBatch K omega s t).count jk) by
    exact (allTokenCounts_sum (Buffer := Buffer) (Server := Server)
      (N.calendarIntervalBatch K omega s t)).symm]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro jk hjk
  rw [calendarScaledInput_eq_prefix_count N,
    calendarScaledInput_eq_prefix_count N,
    calendarIntervalBatch_count N K omega hst]
  have hle :
      (N.totalCalendarTokenPrefix K omega s).count jk <=
        (N.totalCalendarTokenPrefix K omega t).count jk := by
    rw [calendarTokenPrefix_interval N K omega hst, List.count_append]
    omega
  push_cast
  rw [Nat.cast_sub hle]
  ring

private theorem calendarScaledQueueStateFromInitial_ordered_dist_le
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t)
    (i : Buffer) :
    dist (N.calendarScaledQueueStateFromInitial initial U K omega s i)
        (N.calendarScaledQueueStateFromInitial initial U K omega t i) <=
      2 * Finset.univ.sum (fun jk : Server × Buffer =>
        (N.totalCalendarScaledInput K omega t jk.1 jk.2 -
          N.totalCalendarScaledInput K omega s jk.1 jk.2)) := by
  have hrun :=
    runTokens_batch_l1_le_two_mul_length N (U K)
      (initial K)
      (N.totalCalendarTokenPrefix K omega s)
      (N.calendarIntervalBatch K omega s t)
  rw [<- calendarTokenPrefix_interval N K omega hst] at hrun
  have hcoord :
      abs (((N.runTokens (U K) (initial K)
          (N.totalCalendarTokenPrefix K omega t) i : Nat) :
            Real) -
        ((N.runTokens (U K) (initial K)
          (N.totalCalendarTokenPrefix K omega s) i : Nat) :
            Real)) <=
        2 * (N.calendarIntervalBatch K omega s t).length := by
    exact (Finset.single_le_sum
      (fun q _ => abs_nonneg
        (((N.runTokens (U K) (initial K)
            (N.totalCalendarTokenPrefix K omega t) q : Nat) :
              Real) -
          ((N.runTokens (U K) (initial K)
            (N.totalCalendarTokenPrefix K omega s) q : Nat) :
              Real)))
      (Finset.mem_univ i)).trans hrun
  unfold calendarScaledQueueStateFromInitial
    totalCalendarScaledQueueStateFrom
  rw [Real.dist_eq]
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [<- sub_div, abs_div, abs_of_pos hK]
  calc
    abs
          (((N.runTokens (U K) (initial K)
              (N.totalCalendarTokenPrefix K omega s) i :
                Nat) : Real) -
            ((N.runTokens (U K) (initial K)
              (N.totalCalendarTokenPrefix K omega t) i :
                Nat) : Real)) /
        (K : Nat) <=
        (2 * (N.calendarIntervalBatch K omega s t).length : Real) /
          (K : Nat) := by
      apply div_le_div_of_nonneg_right _ hK.le
      simpa [abs_sub_comm] using hcoord
    _ = 2 * Finset.univ.sum (fun jk : Server × Buffer =>
          (N.totalCalendarScaledInput K omega t jk.1 jk.2 -
            N.totalCalendarScaledInput K omega s jk.1 jk.2)) := by
      rw [show
        (2 * (N.calendarIntervalBatch K omega s t).length : Real) /
            (K : Nat) =
          2 * (((N.calendarIntervalBatch K omega s t).length : Real) /
            (K : Nat)) by ring]
      rw [calendarIntervalBatch_scaled_length N K omega hst]

private theorem calendarScaledQueueStateFromInitial_dist_le
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (s t : Real) (i : Buffer) :
    dist (N.calendarScaledQueueStateFromInitial initial U K omega s i)
        (N.calendarScaledQueueStateFromInitial initial U K omega t i) <=
      2 * Finset.univ.sum (fun jk : Server × Buffer =>
        dist (N.totalCalendarScaledInput K omega s jk.1 jk.2)
          (N.totalCalendarScaledInput K omega t jk.1 jk.2)) := by
  rcases le_total s t with hst | hts
  · have h := calendarScaledQueueStateFromInitial_ordered_dist_le N initial U K omega hst i
    convert h using 1
    apply congrArg
    apply Finset.sum_congr rfl
    intro jk hjk
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (calendarScaledInput_mono N K omega hst jk.1 jk.2))]
  · rw [dist_comm]
    have h := calendarScaledQueueStateFromInitial_ordered_dist_le N initial U K omega hts i
    convert h using 1
    apply congrArg
    apply Finset.sum_congr rfl
    intro jk hjk
    rw [Real.dist_eq, abs_of_nonneg
      (sub_nonneg.mpr (calendarScaledInput_mono N K omega hts jk.1 jk.2))]

private theorem calendarScaledAllocationFromInitial_ordered_increment
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t)
    (i : Buffer) (j : Server) (k : Buffer) :
    0 <= N.calendarScaledAllocationFromInitial initial U K omega t i j k -
        N.calendarScaledAllocationFromInitial initial U K omega s i j k /\
      N.calendarScaledAllocationFromInitial initial U K omega t i j k -
          N.calendarScaledAllocationFromInitial initial U K omega s i j k <=
        N.totalCalendarScaledInput K omega t j k -
          N.totalCalendarScaledInput K omega s j k := by
  have happend :=
    runAllocationCount_append N (U K) (initial K)
      (N.totalCalendarTokenPrefix K omega s)
      (N.calendarIntervalBatch K omega s t) i j k
  rw [<- calendarTokenPrefix_interval N K omega hst] at happend
  have hle :=
    runAllocationCount_le_count N (U K)
      (N.runTokens (U K) (initial K)
        (N.totalCalendarTokenPrefix K omega s))
      (N.calendarIntervalBatch K omega s t) i j k
  unfold calendarScaledAllocationFromInitial
    totalCalendarScaledAllocationFrom
  have hK : (0 : Real) < (K : Nat) := by positivity
  constructor
  · apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ hK.le
    exact_mod_cast (show
      N.runAllocationCount (U K) (initial K)
          (N.totalCalendarTokenPrefix K omega s) i j k <=
        N.runAllocationCount (U K) (initial K)
          (N.totalCalendarTokenPrefix K omega t) i j k by
      omega)
  · rw [calendarScaledInput_eq_prefix_count N,
      calendarScaledInput_eq_prefix_count N]
    have halloc_le :
        N.runAllocationCount (U K) (initial K)
            (N.totalCalendarTokenPrefix K omega s) i j k <=
          N.runAllocationCount (U K) (initial K)
            (N.totalCalendarTokenPrefix K omega t) i j k := by
      omega
    have hcount_le :
        (N.totalCalendarTokenPrefix K omega s).count (j, k) <=
          (N.totalCalendarTokenPrefix K omega t).count (j, k) := by
      rw [calendarTokenPrefix_interval N K omega hst, List.count_append]
      omega
    have hnat :
        N.runAllocationCount (U K) (initial K)
              (N.totalCalendarTokenPrefix K omega t) i j k -
            N.runAllocationCount (U K) (initial K)
              (N.totalCalendarTokenPrefix K omega s) i j k <=
          (N.totalCalendarTokenPrefix K omega t).count (j, k) -
            (N.totalCalendarTokenPrefix K omega s).count
              (j, k) := by
      rw [calendarIntervalBatch_count N K omega hst] at hle
      omega
    rw [<- sub_div, <- sub_div]
    apply div_le_div_of_nonneg_right _ hK.le
    rw [← Nat.cast_sub halloc_le, ← Nat.cast_sub hcount_le]
    exact_mod_cast hnat

private theorem calendarScaledAllocationFromInitial_dist_le
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (s t : Real)
    (i : Buffer) (j : Server) (k : Buffer) :
    dist (N.calendarScaledAllocationFromInitial initial U K omega s i j k)
        (N.calendarScaledAllocationFromInitial initial U K omega t i j k) <=
      dist (N.totalCalendarScaledInput K omega s j k)
        (N.totalCalendarScaledInput K omega t j k) := by
  rcases le_total s t with hst | hts
  · have h := calendarScaledAllocationFromInitial_ordered_increment N initial U K omega hst i j k
    rw [Real.dist_eq, Real.dist_eq]
    rw [abs_sub_comm, abs_of_nonneg h.1]
    rw [abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (calendarScaledInput_mono N K omega hst j k))]
    exact h.2
  · rw [dist_comm, dist_comm
      (N.totalCalendarScaledInput K omega s j k)]
    have h := calendarScaledAllocationFromInitial_ordered_increment N initial U K omega hts i j k
    rw [Real.dist_eq, Real.dist_eq]
    rw [abs_sub_comm, abs_of_nonneg h.1]
    rw [abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (calendarScaledInput_mono N K omega hts j k))]
    exact h.2

private theorem calendarStateLimit_continuousOn
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall i, ContinuousOn (fun t => X t i) (Icc (0 : Real) T) := by
  have hinput := hconverges.1
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  change UniformlyOnIcc T
      (fun r t i => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
      X at hstate
  let Avec : Real -> (Server × Buffer -> Real) :=
    fun t jk => A t jk.1 jk.2
  have hAvec_cont : ContinuousOn Avec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro jk
    simpa [Avec, uIcc_of_le hT.le] using
      (hA jk.1 jk.2).continuousOn
  have hAvec_uc : UniformContinuousOn Avec (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hAvec_cont
  intro i
  apply UniformContinuousOn.continuousOn
  rw [Metric.uniformContinuousOn_iff]
  intro epsilon hepsilon
  let C : Real := (Fintype.card (Server × Buffer) : Real) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let eta : Real := epsilon / (16 * C)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp hAvec_uc eta heta
  obtain ⟨rInput, hrInput⟩ := hinput eta heta
  obtain ⟨rState, hrState⟩ := hstate (epsilon / 8) (by positivity)
  refine ⟨delta, hdelta, fun s hs t ht hst => ?_⟩
  let r := max rInput rState
  have hrI : rInput <= r := le_max_left _ _
  have hrS : rState <= r := le_max_right _ _
  have hsState :
      dist (X s i) (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i) <
        epsilon / 8 := by
    rw [Real.dist_eq, abs_sub_comm]
    exact hrState r hrS s hs i
  have htState :
      dist (N.calendarScaledQueueStateFromInitial initial U (K r) omega t i) (X t i) <
        epsilon / 8 := by
    rw [Real.dist_eq]
    exact hrState r hrS t ht i
  have hAmetric : dist (Avec s) (Avec t) < eta :=
    hdeltaWorks s hs t ht hst
  have hterm (jk : Server × Buffer) :
      dist (N.totalCalendarScaledInput (K r) omega s jk.1 jk.2)
          (N.totalCalendarScaledInput (K r) omega t jk.1 jk.2) <
        3 * eta := by
    have hsInput := hrInput r hrI s hs jk
    have htInput := hrInput r hrI t ht jk
    have hcoord :
        dist (Avec s jk) (Avec t jk) <= dist (Avec s) (Avec t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s) (Avec t) <= dist (Avec s) (Avec t)) jk
    rw [Real.dist_eq]
    calc
      abs (N.totalCalendarScaledInput (K r) omega s jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) omega t jk.1 jk.2) <=
          abs (N.totalCalendarScaledInput (K r) omega s jk.1 jk.2 -
            A s jk.1 jk.2) +
          abs (A s jk.1 jk.2 - A t jk.1 jk.2) +
          abs (A t jk.1 jk.2 -
            N.totalCalendarScaledInput (K r) omega t jk.1 jk.2) := by
        calc
          _ <= abs (N.totalCalendarScaledInput (K r) omega s jk.1 jk.2 -
                A s jk.1 jk.2) +
              abs (A s jk.1 jk.2 -
                N.totalCalendarScaledInput (K r) omega t jk.1 jk.2) :=
            abs_sub_le _ _ _
          _ <= _ := by
            have htri :=
              abs_sub_le (A s jk.1 jk.2) (A t jk.1 jk.2)
                (N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)
            linarith
      _ < eta + eta + eta := by
        have hcoord' :
            abs (A s jk.1 jk.2 - A t jk.1 jk.2) < eta := by
          simpa [Avec, Real.dist_eq] using hcoord.trans_lt hAmetric
        have htInput' :
            abs (A t jk.1 jk.2 -
              N.totalCalendarScaledInput (K r) omega t jk.1 jk.2) < eta := by
          simpa [abs_sub_comm] using htInput
        gcongr
      _ = 3 * eta := by ring
  have hraw :=
    calendarScaledQueueStateFromInitial_dist_le N initial U (K r) omega s t i
  have hsum :
      Finset.univ.sum (fun jk : Server × Buffer =>
        dist (N.totalCalendarScaledInput (K r) omega s jk.1 jk.2)
          (N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)) <
        (Fintype.card (Server × Buffer) : Real) * (3 * eta) := by
    calc
      _ < Finset.univ.sum (fun _ : Server × Buffer => 3 * eta) :=
        Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty : (Finset.univ :
            Finset (Server × Buffer)).Nonempty)
          (fun jk _ => hterm jk)
      _ = _ := by simp
  calc
    dist (X s i) (X t i) <=
        dist (X s i) (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i) +
        dist (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i)
          (N.calendarScaledQueueStateFromInitial initial U (K r) omega t i) +
        dist (N.calendarScaledQueueStateFromInitial initial U (K r) omega t i) (X t i) := by
      calc
        _ <= dist (X s i) (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i) +
            dist (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i) (X t i) :=
          dist_triangle _ _ _
        _ <= _ := by
          have htri :=
            dist_triangle
              (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i)
              (N.calendarScaledQueueStateFromInitial initial U (K r) omega t i) (X t i)
          linarith
    _ < epsilon / 8 +
        2 * ((Fintype.card (Server × Buffer) : Real) * (3 * eta)) +
        epsilon / 8 := by
      gcongr
      exact hraw.trans_lt (mul_lt_mul_of_pos_left hsum (by positivity))
    _ < epsilon := by
      dsimp [eta, C]
      have hcard : 0 <= (Fintype.card (Server × Buffer) : Real) := by
        positivity
      have hcardC :
          (Fintype.card (Server × Buffer) : Real) <
            (Fintype.card (Server × Buffer) : Real) + 1 := by linarith
      have hratio :
          (Fintype.card (Server × Buffer) : Real) /
              ((Fintype.card (Server × Buffer) : Real) + 1) < 1 := by
        exact (div_lt_one (by linarith)).2 hcardC
      field_simp
      nlinarith

private theorem calendarGridTime_eq_ffGridTime
    (T : Real) (K : PNat) {l : Nat} (hl : l <= (K : Nat)) :
    calendarGridTime T K l = gridTime T K l := by
  simp [calendarGridTime, gridTime, min_eq_left hl]

private theorem polygonalInterpolate_error_of_nodes
    {T : Real} (hT : 0 < T) (K : PNat)
    (values : Nat -> Real) (g : Real -> Real)
    (delta eta : Real)
    (hnode : forall l, l <= (K : Nat) ->
      abs (values l - g (calendarGridTime T K l)) <= delta)
    (hosc : forall s, s ∈ Icc (0 : Real) T ->
      forall t, t ∈ Icc (0 : Real) T ->
        abs (s - t) <= T / (K : Nat) ->
        abs (g s - g t) <= eta)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    abs (polygonalInterpolate K values t T - g t) <= delta + eta := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) ht.1) hT.le
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hsum :
      Finset.sum (Finset.range ((K : Nat) + 1)) (hatWeight r) = 1 :=
    sum_hatWeight_eq_one K hr0 hrK
  have hterm (l : Nat) (hl : l ∈ Finset.range ((K : Nat) + 1)) :
      abs (hatWeight r l * (values l - g t)) <=
        hatWeight r l * (delta + eta) := by
    by_cases hw : hatWeight r l = 0
    · simp [hw]
    · rw [abs_mul, abs_of_nonneg (hatWeight_nonnegative r l)]
      apply mul_le_mul_of_nonneg_left _ (hatWeight_nonnegative r l)
      have hlK : l <= (K : Nat) := by
        have := Finset.mem_range.mp hl
        omega
      have hdistFF :=
        hatWeight_ne_zero_distance K hT (Finset.mem_range.mp hl) hw
      have hdist :
          abs (calendarGridTime T K l - t) <= T / (K : Nat) := by
        rw [calendarGridTime_eq_ffGridTime T K hlK]
        exact hdistFF
      have hosc' := hosc (calendarGridTime T K l)
        (calendarGridTime_mem_Icc hT K hlK) t ht hdist
      calc
        abs (values l - g t) <=
            abs (values l - g (calendarGridTime T K l)) +
              abs (g (calendarGridTime T K l) - g t) := abs_sub_le _ _ _
        _ <= delta + eta := add_le_add (hnode l hlK) hosc'
  rw [show polygonalInterpolate K values t T - g t =
      Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
        hatWeight r l * (values l - g t)) by
    unfold polygonalInterpolate
    dsimp [r]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, <- Finset.sum_mul, hsum, one_mul]]
  calc
    abs (Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
        hatWeight r l * (values l - g t))) <=
        Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
          abs (hatWeight r l * (values l - g t))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
          hatWeight r l * (delta + eta)) :=
      Finset.sum_le_sum hterm
    _ = delta + eta := by
      rw [<- Finset.sum_mul, hsum, one_mul]

private theorem polygonal_converges_of_nodes
    {T : Real} (hT : 0 < T)
    (K : Nat -> PNat) (hK : StrictMono K)
    (values : Nat -> Nat -> Real) (g : Real -> Real)
    (hg : ContinuousOn g (Icc (0 : Real) T))
    (hnode : forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall l, l <= (K r : Nat) ->
          abs (values r l - g (calendarGridTime T (K r) l)) < epsilon) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall t, t ∈ Icc (0 : Real) T ->
          abs (polygonalInterpolate (K r) (values r) t T - g t) <
            epsilon := by
  have huc : UniformContinuousOn g (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  have hKreal :
      Tendsto (fun r => (((K r : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun r => T / (((K r : Nat) : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp huc (epsilon / 3) (by positivity)
  obtain ⟨rMesh, hrMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh delta hdelta
  obtain ⟨rNode, hrNode⟩ := hnode (epsilon / 3) (by positivity)
  refine ⟨max rMesh rNode, fun r hr t ht => ?_⟩
  have hrM : rMesh <= r := (le_max_left _ _).trans hr
  have hrN : rNode <= r := (le_max_right _ _).trans hr
  have hmeshSmall : T / (((K r : Nat) : Real)) < delta := by
    have h := hrMesh r hrM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at h
    exact h
  have hosc :
      forall s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T ->
          abs (s - t) <= T / (K r : Nat) ->
          abs (g s - g t) <= epsilon / 3 := by
    intro s hs t ht' hst
    have hdist : dist s t < delta := by
      rw [Real.dist_eq]
      exact hst.trans_lt hmeshSmall
    have h := hdeltaWorks s hs t ht' hdist
    simpa [Real.dist_eq] using le_of_lt h
  have herr :=
    polygonalInterpolate_error_of_nodes hT (K r) (values r) g
      (epsilon / 3) (epsilon / 3)
      (fun l hl => le_of_lt (hrNode r hrN l hl)) hosc t ht
  exact herr.trans_lt (by linarith)

private theorem exists_common_nat_bound
    {I : Type*} [Fintype I]
    {P : I -> Nat -> Prop}
    (h : forall i, exists n0, forall n, n0 <= n -> P i n) :
    exists n0, forall n, n0 <= n -> forall i, P i n := by
  classical
  choose bound hbound using h
  refine ⟨Finset.univ.sup bound, fun n hn i => hbound i n ?_⟩
  exact (Finset.le_sup (Finset.mem_univ i)).trans hn

private theorem calendarPolygonalInput_converges
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall jk : Server × Buffer, forall t, t ∈ Icc (0 : Real) T ->
          dist (N.calendarPolygonalInput T (K r) omega t jk.1 jk.2)
            (A t jk.1 jk.2) < epsilon := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  intro epsilon hepsilon
  have hcoord (jk : Server × Buffer) :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall t, t ∈ Icc (0 : Real) T ->
            abs (N.calendarPolygonalInput T (K r) omega t jk.1 jk.2 -
              A t jk.1 jk.2) < epsilon := by
    apply polygonal_converges_of_nodes hT K hK
      (fun r l =>
        (N.calendarGridInput T (K r) omega l jk.1 jk.2 : Real) /
          (K r : Nat))
      (fun t => A t jk.1 jk.2)
    · simpa [uIcc_of_le hT.le] using (hA jk.1 jk.2).continuousOn
    · intro eta heta
      obtain ⟨r0, hr0⟩ := hinput eta heta
      refine ⟨r0, fun r hr l hl => ?_⟩
      have hnode := hr0 r hr (calendarGridTime T (K r) l)
        (calendarGridTime_mem_Icc hT (K r) hl) jk
      change
        abs (N.totalCalendarScaledInput (K r) omega
          (calendarGridTime T (K r) l) jk.1 jk.2 -
            A (calendarGridTime T (K r) l) jk.1 jk.2) < eta at hnode
      rw [calendarScaledInput_eq_prefix_count N] at hnode
      simpa only [calendarGridInput, calendarGridPrefix] using hnode
  obtain ⟨r0, hr0⟩ :=
    exists_common_nat_bound (P := fun jk : Server × Buffer => fun r =>
        forall t, t ∈ Icc (0 : Real) T ->
          abs (N.calendarPolygonalInput T (K r) omega t jk.1 jk.2 -
            A t jk.1 jk.2) < epsilon)
      (fun jk => hcoord jk epsilon hepsilon)
  refine ⟨r0, fun r hr jk t ht => ?_⟩
  rw [Real.dist_eq]
  exact hr0 r hr jk t ht

private theorem calendarPolygonalState_converges
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall i : Buffer, forall t, t ∈ Icc (0 : Real) T ->
          dist (N.calendarPolygonalState initial T U (K r) omega t i)
            (X t i) < epsilon := by
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t i => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
      X at hstate
  have hXcont :=
    calendarStateLimit_continuousOn N initial hT U K omega A X hA hconverges
  intro epsilon hepsilon
  have hcoord (i : Buffer) :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall t, t ∈ Icc (0 : Real) T ->
            abs (N.calendarPolygonalState initial T U (K r) omega t i -
              X t i) < epsilon := by
    apply polygonal_converges_of_nodes hT K hK
      (fun r l =>
        (N.calendarGridState initial T U (K r) omega l i : Real) / (K r : Nat))
      (fun t => X t i) (hXcont i)
    intro eta heta
    obtain ⟨r0, hr0⟩ := hstate eta heta
    refine ⟨r0, fun r hr l hl => ?_⟩
    exact hr0 r hr (calendarGridTime T (K r) l)
      (calendarGridTime_mem_Icc hT (K r) hl) i
  obtain ⟨r0, hr0⟩ :=
    exists_common_nat_bound (P := fun i : Buffer => fun r =>
        forall t, t ∈ Icc (0 : Real) T ->
          abs (N.calendarPolygonalState initial T U (K r) omega t i -
            X t i) < epsilon)
      (fun i => hcoord i epsilon hepsilon)
  refine ⟨r0, fun r hr i t ht => ?_⟩
  rw [Real.dist_eq]
  exact hr0 r hr i t ht

private theorem calendarGridAllocation_step_le
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    abs
        ((N.calendarGridAllocation initial T U K omega (l + 1) i j k : Real) /
            (K : Nat) -
          (N.calendarGridAllocation initial T U K omega l i j k : Real) /
            (K : Nat)) <=
      Finset.univ.sum (fun jk : Server × Buffer =>
        (N.calendarGridInput T K omega (l + 1) jk.1 jk.2 : Real) /
            (K : Nat) -
          (N.calendarGridInput T K omega l jk.1 jk.2 : Real) /
            (K : Nat)) := by
  have happend :=
    calendarGridAllocation_succ N initial hT U K omega l i j k
  have htail :=
    runAllocationCount_le_count N (U K)
      (N.calendarGridState initial T U K omega l)
      (N.calendarGridBatch T K omega l) i j k
  have hmono :
      N.calendarGridAllocation initial T U K omega l i j k <=
        N.calendarGridAllocation initial T U K omega (l + 1) i j k := by
    omega
  have hdiff :
      N.calendarGridAllocation initial T U K omega (l + 1) i j k -
          N.calendarGridAllocation initial T U K omega l i j k <=
        (N.calendarGridBatch T K omega l).length := by
    have htailLength := htail.trans List.count_le_length
    omega
  have hsum :=
    calendarGridBatch_length_eq_input_sum N hT K omega l
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [abs_of_nonneg (sub_nonneg.mpr
    (div_le_div_of_nonneg_right (by exact_mod_cast hmono) hK.le))]
  rw [<- sub_div]
  simp_rw [<- sub_div]
  rw [<- Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hK.le
  rw [← Nat.cast_sub hmono]
  conv_rhs =>
    enter [2, jk]
    rw [← Nat.cast_sub
      (calendarGridInput_mono N hT K omega (Nat.le_succ l) jk.1 jk.2)]
  rw [← Nat.cast_sum]
  exact_mod_cast hdiff.trans_eq hsum

private theorem calendarPolygonalAllocation_increment_domination
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (i : Buffer) (j : Server) (k : Buffer)
    {s t : Real} (hs : s ∈ Icc (0 : Real) T)
    (ht : t ∈ Icc (0 : Real) T) :
    dist (N.calendarPolygonalAllocation initial T U K omega s i j k)
        (N.calendarPolygonalAllocation initial T U K omega t i j k) <=
      Finset.univ.sum (fun jk : Server × Buffer =>
        dist (N.calendarPolygonalInput T K omega s jk.1 jk.2)
          (N.calendarPolygonalInput T K omega t jk.1 jk.2)) := by
  let values : Nat -> Real := fun l =>
    (N.calendarGridAllocation initial T U K omega l i j k : Real) / (K : Nat)
  let control : Server × Buffer -> Nat -> Real := fun jk l =>
    (N.calendarGridInput T K omega l jk.1 jk.2 : Real) / (K : Nat)
  change
    dist (polygonalInterpolate K values s T)
        (polygonalInterpolate K values t T) <=
      Finset.univ.sum (fun jk : Server × Buffer =>
        dist (polygonalInterpolate K (control jk) s T)
          (polygonalInterpolate K (control jk) t T))
  have hcontrol : forall jk l, l < (K : Nat) ->
      control jk l <= control jk (l + 1) := by
    intro jk l hl
    dsimp [control]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast calendarGridInput_mono N hT K omega
      (Nat.le_succ l) jk.1 jk.2
  have hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun jk =>
          control jk (l + 1) - control jk l) := by
    intro l hl
    exact calendarGridAllocation_step_le N initial hT U K omega l i j k
  exact polygonal_increment_domination K values control hT hs ht
    hcontrol hstep

private theorem calendarGridAllocation_scaled_le_input
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    (N.calendarGridAllocation initial T U K omega l i j k : Real) /
        (K : Nat) <=
      (N.calendarGridInput T K omega l j k : Real) / (K : Nat) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    calendarGridAllocation_le_input N initial T U K omega l i j k

private theorem calendarPolygonalAllocation_abs_le_input
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (i : Buffer) (j : Server) (k : Buffer)
    {t : Real} (ht : t ∈ Icc (0 : Real) T) :
    abs (N.calendarPolygonalAllocation initial T U K omega t i j k) <=
      N.calendarPolygonalInput T K omega t j k := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) ht.1) hT.le
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hnonneg :
      0 <= N.calendarPolygonalAllocation initial T U K omega t i j k := by
    unfold calendarPolygonalAllocation polygonalInterpolate
    apply Finset.sum_nonneg
    intro l hl
    exact mul_nonneg (hatWeight_nonnegative _ _)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [abs_of_nonneg hnonneg]
  unfold calendarPolygonalAllocation calendarPolygonalInput
    polygonalInterpolate
  change
    Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
      hatWeight r l *
        (((N.calendarGridAllocation initial T U K omega l i j k : Nat) : Real) /
          (K : Nat))) <=
      Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
        hatWeight r l *
          ((N.calendarGridInput T K omega l j k : Real) / (K : Nat)))
  apply Finset.sum_le_sum
  intro l hl
  exact mul_le_mul_of_nonneg_left
    (calendarGridAllocation_scaled_le_input N initial T U K omega
      l i j k)
    (hatWeight_nonnegative r l)

private theorem exists_calendarPolygonalAllocation_limit
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X) :
    exists q : Nat -> Nat, StrictMono q /\
      exists E : FluidAllocationPath Buffer Server,
        (forall i j k, ContinuousOn (fun t => E t i j k)
          (Icc (0 : Real) T)) /\
        (forall epsilon, 0 < epsilon ->
          exists r0, forall r, r0 <= r ->
            forall i j k t, t ∈ Icc (0 : Real) T ->
              dist
                (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
                (E t i j k) < epsilon) := by
  let f : Nat -> (Buffer × Server × Buffer) -> Real -> Real :=
    fun r ijk t =>
      N.calendarPolygonalAllocation initial T U (K r) omega t
        ijk.1 ijk.2.1 ijk.2.2
  let g : Nat -> (Server × Buffer) -> Real -> Real :=
    fun r jk t => N.calendarPolygonalInput T (K r) omega t jk.1 jk.2
  let control : (Server × Buffer) -> Real -> Real :=
    fun jk t => A t jk.1 jk.2
  have hf :
      forall r ijk, ContinuousOn (f r ijk) (Icc (0 : Real) T) := by
    intro r ijk
    exact (continuous_calendarPolygonalAllocation N initial T U (K r) omega
      ijk.1 ijk.2.1 ijk.2.2).continuousOn
  have hcontrol :
      forall jk, ContinuousOn (control jk) (Icc (0 : Real) T) := by
    intro jk
    simpa [control, uIcc_of_le hT.le] using
      (hA jk.1 jk.2).continuousOn
  have hgconv :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall jk t, t ∈ Icc (0 : Real) T ->
            dist (g r jk t) (control jk t) < epsilon := by
    intro epsilon hepsilon
    simpa [g, control] using
      calendarPolygonalInput_converges N initial hT U K hK omega A X hA
        hconverges epsilon hepsilon
  obtain ⟨rStart, hrStart⟩ := hgconv 1 (by norm_num)
  have hcontrolBound (jk : Server × Buffer) :
      exists C : Real, forall t, t ∈ Icc (0 : Real) T ->
        abs (control jk t) <= C := by
    obtain ⟨C, hC⟩ :=
      isCompact_Icc.bddAbove_image (hcontrol jk).abs
    refine ⟨C, fun t ht => hC ?_⟩
    exact mem_image_of_mem (fun s => abs (control jk s)) ht
  choose C hC using hcontrolBound
  let M : Real :=
    Finset.univ.sum (fun jk : Server × Buffer => max (C jk) 0 + 1)
  have hcoordBound (jk : Server × Buffer) :
      max (C jk) 0 + 1 <= M := by
    dsimp [M]
    exact Finset.single_le_sum
      (f := fun b : Server × Buffer => max (C b) 0 + 1)
      (fun b _ => by positivity) (Finset.mem_univ jk)
  have hbound :
      forall r ijk t, t ∈ Icc (0 : Real) T ->
        abs (f (rStart + r) ijk t) <= M := by
    intro r ijk t ht
    let jk : Server × Buffer := (ijk.2.1, ijk.2.2)
    have hf_le :
        abs (f (rStart + r) ijk t) <= g (rStart + r) jk t := by
      exact calendarPolygonalAllocation_abs_le_input
        N initial hT U (K (rStart + r)) omega
          ijk.1 ijk.2.1 ijk.2.2 ht
    have hg := hrStart (rStart + r) (Nat.le_add_right rStart r) jk t ht
    rw [Real.dist_eq] at hg
    calc
      abs (f (rStart + r) ijk t) <= g (rStart + r) jk t := hf_le
      _ <= abs (control jk t) +
          abs (g (rStart + r) jk t - control jk t) := by
        calc
          g (rStart + r) jk t =
              control jk t +
                (g (rStart + r) jk t - control jk t) := by ring
          _ <= _ := add_le_add (le_abs_self _) (le_abs_self _)
      _ <= C jk + 1 := by
        gcongr
        exact hC jk t ht
      _ <= max (C jk) 0 + 1 := by
        gcongr
        exact le_max_left _ _
      _ <= M := hcoordBound jk
  have hdom :
      forall r ijk s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T ->
          dist (f r ijk s) (f r ijk t) <=
            Finset.univ.sum (fun jk =>
              dist (g r jk s) (g r jk t)) := by
    intro r ijk s hs t ht
    exact calendarPolygonalAllocation_increment_domination N initial hT U (K r)
      omega ijk.1 ijk.2.1 ijk.2.2 hs ht
  obtain ⟨q, hq, limit, hlimitCont, hlimitConv⟩ :=
    calendar_exists_uniformly_convergent_subsequence_finite
      (f := fun r ijk t => f (rStart + r) ijk t)
      (g := fun r jk t => g (rStart + r) jk t)
      (control := control)
      (a := (0 : Real)) (b := T) (M := M)
      (fun r => hf (rStart + r)) hbound hcontrol
      (by
        intro epsilon hepsilon
        obtain ⟨r0, hr0⟩ := hgconv epsilon hepsilon
        refine ⟨r0, fun r hr => hr0 (rStart + r) ?_⟩
        exact hr.trans (Nat.le_add_left r rStart))
      (fun r => hdom (rStart + r))
  let E : FluidAllocationPath Buffer Server :=
    fun t i j k => limit (i, j, k) t
  let q' : Nat -> Nat := fun r => rStart + q r
  have hq' : StrictMono q' := fun _ _ hrs =>
    Nat.add_lt_add_left (hq hrs) rStart
  refine ⟨q', hq', E, ?_, ?_⟩
  · intro i j k
    exact hlimitCont (i, j, k)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hlimitConv epsilon hepsilon
    refine ⟨r0, fun r hr i j k t ht => ?_⟩
    exact hr0 r hr (i, j, k) t ht

private theorem calendarPolygonalAllocation_approximates_scaled
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (N.calendarPolygonalAllocation initial T U (K r) omega t i j k)
            (N.calendarScaledAllocationFromInitial initial U (K r) omega t i j k) < epsilon := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  let Avec : Real -> (Server × Buffer -> Real) :=
    fun t jk => A t jk.1 jk.2
  have hAvecCont : ContinuousOn Avec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro jk
    simpa [Avec, uIcc_of_le hT.le] using
      (hA jk.1 jk.2).continuousOn
  have hAvecUC : UniformContinuousOn Avec (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hAvecCont
  have hKreal :
      Tendsto (fun r => (((K r : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun r => T / (((K r : Nat) : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp hAvecUC
      (epsilon / 4) (by positivity)
  obtain ⟨rMesh, hrMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh delta hdelta
  obtain ⟨rInput, hrInput⟩ := hinput (epsilon / 4) (by positivity)
  refine ⟨max rMesh rInput, fun r hr i j k t ht => ?_⟩
  have hrM : rMesh <= r := (le_max_left _ _).trans hr
  have hrI : rInput <= r := (le_max_right _ _).trans hr
  have hmeshSmall : T / (((K r : Nat) : Real)) < delta := by
    have hm := hrMesh r hrM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at hm
    exact hm
  have hosc :
      forall s, s ∈ Icc (0 : Real) T ->
        forall u, u ∈ Icc (0 : Real) T ->
          abs (s - u) <= T / (K r : Nat) ->
          abs
            (N.calendarScaledAllocationFromInitial initial U (K r) omega s i j k -
              N.calendarScaledAllocationFromInitial initial U (K r) omega u i j k) <=
            3 * (epsilon / 4) := by
    intro s hs u hu hsu
    have hAu : dist (Avec s) (Avec u) < epsilon / 4 := by
      apply hdeltaWorks s hs u hu
      rw [Real.dist_eq]
      exact hsu.trans_lt hmeshSmall
    have hcoord :
        dist (A s j k) (A u j k) <= dist (Avec s) (Avec u) := by
      exact (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s) (Avec u) <= dist (Avec s) (Avec u)) (j, k)
    have hsInput := hrInput r hrI s hs (j, k)
    have huInput := hrInput r hrI u hu (j, k)
    have htoken :
        dist (N.totalCalendarScaledInput (K r) omega s j k)
          (N.totalCalendarScaledInput (K r) omega u j k) <
            3 * (epsilon / 4) := by
      calc
        _ <= dist (N.totalCalendarScaledInput (K r) omega s j k) (A s j k) +
              dist (A s j k) (A u j k) +
              dist (A u j k)
                (N.totalCalendarScaledInput (K r) omega u j k) := by
          calc
            _ <= dist (N.totalCalendarScaledInput (K r) omega s j k) (A s j k) +
                dist (A s j k)
                  (N.totalCalendarScaledInput (K r) omega u j k) :=
              dist_triangle _ _ _
            _ <= _ := by
              have htri := dist_triangle (A s j k) (A u j k)
                (N.totalCalendarScaledInput (K r) omega u j k)
              linarith
        _ < epsilon / 4 + epsilon / 4 + epsilon / 4 := by
          have huInput' :
              dist (A u j k)
                (N.totalCalendarScaledInput (K r) omega u j k) < epsilon / 4 := by
            simpa [Real.dist_eq, abs_sub_comm] using huInput
          exact add_lt_add (add_lt_add hsInput
            (hcoord.trans_lt hAu)) huInput'
        _ = _ := by ring
    have halloc :=
      calendarScaledAllocationFromInitial_dist_le N initial U (K r) omega s u i j k
    rw [Real.dist_eq] at halloc
    exact halloc.trans (le_of_lt htoken)
  have hnode :
      forall l, l <= (K r : Nat) ->
        abs
          (((N.calendarGridAllocation initial T U (K r) omega l i j k : Real) /
              (K r : Nat)) -
            N.calendarScaledAllocationFromInitial initial U (K r) omega
              (calendarGridTime T (K r) l) i j k) <= 0 := by
    intro l hl
    have heq :
        N.calendarScaledAllocationFromInitial initial U (K r) omega
            (calendarGridTime T (K r) l) i j k =
          (N.calendarGridAllocation initial T U (K r) omega l i j k : Real) /
            (K r : Nat) := by
      rfl
    rw [heq, sub_self, abs_zero]
  have herr :=
    polygonalInterpolate_error_of_nodes hT (K r)
      (fun l =>
        (N.calendarGridAllocation initial T U (K r) omega l i j k : Real) /
          (K r : Nat))
      (fun s => N.calendarScaledAllocationFromInitial initial U (K r) omega s i j k)
      0 (3 * (epsilon / 4)) hnode hosc t ht
  rw [Real.dist_eq]
  exact herr.trans_lt (by nlinarith)

private theorem calendarInput_isFluidInput
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X) :
    IsFluidInput T A := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  have hpoint (t : Real) (ht : t ∈ Icc (0 : Real) T)
      (j : Server) (k : Buffer) :
      Tendsto (fun r => N.totalCalendarScaledInput (K r) omega t j k)
        atTop (nhds (A t j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hinput epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr t ht (j, k)⟩
  refine ⟨hA, ?_, ?_⟩
  · intro j k s hs t ht hst
    exact le_of_tendsto_of_tendsto
      (hpoint s hs j k) (hpoint t ht j k)
      (Eventually.of_forall fun r =>
        calendarScaledInput_mono N (K r) omega hst j k)
  · intro j k
    have hzero :
        (fun r => N.totalCalendarScaledInput (K r) omega 0 j k) =
          fun _ => 0 := by
      funext r
      simp [totalCalendarScaledInput, calendarScaledInput]
    apply tendsto_nhds_unique (hpoint 0 ⟨le_rfl, hT.le⟩ j k)
    rw [hzero]
    exact tendsto_const_nhds

private theorem calendarAllocation_raw_converges
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    (N.calendarPoissonExecutionFrom initial).AllocationConvergesOn T U K q omega E := by
  have happ :=
    calendarPolygonalAllocation_approximates_scaled N initial hT U K hK omega A X hA hconverges
  change UniformlyOnIcc T
      (fun r t (ijk : Buffer × Server × Buffer) =>
        N.calendarScaledAllocationFromInitial initial U (K (q r)) omega t
          ijk.1 ijk.2.1 ijk.2.2)
      (fun t ijk => E t ijk.1 ijk.2.1 ijk.2.2)
  intro epsilon hepsilon
  obtain ⟨rPoly, hrPoly⟩ := hpoly (epsilon / 2) (by positivity)
  obtain ⟨rApprox, hrApprox⟩ := happ (epsilon / 2) (by positivity)
  refine ⟨max rPoly rApprox, fun r hr t ht ijk => ?_⟩
  have hrP : rPoly <= r := (le_max_left _ _).trans hr
  have hrAq : rApprox <= q r := by
    exact (le_max_right rPoly rApprox).trans
      (hr.trans (hq.id_le r))
  have hp := hrPoly r hrP ijk.1 ijk.2.1 ijk.2.2 t ht
  have ha := hrApprox (q r) hrAq
    ijk.1 ijk.2.1 ijk.2.2 t ht
  have ha' :
      dist
          (N.calendarScaledAllocationFromInitial initial U (K (q r)) omega t
            ijk.1 ijk.2.1 ijk.2.2)
          (N.calendarPolygonalAllocation initial T U (K (q r)) omega t
            ijk.1 ijk.2.1 ijk.2.2) < epsilon / 2 := by
    simpa [dist_comm] using ha
  change
    dist
      (N.calendarScaledAllocationFromInitial initial U (K (q r)) omega t
        ijk.1 ijk.2.1 ijk.2.2)
      (E t ijk.1 ijk.2.1 ijk.2.2) < epsilon
  calc
    _ <= _ := dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add ha' hp
    _ = epsilon := by ring

private noncomputable def calendarGridPreActionStates
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) (l : Fin (K : Nat)) :
    List (JobState Buffer (K : Nat)) :=
  N.empiricalPreActionStates (U K)
    (N.calendarGridState initial T U K omega l.val)
    (N.calendarGridBatch T K omega l.val) j k

private noncomputable def calendarPolygonalAction
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) (t : Real) : ActionVector Buffer :=
  scaledBatchedPolicyActionInterpolate N K U K
    (N.calendarGridPreActionStates initial T U K omega j k) j k T t

private theorem edgeProgress_eq_ff_clamp (r : Real) (l : Nat) :
    edgeProgress r l = existenceClamp01 (r - l) := by
  unfold edgeProgress existenceClamp01
  rcases le_total (r - l) 0 with h | h
  · simp [max_eq_left h, min_eq_right (h.trans zero_le_one)]
  · by_cases h1 : r - l <= 1
    · simp [max_eq_right h, min_eq_right h1]
    · have h1' : 1 <= r - l := le_of_not_ge h1
      simp [max_eq_right h, min_eq_left h1']

private theorem existenceRampInterpolate_div
    (K : PNat) (values : Nat -> Real) (c t T : Real) :
    existenceRampInterpolate K (fun l => values l / c) t T =
      existenceRampInterpolate K values t T / c := by
  unfold existenceRampInterpolate
  rw [show
    Finset.sum (Finset.range (K : Nat)) (fun l =>
      (values (l + 1) / c - values l / c) *
        existenceClamp01 (((K : Nat) : Real) * t / T - l)) =
      (Finset.sum (Finset.range (K : Nat)) (fun l =>
        (values (l + 1) - values l) *
          existenceClamp01 (((K : Nat) : Real) * t / T - l))) / c by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l hl
    ring]
  ring

private theorem calendarGridPreActionStates_length
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) (l : Fin (K : Nat)) :
    (N.calendarGridPreActionStates initial T U K omega j k l).length =
      N.calendarGridInput T K omega (l.val + 1) j k -
        N.calendarGridInput T K omega l.val j k := by
  unfold calendarGridPreActionStates
  rw [N.empiricalPreActionStates_length]
  exact calendarGridBatch_count N hT K omega l.val j k

private theorem calendarGridPreAction_sum_some
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (l : Fin (K : Nat)) (i : Buffer) (j : Server) (k : Buffer) :
    ((N.calendarGridPreActionStates initial T U K omega j k l).map
      (fun y => N.actionDirac (U K y j k))).sum (some i) =
      (N.calendarGridAllocation initial T U K omega (l.val + 1) i j k : Real) -
        (N.calendarGridAllocation initial T U K omega l.val i j k : Real) := by
  let z := N.calendarGridState initial T U K omega l.val
  let batch := N.calendarGridBatch T K omega l.val
  have hemp := congrFun
    (N.empiricalActionCount_eq_preAction_sum
      (U K) z batch j k) (some i)
  rw [N.empiricalActionCount_some_eq_runAllocationCount] at hemp
  change
    ((N.empiricalPreActionStates (U K) z batch j k).map
      (fun y => N.actionDirac (U K y j k))).sum (some i) = _
  rw [<- hemp]
  have hsucc :=
    calendarGridAllocation_succ N initial hT U K omega l.val i j k
  dsimp [z, batch]
  rw [hsucc, Nat.cast_add]
  ring

private theorem calendarPolygonalInput_eq_batched
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    N.calendarPolygonalInput T K omega t j k =
      scaledBatchedInputInterpolate K
        (N.calendarGridPreActionStates initial T U K omega j k) T t := by
  let states := N.calendarGridPreActionStates initial T U K omega j k
  let values : Nat -> Real :=
    fun l => (N.calendarGridInput T K omega l j k : Real)
  let r : Real := ((K : Nat) : Real) * t / T
  have hbatch :
      batchedInputInterpolate states r =
        existenceRampInterpolate K values t T := by
    rw [batchedInputInterpolate_eq_cumulativeRamp states values r]
    · unfold existenceRampInterpolate
      dsimp [r]
      apply congrArg (fun x => values 0 + x)
      apply Finset.sum_congr rfl
      intro l hl
      rw [edgeProgress_eq_ff_clamp]
    · rw [show values 0 = 0 by
        simp [values, calendarGridInput, calendarGridPrefix,
          calendarGridTime_zero, totalCalendarTokenPrefix_zero N]]
    · intro l
      rw [calendarGridPreActionStates_length N initial hT U K omega j k l]
      dsimp [values]
      rw [Nat.cast_sub
        (calendarGridInput_mono N hT K omega
          (Nat.le_succ l.val) j k)]
  unfold calendarPolygonalInput scaledBatchedInputInterpolate
  rw [polygonalInterpolate_eq_ramp K _ hT ht]
  change existenceRampInterpolate K (fun l =>
      (N.calendarGridInput T K omega l j k : Real) / (K : Nat)) t T =
    batchedInputInterpolate states r / (K : Nat)
  rw [hbatch]
  exact existenceRampInterpolate_div K values (K : Nat) t T

private theorem calendarPolygonalAction_some
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (i : Buffer) (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    N.calendarPolygonalAction initial T U K omega j k t (some i) =
      N.calendarPolygonalAllocation initial T U K omega t i j k := by
  let states := N.calendarGridPreActionStates initial T U K omega j k
  let values : Nat -> Real :=
    fun l => (N.calendarGridAllocation initial T U K omega l i j k : Real)
  let r : Real := ((K : Nat) : Real) * t / T
  have hbatch :
      batchedPolicyActionInterpolate N U K states j k r (some i) =
        existenceRampInterpolate K values t T := by
    rw [batchedPolicyActionInterpolate_eq_batch_sum]
    unfold existenceRampInterpolate
    rw [show values 0 = 0 by
      simp [values, calendarGridAllocation, calendarGridPrefix,
        calendarGridTime_zero, totalCalendarTokenPrefix_zero N,
        runAllocationCount]]
    simp only [zero_add]
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro l hl
    rw [show
      Finset.univ.sum (fun q : Fin (states l).length =>
        edgeProgress r l.val *
          N.actionDirac (U K ((states l).get q) j k) (some i)) =
        (((states l).map
          (fun y => N.actionDirac (U K y j k))).sum (some i)) *
            edgeProgress r l.val by
      have hsum :
          ((states l).map
            (fun y => N.actionDirac (U K y j k))).sum =
            Finset.univ.sum (fun q : Fin (states l).length =>
              N.actionDirac (U K ((states l).get q) j k)) := by
        rw [<- List.sum_ofFn]
        change _ = (List.ofFn
          ((fun y => N.actionDirac (U K y j k)) ∘
            (states l).get)).sum
        rw [<- List.map_ofFn, List.ofFn_get]
      rw [hsum, Finset.sum_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring]
    rw [calendarGridPreAction_sum_some N initial hT U K omega l i j k]
    rw [edgeProgress_eq_ff_clamp]
  unfold calendarPolygonalAction scaledBatchedPolicyActionInterpolate
  change
    batchedPolicyActionInterpolate N U K states j k r (some i) /
        (K : Nat) =
      polygonalInterpolate K
        (fun l => (N.calendarGridAllocation initial T U K omega l i j k : Real) /
          (K : Nat)) t T
  rw [hbatch, polygonalInterpolate_eq_ramp K _ hT ht]
  exact (existenceRampInterpolate_div K values (K : Nat) t T).symm

private theorem calendarPolygonalAction_sum
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    Finset.univ.sum (N.calendarPolygonalAction initial T U K omega j k t) =
      N.calendarPolygonalInput T K omega t j k := by
  rw [calendarPolygonalInput_eq_batched N initial hT U K omega j k ht]
  unfold calendarPolygonalAction scaledBatchedPolicyActionInterpolate
    scaledBatchedInputInterpolate
  rw [<- Finset.sum_div]
  unfold batchedPolicyActionInterpolate finiteActionVectorInterpolate
    batchedInputInterpolate finiteActionInputInterpolate
  field_simp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [<- Finset.mul_sum]
  rw [(N.actionDirac_isDistribution
    (U K
      ((N.calendarGridPreActionStates initial T U K omega j k q.1).get q.2)
      j k)).2]
  rw [mul_one]

private theorem calendarPolygonalAction_none
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    N.calendarPolygonalAction initial T U K omega j k t none =
      N.calendarPolygonalInput T K omega t j k -
        Finset.univ.sum (fun i : Buffer =>
          N.calendarPolygonalAllocation initial T U K omega t i j k) := by
  have hsum := calendarPolygonalAction_sum N initial hT U K omega j k ht
  rw [show
    Finset.univ.sum (N.calendarPolygonalAction initial T U K omega j k t) =
      N.calendarPolygonalAction initial T U K omega j k t none +
        Finset.univ.sum (fun i : Buffer =>
          N.calendarPolygonalAction initial T U K omega j k t (some i)) by
    rw [Fintype.sum_option]] at hsum
  simp_rw [calendarPolygonalAction_some N initial hT U K omega _ _ _ ht] at hsum
  linarith

private theorem calendar_empiricalPreActionStates_mem_dist_le {Knat : Nat}
    (U0 : N.DeterministicStationaryPolicy Knat)
    (z : JobState Buffer Knat)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer)
    {y : JobState Buffer Knat}
    (hy : y ∈ N.empiricalPreActionStates U0 z tokens j k)
    (i : Buffer) :
    abs ((y i : Real) - (z i : Real)) <= 2 * tokens.length := by
  induction tokens generalizing z with
  | nil =>
      simp [empiricalPreActionStates] at hy
  | cons jk rest ih =>
      by_cases hm : jk = (j, k)
      · subst jk
        simp only [empiricalPreActionStates, if_pos,
          List.mem_cons] at hy
        rcases hy with rfl | hy
        · rw [sub_self, abs_zero]
          exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
        · have htail :=
            ih (N.queueStep U0 z (j, k)) hy
          have hone :=
            runTokens_l1_le_two_mul_length N U0 z [(j, k)]
          have hcoord :
              abs (((N.queueStep U0 z (j, k) i : Nat) : Real) -
                (z i : Real)) <= 2 := by
            have hsingle :=
              Finset.single_le_sum
                (fun q _ => abs_nonneg
                  (((N.runTokens U0 z [(j, k)] q : Nat) : Real) -
                    (z q : Real)))
                (Finset.mem_univ i)
            have hrun :
                N.runTokens U0 z [(j, k)] =
                  N.queueStep U0 z (j, k) := by
              rfl
            rw [hrun] at hsingle
            rw [hrun] at hone
            exact hsingle.trans (by simpa using hone)
          calc
            abs ((y i : Real) - (z i : Real)) <=
                abs ((y i : Real) -
                  (N.queueStep U0 z (j, k) i : Real)) +
                abs ((N.queueStep U0 z (j, k) i : Real) -
                  (z i : Real)) := abs_sub_le _ _ _
            _ <= 2 * rest.length + 2 := add_le_add htail hcoord
            _ = 2 * ((j, k) :: rest).length := by simp; ring
      · simp only [empiricalPreActionStates, hm, if_neg] at hy
        have htail := ih (N.queueStep U0 z jk) hy
        have hone :=
          runTokens_l1_le_two_mul_length N U0 z [jk]
        have hcoord :
            abs (((N.queueStep U0 z jk i : Nat) : Real) -
              (z i : Real)) <= 2 := by
          have hsingle :=
            Finset.single_le_sum
              (fun q _ => abs_nonneg
                (((N.runTokens U0 z [jk] q : Nat) : Real) -
                  (z q : Real)))
              (Finset.mem_univ i)
          have hrun :
              N.runTokens U0 z [jk] = N.queueStep U0 z jk := by
            rfl
          rw [hrun] at hsingle
          rw [hrun] at hone
          exact hsingle.trans (by simpa using hone)
        calc
          abs ((y i : Real) - (z i : Real)) <=
              abs ((y i : Real) -
                (N.queueStep U0 z jk i : Real)) +
              abs ((N.queueStep U0 z jk i : Real) -
                (z i : Real)) := abs_sub_le _ _ _
          _ <= 2 * rest.length + 2 := add_le_add htail hcoord
          _ = 2 * (jk :: rest).length := by simp; ring

private theorem calendarGridBatch_scaled_length
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (l : Nat) :
    ((N.calendarGridBatch T K omega l).length : Real) / (K : Nat) =
      Finset.univ.sum (fun jk : Server × Buffer =>
        N.totalCalendarScaledInput K omega
            (calendarGridTime T K (l + 1)) jk.1 jk.2 -
          N.totalCalendarScaledInput K omega
            (calendarGridTime T K l) jk.1 jk.2) := by
  rw [calendarGridBatch_length_eq_input_sum N hT K omega l,
    Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro jk hjk
  rw [calendarScaledInput_eq_prefix_count N,
    calendarScaledInput_eq_prefix_count N]
  simp only [calendarGridInput, calendarGridPrefix]
  have hmono := calendarGridInput_mono N hT K omega
    (Nat.le_succ l) jk.1 jk.2
  have hmono' :
      (N.totalCalendarTokenPrefix K omega
          (calendarGridTime T K l)).count jk <=
        (N.totalCalendarTokenPrefix K omega
          (calendarGridTime T K (l + 1))).count jk := by
    simpa only [calendarGridInput, calendarGridPrefix] using hmono
  rw [Nat.cast_sub hmono']
  ring

private theorem calendarGridBatch_scaled_length_small
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K)
    (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn
        T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall l, l < (K r : Nat) ->
          2 * (((N.calendarGridBatch T (K r) omega l).length : Real) /
            (K r : Nat)) < epsilon := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  let Avec : Real -> (Server × Buffer -> Real) :=
    fun t jk => A t jk.1 jk.2
  have hAvecCont : ContinuousOn Avec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro jk
    simpa [Avec, uIcc_of_le hT.le] using
      (hA jk.1 jk.2).continuousOn
  have hAvecUC : UniformContinuousOn Avec (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hAvecCont
  have hKreal :
      Tendsto (fun r => (((K r : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun r => T / (((K r : Nat) : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  intro epsilon hepsilon
  let C : Real := (Fintype.card (Server × Buffer) : Real) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let eta : Real := epsilon / (8 * C)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp hAvecUC eta heta
  obtain ⟨rMesh, hrMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh delta hdelta
  obtain ⟨rInput, hrInput⟩ := hinput eta heta
  refine ⟨max rMesh rInput, fun r hr l hl => ?_⟩
  have hrM : rMesh <= r := (le_max_left _ _).trans hr
  have hrI : rInput <= r := (le_max_right _ _).trans hr
  let s := calendarGridTime T (K r) l
  let t := calendarGridTime T (K r) (l + 1)
  have hls : l <= (K r : Nat) := Nat.le_of_lt hl
  have hlt : l + 1 <= (K r : Nat) := hl
  have hsMem : s ∈ Icc (0 : Real) T :=
    calendarGridTime_mem_Icc hT (K r) hls
  have htMem : t ∈ Icc (0 : Real) T :=
    calendarGridTime_mem_Icc hT (K r) hlt
  have hmeshSmall : T / (((K r : Nat) : Real)) < delta := by
    have hm := hrMesh r hrM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at hm
    exact hm
  have hst : dist s t < delta := by
    rw [Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr
        (calendarGridTime_mono hT (K r) (Nat.le_succ l)))]
    simpa [s, t, calendarGridTime_succ_sub] using hmeshSmall
  have hAvecNear : dist (Avec s) (Avec t) < eta :=
    hdeltaWorks s hsMem t htMem hst
  have hterm (jk : Server × Buffer) :
      N.totalCalendarScaledInput (K r) omega t jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) omega s jk.1 jk.2 <
        3 * eta := by
    have hsInput := hrInput r hrI s hsMem jk
    have htInput := hrInput r hrI t htMem jk
    have hcoord :
        dist (Avec s jk) (Avec t jk) <= dist (Avec s) (Avec t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s) (Avec t) <= dist (Avec s) (Avec t)) jk
    have hmiddle : abs (A t jk.1 jk.2 - A s jk.1 jk.2) < eta := by
      simpa [Avec, Real.dist_eq, abs_sub_comm] using
        hcoord.trans_lt hAvecNear
    calc
      N.totalCalendarScaledInput (K r) omega t jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) omega s jk.1 jk.2 <=
        abs (N.totalCalendarScaledInput (K r) omega t jk.1 jk.2 -
          A t jk.1 jk.2) +
        abs (A t jk.1 jk.2 - A s jk.1 jk.2) +
        abs (A s jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) omega s jk.1 jk.2) := by
            linarith [le_abs_self
              (N.totalCalendarScaledInput (K r) omega t jk.1 jk.2 -
                A t jk.1 jk.2),
              le_abs_self (A t jk.1 jk.2 - A s jk.1 jk.2),
              le_abs_self (A s jk.1 jk.2 -
                N.totalCalendarScaledInput (K r) omega s jk.1 jk.2)]
      _ < eta + eta + eta := by
        exact add_lt_add (add_lt_add htInput hmiddle)
          (by simpa [abs_sub_comm] using hsInput)
      _ = 3 * eta := by ring
  have hsum :
      Finset.univ.sum (fun jk : Server × Buffer =>
        N.totalCalendarScaledInput (K r) omega t jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) omega s jk.1 jk.2) <
        (Fintype.card (Server × Buffer) : Real) * (3 * eta) := by
    calc
      _ < Finset.univ.sum (fun _ : Server × Buffer => 3 * eta) :=
        Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty : (Finset.univ :
            Finset (Server × Buffer)).Nonempty)
          (fun jk _ => hterm jk)
      _ = _ := by simp
  rw [calendarGridBatch_scaled_length N hT (K r) omega l]
  calc
    2 * Finset.univ.sum (fun jk : Server × Buffer =>
        N.totalCalendarScaledInput (K r) omega t jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) omega s jk.1 jk.2) <
        2 * ((Fintype.card (Server × Buffer) : Real) * (3 * eta)) :=
      mul_lt_mul_of_pos_left hsum (by norm_num)
    _ < epsilon := by
      dsimp [eta, C]
      have hcard : 0 <= (Fintype.card (Server × Buffer) : Real) := by
        positivity
      have hcardC :
          (Fintype.card (Server × Buffer) : Real) <
            (Fintype.card (Server × Buffer) : Real) + 1 := by linarith
      have hratio :
          (Fintype.card (Server × Buffer) : Real) /
              ((Fintype.card (Server × Buffer) : Real) + 1) < 1 :=
        (div_lt_one (by linarith)).2 hcardC
      field_simp
      nlinarith

private theorem calendar_edgeProgress_le_one (r : Real) (l : Nat) :
    edgeProgress r l <= 1 := by
  unfold edgeProgress
  exact max_le (by norm_num) (min_le_left _ _)

private theorem calendar_edgeProgress_pos_imp (r : Real) (l : Nat)
    (h : 0 < edgeProgress r l) :
    (l : Real) < r := by
  unfold edgeProgress at h
  have hm : 0 < min 1 (r - (l : Real)) := by
    by_contra hn
    have hmle : min 1 (r - (l : Real)) <= 0 := le_of_not_gt hn
    rw [max_eq_left hmle] at h
    exact (lt_irrefl 0 h)
  exact sub_pos.mp ((lt_min_iff.mp hm).2)

private theorem calendar_edgeProgress_lt_one_imp (r : Real) (l : Nat)
    (h : edgeProgress r l < 1) :
    r < (l : Real) + 1 := by
  by_contra hn
  have hr : 1 <= r - (l : Real) := by linarith
  unfold edgeProgress at h
  rw [min_eq_left hr, max_eq_right zero_le_one] at h
  exact (lt_irrefl 1 h)

private theorem calendar_used_edge_gridTime_close
    {T : Real} (hT : 0 < T) (K : PNat)
    {t h : Real} (hh : 0 < h) (l : Nat)
    (hused :
      0 <
        edgeProgress (((K : Nat) : Real) * (t + h) / T) l -
          edgeProgress (((K : Nat) : Real) * t / T) l) :
    abs (calendarGridTime T K l - t) <
      h + T / (K : Nat) := by
  let r0 : Real := ((K : Nat) : Real) * t / T
  let r1 : Real := ((K : Nat) : Real) * (t + h) / T
  have hp : edgeProgress r0 l < edgeProgress r1 l := sub_pos.mp hused
  have hr1pos : 0 < edgeProgress r1 l :=
    lt_of_le_of_lt (edgeProgress_nonneg r0 l) hp
  have hr0lt : edgeProgress r0 l < 1 :=
    hp.trans_le (calendar_edgeProgress_le_one r1 l)
  have hlr1 := calendar_edgeProgress_pos_imp r1 l hr1pos
  have hr0l := calendar_edgeProgress_lt_one_imp r0 l hr0lt
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hcancel :
      T / (K : Nat) * (K : Nat) = T :=
    div_mul_cancel₀ T (ne_of_gt hK)
  have hlower : t - T / (K : Nat) < calendarGridTime T K l := by
    dsimp [r0] at hr0l
    unfold calendarGridTime
    apply (lt_div_iff₀ hK).2
    apply (div_lt_iff₀ hT).1 at hr0l
    nlinarith [hcancel]
  have hupper : calendarGridTime T K l < t + h := by
    dsimp [r1] at hlr1
    unfold calendarGridTime
    apply (div_lt_iff₀ hK).2
    apply (lt_div_iff₀ hT).1 at hlr1
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith [div_pos hT hK]

private theorem calendarPreActionStates_near
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X)
    {t epsilon : Real} (ht : t ∈ Ioo (0 : Real) T)
    (hepsilon : 0 < epsilon) :
    exists delta, 0 < delta /\
      exists r0, forall r, r0 <= r ->
        forall h, 0 < h -> h < delta ->
          forall j k (l : Fin (K r : Nat))
            (y : JobState Buffer (K r : Nat)),
            y ∈ N.calendarGridPreActionStates initial T U (K r) omega j k l ->
            0 <
              edgeProgress
                  (((K r : Nat) : Real) * (t + h) / T) l.val -
                edgeProgress
                  (((K r : Nat) : Real) * t / T) l.val ->
            IsNearNormalizedState y (X t) epsilon := by
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t i => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
      X at hstate
  let Xvec : Real -> (Buffer -> Real) := fun s i => X s i
  have hXcont : ContinuousOn Xvec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    exact calendarStateLimit_continuousOn N initial hT U K omega A X hA hconverges
  have hXuc : UniformContinuousOn Xvec (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hXcont
  obtain ⟨deltaX, hdeltaX, hdeltaXWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp hXuc
      (epsilon / 3) (by positivity)
  let delta := min (deltaX / 2) ((T - t) / 2)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by positivity) (by linarith [ht.2])
  have hKreal :
      Tendsto (fun r => (((K r : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun r => T / (((K r : Nat) : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  obtain ⟨rMesh, hrMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh (deltaX / 2) (by positivity)
  obtain ⟨rBatch, hrBatch⟩ :=
    calendarGridBatch_scaled_length_small N initial hT U K hK omega
      A X hA hconverges (epsilon / 3) (by positivity)
  obtain ⟨rState, hrState⟩ := hstate (epsilon / 3) (by positivity)
  refine ⟨delta, hdelta, max rMesh (max rBatch rState),
    fun r hr h hh hhdelta j k l y hy hused => ?_⟩
  have hrM : rMesh <= r :=
    (le_max_left rMesh (max rBatch rState)).trans hr
  have hrB : rBatch <= r :=
    (le_max_left rBatch rState).trans
      ((le_max_right rMesh (max rBatch rState)).trans hr)
  have hrS : rState <= r :=
    (le_max_right rBatch rState).trans
      ((le_max_right rMesh (max rBatch rState)).trans hr)
  have hmeshSmall : T / (((K r : Nat) : Real)) < deltaX / 2 := by
    have hm := hrMesh r hrM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at hm
    exact hm
  have hbatchSmall :
      2 * (((N.calendarGridBatch T (K r) omega l.val).length : Real) /
        (K r : Nat)) < epsilon / 3 :=
    hrBatch r hrB l.val l.isLt
  have hlK : l.val <= (K r : Nat) := Nat.le_of_lt l.isLt
  have hgridMem :
      calendarGridTime T (K r) l.val ∈ Icc (0 : Real) T :=
    calendarGridTime_mem_Icc hT (K r) hlK
  have hgridClose :
      dist (calendarGridTime T (K r) l.val) t < deltaX := by
    rw [Real.dist_eq]
    have hc :=
      calendar_used_edge_gridTime_close hT (K r) hh l.val hused
    exact hc.trans_le (by
      have hdX : delta <= deltaX / 2 := min_le_left _ _
      linarith)
  have hXclose :
      dist (Xvec (calendarGridTime T (K r) l.val)) (Xvec t) <
        epsilon / 3 :=
    hdeltaXWorks _ hgridMem _ ⟨ht.1.le, ht.2.le⟩ hgridClose
  have hfiniteState (i : Buffer) :
      abs
        (((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
            (K r : Nat) -
          X (calendarGridTime T (K r) l.val) i) < epsilon / 3 := by
    exact hrState r hrS _ hgridMem i
  intro i
  have hyraw :=
    calendar_empiricalPreActionStates_mem_dist_le N (U (K r))
      (N.calendarGridState initial T U (K r) omega l.val)
      (N.calendarGridBatch T (K r) omega l.val) j k hy i
  have hygrid :
      abs
        (((y i : Nat) : Real) / (K r : Nat) -
          ((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
            (K r : Nat)) < epsilon / 3 := by
    have hKpos : (0 : Real) < (K r : Nat) := by positivity
    rw [<- sub_div, abs_div, abs_of_pos hKpos]
    calc
      _ <= (2 * (N.calendarGridBatch T (K r) omega l.val).length : Real) /
          (K r : Nat) := div_le_div_of_nonneg_right hyraw hKpos.le
      _ = 2 *
          (((N.calendarGridBatch T (K r) omega l.val).length : Real) /
            (K r : Nat)) := by ring
      _ < epsilon / 3 := hbatchSmall
  have hXcoord :
      abs
        (X (calendarGridTime T (K r) l.val) i - X t i) <
          epsilon / 3 := by
    have hc :
        dist
            (Xvec (calendarGridTime T (K r) l.val) i)
            (Xvec t i) <=
          dist
            (Xvec (calendarGridTime T (K r) l.val))
            (Xvec t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl :
          dist (Xvec (calendarGridTime T (K r) l.val)) (Xvec t) <= _) i
    simpa [Xvec, Real.dist_eq] using hc.trans_lt hXclose
  calc
    abs (((y i : Nat) : Real) / (K r : Nat) - X t i) <=
        abs
          (((y i : Nat) : Real) / (K r : Nat) -
            ((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
              (K r : Nat)) +
        abs
          (((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
              (K r : Nat) -
            X (calendarGridTime T (K r) l.val) i) +
        abs (X (calendarGridTime T (K r) l.val) i - X t i) := by
      calc
        _ <= abs
            (((y i : Nat) : Real) / (K r : Nat) -
              ((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
                (K r : Nat)) +
            abs
              (((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
                (K r : Nat) - X t i) := abs_sub_le _ _ _
        _ <= _ := by
          have htri := abs_sub_le
            (((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
              (K r : Nat))
            (X (calendarGridTime T (K r) l.val) i) (X t i)
          linarith
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 :=
      add_lt_add (add_lt_add hygrid (hfiniteState i)) hXcoord
    _ = epsilon := by ring

private noncomputable def calendarLimitAction
    (A : MatrixPath Server Buffer) (E : FluidAllocationPath Buffer Server)
    (j : Server) (k : Buffer) (t : Real) : ActionVector Buffer
  | none => A t j k - Finset.univ.sum (fun i : Buffer => E t i j k)
  | some i => E t i j k

private theorem calendarPolygonalAction_tendsto
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon)
    {t : Real} (ht : t ∈ Icc (0 : Real) T)
    (j : Server) (k : Buffer) (a : Option Buffer) :
    Tendsto
      (fun r => N.calendarPolygonalAction initial T U (K (q r)) omega j k t a)
      atTop (nhds (calendarLimitAction A E j k t a)) := by
  have hinputConv :=
    calendarPolygonalInput_converges N initial hT U K hK omega A X hA hconverges
  have hApoint :
      Tendsto
        (fun r => N.calendarPolygonalInput T (K (q r)) omega t j k)
        atTop (nhds (A t j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hinputConv epsilon hepsilon
    refine ⟨r0, fun r hr => ?_⟩
    exact hr0 (q r) (hr.trans (hq.id_le r)) (j, k) t ht
  have hEpoint (i : Buffer) :
      Tendsto
        (fun r =>
          N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
        atTop (nhds (E t i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i j k t ht⟩
  cases a with
  | none =>
      rw [show
        (fun r =>
          N.calendarPolygonalAction initial T U (K (q r)) omega j k t none) =
        fun r =>
          N.calendarPolygonalInput T (K (q r)) omega t j k -
            Finset.univ.sum (fun i : Buffer =>
              N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k) by
        funext r
        exact calendarPolygonalAction_none N initial hT U (K (q r)) omega j k ht]
      exact hApoint.sub (tendsto_finsetSum _ (fun i _ => hEpoint i))
  | some i =>
      rw [show
        (fun r =>
          N.calendarPolygonalAction initial T U (K (q r)) omega j k t (some i)) =
        fun r =>
          N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k by
        funext r
        exact calendarPolygonalAction_some N initial hT U (K (q r)) omega i j k ht]
      exact hEpoint i

private theorem calendarLimit_finiteDifference_mem_epsilon
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon)
    {t epsilon h : Real} (ht : t ∈ Ioo (0 : Real) T)
    (hepsilon : 0 < epsilon) (hh : 0 < h)
    (hth : t + h ∈ Icc (0 : Real) T)
    (hden : 0 < A (t + h) j k - A t j k)
    (hnearWindow :
      exists r0, forall r, r0 <= r ->
        forall l
          (y : JobState Buffer (K (q r) : Nat)),
          y ∈ N.calendarGridPreActionStates initial
            T U (K (q r)) omega j k l ->
          0 <
            edgeProgress
                (((K (q r) : Nat) : Real) * (t + h) / T) l.val -
              edgeProgress
                (((K (q r) : Nat) : Real) * t / T) l.val ->
          IsNearNormalizedState y (X t) epsilon) :
    finiteDifferenceRatio
        (fun s => A s j k)
        (fun s => calendarLimitAction A E j k s)
        t h ∈
      N.fluidPolicyEpsilonCorrespondence U j k (X t) epsilon := by
  have hinputConv :=
    calendarPolygonalInput_converges N initial hT U K hK omega A X hA hconverges
  have hApoint (s : Real) (hs : s ∈ Icc (0 : Real) T) :
      Tendsto
        (fun r => N.calendarPolygonalInput T (K (q r)) omega s j k)
        atTop (nhds (A s j k)) := by
    rw [Metric.tendsto_atTop]
    intro eta heta
    obtain ⟨r0, hr0⟩ := hinputConv eta heta
    exact ⟨r0, fun r hr =>
      hr0 (q r) (hr.trans (hq.id_le r)) (j, k) s hs⟩
  have hdenConv :
      Tendsto
        (fun r =>
          N.calendarPolygonalInput T (K (q r)) omega (t + h) j k -
            N.calendarPolygonalInput T (K (q r)) omega t j k)
        atTop (nhds (A (t + h) j k - A t j k)) :=
    (hApoint (t + h) hth).sub
      (hApoint t ⟨ht.1.le, ht.2.le⟩)
  have hdenEventually :
      Filter.Eventually
        (fun r =>
          0 <
            N.calendarPolygonalInput T (K (q r)) omega (t + h) j k -
              N.calendarPolygonalInput T (K (q r)) omega t j k)
        atTop := by
    exact (tendsto_order.mp hdenConv).1 0 hden
  have hKreal :
      Tendsto (fun r => (((K (q r) : Nat) : Real))) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      ((pnat_val_strictMono hK).comp hq).tendsto_atTop
  have hKEventually :
      Filter.Eventually
        (fun r => epsilon⁻¹ <= ((K (q r) : Nat) : Real)) atTop :=
    (tendsto_atTop.1 hKreal epsilon⁻¹)
  obtain ⟨rNear, hrNear⟩ := hnearWindow
  have hnearEventually :
      Filter.Eventually
        (fun r =>
          forall l
            (y : JobState Buffer (K (q r) : Nat)),
            y ∈ N.calendarGridPreActionStates initial
              T U (K (q r)) omega j k l ->
            0 <
              edgeProgress
                  (((K (q r) : Nat) : Real) * (t + h) / T) l.val -
                edgeProgress
                  (((K (q r) : Nat) : Real) * t / T) l.val ->
            IsNearNormalizedState y (X t) epsilon)
        atTop :=
    eventually_atTop.2 ⟨rNear, hrNear⟩
  have hmem :
      Filter.Eventually
        (fun r =>
          finiteDifferenceRatio
              (fun s =>
                N.calendarPolygonalInput T (K (q r)) omega s j k)
              (fun s =>
                N.calendarPolygonalAction initial T U (K (q r)) omega j k s)
              t h ∈
            N.fluidPolicyEpsilonCorrespondence U j k (X t) epsilon)
        atTop := by
    filter_upwards [hdenEventually, hKEventually, hnearEventually] with
      r hpos hsize hnear
    unfold finiteDifferenceRatio
    change
      (fun a =>
        (N.calendarPolygonalAction initial T U (K (q r)) omega j k (t + h) a -
            N.calendarPolygonalAction initial T U (K (q r)) omega j k t a) /
          (N.calendarPolygonalInput T (K (q r)) omega (t + h) j k -
            N.calendarPolygonalInput T (K (q r)) omega t j k)) ∈
        N.fluidPolicyEpsilonCorrespondence U j k (X t) epsilon
    rw [calendarPolygonalInput_eq_batched N initial hT U (K (q r)) omega j k ⟨ht.1.le, ht.2.le⟩]
    rw [calendarPolygonalInput_eq_batched N initial hT U (K (q r)) omega j k hth]
    have hpos' :
        0 <
          scaledBatchedInputInterpolate (K (q r))
              (N.calendarGridPreActionStates initial T U (K (q r)) omega j k)
              T (t + h) -
            scaledBatchedInputInterpolate (K (q r))
              (N.calendarGridPreActionStates initial T U (K (q r)) omega j k)
              T t := by
      simpa only [
        calendarPolygonalInput_eq_batched N initial hT U (K (q r)) omega j k hth,
        calendarPolygonalInput_eq_batched N initial hT U (K (q r)) omega j k ⟨ht.1.le, ht.2.le⟩] using hpos
    exact N.finiteDifferenceRatio_scaledBatched_mem_epsilon
      (K (q r)) U (K (q r))
      (N.calendarGridPreActionStates initial T U (K (q r)) omega j k)
      j k (X t) epsilon T t h hT hh hpos' hsize hnear
  apply closed_mem_of_finiteDifferenceRatio_limit
    (N.fluidPolicyEpsilonCorrespondence_isClosed U j k (X t) epsilon)
    (fun r s => N.calendarPolygonalInput T (K (q r)) omega s j k)
    (fun s => A s j k)
    (fun r s => N.calendarPolygonalAction initial T U (K (q r)) omega j k s)
    (fun s => calendarLimitAction A E j k s)
    t (t + h)
  · exact hApoint t ⟨ht.1.le, ht.2.le⟩
  · exact hApoint (t + h) hth
  · intro a
    exact calendarPolygonalAction_tendsto N initial hT U K hK omega A X hA
      hconverges q hq E hpoly ⟨ht.1.le, ht.2.le⟩ j k a
  · intro a
    exact calendarPolygonalAction_tendsto N initial hT U K hK omega A X hA
      hconverges q hq E hpoly hth j k a
  · exact ne_of_gt hden
  · filter_upwards [hmem] with n hn
    change
      (fun a =>
        (N.calendarPolygonalAction initial T U (K (q n)) omega j k (t + h) a -
            N.calendarPolygonalAction initial T U (K (q n)) omega j k t a) /
          (N.calendarPolygonalInput T (K (q n)) omega (t + h) j k -
            N.calendarPolygonalInput T (K (q n)) omega t j k)) ∈
        N.fluidPolicyEpsilonCorrespondence U j k (X t) epsilon at hn
    exact hn

private theorem calendarLimit_allocation_initial
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (q : Nat -> Nat) (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall i j k, E 0 i j k = 0 := by
  intro i j k
  have hlim :
      Tendsto
        (fun r =>
          N.calendarPolygonalAllocation initial T U (K (q r)) omega 0 i j k)
        atTop (nhds (E 0 i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i j k 0 ⟨le_rfl, hT.le⟩⟩
  have heq :
      (fun r =>
        N.calendarPolygonalAllocation initial T U (K (q r)) omega 0 i j k) =
        fun _ => 0 := by
    funext r
    exact calendarPolygonalAllocation_initial N initial hT U (K (q r)) omega i j k
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem calendarLimit_allocation_incompatible
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (q : Nat -> Nat) (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall t, t ∈ Icc (0 : Real) T ->
      forall i j k, Not (N.compatible i j) -> E t i j k = 0 := by
  intro t ht i j k hij
  have hlim :
      Tendsto
        (fun r =>
          N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
        atTop (nhds (E t i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i j k t ht⟩
  have heq :
      (fun r =>
        N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k) =
        fun _ => 0 := by
    funext r
    exact calendarPolygonalAllocation_incompatible N initial T U (K (q r)) omega t i j k hij
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem calendarLimit_state_in_simplex
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall t, t ∈ Icc (0 : Real) T -> IsFluidState (X t) := by
  have hstate :=
    calendarPolygonalState_converges N initial hT U K hK omega A X hA hconverges
  intro t ht
  have hpoint (i : Buffer) :
      Tendsto (fun r => N.calendarPolygonalState initial T U (K r) omega t i)
        atTop (nhds (X t i)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hstate epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i t ht⟩
  constructor
  · intro i
    have hneg := (hpoint i).neg
    have hle : -X t i <= 0 :=
      le_of_tendsto' hneg (fun r => by
        have hn :=
          (calendarPolygonalState_in_simplex N initial hT U (K r) omega ht).1 i
        linarith)
    linarith
  · apply tendsto_nhds_unique
      (tendsto_finsetSum _ (fun i _ => hpoint i))
    have heq :
        (fun r =>
          Finset.univ.sum (N.calendarPolygonalState initial T U (K r) omega t)) =
          fun _ => 1 := by
      funext r
      exact (calendarPolygonalState_in_simplex N initial hT U (K r) omega ht).2
    rw [heq]
    exact tendsto_const_nhds

private theorem calendarLimit_balance
    {T : Real} (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hX0 : forall i, X 0 i = x0 i)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall t, t ∈ Icc (0 : Real) T ->
      forall i,
        X t i = x0 i +
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun l : Buffer => E t l j i) -
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer => E t i j k) := by
  have hstate :=
    calendarPolygonalState_converges N initial hT U K hK omega A X hA hconverges
  intro t ht i
  have hXpoint :
      Tendsto
        (fun r => N.calendarPolygonalState initial T U (K (q r)) omega t i)
        atTop (nhds (X t i)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hstate epsilon hepsilon
    exact ⟨r0, fun r hr =>
      hr0 (q r) (hr.trans (hq.id_le r)) i t ht⟩
  have hEpoint (l : Buffer) (j : Server) (k : Buffer) :
      Tendsto
        (fun r =>
          N.calendarPolygonalAllocation initial T U (K (q r)) omega t l j k)
        atTop (nhds (E t l j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr l j k t ht⟩
  have hinit :
      Tendsto
        (fun r => ((initial (K (q r)) i : Nat) : Real) /
          (K (q r) : Nat))
        atTop (nhds (x0 i)) := by
    have hzeroState := hconverges.2
    change UniformlyOnIcc T
        (fun r t i => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
        X at hzeroState
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hzeroState epsilon hepsilon
    refine ⟨r0, fun r hr => ?_⟩
    have hz := hr0 (q r) (hr.trans (hq.id_le r))
      0 ⟨le_rfl, hT.le⟩ i
    simpa [Real.dist_eq, calendarScaledQueueStateFromInitial,
      totalCalendarScaledQueueStateFrom, totalCalendarTokenPrefix_zero N,
      runTokens, hX0 i] using hz
  have hrhs :
      Tendsto
        (fun r =>
          ((initial (K (q r)) i : Nat) : Real) /
              (K (q r) : Nat) +
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun l : Buffer =>
                N.calendarPolygonalAllocation initial
                  T U (K (q r)) omega t l j i) -
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer =>
                N.calendarPolygonalAllocation initial
                  T U (K (q r)) omega t i j k))
        atTop
        (nhds
          (x0 i +
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun l : Buffer => E t l j i) -
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer => E t i j k))) :=
    (hinit.add
      (tendsto_finsetSum _ (fun j _ =>
        tendsto_finsetSum _ (fun l _ => hEpoint l j i)))).sub
      (tendsto_finsetSum _ (fun j _ =>
        tendsto_finsetSum _ (fun k _ => hEpoint i j k)))
  apply tendsto_nhds_unique hXpoint
  apply hrhs.congr'
  filter_upwards [] with r
  exact (calendarPolygonal_balance N initial hT U (K (q r)) omega ht i).symm

private theorem calendarLimit_allocation_ac
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T := by
  intro i j k
  apply absolutelyContinuousOnInterval_of_uniform_limits_finset
    (f := fun r t =>
      N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
    (limit := fun t => E t i j k)
    (g := fun r (jk : Server × Buffer) t =>
      N.calendarPolygonalInput T (K (q r)) omega t jk.1 jk.2)
    (control := fun (jk : Server × Buffer) t => A t jk.1 jk.2)
    (s := Finset.univ)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    refine ⟨r0, fun r hr t ht => ?_⟩
    exact hr0 r hr i j k t (by simpa [uIcc_of_le hT.le] using ht)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ :=
      calendarPolygonalInput_converges N initial hT U K hK omega A X hA
        hconverges epsilon hepsilon
    refine ⟨r0, fun r hr jk hjk t ht => ?_⟩
    exact hr0 (q r) (hr.trans (hq.id_le r)) jk t
      (by simpa [uIcc_of_le hT.le] using ht)
  · intro jk hjk
    exact hA jk.1 jk.2
  · intro r s hs t ht
    exact calendarPolygonalAllocation_increment_domination N initial hT U (K (q r)) omega i j k
      (by simpa [uIcc_of_le hT.le] using hs)
      (by simpa [uIcc_of_le hT.le] using ht)

private theorem calendarLimit_allocation_increment
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hinput :
      UniformlyOnIcc T
        (fun r t (jk : Server × Buffer) =>
          N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)
        (fun t jk => A t jk.1 jk.2))
    (hraw :
      (N.calendarPoissonExecutionFrom initial).AllocationConvergesOn T U K q omega E) :
    forall i j k s, s ∈ Icc (0 : Real) T ->
      forall t, t ∈ Icc (0 : Real) T -> s <= t ->
        0 <= E t i j k - E s i j k /\
        E t i j k - E s i j k <= A t j k - A s j k := by
  intro i j k s hs t ht hst
  have hEpoint (u : Real) (hu : u ∈ Icc (0 : Real) T) :
      Tendsto (fun r => N.calendarScaledAllocationFromInitial initial U (K (q r)) omega u i j k)
        atTop (nhds (E u i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hraw epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr u hu (i, j, k)⟩
  have hApoint (u : Real) (hu : u ∈ Icc (0 : Real) T) :
      Tendsto (fun r => N.totalCalendarScaledInput (K (q r)) omega u j k)
        atTop (nhds (A u j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hinput epsilon hepsilon
    exact ⟨r0, fun r hr =>
      hr0 (q r) (hr.trans (hq.id_le r)) u hu (j, k)⟩
  constructor
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds
      ((hEpoint t ht).sub (hEpoint s hs))
      (Eventually.of_forall fun r =>
        (calendarScaledAllocationFromInitial_ordered_increment N initial U (K (q r)) omega hst i j k).1)
  · exact le_of_tendsto_of_tendsto
      ((hEpoint t ht).sub (hEpoint s hs))
      ((hApoint t ht).sub (hApoint s hs))
      (Eventually.of_forall fun r =>
        (calendarScaledAllocationFromInitial_ordered_increment N initial U (K (q r)) omega hst i j k).2)

private theorem calendarLimit_state_ac
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall i, AbsolutelyContinuousOnInterval (fun t => X t i) 0 T := by
  intro i
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t i => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
      X at hstate
  apply absolutelyContinuousOnInterval_of_uniform_limits_finset
    (f := fun r t => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
    (limit := fun t => X t i)
    (g := fun r (jk : Server × Buffer) t =>
      2 * N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)
    (control := fun (jk : Server × Buffer) t =>
      2 * A t jk.1 jk.2)
    (s := Finset.univ)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hstate epsilon hepsilon
    refine ⟨r0, fun r hr t ht => ?_⟩
    exact hr0 r hr t (by simpa [uIcc_of_le hT.le] using ht) i
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hconverges.1 (epsilon / 2) (by positivity)
    refine ⟨r0, fun r hr b hb t ht => ?_⟩
    have h := hr0 r hr t
      (by simpa [uIcc_of_le hT.le] using ht) b
    change
      abs (N.totalCalendarScaledInput (K r) omega t b.1 b.2 -
        A t b.1 b.2) < epsilon / 2 at h
    rw [Real.dist_eq, <- mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    nlinarith
  · intro b hb
    have hac := (hA b.1 b.2).const_mul 2
    unfold AbsolutelyContinuousOnInterval at hac ⊢
    simpa only using hac
  · intro r s hs t ht
    have hdom := calendarScaledQueueStateFromInitial_dist_le N initial U (K r) omega s t i
    calc
      _ <= 2 * Finset.univ.sum (fun jk : Server × Buffer =>
          dist (N.totalCalendarScaledInput (K r) omega s jk.1 jk.2)
            (N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)) := hdom
      _ = Finset.univ.sum (fun jk : Server × Buffer =>
          dist (2 * N.totalCalendarScaledInput (K r) omega s jk.1 jk.2)
            (2 * N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)) := by
        simp_rw [Real.dist_eq, <- mul_sub, abs_mul,
          abs_of_pos (by norm_num : (0 : Real) < 2)]
        rw [Finset.mul_sum]

private theorem calendarLimit_balance_restricted
    {T : Real} (x0 : Simplex Buffer) (X : FluidStatePath Buffer)
    (E : FluidAllocationPath Buffer Server)
    (hbalance :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i,
          X t i = x0 i +
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun l : Buffer => E t l j i) -
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer => E t i j k))
    (hincompat :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i j k, Not (N.compatible i j) -> E t i j k = 0) :
    forall t, t ∈ Icc (0 : Real) T ->
      forall i,
        X t i = x0 i
          + (Finset.univ.sum fun j : Server =>
              Finset.sum (N.buffersOf j) fun l => E t l j i)
          - (Finset.sum (N.serversOf i) fun j =>
              Finset.univ.sum fun k : Buffer => E t i j k) := by
  intro t ht i
  rw [hbalance t ht i]
  have hin (j : Server) :
      Finset.univ.sum (fun l : Buffer => E t l j i) =
        Finset.sum (N.buffersOf j) (fun l => E t l j i) := by
    simp only [buffersOf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlj : N.compatible l j
    · simp [hlj]
    · simp [hlj, hincompat t ht l j i hlj]
  have hout :
      Finset.univ.sum
          (fun j : Server => Finset.univ.sum fun k : Buffer => E t i j k) =
        Finset.sum (N.serversOf i)
          (fun j => Finset.univ.sum fun k : Buffer => E t i j k) := by
    simp only [serversOf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : N.compatible i j
    · simp [hij]
    · simp [hij, hincompat t ht i j]
  simp_rw [hin]
  rw [hout]

private theorem calendar_absolutelyContinuousOnInterval_finset_sum
    {I : Type*} (s : Finset I) (f : I -> Real -> Real)
    {a b : Real}
    (hf : forall i, i ∈ s ->
      AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => s.sum fun i => f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (LipschitzWith.const (0 : Real)).lipschitzOnWith
          |>.absolutelyContinuousOnInterval
  | @insert i s hi ih =>
      have hai := hf i (Finset.mem_insert_self i s)
      have has : forall j, j ∈ s ->
          AbsolutelyContinuousOnInterval (f j) a b := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hfun :
          (fun t => Finset.sum (insert i s) fun j => f j t) =
            fun t => f i t + Finset.sum s fun j => f j t := by
        funext t
        rw [Finset.sum_insert hi]
      rw [hfun]
      have hsum := hai.add (ih has)
      unfold AbsolutelyContinuousOnInterval at hsum ⊢
      simpa only [Real.dist_eq, Pi.add_apply] using hsum

private theorem calendarLimitAction_ac
    {T : Real} (A : MatrixPath Server Buffer)
    (E : FluidAllocationPath Buffer Server)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hE : forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T) :
    forall j k a,
      AbsolutelyContinuousOnInterval
        (fun t => calendarLimitAction A E j k t a) 0 T := by
  intro j k a
  cases a with
  | some i =>
      exact hE i j k
  | none =>
      have hsum :
          AbsolutelyContinuousOnInterval
            (fun t => Finset.univ.sum fun i : Buffer => E t i j k)
            0 T := by
        apply calendar_absolutelyContinuousOnInterval_finset_sum
        intro i hi
        exact hE i j k
      have hsub := (hA j k).sub hsum
      unfold AbsolutelyContinuousOnInterval at hsub ⊢
      simpa only [calendarLimitAction, Pi.sub_apply] using hsub

private theorem calendar_hasDerivAt_eq_zero_of_increment_domination_Icc
    {T : Real} (A E : Real -> Real) {t Edot : Real}
    (ht : t ∈ Ioo (0 : Real) T)
    (hA : HasDerivAt A 0 t) (hE : HasDerivAt E Edot t)
    (hdom : forall s, s ∈ Icc (0 : Real) T ->
      forall u, u ∈ Icc (0 : Real) T -> s <= u ->
        0 <= E u - E s /\ E u - E s <= A u - A s) :
    Edot = 0 := by
  have hsmall :
      Filter.Eventually (fun h => t + h ∈ Icc (0 : Real) T)
        (nhdsWithin 0 (Ioi 0)) := by
    have hlt : 0 < T - t := sub_pos.mpr ht.2
    have hev : Filter.Eventually (fun h : Real => h < T - t) (nhds 0) :=
      eventually_lt_nhds hlt
    filter_upwards [self_mem_nhdsWithin, hev.filter_mono inf_le_left] with
      h hh hupper
    have hhpos : 0 < h := hh
    exact ⟨add_nonneg ht.1.le hhpos.le, by linarith⟩
  have hsqueeze :
      Tendsto (fun h => h⁻¹ * (E (t + h) - E t))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hA.tendsto_slope_zero_right
    next =>
      filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hth
      exact mul_nonneg (inv_nonneg.mpr hh.le)
        (hdom t ⟨ht.1.le, ht.2.le⟩ (t + h) hth
          (le_add_of_nonneg_right hh.le)).1
    next =>
      filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hth
      exact mul_le_mul_of_nonneg_left
        (hdom t ⟨ht.1.le, ht.2.le⟩ (t + h) hth
          (le_add_of_nonneg_right hh.le)).2
        (inv_nonneg.mpr hh.le)
  exact tendsto_nhds_unique hE.tendsto_slope_zero_right hsqueeze

private theorem calendarLimit_zero_derivative_ae
    {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer) (E : FluidAllocationPath Buffer Server)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hE : forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T)
    (hdom : forall i j k s, s ∈ Icc (0 : Real) T ->
      forall t, t ∈ Icc (0 : Real) T -> s <= t ->
        0 <= E t i j k - E s i j k /\
        E t i j k - E s i j k <= A t j k - A s j k) :
    Filter.Eventually
      (fun t => forall j k, deriv (fun s => A s j k) t = 0 ->
        forall i, deriv (fun s => E s i j k) t = 0)
      (ae (volume.restrict (Icc (0 : Real) T))) := by
  rw [<- Measure.restrict_congr_set
    (Ioo_ae_eq_Icc (μ := volume) (a := (0 : Real)) (b := T))]
  have hAdiff (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => t ∈ Icc (0 : Real) T ->
          DifferentiableAt Real (fun s => A s j k) t)
        (ae (volume.restrict (Ioo (0 : Real) T))) := by
    have hv := (hA j k).ae_differentiableAt.filter_mono
      (MeasureTheory.ae_restrict_le
        (μ := volume) (s := Ioo (0 : Real) T))
    filter_upwards [hv] with t ht hmem
    exact ht (by simpa [uIcc_of_le hT.le] using hmem)
  have hEdiff (i : Buffer) (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => t ∈ Icc (0 : Real) T ->
          DifferentiableAt Real (fun s => E s i j k) t)
        (ae (volume.restrict (Ioo (0 : Real) T))) := by
    have hv := (hE i j k).ae_differentiableAt.filter_mono
      (MeasureTheory.ae_restrict_le
        (μ := volume) (s := Ioo (0 : Real) T))
    filter_upwards [hv] with t ht hmem
    exact ht (by simpa [uIcc_of_le hT.le] using hmem)
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => hAdiff j k)),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      ae_all_iff.mpr (fun k => hEdiff i j k)))] with
      t ht hAt hEt
  intro j k hzero i
  apply calendar_hasDerivAt_eq_zero_of_increment_domination_Icc
    (fun s => A s j k) (fun s => E s i j k) ht
  · simpa [hzero] using (hAt j k (Set.Ioo_subset_Icc_self ht)).hasDerivAt
  · exact (hEt i j k (Set.Ioo_subset_Icc_self ht)).hasDerivAt
  · intro s hs u hu hsu
    exact hdom i j k s hs u hu hsu

private theorem calendarLimit_positive_policy_ae
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.calendarPoissonExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon)
    (hEac : forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T) :
    forall j k,
      Filter.Eventually
        (fun t => 0 < deriv (fun s => A s j k) t ->
          Membership.mem
            (N.fluidPolicyCorrespondence U j k (X t))
            (fun a =>
              deriv (fun s => calendarLimitAction A E j k s a) t /
                deriv (fun s => A s j k) t))
        (ae (volume.restrict (Icc (0 : Real) T))) := by
  intro j k
  let mu := volume.restrict (Icc (0 : Real) T)
  have hAdiff :
      Filter.Eventually
        (fun t => DifferentiableAt Real (fun s => A s j k) t)
        (ae mu) := by
    have hv :=
      (hA j k).ae_differentiableAt.filter_mono
        (MeasureTheory.ae_restrict_le
          (μ := volume) (s := Icc (0 : Real) T))
    filter_upwards [ae_restrict_mem measurableSet_Icc, hv] with t ht hdt
    exact hdt (by simpa [uIcc_of_le hT.le] using ht)
  have hActionAc :=
    calendarLimitAction_ac A E hA hEac
  have hActionDiff (a : Option Buffer) :
      Filter.Eventually
        (fun t =>
          DifferentiableAt Real
            (fun s => calendarLimitAction A E j k s a) t)
        (ae mu) := by
    have hv :=
      (hActionAc j k a).ae_differentiableAt.filter_mono
        (MeasureTheory.ae_restrict_le
          (μ := volume) (s := Icc (0 : Real) T))
    filter_upwards [ae_restrict_mem measurableSet_Icc, hv] with t ht hdt
    exact hdt (by simpa [uIcc_of_le hT.le] using ht)
  have hfinite :
      Filter.Eventually
        (fun t => 0 < deriv (fun s => A s j k) t ->
          forall epsilon : {r : Real // 0 < r},
            Filter.Eventually
              (fun h =>
                finiteDifferenceRatio
                    (fun s => A s j k)
                    (fun s => calendarLimitAction A E j k s) t h ∈
                  N.fluidPolicyEpsilonCorrespondence
                    U j k (X t) epsilon.1)
              (nhdsWithin 0 (Ioi 0)))
        (ae mu) := by
    rw [show mu =
      volume.restrict (Ioo (0 : Real) T) by
        dsimp [mu]
        exact Measure.restrict_congr_set
          (Ioo_ae_eq_Icc (μ := volume) (a := (0 : Real)) (b := T)).symm]
    have hAdiffIoo :
        Filter.Eventually
          (fun t => t ∈ Icc (0 : Real) T ->
            DifferentiableAt Real (fun s => A s j k) t)
          (ae (volume.restrict (Ioo (0 : Real) T))) := by
      have hv := (hA j k).ae_differentiableAt.filter_mono
        (MeasureTheory.ae_restrict_le
          (μ := volume) (s := Ioo (0 : Real) T))
      filter_upwards [hv] with t ht hmem
      exact ht (by simpa [uIcc_of_le hT.le] using hmem)
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hAdiffIoo] with
      t ht hAt
    intro hpos epsilon
    obtain ⟨deltaNear, hdeltaNear, rNear, hrNear⟩ :=
      calendarPreActionStates_near N initial hT U K hK omega A X hA hconverges
        ht epsilon.2
    let delta := min deltaNear (T - t)
    have hdelta : 0 < delta := by
      exact lt_min hdeltaNear (sub_pos.mpr ht.2)
    have hslope :
        Filter.Eventually
          (fun h =>
            deriv (fun s => A s j k) t / 2 <
              h⁻¹ * (A (t + h) j k - A t j k))
          (nhdsWithin 0 (Ioi 0)) := by
      have hslopeT :=
        (hAt (Set.Ioo_subset_Icc_self ht)).hasDerivAt
          |>.tendsto_slope_zero_right
      exact (tendsto_order.mp hslopeT).1
        (deriv (fun s => A s j k) t / 2) (by linarith)
    have hsmall :
        Filter.Eventually (fun h : Real => h < delta)
          (nhdsWithin 0 (Ioi 0)) :=
      (eventually_lt_nhds hdelta).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, hsmall, hslope] with
      h hh hhd hs
    have hhpos : 0 < h := hh
    have hhNear : h < deltaNear := hhd.trans_le (min_le_left _ _)
    have hth : t + h ∈ Icc (0 : Real) T := by
      have hhT : h < T - t := hhd.trans_le (min_le_right _ _)
      exact ⟨by linarith [ht.1], by linarith⟩
    have hden : 0 < A (t + h) j k - A t j k := by
      have hprod :
          0 < h⁻¹ * (A (t + h) j k - A t j k) :=
        (by linarith)
      exact pos_of_mul_pos_right hprod (inv_nonneg.mpr hh.le)
    apply calendarLimit_finiteDifference_mem_epsilon N initial hT U K hK omega A X hA hconverges q hq E hpoly ht
        epsilon.2 hhpos hth hden
    refine ⟨rNear, fun r hr l y hy hused => ?_⟩
    exact hrNear (q r) (hr.trans (hq.id_le r)) h hhpos hhNear
      j k l y hy hused
  exact N.ae_derivativeRatio_mem_fluidPolicyCorrespondence
    (TimeMeasure := mu) U j k X
    (fun s => A s j k)
    (fun s => calendarLimitAction A E j k s)
    hAdiff hActionDiff hfinite

theorem calendarPoissonExecutionFrom_stochasticFluidExtension :
    N.StochasticFluidExtensionReadback
      (N.calendarPoissonExecutionFrom initial) := by
  intro T hT x0 U K hK omega A X hX0 hA hconverges
  obtain ⟨q, hq, E, hEcont, hpoly⟩ :=
    exists_calendarPolygonalAllocation_limit N initial hT U K hK omega A X hA hconverges
  have hinput : IsFluidInput T A :=
    calendarInput_isFluidInput N initial hT U K omega A X hA hconverges
  have hraw :
      (N.calendarPoissonExecutionFrom initial).AllocationConvergesOn T U K q omega E :=
    calendarAllocation_raw_converges N initial hT U K hK omega A X hA hconverges q hq E hpoly
  have hE0 : forall i j k, E 0 i j k = 0 :=
    calendarLimit_allocation_initial N initial hT U K omega q E hpoly
  have hEincompat :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i j k, Not (N.compatible i j) -> E t i j k = 0 :=
    calendarLimit_allocation_incompatible N initial hT U K omega q E hpoly
  have hstate :
      forall t, t ∈ Icc (0 : Real) T -> IsFluidState (X t) :=
    calendarLimit_state_in_simplex N initial hT U K hK omega A X hA hconverges
  have hbalance :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i,
          X t i = x0 i
            + (Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun l : Buffer => E t l j i)
            - (Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun k : Buffer => E t i j k) :=
    calendarLimit_balance N initial hT x0 U K hK omega A X hX0 hA hconverges q hq E hpoly
  have hEac :
      forall i j k,
        AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T :=
    calendarLimit_allocation_ac N initial hT U K hK omega A X hA hconverges q hq E hpoly
  have hXac :
      forall i, AbsolutelyContinuousOnInterval (fun t => X t i) 0 T :=
    calendarLimit_state_ac N initial hT U K omega A X hA hconverges
  have hinc :
      forall i j k s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T -> s <= t ->
          0 <= E t i j k - E s i j k /\
          E t i j k - E s i j k <= A t j k - A s j k :=
    calendarLimit_allocation_increment N initial hT U K omega A q hq E hconverges.1 hraw
  have hbalanceRestricted :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i,
          X t i = x0 i
            + (Finset.univ.sum fun j : Server =>
                Finset.sum (N.buffersOf j) fun l => E t l j i)
            - (Finset.sum (N.serversOf i) fun j =>
                Finset.univ.sum fun k : Buffer => E t i j k) :=
    calendarLimit_balance_restricted N x0 X E hbalance hEincompat
  let Xclip : FluidStatePath Buffer :=
    fun t i => X (Set.projIcc (0 : Real) T hT.le t) i
  have hXclip_eq (t : Real) (ht : t ∈ Icc (0 : Real) T) :
      Xclip t = X t := by
    funext i
    simp only [Xclip, Set.projIcc_of_mem hT.le ht]
  have hXclipMeas (i : Buffer) : Measurable (fun t => Xclip t i) := by
    apply Continuous.measurable
    exact (hXac i).continuousOn.comp_continuous
      (continuous_subtype_val.comp
        (continuous_projIcc (a := (0 : Real)) (b := T)))
      (fun t => by
        simpa [uIcc_of_le hT.le] using
          (Set.projIcc (0 : Real) T hT.le t).property)
  let p : FluidActionFractions Buffer Server :=
    fun t j k =>
      N.verifiedPatchedFluidPolicy U j k Xclip
        (fun s => A s j k)
        (fun s => calendarLimitAction A E j k s) t
  have hpositive (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => 0 < deriv (fun s => A s j k) t ->
          Membership.mem
            (N.fluidPolicyCorrespondence U j k (Xclip t))
            (fun a =>
              deriv (fun s => calendarLimitAction A E j k s a) t /
                deriv (fun s => A s j k) t))
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    have hp :=
      calendarLimit_positive_policy_ae N initial hT U K hK omega A X hA hconverges q hq E hpoly hEac j k
    filter_upwards [ae_restrict_mem measurableSet_Icc, hp] with t ht hpt
    simpa only [hXclip_eq t ht] using hpt
  have hzeroE :=
    calendarLimit_zero_derivative_ae hT A E hA hEac hinc
  have hAdiff (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => DifferentiableAt Real (fun s => A s j k) t)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    have hv := (hA j k).ae_differentiableAt.filter_mono
      (MeasureTheory.ae_restrict_le
        (μ := volume) (s := Icc (0 : Real) T))
    filter_upwards [ae_restrict_mem measurableSet_Icc, hv] with t ht hdt
    exact hdt (by simpa [uIcc_of_le hT.le] using ht)
  have hEdiff (i : Buffer) (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => DifferentiableAt Real (fun s => E s i j k) t)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    have hv := (hEac i j k).ae_differentiableAt.filter_mono
      (MeasureTheory.ae_restrict_le
        (μ := volume) (s := Icc (0 : Real) T))
    filter_upwards [ae_restrict_mem measurableSet_Icc, hv] with t ht hdt
    exact hdt (by simpa [uIcc_of_le hT.le] using ht)
  have hzero :
      Filter.Eventually
        (fun t => forall j k, deriv (fun s => A s j k) t = 0 ->
          forall a,
            deriv (fun s => calendarLimitAction A E j k s a) t = 0)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    filter_upwards [hzeroE,
      ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => hAdiff j k)),
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
        ae_all_iff.mpr (fun k => hEdiff i j k)))] with
        t hzeroEt hAdifft hEdifft
    intro j k hAzero a
    cases a with
    | some i =>
        simpa only [calendarLimitAction] using hzeroEt j k hAzero i
    | none =>
        have hA0 : HasDerivAt (fun s => A s j k) 0 t := by
          simpa only [hAzero] using (hAdifft j k).hasDerivAt
        have hsum0 :
            HasDerivAt
              (fun s => Finset.univ.sum fun i : Buffer => E s i j k)
              0 t := by
          have hs :=
            HasDerivAt.fun_sum (u := Finset.univ) fun i hi => by
              simpa only [hzeroEt j k hAzero i] using
                (hEdifft i j k).hasDerivAt
          exact hs.congr_deriv (by simp)
        change
          deriv
            ((fun s => A s j k) -
              (fun s => Finset.univ.sum fun i : Buffer => E s i j k)) t = 0
        simpa using (hA0.sub hsum0).deriv
  have hAnonneg (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => 0 <= deriv (fun s => A s j k) t)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    rw [<- Measure.restrict_congr_set
      (Ioo_ae_eq_Icc (μ := volume) (a := (0 : Real)) (b := T))]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [<- derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact (hinput.2.1 j k).derivWithin_nonneg
  have hAllocationRule (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => forall a,
          deriv (fun s => calendarLimitAction A E j k s a) t =
            deriv (fun s => A s j k) t * p t j k a)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    exact N.verifiedPatchedFluidPolicy_allocation_rule_ae
      (TimeMeasure := volume.restrict (Icc (0 : Real) T))
      U j k Xclip
      (fun s => A s j k)
      (fun s => calendarLimitAction A E j k s)
      (hAnonneg j k) (hpositive j k)
      (by
        filter_upwards [hzero] with t hzt
        exact hzt j k)
  refine ⟨q, hq, ?_⟩
  refine ⟨{
    horizon_pos := hT
    input_valid := hinput
    X := X
    E := E
    p := p
    state_ac := hXac
    allocation_ac := hEac
    state_initial := hX0
    allocation_initial := hE0
    allocation_incompatible := hEincompat
    state_in_simplex := hstate
    fractions_measurable := ?_
    fractions_in_simplex := ?_
    fractions_incompatible := ?_
    policy_rule := ?_
    allocation_rule := ?_
    balance := hbalanceRestricted
  }, rfl, ?_⟩
  · intro j k a
    exact N.verifiedPatchedFluidPolicy_measurable
      U j k Xclip
      (fun s => A s j k)
      (fun s => calendarLimitAction A E j k s)
      hXclipMeas a
  · intro t ht j k
    apply N.verifiedPatchedFluidPolicy_isActionDistribution
    rw [hXclip_eq t ht]
    exact hstate t ht
  · intro t ht j k i hi
    apply N.verifiedPatchedFluidPolicy_incompatible_zero
    · rw [hXclip_eq t ht]
      exact hstate t ht
    · exact hi
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro j k
    rw [show X t = Xclip t by exact (hXclip_eq t ht).symm]
    exact N.verifiedPatchedFluidPolicy_mem U j k Xclip
      (fun s => A s j k)
      (fun s => calendarLimitAction A E j k s) t
      (by
        rw [hXclip_eq t ht]
        exact hstate t ht)
  · filter_upwards [
      ae_all_iff.mpr (fun j =>
        ae_all_iff.mpr (fun k => hAllocationRule j k))] with t ht
    intro i j k hij
    simpa only [calendarLimitAction] using ht j k (some i)
  · exact hraw

/-- The three clauses of `lem:fms-existence` for the totalized
calendar-time Poisson execution from an arbitrary initial-state family. -/
theorem calendarPoissonExecutionFrom_fluidModelExistenceAndConsistency :
    N.FluidModelExistenceAndConsistencyReadback
      (N.calendarPoissonExecutionFrom initial) := by
  exact And.intro (deterministicFluidModelExistence N)
    (And.intro
      (N.calendarPoissonExecutionFrom_stochasticFluidExtension initial)
      (N.calendarPoissonExecutionFrom_subsequentialInput initial))

end


end Network

end StateDepMOR
