import StateDepMOR.FiniteQueueLongRun
import StateDepMOR.Asymptotics

/-!
# Initial-law-dependent finite-chain performance

The event-epoch loss of a stationary policy can depend on its initial
recurrent class.  This module derives the long-run loss from an explicit
initial PMF at every system size.  It never identifies that loss with an
arbitrary invariant PMF.
-/

open Filter

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

variable (N : Network Buffer Server)

/-- An explicit initial queue law for every positive system size. -/
structure InitialLawFamily (N : Network Buffer Server) where
  law : forall K : PNat, PMF (JobState Buffer (K : Nat))

/-- Deterministic initial queue states viewed as initial PMFs. -/
noncomputable def InitialLawFamily.pure
    (state : forall K : PNat, JobState Buffer (K : Nat)) :
    N.InitialLawFamily where
  law := fun K => PMF.pure (state K)

/-- The invariant PMF reached by the Cesaro occupation laws from `initial`.

The choice is made only among PMFs satisfying the full initial-dependent
convergence theorem, rather than among all invariant PMFs.
-/
noncomputable def initialCesaroLimitLaw
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat) :
    PMF (JobState Buffer (K : Nat)) :=
  Classical.choose
    (N.exists_initialCesaroLimitPMF (U K) (initial.law K))

private theorem initialCesaroLimitLaw_spec
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat) :
    N.IsInvariantPMF (U K) (N.initialCesaroLimitLaw U initial K) /\
      (forall x : JobState Buffer (K : Nat),
        Tendsto
          (fun n =>
            (N.occupationPMF (U K) (initial.law K) n x).toReal)
          atTop
          (nhds ((N.initialCesaroLimitLaw U initial K x).toReal))) /\
      Tendsto
        (fun n => N.finiteHorizonAverageWaste
          (U K) (initial.law K) n)
        atTop
        (nhds
          (N.stationaryOneStepWaste
            (U K) (N.initialCesaroLimitLaw U initial K))) :=
  Classical.choose_spec
    (N.exists_initialCesaroLimitPMF (U K) (initial.law K))

theorem initialCesaroLimitLaw_isInvariant
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat) :
    N.IsInvariantPMF (U K) (N.initialCesaroLimitLaw U initial K) :=
  (N.initialCesaroLimitLaw_spec U initial K).1

theorem occupationPMF_tendsto_initialCesaroLimitLaw
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat)
    (x : JobState Buffer (K : Nat)) :
    Tendsto
      (fun n => (N.occupationPMF (U K) (initial.law K) n x).toReal)
      atTop
      (nhds ((N.initialCesaroLimitLaw U initial K x).toReal)) :=
  (N.initialCesaroLimitLaw_spec U initial K).2.1 x

/-- A PMF can equal the selected limit only by being the coordinatewise
Cesaro limit from the same explicit initial law. -/
theorem initialCesaroLimitLaw_eq_of_coordinate_tendsto
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat)
    (limitLaw : PMF (JobState Buffer (K : Nat)))
    (hlimit :
      forall x : JobState Buffer (K : Nat),
        Tendsto
          (fun n =>
            (N.occupationPMF (U K) (initial.law K) n x).toReal)
          atTop (nhds ((limitLaw x).toReal))) :
    N.initialCesaroLimitLaw U initial K = limitLaw := by
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff'
    ((N.initialCesaroLimitLaw U initial K).apply_ne_top x)
    (limitLaw.apply_ne_top x)).mp
  exact tendsto_nhds_unique
    (N.occupationPMF_tendsto_initialCesaroLimitLaw U initial K x)
    (hlimit x)

theorem nStepLaw_eq_of_isInvariant {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K))
    (hinvariant : N.IsInvariantPMF U initial) :
    forall n, N.nStepLaw U initial n = initial := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [N.nStepLaw_succ, ih]
      exact hinvariant

theorem occupationPMF_eq_of_isInvariant {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K))
    (hinvariant : N.IsInvariantPMF U initial) (n : Nat) :
    N.occupationPMF U initial n = initial := by
  unfold occupationPMF
  have hlaw :
      (fun k : Fin (n + 1) => N.nStepLaw U initial k) =
        (fun _ => initial) := by
    funext k
    exact N.nStepLaw_eq_of_isInvariant U initial hinvariant k
  rw [hlaw, PMF.bind_const]

theorem initialCesaroLimitLaw_eq_of_isInvariant
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat)
    (hinvariant : N.IsInvariantPMF (U K) (initial.law K)) :
    N.initialCesaroLimitLaw U initial K = initial.law K := by
  apply PMF.ext
  intro x
  apply (ENNReal.toReal_eq_toReal_iff'
    ((N.initialCesaroLimitLaw U initial K).apply_ne_top x)
    ((initial.law K).apply_ne_top x)).mp
  have hlimit :=
    N.occupationPMF_tendsto_initialCesaroLimitLaw U initial K x
  have hconstant :
      Tendsto (fun _ : Nat => (initial.law K x).toReal)
        atTop (nhds ((initial.law K x).toReal)) :=
    tendsto_const_nhds
  have hsame :
      (fun n : Nat =>
        (N.occupationPMF (U K) (initial.law K) n x).toReal) =
        (fun _ : Nat => (initial.law K x).toReal) := by
    funext n
    rw [N.occupationPMF_eq_of_isInvariant
      (U K) (initial.law K) hinvariant n]
  rw [hsame] at hlimit
  exact tendsto_nhds_unique hlimit hconstant

/-- Initial-law-dependent long-run average waste at system size `K`. -/
noncomputable def initialLongRunLoss
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat) : Real :=
  N.stationaryOneStepWaste
    (U K) (N.initialCesaroLimitLaw U initial K)

@[simp]
theorem initialLongRunLoss_eq_stationaryOneStepWaste
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat) :
    N.initialLongRunLoss U initial K =
      N.stationaryOneStepWaste
        (U K) (N.initialCesaroLimitLaw U initial K) :=
  rfl

/-- The finite-horizon event-epoch averages converge to the loss selected by
their explicit initial law. -/
theorem finiteHorizonAverageWaste_tendsto_initialLongRunLoss
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat) :
    Tendsto
      (fun n => N.finiteHorizonAverageWaste
        (U K) (initial.law K) n)
      atTop
      (nhds (N.initialLongRunLoss U initial K)) :=
  (N.initialCesaroLimitLaw_spec U initial K).2.2

theorem initialLongRunLoss_nonneg
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat) :
    0 <= N.initialLongRunLoss U initial K :=
  N.stationaryOneStepWaste_nonneg
    (U K) (N.initialCesaroLimitLaw U initial K)

theorem initialLongRunLoss_le_one
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat) :
    N.initialLongRunLoss U initial K <= 1 :=
  N.stationaryOneStepWaste_le_one
    (U K) (N.initialCesaroLimitLaw U initial K)

theorem initialLongRunLoss_eq_of_isInvariant
    (U : N.DeterministicPolicySequence)
    (initial : N.InitialLawFamily) (K : PNat)
    (hinvariant : N.IsInvariantPMF (U K) (initial.law K)) :
    N.initialLongRunLoss U initial K =
      N.stationaryOneStepWaste (U K) (initial.law K) := by
  rw [N.initialLongRunLoss_eq_stationaryOneStepWaste,
    N.initialCesaroLimitLaw_eq_of_isInvariant U initial K hinvariant]

/-- Concrete performance semantics for one explicit family of initial laws. -/
noncomputable def InitialLawFamily.toPerformanceSemantics
    (initial : N.InitialLawFamily) : PerformanceSemantics N where
  loss := fun U K => N.initialLongRunLoss U initial K
  loss_nonneg := fun U K => N.initialLongRunLoss_nonneg U initial K
  loss_le_one := fun U K => N.initialLongRunLoss_le_one U initial K

@[simp]
theorem InitialLawFamily.toPerformanceSemantics_loss
    (initial : N.InitialLawFamily)
    (U : N.DeterministicPolicySequence) (K : PNat) :
    initial.toPerformanceSemantics.loss U K =
      N.initialLongRunLoss U initial K :=
  rfl

/-- A strict Hall imbalance bounds the initial-law-dependent loss away from
zero at every system size. -/
theorem initialLongRunLoss_ge_cutImbalance
    (initial : N.InitialLawFamily)
    (U : N.DeterministicPolicySequence)
    (jset : Finset Server)
    (K : PNat) :
    N.netServiceRate jset - N.netArrivalRate jset <=
      N.initialLongRunLoss U initial K := by
  exact N.stationaryOneStepWaste_ge_netImbalance
    (U K) (N.initialCesaroLimitLaw U initial K)
    (N.initialCesaroLimitLaw_isInvariant U initial K) jset

theorem initialLongRunLoss_isOmegaOneDivSq_of_strict_cutImbalance
    (initial : N.InitialLawFamily)
    (U : N.DeterministicPolicySequence)
    (jset : Finset Server)
    (hstrict :
      N.netArrivalRate jset < N.netServiceRate jset) :
    IsOmegaOneDivSq (N.initialLongRunLoss U initial) := by
  let c := N.netServiceRate jset - N.netArrivalRate jset
  have hc : 0 < c := sub_pos.mpr hstrict
  refine Exists.intro c (And.intro hc (Filter.Eventually.of_forall ?_))
  intro K
  have hK : (1 : Real) <= (K : Real) := by
    exact_mod_cast PNat.pos K
  have hKsq : (1 : Real) <= (K : Real) ^ 2 := by
    nlinarith
  have hKsqPos : 0 < (K : Real) ^ 2 :=
    lt_of_lt_of_le zero_lt_one hKsq
  calc
    c / (K : Real) ^ 2 <= c := by
      apply (div_le_iff₀ hKsqPos).2
      nlinarith
    _ <= N.initialLongRunLoss U initial K :=
      N.initialLongRunLoss_ge_cutImbalance initial U jset K

theorem initialThroughputLossExponent_eq_zero_of_strict_cutImbalance
    (initial : N.InitialLawFamily)
    (U : N.DeterministicPolicySequence)
    (jset : Finset Server)
    (hstrict :
      N.netArrivalRate jset < N.netServiceRate jset) :
    initial.toPerformanceSemantics.throughputLossExponent U = 0 := by
  exact
    initial.toPerformanceSemantics
      |>.throughputLossExponent_eq_zero_of_isOmegaOneDivSq U
        (N.initialLongRunLoss_isOmegaOneDivSq_of_strict_cutImbalance
          initial U jset hstrict)

end Network

end StateDepMOR
