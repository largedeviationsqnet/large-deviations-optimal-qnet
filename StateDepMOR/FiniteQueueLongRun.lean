import StateDepMOR.FiniteQueueBalance
import StateDepMOR.FiniteQueueStationarity
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.Sequences

/-!
# Long-run event-epoch laws for the finite queue

This module builds the event-epoch laws from an explicit initial PMF and
their finite Cesaro occupation laws.  The limit law below depends on that
initial PMF: no arbitrary invariant law is identified with the long-run
loss.
-/

open scoped BigOperators ENNReal
open Filter Finset Function

noncomputable section

namespace StateDepMOR

namespace FiniteMarkovChain

universe u

variable {A : Type u} [Fintype A] [Nonempty A]

/-- The Markov operator on real observables. -/
private def expectationOperator (P : A -> PMF A) :
    Module.End Real (A -> Real) where
  toFun g x := Finset.univ.sum (fun y => (P x y).toReal * g y)
  map_add' g h := by
    funext x
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    change (P x y).toReal * (c * g y) =
      c * ((P x y).toReal * g y)
    ring

@[simp]
private theorem expectationOperator_apply (P : A -> PMF A)
    (g : A -> Real) (x : A) :
    expectationOperator P g x =
      Finset.univ.sum (fun y => (P x y).toReal * g y) :=
  rfl

private theorem expectationOperator_lipschitz (P : A -> PMF A) :
    LipschitzWith 1 (expectationOperator P) := by
  apply LipschitzWith.of_dist_le_mul
  intro g h
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [<- (expectationOperator P).map_sub]
  apply (pi_norm_le_iff_of_nonempty _).2
  intro x
  calc
    ‖expectationOperator P (g - h) x‖ <=
        Finset.univ.sum
          (fun y => ‖(P x y).toReal * (g - h) y‖) := by
      exact norm_sum_le Finset.univ
        (fun y => (P x y).toReal * (g - h) y)
    _ = Finset.univ.sum
          (fun y => (P x y).toReal * ‖(g - h) y‖) := by
      apply Finset.sum_congr rfl
      intro y _
      rw [norm_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    _ <= Finset.univ.sum
          (fun y => (P x y).toReal * ‖g - h‖) := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left
        (norm_le_pi_norm (g - h) y) ENNReal.toReal_nonneg
    _ = ‖g - h‖ := by
      rw [<- Finset.sum_mul, PMF.sum_toReal, one_mul]

/-- A contraction on a finite-dimensional real normed space has convergent
Cesaro orbits. -/
private theorem finiteDimensional_mean_ergodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    (f : Module.End Real E) (hf : LipschitzWith 1 f) (x : E) :
    Exists (fun z : E =>
      And (f z = z)
        (Tendsto (fun n => birkhoffAverage Real f id n x)
          atTop (nhds z))) := by
  let fixed : Submodule Real E := f.eqLocus 1
  let differences : Submodule Real E := LinearMap.range (f - 1)
  have hdisjoint : Disjoint fixed differences := by
    rw [Submodule.disjoint_def]
    intro z hzfixed hzdifference
    have hzfix : f z = z := hzfixed
    rcases hzdifference with ⟨y, hy⟩
    change f y - y = z at hy
    have hfy : f y = y + z := sub_eq_iff_eq_add'.mp hy
    have hiterate : forall n : Nat,
        (f : E -> E)^[n] y = y + (n : Real) • z := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          rw [Function.iterate_succ_apply', ih, f.map_add, f.map_smul,
            hfy, hzfix]
          simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
          abel
    have hbound (n : Nat) : ‖(f : E -> E)^[n] y‖ <= ‖y‖ := by
      have h := (hf.iterate n).dist_le_mul y 0
      simpa [iterate_map_zero] using h
    by_contra hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * ‖y‖ / ‖z‖)
    have hnlt : 2 * ‖y‖ < (n : Real) * ‖z‖ :=
      (div_lt_iff₀ hzpos).mp hn
    have hnle : (n : Real) * ‖z‖ <= 2 * ‖y‖ := by
      calc
        (n : Real) * ‖z‖ = ‖(n : Real) • z‖ := by
          rw [norm_smul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
        _ = ‖(y + (n : Real) • z) - y‖ := by
          congr 1
          abel
        _ <= ‖y + (n : Real) • z‖ + ‖y‖ :=
          norm_sub_le _ _
        _ <= ‖y‖ + ‖y‖ := by
          exact add_le_add (by simpa [hiterate n] using hbound n) le_rfl
        _ = 2 * ‖y‖ := by
          ring
    linarith
  have hdim :
      Module.finrank Real E <=
        Module.finrank Real fixed + Module.finrank Real differences := by
    have h := (f - 1).finrank_range_add_finrank_ker
    have hfixed : fixed = LinearMap.ker (f - 1) :=
      LinearMap.eqLocus_eq_ker_sub f 1
    have hrange : differences = LinearMap.range (f - 1) := rfl
    rw [hfixed, hrange]
    simpa [add_comm] using h.symm.le
  have hcompl : IsCompl fixed differences :=
    (Submodule.isCompl_iff_disjoint fixed differences hdim).2 hdisjoint
  let projectionLinear := fixed.projectionOnto differences hcompl
  let projection := LinearMap.toContinuousLinearMap projectionLinear
  refine Exists.intro (projection x) (And.intro (projection x).property ?_)
  apply f.tendsto_birkhoffAverage_of_ker_subset_closure hf projection
  next =>
    intro z
    exact fixed.projectionOnto_apply_left hcompl z
  next =>
    intro z hz
    apply subset_closure
    change z ∈ LinearMap.ker projectionLinear at hz
    rw [fixed.ker_projectionOnto hcompl] at hz
    exact hz

/-- The Cesaro expectations of every real reward converge for a finite
Markov kernel. -/
theorem tendsto_cesaro_expectation
    (P : A -> PMF A) (initial : PMF A) (reward : A -> Real) :
    Exists (fun limit : Real =>
      Tendsto
        (fun n : Nat =>
          (n : Real)⁻¹ *
            Finset.univ.sum (fun x =>
              (initial x).toReal *
                (Finset.range n).sum (fun k =>
                  ((expectationOperator P : (A -> Real) -> (A -> Real))^[k]
                    reward) x)))
        atTop (nhds limit)) := by
  cases finiteDimensional_mean_ergodic
      (expectationOperator P) (expectationOperator_lipschitz P) reward with
  | intro limitFunction hlimit =>
      refine Exists.intro
        (Finset.univ.sum
          (fun x => (initial x).toReal * limitFunction x)) ?_
      have hmean := hlimit.2
      have hcoord (x : A) :
          Tendsto
            (fun n =>
              birkhoffAverage Real (expectationOperator P) id n reward x)
            atTop (nhds (limitFunction x)) := by
        exact (continuous_apply x).continuousAt.tendsto.comp hmean
      have hsum :
          Tendsto
            (fun n =>
              Finset.univ.sum (fun x =>
                (initial x).toReal *
                  birkhoffAverage Real (expectationOperator P) id n reward x))
            atTop
            (nhds (Finset.univ.sum
              (fun x => (initial x).toReal * limitFunction x))) := by
        apply tendsto_finset_sum
        intro x _
        exact tendsto_const_nhds.mul (hcoord x)
      simpa [birkhoffAverage, birkhoffSum, Finset.mul_sum, mul_assoc,
        mul_comm, mul_left_comm] using hsum

end FiniteMarkovChain

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

variable (N : Network Buffer Server)

/-- The queue-state law after `n` event epochs from an explicit initial
law. -/
noncomputable def nStepLaw {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) :
    Nat -> PMF (JobState Buffer K)
  | 0 => initial
  | n + 1 =>
      (nStepLaw U initial n).bind (N.transitionPMF U)

@[simp]
theorem nStepLaw_zero {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) :
    N.nStepLaw U initial 0 = initial :=
  rfl

@[simp]
theorem nStepLaw_succ {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat) :
    N.nStepLaw U initial (n + 1) =
      (N.nStepLaw U initial n).bind (N.transitionPMF U) :=
  rfl

/-- The average of the first `n + 1` queue-state laws. -/
noncomputable def occupationPMF {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat) :
    PMF (JobState Buffer K) :=
  (PMF.uniformOfFintype (Fin (n + 1))).bind
    (fun k => N.nStepLaw U initial k)

/-- Expected waste averaged over the first `n + 1` event epochs. -/
noncomputable def finiteHorizonAverageWaste {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat) : Real :=
  (1 / ((n : Real) + 1)) *
    Finset.sum (Finset.range (n + 1))
      (fun k => N.stationaryOneStepWaste U (N.nStepLaw U initial k))

private theorem uniformFin_toReal (n : Nat) (k : Fin (n + 1)) :
    (PMF.uniformOfFintype (Fin (n + 1)) k).toReal =
      1 / ((n : Real) + 1) := by
  rw [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv]
  rw [ENNReal.toReal_natCast]
  simp [Nat.cast_add, one_div]

@[simp]
theorem occupationPMF_toReal {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat)
    (x : JobState Buffer K) :
    (N.occupationPMF U initial n x).toReal =
      (1 / ((n : Real) + 1)) *
        (Finset.range (n + 1)).sum
          (fun k => (N.nStepLaw U initial k x).toReal) := by
  rw [occupationPMF, PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun k _ =>
    ENNReal.mul_ne_top
      ((PMF.uniformOfFintype (Fin (n + 1))).apply_ne_top k)
      ((N.nStepLaw U initial k).apply_ne_top x))]
  simp_rw [ENNReal.toReal_mul, uniformFin_toReal]
  rw [Fin.sum_univ_eq_sum_range
    (fun k =>
      (1 / ((n : Real) + 1)) *
        (N.nStepLaw U initial k x).toReal)
    (n + 1)]
  rw [Finset.mul_sum]

theorem occupationPMF_bind {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat) :
    (N.occupationPMF U initial n).bind (N.transitionPMF U) =
      (PMF.uniformOfFintype (Fin (n + 1))).bind
        (fun k => N.nStepLaw U initial (k + 1)) := by
  rw [occupationPMF, PMF.bind_bind]
  congr 1

private theorem shift_sum_sub {G : Type*} [AddCommGroup G]
    (f : Nat -> G) (n : Nat) :
    (Finset.range n).sum (fun k => f (k + 1)) -
        (Finset.range n).sum f =
      f n - f 0 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      calc
        (Finset.range n).sum (fun k => f (k + 1)) + f (n + 1) -
            ((Finset.range n).sum f + f n) =
          ((Finset.range n).sum (fun k => f (k + 1)) -
              (Finset.range n).sum f) +
            (f (n + 1) - f n) := by
              abel
        _ = f (n + 1) - f 0 := by
          rw [ih]
          abel

/-- The one-step defect of the occupation law is exactly its endpoint
correction. -/
theorem occupationPMF_bind_sub_toReal {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat)
    (x : JobState Buffer K) :
    (((N.occupationPMF U initial n).bind
        (N.transitionPMF U)) x).toReal -
        (N.occupationPMF U initial n x).toReal =
      (1 / ((n : Real) + 1)) *
        ((N.nStepLaw U initial (n + 1) x).toReal -
          (initial x).toReal) := by
  rw [N.occupationPMF_bind U initial n]
  rw [show
    (((PMF.uniformOfFintype (Fin (n + 1))).bind
      (fun k => N.nStepLaw U initial (k + 1))) x).toReal =
        (1 / ((n : Real) + 1)) *
          (Finset.range (n + 1)).sum
            (fun k => (N.nStepLaw U initial (k + 1) x).toReal) by
    rw [PMF.bind_apply, tsum_fintype]
    rw [ENNReal.toReal_sum (fun k _ =>
      ENNReal.mul_ne_top
        ((PMF.uniformOfFintype (Fin (n + 1))).apply_ne_top k)
        ((N.nStepLaw U initial (k + 1)).apply_ne_top x))]
    simp_rw [ENNReal.toReal_mul, uniformFin_toReal]
    rw [Fin.sum_univ_eq_sum_range
      (fun k =>
        (1 / ((n : Real) + 1)) *
          (N.nStepLaw U initial (k + 1) x).toReal)
      (n + 1)]
    rw [Finset.mul_sum]]
  rw [N.occupationPMF_toReal U initial n x]
  rw [<- mul_sub]
  congr 1
  exact shift_sum_sub
    (fun k => (N.nStepLaw U initial k x).toReal) (n + 1)

/-- Finite-horizon waste is expectation under the matching occupation
law. -/
theorem finiteHorizonAverageWaste_eq_stationaryOneStepWaste {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat) :
    N.finiteHorizonAverageWaste U initial n =
      N.stationaryOneStepWaste U (N.occupationPMF U initial n) := by
  unfold finiteHorizonAverageWaste stationaryOneStepWaste occupationPMF
  rw [PMF.sum_bind_real]
  simp_rw [uniformFin_toReal]
  rw [Fin.sum_univ_eq_sum_range
    (fun k =>
      (1 / ((n : Real) + 1)) *
        Finset.univ.sum (fun x =>
          (N.nStepLaw U initial k x).toReal * N.oneStepWaste U x))
    (n + 1)]
  rw [Finset.mul_sum]

theorem finiteHorizonAverageWaste_nonneg {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat) :
    0 <= N.finiteHorizonAverageWaste U initial n := by
  rw [N.finiteHorizonAverageWaste_eq_stationaryOneStepWaste U initial n]
  exact N.stationaryOneStepWaste_nonneg U (N.occupationPMF U initial n)

theorem finiteHorizonAverageWaste_le_one {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat) :
    N.finiteHorizonAverageWaste U initial n <= 1 := by
  rw [N.finiteHorizonAverageWaste_eq_stationaryOneStepWaste U initial n]
  exact N.stationaryOneStepWaste_le_one U (N.occupationPMF U initial n)

private theorem nStepLaw_expectation {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (reward : JobState Buffer K -> Real)
    (n : Nat) :
    Finset.univ.sum (fun x =>
      (N.nStepLaw U initial n x).toReal * reward x) =
      Finset.univ.sum (fun x =>
        (initial x).toReal *
          ((FiniteMarkovChain.expectationOperator
              (N.transitionPMF U))^[n] reward) x) := by
  induction n generalizing reward with
  | zero =>
      simp
  | succ n ih =>
      rw [N.nStepLaw_succ U initial n, PMF.sum_bind_real]
      rw [ih]
      rw [Function.iterate_succ_apply]
      rfl

private theorem finiteHorizonAverageWaste_eq_operator_average {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat) :
    N.finiteHorizonAverageWaste U initial n =
      (1 / ((n : Real) + 1)) *
        Finset.univ.sum (fun x =>
          (initial x).toReal *
            (Finset.range (n + 1)).sum (fun k =>
              ((FiniteMarkovChain.expectationOperator
                  (N.transitionPMF U))^[k] (N.oneStepWaste U)) x)) := by
  unfold finiteHorizonAverageWaste stationaryOneStepWaste
  congr 1
  calc
    (Finset.range (n + 1)).sum (fun k =>
        Finset.univ.sum (fun x =>
          (N.nStepLaw U initial k x).toReal * N.oneStepWaste U x)) =
      (Finset.range (n + 1)).sum (fun k =>
        Finset.univ.sum (fun x =>
          (initial x).toReal *
            ((FiniteMarkovChain.expectationOperator
                (N.transitionPMF U))^[k] (N.oneStepWaste U)) x)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact N.nStepLaw_expectation U initial (N.oneStepWaste U) k
    _ = Finset.univ.sum (fun x =>
        (initial x).toReal *
          (Finset.range (n + 1)).sum (fun k =>
            ((FiniteMarkovChain.expectationOperator
                (N.transitionPMF U))^[k] (N.oneStepWaste U)) x)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]

private theorem occupationExpectation_eq_operator_average {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K))
    (reward : JobState Buffer K -> Real) (n : Nat) :
    Finset.univ.sum (fun x =>
      (N.occupationPMF U initial n x).toReal * reward x) =
      (1 / ((n : Real) + 1)) *
        Finset.univ.sum (fun x =>
          (initial x).toReal *
            (Finset.range (n + 1)).sum (fun k =>
              ((FiniteMarkovChain.expectationOperator
                  (N.transitionPMF U))^[k] reward) x)) := by
  unfold occupationPMF
  rw [PMF.sum_bind_real]
  simp_rw [uniformFin_toReal]
  rw [Fin.sum_univ_eq_sum_range
    (fun k =>
      (1 / ((n : Real) + 1)) *
        Finset.univ.sum (fun x =>
          (N.nStepLaw U initial k x).toReal * reward x))
    (n + 1)]
  rw [<- Finset.mul_sum]
  congr 1
  calc
    (Finset.range (n + 1)).sum (fun k =>
        Finset.univ.sum (fun x =>
          (N.nStepLaw U initial k x).toReal * reward x)) =
      (Finset.range (n + 1)).sum (fun k =>
        Finset.univ.sum (fun x =>
          (initial x).toReal *
            ((FiniteMarkovChain.expectationOperator
                (N.transitionPMF U))^[k] reward) x)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact N.nStepLaw_expectation U initial reward k
    _ = Finset.univ.sum (fun x =>
        (initial x).toReal *
          (Finset.range (n + 1)).sum (fun k =>
            ((FiniteMarkovChain.expectationOperator
                (N.transitionPMF U))^[k] reward) x)) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]

private theorem exists_occupationExpectation_limit {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K))
    (reward : JobState Buffer K -> Real) :
    Exists (fun limit : Real =>
      Tendsto
        (fun n =>
          Finset.univ.sum (fun x =>
            (N.occupationPMF U initial n x).toReal * reward x))
        atTop (nhds limit)) := by
  letI : Nonempty (JobState Buffer K) :=
    ⟨initial.support_nonempty.choose⟩
  cases FiniteMarkovChain.tendsto_cesaro_expectation
      (N.transitionPMF U) initial reward with
  | intro limit hlimit =>
      refine Exists.intro limit ?_
      have hshift := hlimit.comp (Filter.tendsto_add_atTop_nat 1)
      apply hshift.congr'
      filter_upwards with n
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, one_div]
        using
          (N.occupationExpectation_eq_operator_average
            U initial reward n).symm

/-- For every explicit initial law, finite-horizon average waste has a
limit. -/
theorem exists_finiteHorizonAverageWaste_limit {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) :
    Exists (fun limit : Real =>
      Tendsto (fun n => N.finiteHorizonAverageWaste U initial n)
        atTop (nhds limit)) := by
  letI : Nonempty (JobState Buffer K) :=
    ⟨initial.support_nonempty.choose⟩
  cases FiniteMarkovChain.tendsto_cesaro_expectation
      (N.transitionPMF U) initial (N.oneStepWaste U) with
  | intro limit hlimit =>
      refine Exists.intro limit ?_
      have hshift := hlimit.comp (Filter.tendsto_add_atTop_nat 1)
      simpa [Function.comp_def, Nat.cast_add, Nat.cast_one, one_div,
        N.finiteHorizonAverageWaste_eq_operator_average U initial] using hshift

private def occupationSimplex {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat) :
    stdSimplex Real (JobState Buffer K) :=
  ⟨fun x => (N.occupationPMF U initial n x).toReal,
    And.intro
      (fun x => ENNReal.toReal_nonneg)
      (PMF.sum_toReal (N.occupationPMF U initial n))⟩

@[simp]
private theorem occupationSimplex_apply {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n : Nat)
    (x : JobState Buffer K) :
    N.occupationSimplex U initial n x =
      (N.occupationPMF U initial n x).toReal :=
  rfl

private def simplexToPMF {K : Nat}
    (p : stdSimplex Real (JobState Buffer K)) :
    PMF (JobState Buffer K) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p x)) (by
    rw [(ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (fun x _ => stdSimplex.zero_le p x)).symm]
    rw [stdSimplex.sum_eq_one]
    simp)

@[simp]
private theorem simplexToPMF_toReal {K : Nat}
    (p : stdSimplex Real (JobState Buffer K))
    (x : JobState Buffer K) :
    (simplexToPMF p x).toReal = p x := by
  rw [simplexToPMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (stdSimplex.zero_le p x)

private theorem bind_toReal {K : Nat}
    (p : PMF (JobState Buffer K))
    (U : N.DeterministicStationaryPolicy K)
    (y : JobState Buffer K) :
    ((p.bind (N.transitionPMF U)) y).toReal =
      Finset.univ.sum (fun x =>
        (p x).toReal * (N.transitionPMF U x y).toReal) := by
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top (p.apply_ne_top x)
      ((N.transitionPMF U x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul]

private theorem pmf_toReal_le_one {K : Nat}
    (p : PMF (JobState Buffer K)) (x : JobState Buffer K) :
    (p x).toReal <= 1 := by
  have h := (ENNReal.toReal_le_toReal
    (p.apply_ne_top x) (by simp : Ne (1 : ENNReal) ⊤)).2
      (p.coe_le_one x)
  simpa using h

/-- The exact endpoint correction tends to zero in every coordinate. -/
theorem tendsto_occupationPMF_bind_sub_toReal {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K))
    (x : JobState Buffer K) :
    Tendsto
      (fun n =>
        (((N.occupationPMF U initial n).bind
          (N.transitionPMF U)) x).toReal -
          (N.occupationPMF U initial n x).toReal)
      atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun n : Nat => 1 / ((n : Real) + 1))
  next =>
    intro n
    rw [Real.norm_eq_abs, N.occupationPMF_bind_sub_toReal U initial n x,
      abs_mul, abs_of_nonneg (by positivity)]
    have hdiff :
        abs ((N.nStepLaw U initial (n + 1) x).toReal -
          (initial x).toReal) <= 1 := by
      have hnext_nonneg :
          0 <= (N.nStepLaw U initial (n + 1) x).toReal :=
        ENNReal.toReal_nonneg
      have hinitial_nonneg : 0 <= (initial x).toReal :=
        ENNReal.toReal_nonneg
      rw [abs_le]
      constructor
      · linarith [hnext_nonneg, pmf_toReal_le_one initial x]
      · linarith [pmf_toReal_le_one
          (N.nStepLaw U initial (n + 1)) x, hinitial_nonneg]
    calc
      (1 / ((n : Real) + 1)) *
          abs ((N.nStepLaw U initial (n + 1) x).toReal -
            (initial x).toReal) <=
        (1 / ((n : Real) + 1)) * 1 :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = 1 / ((n : Real) + 1) := by
        rw [mul_one]
  next =>
    exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The Cesaro occupation laws from an explicit initial PMF converge
coordinatewise to an invariant PMF, and average waste converges to the
one-step waste under that same initial-law-dependent invariant PMF. -/
theorem exists_initialCesaroLimitPMF {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) :
    Exists (fun limitLaw : PMF (JobState Buffer K) =>
      And (N.IsInvariantPMF U limitLaw)
        (And
          (forall x : JobState Buffer K,
            Tendsto
              (fun n => (N.occupationPMF U initial n x).toReal)
              atTop (nhds ((limitLaw x).toReal)))
          (Tendsto
            (fun n => N.finiteHorizonAverageWaste U initial n)
            atTop
            (nhds (N.stationaryOneStepWaste U limitLaw))))) := by
  classical
  letI : Nonempty (JobState Buffer K) :=
    ⟨initial.support_nonempty.choose⟩
  choose p phi hphi hp using
    CompactSpace.tendsto_subseq (N.occupationSimplex U initial)
  have hcoordinate (x : JobState Buffer K) :
      Tendsto
        (fun n => (N.occupationPMF U initial n x).toReal)
        atTop (nhds (p x)) := by
    let indicator : JobState Buffer K -> Real :=
      fun y => if y = x then 1 else 0
    obtain ⟨limit, hlimit⟩ :=
      N.exists_occupationExpectation_limit U initial indicator
    have hcoordinate_limit :
        Tendsto
          (fun n => (N.occupationPMF U initial n x).toReal)
          atTop (nhds limit) := by
      simpa [indicator] using hlimit
    have heval :
        Continuous
          (fun q : stdSimplex Real (JobState Buffer K) => q x) :=
      (continuous_apply x).comp continuous_subtype_val
    have hsubsequence :
        Tendsto
          (fun n => (N.occupationPMF U initial (phi n) x).toReal)
          atTop (nhds (p x)) := by
      simpa [Function.comp_def] using
        heval.continuousAt.tendsto.comp hp
    have hsubsequence_limit :
        Tendsto
          (fun n => (N.occupationPMF U initial (phi n) x).toReal)
          atTop (nhds limit) := by
      simpa [Function.comp_def] using
        hcoordinate_limit.comp hphi.tendsto_atTop
    have hlimit_eq : limit = p x :=
      tendsto_nhds_unique hsubsequence_limit hsubsequence
    simpa [hlimit_eq] using hcoordinate_limit
  let limitLaw : PMF (JobState Buffer K) := simplexToPMF p
  have hcoordinate_limitLaw (x : JobState Buffer K) :
      Tendsto
        (fun n => (N.occupationPMF U initial n x).toReal)
        atTop (nhds ((limitLaw x).toReal)) := by
    simpa [limitLaw] using hcoordinate x
  have hfixedCoordinate (y : JobState Buffer K) :
      Finset.univ.sum (fun x =>
        p x * (N.transitionPMF U x y).toReal) = p y := by
    have htransition :
        Tendsto
          (fun n =>
            Finset.univ.sum (fun x =>
              (N.occupationPMF U initial n x).toReal *
                (N.transitionPMF U x y).toReal))
          atTop
          (nhds (Finset.univ.sum (fun x =>
            p x * (N.transitionPMF U x y).toReal))) := by
      apply tendsto_finset_sum
      intro x hx
      exact (hcoordinate x).mul_const (N.transitionPMF U x y).toReal
    have hbind_limit :
        Tendsto
          (fun n =>
            (((N.occupationPMF U initial n).bind
              (N.transitionPMF U)) y).toReal)
          atTop
          (nhds (Finset.univ.sum (fun x =>
            p x * (N.transitionPMF U x y).toReal))) := by
      simpa only [N.bind_toReal] using htransition
    have hbind_to_p :
        Tendsto
          (fun n =>
            (((N.occupationPMF U initial n).bind
              (N.transitionPMF U)) y).toReal)
          atTop (nhds (p y)) := by
      have hsum :=
        (N.tendsto_occupationPMF_bind_sub_toReal U initial y).add
          (hcoordinate y)
      simpa only [sub_add_cancel, zero_add] using hsum
    exact tendsto_nhds_unique hbind_limit hbind_to_p
  have hinvariant : N.IsInvariantPMF U limitLaw := by
    apply PMF.ext
    intro y
    apply (ENNReal.toReal_eq_toReal_iff'
      ((limitLaw.bind (N.transitionPMF U)).apply_ne_top y)
      (limitLaw.apply_ne_top y)).mp
    rw [N.bind_toReal]
    simp only [limitLaw, simplexToPMF_toReal]
    exact hfixedCoordinate y
  have hwaste :
      Tendsto
        (fun n =>
          N.stationaryOneStepWaste U
            (N.occupationPMF U initial n))
        atTop (nhds (N.stationaryOneStepWaste U limitLaw)) := by
    unfold stationaryOneStepWaste
    apply tendsto_finset_sum
    intro x hx
    exact (hcoordinate_limitLaw x).mul_const (N.oneStepWaste U x)
  have havg :
      Tendsto
        (fun n => N.finiteHorizonAverageWaste U initial n)
        atTop (nhds (N.stationaryOneStepWaste U limitLaw)) := by
    apply hwaste.congr'
    filter_upwards with n
    exact
      (N.finiteHorizonAverageWaste_eq_stationaryOneStepWaste
        U initial n).symm
  exact Exists.intro limitLaw
    (And.intro hinvariant
      (And.intro hcoordinate_limitLaw havg))

end Network

end StateDepMOR
