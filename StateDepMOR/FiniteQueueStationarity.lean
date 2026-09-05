import StateDepMOR.FiniteQueueChain
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences

/-!
# Stationarity for the finite event-epoch queue chain

Every Markov kernel on a nonempty finite type has an invariant PMF.  The
proof takes Cesaro averages of one orbit in the real probability simplex,
extracts a convergent subsequence by compactness, and proves that its limit
is fixed because the one-step endpoint correction vanishes.

The result is then applied to the event-epoch transition law from
`FiniteQueueChain`.  The final section proves that both one-step and
stationary one-step waste lie between zero and one.
-/

open scoped BigOperators ENNReal
open Filter

noncomputable section

namespace StateDepMOR

namespace FiniteMarkovChain

universe u

variable {A : Type u} [Fintype A]

private theorem pmf_real_sum (p : PMF A) :
    Finset.univ.sum (fun x => (p x).toReal) = 1 := by
  rw [(ENNReal.toReal_sum (s := Finset.univ)
    (fun x _ => p.apply_ne_top x)).symm]
  calc
    (Finset.univ.sum fun x => p x).toReal =
        (tsum fun x => p x).toReal := by
      congr 1
      exact (tsum_eq_sum (s := Finset.univ)
        (fun x hx => (hx (Finset.mem_univ x)).elim)).symm
    _ = 1 := by
      rw [p.tsum_coe]
      simp

/-- The affine action of a finite Markov kernel on the real simplex. -/
private def markovOperator (P : A -> PMF A)
    (p : stdSimplex Real A) : stdSimplex Real A := by
  refine Subtype.mk
    (fun y => Finset.univ.sum (fun x => p x * (P x y).toReal)) ?_
  apply And.intro
  next =>
    intro y
    exact Finset.sum_nonneg
      (fun x _ => mul_nonneg (stdSimplex.zero_le p x) ENNReal.toReal_nonneg)
  next =>
    calc
      Finset.univ.sum
          (fun y => Finset.univ.sum (fun x => p x * (P x y).toReal)) =
        Finset.univ.sum
          (fun x => Finset.univ.sum (fun y => p x * (P x y).toReal)) :=
            Finset.sum_comm
      _ = Finset.univ.sum
          (fun x => p x * Finset.univ.sum (fun y => (P x y).toReal)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact (Finset.mul_sum Finset.univ
          (fun y => (P x y).toReal) (p x)).symm
      _ = Finset.univ.sum (fun x => p x * 1) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [pmf_real_sum]
      _ = 1 := by
        simp only [mul_one]
        exact stdSimplex.sum_eq_one p

@[simp]
private theorem markovOperator_apply (P : A -> PMF A)
    (p : stdSimplex Real A) (y : A) :
    markovOperator P p y =
      Finset.univ.sum (fun x => p x * (P x y).toReal) :=
  rfl

private theorem continuous_markovOperator (P : A -> PMF A) :
    Continuous (markovOperator P) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro y
  apply continuous_finsetSum
  intro x _
  exact ((continuous_apply x).comp continuous_subtype_val).mul continuous_const

private def orbit (P : A -> PMF A) (p0 : stdSimplex Real A)
    (n : Nat) : stdSimplex Real A :=
  Nat.iterate (markovOperator P) n p0

private theorem orbit_succ (P : A -> PMF A)
    (p0 : stdSimplex Real A) (n : Nat) :
    orbit P p0 (n + 1) = markovOperator P (orbit P p0 n) := by
  simp [orbit, Function.iterate_succ_apply']

private def cesaroAverage (P : A -> PMF A)
    (p0 : stdSimplex Real A) (n : Nat) : stdSimplex Real A := by
  let d : Real := n + 1
  refine Subtype.mk
    (fun y => (1 / d) * (Finset.range (n + 1)).sum
      (fun k => orbit P p0 k y)) ?_
  apply And.intro
  next =>
    intro y
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg
        (fun k _ => stdSimplex.zero_le (orbit P p0 k) y))
  next =>
    dsimp only [d]
    calc
      Finset.univ.sum
          (fun y => (1 / ((n : Real) + 1)) *
            (Finset.range (n + 1)).sum (fun k => orbit P p0 k y)) =
        (1 / ((n : Real) + 1)) *
          Finset.univ.sum
            (fun y => (Finset.range (n + 1)).sum
              (fun k => orbit P p0 k y)) :=
        (Finset.mul_sum Finset.univ
          (fun y => (Finset.range (n + 1)).sum
            (fun k => orbit P p0 k y))
          (1 / ((n : Real) + 1))).symm
      _ = (1 / ((n : Real) + 1)) *
          (Finset.range (n + 1)).sum
            (fun k => Finset.univ.sum (fun y => orbit P p0 k y)) := by
        rw [Finset.sum_comm]
      _ = (1 / ((n : Real) + 1)) *
          (Finset.range (n + 1)).sum (fun _ => (1 : Real)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact stdSimplex.sum_eq_one (orbit P p0 k)
      _ = 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
          Nat.cast_add, Nat.cast_one]
        field_simp

@[simp]
private theorem cesaroAverage_apply (P : A -> PMF A)
    (p0 : stdSimplex Real A) (n : Nat) (y : A) :
    cesaroAverage P p0 n y =
      (1 / ((n : Real) + 1)) *
        (Finset.range (n + 1)).sum (fun k => orbit P p0 k y) :=
  rfl

private theorem markovOperator_cesaro_apply (P : A -> PMF A)
    (p0 : stdSimplex Real A) (n : Nat) (y : A) :
    markovOperator P (cesaroAverage P p0 n) y =
      (1 / ((n : Real) + 1)) *
        (Finset.range (n + 1)).sum
          (fun k => orbit P p0 (k + 1) y) := by
  rw [markovOperator_apply]
  simp_rw [cesaroAverage_apply, mul_assoc, Finset.sum_mul]
  rw [(Finset.mul_sum Finset.univ
    (fun x => (Finset.range (n + 1)).sum
      (fun k => orbit P p0 k x * (P x y).toReal))
    (1 / ((n : Real) + 1))).symm]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [orbit_succ]
  rfl

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

private theorem markovOperator_cesaro_sub_apply (P : A -> PMF A)
    (p0 : stdSimplex Real A) (n : Nat) (y : A) :
    markovOperator P (cesaroAverage P p0 n) y -
        cesaroAverage P p0 n y =
      (1 / ((n : Real) + 1)) *
        (orbit P p0 (n + 1) y - orbit P p0 0 y) := by
  rw [markovOperator_cesaro_apply, cesaroAverage_apply]
  calc
    (1 / ((n : Real) + 1)) *
          (Finset.range (n + 1)).sum
            (fun k => orbit P p0 (k + 1) y) -
        (1 / ((n : Real) + 1)) *
          (Finset.range (n + 1)).sum (fun k => orbit P p0 k y) =
      (1 / ((n : Real) + 1)) *
        ((Finset.range (n + 1)).sum
            (fun k => orbit P p0 (k + 1) y) -
          (Finset.range (n + 1)).sum (fun k => orbit P p0 k y)) :=
        (mul_sub _ _ _).symm
    _ = (1 / ((n : Real) + 1)) *
        (orbit P p0 (n + 1) y - orbit P p0 0 y) := by
      congr 1
      exact shift_sum_sub (fun k => orbit P p0 k y) (n + 1)

private theorem tendsto_markovOperator_cesaro_sub_apply
    (P : A -> PMF A) (p0 : stdSimplex Real A) (y : A) :
    Tendsto
      (fun n =>
        markovOperator P (cesaroAverage P p0 n) y -
          cesaroAverage P p0 n y)
      atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun n : Nat => 1 / ((n : Real) + 1))
  next =>
    intro n
    rw [Real.norm_eq_abs, markovOperator_cesaro_sub_apply, abs_mul]
    rw [abs_of_nonneg (by positivity)]
    have hdiff :
        abs (orbit P p0 (n + 1) y - orbit P p0 0 y) <= 1 := by
      rw [abs_le]
      apply And.intro
      next =>
        linarith [stdSimplex.zero_le (orbit P p0 (n + 1)) y,
          stdSimplex.le_one (orbit P p0 0) y]
      next =>
        linarith [stdSimplex.le_one (orbit P p0 (n + 1)) y,
          stdSimplex.zero_le (orbit P p0 0) y]
    calc
      (1 / ((n : Real) + 1)) *
          abs (orbit P p0 (n + 1) y - orbit P p0 0 y) <=
        (1 / ((n : Real) + 1)) * 1 :=
          mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = 1 / ((n : Real) + 1) := by
        rw [mul_one]
  next =>
    exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Every Markov operator on a nonempty finite real simplex has a fixed
point. -/
private theorem exists_fixed_simplex [Nonempty A] (P : A -> PMF A) :
    Exists (fun p : stdSimplex Real A => markovOperator P p = p) := by
  let p0 : stdSimplex Real A :=
    Classical.choice (inferInstance : Nonempty (stdSimplex Real A))
  choose p phi hphi hlim using
    CompactSpace.tendsto_subseq (cesaroAverage P p0)
  refine Exists.intro p ?_
  apply stdSimplex.ext
  funext y
  have hcoord : Continuous (fun q : stdSimplex Real A => q y) :=
    (continuous_apply y).comp continuous_subtype_val
  have hp_y :
      Tendsto (fun n => cesaroAverage P p0 (phi n) y)
        atTop (nhds (p y)) := by
    simpa [Function.comp_def] using
      hcoord.continuousAt.tendsto.comp hlim
  have hop :
      Tendsto
        (fun n => markovOperator P (cesaroAverage P p0 (phi n)))
        atTop (nhds (markovOperator P p)) := by
    simpa [Function.comp_def] using
      (continuous_markovOperator P).continuousAt.tendsto.comp hlim
  have hop_y :
      Tendsto
        (fun n => markovOperator P (cesaroAverage P p0 (phi n)) y)
        atTop (nhds (markovOperator P p y)) := by
    exact hcoord.continuousAt.tendsto.comp hop
  have hsub_limit :
      Tendsto
        (fun n =>
          markovOperator P (cesaroAverage P p0 (phi n)) y -
            cesaroAverage P p0 (phi n) y)
        atTop (nhds (markovOperator P p y - p y)) :=
    hop_y.sub hp_y
  have hsub_zero :
      Tendsto
        (fun n =>
          markovOperator P (cesaroAverage P p0 (phi n)) y -
            cesaroAverage P p0 (phi n) y)
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_markovOperator_cesaro_sub_apply P p0 y).comp
        hphi.tendsto_atTop
  exact sub_eq_zero.mp (tendsto_nhds_unique hsub_limit hsub_zero)

/-- Convert a point of the real finite simplex into a PMF. -/
private def simplexToPMF (p : stdSimplex Real A) : PMF A :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p x)) (by
    rw [(ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (fun x _ => stdSimplex.zero_le p x)).symm]
    rw [stdSimplex.sum_eq_one]
    simp)

@[simp]
private theorem simplexToPMF_apply (p : stdSimplex Real A) (x : A) :
    simplexToPMF p x = ENNReal.ofReal (p x) :=
  rfl

private theorem bind_toReal (p : PMF A) (P : A -> PMF A) (y : A) :
    ((p.bind P) y).toReal =
      Finset.univ.sum
        (fun x => (p x).toReal * (P x y).toReal) := by
  rw [PMF.bind_apply]
  rw [tsum_eq_sum (s := Finset.univ)
    (fun x hx => (hx (Finset.mem_univ x)).elim)]
  rw [ENNReal.toReal_sum
    (fun x _ => ENNReal.mul_ne_top (p.apply_ne_top x)
      ((P x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul]

private theorem simplexToPMF_bind (P : A -> PMF A)
    (p : stdSimplex Real A) :
    (simplexToPMF p).bind P =
      simplexToPMF (markovOperator P p) := by
  apply PMF.ext
  intro y
  apply (ENNReal.toReal_eq_toReal_iff'
    (((simplexToPMF p).bind P).apply_ne_top y)
    ((simplexToPMF (markovOperator P p)).apply_ne_top y)).mp
  rw [bind_toReal]
  simp_rw [simplexToPMF_apply]
  rw [ENNReal.toReal_ofReal
    (stdSimplex.zero_le (markovOperator P p) y)]
  rw [markovOperator_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [ENNReal.toReal_ofReal (stdSimplex.zero_le p x)]

/-- Every Markov kernel on a nonempty finite type has an invariant PMF. -/
theorem exists_invariant_pmf [Nonempty A] (P : A -> PMF A) :
    Exists (fun pi : PMF A => pi.bind P = pi) := by
  cases exists_fixed_simplex P with
  | intro p hp =>
      exact Exists.intro (simplexToPMF p) (by
        rw [simplexToPMF_bind, hp])

end FiniteMarkovChain

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

variable (N : Network Buffer Server)

omit [DecidableEq Buffer] [DecidableEq Server] in
private theorem server_nonempty
    (N : Network Buffer Server) : Nonempty Server := by
  cases isEmpty_or_nonempty Server with
  | inl h =>
      have hzero :
          Finset.univ.sum (fun j : Server =>
            Finset.univ.sum (fun k : Buffer => N.phi j k)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        exact (h.false j).elim
      have hfalse : (0 : Real) = 1 := hzero.symm.trans N.total_rate
      exact (zero_ne_one hfalse).elim
  | inr h =>
      exact h

omit [DecidableEq Buffer] [DecidableEq Server] in
private theorem buffer_nonempty
    (N : Network Buffer Server) : Nonempty Buffer := by
  cases server_nonempty N with
  | intro j =>
      cases N.server_has_neighbor j with
      | intro i _ =>
          exact Nonempty.intro i

omit [DecidableEq Server] in
/-- Every finite event-epoch queue chain has an invariant PMF. -/
theorem exists_invariantPMF {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    Exists (fun pi : PMF (JobState Buffer K) => N.IsInvariantPMF U pi) := by
  let stateNonempty : Nonempty (JobState Buffer K) :=
    @JobState.instNonempty Buffer inferInstance inferInstance K
      (buffer_nonempty N)
  exact @FiniteMarkovChain.exists_invariant_pmf
    (JobState Buffer K)
    (@JobState.instFintype Buffer inferInstance inferInstance K)
    stateNonempty
    (N.transitionPMF U)

/-- A canonical classical choice of invariant law for the finite queue
chain. -/
noncomputable def invariantPMF {K : Nat}
    (U : N.DeterministicStationaryPolicy K) : PMF (JobState Buffer K) :=
  Classical.choose (N.exists_invariantPMF U)

theorem invariantPMF_isInvariant {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    N.IsInvariantPMF U (N.invariantPMF U) :=
  Classical.choose_spec (N.exists_invariantPMF U)

theorem oneStepWaste_nonneg {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K) :
    0 <= N.oneStepWaste U x := by
  apply Finset.sum_nonneg
  intro jk _
  exact mul_nonneg ENNReal.toReal_nonneg
    (N.wasteIndicator_nonneg U x jk)

theorem oneStepWaste_le_one {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K) :
    N.oneStepWaste U x <= 1 := by
  calc
    N.oneStepWaste U x <=
        Finset.univ.sum (fun jk => (N.tokenLaw jk).toReal * 1) := by
      apply Finset.sum_le_sum
      intro jk _
      exact mul_le_mul_of_nonneg_left
        (N.wasteIndicator_le_one U x jk) ENNReal.toReal_nonneg
    _ = 1 := by
      simpa using FiniteMarkovChain.pmf_real_sum N.tokenLaw

theorem stationaryOneStepWaste_nonneg {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) :
    0 <= N.stationaryOneStepWaste U pi := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg ENNReal.toReal_nonneg (N.oneStepWaste_nonneg U x)

theorem stationaryOneStepWaste_le_one {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) :
    N.stationaryOneStepWaste U pi <= 1 := by
  calc
    N.stationaryOneStepWaste U pi <=
        Finset.univ.sum (fun x => (pi x).toReal * 1) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left
        (N.oneStepWaste_le_one U x) ENNReal.toReal_nonneg
    _ = 1 := by
      simpa using FiniteMarkovChain.pmf_real_sum pi

/-- An invariant queue law together with its stationary waste bounds. -/
theorem exists_invariantPMF_with_waste_bounds {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    Exists (fun pi : PMF (JobState Buffer K) =>
      And (N.IsInvariantPMF U pi)
        (And (0 <= N.stationaryOneStepWaste U pi)
          (N.stationaryOneStepWaste U pi <= 1))) := by
  cases N.exists_invariantPMF U with
  | intro pi hpi =>
      exact Exists.intro pi
        (And.intro hpi
          (And.intro (N.stationaryOneStepWaste_nonneg U pi)
            (N.stationaryOneStepWaste_le_one U pi)))

end Network

end StateDepMOR
