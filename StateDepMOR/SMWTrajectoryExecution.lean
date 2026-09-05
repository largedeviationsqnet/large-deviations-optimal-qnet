import StateDepMOR.PaperStatements
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Concrete stochastic trajectories for the SMW resting-state remark

The sample space and trajectories are the independent calendar-time
exponential clocks from `PoissonProcessExecution`.  Queue paths retain the
arbitrary finite initial state over which the paper takes its maximum.
-/

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace StateDepMOR.PaperStatements

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]
variable [LinearOrder Buffer]

/-- Distance from `alpha` for one concrete finite initial state. -/
noncomputable def calendarSMWDistance
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (K : PNat) (T : Real)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (x0 : JobState Buffer (K : Nat)) : Real :=
  Real.sqrt
    (Finset.univ.sum fun i =>
      (N.calendarScaledQueueStateFrom
          (N.smwPolicy alpha halpha) K x0 omega T i - alpha i) ^ 2)

theorem worstInitialSMWDistance_eq_sSup_range
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (K : PNat) (T : Real)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    worstInitialSMWDistance N alpha halpha K T omega =
      sSup (Set.range (calendarSMWDistance N alpha halpha K T omega)) := by
  apply congrArg sSup
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_range, calendarSMWDistance,
    worstInitialSMWDistance]
  constructor
  · rintro ⟨x0, rfl⟩
    exact ⟨x0, rfl⟩
  · rintro ⟨x0, rfl⟩
    exact ⟨x0, rfl⟩

theorem exists_jobState_maximizing_calendarSMWDistance
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (K : PNat) (T : Real)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    exists x0 : JobState Buffer (K : Nat),
      worstInitialSMWDistance N alpha halpha K T omega =
        calendarSMWDistance N alpha halpha K T omega x0 := by
  rw [worstInitialSMWDistance_eq_sSup_range]
  have hrange_nonempty :
      (Set.range
        (calendarSMWDistance N alpha halpha K T omega)).Nonempty :=
    Set.range_nonempty _
  have hrange_finite :
      (Set.range
        (calendarSMWDistance N alpha halpha K T omega)).Finite :=
    Set.finite_range _
  obtain ⟨x0, hx0⟩ := hrange_nonempty.csSup_mem hrange_finite
  exact ⟨x0, hx0.symm⟩

theorem calendarSMWDistance_le_worstInitialSMWDistance
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (K : PNat) (T : Real)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (x0 : JobState Buffer (K : Nat)) :
    calendarSMWDistance N alpha halpha K T omega x0 <=
      worstInitialSMWDistance N alpha halpha K T omega := by
  rw [worstInitialSMWDistance_eq_sSup_range]
  exact le_csSup (Set.finite_range _).bddAbove ⟨x0, rfl⟩

theorem worstInitialSMWDistance_nonneg
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (K : PNat) (T : Real)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    0 <= worstInitialSMWDistance N alpha halpha K T omega := by
  obtain ⟨x0, hx0⟩ :=
    exists_jobState_maximizing_calendarSMWDistance
      N alpha halpha K T omega
  rw [hx0]
  exact Real.sqrt_nonneg _

/-- A bounded nonnegative sequence has limsup zero when every sequence
tending to infinity has a subsubsequence converging to zero. -/
theorem limsup_pnat_eq_zero_of_subsequential_compactness
    (f : PNat -> Real)
    (hzero : forall K, 0 <= f K)
    (M : Real) (hM : forall K, f K <= M)
    (hsubseq :
      forall q : Nat -> PNat, Tendsto q atTop atTop ->
        exists r : Nat -> Nat, Tendsto r atTop atTop /\
          Tendsto (fun n => f (q (r n))) atTop (nhds 0)) :
    limsup f atTop = 0 := by
  have hcobdd : IsCoboundedUnder (fun x y : Real => x <= y) atTop f :=
    isCoboundedUnder_le_of_le atTop hzero
  have hbdd : IsBoundedUnder (fun x y : Real => x <= y) atTop f :=
    isBoundedUnder_of ⟨M, hM⟩
  obtain ⟨q, hq_limsup, hq_top⟩ :=
    exists_seq_tendsto_limsup (f := atTop) (u := f) hcobdd hbdd
  obtain ⟨r, hr_top, hr_zero⟩ := hsubseq q hq_top
  have hr_limsup :
      Tendsto (fun n => f (q (r n))) atTop (nhds (limsup f atTop)) :=
    hq_limsup.comp hr_top
  exact tendsto_nhds_unique hr_limsup hr_zero

namespace Network

variable (N : StateDepMOR.Network Buffer Server)

/-- Extend states selected on a strict system-size subsequence to an
arbitrary initial-state family. -/
noncomputable def initialFamilyOfStrictSubsequence
    (K : Nat -> PNat) (z : forall n, JobState Buffer (K n : Nat))
    (L : PNat) : JobState Buffer (L : Nat) := by
  classical
  let jobs : Buffer -> Nat :=
    Function.extend K (fun n => (z n).jobs)
      (fun M => (N.eventInitialState M).jobs) L
  refine { jobs := jobs, total_jobs := ?_ }
  dsimp [jobs]
  rw [Function.extend_def]
  split_ifs with h
  · rw [(z (Classical.choose h)).total_jobs]
    exact congrArg Subtype.val (Classical.choose_spec h)
  · exact (N.eventInitialState L).total_jobs

theorem initialFamilyOfStrictSubsequence_apply
    (K : Nat -> PNat) (hK : StrictMono K)
    (z : forall n, JobState Buffer (K n : Nat)) (n : Nat) :
    initialFamilyOfStrictSubsequence N K z (K n) = z n := by
  classical
  apply JobState.ext
  funext i
  change
    Function.extend K (fun m => (z m).jobs)
      (fun M => (N.eventInitialState M).jobs) (K n) i =
        (z n).jobs i
  rw [hK.injective.extend_apply]

theorem calendarSMWDistance_le_sqrt_card
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (K : PNat) (x0 : JobState Buffer (K : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (T : Real) :
    calendarSMWDistance N alpha halpha K T omega x0 <=
      Real.sqrt (Fintype.card Buffer) := by
  let y : JobState Buffer (K : Nat) :=
    N.runTokens (N.smwPolicy alpha halpha K) x0
      (N.calendarTokenPrefix K omega T)
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hy0 (i : Buffer) : 0 <= (y i : Real) / (K : Nat) := by
    positivity
  have hy1 (i : Buffer) : (y i : Real) / (K : Nat) <= 1 := by
    apply (div_le_iff₀ hK).2
    have hc : (y i : Real) <= ((K : Nat) : Real) := by
      exact_mod_cast JobState.coordinate_le y i
    simpa using hc
  have ha1 (i : Buffer) : alpha i <= 1 := by
    calc
      alpha i <= Finset.univ.sum (fun q => alpha q) :=
        Finset.single_le_sum
          (fun q _ => alpha.nonneg q) (Finset.mem_univ i)
      _ = 1 := alpha.sum_eq_one
  have hterm (i : Buffer) :
      ((y i : Real) / (K : Nat) - alpha i) ^ 2 <= 1 := by
    have hdlo : -1 <= (y i : Real) / (K : Nat) - alpha i := by
      linarith [alpha.nonneg i, hy0 i, ha1 i]
    have hdhi : (y i : Real) / (K : Nat) - alpha i <= 1 := by
      linarith [alpha.nonneg i, hy0 i, hy1 i]
    have hplus :
        0 <= 1 + ((y i : Real) / (K : Nat) - alpha i) := by
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hdhi) hplus]
  have hsum :
      (Finset.univ.sum fun i =>
        ((y i : Real) / (K : Nat) - alpha i) ^ 2) <=
        (Fintype.card Buffer : Real) := by
    calc
      (Finset.univ.sum fun i =>
          ((y i : Real) / (K : Nat) - alpha i) ^ 2) <=
          Finset.univ.sum (fun _ : Buffer => (1 : Real)) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = (Fintype.card Buffer : Real) := by simp
  unfold calendarSMWDistance
  change Real.sqrt
    (Finset.univ.sum fun i =>
      (((y i : Nat) : Real) / (K : Nat) - alpha i) ^ 2) <= _
  exact Real.sqrt_le_sqrt hsum

theorem worstInitialSMWDistance_le_sqrt_card
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (T : Real) :
    worstInitialSMWDistance N alpha halpha K T omega <=
      Real.sqrt (Fintype.card Buffer) := by
  obtain ⟨x0, hx0⟩ :=
    exists_jobState_maximizing_calendarSMWDistance
      N alpha halpha K T omega
  rw [hx0]
  exact calendarSMWDistance_le_sqrt_card N alpha halpha K x0 omega T

end Network

end StateDepMOR.PaperStatements
