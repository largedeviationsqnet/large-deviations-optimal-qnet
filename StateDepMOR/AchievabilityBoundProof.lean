import StateDepMOR.AchievabilityFinal
import StateDepMOR.AchievabilityRateTransfer
import StateDepMOR.AchievabilityReturnFailure
import StateDepMOR.AchievabilityCalendarBridge
import StateDepMOR.AchievabilityTriangular

/-!
# Paper-facing achievability bound

This module owns the final assembly of the repaired achievability statement.
The local variational exponent remains indexed by the fixed positive horizon
from the statement; no cross-horizon invariance is used.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

namespace StateDepMOR.PaperStatements.Network

universe u v w

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : StateDepMOR.Network Buffer Server)

/-! ## Full-measure calendar endpoint bridge -/

/-- The endpoint-to-path bridge remains valid when containment is proved
only for regular calendar samples.  Regularity has full calendar measure
and is the hypothesis used by the triangular fluid-limit events. -/
theorem calendarBlockEndpointEvent_le_calendarPathLaw_ae_regular
    {H : Real} (hH : 0 < H)
    (K : PNat) (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat))
    (Target : JobState Buffer (K : Nat) -> Prop)
    (F : Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H))
    (hF : MeasurableSet F)
    (hcontain :
      forall omega :
          StateDepMOR.Network.CalendarPoissonSample
            (Buffer := Buffer) (Server := Server),
        StateDepMOR.PoissonSamplePath.IsRegularSample omega ->
        Target (calendarBlockEndpoint N K U x omega H) ->
          StateDepMOR.PoissonSamplePath.calendarPath N H K omega ∈ F) :
    N.calendarPoissonMeasure
        {omega | Target (calendarBlockEndpoint N K U x omega H)} <=
      StateDepMOR.PoissonSamplePath.calendarPathLaw
        N H (K : Nat) F := by
  rw [StateDepMOR.PoissonSamplePath.calendarPathLaw_apply
    N hH (K : Nat) hF]
  apply measure_mono_ae
  filter_upwards
    [StateDepMOR.PoissonSamplePath.regularSample_ae N] with
      omega hregular htarget
  change
    StateDepMOR.PoissonSamplePath.calendarPath N H
      (StateDepMOR.PoissonSamplePath.positiveSize (K : Nat)) omega ∈ F
  rw [positiveSize_pnat_val K]
  exact hcontain omega hregular htarget

/-- Real-valued form of the regular-sample endpoint bridge. -/
theorem ofReal_calendarBlockEndpointEvent_le_calendarPathLaw_ae_regular
    {H : Real} (hH : 0 < H)
    (K : PNat) (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat))
    (Target : JobState Buffer (K : Nat) -> Prop)
    (F : Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H))
    (hF : MeasurableSet F)
    (hcontain :
      forall omega :
          StateDepMOR.Network.CalendarPoissonSample
            (Buffer := Buffer) (Server := Server),
        StateDepMOR.PoissonSamplePath.IsRegularSample omega ->
        Target (calendarBlockEndpoint N K U x omega H) ->
          StateDepMOR.PoissonSamplePath.calendarPath N H K omega ∈ F) :
    ENNReal.ofReal
        (N.calendarPoissonMeasure.real
          {omega | Target (calendarBlockEndpoint N K U x omega H)}) <=
      StateDepMOR.PoissonSamplePath.calendarPathLaw
        N H (K : Nat) F := by
  rw [measureReal_def]
  rw [ENNReal.ofReal_toReal (measure_ne_top N.calendarPoissonMeasure _)]
  exact calendarBlockEndpointEvent_le_calendarPathLaw_ae_regular
    N hH K U x Target F hF hcontain

/-- On a finite discrete state space, the real event mass of a PMF is the
real mass of the corresponding event under its associated measure. -/
theorem pmfEventMass_eq_toMeasure_real
    {A : Type*} [Fintype A] [DecidableEq A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    (pi : PMF A) (P : A -> Prop) [DecidablePred P] :
    pmfEventMass pi P = pi.toMeasure.real {x | P x} := by
  classical
  let s : Finset A := Finset.univ.filter P
  have hset : {x : A | P x} = (s : Set A) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_coe, s, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [hset, measureReal_def, PMF.toMeasure_apply_finset]
  rw [ENNReal.toReal_sum (fun x _ => pi.apply_ne_top x)]
  unfold pmfEventMass
  simp [s, Finset.sum_filter]

/-! ## Uniform contraction for varying finite-system events -/

/-- Closed tail hull of a family of events whose index is the system size. -/
def varyingEventTailClosure
    {X : Type w} [TopologicalSpace X]
    (event : Nat -> Set X) (n : Nat) : Set X :=
  closure {x | exists k, n <= k /\ x ∈ event k}

/-- Kuratowski upper limit of a family of size-dependent events. -/
def varyingEventOuterLimit
    {X : Type w} [TopologicalSpace X]
    (event : Nat -> Set X) : Set X :=
  ⋂ n, varyingEventTailClosure event n

theorem event_subset_varyingEventTailClosure
    {X : Type w} [TopologicalSpace X]
    (event : Nat -> Set X) (n : Nat) :
    event n <= varyingEventTailClosure event n := by
  intro x hx
  exact subset_closure ⟨n, le_rfl, hx⟩

theorem varyingEventTailClosure_antitone
    {X : Type w} [TopologicalSpace X]
    (event : Nat -> Set X) :
    Antitone (varyingEventTailClosure event) := by
  intro n m hnm
  apply closure_minimal
  · intro x hx
    obtain ⟨k, hmk, hxk⟩ := hx
    exact subset_closure ⟨k, hnm.trans hmk, hxk⟩
  · exact isClosed_closure

/-- Every point of a varying-event outer limit is approached by event
points along strictly increasing event indices. -/
theorem exists_strictMono_event_sequence_tendsto_of_mem_outerLimit
    {X : Type w} [PseudoMetricSpace X]
    (event : Nat -> Set X) {x : X}
    (hx : x ∈ varyingEventOuterLimit event) :
    exists K : Nat -> Nat, StrictMono K /\
      exists y : Nat -> X,
        (forall n, y n ∈ event (K n)) /\
          Tendsto y atTop (nhds x) := by
  have hxTail (n : Nat) :
      x ∈ varyingEventTailClosure event n :=
    Set.mem_iInter.mp hx n
  have hexists (lower n : Nat) :
      exists p : Nat × X,
        lower < p.1 /\ p.2 ∈ event p.1 /\
          dist x p.2 < 1 / ((n : Real) + 1) := by
    have hepsilon : 0 < 1 / ((n : Real) + 1) := by positivity
    obtain ⟨y, ⟨k, hk, hy⟩, hxy⟩ :=
      Metric.mem_closure_iff.mp (hxTail (lower + 1))
        (1 / ((n : Real) + 1)) hepsilon
    exact ⟨(k, y), Nat.lt_of_succ_le hk, hy, hxy⟩
  let choosePair (lower n : Nat) : Nat × X :=
    Classical.choose (hexists lower n)
  have choosePair_spec (lower n : Nat) :
      lower < (choosePair lower n).1 /\
        (choosePair lower n).2 ∈ event (choosePair lower n).1 /\
          dist x (choosePair lower n).2 <
            1 / ((n : Real) + 1) :=
    Classical.choose_spec (hexists lower n)
  let seq : Nat -> Nat × X :=
    fun n =>
      Nat.rec (choosePair 0 0)
        (fun m previous => choosePair previous.1 (m + 1)) n
  let K : Nat -> Nat := fun n => (seq n).1
  let y : Nat -> X := fun n => (seq n).2
  have hKstep (n : Nat) : K n < K (n + 1) := by
    exact (choosePair_spec (seq n).1 (n + 1)).1
  have hyMem (n : Nat) : y n ∈ event (K n) := by
    cases n with
    | zero =>
        exact (choosePair_spec 0 0).2.1
    | succ n =>
        exact (choosePair_spec (seq n).1 (n + 1)).2.1
  have hyDist (n : Nat) :
      dist (y n) x <= 1 / ((n : Real) + 1) := by
    have hlt : dist x (y n) < 1 / ((n : Real) + 1) := by
      cases n with
      | zero =>
          exact (choosePair_spec 0 0).2.2
      | succ n =>
          exact (choosePair_spec (seq n).1 (n + 1)).2.2
    simpa only [dist_comm] using hlt.le
  have hyTendsto : Tendsto y atTop (nhds x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg)
      hyDist tendsto_one_div_add_atTop_nhds_zero_nat
  exact ⟨K, strictMono_nat_of_lt_succ hKstep,
    y, hyMem, hyTendsto⟩

/-- Compact good-rate sublevels separate from some closed tail hull as soon
as they separate from the varying-event outer limit. -/
theorem exists_tailClosure_disjoint_compactSublevel
    {X : Type w} [TopologicalSpace X] [T2Space X]
    (event : Nat -> Set X) (I : X -> ENNReal) (level : ENNReal)
    (hcompact : IsCompact {x | I x <= level})
    (houter :
      Disjoint (varyingEventOuterLimit event) {x | I x <= level}) :
    exists n,
      Disjoint (varyingEventTailClosure event n) {x | I x <= level} := by
  by_contra hnone
  push Not at hnone
  let C : Nat -> Set X := fun n =>
    {x | I x <= level} ∩ varyingEventTailClosure event n
  have hCnonempty (n : Nat) : (C n).Nonempty := by
    obtain ⟨x, hxtail, hxlevel⟩ :=
      Set.not_disjoint_iff.mp (hnone n)
    exact ⟨x, hxlevel, hxtail⟩
  have hCstep (n : Nat) : C (n + 1) <= C n := by
    intro x hx
    exact ⟨hx.1,
      varyingEventTailClosure_antitone event (Nat.le_succ n) hx.2⟩
  have hCcompact : IsCompact (C 0) := by
    exact hcompact.inter_right isClosed_closure
  have hCclosed (n : Nat) : IsClosed (C n) := by
    exact hcompact.isClosed.inter isClosed_closure
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      C hCstep hCnonempty hCcompact hCclosed
  have hxC (n : Nat) : x ∈ C n := Set.mem_iInter.mp hx n
  exact Set.disjoint_left.mp houter
    (Set.mem_iInter.mpr fun n => (hxC n).2) (hxC 0).1

/-- Scaled log mass when the measured event itself varies with system size.
Index `n` still denotes physical size `n + 1`, matching `scaledLogMass`. -/
noncomputable def scaledLogVaryingMass
    {X : Type w} [MeasurableSpace X]
    (mu : Nat -> Measure X) (event : Nat -> Set X) (n : Nat) : EReal :=
  ENNReal.log (mu (n + 1) (event n)) / ((n + 1 : Nat) : EReal)

/-- Pointwise transfer from a positive-size loss to a size-dependent event.
The event index `n` and physical system size `n + 1` are kept explicit. -/
theorem scaledLogLossPNat_le_scaledLogVaryingMass
    {X : Type w} [MeasurableSpace X]
    (loss : PNat -> Real) (mu : Nat -> Measure X)
    (event : Nat -> Set X)
    (hbound : forall n : Nat,
      ENNReal.ofReal (loss n.succPNat) <= mu (n + 1) (event n))
    (n : Nat) :
    scaledLogLossPNat loss n.succPNat <=
      scaledLogVaryingMass mu event n := by
  have hlog :
      ENNReal.log (ENNReal.ofReal (loss n.succPNat)) <=
        ENNReal.log (mu (n + 1) (event n)) :=
    ENNReal.log_le_log (hbound n)
  unfold scaledLogLossPNat scaledLogVaryingMass
  have hden :
      (0 : EReal) <= ((((n + 1 : Nat) : Real)) : EReal) := by
    positivity
  have hdiv := EReal.div_le_div_right_of_nonneg hden hlog
  rw [<- EReal.coe_coe_eq_natCast (n + 1)]
  exact hdiv

/-- A size-dependent event-mass domination transfers to the paper's
positive-natural scaled-log `limsup`. -/
theorem limsup_scaledLogLossPNat_le_limsup_scaledLogVaryingMass
    {X : Type w} [MeasurableSpace X]
    (loss : PNat -> Real) (mu : Nat -> Measure X)
    (event : Nat -> Set X)
    (hbound : forall n : Nat,
      ENNReal.ofReal (loss n.succPNat) <= mu (n + 1) (event n)) :
    limsup (scaledLogLossPNat loss) atTop <=
      limsup (scaledLogVaryingMass mu event) atTop := by
  rw [<- StateDepMOR.limsup_comp_succPNat
    (scaledLogLossPNat loss)]
  exact limsup_le_limsup
    (Eventually.of_forall
      (scaledLogLossPNat_le_scaledLogVaryingMass
        loss mu event hbound))

theorem scaledLogVaryingMass_nonpos_of_mass_le_one
    {X : Type w} [MeasurableSpace X]
    (mu : Nat -> Measure X)
    (hmass : StateDepMOR.PoissonUpperAssembly.MassLeOne mu)
    (event : Nat -> Set X) (n : Nat) :
    scaledLogVaryingMass mu event n <= 0 := by
  exact
    StateDepMOR.PoissonUpperAssembly.scaledLogMass_nonpos_of_mass_le_one
      mu hmass (event n) n

private theorem varying_log_two_div_tendsto_zero :
    Tendsto
      (fun n : Nat =>
        ENNReal.log (2 : ENNReal) / ((n + 1 : Nat) : EReal))
      atTop (nhds 0) := by
  have h :=
    EReal.tendsto_const_div_atTop_nhds_zero_nat
      (C := ENNReal.log (2 : ENNReal)) (by simp) (by simp)
  change Tendsto
    (Function.comp
      (fun n : Nat => ENNReal.log (2 : ENNReal) / (n : EReal))
      (fun n : Nat => n + 1)) atTop (nhds 0)
  exact h.comp (tendsto_add_atTop_nat 1)

private theorem scaledLogVaryingMass_union_pointwise
    {X : Type w} [MeasurableSpace X]
    (mu : Nat -> Measure X) (A B : Nat -> Set X) (n : Nat) :
    scaledLogVaryingMass mu (fun k => A k ∪ B k) n <=
      ENNReal.log (2 : ENNReal) / ((n + 1 : Nat) : EReal) +
        max (scaledLogVaryingMass mu A n)
          (scaledLogVaryingMass mu B n) := by
  let a := mu (n + 1) (A n)
  let b := mu (n + 1) (B n)
  have hab :
      mu (n + 1) (A n ∪ B n) <= (2 : ENNReal) * max a b := by
    calc
      mu (n + 1) (A n ∪ B n) <= a + b :=
        measure_union_le (A n) (B n)
      _ <= max a b + max a b :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = (2 : ENNReal) * max a b := by rw [two_mul]
  unfold scaledLogVaryingMass
  apply (EReal.div_le_div_right_of_nonneg (by positivity)
    (ENNReal.log_le_log hab)).trans_eq
  rw [ENNReal.log_mul_add,
    EReal.add_div_of_nonneg_right (by positivity)]
  congr 1
  rw [ENNReal.log_monotone.map_max]
  dsimp [a, b]
  rcases le_total
      (ENNReal.log (mu (n + 1) (A n)))
      (ENNReal.log (mu (n + 1) (B n))) with h | h
  · rw [max_eq_right h, max_eq_right
      (EReal.div_le_div_right_of_nonneg (by positivity) h)]
  · rw [max_eq_left h, max_eq_left
      (EReal.div_le_div_right_of_nonneg (by positivity) h)]

/-- A binary union of size-dependent events has the worse of the two
scaled-log upper rates. -/
theorem limsup_scaledLogVaryingMass_union_le_max
    {X : Type w} [MeasurableSpace X]
    (mu : Nat -> Measure X)
    (hmass : StateDepMOR.PoissonUpperAssembly.MassLeOne mu)
    (A B : Nat -> Set X) :
    limsup
        (scaledLogVaryingMass mu (fun n => A n ∪ B n)) atTop <=
      max (limsup (scaledLogVaryingMass mu A) atTop)
        (limsup (scaledLogVaryingMass mu B) atTop) := by
  let e : Nat -> EReal :=
    fun n => ENNReal.log (2 : ENNReal) / ((n + 1 : Nat) : EReal)
  let m : Nat -> EReal :=
    fun n =>
      max (scaledLogVaryingMass mu A n)
        (scaledLogVaryingMass mu B n)
  have he : Tendsto e atTop (nhds 0) :=
    varying_log_two_div_tendsto_zero
  have heL : limsup e atTop = 0 := he.limsup_eq
  have hmA :
      Filter.IsBoundedUnder (fun x y : EReal => x <= y) atTop
        (scaledLogVaryingMass mu A) :=
    Filter.isBoundedUnder_of_eventually_le
      (Eventually.of_forall
        (scaledLogVaryingMass_nonpos_of_mass_le_one mu hmass A))
  have hmB :
      Filter.IsBoundedUnder (fun x y : EReal => x <= y) atTop
        (scaledLogVaryingMass mu B) :=
    Filter.isBoundedUnder_of_eventually_le
      (Eventually.of_forall
        (scaledLogVaryingMass_nonpos_of_mass_le_one mu hmass B))
  have hmL :
      limsup m atTop =
        max (limsup (scaledLogVaryingMass mu A) atTop)
          (limsup (scaledLogVaryingMass mu B) atTop) :=
    limsup_max
  have hpoint :
      forall n,
        scaledLogVaryingMass mu (fun k => A k ∪ B k) n <=
          e n + m n :=
    scaledLogVaryingMass_union_pointwise mu A B
  calc
    limsup
        (scaledLogVaryingMass mu (fun n => A n ∪ B n)) atTop <=
        limsup (e + m) atTop := by
      apply limsup_le_limsup
      · exact Eventually.of_forall hpoint
      · exact Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le)
      · exact Filter.isBoundedUnder_of_eventually_le
          (Eventually.of_forall fun _ => le_top)
    _ <= limsup e atTop + limsup m atTop := by
      apply EReal.limsup_add_le
      · left
        rw [heL]
        simp
      · left
        rw [heL]
        simp
    _ = max (limsup (scaledLogVaryingMass mu A) atTop)
          (limsup (scaledLogVaryingMass mu B) atTop) := by
      rw [heL, zero_add, hmL]

/-- Final two-event rate assembly. Both event estimates are concrete
size-dependent probability bounds; no probabilistic or LDP premise is hidden
behind a proposition-valued interface. -/
theorem le_negativeLimsupLogRate_of_varying_union
    {X : Type w} [MeasurableSpace X]
    (loss : PNat -> Real) (mu : Nat -> Measure X)
    (hmass : StateDepMOR.PoissonUpperAssembly.MassLeOne mu)
    (A B : Nat -> Set X) (d : Real)
    (hbound : forall n : Nat,
      ENNReal.ofReal (loss n.succPNat) <=
        mu (n + 1) (A n ∪ B n))
    (hA :
      limsup (scaledLogVaryingMass mu A) atTop <= -(d : EReal))
    (hB :
      limsup (scaledLogVaryingMass mu B) atTop <= -(d : EReal)) :
    (d : EReal) <= negativeLimsupLogRate loss := by
  apply le_negativeLimsupLogRate_of_limsup_scaledLogLossPNat_le
  exact
    (limsup_scaledLogLossPNat_le_limsup_scaledLogVaryingMass
      loss mu (fun n => A n ∪ B n) hbound).trans
      ((limsup_scaledLogVaryingMass_union_le_max
        mu hmass A B).trans (by simpa using max_le hA hB))

/-- A positive real lower approximant of an extended-real value can be
strictly enlarged while remaining a real lower approximant. -/
theorem exists_larger_positive_real_below_ereal
    {r : Real} {x : EReal} (hr : 0 < r) (hrx : (r : EReal) < x) :
    exists c : Real, 0 < c /\ r < c /\ (c : EReal) < x := by
  obtain ⟨c, hrc, hcx⟩ := EReal.exists_between_coe_real hrx
  exact ⟨c, hr.trans (EReal.coe_lt_coe_iff.mp hrc),
    EReal.coe_lt_coe_iff.mp hrc, hcx⟩

/-- Shrinking the near-alpha radius preserves any strictly smaller
excursion exponent. -/
theorem exists_excursion_radius
    {d c : Real} (hd : 0 < d) (hdc : d < c) :
    exists rho : Real,
      0 < rho /\ rho < 1 /\ d < c * (1 - rho) := by
  have hc : 0 < c := hd.trans hdc
  let rho := (c - d) / (2 * c)
  have hden : 0 < 2 * c := by positivity
  have hrho : 0 < rho := div_pos (sub_pos.mpr hdc) hden
  have hrhoOne : rho < 1 := by
    dsimp only [rho]
    apply (div_lt_one hden).2
    linarith
  have hcost : d < c * (1 - rho) := by
    dsimp only [rho]
    field_simp [ne_of_gt hc]
    nlinarith
  exact ⟨rho, hrho, hrhoOne, hcost⟩

/-- A positive affine persistence lower bound eventually exceeds any fixed
real rate while retaining a prescribed minimum observation horizon. -/
theorem exists_horizon_affine_cost_gt
    {a b d T : Real} (ha : 0 < a) :
    exists H : Real, 0 < H /\ T <= H /\ d < a * H - b := by
  let H := max T 0 + (|d + b| + 1) / a
  have hfrac : 0 < (|d + b| + 1) / a := by positivity
  have hH : 0 < H := by
    dsimp only [H]
    exact add_pos_of_nonneg_of_pos (le_max_right T 0) hfrac
  have hTH : T <= H := by
    dsimp only [H]
    exact (le_max_left T 0).trans
      (le_add_of_nonneg_right hfrac.le)
  have habs : d + b <= |d + b| := le_abs_self (d + b)
  have hcost : d < a * H - b := by
    dsimp only [H]
    rw [mul_add]
    have hdiv : a * ((|d + b| + 1) / a) = |d + b| + 1 := by
      field_simp [ne_of_gt ha]
    rw [hdiv]
    have hmax : 0 <= a * max T 0 :=
      mul_nonneg ha.le (le_max_right T 0)
    linarith
  exact ⟨H, hH, hTH, hcost⟩

theorem scaledLogVaryingMass_le_tailClosure
    {X : Type w} [MeasurableSpace X] [TopologicalSpace X]
    (mu : Nat -> Measure X) (event : Nat -> Set X) {n k : Nat}
    (hnk : n <= k) :
    scaledLogVaryingMass mu event k <=
      scaledLogMass mu (varyingEventTailClosure event n) k := by
  unfold scaledLogVaryingMass scaledLogMass
  apply EReal.div_le_div_right_of_nonneg (by positivity)
  apply ENNReal.log_le_log
  apply measure_mono
  intro x hx
  exact subset_closure ⟨k, hnk, hx⟩

/-- A good-rate closed upper bound contracts uniformly over a varying event
family once its outer limit avoids the chosen compact rate sublevel. -/
theorem varyingEvent_closed_upper_at_ennreal_level
    {X : Type w} [MeasurableSpace X] [TopologicalSpace X] [T2Space X]
    (mu : Nat -> Measure X) (event : Nat -> Set X) (I : X -> ENNReal)
    (level : ENNReal)
    (hmass : StateDepMOR.PoissonUpperAssembly.MassLeOne mu)
    (hcompact : IsCompact {x | I x <= level})
    (hclosedUpper :
      forall F : Set X, IsClosed F ->
        limsup (scaledLogMass mu F) atTop <=
          -(rateInf I F : EReal))
    (houter :
      Disjoint (varyingEventOuterLimit event) {x | I x <= level}) :
    limsup (scaledLogVaryingMass mu event) atTop <=
      -((level : ENNReal) : EReal) := by
  obtain ⟨n, hn⟩ :=
    exists_tailClosure_disjoint_compactSublevel
      event I level hcompact houter
  let F := varyingEventTailClosure event n
  have hrate : level <= rateInf I F := by
    unfold rateInf
    apply le_sInf
    intro y hy
    obtain ⟨x, hxF, rfl⟩ := hy
    exact le_of_not_ge (Set.disjoint_left.mp hn hxF)
  have hfixed :
      limsup (scaledLogMass mu F) atTop <=
        -((level : ENNReal) : EReal) := by
    exact (hclosedUpper F isClosed_closure).trans
      (EReal.neg_le_neg_iff.mpr
        (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hrate))
  have hpoint :
      Filter.Eventually
        (fun k =>
          scaledLogVaryingMass mu event k <=
            scaledLogMass mu F k)
        atTop := by
    filter_upwards [eventually_ge_atTop n] with k hk
    exact scaledLogVaryingMass_le_tailClosure mu event hk
  exact (limsup_le_limsup hpoint
    (Filter.isCoboundedUnder_le_of_le atTop fun _ => bot_le)
    (Filter.isBoundedUnder_of_eventually_le
      (Eventually.of_forall
        (StateDepMOR.PoissonUpperAssembly.scaledLogMass_nonpos_of_mass_le_one
          mu hmass F)))).trans hfixed

/-! ## Concrete triangular calendar events -/

/-- At physical size `n + 1`, the calendar input paths that can drive some
finite initial queue state from Lyapunov level at most `rho` to the queue
boundary by time `H`. Regular samples are used only to identify the raw
calendar path with the totalized queue execution; they have full measure. -/
def finiteCalendarExcursionEvent
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (rho H : Real) (n : Nat) :
    Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H) :=
  {a | exists
      (z : JobState Buffer (n.succPNat : Nat))
      (omega : StateDepMOR.Network.CalendarPoissonSample
        (Buffer := Buffer) (Server := Server)),
      StateDepMOR.PoissonSamplePath.IsRegularSample omega /\
      StateDepMOR.PoissonSamplePath.calendarPath
          N H n.succPNat omega = a /\
      Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U n.succPNat z omega 0 i) <= rho /\
      Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U n.succPNat z omega H i) = 1}

/-- Every finite-action point in the upper limit of the varying finite-size
excursion events is a genuine fluid excursion on the same horizon. -/
theorem finiteCalendarExcursion_outerLimit_subset
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    {rho H : Real} (hrho : rho < 1) (hH : 0 < H)
    {a : StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H}
    (ha :
      a ∈ varyingEventOuterLimit
        (finiteCalendarExcursionEvent N alpha U rho H))
    (hfinite :
      Ne
        (poissonPathRate N H
          (StateDepMOR.PoissonSamplePath.asMatrix H a))
        (Top.top : ENNReal)) :
    a ∈ fluidExcursionInputSet N alpha U rho H := by
  classical
  obtain ⟨Kindex, hKindex, path, hpathMem, hpath⟩ :=
    exists_strictMono_event_sequence_tendsto_of_mem_outerLimit
      (finiteCalendarExcursionEvent N alpha U rho H) ha
  have hwitness (n : Nat) :
      exists
        (z : JobState Buffer ((Kindex n).succPNat : Nat))
        (omega : StateDepMOR.Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server)),
        StateDepMOR.PoissonSamplePath.IsRegularSample omega /\
        StateDepMOR.PoissonSamplePath.calendarPath
            N H (Kindex n).succPNat omega = path n /\
        Lyapunov.LAlphaAmbient (fun i => alpha i)
            (fun i =>
              N.totalCalendarScaledQueueStateFrom
                U (Kindex n).succPNat z omega 0 i) <= rho /\
        Lyapunov.LAlphaAmbient (fun i => alpha i)
            (fun i =>
              N.totalCalendarScaledQueueStateFrom
                U (Kindex n).succPNat z omega H i) = 1 :=
    hpathMem n
  choose z omega hregular hcalendar hstart hhit using hwitness
  let K : Nat -> PNat := fun n => (Kindex n).succPNat
  have hK : StrictMono K := by
    intro m n hmn
    exact Nat.succPNat_strictMono (hKindex hmn)
  have hJ1 :
      Tendsto
        (fun n =>
          StateDepMOR.PoissonSamplePath.calendarPath
            N H (K n) (omega n))
        atTop (nhds a) := by
    apply hpath.congr'
    exact Eventually.of_forall fun n => by
      simpa only [K] using (hcalendar n).symm
  obtain ⟨x0, s, tau, htau, hs, htauHit, hbefore⟩ :=
    StateDepMOR.Network.exists_triangular_calendar_fluid_excursion
      N U alpha halpha rho H hrho hH K hK z omega a
        (fun _ => H) (fun _ => ⟨hH.le, le_rfl⟩)
        hregular hJ1 hfinite hstart hhit
  exact ⟨x0, s, tau, htau, hs, htauHit, hbefore⟩

/-- At physical size `n + 1`, the repaired term-(c) event: the queue starts
below `rho`, does not return below `delta`, and remains strictly inside the
queue boundary throughout the block. -/
def finiteCalendarPersistenceEvent
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (delta rho H : Real) (n : Nat) :
    Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H) :=
  {a | exists
      (z : JobState Buffer (n.succPNat : Nat))
      (omega : StateDepMOR.Network.CalendarPoissonSample
        (Buffer := Buffer) (Server := Server)),
      StateDepMOR.PoissonSamplePath.IsRegularSample omega /\
      StateDepMOR.PoissonSamplePath.calendarPath
          N H n.succPNat omega = a /\
      Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U n.succPNat z omega 0 i) <= rho /\
      forall t, t ∈ Icc (0 : Real) H ->
        delta <=
            Lyapunov.LAlphaAmbient (fun i => alpha i)
              (fun i =>
                N.totalCalendarScaledQueueStateFrom
                  U n.succPNat z omega t i) /\
          Lyapunov.LAlphaAmbient (fun i => alpha i)
              (fun i =>
                N.totalCalendarScaledQueueStateFrom
                  U n.succPNat z omega t i) < 1}

/-- Every finite-action point in the upper limit of the varying repaired
term-(c) events belongs to the boundary-inclusive closed fluid envelope. -/
theorem finiteCalendarPersistence_outerLimit_subset
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {delta rho H : Real} (hH : 0 < H)
    {a : StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H}
    (ha :
      a ∈ varyingEventOuterLimit
        (finiteCalendarPersistenceEvent N alpha U delta rho H))
    (hfinite :
      Ne
        (poissonPathRate N H
          (StateDepMOR.PoissonSamplePath.asMatrix H a))
        (Top.top : ENNReal)) :
    a ∈ persistentFluidClosedInputSet N alpha U delta rho H := by
  classical
  obtain ⟨Kindex, hKindex, path, hpathMem, hpath⟩ :=
    exists_strictMono_event_sequence_tendsto_of_mem_outerLimit
      (finiteCalendarPersistenceEvent N alpha U delta rho H) ha
  have hwitness (n : Nat) :
      exists
        (z : JobState Buffer ((Kindex n).succPNat : Nat))
        (omega : StateDepMOR.Network.CalendarPoissonSample
          (Buffer := Buffer) (Server := Server)),
        StateDepMOR.PoissonSamplePath.IsRegularSample omega /\
        StateDepMOR.PoissonSamplePath.calendarPath
            N H (Kindex n).succPNat omega = path n /\
        Lyapunov.LAlphaAmbient (fun i => alpha i)
            (fun i =>
              N.totalCalendarScaledQueueStateFrom
                U (Kindex n).succPNat z omega 0 i) <= rho /\
        forall t, t ∈ Icc (0 : Real) H ->
          delta <=
              Lyapunov.LAlphaAmbient (fun i => alpha i)
                (fun i =>
                  N.totalCalendarScaledQueueStateFrom
                    U (Kindex n).succPNat z omega t i) /\
            Lyapunov.LAlphaAmbient (fun i => alpha i)
                (fun i =>
                  N.totalCalendarScaledQueueStateFrom
                    U (Kindex n).succPNat z omega t i) < 1 :=
    hpathMem n
  choose z omega hregular hcalendar hstart hband using hwitness
  let K : Nat -> PNat := fun n => (Kindex n).succPNat
  have hK : StrictMono K := by
    intro m n hmn
    exact Nat.succPNat_strictMono (hKindex hmn)
  have hJ1 :
      Tendsto
        (fun n =>
          StateDepMOR.PoissonSamplePath.calendarPath
            N H (K n) (omega n))
        atTop (nhds a) := by
    apply hpath.congr'
    exact Eventually.of_forall fun n => by
      simpa only [K] using (hcalendar n).symm
  obtain ⟨x0, s, hs, hclosedBand⟩ :=
    StateDepMOR.Network.exists_triangular_calendar_fluid_persistence
      N U alpha delta rho H hH K hK z omega a hregular hJ1 hfinite
        hstart hband
  exact ⟨x0, s, hs, hclosedBand⟩

/-! ## Uniform varying-size J1 upper estimates -/

/-- Uniform finite-size excursion contraction on any observation horizon
`H` that contains the fixed paper horizon `T`. -/
theorem finiteCalendarExcursion_varying_upper
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    {rho T H c d : Real}
    (hT : 0 < T) (hTH : T <= H)
    (hrho : rho < 1) (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (hd : 0 <= d) (hdcost : d < c * (1 - rho)) :
    limsup
        (scaledLogVaryingMass
          (StateDepMOR.PoissonSamplePath.calendarPathLaw N H)
          (finiteCalendarExcursionEvent N alpha U rho H))
        atTop <=
      -(d : EReal) := by
  let I :
      StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H -> ENNReal :=
    fun a =>
      poissonPathRate N H
        (StateDepMOR.PoissonSamplePath.asMatrix H a)
  have hH : 0 < H := hT.trans_le hTH
  letI : MetricSpace
      (StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H) :=
    StateDepMOR.PoissonSamplePath.pathMetricSpace H hH
  letI : T0Space
      (StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H) :=
    { t0 := fun x y hxy =>
        StateDepMOR.PoissonSamplePath.j1EDist_eq_zero_imp_eq
          hH hxy.edist_eq_zero }
  have hcompact :
      IsCompact {a | I a <= ENNReal.ofReal d} := by
    simpa only [I] using
      StateDepMOR.PoissonSamplePath.isCompact_poissonPathRate_sublevel
        N hH d
  have houter :
      Disjoint
        (varyingEventOuterLimit
          (finiteCalendarExcursionEvent N alpha U rho H))
        {a | I a <= ENNReal.ofReal d} := by
    rw [Set.disjoint_left]
    intro a haouter halevel
    have hfinite : Ne (I a) (Top.top : ENNReal) :=
      ne_of_lt (halevel.trans_lt ENNReal.ofReal_lt_top)
    have hfluid :
        a ∈ fluidExcursionInputSet N alpha U rho H :=
      finiteCalendarExcursion_outerLimit_subset
        N alpha halpha U hrho hH haouter hfinite
    have hlower :
        ENNReal.ofReal (c * (1 - rho)) <= I a :=
      fluidExcursionInputSet_action_lower_fixed_target_horizon
        N alpha U hT hTH hrho hcpos hc hfluid
    have hstrict :
        ENNReal.ofReal d <
          ENNReal.ofReal (c * (1 - rho)) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd).2 hdcost
    exact (not_lt_of_ge halevel) (hstrict.trans_le hlower)
  have hupper :=
    varyingEvent_closed_upper_at_ennreal_level
      (StateDepMOR.PoissonSamplePath.calendarPathLaw N H)
      (finiteCalendarExcursionEvent N alpha U rho H)
      I (ENNReal.ofReal d)
      (StateDepMOR.PoissonUpperFinal.calendarPathLaw_massLeOne N hH)
      hcompact
      (fun F hF =>
        StateDepMOR.PoissonSamplePath.calendarPathLaw_closed_upper_bound
          N hH F hF)
      houter
  simpa [EReal.coe_ennreal_ofReal, max_eq_left hd] using hupper

/-- The repaired persistence event has a uniform varying-size upper bound
with an affine exponent whose slope is strictly positive. -/
theorem exists_finiteCalendarPersistence_varying_upper
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative : NegativeDriftCondition (N := N) alpha U)
    {delta rho : Real} (hdelta : 0 < delta) :
    exists a : Real, 0 < a /\ exists b : Real,
      forall (H : Real), 0 < H ->
      forall d : Real, 0 <= d -> d < a * H - b ->
        limsup
            (scaledLogVaryingMass
              (StateDepMOR.PoissonSamplePath.calendarPathLaw N H)
              (finiteCalendarPersistenceEvent
                N alpha U delta rho H))
            atTop <=
          -(d : EReal) := by
  obtain ⟨a, ha, b, hlower⟩ :=
    persistentFluidInputClosed_action_linear_lower
      N alpha halpha U hnegative (rho := rho) hdelta
  refine ⟨a, ha, b, ?_⟩
  intro H hH d hd hdaction
  let I :
      StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H -> ENNReal :=
    fun path =>
      poissonPathRate N H
        (StateDepMOR.PoissonSamplePath.asMatrix H path)
  letI : MetricSpace
      (StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H) :=
    StateDepMOR.PoissonSamplePath.pathMetricSpace H hH
  letI : T0Space
      (StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H) :=
    { t0 := fun x y hxy =>
        StateDepMOR.PoissonSamplePath.j1EDist_eq_zero_imp_eq
          hH hxy.edist_eq_zero }
  have hcompact :
      IsCompact {path | I path <= ENNReal.ofReal d} := by
    simpa only [I] using
      StateDepMOR.PoissonSamplePath.isCompact_poissonPathRate_sublevel
        N hH d
  have houter :
      Disjoint
        (varyingEventOuterLimit
          (finiteCalendarPersistenceEvent N alpha U delta rho H))
        {path | I path <= ENNReal.ofReal d} := by
    rw [Set.disjoint_left]
    intro path hpathOuter hpathLevel
    have hfinite : Ne (I path) (Top.top : ENNReal) :=
      ne_of_lt (hpathLevel.trans_lt ENNReal.ofReal_lt_top)
    have hpersistent :
        path ∈ persistentFluidClosedInputSet
          N alpha U delta rho H :=
      finiteCalendarPersistence_outerLimit_subset
        N alpha U hH hpathOuter hfinite
    have hrate :
        ENNReal.ofReal (a * H - b) <= I path :=
      hlower H
        (StateDepMOR.PoissonSamplePath.asMatrix H path)
        hpersistent
    have hstrict :
        ENNReal.ofReal d < ENNReal.ofReal (a * H - b) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd).2 hdaction
    exact (not_lt_of_ge hpathLevel) (hstrict.trans_le hrate)
  have hupper :=
    varyingEvent_closed_upper_at_ennreal_level
      (StateDepMOR.PoissonSamplePath.calendarPathLaw N H)
      (finiteCalendarPersistenceEvent N alpha U delta rho H)
      I (ENNReal.ofReal d)
      (StateDepMOR.PoissonUpperFinal.calendarPathLaw_massLeOne N hH)
      hcompact
      (fun F hF =>
        StateDepMOR.PoissonSamplePath.calendarPathLaw_closed_upper_bound
          N hH F hF)
      houter
  simpa [EReal.coe_ennreal_ofReal, max_eq_left hd] using hupper

end StateDepMOR.PaperStatements.Network
