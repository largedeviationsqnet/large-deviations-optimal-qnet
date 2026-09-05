import StateDepMOR.FluidExistenceProof
import StateDepMOR.SMWTrajectoryExecution
import StateDepMOR.FluidResting
import StateDepMOR.PoissonSamplePathLDP
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

open scoped BigOperators Topology
open Filter MeasureTheory Set

set_option maxHeartbeats 1600000

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]
variable [LinearOrder Buffer]

variable (N : StateDepMOR.Network Buffer Server)

noncomputable def normalizedJobState
    (K : PNat) (x : JobState Buffer (K : Nat)) :
    stdSimplex Real Buffer where
  val i := (x i : Real) / (K : Nat)
  property := by
    constructor
    · intro i
      positivity
    · rw [<- Finset.sum_div]
      have htotal :
          Finset.univ.sum (fun i => (x i : Real)) = (K : Nat) := by
        exact_mod_cast x.total_jobs
      rw [htotal]
      exact div_self (by positivity)

theorem exists_convergent_normalized_jobState_subsequence
    (K : Nat -> PNat)
    (x : forall n, JobState Buffer (K n : Nat)) :
    exists q : Nat -> Nat, StrictMono q /\
      exists a : stdSimplex Real Buffer,
        Tendsto
          (fun n => normalizedJobState (K (q n)) (x (q n)))
          atTop (nhds a) := by
  obtain ⟨a, q, hq, hconv⟩ :=
    CompactSpace.tendsto_subseq
      (fun n => normalizedJobState (K n) (x n))
  exact ⟨q, hq, a, hconv⟩

private theorem runTokens_append_local {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (xs ys : List (StateDepMOR.Network.TokenType
      (Buffer := Buffer) (Server := Server))) :
    N.runTokens U x (xs ++ ys) =
      N.runTokens U (N.runTokens U x xs) ys := by
  induction xs generalizing x with
  | nil => simp [StateDepMOR.Network.runTokens]
  | cons jk xs ih =>
      simp only [List.cons_append, StateDepMOR.Network.runTokens]
      exact ih (N.queueStep U x jk)

private theorem queueStep_coordinate_sub_local {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : StateDepMOR.Network.TokenType
      (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    ((N.queueStep U x jk i : Nat) : Real) - (x i : Real) =
      (match U x jk.1 jk.2 with
        | none => 0
        | some _ => if jk.2 = i then 1 else 0) -
      (if U x jk.1 jk.2 = some i then 1 else 0) := by
  have h := N.jobsIn_queueStep_sub U x ({i} : Finset Buffer) jk
  cases haction : U x jk.1 jk.2 with
  | none => simpa [JobState.jobsIn, StateDepMOR.Network.cutChange,
      haction] using h
  | some q =>
      by_cases hqi : q = i
      · subst q
        simpa [JobState.jobsIn, StateDepMOR.Network.cutChange,
          haction] using h
      · simpa [JobState.jobsIn, StateDepMOR.Network.cutChange,
          haction, hqi] using h

private theorem runTokens_coordinate_change_le_length {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (StateDepMOR.Network.TokenType
      (Buffer := Buffer) (Server := Server)))
    (i : Buffer) :
    abs (((N.runTokens U x tokens i : Nat) : Real) - (x i : Real)) <=
      tokens.length := by
  induction tokens generalizing x with
  | nil => simp [StateDepMOR.Network.runTokens]
  | cons jk rest ih =>
      simp only [StateDepMOR.Network.runTokens, List.length_cons]
      let y := N.queueStep U x jk
      have htail := ih y
      have hstep :
          abs (((y i : Nat) : Real) - (x i : Real)) <= 1 := by
        have heq := queueStep_coordinate_sub_local N U x jk i
        change ((y i : Nat) : Real) - (x i : Real) = _ at heq
        rw [heq]
        cases haction : U x jk.1 jk.2 with
        | none => simp [haction]
        | some q =>
            by_cases hqi : q = i
            · subst q
              by_cases hki : jk.2 = i
              · simp [hki]
              · simp [hki]
            · by_cases hki : jk.2 = i
              · simp [haction, hqi, hki]
              · simp [haction, hqi, hki]
      calc
        abs (((N.runTokens U y rest i : Nat) : Real) - (x i : Real)) <=
            abs (((N.runTokens U y rest i : Nat) : Real) - (y i : Real)) +
              abs (((y i : Nat) : Real) - (x i : Real)) := abs_sub_le _ _ _
        _ <= rest.length + 1 := add_le_add htail hstep
        _ = (jk :: rest).length := by simp

private theorem allTokenCounts_sum_local
    (tokens : List (StateDepMOR.Network.TokenType
      (Buffer := Buffer) (Server := Server))) :
    (Finset.univ.sum fun jk : Prod Server Buffer => tokens.count jk) =
      tokens.length := by
  classical
  induction tokens with
  | nil => simp
  | cons a tokens ih =>
      simp only [List.count_cons, List.length_cons]
      rw [Finset.sum_add_distrib, ih]
      have hone :
          Finset.univ.sum
              (fun jk : Prod Server Buffer =>
                if a == jk then 1 else 0) = 1 := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro b _ hba
          simp [Ne.symm hba]
        · simp
      rw [hone]

private theorem totalRawCalendarEvents_token_count_local
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) :
    ((N.totalRawCalendarEvents K omega t).map fun event => event.1).count
        (j, k) =
      N.totalCalendarTokenCount K omega t j k := by
  classical
  simp only [StateDepMOR.Network.totalRawCalendarEvents,
    StateDepMOR.Network.rawCalendarEvents,
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

private theorem totalCalendarTokenPrefix_count_local
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) :
    (N.totalCalendarTokenPrefix K omega t).count (j, k) =
      N.totalCalendarTokenCount K omega t j k := by
  classical
  unfold StateDepMOR.Network.totalCalendarTokenPrefix
  calc
    ((N.totalChronologicalCalendarEvents K omega t).map
        fun event => event.1).count (j, k) =
        ((N.totalRawCalendarEvents K omega t).map
          fun event => event.1).count (j, k) :=
      ((N.totalChronologicalCalendarEvents_perm_raw K omega t).map
        fun event => event.1).count_eq _
    _ = N.totalCalendarTokenCount K omega t j k :=
      totalRawCalendarEvents_token_count_local N K omega t j k

private theorem totalCalendarScaledInput_eq_prefix_count_local
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) :
    N.totalCalendarScaledInput K omega t j k =
      ((N.totalCalendarTokenPrefix K omega t).count (j, k) : Real) /
        (K : Nat) := by
  unfold StateDepMOR.Network.totalCalendarScaledInput
    StateDepMOR.Network.calendarScaledInput
  rw [totalCalendarTokenPrefix_count_local N]
  rfl

private noncomputable def calendarIntervalBatchLocal
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (s t : Real) :
    List (StateDepMOR.Network.TokenType
      (Buffer := Buffer) (Server := Server)) :=
  (N.totalCalendarTokenPrefix K omega t).drop
    (N.totalCalendarTokenPrefix K omega s).length

private theorem calendarTokenPrefix_interval_local
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    {s t : Real} (hst : s <= t) :
    N.totalCalendarTokenPrefix K omega t =
      N.totalCalendarTokenPrefix K omega s ++
        calendarIntervalBatchLocal N K omega s t := by
  unfold calendarIntervalBatchLocal
  obtain ⟨suffix, hsuffix⟩ :=
    N.totalCalendarTokenPrefix_append K omega hst
  rw [hsuffix, List.drop_left]

private theorem calendarIntervalBatch_count_local
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    {s t : Real} (hst : s <= t) (j : Server) (k : Buffer) :
    (calendarIntervalBatchLocal N K omega s t).count (j, k) =
      (N.totalCalendarTokenPrefix K omega t).count (j, k) -
        (N.totalCalendarTokenPrefix K omega s).count (j, k) := by
  rw [calendarTokenPrefix_interval_local N K omega hst,
    List.count_append, Nat.add_sub_cancel_left]

private theorem totalCalendarScaledInput_mono_local
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    {s t : Real} (hst : s <= t) (j : Server) (k : Buffer) :
    N.totalCalendarScaledInput K omega s j k <=
      N.totalCalendarScaledInput K omega t j k := by
  rw [totalCalendarScaledInput_eq_prefix_count_local N,
    totalCalendarScaledInput_eq_prefix_count_local N]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    (show
      (N.totalCalendarTokenPrefix K omega s).count (j, k) <=
        (N.totalCalendarTokenPrefix K omega t).count (j, k) by
      rw [calendarTokenPrefix_interval_local N K omega hst,
        List.count_append]
      omega)

private theorem calendarIntervalBatch_scaled_length_local
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    {s t : Real} (hst : s <= t) :
    ((calendarIntervalBatchLocal N K omega s t).length : Real) /
        (K : Nat) =
      Finset.univ.sum (fun jk : Prod Server Buffer =>
        N.totalCalendarScaledInput K omega t jk.1 jk.2 -
          N.totalCalendarScaledInput K omega s jk.1 jk.2) := by
  rw [show
    (calendarIntervalBatchLocal N K omega s t).length =
      Finset.univ.sum (fun jk : Prod Server Buffer =>
        (calendarIntervalBatchLocal N K omega s t).count jk) by
    exact (allTokenCounts_sum_local
      (Buffer := Buffer) (Server := Server)
      (calendarIntervalBatchLocal N K omega s t)).symm]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro jk _
  rw [totalCalendarScaledInput_eq_prefix_count_local N,
    totalCalendarScaledInput_eq_prefix_count_local N,
    calendarIntervalBatch_count_local N K omega hst]
  have hle :
      (N.totalCalendarTokenPrefix K omega s).count jk <=
        (N.totalCalendarTokenPrefix K omega t).count jk := by
    rw [calendarTokenPrefix_interval_local N K omega hst,
      List.count_append]
    omega
  push_cast
  rw [Nat.cast_sub hle]
  ring

private theorem totalCalendarScaledQueueStateFrom_ordered_dist_le_input
    (U : N.DeterministicPolicySequence)
    (K : PNat) (x : JobState Buffer (K : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    {s t : Real} (hst : s <= t) (i : Buffer) :
    dist (N.totalCalendarScaledQueueStateFrom U K x omega s i)
        (N.totalCalendarScaledQueueStateFrom U K x omega t i) <=
      Finset.univ.sum (fun jk : Prod Server Buffer =>
        dist (N.totalCalendarScaledInput K omega s jk.1 jk.2)
          (N.totalCalendarScaledInput K omega t jk.1 jk.2)) := by
  have hprefix :=
    calendarTokenPrefix_interval_local N K omega hst
  have hchange :=
    runTokens_coordinate_change_le_length N (U K)
      (N.runTokens (U K) x (N.totalCalendarTokenPrefix K omega s))
      (calendarIntervalBatchLocal N K omega s t) i
  rw [<- runTokens_append_local N, <- hprefix] at hchange
  unfold StateDepMOR.Network.totalCalendarScaledQueueStateFrom
  rw [Real.dist_eq, <- sub_div, abs_div,
    abs_of_pos (show (0 : Real) < (K : Nat) by positivity)]
  calc
    abs
        (((N.runTokens (U K) x
            (N.totalCalendarTokenPrefix K omega s) i : Nat) : Real) -
          ((N.runTokens (U K) x
            (N.totalCalendarTokenPrefix K omega t) i : Nat) : Real)) /
        (K : Nat) <=
        ((calendarIntervalBatchLocal N K omega s t).length : Real) /
          (K : Nat) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa [abs_sub_comm] using hchange
    _ = Finset.univ.sum (fun jk : Prod Server Buffer =>
        N.totalCalendarScaledInput K omega t jk.1 jk.2 -
          N.totalCalendarScaledInput K omega s jk.1 jk.2) :=
      calendarIntervalBatch_scaled_length_local N K omega hst
    _ = Finset.univ.sum (fun jk : Prod Server Buffer =>
        dist (N.totalCalendarScaledInput K omega s jk.1 jk.2)
          (N.totalCalendarScaledInput K omega t jk.1 jk.2)) := by
      apply Finset.sum_congr rfl
      intro jk _
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg
        (sub_nonneg.mpr
          (totalCalendarScaledInput_mono_local N K omega hst _ _))]

theorem totalCalendarScaledQueueStateFrom_dist_le_input
    (U : N.DeterministicPolicySequence)
    (K : PNat) (x : JobState Buffer (K : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (s t : Real) (i : Buffer) :
    dist (N.totalCalendarScaledQueueStateFrom U K x omega s i)
        (N.totalCalendarScaledQueueStateFrom U K x omega t i) <=
      Finset.univ.sum (fun jk : Prod Server Buffer =>
        dist (N.totalCalendarScaledInput K omega s jk.1 jk.2)
          (N.totalCalendarScaledInput K omega t jk.1 jk.2)) := by
  rcases le_total s t with hst | hts
  · exact totalCalendarScaledQueueStateFrom_ordered_dist_le_input
      N U K x omega hst i
  · rw [dist_comm]
    have h :=
      totalCalendarScaledQueueStateFrom_ordered_dist_le_input
        N U K x omega hts i
    simpa [dist_comm] using h

private theorem monotone_pointwise_to_linear_uniform
    {T c : Real} (hT : 0 < T) (hc : 0 <= c)
    (f : Nat -> Real -> Real)
    (hmono : forall n, Monotone (f n))
    (hlim : forall t, t ∈ Icc (0 : Real) T ->
      Tendsto (fun n => f n t) atTop (nhds (c * t))) :
    forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall t, t ∈ Icc (0 : Real) T ->
          abs (f n t - c * t) < epsilon := by
  intro epsilon hepsilon
  obtain ⟨m, hm⟩ :=
    exists_nat_gt (3 * c * T / epsilon)
  let M : Nat := m + 1
  have hMnat : 0 < M := by omega
  have hMreal : (0 : Real) < M := by exact_mod_cast hMnat
  have hmesh : c * (T / M) < epsilon / 3 := by
    have hratio :
        3 * c * T / epsilon < (M : Real) := by
      exact hm.trans_le (by exact_mod_cast Nat.le_add_right m 1)
    have hmul : 3 * c * T < (M : Real) * epsilon :=
      (div_lt_iff₀ hepsilon).1 hratio
    calc
      c * (T / M) = (c * T) / M := by ring
      _ < epsilon / 3 := by
        rw [div_lt_div_iff₀ hMreal (show (0 : Real) < 3 by norm_num)]
        nlinarith
  have hpoint (l : Fin (M + 1)) :
      Tendsto
        (fun n => f n (T * (l : Nat) / M))
        atTop (nhds (c * (T * (l : Nat) / M))) := by
    apply hlim
    constructor
    · positivity
    · apply (div_le_iff₀ hMreal).2
      have hl : (l : Nat) <= M := by omega
      have hlreal : ((l : Nat) : Real) <= M := by exact_mod_cast hl
      nlinarith
  have hevent :
      forall l : Fin (M + 1),
        ∀ᶠ n in atTop,
          abs (f n (T * (l : Nat) / M) -
            c * (T * (l : Nat) / M)) < epsilon / 3 := by
    intro l
    simpa [Real.dist_eq] using
      (hpoint l).eventually
        (Metric.ball_mem_nhds _ (show 0 < epsilon / 3 by positivity))
  have hall :
      ∀ᶠ n in atTop,
        forall l : Fin (M + 1),
          abs (f n (T * (l : Nat) / M) -
            c * (T * (l : Nat) / M)) < epsilon / 3 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      (eventually_all.2 hevent)
  obtain ⟨n0, hn0⟩ := (eventually_atTop.1 hall)
  refine ⟨n0, fun n hn t ht => ?_⟩
  have hn := hn0 n hn
  by_cases htT : t = T
  · subst t
    have hMlt : M < M + 1 := by omega
    have hMT :
        abs (f n T - c * T) < epsilon / 3 := by
      simpa using hn ⟨M, hMlt⟩
    exact hMT.trans (by linarith)
  · let l : Nat := Nat.floor ((M : Real) * t / T)
    have hr0 : 0 <= (M : Real) * t / T :=
      div_nonneg (mul_nonneg hMreal.le ht.1) hT.le
    have hrMlt : (M : Real) * t / T < M := by
      apply (div_lt_iff₀ hT).2
      have htt : t < T := lt_of_le_of_ne ht.2 htT
      nlinarith
    have hlM : l < M := by
      exact_mod_cast (Nat.floor_lt hr0).2 hrMlt
    have hl0 : T * (l : Real) / M <= t := by
      have hfloor : (l : Real) <= (M : Real) * t / T :=
        Nat.floor_le hr0
      apply (div_le_iff₀ hMreal).2
      apply (le_div_iff₀ hT).1 at hfloor
      nlinarith
    have hltNext : t < T * ((l + 1 : Nat) : Real) / M := by
      have hfloor := Nat.lt_floor_add_one ((M : Real) * t / T)
      apply (lt_div_iff₀ hMreal).2
      apply (div_lt_iff₀ hT).1 at hfloor
      norm_num at hfloor ⊢
      nlinarith
    have hlmem : l < M + 1 := by omega
    have hnextmem : l + 1 < M + 1 := by omega
    have hlo := hn ⟨l, hlmem⟩
    have hhi := hn ⟨l + 1, hnextmem⟩
    have hmonoLo :
        f n (T * (l : Real) / M) <= f n t :=
      hmono n hl0
    have hmonoHi :
        f n t <= f n (T * ((l + 1 : Nat) : Real) / M) :=
      hmono n hltNext.le
    rw [abs_lt] at hlo hhi ⊢
    constructor
    · have hcontrolLo :
          c * t - c * (T * (l : Real) / M) <= c * (T / M) := by
        have hgap : t - T * (l : Real) / M <= T / M := by
          exact le_of_lt <| calc
            t - T * (l : Real) / M <
                T * ((l + 1 : Nat) : Real) / M -
                  T * (l : Real) / M := sub_lt_sub_right hltNext _
            _ = T / M := by push_cast; ring
        have := mul_le_mul_of_nonneg_left hgap hc
        nlinarith
      nlinarith [hlo.1]
    · have hcontrolHi :
          c * (T * ((l + 1 : Nat) : Real) / M) - c * t <=
            c * (T / M) := by
        have hgap :
            T * ((l + 1 : Nat) : Real) / M - t <= T / M := by
          calc
            T * ((l + 1 : Nat) : Real) / M - t <=
                T * ((l + 1 : Nat) : Real) / M -
                  T * (l : Real) / M := sub_le_sub_left hl0 _
            _ = T / M := by push_cast; ring
        have := mul_le_mul_of_nonneg_left hgap hc
        nlinarith
      nlinarith [hhi.2]

theorem totalCalendarScaledInput_uniformlyOnIcc
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (K : Nat -> PNat) (hK : StrictMono K)
    {T : Real} (hT : 0 < T) :
    UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) omega t jk.1 jk.2)
      (fun t jk => N.phi jk.1 jk.2 * t) := by
  intro epsilon hepsilon
  have hcoord (jk : Server × Buffer) :
      exists n0, forall n : Nat, n0 <= n ->
        forall t, t ∈ Icc (0 : Real) T ->
          abs (N.totalCalendarScaledInput (K n) omega t jk.1 jk.2 -
            N.phi jk.1 jk.2 * t) < epsilon := by
    apply monotone_pointwise_to_linear_uniform hT
      (N.phi_nonneg jk.1 jk.2)
    · intro n s t hst
      exact totalCalendarScaledInput_mono_local N (K n) omega hst _ _
    · intro t ht
      exact N.totalCalendarScaledInput_tendsto
        omega K hK t ht.1 jk.1 jk.2
    · exact hepsilon
  choose bound hbound using hcoord
  refine ⟨Finset.univ.sup bound, fun n hn t ht jk => ?_⟩
  exact hbound jk n
    ((Finset.le_sup (Finset.mem_univ jk)).trans hn) t ht

private def hatWeightLocal (r : Real) (l : Nat) : Real :=
  max 0 (1 - abs (r - l))

private noncomputable def polygonalInterpolateLocal
    (K : PNat) (values : Nat -> Real) (t T : Real) : Real :=
  Finset.sum (Finset.range ((K : Nat) + 1)) fun l =>
    hatWeightLocal (((K : Nat) : Real) * t / T) l * values l

private theorem continuous_polygonalInterpolateLocal
    (K : PNat) (values : Nat -> Real) (T : Real) :
    Continuous (fun t => polygonalInterpolateLocal K values t T) := by
  unfold polygonalInterpolateLocal
  apply continuous_finsetSum
  intro l _
  apply Continuous.mul
  · apply Continuous.max continuous_const
    apply Continuous.sub continuous_const
    exact (Continuous.abs (continuous_id.sub continuous_const)).comp
      (continuous_const.mul continuous_id |>.div_const T)
  · exact continuous_const

private theorem hatWeightLocal_nonneg (r : Real) (l : Nat) :
    0 <= hatWeightLocal r l :=
  le_max_left _ _

private theorem hatWeightLocal_eq_zero_of_one_le_abs
    {r : Real} {l : Nat} (h : 1 <= abs (r - l)) :
    hatWeightLocal r l = 0 := by
  unfold hatWeightLocal
  rw [max_eq_left]
  linarith

private theorem sum_hatWeightLocal_eq_one
    (K : PNat) {r : Real}
    (hr0 : 0 <= r) (hrK : r <= (K : Nat)) :
    Finset.sum (Finset.range ((K : Nat) + 1))
      (hatWeightLocal r) = 1 := by
  classical
  let n : Nat := Nat.floor r
  have hn_le : (n : Real) <= r := Nat.floor_le hr0
  have hr_lt : r < (n : Real) + 1 := Nat.lt_floor_add_one r
  by_cases heq : r = (K : Nat)
  · subst r
    rw [Finset.sum_eq_single (K : Nat)]
    · simp [hatWeightLocal]
    · intro l hl hlne
      have hlK : l < (K : Nat) + 1 := Finset.mem_range.mp hl
      have hl_le : l <= (K : Nat) := by omega
      apply hatWeightLocal_eq_zero_of_one_le_abs
      rw [abs_of_nonneg]
      · have hcast : (l : Real) + 1 <= (K : Nat) := by
          exact_mod_cast (show l + 1 <= (K : Nat) by omega)
        linarith
      · exact sub_nonneg.mpr (by exact_mod_cast hl_le)
    · simp
  · have hrKlt : r < (K : Nat) := lt_of_le_of_ne hrK heq
    have hnK : n < (K : Nat) := (Nat.floor_lt hr0).2 hrKlt
    have hsubset :
        ({n, n + 1} : Finset Nat) <=
          Finset.range ((K : Nat) + 1) := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    have hzero :
        forall l, l ∈ Finset.range ((K : Nat) + 1) ->
          l ∉ ({n, n + 1} : Finset Nat) ->
          hatWeightLocal r l = 0 := by
      intro l _ hlpair
      have hln : l ≠ n := by
        intro h
        apply hlpair
        simp [h]
      have hln1 : l ≠ n + 1 := by
        intro h
        apply hlpair
        simp [h]
      apply hatWeightLocal_eq_zero_of_one_le_abs
      by_cases hlt : l < n
      · have hcast : (l : Real) + 1 <= n := by
          exact_mod_cast (show l + 1 <= n by omega)
        rw [abs_of_nonneg] <;> linarith
      · have hnlt : n + 1 < l := by omega
        have hcast : (n : Real) + 2 <= l := by
          exact_mod_cast (show n + 2 <= l by omega)
        rw [abs_of_nonpos] <;> linarith
    rw [← Finset.sum_subset hsubset hzero]
    rw [Finset.sum_pair (by omega : n ≠ n + 1)]
    have hleft : 0 <= 1 - abs (r - (n : Real)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hn_le)]
      linarith
    have hright :
        0 <= 1 - abs (r - ((n + 1 : Nat) : Real)) := by
      rw [abs_of_nonpos] <;> norm_num at * <;> linarith
    simp only [hatWeightLocal, max_eq_right hleft,
      max_eq_right hright]
    rw [abs_of_nonneg (sub_nonneg.mpr hn_le), abs_of_nonpos]
    · norm_num at *
      ring
    · norm_num at *
      linarith

private theorem hatWeightLocal_ne_zero_imp
    {r : Real} {l : Nat} (h : hatWeightLocal r l ≠ 0) :
    abs (r - l) < 1 := by
  by_contra hnot
  exact h (hatWeightLocal_eq_zero_of_one_le_abs (not_lt.mp hnot))

private noncomputable def calendarGridTimeLocal
    (T : Real) (K : PNat) (l : Nat) : Real :=
  T * (l : Real) / (K : Nat)

private noncomputable def calendarStatePolygonal
    (U : N.DeterministicPolicySequence)
    (K : PNat) (x : JobState Buffer (K : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (T t : Real) (i : Buffer) : Real :=
  polygonalInterpolateLocal K
    (fun l => N.totalCalendarScaledQueueStateFrom
      U K x omega (calendarGridTimeLocal T K l) i) t T

private theorem continuous_calendarStatePolygonal
    (U : N.DeterministicPolicySequence)
    (K : PNat) (x : JobState Buffer (K : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (T : Real) (i : Buffer) :
    Continuous (fun t => calendarStatePolygonal N U K x omega T t i) :=
  continuous_polygonalInterpolateLocal K _ T

private theorem calendarStatePolygonal_mem_Icc
    (U : N.DeterministicPolicySequence)
    (K : PNat) (x : JobState Buffer (K : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    {T t : Real} (hT : 0 < T) (ht : t ∈ Icc (0 : Real) T)
    (i : Buffer) :
    calendarStatePolygonal N U K x omega T t i ∈ Icc (0 : Real) 1 := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg (mul_nonneg (by positivity) ht.1) hT.le
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hsum := sum_hatWeightLocal_eq_one K hr0 hrK
  have hvalue (l : Nat) :
      N.totalCalendarScaledQueueStateFrom U K x omega
          (calendarGridTimeLocal T K l) i ∈ Icc (0 : Real) 1 := by
    constructor
    · unfold StateDepMOR.Network.totalCalendarScaledQueueStateFrom
      positivity
    · unfold StateDepMOR.Network.totalCalendarScaledQueueStateFrom
      apply (div_le_iff₀ (show (0 : Real) < (K : Nat) by positivity)).2
      have hc :
          (((N.runTokens (U K) x
            (N.totalCalendarTokenPrefix K omega
              (calendarGridTimeLocal T K l))) i : Nat) : Real) <=
            ((K : Nat) : Real) := by
        exact_mod_cast JobState.coordinate_le
          (N.runTokens (U K) x
            (N.totalCalendarTokenPrefix K omega
              (calendarGridTimeLocal T K l))) i
      simpa using hc
  constructor
  · unfold calendarStatePolygonal polygonalInterpolateLocal
    apply Finset.sum_nonneg
    intro l _
    exact mul_nonneg (hatWeightLocal_nonneg _ _) (hvalue l).1
  · unfold calendarStatePolygonal polygonalInterpolateLocal
    calc
      Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
          hatWeightLocal r l *
            N.totalCalendarScaledQueueStateFrom U K x omega
              (calendarGridTimeLocal T K l) i) <=
          Finset.sum (Finset.range ((K : Nat) + 1))
            (fun l => hatWeightLocal r l * 1) := by
        apply Finset.sum_le_sum
        intro l _
        exact mul_le_mul_of_nonneg_left (hvalue l).2
          (hatWeightLocal_nonneg _ _)
      _ = 1 := by simpa using hsum

private theorem totalInput_sum_dist_eventually_small
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (K : Nat -> PNat) (hK : StrictMono K)
    {T epsilon : Real} (hT : 0 < T) (hepsilon : 0 < epsilon) :
    exists n0 delta, 0 < delta /\
      forall n, n0 <= n ->
        forall s, s ∈ Icc (0 : Real) T ->
          forall t, t ∈ Icc (0 : Real) T ->
            abs (s - t) < delta ->
              Finset.univ.sum (fun jk : Server × Buffer =>
                dist
                  (N.totalCalendarScaledInput (K n) omega s jk.1 jk.2)
                  (N.totalCalendarScaledInput (K n) omega t jk.1 jk.2)) <
                epsilon := by
  let C : Real :=
    (Fintype.card (Server × Buffer) : Real) +
      Finset.univ.sum (fun jk : Server × Buffer => N.phi jk.1 jk.2) + 1
  have hC : 0 < C := by
    dsimp [C]
    have hsum : 0 <=
        Finset.univ.sum (fun jk : Server × Buffer => N.phi jk.1 jk.2) :=
      Finset.sum_nonneg fun jk _ => N.phi_nonneg jk.1 jk.2
    positivity
  let eta : Real := epsilon / (8 * C)
  let delta : Real := epsilon / (4 * C)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨n0, hn0⟩ :=
    totalCalendarScaledInput_uniformlyOnIcc N omega K hK hT eta heta
  refine ⟨n0, delta, hdelta, fun n hn s hs t ht hst => ?_⟩
  have hsapprox (jk : Server × Buffer) :
      abs (N.totalCalendarScaledInput (K n) omega s jk.1 jk.2 -
        N.phi jk.1 jk.2 * s) < eta :=
    hn0 n hn s hs jk
  have htapprox (jk : Server × Buffer) :
      abs (N.totalCalendarScaledInput (K n) omega t jk.1 jk.2 -
        N.phi jk.1 jk.2 * t) < eta :=
    hn0 n hn t ht jk
  have hterm (jk : Server × Buffer) :
      dist
          (N.totalCalendarScaledInput (K n) omega s jk.1 jk.2)
          (N.totalCalendarScaledInput (K n) omega t jk.1 jk.2) <
        2 * eta + N.phi jk.1 jk.2 * delta := by
    rw [Real.dist_eq]
    calc
      abs (N.totalCalendarScaledInput (K n) omega s jk.1 jk.2 -
          N.totalCalendarScaledInput (K n) omega t jk.1 jk.2) <=
          abs (N.totalCalendarScaledInput (K n) omega s jk.1 jk.2 -
            N.phi jk.1 jk.2 * s) +
          abs (N.phi jk.1 jk.2 * s -
            N.phi jk.1 jk.2 * t) +
          abs (N.phi jk.1 jk.2 * t -
            N.totalCalendarScaledInput (K n) omega t jk.1 jk.2) := by
        calc
          _ <= abs (N.totalCalendarScaledInput (K n) omega s jk.1 jk.2 -
                N.phi jk.1 jk.2 * s) +
              abs (N.phi jk.1 jk.2 * s -
                N.totalCalendarScaledInput (K n) omega t jk.1 jk.2) :=
            abs_sub_le _ _ _
          _ <= _ := by
            have htri := abs_sub_le
              (N.phi jk.1 jk.2 * s)
              (N.phi jk.1 jk.2 * t)
              (N.totalCalendarScaledInput (K n) omega t jk.1 jk.2)
            linarith
      _ < eta + (N.phi jk.1 jk.2 * delta) + eta := by
        have hmiddle :
            abs (N.phi jk.1 jk.2 * s -
              N.phi jk.1 jk.2 * t) <=
                N.phi jk.1 jk.2 * delta := by
          rw [← mul_sub, abs_mul,
            abs_of_nonneg (N.phi_nonneg jk.1 jk.2)]
          exact mul_le_mul_of_nonneg_left hst.le
            (N.phi_nonneg jk.1 jk.2)
        have htapprox' :
            abs (N.phi jk.1 jk.2 * t -
              N.totalCalendarScaledInput (K n) omega t jk.1 jk.2) < eta := by
          simpa [abs_sub_comm] using htapprox jk
        linarith [hsapprox jk, hmiddle, htapprox']
      _ = 2 * eta + N.phi jk.1 jk.2 * delta := by ring
  calc
    Finset.univ.sum (fun jk : Server × Buffer =>
        dist
          (N.totalCalendarScaledInput (K n) omega s jk.1 jk.2)
          (N.totalCalendarScaledInput (K n) omega t jk.1 jk.2)) <
        Finset.univ.sum (fun jk : Server × Buffer =>
          (2 * eta + N.phi jk.1 jk.2 * delta)) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun jk _ => hterm jk)
    _ = (Fintype.card (Server × Buffer) : Real) * (2 * eta) +
        (Finset.univ.sum
          (fun jk : Server × Buffer => N.phi jk.1 jk.2)) * delta := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_mul]
      simp
    _ < epsilon := by
      dsimp [eta, delta, C]
      have hcard : 0 <=
          (Fintype.card (Server × Buffer) : Real) := by positivity
      have hsum : 0 <=
          Finset.univ.sum
            (fun jk : Server × Buffer => N.phi jk.1 jk.2) :=
        Finset.sum_nonneg fun jk _ => N.phi_nonneg jk.1 jk.2
      field_simp
      nlinarith

private theorem calendarGridTimeLocal_mem_Icc
    {T : Real} (hT : 0 < T) (K : PNat)
    {l : Nat} (hl : l <= (K : Nat)) :
    calendarGridTimeLocal T K l ∈ Icc (0 : Real) T := by
  constructor
  · unfold calendarGridTimeLocal
    positivity
  · unfold calendarGridTimeLocal
    apply (div_le_iff₀ (show (0 : Real) < (K : Nat) by positivity)).2
    have hlreal : (l : Real) <= (K : Nat) := by exact_mod_cast hl
    nlinarith

private theorem calendarGridTimeLocal_close_of_hat_ne
    {T t : Real} (hT : 0 < T) (K : PNat)
    (l : Nat)
    (hhat :
      hatWeightLocal (((K : Nat) : Real) * t / T) l ≠ 0) :
    abs (calendarGridTimeLocal T K l - t) <
      T / (K : Nat) := by
  have hsupport := hatWeightLocal_ne_zero_imp hhat
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hscale : 0 < T / (K : Nat) := div_pos hT hK
  have heq :
      calendarGridTimeLocal T K l - t =
        (T / (K : Nat)) *
          ((l : Real) - ((K : Nat) : Real) * t / T) := by
    unfold calendarGridTimeLocal
    field_simp
  rw [heq, abs_mul, abs_of_pos hscale]
  rw [abs_sub_comm] at hsupport
  nlinarith

theorem calendarStatePolygonal_uniformly_close
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K)
    (x : forall n, JobState Buffer (K n : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    {T : Real} (hT : 0 < T) :
    forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall t, t ∈ Icc (0 : Real) T ->
          forall i,
            dist
              (calendarStatePolygonal N U (K n) (x n) omega T t i)
              (N.totalCalendarScaledQueueStateFrom
                U (K n) (x n) omega t i) < epsilon := by
  intro epsilon hepsilon
  obtain ⟨nInput, delta, hdelta, hinput⟩ :=
    totalInput_sum_dist_eventually_small N omega K hK hT
      (show 0 < epsilon / 2 by positivity)
  have hKval : Tendsto (fun n => (K n : Nat)) atTop atTop :=
    (show StrictMono (fun n => (K n : Nat)) from fun _ _ h =>
      hK h).tendsto_atTop
  have hKreal :
      Tendsto (fun n => ((K n : Nat) : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hKval
  have hmesh :
      Tendsto (fun n => T / ((K n : Nat) : Real))
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  obtain ⟨nMesh, hnMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh delta hdelta
  refine ⟨max nInput nMesh, fun n hn t ht i => ?_⟩
  have hnI : nInput <= n := (le_max_left _ _).trans hn
  have hnM : nMesh <= n := (le_max_right _ _).trans hn
  have hmeshSmall : T / ((K n : Nat) : Real) < delta := by
    have h := hnMesh n hnM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at h
    exact h
  let r : Real := ((K n : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg (mul_nonneg (by positivity) ht.1) hT.le
  have hrK : r <= (K n : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hsum := sum_hatWeightLocal_eq_one (K n) hr0 hrK
  let raw : Real :=
    N.totalCalendarScaledQueueStateFrom U (K n) (x n) omega t i
  have hterm (l : Nat) (hl : l ∈ Finset.range ((K n : Nat) + 1)) :
      abs (hatWeightLocal r l *
        (N.totalCalendarScaledQueueStateFrom U (K n) (x n) omega
          (calendarGridTimeLocal T (K n) l) i - raw)) <=
        hatWeightLocal r l * (epsilon / 2) := by
    by_cases hw : hatWeightLocal r l = 0
    · simp [hw]
    · rw [abs_mul, abs_of_nonneg (hatWeightLocal_nonneg r l)]
      apply mul_le_mul_of_nonneg_left _ (hatWeightLocal_nonneg r l)
      apply le_of_lt
      have hlK : l <= (K n : Nat) := by
        have := Finset.mem_range.mp hl
        omega
      have hgrid :=
        calendarGridTimeLocal_mem_Icc hT (K n) hlK
      have hclose :
          abs (calendarGridTimeLocal T (K n) l - t) < delta :=
        (calendarGridTimeLocal_close_of_hat_ne hT (K n) l hw).trans
          hmeshSmall
      have hstate :=
        totalCalendarScaledQueueStateFrom_dist_le_input
          N U (K n) (x n) omega
            (calendarGridTimeLocal T (K n) l) t i
      have hin :=
        hinput n hnI (calendarGridTimeLocal T (K n) l) hgrid
          t ht hclose
      change abs
        (N.totalCalendarScaledQueueStateFrom U (K n) (x n) omega
          (calendarGridTimeLocal T (K n) l) i - raw) < epsilon / 2
      rw [← Real.dist_eq]
      exact hstate.trans_lt hin
  rw [Real.dist_eq]
  unfold calendarStatePolygonal polygonalInterpolateLocal
  change abs
    ((Finset.sum (Finset.range ((K n : Nat) + 1)) fun l =>
      hatWeightLocal r l *
        N.totalCalendarScaledQueueStateFrom U (K n) (x n) omega
          (calendarGridTimeLocal T (K n) l) i) - raw) < epsilon
  rw [show
    (Finset.sum (Finset.range ((K n : Nat) + 1)) fun l =>
      hatWeightLocal r l *
        N.totalCalendarScaledQueueStateFrom U (K n) (x n) omega
          (calendarGridTimeLocal T (K n) l) i) - raw =
      Finset.sum (Finset.range ((K n : Nat) + 1)) (fun l =>
        hatWeightLocal r l *
          (N.totalCalendarScaledQueueStateFrom U (K n) (x n) omega
            (calendarGridTimeLocal T (K n) l) i - raw)) by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hsum, one_mul]]
  calc
    abs (Finset.sum (Finset.range ((K n : Nat) + 1)) (fun l =>
        hatWeightLocal r l *
          (N.totalCalendarScaledQueueStateFrom U (K n) (x n) omega
            (calendarGridTimeLocal T (K n) l) i - raw))) <=
        Finset.sum (Finset.range ((K n : Nat) + 1)) (fun l =>
          abs (hatWeightLocal r l *
            (N.totalCalendarScaledQueueStateFrom U (K n) (x n) omega
              (calendarGridTimeLocal T (K n) l) i - raw))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (Finset.range ((K n : Nat) + 1)) (fun l =>
          hatWeightLocal r l * (epsilon / 2)) :=
      Finset.sum_le_sum hterm
    _ = epsilon / 2 := by rw [← Finset.sum_mul, hsum, one_mul]
    _ < epsilon := by linarith

theorem exists_calendar_pair_convergent_subsequence
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K)
    (x : forall n, JobState Buffer (K n : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    {T : Real} (hT : 0 < T) :
    exists q : Nat -> Nat, StrictMono q /\
      exists X : StateDepMOR.Network.FluidStatePath Buffer,
        (N.calendarPoissonExecutionFrom
          (initialFamilyOfStrictSubsequence N K x)).PairConvergesOn
            T U (K ∘ q) omega
            (fun t j k => N.phi j k * t) X := by
  let D := Icc (0 : Real) T
  letI : CompactSpace D :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let f : Nat -> Real -> (Buffer -> Real) := fun n t i =>
    calendarStatePolygonal N U (K n) (x n) omega T t i
  have hf (n : Nat) : ContinuousOn (f n) (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro i
    exact (continuous_calendarStatePolygonal
      N U (K n) (x n) omega T i).continuousOn
  have hfamily :
      UniformEquicontinuous (fun n : Nat => fun t : D => f n t.1) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro epsilon hepsilon
    obtain ⟨nClose, hnClose⟩ :=
      calendarStatePolygonal_uniformly_close
        N U K hK x omega hT (epsilon / 8) (by positivity)
    obtain ⟨nInput, deltaInput, hdeltaInput, hnInput⟩ :=
      totalInput_sum_dist_eventually_small
        N omega K hK (epsilon := epsilon / 2) hT (by positivity)
    let nTail := max nClose nInput
    have hprefix :
        UniformEquicontinuous
          (fun n : Fin nTail => fun t : D => f n.1 t.1) := by
      rw [uniformEquicontinuous_finite]
      intro n
      exact CompactSpace.uniformContinuous_of_continuous
        ((hf n.1).domRestrict)
    obtain ⟨deltaPrefix, hdeltaPrefix, hprefixWorks⟩ :=
      (Metric.uniformEquicontinuous_iff.mp hprefix)
        epsilon hepsilon
    refine ⟨min deltaInput deltaPrefix,
      lt_min hdeltaInput hdeltaPrefix, ?_⟩
    intro s t hst n
    by_cases hn : nTail <= n
    · have hnC : nClose <= n := (le_max_left _ _).trans hn
      have hnI : nInput <= n := (le_max_right _ _).trans hn
      have hstInput : abs (s.1 - t.1) < deltaInput := by
        rw [← Real.dist_eq]
        exact hst.trans_le (min_le_left _ _)
      have hraw :
          Finset.univ.sum (fun jk : Server × Buffer =>
            dist
              (N.totalCalendarScaledInput (K n) omega
                s.1 jk.1 jk.2)
              (N.totalCalendarScaledInput (K n) omega
                t.1 jk.1 jk.2)) < epsilon / 2 :=
        hnInput n hnI s.1 s.2 t.1 t.2 hstInput
      apply (dist_pi_lt_iff (by positivity)).2
      intro i
      have hsClose :=
        hnClose n hnC s.1 s.2 i
      have htClose :=
        hnClose n hnC t.1 t.2 i
      have hstate :=
        totalCalendarScaledQueueStateFrom_dist_le_input
          N U (K n) (x n) omega s.1 t.1 i
      calc
        dist (f n s.1 i) (f n t.1 i) <=
            dist (f n s.1 i)
              (N.totalCalendarScaledQueueStateFrom
                U (K n) (x n) omega s.1 i) +
            dist
              (N.totalCalendarScaledQueueStateFrom
                U (K n) (x n) omega s.1 i)
              (N.totalCalendarScaledQueueStateFrom
                U (K n) (x n) omega t.1 i) +
            dist
              (N.totalCalendarScaledQueueStateFrom
                U (K n) (x n) omega t.1 i)
              (f n t.1 i) := by
          calc
            _ <= dist (f n s.1 i)
                  (N.totalCalendarScaledQueueStateFrom
                    U (K n) (x n) omega s.1 i) +
                dist
                  (N.totalCalendarScaledQueueStateFrom
                    U (K n) (x n) omega s.1 i)
                  (f n t.1 i) := dist_triangle _ _ _
            _ <= _ := by
              have htri := dist_triangle
                (N.totalCalendarScaledQueueStateFrom
                  U (K n) (x n) omega s.1 i)
                (N.totalCalendarScaledQueueStateFrom
                  U (K n) (x n) omega t.1 i)
                (f n t.1 i)
              linarith
        _ < epsilon / 8 + epsilon / 2 + epsilon / 8 := by
          have htClose' :
              dist
                (N.totalCalendarScaledQueueStateFrom
                  U (K n) (x n) omega t.1 i)
                (f n t.1 i) < epsilon / 8 := by
            simpa [dist_comm] using htClose
          gcongr
          exact hstate.trans_lt hraw
        _ < epsilon := by linarith
    · have hnlt : n < nTail := Nat.lt_of_not_ge hn
      exact hprefixWorks s t
        (hst.trans_le (min_le_right _ _)) ⟨n, hnlt⟩
  let F : Nat -> BoundedContinuousFunction D (Buffer -> Real) := fun n =>
    BoundedContinuousFunction.mkOfCompact
      (ContinuousMap.mk (fun t : D => f n t.1) ((hf n).domRestrict))
  let S : Set (BoundedContinuousFunction D (Buffer -> Real)) :=
    Set.range F
  have hcompact : IsCompact (closure S) := by
    apply BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall (0 : Buffer -> Real) 1)
      (isCompact_closedBall (0 : Buffer -> Real) 1) S
    · intro p t hp
      obtain ⟨n, rfl⟩ := hp
      apply (dist_pi_le_iff (by norm_num)).2
      intro i
      have hi :=
        calendarStatePolygonal_mem_Icc
          N U (K n) (x n) omega hT t.2 i
      change dist (calendarStatePolygonal
        N U (K n) (x n) omega T t.1 i) 0 <= 1
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hi.1]
      exact hi.2
    · let index : S -> Nat := fun p => Classical.choose p.2
      have hindex (p : S) : F (index p) = p.1 :=
        Classical.choose_spec p.2
      intro t
      rw [Metric.equicontinuousAt_iff]
      intro epsilon hepsilon
      have hnat := hfamily.equicontinuous t
      rw [Metric.equicontinuousAt_iff] at hnat
      obtain ⟨delta, hdelta, hworks⟩ := hnat epsilon hepsilon
      refine ⟨delta, hdelta, fun s hs p => ?_⟩
      rw [show p.1 t = F (index p) t by rw [hindex]]
      rw [show p.1 s = F (index p) s by rw [hindex]]
      exact hworks s hs (index p)
  obtain ⟨limitB, _, q, hq, hqconv⟩ :=
    hcompact.tendsto_subseq
      (fun n => subset_closure
        (show F n ∈ S from Set.mem_range_self n))
  let X : StateDepMOR.Network.FluidStatePath Buffer := fun t =>
    if ht : t ∈ Icc (0 : Real) T then
      limitB (show D from ⟨t, ht⟩)
    else 0
  have hpoly :
      forall epsilon, 0 < epsilon ->
        exists n0, forall n, n0 <= n ->
          forall t, t ∈ Icc (0 : Real) T ->
            forall i, dist (f (q n) t i) (X t i) < epsilon := by
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ :=
      Metric.tendsto_atTop.mp hqconv epsilon hepsilon
    refine ⟨n0, fun n hn t ht i => ?_⟩
    have hall := hn0 n hn
    have hcoord :=
      (dist_pi_le_iff dist_nonneg).mp
        (BoundedContinuousFunction.dist_coe_le_dist
          (f := F (q n)) (g := limitB)
          (show D from ⟨t, ht⟩)) i
    have hX : X t = limitB (show D from ⟨t, ht⟩) := dif_pos ht
    rw [hX]
    exact hcoord.trans_lt (by
      simpa [F, f, Function.comp_apply] using hall)
  refine ⟨q, hq, X, ?_⟩
  constructor
  · intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ :=
      totalCalendarScaledInput_uniformlyOnIcc
        N omega K hK hT epsilon hepsilon
    refine ⟨n0, fun n hn t ht jk => ?_⟩
    exact hn0 (q n) ((hq.id_le n).trans' hn) t ht jk
  · intro epsilon hepsilon
    obtain ⟨nRaw, hnRaw⟩ :=
      calendarStatePolygonal_uniformly_close
        N U K hK x omega hT (epsilon / 3) (by positivity)
    obtain ⟨nPoly, hnPoly⟩ :=
      hpoly (epsilon / 3) (by positivity)
    refine ⟨max nRaw nPoly, fun n hn t ht i => ?_⟩
    have hnR : nRaw <= q n :=
      (le_max_left _ _).trans hn |>.trans (hq.id_le n)
    have hnP : nPoly <= n := (le_max_right _ _).trans hn
    change abs
      ((N.calendarPoissonExecutionFrom
        (initialFamilyOfStrictSubsequence N K x)).state
          U (K (q n)) omega t i - X t i) < epsilon
    change abs
      (N.totalCalendarScaledQueueStateFrom U (K (q n))
        (initialFamilyOfStrictSubsequence N K x (K (q n)))
        omega t i - X t i) < epsilon
    rw [initialFamilyOfStrictSubsequence_apply N K hK x (q n)]
    rw [← Real.dist_eq]
    calc
      dist
          (N.totalCalendarScaledQueueStateFrom U (K (q n))
            (x (q n)) omega t i)
          (X t i) <=
          dist
            (N.totalCalendarScaledQueueStateFrom U (K (q n))
              (x (q n)) omega t i)
            (f (q n) t i) +
          dist (f (q n) t i) (X t i) :=
        dist_triangle _ _ _
      _ < epsilon / 3 + epsilon / 3 := by
        have hraw := hnRaw (q n) hnR t ht i
        have hraw' :
            dist
              (N.totalCalendarScaledQueueStateFrom U (K (q n))
                (x (q n)) omega t i)
              (f (q n) t i) < epsilon / 3 := by
          simpa [f, dist_comm] using hraw
        exact add_lt_add hraw' (hnPoly n hnP t ht i)
      _ < epsilon := by linarith

private theorem totalCalendarTokenPrefix_zero_local
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    N.totalCalendarTokenPrefix K omega 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro jk hjk
  have hpositive :
      0 < (N.totalCalendarTokenPrefix K omega 0).count jk :=
    List.count_pos_iff.2 hjk
  rcases jk with ⟨j, k⟩
  rw [totalCalendarTokenPrefix_count_local N] at hpositive
  simpa [StateDepMOR.Network.totalCalendarTokenCount] using hpositive

theorem exists_totalized_terminal_alpha_subsequence
    (hconnected : N.IsConnected)
    (hflex : N.HasLimitedFlexibility)
    (hcrp : N.HasCRP)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (T0 : Real)
    (hT0 : 0 < T0)
    (hrest :
      forall (T : Real) (x0 : Simplex Buffer)
        (A : StateDepMOR.MatrixPath Server Buffer)
        (s : N.FluidModelSolution (N.smwPolicy alpha halpha) T x0 A),
        s.IsFluidLimit ->
        forall t, t ∈ Icc T0 T -> s.X t = fun i => alpha i)
    {T : Real} (hT0T : T0 < T)
    (K : Nat -> PNat) (hK : StrictMono K)
    (z : forall n, JobState Buffer (K n : Nat))
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    exists r : Nat -> Nat, Tendsto r atTop atTop /\
      forall i,
        Tendsto
          (fun n =>
            N.totalCalendarScaledQueueStateFrom
              (N.smwPolicy alpha halpha) (K (r n)) (z (r n))
              omega T i)
          atTop (nhds (alpha i)) := by
  have hT : 0 < T := hT0.trans hT0T
  obtain ⟨p, hp, a, ha⟩ :=
    exists_convergent_normalized_jobState_subsequence
      (K := K) (x := z)
  let K1 : Nat -> PNat := K ∘ p
  let z1 : forall n, JobState Buffer (K1 n : Nat) := fun n => z (p n)
  have hK1 : StrictMono K1 := hK.comp hp
  obtain ⟨q, hq, X, hpair⟩ :=
    exists_calendar_pair_convergent_subsequence
      N (N.smwPolicy alpha halpha) K1 hK1 z1 omega hT
  let initial : forall L : PNat, JobState Buffer (L : Nat) :=
    initialFamilyOfStrictSubsequence N K1 z1
  let x0 : Simplex Buffer := {
    val := fun i => a i
    nonneg := fun i => a.property.1 i
    sum_eq_one := a.property.2
  }
  have hX0 : forall i, X 0 i = x0 i := by
    intro i
    have hstate :
        Tendsto
          (fun n =>
            (N.calendarPoissonExecutionFrom initial).state
              (N.smwPolicy alpha halpha) (K1 (q n)) omega 0 i)
          atTop (nhds (X 0 i)) := by
      rw [Metric.tendsto_atTop]
      intro epsilon hepsilon
      obtain ⟨n0, hn0⟩ := hpair.2 epsilon hepsilon
      refine ⟨n0, fun n hn => ?_⟩
      simpa [Real.dist_eq] using
        hn0 n hn 0 ⟨le_rfl, hT.le⟩ i
    have hinitial :
        Tendsto
          (fun n =>
            (N.calendarPoissonExecutionFrom initial).state
              (N.smwPolicy alpha halpha) (K1 (q n)) omega 0 i)
          atTop (nhds (x0 i)) := by
      have haCoord :
          Tendsto
            (fun n => normalizedJobState (K1 (q n)) (z1 (q n)) i)
            atTop (nhds (a i)) := by
        have hall :
            Tendsto
              (fun n => normalizedJobState (K1 (q n)) (z1 (q n)))
              atTop (nhds a) := by
          simpa [K1, z1, Function.comp_def] using
            ha.comp hq.tendsto_atTop
        exact ((continuous_apply i).comp continuous_subtype_val)
          |>.continuousAt.tendsto.comp hall
      convert haCoord using 1
      funext n
      change
        N.totalCalendarScaledQueueStateFrom
            (N.smwPolicy alpha halpha) (K1 (q n))
            (initial (K1 (q n))) omega 0 i =
          (z1 (q n) i : Real) / (K1 (q n) : Nat)
      rw [show initial (K1 (q n)) = z1 (q n) by
        exact initialFamilyOfStrictSubsequence_apply
          N K1 hK1 z1 (q n)]
      simp [StateDepMOR.Network.totalCalendarScaledQueueStateFrom,
        totalCalendarTokenPrefix_zero_local N,
        StateDepMOR.Network.runTokens]
    exact tendsto_nhds_unique hstate hinitial
  have hA :
      StateDepMOR.IsAbsolutelyContinuousMatrixPath T
        (fun t j k => N.phi j k * t) := by
    intro j k
    simpa [mul_comm] using
      (lipschitzWith_smul (N.phi j k)).lipschitzOnWith
        |>.absolutelyContinuousOnInterval (a := (0 : Real)) (b := T)
  obtain ⟨qAlloc, hqAlloc, s, hsX, _⟩ :=
    N.calendarPoissonExecutionFrom_stochasticFluidExtension initial
      T hT x0 (N.smwPolicy alpha halpha) (K1 ∘ q)
      (hK1.comp hq) omega (fun t j k => N.phi j k * t) X
      hX0 hA hpair
  have hsFluid : s.IsFluidLimit := by
    intro t _ j k
    rfl
  have hXT : X T = fun i => alpha i := by
    rw [← hsX]
    exact hrest T x0 (fun t j k => N.phi j k * t) s hsFluid T
      ⟨hT0T.le, le_rfl⟩
  refine ⟨p ∘ q, hp.tendsto_atTop.comp hq.tendsto_atTop, ?_⟩
  intro i
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨n0, hn0⟩ := hpair.2 epsilon hepsilon
  refine ⟨n0, fun n hn => ?_⟩
  have hterminal := hn0 n hn T ⟨hT.le, le_rfl⟩ i
  change abs
      (N.totalCalendarScaledQueueStateFrom
        (N.smwPolicy alpha halpha) (K1 (q n))
        (initial (K1 (q n))) omega T i - X T i) < epsilon at hterminal
  rw [show initial (K1 (q n)) = z1 (q n) by
        exact initialFamilyOfStrictSubsequence_apply
          N K1 hK1 z1 (q n),
    show X T i = alpha i from congrFun hXT i] at hterminal
  simpa [K1, z1, Function.comp_def, Real.dist_eq] using hterminal

theorem all_calendarEventTime_crossCoordinate_ne_ae :
    Filter.Eventually
      (fun omega =>
        forall (K : PNat) (j : Server) (k : Buffer)
          (j' : Server) (k' : Buffer),
          0 < N.phi j k ->
          0 < N.phi j' k' ->
          Ne (j, k) (j', k') ->
          forall (r q : Nat),
            Ne (N.calendarEventTime K omega ((j, k), r))
              (N.calendarEventTime K omega ((j', k'), q)))
      (MeasureTheory.ae N.calendarPoissonMeasure) := by
  rw [ae_all_iff]
  intro K
  filter_upwards
    [StateDepMOR.PoissonSamplePath.noSimultaneousPoissonJumps_ae
      N K (T := 1) zero_lt_one] with omega homega
  exact homega.2.2

private theorem rawCalendarEvents_positive_rate
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (t : Real)
    (event : StateDepMOR.Network.CalendarEvent
      (Buffer := Buffer) (Server := Server))
    (hevent : event ∈ N.rawCalendarEvents K omega t) :
    0 < N.phi event.1.1 event.1.2 := by
  by_contra hnot
  have hzero : N.phi event.1.1 event.1.2 = 0 :=
    le_antisymm (le_of_not_gt hnot)
      (N.phi_nonneg event.1.1 event.1.2)
  rcases event with ⟨⟨j, k⟩, r⟩
  simp [StateDepMOR.Network.rawCalendarEvents, hzero] at hevent

private theorem calendarEventSortRelations_agree
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (t : Real)
    (hpos : forall j k r, 0 < omega j k r)
    (hcross :
      forall (j : Server) (k : Buffer) (j' : Server) (k' : Buffer),
        0 < N.phi j k ->
        0 < N.phi j' k' ->
        Ne (j, k) (j', k') ->
        forall (r q : Nat),
          Ne (N.calendarEventTime K omega ((j, k), r))
            (N.calendarEventTime K omega ((j', k'), q))) :
    forall a, a ∈ N.rawCalendarEvents K omega t ->
      forall b, b ∈ N.rawCalendarEvents K omega t ->
        (toLex
            (N.calendarEventTime K omega a,
              StateDepMOR.Network.totalCalendarEventTieKey a) <=
            toLex
              (N.calendarEventTime K omega b,
                StateDepMOR.Network.totalCalendarEventTieKey b) <->
          N.calendarEventTime K omega a <=
            N.calendarEventTime K omega b) := by
  have hinjective :
      Set.InjOn (N.calendarEventTime K omega)
        {event |
          0 < N.phi event.1.1 event.1.2} :=
    StateDepMOR.PoissonSamplePath.calendarEventTime_injective_on_positive
      N K omega hpos hcross
  intro a ha b hb
  have hpa : 0 < N.phi a.1.1 a.1.2 :=
    rawCalendarEvents_positive_rate N K omega t a ha
  have hpb : 0 < N.phi b.1.1 b.1.2 :=
    rawCalendarEvents_positive_rate N K omega t b hb
  rw [Prod.Lex.toLex_le_toLex]
  constructor
  · rintro (hlt | ⟨heq, -⟩)
    · exact hlt.le
    · exact heq.le
  · intro hle
    rcases hle.eq_or_lt with heq | hlt
    · have hab : a = b := hinjective hpa hpb heq
      subst b
      exact Or.inr ⟨rfl, le_rfl⟩
    · exact Or.inl hlt

private theorem totalChronologicalCalendarEvents_eq_raw_of_regular
    (K : PNat)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (t : Real)
    (htotal :
      StateDepMOR.Network.totalCalendarPoissonSample omega = omega)
    (hpos : forall j k r, 0 < omega j k r)
    (hcross :
      forall (j : Server) (k : Buffer) (j' : Server) (k' : Buffer),
        0 < N.phi j k ->
        0 < N.phi j' k' ->
        Ne (j, k) (j', k') ->
        forall (r q : Nat),
          Ne (N.calendarEventTime K omega ((j, k), r))
            (N.calendarEventTime K omega ((j', k'), q))) :
    N.totalChronologicalCalendarEvents K omega t =
      N.chronologicalCalendarEvents K omega t := by
  classical
  unfold StateDepMOR.Network.totalChronologicalCalendarEvents
    StateDepMOR.Network.chronologicalCalendarEvents
    StateDepMOR.Network.totalRawCalendarEvents
    StateDepMOR.Network.totalCalendarEventOrderKey
    StateDepMOR.Network.totalCalendarEventTime
  rw [htotal]
  let events := N.rawCalendarEvents K omega t
  let totalOrder :=
    fun a b : StateDepMOR.Network.CalendarEvent
        (Buffer := Buffer) (Server := Server) =>
      toLex
          (N.calendarEventTime K omega a,
            StateDepMOR.Network.totalCalendarEventTieKey a) <=
        toLex
          (N.calendarEventTime K omega b,
            StateDepMOR.Network.totalCalendarEventTieKey b)
  let timeOrder :=
    fun a b : StateDepMOR.Network.CalendarEvent
        (Buffer := Buffer) (Server := Server) =>
      N.calendarEventTime K omega a <=
        N.calendarEventTime K omega b
  have hrelations :
      forall a, a ∈ events ->
        forall b, b ∈ events ->
          (totalOrder a b <-> timeOrder a b) := by
    simpa [events, totalOrder, timeOrder] using
      calendarEventSortRelations_agree N K omega t hpos hcross
  have hsort :=
    List.map_insertionSort
      (r := totalOrder) (s := timeOrder)
      (f := id) events hrelations
  simpa [events, totalOrder, timeOrder] using hsort

theorem totalCalendarTokenPrefix_eq_raw_ae :
    Filter.Eventually
      (fun omega =>
        forall (K : PNat) (t : Real),
          N.totalCalendarTokenPrefix K omega t =
            N.calendarTokenPrefix K omega t)
      (MeasureTheory.ae N.calendarPoissonMeasure) := by
  filter_upwards
    [N.totalCalendarPoissonSample_ae_eq_apply,
      N.all_calendarInterarrival_pos_ae_for_totalization,
      all_calendarEventTime_crossCoordinate_ne_ae N] with
      omega htotal hpos hcross
  intro K t
  unfold StateDepMOR.Network.totalCalendarTokenPrefix
    StateDepMOR.Network.calendarTokenPrefix
  rw [totalChronologicalCalendarEvents_eq_raw_of_regular
    N K omega t htotal hpos (hcross K)]

theorem totalCalendarScaledQueueStateFrom_eq_raw_ae :
    Filter.Eventually
      (fun omega =>
        forall (U : N.DeterministicPolicySequence) (K : PNat)
          (x : JobState Buffer (K : Nat)) (t : Real) (i : Buffer),
          N.totalCalendarScaledQueueStateFrom U K x omega t i =
            N.calendarScaledQueueStateFrom U K x omega t i)
      (MeasureTheory.ae N.calendarPoissonMeasure) := by
  filter_upwards [totalCalendarTokenPrefix_eq_raw_ae N] with omega homega
  intro U K x t i
  simp [StateDepMOR.Network.totalCalendarScaledQueueStateFrom,
    StateDepMOR.Network.calendarScaledQueueStateFrom, homega K t]

theorem calendarSMWDistance_tendsto_zero_of_coordinatewise
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (K : Nat -> PNat) (T : Real)
    (omega : StateDepMOR.Network.CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (x : forall n, JobState Buffer (K n : Nat))
    (hstate : forall i,
      Tendsto
        (fun n =>
          N.calendarScaledQueueStateFrom
            (N.smwPolicy alpha halpha) (K n) (x n) omega T i)
        atTop (nhds (alpha i))) :
    Tendsto
      (fun n =>
        calendarSMWDistance N alpha halpha (K n) T omega (x n))
      atTop (nhds 0) := by
  have hterm (i : Buffer) :
      Tendsto
        (fun n =>
          (N.calendarScaledQueueStateFrom
              (N.smwPolicy alpha halpha) (K n) (x n) omega T i -
            alpha i) ^ 2)
        atTop (nhds 0) := by
    have hconstant :
        Tendsto (fun _ : Nat => alpha i) atTop (nhds (alpha i)) :=
      tendsto_const_nhds
    convert ((hstate i).sub hconstant).pow 2 using 1 <;> simp
  have hsum :
      Tendsto
        (fun n =>
          Finset.univ.sum fun i =>
            (N.calendarScaledQueueStateFrom
                (N.smwPolicy alpha halpha) (K n) (x n) omega T i -
              alpha i) ^ 2)
        atTop (nhds 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  change Tendsto
    (fun n =>
      Real.sqrt
        (Finset.univ.sum fun i =>
          (N.calendarScaledQueueStateFrom
              (N.smwPolicy alpha halpha) (K n) (x n) omega T i -
            alpha i) ^ 2))
    atTop (nhds 0)
  simpa only [Real.sqrt_zero] using hsum.sqrt

theorem smwConvergesToWRemark_proved :
    StateDepMOR.PaperStatements.SMWConvergesToWRemarkStatement N := by
  intro hconnected hflex hcrp alpha halpha
  obtain ⟨T0, hT0, hrest⟩ :=
    smwFluidSolution_eq_alpha_after_uniform_time
      N hconnected hflex hcrp alpha halpha
  refine ⟨T0, hT0, fun T hT0T => ?_⟩
  filter_upwards [totalCalendarScaledQueueStateFrom_eq_raw_ae N] with
      omega hraw
  apply limsup_pnat_eq_zero_of_subsequential_compactness
      (f := fun K =>
        worstInitialSMWDistance N alpha halpha K T omega)
      (M := Real.sqrt (Fintype.card Buffer))
  · intro K
    exact worstInitialSMWDistance_nonneg
      N alpha halpha K T omega
  · intro K
    exact worstInitialSMWDistance_le_sqrt_card
      N alpha halpha K omega T
  · intro q hq
    obtain ⟨p, hp, hqp⟩ :=
      Filter.strictMono_subseq_of_tendsto_atTop hq
    have hmax (n : Nat) :
        exists x0 : JobState Buffer (q (p n) : Nat),
          worstInitialSMWDistance N alpha halpha (q (p n)) T omega =
            calendarSMWDistance
              N alpha halpha (q (p n)) T omega x0 :=
      exists_jobState_maximizing_calendarSMWDistance
        N alpha halpha (q (p n)) T omega
    choose z hz using hmax
    obtain ⟨r, hr, htotal⟩ :=
      exists_totalized_terminal_alpha_subsequence
        N hconnected hflex hcrp alpha halpha T0 hT0 hrest hT0T
          (q ∘ p) hqp z omega
    have hrawState (i : Buffer) :
        Tendsto
          (fun n =>
            N.calendarScaledQueueStateFrom
              (N.smwPolicy alpha halpha) (q (p (r n)))
              (z (r n)) omega T i)
          atTop (nhds (alpha i)) := by
      simpa only [Function.comp_apply, hraw] using htotal i
    have hdistance :
        Tendsto
          (fun n =>
            calendarSMWDistance N alpha halpha
              (q (p (r n))) T omega (z (r n)))
          atTop (nhds 0) :=
      calendarSMWDistance_tendsto_zero_of_coordinatewise
        N alpha halpha (fun n => q (p (r n))) T omega
          (fun n => z (r n)) hrawState
    refine ⟨p ∘ r, hp.tendsto_atTop.comp hr, ?_⟩
    convert hdistance using 1
    funext n
    simpa [Function.comp_apply] using hz (r n)

end StateDepMOR.PaperStatements.Network
