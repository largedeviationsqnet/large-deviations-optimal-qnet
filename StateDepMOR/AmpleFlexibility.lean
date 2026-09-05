import StateDepMOR.InitialPerformance
import StateDepMOR.FiniteQueueBalance
import StateDepMOR.MinInvariantPerformance
import StateDepMOR.PaperStatements

/-!
# Ample flexibility

This module proves Proposition 1 from the concrete event-epoch chain.  A
reservation assigns a distinct unit of queue mass to every server.  Once
such a reservation exists, every positive-rate token can move its server's
reserved job while preserving all reservations.

Connectivity is used only to reach the closed set of reservable states.
The proof then uses stationarity of the initial-law Cesaro limit, so it does
not assume irreducibility or select a favorable recurrent class.
-/

open scoped BigOperators ENNReal

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

namespace Network

variable (N : Network Buffer Server)

/-- Number of jobs reserved at `i` by the servers in `S`. -/
def reservationCount (_N : Network Buffer Server)
    (S : Finset Server) (r : Server -> Buffer)
    (i : Buffer) : Nat :=
  (S.filter fun j => r j = i).card

/-- A partial reservation uses distinct units of queue mass for the servers
in `S`, with each unit currently at a compatible buffer. -/
def IsPartialReservation {K : Nat} (x : JobState Buffer K)
    (S : Finset Server) (r : Server -> Buffer) : Prop :=
  (forall j, j ∈ S -> N.compatible (r j) j) /\
    (forall i, N.reservationCount S r i <= x i)

/-- A state contains one distinct reserved job for every server. -/
def CoversServers {K : Nat} (x : JobState Buffer K) : Prop :=
  exists r : Server -> Buffer,
    N.IsPartialReservation x Finset.univ r

private theorem reservationCount_sum
    (S : Finset Server) (r : Server -> Buffer) :
    Finset.univ.sum (N.reservationCount S r) = S.card := by
  classical
  have h := Finset.sum_fiberwise S r (fun _ => (1 : Nat))
  change
    Finset.univ.sum
        (fun i => (S.filter fun j => r j = i).card) =
      S.card
  simpa using h

private theorem filter_update_away
    (S : Finset Server) (r : Server -> Buffer)
    (j : Server) (dst i : Buffer) (hj : j ∉ S) :
    S.filter (fun q => Function.update r j dst q = i) =
      S.filter (fun q => r q = i) := by
  apply Finset.filter_congr
  intro q hq
  have hqj : Ne q j := by
    intro h
    subst q
    exact hj hq
  simp [Function.update, hqj]

private theorem reservationCount_insert_update
    (S : Finset Server) (r : Server -> Buffer)
    (j : Server) (dst i : Buffer) (hj : j ∉ S) :
    N.reservationCount (insert j S) (Function.update r j dst) i =
      N.reservationCount S r i + if dst = i then 1 else 0 := by
  unfold reservationCount
  rw [Finset.filter_insert]
  rw [filter_update_away S r j dst i hj]
  by_cases hdi : dst = i
  · simp [hdi, hj]
  · simp [hdi]

private theorem moveJob_apply {K : Nat}
    (x : JobState Buffer K) (src dst i : Buffer) (hsrc : 0 < x src) :
    x.moveJob src dst hsrc i =
      if i = dst then
        (if dst = src then x src - 1 else x dst) + 1
      else if i = src then x src - 1 else x i := by
  simp [JobState.moveJob, Function.update]

private theorem moveJob_self {K : Nat}
    (x : JobState Buffer K) (src : Buffer) (hsrc : 0 < x src) :
    x.moveJob src src hsrc = x := by
  apply JobState.ext
  funext i
  by_cases hi : i = src
  · subst i
    simp [JobState.moveJob, Function.update, Nat.sub_add_cancel hsrc]
  · simp [JobState.moveJob, Function.update, hi]

/-- Moving a spare job preserves a partial reservation, and the moved job
is still spare at its destination. -/
private theorem move_spare
    {K : Nat} (x : JobState Buffer K)
    (S : Finset Server) (r : Server -> Buffer)
    (src dst : Buffer)
    (hres : N.IsPartialReservation x S r)
    (hspare : N.reservationCount S r src < x src) :
    let hsrc : 0 < x src := Nat.zero_lt_of_lt hspare
    N.IsPartialReservation (x.moveJob src dst hsrc) S r /\
      N.reservationCount S r dst <
        x.moveJob src dst hsrc dst := by
  intro hsrc
  by_cases hsame : dst = src
  · subst dst
    rw [moveJob_self]
    exact ⟨hres, hspare⟩
  · constructor
    · constructor
      · exact hres.1
      · intro i
        by_cases hidst : i = dst
        · subst i
          rw [moveJob_apply]
          simp [hsame]
          exact Nat.le_add_right_of_le (hres.2 dst)
        · by_cases hisrc : i = src
          · subst i
            rw [moveJob_apply]
            simp [hidst]
            omega
          · rw [moveJob_apply]
            simp [hidst, hisrc]
            exact hres.2 i
    · rw [moveJob_apply]
      simp [hsame]
      have hcapacity := hres.2 dst
      omega

/-- One positive-rate legal queue move. -/
def QueueMove {K : Nat}
    (x y : JobState Buffer K) : Prop :=
  exists src dst,
    exists hsrc : 0 < x src,
      N.TokenStep src dst /\
        y = x.moveJob src dst hsrc

/-- A queue path consisting of finitely many positive-rate legal moves. -/
abbrev QueueReach {K : Nat} :=
  Relation.ReflTransGen (N.QueueMove (K := K))

/-- Lift a positive-rate buffer path by moving one spare job along it. -/
private theorem move_spare_along
    {K : Nat} (S : Finset Server) (r : Server -> Buffer)
    {src dst : Buffer}
    (hpath : Relation.ReflTransGen N.TokenStep src dst)
    (x : JobState Buffer K)
    (hres : N.IsPartialReservation x S r)
    (hspare : N.reservationCount S r src < x src) :
    exists y : JobState Buffer K,
      N.QueueReach x y /\
        N.IsPartialReservation y S r /\
        N.reservationCount S r dst < y dst := by
  induction hpath generalizing x with
  | refl =>
      exact ⟨x, Relation.ReflTransGen.refl, hres, hspare⟩
  | @tail b c hab hbc ih =>
      obtain ⟨y, hxy, hyres, hyspare⟩ := ih x hres hspare
      let hpos : 0 < y b := Nat.zero_lt_of_lt hyspare
      let z := y.moveJob b c hpos
      have hmoved := N.move_spare y S r b c hyres hyspare
      refine ⟨z, hxy.tail ?_, hmoved.1, hmoved.2⟩
      exact ⟨b, c, hpos, hbc, rfl⟩

private theorem exists_spare
    {K : Nat} (x : JobState Buffer K)
    (S : Finset Server) (r : Server -> Buffer)
    (hcard : S.card < K) :
    exists src, N.reservationCount S r src < x src := by
  have hsum :
      Finset.univ.sum (N.reservationCount S r) <
        Finset.univ.sum (fun i => x i) := by
    rw [N.reservationCount_sum S r, x.total_jobs]
    exact hcard
  obtain ⟨src, _, hsrc⟩ := Finset.exists_lt_of_sum_lt hsum
  exact ⟨src, hsrc⟩

private theorem extend_reservation
    {K : Nat} (x : JobState Buffer K)
    (S : Finset Server) (r : Server -> Buffer)
    (j : Server) (dst : Buffer)
    (hj : j ∉ S)
    (hres : N.IsPartialReservation x S r)
    (hcompat : N.compatible dst j)
    (hspare : N.reservationCount S r dst < x dst) :
    N.IsPartialReservation x (insert j S)
      (Function.update r j dst) := by
  constructor
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqS
    · simpa using hcompat
    · have hqj : Ne q j := by
        intro h
        subst q
        exact hj hqS
      simpa [Function.update, hqj] using hres.1 q hqS
  · intro i
    rw [N.reservationCount_insert_update S r j dst i hj]
    by_cases hdi : dst = i
    · subst i
      simp
      omega
    · simp [hdi]
      exact hres.2 i

/-- Every state can reach a state with a partial reservation for `S`, as
long as there are at least `|S|` jobs. -/
private theorem exists_reachable_partial_reservation
    (hconnected : N.IsConnected)
    {K : Nat} (x : JobState Buffer K)
    (S : Finset Server) (hcard : S.card <= K) :
    exists y : JobState Buffer K, exists r : Server -> Buffer,
      N.QueueReach x y /\
        N.IsPartialReservation y S r := by
  classical
  induction S using Finset.induction_on generalizing x with
  | empty =>
      let i0 : Buffer := Classical.choice (inferInstance : Nonempty Buffer)
      let r : Server -> Buffer := fun _ => i0
      refine ⟨x, r, Relation.ReflTransGen.refl, ?_⟩
      constructor
      · simp
      · intro i
        simp [reservationCount]
  | @insert j S hj ih =>
      have hcardS : S.card <= K := by
        rw [Finset.card_insert_of_notMem hj] at hcard
        omega
      obtain ⟨y, r, hxy, hyres⟩ := ih x hcardS
      have hstrict : S.card < K := by
        rw [Finset.card_insert_of_notMem hj] at hcard
        omega
      obtain ⟨src, hsrc⟩ := N.exists_spare y S r hstrict
      obtain ⟨dst, hdst⟩ := N.server_has_neighbor j
      obtain ⟨z, hyz, hzres, hzspare⟩ :=
        N.move_spare_along S r (hconnected src dst) y hyres hsrc
      let r' := Function.update r j dst
      refine ⟨z, r', hxy.trans hyz, ?_⟩
      exact N.extend_reservation z S r j dst hj hzres hdst hzspare

theorem exists_reachable_cover
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) :
    exists y : JobState Buffer K,
      N.QueueReach x y /\ N.CoversServers y := by
  obtain ⟨y, r, hxy, hyres⟩ :=
    N.exists_reachable_partial_reservation
      hconnected x Finset.univ (by simpa using hcard)
  exact ⟨y, hxy, r, hyres⟩

/-- A queue path with an explicit number of moves. -/
inductive QueueReachesIn {K : Nat} :
    Nat -> JobState Buffer K -> JobState Buffer K -> Prop
  | zero (x) : QueueReachesIn 0 x x
  | succ {n x y z} :
      N.QueueMove x y ->
      QueueReachesIn n y z ->
      QueueReachesIn (n + 1) x z

private theorem QueueReachesIn.append
    {K : Nat} {n : Nat} {x y z : JobState Buffer K}
    (hxy : N.QueueReachesIn n x y)
    (hyz : N.QueueMove y z) :
    N.QueueReachesIn (n + 1) x z := by
  induction hxy with
  | zero =>
      exact QueueReachesIn.succ hyz (QueueReachesIn.zero z)
  | @succ m a b c hab hbc ih =>
      simpa [Nat.add_assoc] using
        QueueReachesIn.succ hab (ih hyz)

private theorem queueReach_has_length
    {K : Nat} {x y : JobState Buffer K}
    (hxy : N.QueueReach x y) :
    exists n, N.QueueReachesIn n x y := by
  induction hxy with
  | refl =>
      exact ⟨0, QueueReachesIn.zero x⟩
  | tail hab hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, QueueReachesIn.append N hn hbc⟩

/-- There is a finite-length queue path from every state to the reserved
set. -/
private theorem exists_steps_to_cover
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) :
    exists n, exists y : JobState Buffer K,
      N.QueueReachesIn n x y /\ N.CoversServers y := by
  obtain ⟨y, hxy, hycover⟩ :=
    N.exists_reachable_cover hconnected hcard x
  obtain ⟨n, hn⟩ := N.queueReach_has_length hxy
  exact ⟨n, y, hn, hycover⟩

/-- Shortest number of positive-rate queue moves needed to reach the
reserved-state set. -/
noncomputable def coverDistance
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) : Nat :=
  by
    classical
    exact Nat.find (N.exists_steps_to_cover hconnected hcard x)

private theorem coverDistance_spec
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) :
    exists y : JobState Buffer K,
      N.QueueReachesIn
          (N.coverDistance hconnected hcard x) x y /\
        N.CoversServers y := by
  classical
  exact Nat.find_spec (N.exists_steps_to_cover hconnected hcard x)

theorem coverDistance_eq_zero_iff
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) :
    N.coverDistance hconnected hcard x = 0 <->
      N.CoversServers x := by
  classical
  constructor
  · intro hzero
    obtain ⟨y, hxy, hycover⟩ :=
      N.coverDistance_spec hconnected hcard x
    rw [hzero] at hxy
    cases hxy
    exact hycover
  · intro hx
    unfold coverDistance
    apply Nat.eq_zero_of_le_zero
    apply Nat.find_min'
    exact ⟨x, QueueReachesIn.zero x, hx⟩

private theorem QueueReachesIn.exists_head
    {K : Nat} {n : Nat} {x z : JobState Buffer K}
    (h : N.QueueReachesIn n x z) (hn : 0 < n) :
    exists m, exists y : JobState Buffer K,
      n = m + 1 /\
        N.QueueMove x y /\
        N.QueueReachesIn m y z := by
  cases h with
  | zero =>
      exact (Nat.not_lt_zero 0 hn).elim
  | @succ m _ y _ hxy hyz =>
      exact ⟨m, y, rfl, hxy, hyz⟩

/-- Outside the reserved-state set, a shortest path supplies one
positive-rate queue move that strictly decreases `coverDistance`. -/
private theorem exists_distance_decreasing_move
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : Not (N.CoversServers x)) :
    exists y : JobState Buffer K,
      N.QueueMove x y /\
        N.coverDistance hconnected hcard y <
          N.coverDistance hconnected hcard x := by
  classical
  let d := N.coverDistance hconnected hcard x
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hx ((N.coverDistance_eq_zero_iff
      hconnected hcard x).mp hzero)
  obtain ⟨z, hxz, hzcover⟩ :=
    N.coverDistance_spec hconnected hcard x
  change N.QueueReachesIn d x z at hxz
  obtain ⟨n, y, hd, hxy, hyz⟩ :=
    QueueReachesIn.exists_head N hxz hdpos
  refine ⟨y, hxy, ?_⟩
  have hle :
      N.coverDistance hconnected hcard y <= n := by
    unfold coverDistance
    apply Nat.find_min'
    exact ⟨z, hyz, hzcover⟩
  change N.coverDistance hconnected hcard y < d
  omega

/-- The token, source, and destination selected by a shortest-path step. -/
structure ProgressDatum
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) where
  src : Buffer
  dst : Buffer
  origin : Server
  source_pos : 0 < x src
  source_compatible : N.compatible src origin
  token_pos : 0 < N.phi origin dst
  distance_lt :
    N.coverDistance hconnected hcard
        (x.moveJob src dst source_pos) <
      N.coverDistance hconnected hcard x

private theorem exists_progressDatum
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : Not (N.CoversServers x)) :
    Nonempty (N.ProgressDatum hconnected hcard x) := by
  obtain ⟨y, hmove, hlt⟩ :=
    N.exists_distance_decreasing_move hconnected hcard x hx
  obtain ⟨src, dst, hsrc, ⟨j, hcompat, hphi⟩, rfl⟩ := hmove
  exact ⟨{
    src := src
    dst := dst
    origin := j
    source_pos := hsrc
    source_compatible := hcompat
    token_pos := hphi
    distance_lt := hlt
  }⟩

noncomputable def progressDatum
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : Not (N.CoversServers x)) :
    N.ProgressDatum hconnected hcard x :=
  Classical.choice
    (N.exists_progressDatum hconnected hcard x hx)

noncomputable def coverReservation
    {K : Nat} (x : JobState Buffer K)
    (hx : N.CoversServers x) : Server -> Buffer :=
  Classical.choose hx

private theorem coverReservation_spec
    {K : Nat} (x : JobState Buffer K)
    (hx : N.CoversServers x) :
    N.IsPartialReservation x Finset.univ
      (N.coverReservation x hx) :=
  Classical.choose_spec hx

private theorem coverReservation_positive
    {K : Nat} (x : JobState Buffer K)
    (hx : N.CoversServers x) (j : Server) :
    0 < x (N.coverReservation x hx j) := by
  let r := N.coverReservation x hx
  have hj :
      j ∈ Finset.univ.filter (fun q => r q = r j) := by
    simp
  have hcount :
      0 < N.reservationCount Finset.univ r (r j) := by
    exact Finset.card_pos.mpr ⟨j, hj⟩
  have hcapacity :=
    (N.coverReservation_spec x hx).2 (r j)
  exact hcount.trans_le hcapacity

private theorem coverReservation_compatible
    {K : Nat} (x : JobState Buffer K)
    (hx : N.CoversServers x) (j : Server) :
    N.compatible (N.coverReservation x hx j) j :=
  (N.coverReservation_spec x hx).1 j (Finset.mem_univ j)

/-- At a covered state, serve the job reserved for the token's origin when
the destination is compatible.  Outside the covered set, execute only the
one positive-rate move selected by a shortest path and idle on every other
token. -/
noncomputable def ampleStationaryPolicy
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K) :
    N.DeterministicStationaryPolicy K := by
  classical
  refine {
    action := fun x j k =>
      if hx : N.CoversServers x then
        if N.compatible k j then
          some (N.coverReservation x hx j)
        else
          none
      else
        let d := N.progressDatum hconnected hcard x hx
        if j = d.origin /\ k = d.dst then some d.src else none
    legal := ?_
  }
  intro x j k
  dsimp only
  split
  next hx =>
    split
    next hk =>
      exact ⟨N.coverReservation_compatible x hx j,
        N.coverReservation_positive x hx j⟩
    next =>
      trivial
  next hx =>
    let d := N.progressDatum hconnected hcard x hx
    change N.IsLegalAction x j
      (if j = d.origin /\ k = d.dst then some d.src else none)
    split
    next hmatch =>
      rw [hmatch.1]
      exact ⟨d.source_compatible, d.source_pos⟩
    next =>
      trivial

private theorem ampleStationaryPolicy_cover_compatible
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : N.CoversServers x)
    (j : Server) (k : Buffer) (hk : N.compatible k j) :
    N.ampleStationaryPolicy hconnected hcard x j k =
      some (N.coverReservation x hx j) := by
  classical
  simp [ampleStationaryPolicy, hx, hk]

private theorem ampleStationaryPolicy_cover_incompatible
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : N.CoversServers x)
    (j : Server) (k : Buffer) (hk : Not (N.compatible k j)) :
    N.ampleStationaryPolicy hconnected hcard x j k = none := by
  classical
  simp [ampleStationaryPolicy, hx, hk]

private theorem queueStep_eq_move_of_action_eq
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (j : Server) (k src : Buffer)
    (hsrc : 0 < x src)
    (haction : U x j k = some src) :
    N.queueStep U x (j, k) = x.moveJob src k hsrc := by
  unfold queueStep
  split
  next hnone =>
    rw [haction] at hnone
    contradiction
  next i hsome =>
    have hi : i = src := Option.some.inj (hsome.symm.trans haction)
    subst i
    rfl

private theorem queueStep_eq_self_of_action_eq_none
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (j : Server) (k : Buffer)
    (haction : U x j k = none) :
    N.queueStep U x (j, k) = x := by
  unfold queueStep
  split
  next =>
    rfl
  next i hsome =>
    rw [haction] at hsome
    contradiction

private theorem cover_move_preserves
    {K : Nat} (x : JobState Buffer K)
    (hx : N.CoversServers x)
    (j : Server) (dst : Buffer)
    (hcompat : N.compatible dst j) :
    let src := N.coverReservation x hx j
    let hsrc : 0 < x src := N.coverReservation_positive x hx j
    N.CoversServers (x.moveJob src dst hsrc) := by
  intro src hsrc
  let r := N.coverReservation x hx
  let S := Finset.univ.erase j
  have hfull := N.coverReservation_spec x hx
  have hpartial : N.IsPartialReservation x S r := by
    constructor
    · intro q hq
      exact hfull.1 q (Finset.mem_univ q)
    · intro i
      apply (Finset.card_le_card ?_).trans (hfull.2 i)
      exact Finset.filter_subset_filter (fun q => r q = i)
        (Finset.erase_subset j Finset.univ)
  have hcount :
      N.reservationCount Finset.univ r src =
        N.reservationCount S r src + 1 := by
    have h :=
      N.reservationCount_insert_update S r j src src
        (by simp [S])
    simpa [S, src, r, Finset.insert_erase,
      Function.update_eq_self] using h
  have hspare : N.reservationCount S r src < x src := by
    have hcapacity := hfull.2 src
    rw [hcount] at hcapacity
    omega
  have hmoved := N.move_spare x S r src dst hpartial hspare
  let r' := Function.update r j dst
  refine ⟨r', ?_⟩
  have hextend :=
    N.extend_reservation
      (x.moveJob src dst hsrc) S r j dst
      (by simp [S])
      hmoved.1 hcompat hmoved.2
  simpa [S, r', Finset.insert_erase] using hextend

theorem ampleStationaryPolicy_preserves_cover
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : N.CoversServers x)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    N.CoversServers
      (N.queueStep (N.ampleStationaryPolicy hconnected hcard) x jk) := by
  classical
  by_cases hk : N.compatible jk.2 jk.1
  · have haction :=
      N.ampleStationaryPolicy_cover_compatible
        hconnected hcard x hx jk.1 jk.2 hk
    have hstep :=
      N.queueStep_eq_move_of_action_eq
        (N.ampleStationaryPolicy hconnected hcard) x jk.1 jk.2
        (N.coverReservation x hx jk.1)
        (N.coverReservation_positive x hx jk.1) haction
    rw [show jk = (jk.1, jk.2) by exact Prod.eta jk, hstep]
    exact N.cover_move_preserves x hx jk.1 jk.2 hk
  · have haction :=
      N.ampleStationaryPolicy_cover_incompatible
        hconnected hcard x hx jk.1 jk.2 hk
    have hstep :=
      N.queueStep_eq_self_of_action_eq_none
        (N.ampleStationaryPolicy hconnected hcard) x jk.1 jk.2
        haction
    rw [show jk = (jk.1, jk.2) by exact Prod.eta jk, hstep]
    exact hx

theorem ampleStationaryPolicy_oneStepWaste_eq_zero_of_cover
    (hconnected : N.IsConnected)
    (hample : forall j k, 0 < N.phi j k -> N.compatible k j)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : N.CoversServers x) :
    N.oneStepWaste (N.ampleStationaryPolicy hconnected hcard) x = 0 := by
  classical
  unfold oneStepWaste
  apply Finset.sum_eq_zero
  intro jk hjk
  by_cases hk : N.compatible jk.2 jk.1
  · have haction :=
      N.ampleStationaryPolicy_cover_compatible
        hconnected hcard x hx jk.1 jk.2 hk
    simp [wasteIndicator, haction]
  · have hphi : N.phi jk.1 jk.2 = 0 := by
      apply le_antisymm
      · exact not_lt.mp (fun hp => hk (hample jk.1 jk.2 hp))
      · exact N.phi_nonneg jk.1 jk.2
    rw [N.tokenLaw_toReal]
    simp [hphi]

private theorem ampleStationaryPolicy_progress_action
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : Not (N.CoversServers x)) :
    let d := N.progressDatum hconnected hcard x hx
    N.ampleStationaryPolicy hconnected hcard x d.origin d.dst =
      some d.src := by
  classical
  intro d
  simp [ampleStationaryPolicy, hx, d]

private theorem ampleStationaryPolicy_other_action
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : Not (N.CoversServers x))
    (j : Server) (k : Buffer)
    (hother :
      let d := N.progressDatum hconnected hcard x hx
      Not (j = d.origin /\ k = d.dst)) :
    N.ampleStationaryPolicy hconnected hcard x j k = none := by
  classical
  simp [ampleStationaryPolicy, hx, hother]

private theorem ampleStationaryPolicy_progress_step
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : Not (N.CoversServers x)) :
    let d := N.progressDatum hconnected hcard x hx
    N.queueStep (N.ampleStationaryPolicy hconnected hcard) x
        (d.origin, d.dst) =
      x.moveJob d.src d.dst d.source_pos := by
  intro d
  apply N.queueStep_eq_move_of_action_eq
  exact N.ampleStationaryPolicy_progress_action
    hconnected hcard x hx

private theorem ampleStationaryPolicy_other_step
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : Not (N.CoversServers x))
    (j : Server) (k : Buffer)
    (hother :
      let d := N.progressDatum hconnected hcard x hx
      Not (j = d.origin /\ k = d.dst)) :
    N.queueStep (N.ampleStationaryPolicy hconnected hcard) x (j, k) =
      x := by
  apply N.queueStep_eq_self_of_action_eq_none
  exact N.ampleStationaryPolicy_other_action
    hconnected hcard x hx j k hother

theorem coverDistance_queueStep_le
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    N.coverDistance hconnected hcard
        (N.queueStep (N.ampleStationaryPolicy hconnected hcard) x jk) <=
      N.coverDistance hconnected hcard x := by
  classical
  by_cases hx : N.CoversServers x
  · have hnext :=
      N.ampleStationaryPolicy_preserves_cover
        hconnected hcard x hx jk
    rw [(N.coverDistance_eq_zero_iff hconnected hcard x).2 hx]
    exact
      ((N.coverDistance_eq_zero_iff hconnected hcard _).2 hnext).le
  · let d := N.progressDatum hconnected hcard x hx
    by_cases hmatch : jk.1 = d.origin /\ jk.2 = d.dst
    · have hjk : jk = (d.origin, d.dst) := by
        exact Prod.ext hmatch.1 hmatch.2
      rw [hjk, N.ampleStationaryPolicy_progress_step
        hconnected hcard x hx]
      exact d.distance_lt.le
    · have hstep :=
        N.ampleStationaryPolicy_other_step
          hconnected hcard x hx jk.1 jk.2 hmatch
      rw [show jk = (jk.1, jk.2) by exact Prod.eta jk, hstep]

/-- Expected one-step decrease of the shortest distance to the covered
state set. -/
noncomputable def expectedCoverDistanceDrop
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) : Real :=
  Finset.univ.sum fun jk =>
    (N.tokenLaw jk).toReal *
      ((N.coverDistance hconnected hcard x : Real) -
        (N.coverDistance hconnected hcard
          (N.queueStep (N.ampleStationaryPolicy hconnected hcard) x jk) :
            Real))

theorem expectedCoverDistanceDrop_nonnegative
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) :
    0 <= N.expectedCoverDistanceDrop hconnected hcard x := by
  unfold expectedCoverDistanceDrop
  apply Finset.sum_nonneg
  intro jk hjk
  apply mul_nonneg ENNReal.toReal_nonneg
  apply sub_nonneg.mpr
  exact_mod_cast N.coverDistance_queueStep_le hconnected hcard x jk

theorem expectedCoverDistanceDrop_pos_of_not_cover
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) (hx : Not (N.CoversServers x)) :
    0 < N.expectedCoverDistanceDrop hconnected hcard x := by
  classical
  let d := N.progressDatum hconnected hcard x hx
  let chosen : TokenType (Buffer := Buffer) (Server := Server) :=
    (d.origin, d.dst)
  have hterm_nonneg :
      forall jk,
        jk ∈ (Finset.univ :
          Finset (TokenType (Buffer := Buffer) (Server := Server))) ->
        0 <=
          (N.tokenLaw jk).toReal *
            ((N.coverDistance hconnected hcard x : Real) -
              (N.coverDistance hconnected hcard
                (N.queueStep
                  (N.ampleStationaryPolicy hconnected hcard) x jk) :
                    Real)) := by
    intro jk hjk
    apply mul_nonneg ENNReal.toReal_nonneg
    apply sub_nonneg.mpr
    exact_mod_cast N.coverDistance_queueStep_le
      hconnected hcard x jk
  have hchosen_pos :
      0 <
        (N.tokenLaw chosen).toReal *
          ((N.coverDistance hconnected hcard x : Real) -
            (N.coverDistance hconnected hcard
              (N.queueStep
                (N.ampleStationaryPolicy hconnected hcard) x chosen) :
                  Real)) := by
    have hprob : 0 < (N.tokenLaw chosen).toReal := by
      rw [N.tokenLaw_toReal]
      exact d.token_pos
    have hstep :
        N.queueStep (N.ampleStationaryPolicy hconnected hcard) x chosen =
          x.moveJob d.src d.dst d.source_pos := by
      exact N.ampleStationaryPolicy_progress_step
        hconnected hcard x hx
    rw [hstep]
    apply mul_pos hprob
    exact sub_pos.mpr (by exact_mod_cast d.distance_lt)
  have hle :=
    Finset.single_le_sum hterm_nonneg
      (Finset.mem_univ chosen)
  exact hchosen_pos.trans_le hle

private theorem expectedCoverDistanceDrop_eq
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (x : JobState Buffer K) :
    N.expectedCoverDistanceDrop hconnected hcard x =
      (N.coverDistance hconnected hcard x : Real) -
        Finset.univ.sum (fun jk =>
          (N.tokenLaw jk).toReal *
            (N.coverDistance hconnected hcard
              (N.queueStep
                (N.ampleStationaryPolicy hconnected hcard) x jk) :
                  Real)) := by
  unfold expectedCoverDistanceDrop
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, PMF.sum_toReal, one_mul]

theorem stationary_expectedCoverDistanceDrop_eq_zero
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (pi : PMF (JobState Buffer K))
    (hpi :
      N.IsInvariantPMF
        (N.ampleStationaryPolicy hconnected hcard) pi) :
    Finset.univ.sum (fun x =>
      (pi x).toReal *
        N.expectedCoverDistanceDrop hconnected hcard x) = 0 := by
  have hstationary :=
    N.stationary_expectation
      (N.ampleStationaryPolicy hconnected hcard) pi hpi
      (fun x => (N.coverDistance hconnected hcard x : Real))
  simp_rw [N.expectedCoverDistanceDrop_eq, mul_sub]
  rw [Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr hstationary.symm

theorem invariantPMF_toReal_eq_zero_of_not_cover
    (hconnected : N.IsConnected)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (pi : PMF (JobState Buffer K))
    (hpi :
      N.IsInvariantPMF
        (N.ampleStationaryPolicy hconnected hcard) pi)
    (x : JobState Buffer K) (hx : Not (N.CoversServers x)) :
    (pi x).toReal = 0 := by
  have hzero :=
    N.stationary_expectedCoverDistanceDrop_eq_zero
      hconnected hcard pi hpi
  have hnonnegative :
      forall y,
        y ∈ (Finset.univ : Finset (JobState Buffer K)) ->
        0 <=
          (pi y).toReal *
            N.expectedCoverDistanceDrop hconnected hcard y := by
    intro y hy
    exact mul_nonneg ENNReal.toReal_nonneg
      (N.expectedCoverDistanceDrop_nonnegative hconnected hcard y)
  have hterm :
      (pi x).toReal *
          N.expectedCoverDistanceDrop hconnected hcard x =
        0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonnegative).mp hzero
      x (Finset.mem_univ x)
  exact (mul_eq_zero.mp hterm).resolve_right
    (ne_of_gt
      (N.expectedCoverDistanceDrop_pos_of_not_cover
        hconnected hcard x hx))

theorem ampleStationaryPolicy_stationaryWaste_eq_zero
    (hconnected : N.IsConnected)
    (hample : forall j k, 0 < N.phi j k -> N.compatible k j)
    {K : Nat} (hcard : Fintype.card Server <= K)
    (pi : PMF (JobState Buffer K))
    (hpi :
      N.IsInvariantPMF
        (N.ampleStationaryPolicy hconnected hcard) pi) :
    N.stationaryOneStepWaste
      (N.ampleStationaryPolicy hconnected hcard) pi = 0 := by
  unfold stationaryOneStepWaste
  apply Finset.sum_eq_zero
  intro x hxmem
  by_cases hx : N.CoversServers x
  · rw [N.ampleStationaryPolicy_oneStepWaste_eq_zero_of_cover
      hconnected hample hcard x hx]
    simp
  · rw [N.invariantPMF_toReal_eq_zero_of_not_cover
      hconnected hcard pi hpi x hx]
    simp

/-- A policy that always discards the token. -/
def idleStationaryPolicy (K : Nat) :
    N.DeterministicStationaryPolicy K where
  action _ _ _ := none
  legal _ _ _ := by
    trivial

/-- One policy sequence that uses the ample-flexibility controller whenever
there are enough jobs to reserve one per server. -/
noncomputable def amplePolicySequence
    (hconnected : N.IsConnected) :
    N.DeterministicPolicySequence := by
  classical
  intro K
  exact if hcard : Fintype.card Server <= (K : Nat) then
    N.ampleStationaryPolicy hconnected hcard
  else
    N.idleStationaryPolicy (K : Nat)

theorem amplePolicySequence_apply
    (hconnected : N.IsConnected)
    (K : PNat) (hcard : Fintype.card Server <= (K : Nat)) :
    N.amplePolicySequence hconnected K =
      N.ampleStationaryPolicy hconnected hcard := by
  classical
  simp [amplePolicySequence, hcard]

theorem amplePolicy_initialLongRunLoss_eq_zero
    (hconnected : N.IsConnected)
    (hample : forall j k, 0 < N.phi j k -> N.compatible k j)
    (initial : N.InitialLawFamily)
    (K : PNat) (hcard : Fintype.card Server <= (K : Nat)) :
    N.initialLongRunLoss (N.amplePolicySequence hconnected) initial K =
      0 := by
  rw [N.initialLongRunLoss_eq_stationaryOneStepWaste]
  have hinvariant :=
    N.initialCesaroLimitLaw_isInvariant
      (N.amplePolicySequence hconnected) initial K
  rw [N.amplePolicySequence_apply hconnected K hcard] at hinvariant
  rw [N.amplePolicySequence_apply hconnected K hcard]
  exact N.ampleStationaryPolicy_stationaryWaste_eq_zero
    hconnected hample hcard
    (N.initialCesaroLimitLaw
      (N.amplePolicySequence hconnected) initial K)
    hinvariant

/-- The ample-flexibility policy has zero loss under the repaired
minimum-recurrent-class convention. -/
theorem amplePolicy_minimumInvariantLoss_eq_zero
    (hconnected : N.IsConnected)
    (hample : forall j k, 0 < N.phi j k -> N.compatible k j)
    (K : PNat) (hcard : Fintype.card Server <= (K : Nat)) :
    N.minimumInvariantLossFamily (N.amplePolicySequence hconnected) K = 0 := by
  rw [minimumInvariantLossFamily,
    N.amplePolicySequence_apply hconnected K hcard]
  rw [N.minimumInvariantLoss_eq_stationaryOneStepWaste]
  exact N.ampleStationaryPolicy_stationaryWaste_eq_zero
    hconnected hample hcard
    (N.minimumInvariantPMF (N.ampleStationaryPolicy hconnected hcard))
    (N.minimumInvariantPMF_isInvariant
      (N.ampleStationaryPolicy hconnected hcard))

end Network

end StateDepMOR

namespace StateDepMOR.PaperStatements

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-- Exact concrete-chain proof of repaired Proposition 1 under the
minimum-recurrent-class convention. -/
theorem ampleFlexibilityNecessaryStatement_proved
    (N : StateDepMOR.Network Buffer Server) :
    AmpleFlexibilityNecessaryStatement N := by
  intro hconnected hample K hcard
  let U := N.amplePolicySequence hconnected
  refine ⟨U, ?_⟩
  exact N.amplePolicy_minimumInvariantLoss_eq_zero
    hconnected hample K hcard

end StateDepMOR.PaperStatements
