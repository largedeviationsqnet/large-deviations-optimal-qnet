import StateDepMOR.FiniteQueueBalance

/-!
# Finite token trajectories

This module proves the deterministic pathwise comparison used in the
critical Hall argument. A cut can lose queue mass faster than its primitive
token walk only if some service opportunity is wasted.
-/

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

variable (N : Network Buffer Server)

/-- Run a finite marked-token sequence through a stationary policy. -/
def runTokens {K : Nat} (U : N.DeterministicStationaryPolicy K) :
    JobState Buffer K ->
      List (TokenType (Buffer := Buffer) (Server := Server)) ->
      JobState Buffer K
  | x, [] => x
  | x, jk :: rest => runTokens U (N.queueStep U x jk) rest

/-- The primitive cut-walk increment: destination mass minus origin mass. -/
def primitiveCutIncrement (jset : Finset Server)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) : Real :=
  N.tokenDestinationIn (N.neighborhood jset) jk -
    N.tokenOriginIn jset jk

/-- Sum of primitive cut-walk increments along a finite token list. -/
def primitiveCutSum (jset : Finset Server) :
    List (TokenType (Buffer := Buffer) (Server := Server)) -> Real
  | [] => 0
  | jk :: rest =>
      N.primitiveCutIncrement jset jk + primitiveCutSum jset rest

/-- Number of wasted tokens along a finite execution, represented in
`Real` to combine directly with the cut balance. -/
def trajectoryWaste {K : Nat} (U : N.DeterministicStationaryPolicy K) :
    JobState Buffer K ->
      List (TokenType (Buffer := Buffer) (Server := Server)) -> Real
  | _, [] => 0
  | x, jk :: rest =>
      N.wasteIndicator U x jk +
        trajectoryWaste U (N.queueStep U x jk) rest

theorem trajectoryWaste_nonneg {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    0 <= N.trajectoryWaste U x tokens := by
  induction tokens generalizing x with
  | nil =>
      simp [trajectoryWaste]
  | cons jk rest ih =>
      simp only [trajectoryWaste]
      exact add_nonneg (N.wasteIndicator_nonneg U x jk)
        (ih (N.queueStep U x jk))

theorem cutChange_le_primitive_add_waste {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (jset : Finset Server)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    N.cutChange U x (N.neighborhood jset) jk <=
      N.primitiveCutIncrement jset jk + N.wasteIndicator U x jk := by
  have h :=
    N.waste_ge_origin_sub_destination_add_cutChange U x jset jk
  unfold primitiveCutIncrement
  linarith

/-- Pathwise cut comparison over an arbitrary finite token sequence. -/
theorem runTokens_jobsIn_sub_le
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (jset : Finset Server)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    JobState.jobsIn (N.runTokens U x tokens) (N.neighborhood jset) -
        JobState.jobsIn x (N.neighborhood jset) <=
      N.primitiveCutSum jset tokens + N.trajectoryWaste U x tokens := by
  induction tokens generalizing x with
  | nil =>
      simp [runTokens, primitiveCutSum, trajectoryWaste]
  | cons jk rest ih =>
      let xnext := N.queueStep U x jk
      have htail := ih xnext
      have hone :=
        N.cutChange_le_primitive_add_waste U x jset jk
      have hbalance :=
        N.jobsIn_queueStep_sub U x (N.neighborhood jset) jk
      simp only [runTokens, primitiveCutSum, trajectoryWaste]
      change
        JobState.jobsIn (N.runTokens U xnext rest) (N.neighborhood jset) -
            JobState.jobsIn x (N.neighborhood jset) <=
          N.primitiveCutIncrement jset jk +
            N.primitiveCutSum jset rest +
          (N.wasteIndicator U x jk +
            N.trajectoryWaste U xnext rest)
      change
        JobState.jobsIn xnext (N.neighborhood jset) -
            JobState.jobsIn x (N.neighborhood jset) =
          N.cutChange U x (N.neighborhood jset) jk at hbalance
      linarith

/-- If the primitive cut walk falls below minus its initial queue mass, at
least one token must have been wasted. -/
theorem trajectoryWaste_pos_of_primitiveCutSum_lt
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (jset : Finset Server)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (hdrop :
      N.primitiveCutSum jset tokens <
        -JobState.jobsIn x (N.neighborhood jset)) :
    0 < N.trajectoryWaste U x tokens := by
  have hbound := N.runTokens_jobsIn_sub_le U x jset tokens
  have hfinal :
      0 <= JobState.jobsIn
        (N.runTokens U x tokens) (N.neighborhood jset) := by
    unfold JobState.jobsIn
    exact Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  have hwaste := N.trajectoryWaste_nonneg U x tokens
  by_contra hnot
  have hzero : N.trajectoryWaste U x tokens = 0 :=
    le_antisymm (le_of_not_gt hnot) hwaste
  rw [hzero, add_zero] at hbound
  linarith

end Network

end StateDepMOR
