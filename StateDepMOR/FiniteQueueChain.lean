import StateDepMOR.Policy
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Finite queueing-chain semantics

This module gives the event-epoch dynamics of the closed queueing network.
A token type is sampled with probability `phi j k`; a deterministic
stationary policy then either wastes the token or moves one job from the
selected source buffer to the token's destination.

No assertion about existence or uniqueness of invariant laws is made here.
-/

open scoped BigOperators ENNReal

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace JobState

theorem coordinate_le {K : ℕ} (x : JobState Buffer K) (i : Buffer) :
    x i ≤ K := by
  calc
    x i ≤ ∑ q, x q :=
      Finset.single_le_sum (fun q _ => Nat.zero_le (x q)) (Finset.mem_univ i)
    _ = K := x.total_jobs

/-- Queue states are finite because every coordinate lies in `Fin (K + 1)`. -/
noncomputable instance instFintype (K : ℕ) : Fintype (JobState Buffer K) :=
  Fintype.ofInjective
    (fun x i => (⟨x i, Nat.lt_succ_of_le (x.coordinate_le i)⟩ : Fin (K + 1)))
    (by
      intro x y hxy
      apply JobState.ext
      funext i
      exact congrArg Fin.val (congrFun hxy i))

/-- If there is at least one buffer, putting all jobs there gives a queue
state for every `K`. -/
noncomputable instance instNonempty (K : ℕ) [Nonempty Buffer] :
    Nonempty (JobState Buffer K) := by
  classical
  let i₀ : Buffer := Classical.choice (inferInstance : Nonempty Buffer)
  refine ⟨{ jobs := fun i => if i = i₀ then K else 0, total_jobs := ?_ }⟩
  simp [i₀]

private theorem sum_update_sub_one_add_one
    (f : Buffer → ℕ) (i : Buffer) (hi : 0 < f i) :
    (∑ q, Function.update f i (f i - 1) q) + 1 = ∑ q, f q := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hsum :=
    Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

private theorem sum_update_add_one
    (f : Buffer → ℕ) (i : Buffer) :
    (∑ q, Function.update f i (f i + 1) q) = (∑ q, f q) + 1 := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hsum :=
    Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

/-- Move one job from `src` to `dst`. The two updates are deliberately
sequential, so `src = dst` leaves the queue state unchanged. -/
def moveJob {K : ℕ} (x : JobState Buffer K) (src dst : Buffer)
    (hsrc : 0 < x src) : JobState Buffer K := by
  let afterDeparture := Function.update x.jobs src (x src - 1)
  let afterArrival :=
    Function.update afterDeparture dst (afterDeparture dst + 1)
  refine ⟨afterArrival, ?_⟩
  have hdeparture :
      (∑ i, afterDeparture i) + 1 = ∑ i, x i := by
    exact sum_update_sub_one_add_one x.jobs src hsrc
  have harrival :
      (∑ i, afterArrival i) = (∑ i, afterDeparture i) + 1 := by
    exact sum_update_add_one afterDeparture dst
  calc
    ∑ i, afterArrival i = ∑ i, afterDeparture i + 1 := harrival
    _ = ∑ i, x i := hdeparture
    _ = K := x.total_jobs

@[simp]
theorem moveJob_total_jobs {K : ℕ} (x : JobState Buffer K)
    (src dst : Buffer) (hsrc : 0 < x src) :
    ∑ i, moveJob x src dst hsrc i = K :=
  (moveJob x src dst hsrc).total_jobs

end JobState

namespace Network

variable (N : Network Buffer Server)

/-- A marked service-token type `(origin server, destination buffer)`. -/
abbrev TokenType := Server × Buffer

/-- The finite token law whose atom `(j,k)` has mass `phi j k`. -/
noncomputable def tokenLaw : PMF (TokenType (Buffer := Buffer) (Server := Server)) :=
  PMF.ofFintype
    (fun jk => ENNReal.ofReal (N.phi jk.1 jk.2))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · rw [Fintype.sum_prod_type, N.total_rate]
        simp
      · intro jk _
        exact N.phi_nonneg jk.1 jk.2)

@[simp]
theorem tokenLaw_apply (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    N.tokenLaw jk = ENNReal.ofReal (N.phi jk.1 jk.2) :=
  rfl

@[simp]
theorem tokenLaw_toReal (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    (N.tokenLaw jk).toReal = N.phi jk.1 jk.2 := by
  rw [tokenLaw_apply, ENNReal.toReal_ofReal (N.phi_nonneg jk.1 jk.2)]

/-- Apply one marked service token under `U`. A wasted token leaves the state
unchanged; a selected legal source loses one job and the destination gains
that job. -/
def queueStep {K : ℕ} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    JobState Buffer K :=
  match h : U x jk.1 jk.2 with
  | none => x
  | some i =>
      x.moveJob i jk.2 (by
        have hlegal := U.legal x jk.1 jk.2
        rw [h] at hlegal
        exact hlegal.2)

/-- Real-valued indicator that the policy discards the current token. -/
def wasteIndicator {K : ℕ} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) : ℝ :=
  if U x jk.1 jk.2 = none then 1 else 0

theorem wasteIndicator_nonneg {K : ℕ}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    0 ≤ N.wasteIndicator U x jk := by
  by_cases h : U x jk.1 jk.2 = none <;> simp [wasteIndicator, h]

theorem wasteIndicator_le_one {K : ℕ}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    N.wasteIndicator U x jk ≤ 1 := by
  by_cases h : U x jk.1 jk.2 = none <;> simp [wasteIndicator, h]

/-- Job-count conservation for every legal policy decision. -/
@[simp]
theorem queueStep_total_jobs {K : ℕ}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    ∑ i, N.queueStep U x jk i = K :=
  (N.queueStep U x jk).total_jobs

/-- Event-epoch transition law, obtained by pushing the marked-token law
through the deterministic queue update. -/
noncomputable def transitionPMF {K : ℕ}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K) :
    PMF (JobState Buffer K) :=
  (N.tokenLaw).map (N.queueStep U x)

/-- An invariant probability mass function for the event-epoch queue chain. -/
def IsInvariantPMF {K : ℕ} (U : N.DeterministicStationaryPolicy K)
    (π : PMF (JobState Buffer K)) : Prop :=
  π.bind (N.transitionPMF U) = π

/-- Expected waste at the next service-token epoch from a fixed state. -/
noncomputable def oneStepWaste {K : ℕ}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K) : ℝ :=
  ∑ jk, (N.tokenLaw jk).toReal * N.wasteIndicator U x jk

/-- Stationary expected waste per service-token epoch under an invariant
queue-state PMF. The definition is meaningful for every PMF; invariance is a
separate predicate so callers can retain the proof explicitly. -/
noncomputable def stationaryOneStepWaste {K : ℕ}
    (U : N.DeterministicStationaryPolicy K)
    (π : PMF (JobState Buffer K)) : ℝ :=
  ∑ x, (π x).toReal * N.oneStepWaste U x

end Network

end StateDepMOR
