import StateDepMOR.Network

/-!
# Scheduling policies and performance semantics

This file is a typed specification layer for the policy and performance
definitions in `StateDep_MOR.tex`.  It deliberately does not model the
underlying stochastic process.
-/

open scoped BigOperators
open Filter

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

/-- The integer state space `Ω_K` in `StateDep_MOR.tex`, lines 526--531:
nonnegative queue lengths whose sum is exactly `K`. -/
@[ext]
structure JobState (Buffer : Type u) [Fintype Buffer] (K : ℕ) where
  jobs : Buffer → ℕ
  total_jobs : ∑ i, jobs i = K

namespace JobState

instance {K : ℕ} : CoeFun (JobState Buffer K) fun _ => Buffer → ℕ :=
  ⟨JobState.jobs⟩

end JobState

namespace Network

variable (N : Network Buffer Server)

/-- A scheduling action is either a selected buffer or `none`, corresponding
to `∅` (a wasted service token) in `StateDep_MOR.tex`, lines 533--541. -/
abbrev ServiceAction (_N : Network Buffer Server) := Option Buffer

/-- Admissibility from `StateDep_MOR.tex`, lines 562--574: a selected buffer
must be compatible with the origin server and currently nonempty.  The
explicit waste action `none` remains legal. -/
def IsLegalAction {K : ℕ} (x : JobState Buffer K) (j : Server) :
    N.ServiceAction → Prop
  | none => True
  | some i => N.compatible i j ∧ 0 < x i

/-- A deterministic stationary policy `U^K ∈ 𝒰^K` from
`StateDep_MOR.tex`, lines 533--541.  It observes only the current state and
the marked service-token type `(j', k)`, and every selected action is
admissible. -/
structure DeterministicStationaryPolicy (K : ℕ) where
  action : JobState Buffer K → Server → Buffer → N.ServiceAction
  legal : ∀ x j k, N.IsLegalAction x j (action x j k)

namespace DeterministicStationaryPolicy

instance {K : ℕ} :
    CoeFun (N.DeterministicStationaryPolicy K)
      fun _ => JobState Buffer K → Server → Buffer → N.ServiceAction :=
  ⟨DeterministicStationaryPolicy.action⟩

end DeterministicStationaryPolicy

/-- A paper policy `U = (U^K)_{K=1}^∞`; using `ℕ+` makes the lower bound
`K ≥ 1` part of the type.  See `StateDep_MOR.tex`, lines 485 and 537--541. -/
abbrev DeterministicPolicySequence :=
  ∀ K : ℕ+, N.DeterministicStationaryPolicy (K : ℕ)

/-- A stationary policy is non-idling when it wastes a token exactly when
the origin server has no compatible nonempty buffer.  This separates the
non-idling condition used later in the paper from basic admissibility. -/
def IsNonIdling {K : ℕ} (U : N.DeterministicStationaryPolicy K) : Prop :=
  ∀ x j k, U x j k = none ↔ ∀ i, N.compatible i j → x i = 0

/-- A sequence is non-idling at every positive job count `K`. -/
def IsNonIdlingSequence (U : N.DeterministicPolicySequence) : Prop :=
  ∀ K, N.IsNonIdling (U K)

section SMW

variable [LinearOrder Buffer]

/-- The scaled queue length `X_i / α_i` in Definition SMW(`α`),
`StateDep_MOR.tex`, lines 791--798. -/
noncomputable def scaledQueueLength (_N : Network Buffer Server) {K : ℕ}
    (α : Simplex Buffer) (x : JobState Buffer K)
    (i : Buffer) : ℝ :=
  (x i : ℝ) / α i

/-- Declarative characterization of the deterministic SMW winner: it has
maximum scaled queue length among compatible buffers, and every tied
maximizer has index at most its index.  Thus it is the highest-index
maximizer required at `StateDep_MOR.tex`, line 797. -/
def IsSMWWinner {K : ℕ} (α : Simplex Buffer) (x : JobState Buffer K)
    (j : Server) (i : Buffer) : Prop :=
  N.compatible i j ∧
    (∀ q, N.compatible q j → N.scaledQueueLength α x q ≤ N.scaledQueueLength α x i) ∧
    (∀ q, N.compatible q j → N.scaledQueueLength α x q =
      N.scaledQueueLength α x i → q ≤ i)

private theorem exists_smwWinner {K : ℕ} (α : Simplex Buffer)
    (x : JobState Buffer K) (j : Server) :
    ∃ i, N.IsSMWWinner α x j i := by
  classical
  let s := N.buffersOf j
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := N.server_has_neighbor j
    exact ⟨i, N.mem_buffersOf i j |>.2 hi⟩
  obtain ⟨i₀, hi₀s, hi₀max⟩ :=
    Finset.exists_max_image s (N.scaledQueueLength α x) hs
  let maximizers := s.filter fun i => N.scaledQueueLength α x i =
    N.scaledQueueLength α x i₀
  have hi₀m : i₀ ∈ maximizers := by
    simp [maximizers, hi₀s]
  have hm : maximizers.Nonempty := ⟨i₀, hi₀m⟩
  let i := maximizers.max' hm
  have him : i ∈ maximizers := maximizers.max'_mem hm
  have his : i ∈ s := (Finset.mem_filter.1 him).1
  have hiweight : N.scaledQueueLength α x i =
      N.scaledQueueLength α x i₀ := (Finset.mem_filter.1 him).2
  refine ⟨i, N.mem_buffersOf i j |>.1 his, ?_, ?_⟩
  · intro q hq
    rw [hiweight]
    exact hi₀max q (N.mem_buffersOf q j |>.2 hq)
  · intro q hq htie
    apply maximizers.le_max' q
    apply Finset.mem_filter.2
    refine ⟨N.mem_buffersOf q j |>.2 hq, ?_⟩
    rw [← hiweight]
    exact htie

/-- The unique highest-index compatible maximizer used by the executable
SMW constructor. -/
noncomputable def smwWinner {K : ℕ} (α : Simplex Buffer)
    (x : JobState Buffer K) (j : Server) : Buffer :=
  Classical.choose (N.exists_smwWinner α x j)

theorem smwWinner_spec {K : ℕ} (α : Simplex Buffer)
    (x : JobState Buffer K) (j : Server) :
    N.IsSMWWinner α x j (N.smwWinner α x j) :=
  Classical.choose_spec (N.exists_smwWinner α x j)

/-- The action in Definition SMW(`α`), `StateDep_MOR.tex`, lines 791--798.
It serves the highest-index scaled maximizer exactly when that maximum is
positive; because `α` is interior, this is equivalent to the winner's queue
being nonempty. -/
noncomputable def smwAction {K : ℕ} (α : Simplex Buffer)
    (x : JobState Buffer K) (j : Server) : N.ServiceAction :=
  if 0 < x (N.smwWinner α x j) then some (N.smwWinner α x j) else none

/-- Source-faithful readback of one SMW decision, including the positive-max
rule and deterministic highest-index tie break from
`StateDep_MOR.tex`, lines 791--798. -/
def IsSMWAction {K : ℕ} (α : Simplex Buffer) (x : JobState Buffer K)
    (j : Server) (a : N.ServiceAction) : Prop :=
  if ∃ q, N.compatible q j ∧ 0 < x q then
    ∃ i, a = some i ∧ 0 < x i ∧ N.IsSMWWinner α x j i
  else
    a = none

private theorem smwWinner_positive {K : ℕ} {α : Simplex Buffer}
    (hα : α.IsInterior) (x : JobState Buffer K) (j : Server)
    (h : ∃ q, N.compatible q j ∧ 0 < x q) :
    0 < x (N.smwWinner α x j) := by
  obtain ⟨q, hqj, hqx⟩ := h
  have hqweight : 0 < N.scaledQueueLength α x q :=
    div_pos (Nat.cast_pos.2 hqx) (hα q)
  have hiweight : 0 < N.scaledQueueLength α x (N.smwWinner α x j) :=
    hqweight.trans_le ((N.smwWinner_spec α x j).2.1 q hqj)
  rcases (div_pos_iff.1 hiweight) with hpos | hneg
  · exact_mod_cast hpos.1
  · exact ((not_lt_of_ge (le_of_lt (hα (N.smwWinner α x j)))) hneg.2).elim

theorem smwAction_spec {K : ℕ} {α : Simplex Buffer}
    (hα : α.IsInterior) (x : JobState Buffer K) (j : Server) :
    N.IsSMWAction α x j (N.smwAction α x j) := by
  classical
  unfold IsSMWAction
  split_ifs with h
  · refine ⟨N.smwWinner α x j, ?_, N.smwWinner_positive hα x j h,
      N.smwWinner_spec α x j⟩
    simp [smwAction, N.smwWinner_positive hα x j h]
  · have hz : x (N.smwWinner α x j) = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hi
      exact h ⟨N.smwWinner α x j, (N.smwWinner_spec α x j).1, hi⟩
    simp [smwAction, hz]

/-- The deterministic stationary SMW(`α`) policy for a fixed `K`. -/
noncomputable def smwStationaryPolicy (α : Simplex Buffer)
    (_hα : α.IsInterior) (K : ℕ) : N.DeterministicStationaryPolicy K where
  action x j _k := N.smwAction α x j
  legal x j _k := by
    classical
    simp only [smwAction]
    split_ifs with h
    · exact ⟨(N.smwWinner_spec α x j).1, h⟩
    · trivial

/-- Constructor for the paper's policy sequence SMW(`α`). -/
noncomputable def smwPolicy (α : Simplex Buffer) (hα : α.IsInterior) :
    N.DeterministicPolicySequence :=
  fun K => N.smwStationaryPolicy α hα K

/-- Predicate form of Definition SMW(`α`), useful for statement readbacks. -/
def IsSMWPolicy (α : Simplex Buffer) (U : N.DeterministicPolicySequence) : Prop :=
  α.IsInterior ∧ ∀ K x j k, N.IsSMWAction α x j (U K x j k)

theorem smwPolicy_isSMW (α : Simplex Buffer) (hα : α.IsInterior) :
    N.IsSMWPolicy α (N.smwPolicy α hα) := by
  refine ⟨hα, ?_⟩
  intro K x j k
  exact N.smwAction_spec hα x j

theorem smwPolicy_nonIdling (α : Simplex Buffer) (hα : α.IsInterior) :
    N.IsNonIdlingSequence (N.smwPolicy α hα) := by
  intro K x j k
  constructor
  · intro hnone i hij
    by_contra hi
    have hipos : 0 < x i := Nat.pos_of_ne_zero hi
    have hwinner := N.smwWinner_positive hα x j ⟨i, hij, hipos⟩
    simp [smwPolicy, smwStationaryPolicy, smwAction, hwinner] at hnone
  · intro hall
    have hz : x (N.smwWinner α x j) = 0 :=
      hall _ (N.smwWinner_spec α x j).1
    simp [smwPolicy, smwStationaryPolicy, smwAction, hz]

end SMW

end Network

/-- An abstract interpretation of the paper's long-run throughput-loss
probability `P^{K,U}` from equation `eq:lb_performance_measure`,
`StateDep_MOR.tex`, lines 609--625.  No stochastic construction is assumed;
only the probability bounds are exposed. -/
structure PerformanceSemantics (N : Network Buffer Server) where
  loss : N.DeterministicPolicySequence → ℕ+ → ℝ
  loss_nonneg : ∀ U K, 0 ≤ loss U K
  loss_le_one : ∀ U K, loss U K ≤ 1

namespace PerformanceSemantics

variable {N : Network Buffer Server}

omit [DecidableEq Buffer] [DecidableEq Server] in
theorem loss_mem_Icc (P : PerformanceSemantics N)
    (U : N.DeterministicPolicySequence) (K : ℕ+) :
    P.loss U K ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨P.loss_nonneg U K, P.loss_le_one U K⟩

/-- The term `(1/K) log P^{K,U}` in equation `eq:lb_measure_rate`.
`ENNReal.log` maps a zero loss to `⊥`, preserving `log 0 = -∞`. -/
noncomputable def scaledLogLoss (P : PerformanceSemantics N)
    (U : N.DeterministicPolicySequence) (K : ℕ+) : EReal :=
  ENNReal.log (ENNReal.ofReal (P.loss U K)) / (((K : ℕ) : ℝ) : EReal)

/-- The exact throughput-loss exponent
`γ(U) = -limsup_{K→∞} K⁻¹ log P^{K,U}` from equation
`eq:lb_measure_rate`, `StateDep_MOR.tex`, lines 628--632.

The index type is `ℕ+`, so the asymptotic sequence starts at `K = 1`.
-/
noncomputable def throughputLossExponent (P : PerformanceSemantics N)
    (U : N.DeterministicPolicySequence) : EReal :=
  -Filter.limsup (P.scaledLogLoss U) Filter.atTop

omit [DecidableEq Buffer] [DecidableEq Server] in
theorem scaledLogLoss_eq_bot_of_loss_eq_zero (P : PerformanceSemantics N)
    (U : N.DeterministicPolicySequence) (K : ℕ+) (h : P.loss U K = 0) :
    P.scaledLogLoss U K = ⊥ := by
  rw [scaledLogLoss, h, ENNReal.ofReal_zero, ENNReal.log_zero]
  apply EReal.bot_div_of_pos_ne_top
  · exact_mod_cast PNat.pos K
  · exact EReal.coe_ne_top _

/-- At every `K` where loss is zero, the finite-`K` negative logarithmic
rate is `+∞`. -/
theorem neg_scaledLogLoss_eq_top_of_loss_eq_zero (P : PerformanceSemantics N)
    (U : N.DeterministicPolicySequence) (K : ℕ+) (h : P.loss U K = 0) :
    -(P.scaledLogLoss U K) = ⊤ := by
  rw [P.scaledLogLoss_eq_bot_of_loss_eq_zero U K h]
  exact EReal.neg_bot

/-- A policy with identically zero loss has throughput-loss exponent `+∞`,
as required by the extended-real interpretation of equation
`eq:lb_measure_rate`. -/
theorem throughputLossExponent_eq_top_of_loss_eq_zero (P : PerformanceSemantics N)
    (U : N.DeterministicPolicySequence) (h : ∀ K, P.loss U K = 0) :
    P.throughputLossExponent U = ⊤ := by
  have hscaled : P.scaledLogLoss U = fun _ => (⊥ : EReal) := by
    funext K
    exact P.scaledLogLoss_eq_bot_of_loss_eq_zero U K (h K)
  rw [throughputLossExponent, hscaled, Filter.limsup_const_bot, EReal.neg_bot]

end PerformanceSemantics

/-- Source-faithful meaning of `f(K) = Ω(1/K²)` in
Proposition `prop:state_ind_no_exp`, `StateDep_MOR.tex`, lines 911--918:
an eventually valid lower bound with a positive constant. -/
def IsOmegaOneDivSq (f : ℕ+ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ K : ℕ+ in Filter.atTop, c / ((K : ℝ) ^ 2) ≤ f K

/-- Source-faithful positive-liminf predicate from
Proposition `prop:state_ind_no_exp`, `StateDep_MOR.tex`, lines 911--918. -/
noncomputable def HasPositiveLiminf (f : ℕ+ → ℝ) : Prop :=
  0 < Filter.liminf f Filter.atTop

end StateDepMOR
