import StateDepMOR.GammaLowerBound
import StateDepMOR.PoissonCountLDP
import StateDepMOR.FiniteQueueTrajectories
import StateDepMOR.EventEpochExecution
import StateDepMOR.FluidAttraction
import StateDepMOR.HallNecessary
import StateDepMOR.HallCriticalEquality
import StateDepMOR.GammaOptimizer
import StateDepMOR.Asymptotics
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Concrete converse proofs

This module proves the two converse exports using the concrete finite queue
chain and `Network.minimumInvariantLossFamily`.  The proof is split between
the ample-flexibility case, where the variational converse value is `top`,
and finite-horizon forcing arguments in the limited-flexibility case.
-/

open scoped BigOperators ENNReal Topology
open Filter Set

namespace StateDepMOR

/-! ## Finite stationary-law support -/

/-- Every PMF on a nonempty finite type has an atom at least the reciprocal
of the cardinality. -/
theorem exists_pmf_atom_ge_card_reciprocal
    {A : Type*} [Fintype A] [Nonempty A] (pi : PMF A) :
    exists x : A, 1 / (Fintype.card A : Real) <= (pi x).toReal := by
  by_contra h
  push Not at h
  have hcard : 0 < (Fintype.card A : Real) := by
    exact_mod_cast Fintype.card_pos
  have hsum :
      (Finset.univ.sum fun x : A => (pi x).toReal) <
        Finset.univ.sum (fun _x : A =>
          1 / (Fintype.card A : Real)) := by
    apply Finset.sum_lt_sum
    · intro x _hx
      exact (h x).le
    · let x : A := Classical.choice (inferInstance : Nonempty A)
      exact ⟨x, Finset.mem_univ x, h x⟩
  rw [PMF.sum_toReal] at hsum
  simpa [hcard.ne'] using hsum

namespace JobState

/-- The finite queue-state space embeds into the coordinate box
`{0, ..., K}^Buffer`. -/
theorem card_le_coordinate_box
    {Buffer : Type*} [Fintype Buffer] [DecidableEq Buffer]
    (K : Nat) :
    Fintype.card (JobState Buffer K) <=
      (K + 1) ^ Fintype.card Buffer := by
  let f : JobState Buffer K -> Buffer -> Fin (K + 1) :=
    fun x i => Fin.mk (x i) (Nat.lt_succ_of_le (x.coordinate_le i))
  have hf : Function.Injective f := by
    intro x y hxy
    apply JobState.ext
    funext i
    exact congrArg Fin.val (congrFun hxy i)
  calc
    Fintype.card (JobState Buffer K) <=
        Fintype.card (Buffer -> Fin (K + 1)) :=
      Fintype.card_le_of_injective f hf
    _ = (K + 1) ^ Fintype.card Buffer := by simp

end JobState

namespace Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-- At every positive system size, the selected minimum-loss invariant law
has an atom with the polynomial state-space lower bound. -/
theorem exists_minimumInvariantPMF_atom_ge_polynomial
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (K : PNat) :
    exists x : JobState Buffer (K : Nat),
      1 / (((K : Nat) + 1 : Nat) ^ Fintype.card Buffer : Real) <=
        (N.minimumInvariantPMF (U K) x).toReal := by
  obtain ⟨x, hx⟩ :=
    exists_pmf_atom_ge_card_reciprocal
      (N.minimumInvariantPMF (U K))
  refine ⟨x, ?_⟩
  have hcard_pos :
      0 < (Fintype.card (JobState Buffer (K : Nat)) : Real) := by
    exact_mod_cast Fintype.card_pos
  have hcard_le :
      (Fintype.card (JobState Buffer (K : Nat)) : Real) <=
        ((((K : Nat) + 1 : Nat) ^ Fintype.card Buffer : Nat) : Real) := by
    exact_mod_cast
      JobState.card_le_coordinate_box (Buffer := Buffer) (K : Nat)
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    (one_div_le_one_div_of_le hcard_pos hcard_le).trans hx

end Network

namespace PaperStatements
namespace Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

private noncomputable def converseSelectedBuffer
    (N : StateDepMOR.Network Buffer Server) (j : Server) : Buffer :=
  Classical.choose (N.server_has_neighbor j)

private theorem converseSelectedBuffer_compatible
    (N : StateDepMOR.Network Buffer Server) (j : Server) :
    N.compatible (converseSelectedBuffer N j) j :=
  Classical.choose_spec (N.server_has_neighbor j)

private theorem noWasteDrift_sum_eq_zero
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) {drift : Buffer -> Real}
    (hdrift : drift ∈ N.noWasteDriftSet f) :
    Finset.sum Finset.univ drift = 0 := by
  classical
  obtain ⟨d, _hdnonneg, hdsum, hdrift⟩ := hdrift
  simp_rw [hdrift, Finset.sum_sub_distrib]
  have harrivals :
      Finset.sum Finset.univ
          (fun i => Finset.sum Finset.univ (fun j => f j i)) =
        Finset.sum Finset.univ
          (fun j => Finset.sum Finset.univ (fun k => f j k)) := by
    rw [Finset.sum_comm]
  have hdepartures :
      Finset.sum Finset.univ
          (fun i => Finset.sum (N.serversOf i) (fun j =>
            d i j * Finset.sum Finset.univ (fun k => f j k))) =
        Finset.sum Finset.univ
          (fun j => Finset.sum Finset.univ (fun k => f j k)) := by
    simp only [StateDepMOR.Network.serversOf, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show
        Finset.sum Finset.univ
            (fun i =>
              if N.compatible i j then
                d i j * Finset.sum Finset.univ (fun k => f j k)
              else 0) =
          Finset.sum (N.buffersOf j)
            (fun i => d i j * Finset.sum Finset.univ (fun k => f j k)) by
      simp only [StateDepMOR.Network.buffersOf, Finset.sum_filter]]
    rw [← Finset.sum_mul, hdsum j, one_mul]
  rw [harrivals, hdepartures, sub_self]

private theorem noWasteLyapunov_nonneg
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real) {drift : Buffer -> Real}
    (hdrift : drift ∈ N.noWasteDriftSet f) :
    0 <= Lyapunov.LAlphaAmbient (fun i => alpha i)
      ((fun i => alpha i) + drift) := by
  have hsum := noWasteDrift_sum_eq_zero N f hdrift
  have hexists : exists i, drift i <= 0 := by
    by_contra h
    push Not at h
    have hpos : 0 < Finset.sum Finset.univ drift :=
      Finset.sum_pos (fun i _ => h i) Finset.univ_nonempty
    rw [hsum] at hpos
    exact lt_irrefl 0 hpos
  obtain ⟨i, hi⟩ := hexists
  rw [Lyapunov.LAlphaAmbient_centered
    (fun i => alpha i) drift (fun i => ne_of_gt (halpha i))]
  have hratio : drift i / alpha i <= 0 :=
    div_nonpos_of_nonpos_of_nonneg hi (halpha i).le
  have hmin :
      Lyapunov.minCoordinate (fun q => drift q / alpha q) <= 0 :=
    (Finset.inf'_le (fun q => drift q / alpha q)
      (Finset.mem_univ i)).trans hratio
  linarith

private theorem vAlpha_le_of_noWasteDrift
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real) {drift : Buffer -> Real}
    (hdrift : drift ∈ N.noWasteDriftSet f) :
    vAlpha (N := N) alpha f <=
      Lyapunov.LAlphaAmbient (fun i => alpha i)
        ((fun i => alpha i) + drift) := by
  unfold vAlpha
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro value hvalue
    obtain ⟨z, hz, rfl⟩ := hvalue
    exact noWasteLyapunov_nonneg N alpha halpha f hz
  · exact ⟨drift, hdrift, rfl⟩

private theorem zero_mem_noWasteDriftSet_of_supported
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    (hf : IsNonnegativeRate f)
    (hsupported : forall j k, 0 < f j k -> N.compatible k j) :
    (0 : Buffer -> Real) ∈ N.noWasteDriftSet f := by
  classical
  let row : Server -> Real :=
    fun j => Finset.sum Finset.univ (fun k => f j k)
  let d : Buffer -> Server -> Real := fun i j =>
    if hrow : row j = 0 then
      if i = converseSelectedBuffer N j then 1 else 0
    else
      if N.compatible i j then f j i / row j else 0
  have hrow_nonneg (j : Server) : 0 <= row j := by
    exact Finset.sum_nonneg (fun k _ => hf j k)
  have hzero (j : Server) (hrow : row j = 0) (k : Buffer) :
      f j k = 0 := by
    have hle : f j k <= row j := by
      exact Finset.single_le_sum (fun q _ => hf j q) (Finset.mem_univ k)
    rw [hrow] at hle
    exact le_antisymm hle (hf j k)
  have hfull (j : Server) (hrow : row j ≠ 0) :
      Finset.sum (N.buffersOf j) (fun i => f j i) = row j := by
    rw [show row j = Finset.sum Finset.univ (fun i => f j i) by rfl]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hiuniv hin
    have hincompat : Not (N.compatible i j) := by
      intro hcompat
      exact hin ((N.mem_buffersOf i j).2 hcompat)
    have hnotpos : Not (0 < f j i) := fun hpos =>
      hincompat (hsupported j i hpos)
    exact le_antisymm (le_of_not_gt hnotpos) (hf j i)
  refine ⟨d, ?_, ?_, ?_⟩
  · intro i j
    dsimp [d]
    split_ifs <;>
      try positivity
    exact div_nonneg (hf j i) (hrow_nonneg j)
  · intro j
    by_cases hrow : row j = 0
    · have hselected :
          converseSelectedBuffer N j ∈ N.buffersOf j :=
        (N.mem_buffersOf _ j).2 (converseSelectedBuffer_compatible N j)
      simp [d, hrow, hselected]
    · have hrowpos : 0 < row j :=
        lt_of_le_of_ne (hrow_nonneg j) (Ne.symm hrow)
      simp only [d, hrow, dite_false]
      rw [show
          Finset.sum (N.buffersOf j)
              (fun i => if N.compatible i j then f j i / row j else 0) =
            Finset.sum (N.buffersOf j) (fun i => f j i / row j) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [if_pos ((N.mem_buffersOf i j).1 hi)]]
      rw [← Finset.sum_div, hfull j hrow, div_self hrow]
  · intro i
    simp only [Pi.zero_apply]
    have hterm (j : Server) :
        d i j * row j = f j i := by
      by_cases hrow : row j = 0
      · rw [hzero j hrow i]
        simp [d, row, hrow]
      · by_cases hfzero : f j i = 0
        · simp [d, row, hrow, hfzero]
        · have hpositive : 0 < f j i :=
            lt_of_le_of_ne (hf j i) (Ne.symm hfzero)
          have hcompat : N.compatible i j :=
            hsupported j i hpositive
          simp [d, row, hrow, hcompat]
    rw [show
        Finset.sum (N.serversOf i)
            (fun j => d i j * Finset.sum Finset.univ (fun k => f j k)) =
          Finset.sum Finset.univ (fun j => f j i) by
      rw [← Finset.sum_subset (Finset.subset_univ (N.serversOf i))]
      · apply Finset.sum_congr rfl
        intro j hj
        simpa only [row] using hterm j
      · intro j hjuniv hjnot
        have hincompat : Not (N.compatible i j) := by
          intro hcompat
          exact hjnot ((N.mem_serversOf i j).2 hcompat)
        have hnotpos : Not (0 < f j i) := fun hpos =>
          hincompat (hsupported j i hpos)
        exact le_antisymm (le_of_not_gt hnotpos) (hf j i)]
    exact (sub_self _).symm

private theorem gammaCB_eq_top_of_not_limited
    (N : StateDepMOR.Network Buffer Server)
    (hample : Not N.HasLimitedFlexibility)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior) :
    gammaCB (N := N) alpha = (Top.top : EReal) := by
  classical
  unfold gammaCB
  apply sInf_eq_top.mpr
  intro q hq
  obtain ⟨f, hf, hv, rfl⟩ := hq
  have hlocal : N.localRate f = (Top.top : ENNReal) := by
    by_contra hfinite
    have hsupported : forall j k, 0 < f j k -> N.compatible k j := by
      intro j k hpositive
      by_cases hphi : N.phi j k = 0
      · have := N.localRate_ne_top_implies_zero_of_phi_eq_zero
          f hfinite j k hphi
        linarith
      · have hphipos : 0 < N.phi j k :=
          lt_of_le_of_ne (N.phi_nonneg j k) (Ne.symm hphi)
        by_contra hincompatible
        exact hample ⟨j, k, hincompatible, hphipos⟩
    have hzero :
        (0 : Buffer -> Real) ∈ N.noWasteDriftSet f :=
      zero_mem_noWasteDriftSet_of_supported N f hf hsupported
    have hvle :
        vAlpha (N := N) alpha f <= 0 := by
      have h := vAlpha_le_of_noWasteDrift N alpha halpha f hzero
      have hself :
          Lyapunov.LAlphaAmbient (fun i => alpha i)
              (fun i => alpha i) = 0 := by
        have hcentered := Lyapunov.LAlphaAmbient_centered
          (fun i => alpha i) (0 : Buffer -> Real)
          (fun i => ne_of_gt (halpha i))
        simpa [Lyapunov.minCoordinate] using hcentered
      simpa [hself] using h
    exact (not_lt_of_ge hvle) hv
  rw [hlocal]
  exact EReal.top_div_of_pos_ne_top
    (EReal.coe_pos.2 hv) (EReal.coe_ne_top _)

theorem gammaCBSup_eq_top_of_not_limited
    (N : StateDepMOR.Network Buffer Server)
    (hample : Not N.HasLimitedFlexibility) :
    gammaCBSup (N := N) = (Top.top : EReal) := by
  classical
  apply top_unique
  unfold gammaCBSup
  apply le_csSup
  · exact ⟨Top.top, fun _ _ => le_top⟩
  · refine ⟨Simplex.uniform, Simplex.uniform_isInterior, ?_⟩
    exact (gammaCB_eq_top_of_not_limited
      N hample Simplex.uniform Simplex.uniform_isInterior).symm

end Network
end PaperStatements
end StateDepMOR

namespace StateDepMOR
namespace Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : Network Buffer Server)

/-! ## Exact finite-block accounting -/

def finiteTokenCounts
    (_N : Network Buffer Server)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    Server -> Buffer -> Nat :=
  fun j k => tokens.count (j, k)

def finiteTokenRates
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    Server -> Buffer -> Real :=
  fun j k => (N.finiteTokenCounts tokens j k : Real)

private theorem oneStep_incoming {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun q : Buffer =>
        if U x jk.1 jk.2 = some q /\ jk.1 = j /\ jk.2 = i
        then (1 : Real) else 0) =
      match U x jk.1 jk.2 with
      | none => 0
      | some _ => if jk.2 = i then 1 else 0 := by
  classical
  cases haction : U x jk.1 jk.2 with
  | none => simp [haction]
  | some q =>
      by_cases hki : jk.2 = i
      next =>
        subst i
        rw [Finset.sum_eq_single jk.1]
        next =>
          rw [Finset.sum_eq_single q]
          next => simp [haction]
          next =>
            intro b _ hb
            simp [haction, Ne.symm hb]
          next => simp
        next =>
          intro s _ hs
          simp [haction, Ne.symm hs]
        next => simp
      next =>
        simp only [haction, hki, if_false]
        apply Finset.sum_eq_zero
        intro s _
        apply Finset.sum_eq_zero
        intro q' _
        simp [hki]

private theorem oneStep_outgoing {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        if U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k
        then (1 : Real) else 0) =
      if U x jk.1 jk.2 = some i then 1 else 0 := by
  classical
  by_cases hi : U x jk.1 jk.2 = some i
  next =>
    rw [Finset.sum_eq_single jk.1]
    next =>
      rw [Finset.sum_eq_single jk.2]
      next => simp [hi]
      next =>
        intro k _ hk
        simp [hi, Ne.symm hk]
      next => simp
    next =>
      intro j _ hj
      simp [hi, Ne.symm hj]
    next => simp
  next => simp [hi]

private theorem queueStep_coordinate_sub {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    ((N.queueStep U x jk i : Nat) : Real) - (x i : Real) =
      (match U x jk.1 jk.2 with
        | none => 0
        | some _ => if jk.2 = i then 1 else 0) -
      (if U x jk.1 jk.2 = some i then 1 else 0) := by
  have h := N.jobsIn_queueStep_sub U x ({i} : Finset Buffer) jk
  cases haction : U x jk.1 jk.2 with
  | none => simpa [JobState.jobsIn, cutChange, haction] using h
  | some q =>
      by_cases hqi : q = i
      next =>
        subst q
        simpa [JobState.jobsIn, cutChange, haction] using h
      next =>
        simpa [JobState.jobsIn, cutChange, haction, hqi] using h

/-- Exact queue balance along an arbitrary finite token list. -/
theorem converse_runTokens_runAllocationCount_balance {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) :
    ((N.runTokens U x tokens i : Nat) : Real) - (x i : Real) =
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          (N.runAllocationCount U x tokens q j i : Nat)) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (N.runAllocationCount U x tokens i j k : Nat)) := by
  classical
  induction tokens generalizing x with
  | nil => simp [runTokens, runAllocationCount]
  | cons jk rest ih =>
      let xnext := N.queueStep U x jk
      have htail := ih xnext
      have hstep := N.queueStep_coordinate_sub U x jk i
      have hin := N.oneStep_incoming U x jk i
      have hout := N.oneStep_outgoing U x jk i
      simp only [runTokens, runAllocationCount, Nat.cast_add,
        Finset.sum_add_distrib]
      change
        ((N.runTokens U xnext rest i : Nat) : Real) - (x i : Real) = _
      change
        ((N.runTokens U xnext rest i : Nat) : Real) -
            ((xnext i : Nat) : Real) = _ at htail
      change ((xnext i : Nat) : Real) - (x i : Real) = _ at hstep
      rw [show
        ((N.runTokens U xnext rest i : Nat) : Real) - (x i : Real) =
          (((N.runTokens U xnext rest i : Nat) : Real) -
            ((xnext i : Nat) : Real)) +
          (((xnext i : Nat) : Real) - (x i : Real)) by ring]
      rw [htail, hstep, <- hin, <- hout]
      push_cast
      ring

private theorem runAllocationCount_incompatible {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    N.runAllocationCount U x tokens i j k = 0 := by
  induction tokens generalizing x with
  | nil => rfl
  | cons jk rest ih =>
      simp only [runAllocationCount]
      have hne :
          Not (U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k) := by
        rintro ⟨haction, hj, _⟩
        have hlegal := U.legal x jk.1 jk.2
        rw [haction] at hlegal
        exact hij (hj ▸ hlegal.1)
      simp [hne, ih (N.queueStep U x jk)]

theorem sum_runAllocationCount_eq_count_of_no_waste {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (hzero : N.trajectoryWaste U x tokens = 0)
    (j : Server) (k : Buffer) :
    Finset.univ.sum (fun i =>
        N.runAllocationCount U x tokens i j k) =
      tokens.count (j, k) := by
  induction tokens generalizing x with
  | nil => simp [runAllocationCount]
  | cons jk rest ih =>
      have hwaste_nonneg := N.wasteIndicator_nonneg U x jk
      have htail_nonneg :=
        N.trajectoryWaste_nonneg U (N.queueStep U x jk) rest
      have hwaste : N.wasteIndicator U x jk = 0 := by
        simp only [trajectoryWaste] at hzero
        linarith
      have htail :
          N.trajectoryWaste U (N.queueStep U x jk) rest = 0 := by
        simp only [trajectoryWaste] at hzero
        linarith
      have haction : Not (U x jk.1 jk.2 = none) := by
        intro hnone
        simp [wasteIndicator, hnone] at hwaste
      obtain ⟨q, hq⟩ : exists q, U x jk.1 jk.2 = some q := by
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists.mp haction
        exact ⟨q, hq.symm⟩
      rw [show
        Finset.univ.sum (fun i =>
            N.runAllocationCount U x (jk :: rest) i j k) =
          Finset.univ.sum (fun i =>
            (if U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k
              then 1 else 0)) +
          Finset.univ.sum (fun i =>
            N.runAllocationCount U (N.queueStep U x jk) rest i j k) by
              simp only [runAllocationCount, Finset.sum_add_distrib]]
      rw [ih (N.queueStep U x jk) htail]
      by_cases hmatch : jk = (j, k)
      · subst jk
        simp [hq, Nat.add_comm]
      · have hbeq : (jk == (j, k)) = false :=
          beq_eq_false_iff_ne.mpr hmatch
        have hpair : Not (jk.1 = j /\ jk.2 = k) := by
          intro h
          exact hmatch (Prod.ext h.1 h.2)
        simp [List.count_cons, hbeq, hpair]

private noncomputable def converseFallbackBuffer (j : Server) : Buffer :=
  Classical.choose (N.server_has_neighbor j)

private theorem converseFallbackBuffer_compatible (j : Server) :
    N.compatible (N.converseFallbackBuffer j) j :=
  Classical.choose_spec (N.server_has_neighbor j)

private noncomputable def finiteAllocationFraction {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) : Real :=
  let total := Finset.univ.sum (fun k => tokens.count (j, k))
  if total = 0 then
    if i = N.converseFallbackBuffer j then 1 else 0
  else
    (Finset.univ.sum (fun k =>
      N.runAllocationCount U x tokens i j k) : Real) / total

private theorem finiteAllocationFraction_nonneg {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) :
    0 <= N.finiteAllocationFraction U x tokens i j := by
  classical
  let total : Nat := Finset.univ.sum (fun k => tokens.count (j, k))
  by_cases htotal : total = 0
  · by_cases hi : i = N.converseFallbackBuffer j
    · simp [finiteAllocationFraction, total, htotal, hi]
    · simp [finiteAllocationFraction, total, htotal, hi]
  · simp only [finiteAllocationFraction, total, htotal, if_false]
    positivity

private theorem sum_allocations_over_compatible {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) :
    Finset.sum (N.buffersOf j) (fun i =>
        N.runAllocationCount U x tokens i j k) =
      Finset.univ.sum (fun i =>
        N.runAllocationCount U x tokens i j k) := by
  classical
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hnot : Not (N.compatible i j) := by
    simpa using hi
  exact N.runAllocationCount_incompatible U x tokens i j k hnot

private theorem finiteAllocationFraction_sum {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (hzero : N.trajectoryWaste U x tokens = 0)
    (j : Server) :
    Finset.sum (N.buffersOf j) (fun i =>
      N.finiteAllocationFraction U x tokens i j) = 1 := by
  classical
  let total : Nat := Finset.univ.sum (fun k => tokens.count (j, k))
  by_cases htotal : total = 0
  · have hmem : N.converseFallbackBuffer j ∈ N.buffersOf j := by
      exact (N.mem_buffersOf (N.converseFallbackBuffer j) j).2
        (N.converseFallbackBuffer_compatible j)
    simp [finiteAllocationFraction, total, htotal, hmem]
  · have htotal_pos : (0 : Real) < total := by
      exact_mod_cast Nat.pos_of_ne_zero htotal
    rw [show
      Finset.sum (N.buffersOf j) (fun i =>
          N.finiteAllocationFraction U x tokens i j) =
        (Finset.sum (N.buffersOf j) (fun i =>
          Finset.univ.sum (fun k =>
            N.runAllocationCount U x tokens i j k)) : Real) / total by
          simp only [finiteAllocationFraction, total, htotal, if_false,
            Finset.sum_div, Nat.cast_sum]]
    have hswap :
        Finset.sum (N.buffersOf j) (fun i =>
            Finset.univ.sum (fun k =>
              N.runAllocationCount U x tokens i j k)) =
          total := by
      dsimp [total]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [N.sum_allocations_over_compatible U x tokens j k,
        N.sum_runAllocationCount_eq_count_of_no_waste
          U x tokens hzero j k]
    have hswap_real :
        (Finset.sum (N.buffersOf j) (fun i =>
            Finset.univ.sum (fun k =>
              N.runAllocationCount U x tokens i j k)) : Real) =
          (total : Real) := by
      exact_mod_cast hswap
    rw [hswap_real]
    exact div_self htotal_pos.ne'

private theorem finiteDisplacement_mem_noWasteDriftSet {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (hzero : N.trajectoryWaste U x tokens = 0) :
    (fun i =>
        ((N.runTokens U x tokens i : Nat) : Real) - (x i : Real)) ∈
      N.noWasteDriftSet (N.finiteTokenRates tokens) := by
  classical
  let d : Buffer -> Server -> Real :=
    N.finiteAllocationFraction U x tokens
  refine ⟨d, ?_, ?_, ?_⟩
  · intro i j
    exact N.finiteAllocationFraction_nonneg U x tokens i j
  · intro j
    exact N.finiteAllocationFraction_sum U x tokens hzero j
  · intro i
    change
      ((N.runTokens U x tokens i : Nat) : Real) - (x i : Real) =
        (Finset.univ.sum fun j : Server => N.finiteTokenRates tokens j i) -
        (Finset.sum (N.serversOf i) fun j : Server =>
          d i j * Finset.univ.sum (fun k : Buffer =>
            N.finiteTokenRates tokens j k))
    rw [N.converse_runTokens_runAllocationCount_balance U x tokens i]
    dsimp [finiteTokenRates, finiteTokenCounts, d]
    have hin (j : Server) :
        (tokens.count (j, i) : Real) =
          Finset.univ.sum (fun q : Buffer =>
            (N.runAllocationCount U x tokens q j i : Nat)) := by
      exact_mod_cast
        (N.sum_runAllocationCount_eq_count_of_no_waste
          U x tokens hzero j i).symm
    have hout (j : Server) :
        N.finiteAllocationFraction U x tokens i j *
            Finset.univ.sum (fun k => (tokens.count (j, k) : Real)) =
          Finset.univ.sum (fun k =>
            (N.runAllocationCount U x tokens i j k : Nat)) := by
      let total : Nat := Finset.univ.sum (fun k => tokens.count (j, k))
      by_cases htotal : total = 0
      · have hcounts (k : Buffer) : tokens.count (j, k) = 0 := by
          have hk := Finset.single_le_sum
            (fun q _ => Nat.zero_le (tokens.count (j, q)))
            (Finset.mem_univ k)
          dsimp [total] at htotal
          omega
        have halloc (k : Buffer) :
            N.runAllocationCount U x tokens i j k = 0 := by
          have hsum :=
            N.sum_runAllocationCount_eq_count_of_no_waste
              U x tokens hzero j k
          rw [hcounts k] at hsum
          have hle := Finset.single_le_sum
            (fun q _ => Nat.zero_le
              (N.runAllocationCount U x tokens q j k))
            (Finset.mem_univ i)
          omega
        simp [hcounts, halloc]
      · have htotal_real : Not ((total : Real) = 0) := by
          exact_mod_cast htotal
        have htotal_cast :
            Finset.univ.sum (fun k => (tokens.count (j, k) : Real)) =
              (total : Real) := by
          dsimp [total]
          norm_cast
        simp only [finiteAllocationFraction, total, htotal, if_false,
          Nat.cast_sum]
        rw [htotal_cast]
        exact div_mul_cancel₀ _ htotal_real
    simp_rw [hin, hout]
    push_cast
    have hserver :
        Finset.sum (N.serversOf i) (fun j =>
            Finset.univ.sum (fun k =>
              (N.runAllocationCount U x tokens i j k : Real))) =
          Finset.univ.sum (fun j =>
            Finset.univ.sum (fun k =>
              (N.runAllocationCount U x tokens i j k : Real))) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hnot
      have hij : Not (N.compatible i j) := by
        simpa using hnot
      apply Finset.sum_eq_zero
      intro k hk
      simp [N.runAllocationCount_incompatible U x tokens i j k hij]
    rw [hserver]

private theorem vAlphaImage_bddBelow_of_nonneg
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k) :
    BddBelow
      ((fun z =>
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          ((fun i => alpha i) + z)) '' N.noWasteDriftSet f) := by
  classical
  let total : Real := Finset.univ.sum (fun j : Server =>
    Finset.univ.sum (fun k : Buffer => f j k))
  let m : Real := Lyapunov.minCoordinate (fun i => alpha i)
  have htotal : 0 <= total := by
    dsimp [total]
    exact Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun k _ => hf j k))
  have hm : 0 < m := Lyapunov.minCoordinate_pos halpha
  refine ⟨-(total / m), ?_⟩
  intro value hvalue
  obtain ⟨z, hz, rfl⟩ := hvalue
  obtain ⟨d, hd, _hdsum, hz⟩ := hz
  let i0 : Buffer := N.converseFallbackBuffer
    (Classical.choice (inferInstance : Nonempty Server))
  have hout :
      0 <= Finset.sum (N.serversOf i0) (fun j =>
        d i0 j * Finset.univ.sum (fun k => f j k)) := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hd i0 j)
      (Finset.sum_nonneg (fun k hk => hf j k))
  have harrival :
      Finset.univ.sum (fun j : Server => f j i0) <= total := by
    dsimp [total]
    apply Finset.sum_le_sum
    intro j hj
    exact Finset.single_le_sum
      (fun k _ => hf j k) (Finset.mem_univ i0)
  have hzle : z i0 <= total := by
    rw [hz i0]
    linarith
  have hm_le_alpha : m <= alpha i0 :=
    Finset.inf'_le (fun i => alpha i) (Finset.mem_univ i0)
  have hratio : z i0 / alpha i0 <= total / m := by
    calc
      z i0 / alpha i0 <= total / alpha i0 :=
        (div_le_div_iff_of_pos_right (halpha i0)).2 hzle
      _ <= total / m :=
        div_le_div_of_nonneg_left htotal hm hm_le_alpha
  change
    -(total / m) <=
      Lyapunov.LAlphaAmbient (fun i => alpha i)
        ((fun i => alpha i) + z)
  rw [Lyapunov.LAlphaAmbient_centered
    (fun i => alpha i) z (fun i => ne_of_gt (halpha i))]
  calc
    -(total / m) <= -(z i0 / alpha i0) := neg_le_neg hratio
    _ <= -Lyapunov.minCoordinate (fun i => z i / alpha i) :=
      neg_le_neg
        (Finset.inf'_le (fun i => z i / alpha i) (Finset.mem_univ i0))

private theorem vAlpha_le_of_mem
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real)
    {drift : Buffer -> Real} (hdrift : drift ∈ N.noWasteDriftSet f)
    (hbounded :
      BddBelow
        ((fun z =>
          Lyapunov.LAlphaAmbient (fun i => alpha i)
            ((fun i => alpha i) + z)) '' N.noWasteDriftSet f)) :
    PaperStatements.Network.vAlpha (N := N) alpha f <=
      Lyapunov.LAlphaAmbient (fun i => alpha i)
        ((fun i => alpha i) + drift) := by
  unfold PaperStatements.Network.vAlpha
  apply csInf_le hbounded
  exact ⟨drift, hdrift, rfl⟩

private theorem finite_state_LAlpha_le
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {K : Nat} (x y : JobState Buffer K) (C : Real)
    (hx : forall i, (x i : Real) <= C * alpha i) :
    Lyapunov.LAlphaAmbient (fun i => alpha i)
        ((fun i => alpha i) +
          (fun i => (y i : Real) - (x i : Real))) <= C := by
  rw [Lyapunov.LAlphaAmbient_centered
    (fun i => alpha i) (fun i => (y i : Real) - (x i : Real))
    (fun i => ne_of_gt (halpha i))]
  apply neg_le.mp
  apply Finset.le_inf' Finset.univ_nonempty
  intro i hi
  apply (le_div_iff₀ (halpha i)).2
  have hy : (0 : Real) <= y i := by positivity
  calc
    -C * alpha i = -(C * alpha i) := by ring
    _ <= -(x i : Real) := neg_le_neg (hx i)
    _ <= (y i : Real) - (x i : Real) := by linarith

/-- If a finite token block has more policy-independent `vAlpha` displacement
than the initial queue can absorb, at least one token in the block is wasted. -/
theorem exact_counts_force_trajectoryWaste_pos
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (C : Real)
    (hx : forall i, (x i : Real) <= C * alpha i)
    (hforce :
      C < PaperStatements.Network.vAlpha (N := N) alpha
        (N.finiteTokenRates tokens)) :
    0 < N.trajectoryWaste U x tokens := by
  by_contra hnot
  have hnonneg := N.trajectoryWaste_nonneg U x tokens
  have hzero : N.trajectoryWaste U x tokens = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  have hdrift :=
    N.finiteDisplacement_mem_noWasteDriftSet U x tokens hzero
  have hf : forall j k, 0 <= N.finiteTokenRates tokens j k := by
    intro j k
    simp [finiteTokenRates, finiteTokenCounts]
  have hv := N.vAlpha_le_of_mem alpha (N.finiteTokenRates tokens)
    hdrift (N.vAlphaImage_bddBelow_of_nonneg alpha halpha
      (N.finiteTokenRates tokens) hf)
  have hupper :=
    finite_state_LAlpha_le alpha halpha x (N.runTokens U x tokens) C hx
  exact (not_lt_of_ge (hv.trans hupper)) hforce

theorem exact_coordinate_counts_force_trajectoryWaste_pos
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (n : Server -> Buffer -> Nat)
    (C : Real)
    (hx : forall i, (x i : Real) <= C * alpha i)
    (hcounts : forall j k, tokens.count (j, k) = n j k)
    (hforce :
      C < PaperStatements.Network.vAlpha (N := N) alpha
        (fun j k => (n j k : Real))) :
    0 < N.trajectoryWaste U x tokens := by
  have hrates :
      N.finiteTokenRates tokens = (fun j k => (n j k : Real)) := by
    funext j k
    simp [finiteTokenRates, finiteTokenCounts, hcounts]
  apply N.exact_counts_force_trajectoryWaste_pos alpha halpha U x tokens C hx
  rw [hrates]
  exact hforce

theorem exact_coordinate_counts_force_near_alpha
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {K : Nat} (hK : 0 < K)
    (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (n : Server -> Buffer -> Nat)
    (eps : Real) (heps : 0 <= eps)
    (hnear : forall i,
      abs ((x i : Real) / (K : Real) - alpha i) <= eps)
    (hcounts : forall j k, tokens.count (j, k) = n j k)
    (hforce :
      (K : Real) *
          (1 + eps /
            Lyapunov.minCoordinate (fun i => alpha i)) <
        PaperStatements.Network.vAlpha (N := N) alpha
          (fun j k => (n j k : Real))) :
    0 < N.trajectoryWaste U x tokens := by
  let m : Real := Lyapunov.minCoordinate (fun i => alpha i)
  have hm : 0 < m := Lyapunov.minCoordinate_pos halpha
  have hKreal : (0 : Real) < K := by exact_mod_cast hK
  apply N.exact_coordinate_counts_force_trajectoryWaste_pos
    alpha halpha U x tokens n
      ((K : Real) * (1 + eps / m))
  · intro i
    have hupper :
        (x i : Real) / (K : Real) <= alpha i + eps := by
      have habs :
          (x i : Real) / (K : Real) - alpha i <=
            abs ((x i : Real) / (K : Real) - alpha i) :=
        le_abs_self _
      linarith [hnear i]
    have hscaled :
        (x i : Real) <= (alpha i + eps) * (K : Real) :=
      (div_le_iff₀ hKreal).1 hupper
    have hm_le_alpha : m <= alpha i :=
      Finset.inf'_le (fun q => alpha q) (Finset.mem_univ i)
    have heps_ratio : eps <= eps * alpha i / m := by
      apply (le_div_iff₀ hm).2
      exact mul_le_mul_of_nonneg_left hm_le_alpha heps
    calc
      (x i : Real) <= (alpha i + eps) * (K : Real) := hscaled
      _ <= (alpha i + eps * alpha i / m) * (K : Real) := by
        exact mul_le_mul_of_nonneg_right
          (by linarith [heps_ratio]) hKreal.le
      _ = ((K : Real) * (1 + eps / m)) * alpha i := by ring
  · exact hcounts
  · simpa only [m] using hforce

/-! ## Exact count-event mass and stationary loss -/

def totalFiniteCount (_N : Network Buffer Server)
    (n : Server -> Buffer -> Nat) : Nat :=
  Finset.univ.sum (fun j => Finset.univ.sum (fun k => n j k))

def tokenVectorHasCounts
    (n : Server -> Buffer -> Nat)
    (tokens : Fin (N.totalFiniteCount n) ->
      TokenType (Buffer := Buffer) (Server := Server)) : Prop :=
  forall j k, (List.ofFn tokens).count (j, k) = n j k

noncomputable def exactCountVectorMass
    (n : Server -> Buffer -> Nat) : Real := by
  classical
  exact Finset.univ.sum (fun tokens : Fin (N.totalFiniteCount n) ->
    TokenType (Buffer := Buffer) (Server := Server) =>
      if N.tokenVectorHasCounts n tokens then
        (N.tokenVectorLaw (N.totalFiniteCount n) tokens).toReal
      else 0)

private theorem trajectoryWaste_one_le_of_pos {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (hpos : 0 < N.trajectoryWaste U x tokens) :
    1 <= N.trajectoryWaste U x tokens := by
  induction tokens generalizing x with
  | nil => simp [trajectoryWaste] at hpos
  | cons jk rest ih =>
      by_cases hwaste : U x jk.1 jk.2 = none
      next =>
        simp only [trajectoryWaste, wasteIndicator, if_pos hwaste]
        linarith [N.trajectoryWaste_nonneg
          (U := U) (N.queueStep U x jk) rest]
      next =>
        simp only [trajectoryWaste, wasteIndicator, if_neg hwaste,
          zero_add] at hpos
        simp only [trajectoryWaste, wasteIndicator, if_neg hwaste,
          zero_add]
        exact ih (N.queueStep U x jk) hpos

private theorem expectedTrajectoryWasteFrom_nonneg {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (m : Nat) :
    0 <= N.expectedTrajectoryWasteFrom U x m := by
  unfold expectedTrajectoryWasteFrom
  apply Finset.sum_nonneg
  intro tokens htokens
  exact mul_nonneg ENNReal.toReal_nonneg
    (N.trajectoryWaste_nonneg U x (List.ofFn tokens))

theorem exactCountVectorMass_le_expectedTrajectoryWasteFrom
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (n : Server -> Buffer -> Nat)
    (hforce : forall tokens,
      N.tokenVectorHasCounts n tokens ->
        0 < N.trajectoryWaste U x (List.ofFn tokens)) :
    N.exactCountVectorMass n <=
      N.expectedTrajectoryWasteFrom U x (N.totalFiniteCount n) := by
  unfold exactCountVectorMass expectedTrajectoryWasteFrom
  apply Finset.sum_le_sum
  intro tokens htokens
  by_cases hcounts : N.tokenVectorHasCounts n tokens
  next =>
    rw [if_pos hcounts]
    calc
      (N.tokenVectorLaw (N.totalFiniteCount n) tokens).toReal =
          (N.tokenVectorLaw (N.totalFiniteCount n) tokens).toReal * 1 := by
        ring
      _ <= (N.tokenVectorLaw (N.totalFiniteCount n) tokens).toReal *
          N.trajectoryWaste U x (List.ofFn tokens) :=
        mul_le_mul_of_nonneg_left
          (N.trajectoryWaste_one_le_of_pos U x
            (List.ofFn tokens) (hforce tokens hcounts))
          ENNReal.toReal_nonneg
  next =>
    rw [if_neg hcounts]
    exact mul_nonneg ENNReal.toReal_nonneg
      (N.trajectoryWaste_nonneg U x (List.ofFn tokens))

theorem stationaryMass_mul_exactCountVectorMass_le_minimumInvariantLoss
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (n : Server -> Buffer -> Nat)
    (hforce : forall tokens,
      N.tokenVectorHasCounts n tokens ->
        0 < N.trajectoryWaste U x (List.ofFn tokens)) :
    (N.minimumInvariantPMF U x).toReal *
        N.exactCountVectorMass n <=
      (N.totalFiniteCount n : Real) * N.minimumInvariantLoss U := by
  let pi := N.minimumInvariantPMF U
  let m := N.totalFiniteCount n
  have hmass :=
    N.exactCountVectorMass_le_expectedTrajectoryWasteFrom U x n hforce
  have hweighted :
      (pi x).toReal * N.exactCountVectorMass n <=
        (pi x).toReal * N.expectedTrajectoryWasteFrom U x m :=
    mul_le_mul_of_nonneg_left hmass ENNReal.toReal_nonneg
  have hterm :
      (pi x).toReal * N.expectedTrajectoryWasteFrom U x m <=
        N.expectedTrajectoryWaste U pi m := by
    unfold expectedTrajectoryWaste
    simpa using
      (Finset.single_le_sum
        (s := Finset.univ)
        (fun y _ => mul_nonneg ENNReal.toReal_nonneg
          (N.expectedTrajectoryWasteFrom_nonneg U y m))
        (Finset.mem_univ x))
  calc
    (N.minimumInvariantPMF U x).toReal *
        N.exactCountVectorMass n =
        (pi x).toReal * N.exactCountVectorMass n := rfl
    _ <= (pi x).toReal * N.expectedTrajectoryWasteFrom U x m :=
      hweighted
    _ <= N.expectedTrajectoryWaste U pi m := hterm
    _ = (m : Real) * N.stationaryOneStepWaste U pi := by
      exact N.expectedTrajectoryWaste_eq_mul_stationary_of_invariant
        U pi (N.minimumInvariantPMF_isInvariant U) m
    _ = (N.totalFiniteCount n : Real) * N.minimumInvariantLoss U := by
      rw [N.minimumInvariantLoss_eq_stationaryOneStepWaste U]

theorem forcedCountMass_near_alpha_le_minimumInvariantLoss
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {K : Nat} (hK : 0 < K)
    (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K)
    (n : Server -> Buffer -> Nat)
    (eps : Real) (heps : 0 <= eps)
    (hnear : forall i,
      abs ((x i : Real) / (K : Real) - alpha i) <= eps)
    (hforce :
      (K : Real) *
          (1 + eps /
            Lyapunov.minCoordinate (fun i => alpha i)) <
        PaperStatements.Network.vAlpha (N := N) alpha
          (fun j k => (n j k : Real))) :
    (N.minimumInvariantPMF U x).toReal * N.exactCountVectorMass n <=
      (N.totalFiniteCount n : Real) * N.minimumInvariantLoss U := by
  apply N.stationaryMass_mul_exactCountVectorMass_le_minimumInvariantLoss
  intro tokens hcounts
  exact N.exact_coordinate_counts_force_near_alpha
    alpha halpha hK U x (List.ofFn tokens) n eps heps hnear hcounts hforce

theorem poissonSingleton_mul_stationaryMass_le_minimumInvariantLoss
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (n : Server -> Buffer -> Nat)
    (T : NNReal)
    (hcountBridge :
      (poissonCountLaw N K T).real {n} <= N.exactCountVectorMass n)
    (hforce : forall tokens,
      N.tokenVectorHasCounts n tokens ->
        0 < N.trajectoryWaste U x (List.ofFn tokens)) :
    (N.minimumInvariantPMF U x).toReal *
        (poissonCountLaw N K T).real {n} <=
      (N.totalFiniteCount n : Real) * N.minimumInvariantLoss U := by
  calc
    (N.minimumInvariantPMF U x).toReal *
        (poissonCountLaw N K T).real {n} <=
        (N.minimumInvariantPMF U x).toReal *
          N.exactCountVectorMass n :=
      mul_le_mul_of_nonneg_left hcountBridge ENNReal.toReal_nonneg
    _ <= (N.totalFiniteCount n : Real) * N.minimumInvariantLoss U :=
      N.stationaryMass_mul_exactCountVectorMass_le_minimumInvariantLoss
        U x n hforce

/-! ## Poisson count atoms versus IID token blocks -/

private theorem prod_X_eq_monomial_ofFn
    {alpha : Type*} [DecidableEq alpha] (m : Nat)
    (f : Fin m -> alpha) :
    (Finset.univ.prod (fun i =>
      MvPolynomial.X (R := Nat) (f i))) =
      MvPolynomial.monomial
        (Multiset.toFinsupp (List.ofFn f : Multiset alpha)) 1 := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      rw [Fin.prod_univ_succ, List.ofFn_succ]
      rw [ih (fun i => f i.succ)]
      rw [MvPolynomial.X, MvPolynomial.monomial_mul]
      have h :
          Finsupp.single (f 0) 1 +
              Multiset.toFinsupp
                (List.ofFn (fun i => f i.succ) : Multiset alpha) =
            Multiset.toFinsupp
              (f 0 :: List.ofFn (fun i => f i.succ) : Multiset alpha) := by
        ext a
        by_cases ha : f 0 = a
        · subst a
          simp [Multiset.toFinsupp_apply, Nat.add_comm]
        · simp [Multiset.toFinsupp_apply, ha, Ne.symm ha]
      rw [h]
      simp

private theorem countFiber_card_eq_countPerms
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (m : Multiset alpha) :
    ((Finset.univ : Finset (Fin m.card -> alpha)).filter
        (fun f => (List.ofFn f : Multiset alpha) = m)).card =
      m.countPerms := by
  let q := Multiset.toFinsupp m
  let P : MvPolynomial alpha Nat :=
    (Finset.univ.sum fun a => MvPolynomial.X a) ^ m.card
  have hqsum : q.sum (fun _ c => c) = m.card := by
    exact Multiset.toFinsupp_sum_eq m
  have hcoeff : MvPolynomial.coeff q P = m.countPerms := by
    change MvPolynomial.coeff q
      ((Finset.univ.sum fun a => MvPolynomial.X a) ^ m.card) =
        m.countPerms
    have h :=
      MvPolynomial.coeff_linearCombination_X_pow_of_fintype
        (R := Nat) (fun _ : alpha => 1) q m.card
    simp only [one_smul] at h
    rw [h, if_pos hqsum]
    simp [Multiset.countPerms, q]
  have hcoeff' :
      MvPolynomial.coeff q P =
        Finset.univ.sum (fun f : Fin m.card -> alpha =>
          if (List.ofFn f : Multiset alpha) = m then 1 else 0) := by
    change MvPolynomial.coeff q
      ((Finset.univ.sum fun a => MvPolynomial.X a) ^ m.card) = _
    rw [Finset.sum_pow' Finset.univ
      (fun a : alpha => MvPolynomial.X (R := Nat) a) m.card]
    simp only [Fintype.piFinset_univ, MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro f hf
    rw [prod_X_eq_monomial_ofFn, MvPolynomial.coeff_monomial]
    have heq :
        Multiset.toFinsupp (List.ofFn f : Multiset alpha) = q <->
          (List.ofFn f : Multiset alpha) = m := by
      dsimp only [q]
      constructor
      · intro h
        exact Multiset.toFinsupp.injective h
      · intro h
        rw [h]
    by_cases hm : (List.ofFn f : Multiset alpha) = m
    · rw [if_pos (heq.mpr hm), if_pos hm]
    · have hq :
          Not (Multiset.toFinsupp (List.ofFn f : Multiset alpha) = q) :=
        fun h => hm (heq.mp h)
      rw [if_neg hq, if_neg hm]
  rw [hcoeff] at hcoeff'
  rw [hcoeff']
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

private theorem countFiber_card_eq_countPerms_of_card
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (m : Multiset alpha) (L : Nat) (hcard : m.card = L) :
    ((Finset.univ : Finset (Fin L -> alpha)).filter
        (fun f => (List.ofFn f : Multiset alpha) = m)).card =
      m.countPerms := by
  subst L
  exact countFiber_card_eq_countPerms m

private noncomputable def countMultiset
    (_N : Network Buffer Server) (n : Server -> Buffer -> Nat) :
    Multiset (TokenType (Buffer := Buffer) (Server := Server)) :=
  Finsupp.toMultiset
    (Finsupp.equivFunOnFinite.symm (fun jk => n jk.1 jk.2))

private theorem countMultiset_card
    (n : Server -> Buffer -> Nat) :
    (N.countMultiset n).card = N.totalFiniteCount n := by
  classical
  rw [Network.countMultiset, Finsupp.card_toMultiset,
    Finsupp.sum_fintype]
  · rw [Fintype.sum_prod_type]
    rfl
  · intro
    rfl

private theorem countMultiset_count
    (n : Server -> Buffer -> Nat)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    (N.countMultiset n).count jk = n jk.1 jk.2 := by
  classical
  change Multiset.toFinsupp (N.countMultiset n) jk = _
  rw [Network.countMultiset, Finsupp.toMultiset_toFinsupp]
  rfl

private theorem list_count_eq_multiset_count
    (l : List (TokenType (Buffer := Buffer) (Server := Server)))
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    l.count jk = (l : Multiset
      (TokenType (Buffer := Buffer) (Server := Server))).count jk := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : a = jk
      · subst a
        simp [ih]
      · simp [ih, h]

private theorem tokenVectorHasCounts_iff_multiset_eq
    (n : Server -> Buffer -> Nat)
    (tokens : Fin (N.totalFiniteCount n) ->
      TokenType (Buffer := Buffer) (Server := Server)) :
    N.tokenVectorHasCounts n tokens <->
      (List.ofFn tokens : Multiset
        (TokenType (Buffer := Buffer) (Server := Server))) =
        N.countMultiset n := by
  classical
  constructor
  · intro h
    ext jk
    rw [<- list_count_eq_multiset_count, N.countMultiset_count n jk]
    exact h jk.1 jk.2
  · intro h j k
    have hc := congrArg (fun m : Multiset
        (TokenType (Buffer := Buffer) (Server := Server)) =>
          m.count (j, k)) h
    rw [<- list_count_eq_multiset_count] at hc
    simpa only [N.countMultiset_count n (j, k)] using hc

private theorem token_probability_prod_of_counts
    (n : Server -> Buffer -> Nat)
    (tokens : Fin (N.totalFiniteCount n) ->
      TokenType (Buffer := Buffer) (Server := Server))
    (hcounts : N.tokenVectorHasCounts n tokens) :
    Finset.univ.prod (fun r => N.phi (tokens r).1 (tokens r).2) =
      Finset.univ.prod (fun jk :
        TokenType (Buffer := Buffer) (Server := Server) =>
          N.phi jk.1 jk.2 ^ n jk.1 jk.2) := by
  classical
  have hm := (N.tokenVectorHasCounts_iff_multiset_eq n tokens).mp hcounts
  rw [<- List.prod_ofFn]
  rw [List.ofFn_comp' tokens (fun jk => N.phi jk.1 jk.2)]
  change
    (((List.ofFn tokens : List
      (TokenType (Buffer := Buffer) (Server := Server))) : Multiset
        (TokenType (Buffer := Buffer) (Server := Server))).map
          (fun jk => N.phi jk.1 jk.2)).prod = _
  rw [hm, Finset.prod_multiset_map_count]
  simp_rw [N.countMultiset_count n]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro jk hjk hnot
  have hz : n jk.1 jk.2 = 0 := by
    rw [<- N.countMultiset_count n jk]
    exact Multiset.count_eq_zero.mpr (by simpa using hnot)
  simp [hz]

theorem exactCountVectorMass_eq_multinomial
    (n : Server -> Buffer -> Nat) :
    N.exactCountVectorMass n =
      (N.countMultiset n).countPerms *
        Finset.univ.prod (fun jk :
          TokenType (Buffer := Buffer) (Server := Server) =>
            N.phi jk.1 jk.2 ^ n jk.1 jk.2) := by
  classical
  let c : Real :=
    Finset.univ.prod (fun jk :
      TokenType (Buffer := Buffer) (Server := Server) =>
        N.phi jk.1 jk.2 ^ n jk.1 jk.2)
  unfold exactCountVectorMass
  simp only [N.tokenVectorLaw_apply_toReal, N.tokenLaw_toReal]
  calc
    Finset.univ.sum (fun tokens :
        Fin (N.totalFiniteCount n) ->
          TokenType (Buffer := Buffer) (Server := Server) =>
      if N.tokenVectorHasCounts n tokens then
        Finset.univ.prod (fun r =>
          N.phi (tokens r).1 (tokens r).2)
      else 0) =
        Finset.univ.sum (fun tokens :
          Fin (N.totalFiniteCount n) ->
            TokenType (Buffer := Buffer) (Server := Server) =>
          if N.tokenVectorHasCounts n tokens then c else 0) := by
      apply Finset.sum_congr rfl
      intro tokens htokens
      split_ifs with hcounts
      · exact N.token_probability_prod_of_counts n tokens hcounts
      · rfl
    _ = (((Finset.univ.filter fun tokens :
          Fin (N.totalFiniteCount n) ->
            TokenType (Buffer := Buffer) (Server := Server) =>
          N.tokenVectorHasCounts n tokens).card : Nat) : Real) * c := by
      rw [<- Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ = (N.countMultiset n).countPerms * c := by
      congr 1
      exact_mod_cast (by
        simpa only [N.tokenVectorHasCounts_iff_multiset_eq n] using
          countFiber_card_eq_countPerms_of_card
            (N.countMultiset n) (N.totalFiniteCount n)
            (N.countMultiset_card n))
    _ = (N.countMultiset n).countPerms *
        Finset.univ.prod (fun jk :
          TokenType (Buffer := Buffer) (Server := Server) =>
            N.phi jk.1 jk.2 ^ n jk.1 jk.2) := rfl

private theorem countPerms_mul_prod_factorial
    (n : Server -> Buffer -> Nat) :
    (N.countMultiset n).countPerms *
        Finset.univ.prod (fun jk :
          TokenType (Buffer := Buffer) (Server := Server) =>
            Nat.factorial (n jk.1 jk.2)) =
      Nat.factorial (N.totalFiniteCount n) := by
  classical
  let c : TokenType (Buffer := Buffer) (Server := Server) -> Nat :=
    fun jk => n jk.1 jk.2
  have hmulti :
      Nat.multinomial Finset.univ c = (N.countMultiset n).countPerms := by
    calc
      Nat.multinomial Finset.univ c =
          Nat.multinomial Finset.univ
            (Multiset.toFinsupp (N.countMultiset n)) := by
        apply Nat.multinomial_congr
        intro jk hjk
        exact (N.countMultiset_count n jk).symm
      _ = (Multiset.toFinsupp (N.countMultiset n)).multinomial :=
        Finsupp.multinomial_of_support_subset (Finset.subset_univ _)
      _ = (N.countMultiset n).countPerms := rfl
  have hspec := Nat.multinomial_spec (Finset.univ :
    Finset (TokenType (Buffer := Buffer) (Server := Server))) c
  rw [hmulti] at hspec
  simpa [c, mul_comm, totalFiniteCount, Fintype.sum_prod_type] using
    hspec

private theorem countMultiset_count_sum
    (n : Server -> Buffer -> Nat) :
    Finset.univ.sum (fun jk :
        TokenType (Buffer := Buffer) (Server := Server) =>
          n jk.1 jk.2) = N.totalFiniteCount n := by
  rw [Fintype.sum_prod_type]
  rfl

private theorem poissonCountAtomReal_factorization
    (K : Nat) (T : NNReal) (n : Server -> Buffer -> Nat) :
    poissonCountAtomReal N K (T : Real) n =
      (ProbabilityTheory.poissonMeasure ((K : NNReal) * T)).real
          {N.totalFiniteCount n} *
        N.exactCountVectorMass n := by
  classical
  let lambda : Real := (K : Real) * (T : Real)
  let qprod : Real := Finset.univ.prod (fun jk :
    TokenType (Buffer := Buffer) (Server := Server) =>
      N.phi jk.1 jk.2 ^ n jk.1 jk.2)
  let fprod : Nat := Finset.univ.prod (fun jk :
    TokenType (Buffer := Buffer) (Server := Server) =>
      (n jk.1 jk.2).factorial)
  have hexp :
      Finset.univ.prod (fun jk :
          TokenType (Buffer := Buffer) (Server := Server) =>
        Real.exp (-(lambda * N.phi jk.1 jk.2))) =
        Real.exp (-lambda) := by
    rw [<- Real.exp_sum]
    congr 1
    calc
      Finset.univ.sum (fun jk :
          TokenType (Buffer := Buffer) (Server := Server) =>
            -(lambda * N.phi jk.1 jk.2)) =
          -lambda * Finset.univ.sum (fun jk :
            TokenType (Buffer := Buffer) (Server := Server) =>
              N.phi jk.1 jk.2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro jk hjk
        ring
      _ = -lambda := by
        rw [Fintype.sum_prod_type, N.total_rate]
        ring
  have hpow :
      Finset.univ.prod (fun jk :
          TokenType (Buffer := Buffer) (Server := Server) =>
        (lambda * N.phi jk.1 jk.2) ^ n jk.1 jk.2) =
        lambda ^ N.totalFiniteCount n * qprod := by
    simp only [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      N.countMultiset_count_sum n]
  have hfactorial_real :
      ((N.countMultiset n).countPerms : Real) * (fprod : Real) =
        ((N.totalFiniteCount n).factorial : Real) := by
    exact_mod_cast N.countPerms_mul_prod_factorial n
  rw [N.exactCountVectorMass_eq_multinomial n]
  rw [ProbabilityTheory.poissonMeasure_real_singleton]
  unfold poissonCountAtomReal poissonAtomReal
  rw [<- Fintype.prod_prod_type']
  change
    Finset.univ.prod (fun jk :
      TokenType (Buffer := Buffer) (Server := Server) =>
        Real.exp (-(lambda * N.phi jk.1 jk.2)) *
          (lambda * N.phi jk.1 jk.2) ^ n jk.1 jk.2 /
            (n jk.1 jk.2).factorial) =
      (Real.exp (-lambda) * lambda ^ N.totalFiniteCount n /
          (N.totalFiniteCount n).factorial) *
        ((N.countMultiset n).countPerms * qprod)
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, hexp, hpow]
  have hfprod_real :
      Finset.univ.prod (fun jk :
          TokenType (Buffer := Buffer) (Server := Server) =>
        ((n jk.1 jk.2).factorial : Real)) = (fprod : Real) := by
    exact_mod_cast rfl
  rw [hfprod_real]
  change
    Real.exp (-lambda) * (lambda ^ N.totalFiniteCount n * qprod) /
        (fprod : Real) =
      (Real.exp (-lambda) * lambda ^ N.totalFiniteCount n /
          ((N.totalFiniteCount n).factorial : Real)) *
        (((N.countMultiset n).countPerms : Real) * qprod)
  have hfprod : Ne (fprod : Real) 0 := by positivity
  have htotalfac :
      Ne ((N.totalFiniteCount n).factorial : Real) 0 := by positivity
  field_simp [hfprod, htotalfac]
  rw [<- hfactorial_real]
  ring

/-- Independent coordinate Poisson counts have no more mass than the IID
token block with the same coordinate counts: the omitted factor is the
probability of the corresponding total Poisson count. -/
theorem poissonCountLaw_real_singleton_le_exactCountVectorMass
    (K : Nat) (T : NNReal) (n : Server -> Buffer -> Nat) :
    (poissonCountLaw N K T).real {n} <=
      N.exactCountVectorMass n := by
  rw [poissonCountLaw_real_singleton,
    N.poissonCountAtomReal_factorization K T n]
  have htotal :
      (ProbabilityTheory.poissonMeasure ((K : NNReal) * T)).real
          {N.totalFiniteCount n} <= 1 :=
    MeasureTheory.measureReal_le_one
  have hmass : 0 <= N.exactCountVectorMass n := by
    unfold exactCountVectorMass
    apply Finset.sum_nonneg
    intro tokens htokens
    split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl
  exact mul_le_of_le_one_left hmass htotal

end Network
end StateDepMOR

namespace StateDepMOR
namespace ConverseAsymptotics

/-! ## Subsequential logarithmic bounds -/

noncomputable def scaledLogLoss (loss : PNat -> Real) (K : PNat) : EReal :=
  ENNReal.log (ENNReal.ofReal (loss K)) /
    ((((K : Nat) : Real)) : EReal)

theorem negativeLiminfLogRate_eq_neg_liminf_scaledLogLoss
    (loss : PNat -> Real) :
    PaperStatements.negativeLiminfLogRate loss =
      -liminf (scaledLogLoss loss) atTop :=
  rfl

theorem scaledLogLoss_eq_coe_of_pos
    (loss : PNat -> Real) (K : PNat) (hloss : 0 < loss K) :
    scaledLogLoss loss K =
      ((Real.log (loss K) / ((K : Nat) : Real) : Real) : EReal) := by
  rw [scaledLogLoss, ENNReal.log_ofReal_of_pos hloss, <- EReal.coe_div]

/-- A lower bound along a sequence realizing the original liminf controls
that original `-liminf`, not merely the selected subsequence's rate. -/
theorem negativeLiminfLogRate_le_of_realizing_lower_bound
    (loss : PNat -> Real) (lower : Nat -> Real)
    (K : Nat -> PNat) (cost : Real)
    (hrealize :
      Tendsto (fun r => scaledLogLoss loss (K r)) atTop
        (nhds (liminf (scaledLogLoss loss) atTop)))
    (hlower : Filter.Eventually (fun r => 0 < lower r) atTop)
    (hbound :
      Filter.Eventually (fun r => lower r <= loss (K r)) atTop)
    (hcost :
      Tendsto
        (fun r => -Real.log (lower r) / ((K r : Nat) : Real))
        atTop (nhds cost)) :
    PaperStatements.negativeLiminfLogRate loss <= (cost : EReal) := by
  have hloss :
      Filter.Eventually (fun r => 0 < loss (K r)) atTop := by
    filter_upwards [hlower, hbound] with r hlower_r hbound_r
    exact hlower_r.trans_le hbound_r
  have hleft :
      Tendsto
        (fun r =>
          ((Real.log (lower r) / ((K r : Nat) : Real) : Real) : EReal))
        atTop (nhds ((-cost : Real) : EReal)) := by
    have hneg :
        Tendsto
          (fun r => Real.log (lower r) / ((K r : Nat) : Real))
          atTop (nhds (-cost)) := by
      convert hcost.neg using 1
      funext r
      ring
    exact (continuous_coe_real_ereal.tendsto (-cost)).comp hneg
  have hle :
      Filter.Eventually
        (fun r =>
          ((Real.log (lower r) / ((K r : Nat) : Real) : Real) : EReal) <=
            scaledLogLoss loss (K r))
        atTop := by
    filter_upwards [hlower, hbound, hloss] with
      r hlower_r hbound_r hloss_r
    rw [scaledLogLoss_eq_coe_of_pos loss (K r) hloss_r,
      EReal.coe_le_coe_iff]
    apply div_le_div_of_nonneg_right
    next => exact Real.log_le_log hlower_r hbound_r
    next => exact_mod_cast (K r).pos.le
  have hlim :
      ((-cost : Real) : EReal) <=
        liminf (scaledLogLoss loss) atTop :=
    le_of_tendsto_of_tendsto hleft hrealize hle
  rw [negativeLiminfLogRate_eq_neg_liminf_scaledLogLoss]
  have hneg := EReal.neg_le_neg_iff.mpr hlim
  simpa using hneg

theorem tendsto_log_pnat_pow_div (degree : Nat) :
    Tendsto
      (fun K : PNat =>
        Real.log ((((K : Nat) : Real) ^ degree)) /
          (((K : Nat) : Real)))
      atTop (nhds 0) := by
  convert
    ((tendsto_const_nhds :
        Tendsto (fun _ : PNat => (degree : Real)) atTop
          (nhds (degree : Real))).mul
      StateDepMOR.tendsto_log_pnat_div) using 1
  next =>
    funext K
    rw [Real.log_pow]
    ring
  next => simp

noncomputable def roundedPoissonCount
    {Buffer Server : Type*} (T : NNReal)
    (f : Server -> Buffer -> Real) (K : Nat) :
    Server -> Buffer -> Nat :=
  fun j k => Nat.floor ((T : Real) * f j k * K)

theorem roundedPoissonCount_zero
    {Buffer Server : Type*} (T : NNReal)
    (f : Server -> Buffer -> Real) (j : Server) (k : Buffer)
    (hf : f j k = 0) :
    roundedPoissonCount T f K j k = 0 := by
  simp [roundedPoissonCount, hf]

theorem roundedPoissonCount_ratio_tendsto
    {Buffer Server : Type*} (T : NNReal)
    (f : Server -> Buffer -> Real) (hf : forall j k, 0 <= f j k)
    (j : Server) (k : Buffer) :
    Tendsto
      (fun K : Nat => (roundedPoissonCount T f K j k : Real) / K)
      atTop (nhds ((T : Real) * f j k)) := by
  have h :=
    (tendsto_nat_floor_mul_div_atTop
      (R := Real) (mul_nonneg T.coe_nonneg (hf j k))).comp
      (tendsto_natCast_atTop_atTop (R := Real))
  change Tendsto
    (fun K : Nat =>
      ((Nat.floor ((T : Real) * f j k * K) : Nat) : Real) / K)
    atTop (nhds ((T : Real) * f j k))
  convert h using 1
  funext K
  rfl

theorem poissonCountLaw_log_asymptotic_pnat
    {Buffer Server : Type*} [Fintype Buffer] [Fintype Server]
    (N : Network Buffer Server) (T : NNReal) (hT : 0 < T)
    (f : Server -> Buffer -> Real)
    (n : Nat -> Server -> Buffer -> Nat)
    (hzero : forall j k, N.phi j k = 0 -> forall K, n K j k = 0)
    (hn : forall j k,
      Tendsto (fun K => (n K j k : Real) / K)
        atTop (nhds ((T : Real) * f j k))) :
    Tendsto
      (fun K : PNat =>
        -Real.log ((poissonCountLaw N K T).real {n K}) /
          (((K : Nat) : Real)))
      atTop
      (nhds ((T : Real) *
        Finset.univ.sum (fun j =>
          Finset.univ.sum (fun k =>
            poissonCostReal (N.phi j k) (f j k))))) := by
  exact (poissonCountLaw_log_asymptotic N T hT f n hzero hn).comp
    tendsto_PNat_val_atTop_atTop

theorem localRate_eq_ofReal_sum_poissonCostReal
    {Buffer Server : Type*} [Fintype Buffer] [Fintype Server]
    (N : Network Buffer Server) (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (hzero : forall j k, N.phi j k = 0 -> f j k = 0) :
    N.localRate f =
      ENNReal.ofReal
        (Finset.univ.sum (fun j =>
          Finset.univ.sum (fun k =>
            poissonCostReal (N.phi j k) (f j k)))) := by
  classical
  have hcost : forall j k,
      0 <= poissonCostReal (N.phi j k) (f j k) := by
    intro j k
    rcases (N.phi_nonneg j k).eq_or_lt with hphi_zero | hphi_pos
    next =>
      rw [<- hphi_zero, hzero j k hphi_zero.symm]
      simp [poissonCostReal]
    next => exact poissonCostReal_nonneg hphi_pos (hf j k)
  rw [Network.localRate, ENNReal.ofReal_sum_of_nonneg]
  next =>
    apply Finset.sum_congr rfl
    intro j hj
    rw [ENNReal.ofReal_sum_of_nonneg]
    next =>
      apply Finset.sum_congr rfl
      intro k hk
      rcases (N.phi_nonneg j k).eq_or_lt with hphi_zero | hphi_pos
      next =>
        rw [<- hphi_zero, hzero j k hphi_zero.symm]
        simp [poissonCostReal]
      next => exact poissonCost_of_nominal_pos hphi_pos (hf j k)
    next => exact fun k hk => hcost j k
  next => exact fun j hj => Finset.sum_nonneg fun k hk => hcost j k

theorem poissonCost_horizon_eq_localRate_div
    {Buffer Server : Type*} [Fintype Buffer] [Fintype Server]
    (N : Network Buffer Server) (T : NNReal)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (hsupport : forall j k, N.phi j k = 0 -> f j k = 0)
    (v : Real) (hT : (T : Real) = 1 / v) :
    ((((T : Real) *
          Finset.univ.sum (fun j =>
            Finset.univ.sum (fun k =>
              poissonCostReal (N.phi j k) (f j k)))) : Real) : EReal) =
      (N.localRate f : EReal) / (v : EReal) := by
  classical
  let c : Real :=
    Finset.univ.sum (fun j =>
      Finset.univ.sum (fun k =>
        poissonCostReal (N.phi j k) (f j k)))
  have hc : 0 <= c := by
    dsimp [c]
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro k hk
    rcases (N.phi_nonneg j k).eq_or_lt with hphi_zero | hphi_pos
    next =>
      rw [<- hphi_zero, hsupport j k hphi_zero.symm]
      simp [poissonCostReal]
    next => exact poissonCostReal_nonneg hphi_pos (hf j k)
  have hlocal := localRate_eq_ofReal_sum_poissonCostReal
    N f hf hsupport
  change (((T : Real) * c : Real) : EReal) =
    (N.localRate f : EReal) / (v : EReal)
  rw [hlocal, EReal.coe_ennreal_ofReal, max_eq_left hc, <- EReal.coe_div]
  rw [hT]
  congr 1
  ring

end ConverseAsymptotics
end StateDepMOR

namespace StateDepMOR
namespace PaperStatements
namespace Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

omit [DecidableEq Buffer] [DecidableEq Server] [Nonempty Server] in
theorem gammaCB_nonnegative
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (_halpha : alpha.IsInterior) :
    0 <= gammaCB (N := N) alpha := by
  classical
  unfold gammaCB
  let candidates : Set EReal :=
    {q : EReal |
      exists f : Server -> Buffer -> Real,
        IsNonnegativeRate f /\
        0 < vAlpha (N := N) alpha f /\
        q = (N.localRate f : EReal) /
          (vAlpha (N := N) alpha f : EReal)}
  change 0 <= sInf candidates
  apply le_sInf
  intro q hq
  change
    exists f : Server -> Buffer -> Real,
      IsNonnegativeRate f /\
      0 < vAlpha (N := N) alpha f /\
      q = (N.localRate f : EReal) /
        (vAlpha (N := N) alpha f : EReal) at hq
  let f := Classical.choose hq
  have hfq := Classical.choose_spec hq
  rw [hfq.2.2]
  exact EReal.div_nonneg (by positivity)
    (EReal.coe_nonneg.2 hfq.2.1.le)

omit [DecidableEq Buffer] [DecidableEq Server] [Nonempty Server] in
theorem gammaCBSup_nonnegative
    (N : StateDepMOR.Network Buffer Server) :
    0 <= gammaCBSup (N := N) := by
  classical
  unfold gammaCBSup
  have hbounded :
      BddAbove {q : EReal | exists alpha : Simplex Buffer,
        alpha.IsInterior /\ q = gammaCB (N := N) alpha} :=
    Exists.intro Top.top (fun _ _ => le_top)
  have hmem :
      {q : EReal | exists alpha : Simplex Buffer,
        alpha.IsInterior /\ q = gammaCB (N := N) alpha}
          (gammaCB (N := N) Simplex.uniform) :=
    Exists.intro Simplex.uniform
      (And.intro Simplex.uniform_isInterior (Eq.refl _))
  exact
    (gammaCB_nonnegative N Simplex.uniform Simplex.uniform_isInterior).trans
      (le_csSup hbounded hmem)

end Network

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

theorem negativeLiminfLogRate_minimumInvariantLossFamily_eq_zero_of_not_hasCRP
    (N : StateDepMOR.Network Buffer Server)
    (hcrp : Not N.HasCRP)
    (U : N.DeterministicPolicySequence) :
    negativeLiminfLogRate (N.minimumInvariantLossFamily U) = 0 := by
  let J := Classical.choose
    (N.exists_strict_or_critical_cut_of_not_hasCRP hcrp)
  have hcut := Classical.choose_spec
    (N.exists_strict_or_critical_cut_of_not_hasCRP hcrp)
  cases hcut.2 with
  | inl hstrict =>
      exact negative_liminf_log_rate_eq_zero_of_isOmegaOneDivSq
        (N.minimumInvariantLossFamily U)
        (N.minimumInvariantLossFamily_nonnegative U)
        (N.minimumInvariantLossFamily_le_one U)
        (N.minimumInvariantLoss_isOmegaOneDivSq_of_strict_cutImbalance
          U J hstrict)
  | inr hcritical =>
      exact negative_liminf_log_rate_eq_zero_of_isOmegaOneDivSq
        (N.minimumInvariantLossFamily U)
        (N.minimumInvariantLossFamily_nonnegative U)
        (N.minimumInvariantLossFamily_le_one U)
        (minimumInvariantLoss_isOmegaOneDivSq_of_critical_cut
          N U J hcut.1 hcritical)

theorem pointwiseConverseStatement_of_not_hasCRP
    (N : StateDepMOR.Network Buffer Server)
    (hcrp : Not N.HasCRP) :
    PointwiseConverseStatement N := by
  intro U
  rw [
    negativeLiminfLogRate_minimumInvariantLossFamily_eq_zero_of_not_hasCRP
      N hcrp U]
  exact Network.gammaCBSup_nonnegative N

theorem fluidRestingPointStatement_of_not_hasCRP
    (N : StateDepMOR.Network Buffer Server)
    (hcrp : Not N.HasCRP) :
    FluidRestingPointStatement N := by
  intro alpha halpha U hnegative
  rw [
    negativeLiminfLogRate_minimumInvariantLossFamily_eq_zero_of_not_hasCRP
      N hcrp U]
  exact Network.gammaCB_nonnegative N alpha halpha

end PaperStatements
end StateDepMOR

namespace StateDepMOR
namespace Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : Network Buffer Server)

/-! ## Compact normalized states and scaling -/

/-- A queue state divided by its positive job count, in Mathlib's compact
simplex. -/
noncomputable def normalizedJobStdSimplex {K : Nat} (hK : 0 < K)
    (x : JobState Buffer K) : stdSimplex Real Buffer where
  val i := (x i : Real) / K
  property := by
    constructor
    next =>
      intro i
      positivity
    next =>
      rw [<- Finset.sum_div]
      have htotal : Finset.sum Finset.univ (fun i => (x i : Real)) = K := by
        exact_mod_cast x.total_jobs
      rw [htotal]
      exact div_self (by exact_mod_cast hK.ne')

/-- An interior perturbation of a possibly boundary simplex point. -/
noncomputable def interiorPerturb (a : stdSimplex Real Buffer) (eta : Real)
    (heta : 0 < eta) : Simplex Buffer where
  val i := (a i + eta * Simplex.uniform i) / (1 + eta)
  nonneg i := div_nonneg
    (add_nonneg (stdSimplex.zero_le a i)
      (mul_nonneg heta.le (Simplex.uniform.nonneg i)))
    (by linarith)
  sum_eq_one := by
    rw [<- Finset.sum_div, Finset.sum_add_distrib, <- Finset.mul_sum]
    rw [stdSimplex.sum_eq_one, Simplex.uniform.sum_eq_one]
    field_simp

theorem interiorPerturb_isInterior (a : stdSimplex Real Buffer)
    (eta : Real) (heta : 0 < eta) :
    (interiorPerturb a eta heta).IsInterior := by
  intro i
  apply div_pos
  next =>
    exact add_pos_of_nonneg_of_pos (stdSimplex.zero_le a i)
      (mul_pos heta (Simplex.uniform_isInterior i))
  next => linarith

theorem interiorPerturb_slack
    (a : stdSimplex Real Buffer) (eta : Real) (heta : 0 < eta)
    (i : Buffer) :
    (1 + eta) * interiorPerturb a eta heta i =
      a i + eta * Simplex.uniform i := by
  rw [interiorPerturb]
  field_simp

/-- A selected polynomial-mass atom of the concrete minimizing invariant
PMF. -/
noncomputable def frequentState
    (U : N.DeterministicPolicySequence) (K : PNat) :
    JobState Buffer (K : Nat) :=
  Classical.choose (N.exists_minimumInvariantPMF_atom_ge_polynomial U K)

theorem frequentState_mass
    (U : N.DeterministicPolicySequence) (K : PNat) :
    1 / ((((K : Nat) + 1 : Nat) ^ Fintype.card Buffer : Nat) : Real) <=
      (N.minimumInvariantPMF (U K) (N.frequentState U K)).toReal := by
  dsimp [frequentState]
  simpa only [Nat.cast_pow] using
    (Classical.choose_spec
      (N.exists_minimumInvariantPMF_atom_ge_polynomial U K))

noncomputable def frequentNormalizedState
    (U : N.DeterministicPolicySequence) (K : PNat) :
    stdSimplex Real Buffer :=
  normalizedJobStdSimplex K.pos (N.frequentState U K)

theorem frequentNormalizedState_apply
    (U : N.DeterministicPolicySequence) (K : PNat) (i : Buffer) :
    N.frequentNormalizedState U K i =
      (N.frequentState U K i : Real) / (K : Nat) :=
  rfl

private theorem noWasteDriftSet_scale
    (f : Server -> Buffer -> Real) (c : Real) (hc : 0 <= c) :
    N.noWasteDriftSet (fun j k => c * f j k) =
      (fun z => fun i => c * z i) '' N.noWasteDriftSet f := by
  classical
  ext z
  constructor
  next =>
    rintro ⟨d, hd, hdsum, hz⟩
    by_cases hzero : c = 0
    next =>
      subst c
      have hz0 : z = 0 := by
        funext i
        simpa using hz i
      rw [hz0]
      obtain ⟨z0, hz0mem⟩ :=
        PaperStatements.Network.noWasteDriftSet_nonempty N f
      exact ⟨z0, hz0mem, by funext i; simp⟩
    next =>
      let z' : Buffer -> Real := fun i => z i / c
      refine ⟨z', ?_, ?_⟩
      next =>
        refine ⟨d, hd, hdsum, ?_⟩
        intro i
        dsimp [z']
        apply (div_eq_iff hzero).2
        rw [hz i]
        have hin :
            Finset.univ.sum (fun j : Server => c * f j i) =
              c * Finset.univ.sum (fun j : Server => f j i) :=
          (Finset.mul_sum Finset.univ (fun j : Server => f j i) c).symm
        have hout :
            Finset.sum (N.serversOf i) (fun j =>
                d i j * Finset.univ.sum (fun k => c * f j k)) =
              c * Finset.sum (N.serversOf i) (fun j =>
                d i j * Finset.univ.sum (fun k => f j k)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          simpa [mul_assoc, mul_comm, mul_left_comm] using
            (Finset.mul_sum Finset.univ (fun k => f j k)
              (d i j * c)).symm
        rw [hin, hout]
        ring
      next =>
        funext i
        exact mul_div_cancel₀ (z i) hzero
  next =>
    rintro ⟨z0, ⟨d, hd, hdsum, hz0⟩, rfl⟩
    refine ⟨d, hd, hdsum, ?_⟩
    intro i
    change c * z0 i = _
    rw [hz0 i]
    have hin :
        Finset.univ.sum (fun j : Server => c * f j i) =
          c * Finset.univ.sum (fun j : Server => f j i) :=
      (Finset.mul_sum Finset.univ (fun j : Server => f j i) c).symm
    have hout :
        Finset.sum (N.serversOf i) (fun j =>
            d i j * Finset.univ.sum (fun k => c * f j k)) =
          c * Finset.sum (N.serversOf i) (fun j =>
            d i j * Finset.univ.sum (fun k => f j k)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (Finset.mul_sum Finset.univ (fun k => f j k)
          (d i j * c)).symm
    rw [hin, hout]
    ring

private theorem lAlphaAmbient_centered_scale
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (z : Buffer -> Real) (c : Real) (hc : 0 <= c) :
    Lyapunov.LAlphaAmbient (fun i => alpha i)
        ((fun i => alpha i) + (fun i => c * z i)) =
      c * Lyapunov.LAlphaAmbient (fun i => alpha i)
        ((fun i => alpha i) + z) := by
  rw [Lyapunov.LAlphaAmbient_centered
      (fun i => alpha i) (fun i => c * z i)
        (fun i => ne_of_gt (halpha i)),
    Lyapunov.LAlphaAmbient_centered
      (fun i => alpha i) z (fun i => ne_of_gt (halpha i))]
  simp only [mul_div_assoc]
  rw [show Lyapunov.minCoordinate (fun i => c * (z i / alpha i)) =
      c * Lyapunov.minCoordinate (fun i => z i / alpha i) by
    unfold Lyapunov.minCoordinate
    obtain ⟨q, hq, hqeq⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun i => z i / alpha i)
    apply le_antisymm
    next =>
      calc
        Finset.univ.inf' Finset.univ_nonempty
            (fun i => c * (z i / alpha i)) <=
            c * (z q / alpha q) :=
          Finset.inf'_le _ hq
        _ = c * Finset.univ.inf' Finset.univ_nonempty
            (fun i => z i / alpha i) := by rw [hqeq]
    next =>
      apply Finset.le_inf' Finset.univ_nonempty
      intro i hi
      exact mul_le_mul_of_nonneg_left (Finset.inf'_le _ hi) hc]
  ring

private theorem sInf_image_mul_pos
    (s : Set Real) (hs : s.Nonempty) (hbounded : BddBelow s)
    (c : Real) (hc : 0 < c) :
    sInf ((fun x => c * x) '' s) = c * sInf s := by
  have himage_nonempty : ((fun x => c * x) '' s).Nonempty := hs.image _
  have himage_bdd : BddBelow ((fun x => c * x) '' s) := by
    obtain ⟨b, hb⟩ := hbounded
    exact ⟨c * b, by
      rintro _ ⟨x, hx, rfl⟩
      exact mul_le_mul_of_nonneg_left (hb hx) hc.le⟩
  apply le_antisymm
  next =>
    rw [mul_comm]
    have hdiv : sInf ((fun x => c * x) '' s) / c <= sInf s := by
      apply le_csInf hs
      intro x hx
      apply (div_le_iff₀ hc).2
      exact csInf_le himage_bdd ⟨x, hx, mul_comm c x⟩
    exact (div_le_iff₀ hc).1 hdiv
  next =>
    apply le_csInf himage_nonempty
    rintro _ ⟨x, hx, rfl⟩
    exact mul_le_mul_of_nonneg_left (csInf_le hbounded hx) hc.le

theorem vAlpha_scale_nonneg
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real) (hf : forall j k, 0 <= f j k)
    (c : Real) (hc : 0 < c) :
    PaperStatements.Network.vAlpha (N := N) alpha
        (fun j k => c * f j k) =
      c * PaperStatements.Network.vAlpha (N := N) alpha f := by
  rw [PaperStatements.Network.vAlpha,
    N.noWasteDriftSet_scale f c hc.le]
  simp only [Set.image_image, Function.comp_apply,
    lAlphaAmbient_centered_scale alpha halpha _ c hc.le]
  rw [<- Set.image_image]
  apply sInf_image_mul_pos
  next =>
    exact (PaperStatements.Network.noWasteDriftSet_nonempty N f).image _
  next =>
    exact N.vAlphaImage_bddBelow_of_nonneg alpha halpha f hf
  next => exact hc

/-! ## Rounded-count forcing along a liminf-realizing subsequence -/

theorem exists_frequent_state_liminf_subsequence
    (U : N.DeterministicPolicySequence) :
    exists (K : Nat -> PNat) (a : stdSimplex Real Buffer),
      Tendsto K atTop atTop /\
      Tendsto
        (fun r =>
          ConverseAsymptotics.scaledLogLoss
            (N.minimumInvariantLossFamily U) (K r))
        atTop
        (nhds
          (liminf
            (ConverseAsymptotics.scaledLogLoss
              (N.minimumInvariantLossFamily U)) atTop)) /\
      Tendsto (fun r => N.frequentNormalizedState U (K r))
        atTop (nhds a) := by
  obtain ⟨K0, hlog, hK0⟩ :=
    exists_seq_tendsto_liminf
      (f := (atTop : Filter PNat))
      (u := ConverseAsymptotics.scaledLogLoss
        (N.minimumInvariantLossFamily U))
  obtain ⟨a, q, hq, ha⟩ :=
    CompactSpace.tendsto_subseq
      (fun r => N.frequentNormalizedState U (K0 r))
  let K : Nat -> PNat := fun r => K0 (q r)
  refine ⟨K, a, ?_, ?_, ?_⟩
  next => exact hK0.comp hq.tendsto_atTop
  next => exact hlog.comp hq.tendsto_atTop
  next => exact ha

theorem frequentState_capacity_eventually
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (a : stdSimplex Real Buffer)
    (ha : Tendsto (fun r => N.frequentNormalizedState U (K r))
      atTop (nhds a))
    (eta : Real) (heta : 0 < eta) :
    Filter.Eventually
      (fun r => forall i,
        (N.frequentState U (K r) i : Real) <=
          (((K r : Nat) : Real) * (1 + eta)) *
            interiorPerturb a eta heta i)
      atTop := by
  rw [Filter.eventually_all]
  intro i
  have hval :
      Tendsto
        (fun r =>
          ((N.frequentNormalizedState U (K r) :
            stdSimplex Real Buffer) : Buffer -> Real))
        atTop (nhds ((a : stdSimplex Real Buffer) : Buffer -> Real)) :=
    (continuous_subtype_val.tendsto a).comp ha
  have hcoord :
      Tendsto (fun r => N.frequentNormalizedState U (K r) i)
        atTop (nhds (a i)) :=
    hval.apply_nhds i
  have hslack : 0 < eta * Simplex.uniform i :=
    mul_pos heta (Simplex.uniform_isInterior i)
  have hevent :
      Filter.Eventually
        (fun r =>
          N.frequentNormalizedState U (K r) i <
            a i + eta * Simplex.uniform i)
        atTop :=
    hcoord.eventually_lt_const (lt_add_of_pos_right _ hslack)
  filter_upwards [hevent] with r hr
  have hKreal : (0 : Real) < (K r : Nat) := by
    exact_mod_cast (K r).pos
  rw [N.frequentNormalizedState_apply] at hr
  have hscaled :
      (N.frequentState U (K r) i : Real) <
        ((K r : Nat) : Real) *
          (a i + eta * Simplex.uniform i) := by
    simpa [mul_comm] using (div_lt_iff₀ hKreal).1 hr
  rw [<- interiorPerturb_slack a eta heta i] at hscaled
  calc
    (N.frequentState U (K r) i : Real) <=
        ((K r : Nat) : Real) *
          ((1 + eta) * interiorPerturb a eta heta i) :=
      hscaled.le
    _ = (((K r : Nat) : Real) * (1 + eta)) *
          interiorPerturb a eta heta i := by ring

theorem roundedCountRate_tendsto
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (T : NNReal)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop) :
    Tendsto
      (fun r j k =>
        (ConverseAsymptotics.roundedPoissonCount T f (K r) j k : Real) /
          ((K r : Nat) : Real))
      atTop (nhds (fun j k => (T : Real) * f j k)) := by
  let g : Nat -> Server -> Buffer -> Real := fun r j k =>
    (ConverseAsymptotics.roundedPoissonCount T f (K r) j k : Real) /
      ((K r : Nat) : Real)
  have hKnat :
      Tendsto (fun r => (K r : Nat)) atTop atTop :=
    tendsto_PNat_val_atTop_atTop.comp hK
  change Tendsto g atTop (nhds (fun j k => (T : Real) * f j k))
  rw [tendsto_pi_nhds]
  intro j
  rw [tendsto_pi_nhds]
  intro k
  exact
    (ConverseAsymptotics.roundedPoissonCount_ratio_tendsto
      T f hf j k).comp hKnat

theorem roundedCountRate_vAlpha_tendsto
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (T : NNReal)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop) :
    Tendsto
      (fun r =>
        PaperStatements.Network.vAlpha (N := N) alpha
          (fun j k =>
            (ConverseAsymptotics.roundedPoissonCount
              T f (K r) j k : Real) / ((K r : Nat) : Real)))
      atTop
      (nhds
        (PaperStatements.Network.vAlpha (N := N) alpha
          (fun j k => (T : Real) * f j k))) := by
  let g : Nat -> Server -> Buffer -> Real := fun r j k =>
    (ConverseAsymptotics.roundedPoissonCount T f (K r) j k : Real) /
      ((K r : Nat) : Real)
  have hg :
      Tendsto g atTop (nhds (fun j k => (T : Real) * f j k)) :=
    roundedCountRate_tendsto f hf T K hK
  change Tendsto
    (fun r => PaperStatements.Network.vAlpha (N := N) alpha (g r))
    atTop
    (nhds
      (PaperStatements.Network.vAlpha (N := N) alpha
        (fun j k => (T : Real) * f j k)))
  exact
    ((PaperStatements.Network.vAlpha_continuous N alpha).tendsto
      (fun j k => (T : Real) * f j k)).comp hg

theorem roundedCount_vAlpha_force_eventually
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (T : NNReal) (hT : 0 < T) (c : Real)
    (hc :
      c < (T : Real) *
        PaperStatements.Network.vAlpha (N := N) alpha f)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop) :
    Filter.Eventually
      (fun r =>
        ((K r : Nat) : Real) * c <
          PaperStatements.Network.vAlpha (N := N) alpha
            (fun j k =>
              (ConverseAsymptotics.roundedPoissonCount
                T f (K r) j k : Real)))
      atTop := by
  let g : Nat -> Server -> Buffer -> Real := fun r j k =>
    (ConverseAsymptotics.roundedPoissonCount T f (K r) j k : Real) /
      ((K r : Nat) : Real)
  have hv :
      Tendsto
        (fun r =>
          PaperStatements.Network.vAlpha (N := N) alpha (g r))
        atTop
        (nhds
          (PaperStatements.Network.vAlpha (N := N) alpha
            (fun j k => (T : Real) * f j k))) :=
    N.roundedCountRate_vAlpha_tendsto alpha f hf T K hK
  have hscale :
      PaperStatements.Network.vAlpha (N := N) alpha
          (fun j k => (T : Real) * f j k) =
        (T : Real) *
          PaperStatements.Network.vAlpha (N := N) alpha f :=
    N.vAlpha_scale_nonneg alpha halpha f hf T hT
  rw [hscale] at hv
  have hevent :
      Filter.Eventually
        (fun r =>
          c < PaperStatements.Network.vAlpha (N := N) alpha (g r))
        atTop :=
    hv.eventually_const_lt hc
  filter_upwards [hevent] with r hr
  have hKreal : (0 : Real) < (K r : Nat) := by
    exact_mod_cast (K r).pos
  have hscaled :=
    mul_lt_mul_of_pos_left hr hKreal
  have hg_nonneg : forall j k, 0 <= g r j k := by
    intro j k
    dsimp [g]
    positivity
  have hvscale :=
    N.vAlpha_scale_nonneg alpha halpha (g r) hg_nonneg
      ((K r : Nat) : Real) hKreal
  have hmatrix :
      (fun j k => ((K r : Nat) : Real) * g r j k) =
        (fun j k =>
          (ConverseAsymptotics.roundedPoissonCount
            T f (K r) j k : Real)) := by
    funext j k
    dsimp [g]
    exact mul_div_cancel₀ _
      (ne_of_gt hKreal)
  rw [hmatrix] at hvscale
  rw [hvscale]
  exact hscaled

theorem roundedTotalCount_ratio_tendsto
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (T : NNReal)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop) :
    Tendsto
      (fun r =>
        (N.totalFiniteCount
          (ConverseAsymptotics.roundedPoissonCount T f (K r)) : Real) /
            ((K r : Nat) : Real))
      atTop
      (nhds
        ((T : Real) *
          Finset.univ.sum (fun j =>
            Finset.univ.sum (fun k => f j k)))) := by
  have hcoord := roundedCountRate_tendsto f hf T K hK
  have hsum :
      Tendsto
        (fun r =>
          Finset.univ.sum (fun j =>
            Finset.univ.sum (fun k =>
              (ConverseAsymptotics.roundedPoissonCount
                T f (K r) j k : Real) / ((K r : Nat) : Real))))
        atTop
        (nhds
          (Finset.univ.sum (fun j =>
            Finset.univ.sum (fun k => (T : Real) * f j k)))) := by
    apply tendsto_finsetSum
    intro j hj
    apply tendsto_finsetSum
    intro k hk
    exact (hcoord.apply_nhds j).apply_nhds k
  simpa only [Network.totalFiniteCount, Nat.cast_sum, Finset.sum_div,
    Finset.mul_sum] using hsum

theorem roundedCount_prefactor_le_power_eventually
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (T : NNReal)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop) :
    Filter.Eventually
      (fun r =>
        (((((K r : Nat) + 1 : Nat) ^ Fintype.card Buffer : Nat) : Real) *
            (N.totalFiniteCount
              (ConverseAsymptotics.roundedPoissonCount
                T f (K r)) : Real)) <=
          (((K r : Nat) : Real) ^ (Fintype.card Buffer + 3)))
      atTop := by
  let L : Real :=
    (T : Real) *
      Finset.univ.sum (fun j =>
        Finset.univ.sum (fun k => f j k))
  let C : Real := abs L + 1
  have hratio :=
    N.roundedTotalCount_ratio_tendsto f hf T K hK
  change Tendsto _ atTop (nhds L) at hratio
  have hLC : L < C := by
    dsimp [C]
    linarith [le_abs_self L]
  have hratio_bound :
      Filter.Eventually
        (fun r =>
          (N.totalFiniteCount
            (ConverseAsymptotics.roundedPoissonCount T f (K r)) : Real) /
              ((K r : Nat) : Real) < C)
        atTop :=
    hratio.eventually_lt_const hLC
  have hKreal :
      Tendsto (fun r => ((K r : Nat) : Real)) atTop atTop :=
    StateDepMOR.tendsto_pnatCast_atTop.comp hK
  have hC_le_K :
      Filter.Eventually (fun r => C <= ((K r : Nat) : Real)) atTop :=
    (eventually_ge_atTop C).filter_mono hKreal
  have htwo_pow_le_K :
      Filter.Eventually
        (fun r =>
          ((2 : Real) ^ Fintype.card Buffer) <=
            ((K r : Nat) : Real))
        atTop :=
    (eventually_ge_atTop ((2 : Real) ^ Fintype.card Buffer)).filter_mono
      hKreal
  filter_upwards [hratio_bound, hC_le_K, htwo_pow_le_K] with
    r hratio_r hC_r htwo_r
  let k : Real := ((K r : Nat) : Real)
  let total : Real :=
    (N.totalFiniteCount
      (ConverseAsymptotics.roundedPoissonCount T f (K r)) : Real)
  change
    (((((K r : Nat) + 1 : Nat) ^ Fintype.card Buffer : Nat) : Real) *
        total) <= k ^ (Fintype.card Buffer + 3)
  have hk : 1 <= k := by
    dsimp [k]
    exact_mod_cast (K r).pos
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have htotal : total <= k ^ 2 := by
    have hratio_le : total / k <= k :=
      hratio_r.le.trans hC_r
    apply (div_le_iff₀ hkpos).1 at hratio_le
    nlinarith
  have hbase : (((K r : Nat) + 1 : Nat) : Real) <= 2 * k := by
    have hadd := add_le_add_left hk k
    simpa [k, Nat.cast_add, Nat.cast_one, two_mul, add_comm] using hadd
  have hbox :
      (((((K r : Nat) + 1 : Nat) ^ Fintype.card Buffer : Nat) : Real) <=
        (2 * k) ^ Fintype.card Buffer) := by
    simpa only [Nat.cast_pow] using
      (pow_le_pow_left₀ (by positivity) hbase (Fintype.card Buffer))
  calc
    (((((K r : Nat) + 1 : Nat) ^ Fintype.card Buffer : Nat) : Real) *
        total) <=
        (2 * k) ^ Fintype.card Buffer * (k ^ 2) :=
      mul_le_mul hbox htotal (by positivity) (by positivity)
    _ = (2 : Real) ^ Fintype.card Buffer *
        k ^ Fintype.card Buffer * k ^ 2 := by
      rw [mul_pow]
    _ <= k * k ^ Fintype.card Buffer * k ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htwo_r (by positivity))
        (by positivity)
    _ = k ^ (Fintype.card Buffer + 3) := by
      rw [pow_add]
      ring

theorem roundedCount_forcing_polynomial_lower_bound
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (T : NNReal) (hT : 0 < T) (c : Real)
    (hc :
      c < (T : Real) *
        PaperStatements.Network.vAlpha (N := N) alpha f)
    (hcapacity :
      Filter.Eventually
        (fun r => forall i,
          (N.frequentState U (K r) i : Real) <=
            (((K r : Nat) : Real) * c) * alpha i)
        atTop) :
    Filter.Eventually
      (fun r =>
        (1 / (((K r : Nat) : Real) ^
            (Fintype.card Buffer + 3)) *
          (poissonCountLaw N (K r) T).real
            {ConverseAsymptotics.roundedPoissonCount T f (K r)} <=
          N.minimumInvariantLossFamily U (K r)))
      atTop := by
  have hforce :=
    N.roundedCount_vAlpha_force_eventually
      alpha halpha f hf T hT c hc K hK
  have hprefactor :=
    N.roundedCount_prefactor_le_power_eventually f hf T K hK
  filter_upwards [hcapacity, hforce, hprefactor] with
    r hcapacity_r hforce_r hprefactor_r
  let n : Server -> Buffer -> Nat :=
    ConverseAsymptotics.roundedPoissonCount T f (K r)
  let mass : Real :=
    (N.minimumInvariantPMF (U (K r)) (N.frequentState U (K r))).toReal
  let atom : Real := (poissonCountLaw N (K r) T).real {n}
  let box : Real :=
    ((((K r : Nat) + 1 : Nat) ^ Fintype.card Buffer : Nat) : Real)
  let total : Real := (N.totalFiniteCount n : Real)
  let loss : Real := N.minimumInvariantLossFamily U (K r)
  let power : Real :=
    ((K r : Nat) : Real) ^ (Fintype.card Buffer + 3)
  have htrajectory :
      forall tokens, N.tokenVectorHasCounts n tokens ->
        0 < N.trajectoryWaste (U (K r)) (N.frequentState U (K r))
          (List.ofFn tokens) := by
    intro tokens hcounts
    exact N.exact_coordinate_counts_force_trajectoryWaste_pos
      alpha halpha (U (K r)) (N.frequentState U (K r))
      (List.ofFn tokens) n (((K r : Nat) : Real) * c)
      hcapacity_r hcounts hforce_r
  have hstation :
      mass * atom <= total * loss := by
    dsimp [mass, atom, total, loss, n]
    exact N.poissonSingleton_mul_stationaryMass_le_minimumInvariantLoss
      (U (K r)) (N.frequentState U (K r))
      (ConverseAsymptotics.roundedPoissonCount T f (K r)) T
      (N.poissonCountLaw_real_singleton_le_exactCountVectorMass
        (K r) T
        (ConverseAsymptotics.roundedPoissonCount T f (K r)))
      htrajectory
  have hmass : 1 / box <= mass := by
    dsimp [box, mass]
    exact N.frequentState_mass U (K r)
  have hbox : 0 < box := by
    dsimp [box]
    positivity
  have hone_mass : 1 <= box * mass := by
    have h := (div_le_iff₀ hbox).1 hmass
    simpa [mul_comm] using h
  have hatom : 0 <= atom := by
    dsimp [atom]
    exact MeasureTheory.measureReal_nonneg
  have hbox_nonneg : 0 <= box := hbox.le
  have hloss : 0 <= loss := by
    dsimp [loss]
    exact N.minimumInvariantLossFamily_nonnegative U (K r)
  have hpower : 0 < power := by
    dsimp [power]
    positivity
  have hatom_le : atom <= power * loss := by
    calc
      atom = 1 * atom := by ring
      _ <= (box * mass) * atom :=
        mul_le_mul_of_nonneg_right hone_mass hatom
      _ = box * (mass * atom) := by ring
      _ <= box * (total * loss) :=
        mul_le_mul_of_nonneg_left hstation hbox_nonneg
      _ = (box * total) * loss := by ring
      _ <= power * loss :=
        mul_le_mul_of_nonneg_right hprefactor_r hloss
  change 1 / power * atom <= loss
  have heq : 1 / power * atom = atom / power := by
    simp only [one_div, div_eq_mul_inv]
    ring
  rw [heq]
  apply (div_le_iff₀ hpower).2
  simpa [mul_comm] using hatom_le

theorem poissonCountLaw_rounded_singleton_pos
    (f : Server -> Buffer -> Real)
    (hsupport : forall j k, N.phi j k = 0 -> f j k = 0)
    (T : NNReal) (hT : 0 < T) (K : PNat) :
    0 < (poissonCountLaw N K T).real
      {ConverseAsymptotics.roundedPoissonCount T f K} := by
  rw [poissonCountLaw_real_singleton, poissonCountAtomReal]
  apply Finset.prod_pos
  intro j hj
  apply Finset.prod_pos
  intro k hk
  rcases (N.phi_nonneg j k).eq_or_lt with hphi_zero | hphi_pos
  next =>
    rw [<- hphi_zero,
      ConverseAsymptotics.roundedPoissonCount_zero T f j k
        (hsupport j k hphi_zero.symm)]
    simp [poissonAtomReal]
  next =>
    exact poissonAtomReal_pos K
      (ConverseAsymptotics.roundedPoissonCount T f K j k)
      T (N.phi j k) K.pos (by exact_mod_cast hT) hphi_pos

theorem negativeLiminfLogRate_le_rounded_forcing_cost
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop)
    (hrealize :
      Tendsto
        (fun r =>
          ConverseAsymptotics.scaledLogLoss
            (N.minimumInvariantLossFamily U) (K r))
        atTop
        (nhds
          (liminf
            (ConverseAsymptotics.scaledLogLoss
              (N.minimumInvariantLossFamily U)) atTop)))
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (hsupport : forall j k, N.phi j k = 0 -> f j k = 0)
    (T : NNReal) (hT : 0 < T) (c : Real)
    (hc :
      c < (T : Real) *
        PaperStatements.Network.vAlpha (N := N) alpha f)
    (hcapacity :
      Filter.Eventually
        (fun r => forall i,
          (N.frequentState U (K r) i : Real) <=
            (((K r : Nat) : Real) * c) * alpha i)
        atTop) :
    PaperStatements.negativeLiminfLogRate
        (N.minimumInvariantLossFamily U) <=
      ((((T : Real) *
        Finset.univ.sum (fun j =>
          Finset.univ.sum (fun k =>
            poissonCostReal (N.phi j k) (f j k)))) : Real) : EReal) := by
  let degree : Nat := Fintype.card Buffer + 3
  let atom : Nat -> Real := fun r =>
    (poissonCountLaw N (K r) T).real
      {ConverseAsymptotics.roundedPoissonCount T f (K r)}
  let prefactor : Nat -> Real := fun r =>
    ((K r : Nat) : Real) ^ degree
  let lower : Nat -> Real := fun r => 1 / prefactor r * atom r
  let cost : Real :=
    (T : Real) *
      Finset.univ.sum (fun j =>
        Finset.univ.sum (fun k =>
          poissonCostReal (N.phi j k) (f j k)))
  have hbound :
      Filter.Eventually
        (fun r => lower r <= N.minimumInvariantLossFamily U (K r))
        atTop := by
    simpa only [lower, prefactor, atom, degree] using
      N.roundedCount_forcing_polynomial_lower_bound
        U K hK alpha halpha f hf T hT c hc hcapacity
  have hatom : forall r, 0 < atom r := by
    intro r
    exact N.poissonCountLaw_rounded_singleton_pos
      f hsupport T hT (K r)
  have hprefactor : forall r, 0 < prefactor r := by
    intro r
    dsimp [prefactor]
    positivity
  have hlower :
      Filter.Eventually (fun r => 0 < lower r) atTop :=
    Filter.Eventually.of_forall fun r =>
      mul_pos (div_pos zero_lt_one (hprefactor r)) (hatom r)
  have hzero :
      forall j k, N.phi j k = 0 ->
        forall q,
          ConverseAsymptotics.roundedPoissonCount T f q j k = 0 := by
    intro j k hphi q
    exact ConverseAsymptotics.roundedPoissonCount_zero
      T f j k (hsupport j k hphi)
  have hn :
      forall j k,
        Tendsto
          (fun q : Nat =>
            (ConverseAsymptotics.roundedPoissonCount T f q j k : Real) / q)
          atTop (nhds ((T : Real) * f j k)) :=
    ConverseAsymptotics.roundedPoissonCount_ratio_tendsto T f hf
  have hatom_cost :
      Tendsto
        (fun r => -Real.log (atom r) / ((K r : Nat) : Real))
        atTop (nhds cost) := by
    have hfull :=
      ConverseAsymptotics.poissonCountLaw_log_asymptotic_pnat
        N T hT f (ConverseAsymptotics.roundedPoissonCount T f)
        hzero hn
    exact hfull.comp hK
  have hprefactor_rate :
      Tendsto
        (fun r => Real.log (prefactor r) / ((K r : Nat) : Real))
        atTop (nhds 0) := by
    exact (ConverseAsymptotics.tendsto_log_pnat_pow_div degree).comp hK
  have hlower_cost :
      Tendsto
        (fun r => -Real.log (lower r) / ((K r : Nat) : Real))
        atTop (nhds cost) := by
    have hsum := hprefactor_rate.add hatom_cost
    simpa only [zero_add] using hsum.congr' (by
      filter_upwards [] with r
      dsimp [lower]
      rw [one_div, Real.log_mul
        (inv_ne_zero (hprefactor r).ne') (hatom r).ne',
        Real.log_inv]
      ring)
  exact
    ConverseAsymptotics.negativeLiminfLogRate_le_of_realizing_lower_bound
      (N.minimumInvariantLossFamily U) lower K cost
      hrealize hlower hbound hlower_cost

theorem ereal_le_coe_of_forall_pos_le_add
    (x : EReal) (g : Real)
    (h : forall epsilon : Real, 0 < epsilon ->
      x <= ((g + epsilon : Real) : EReal)) :
    x <= (g : EReal) := by
  by_contra hnot
  have hgx : (g : EReal) < x := lt_of_not_ge hnot
  obtain ⟨y, hgy, hyx⟩ := EReal.exists_between_coe_real hgx
  have hepsilon : 0 < y - g :=
    sub_pos.2 (EReal.coe_lt_coe_iff.mp hgy)
  have hle := h (y - g) hepsilon
  rw [show g + (y - g) = y by ring] at hle
  exact (not_lt_of_ge hle) hyx

theorem candidate_scaled_ratio_bound
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop)
    (hrealize :
      Tendsto
        (fun r => ConverseAsymptotics.scaledLogLoss
          (N.minimumInvariantLossFamily U) (K r))
        atTop
        (nhds (liminf
          (ConverseAsymptotics.scaledLogLoss
            (N.minimumInvariantLossFamily U)) atTop)))
    (a : stdSimplex Real Buffer)
    (ha : Tendsto (fun r => N.frequentNormalizedState U (K r))
      atTop (nhds a))
    (eta : Real) (heta : 0 < eta)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (hsupport : forall j k, N.phi j k = 0 -> f j k = 0)
    (hv : 0 < PaperStatements.Network.vAlpha (N := N)
      (interiorPerturb a eta heta) f) :
    PaperStatements.negativeLiminfLogRate
        (N.minimumInvariantLossFamily U) <=
      ((1 + eta : Real) : EReal) *
        ((N.localRate f : EReal) /
          (PaperStatements.Network.vAlpha (N := N)
            (interiorPerturb a eta heta) f : EReal)) := by
  let alpha := interiorPerturb a eta heta
  let v0 := PaperStatements.Network.vAlpha (N := N) alpha f
  let I : Real := Finset.univ.sum (fun j =>
    Finset.univ.sum (fun k =>
      poissonCostReal (N.phi j k) (f j k)))
  have hI : 0 <= I := by
    dsimp [I]
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro k hk
    rcases (N.phi_nonneg j k).eq_or_lt with hzero | hpos
    · rw [<- hzero, hsupport j k hzero.symm]
      simp [poissonCostReal]
    · exact poissonCostReal_nonneg hpos (hf j k)
  have hreal :
      PaperStatements.negativeLiminfLogRate
          (N.minimumInvariantLossFamily U) <=
        (((1 + eta) * I / v0 : Real) : EReal) := by
    apply ereal_le_coe_of_forall_pos_le_add
    intro epsilon hepsilon
    let t : Real :=
      (1 + eta) / v0 + epsilon / (I + 1)
    have hIone : 0 < I + 1 := by linarith
    have ht : 0 < t := by
      dsimp [t, v0]
      positivity
    let T : NNReal := ⟨t, ht.le⟩
    have hT : 0 < T := by
      exact_mod_cast ht
    have hforce :
        1 + eta < (T : Real) * v0 := by
      change 1 + eta < t * v0
      dsimp [t]
      have hv0 : 0 < v0 := hv
      calc
        1 + eta <
            1 + eta + (epsilon / (I + 1)) * v0 := by
          exact lt_add_of_pos_right _
            (mul_pos (div_pos hepsilon hIone) hv0)
        _ = ((1 + eta) / v0 + epsilon / (I + 1)) * v0 := by
          field_simp
    have hcapacity :=
      N.frequentState_capacity_eventually U K a ha eta heta
    have hbound :=
      N.negativeLiminfLogRate_le_rounded_forcing_cost
        U K hK hrealize alpha
        (interiorPerturb_isInterior a eta heta)
        f hf hsupport T hT (1 + eta) hforce hcapacity
    have hcost :
        (T : Real) * I <= (1 + eta) * I / v0 + epsilon := by
      change t * I <= (1 + eta) * I / v0 + epsilon
      dsimp [t]
      have hfrac : epsilon * I / (I + 1) <= epsilon := by
        apply (div_le_iff₀ hIone).2
        nlinarith
      calc
        ((1 + eta) / v0 + epsilon / (I + 1)) * I =
            (1 + eta) * I / v0 + epsilon * I / (I + 1) := by ring
        _ <= (1 + eta) * I / v0 + epsilon := by linarith
    exact hbound.trans (EReal.coe_le_coe_iff.mpr hcost)
  have hlocal :=
    ConverseAsymptotics.localRate_eq_ofReal_sum_poissonCostReal
      N f hf hsupport
  rw [hlocal, EReal.coe_ennreal_ofReal, max_eq_left hI,
    <- EReal.coe_div, <- EReal.coe_mul]
  simpa [v0, alpha, mul_div_assoc] using hreal

theorem scaled_loss_le_gammaCB
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop)
    (hrealize :
      Tendsto
        (fun r => ConverseAsymptotics.scaledLogLoss
          (N.minimumInvariantLossFamily U) (K r))
        atTop
        (nhds (liminf
          (ConverseAsymptotics.scaledLogLoss
            (N.minimumInvariantLossFamily U)) atTop)))
    (a : stdSimplex Real Buffer)
    (ha : Tendsto (fun r => N.frequentNormalizedState U (K r))
      atTop (nhds a))
    (eta : Real) (heta : 0 < eta) :
    PaperStatements.negativeLiminfLogRate
        (N.minimumInvariantLossFamily U) /
        ((1 + eta : Real) : EReal) <=
      PaperStatements.Network.gammaCB (N := N)
        (interiorPerturb a eta heta) := by
  let x := PaperStatements.negativeLiminfLogRate
    (N.minimumInvariantLossFamily U)
  let alpha := interiorPerturb a eta heta
  have hc : (0 : EReal) < ((1 + eta : Real) : EReal) :=
    EReal.coe_pos.2 (by linarith)
  have hctop : Ne (((1 + eta : Real) : EReal)) Top.top :=
    EReal.coe_ne_top _
  unfold PaperStatements.Network.gammaCB
  apply le_sInf
  intro q hq
  obtain ⟨f, hf, hv, rfl⟩ := hq
  by_cases htop : N.localRate f = (Top.top : ENNReal)
  · rw [htop]
    rw [EReal.coe_ennreal_top,
      EReal.top_div_of_pos_ne_top (EReal.coe_pos.2 hv)
        (EReal.coe_ne_top _)]
    exact le_top
  · have hsupport :
        forall j k, N.phi j k = 0 -> f j k = 0 :=
      N.localRate_ne_top_implies_zero_of_phi_eq_zero f htop
    have hscaled := N.candidate_scaled_ratio_bound
      U K hK hrealize a ha eta heta f hf hsupport hv
    apply (EReal.div_le_iff_le_mul hc hctop).2
    simpa [x, alpha, mul_comm] using hscaled

end Network

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

namespace PaperStatements

theorem smwExponentSup_eq_coe_best_for_converse
    (N : StateDepMOR.Network Buffer Server)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    smwExponentSup N = (N.bestSMWExponent : EReal) := by
  let S : Set Real := N.interiorExponentSet
  have hSne : S.Nonempty := N.interiorExponentSet_nonempty
  have hSbdd : BddAbove S := N.interiorExponentSet_bddAbove hflex hcrp
  have hset :
      {q : EReal | exists alpha : Simplex Buffer,
        alpha.IsInterior /\ q = (N.explicitExponent alpha : EReal)} =
        (fun r : Real => (r : EReal)) '' S := by
    ext q
    constructor
    · rintro ⟨alpha, halpha, rfl⟩
      exact ⟨N.explicitExponent alpha, ⟨alpha, halpha, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨alpha, halpha, rfl⟩, rfl⟩
      exact ⟨alpha, halpha, rfl⟩
  rw [smwExponentSup, hset]
  change
    (sSup ((fun r : Real => WithBot.some (WithTop.some r)) '' S) :
      WithBot (WithTop Real)) =
      WithBot.some (WithTop.some N.bestSMWExponent)
  let STop : Set (WithTop Real) :=
    (fun r : Real => (r : WithTop Real)) '' S
  have hSTop_nonempty : STop.Nonempty := hSne.image _
  have hSTop_bdd : BddAbove STop := OrderTop.bddAbove _
  have hwb :
      WithBot.some (sSup STop : WithTop Real) =
        (sSup ((fun r : WithTop Real => WithBot.some r) '' STop) :
          WithBot (WithTop Real)) := by
    exact WithBot.coe_sSup' hSTop_nonempty hSTop_bdd
  have himage :
      (fun r : Real => WithBot.some (WithTop.some r)) '' S =
        (fun r : WithTop Real => WithBot.some r) '' STop := by
    ext q
    simp only [STop, Set.mem_image]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(r : WithTop Real), ⟨r, hr, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [himage, <- hwb]
  have htop : ((sSup S : Real) : WithTop Real) = sSup STop := by
    simpa only [STop] using WithTop.coe_sSup' hSbdd
  rw [<- htop]
  simp only [S, StateDepMOR.Network.bestSMWExponent]

end PaperStatements

namespace Network

theorem pointwiseConverseStatement_of_limited_crp
    (N : Network Buffer Server)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    PaperStatements.PointwiseConverseStatement N := by
  intro U
  obtain ⟨K, a, hK, hrealize, ha⟩ :=
    N.exists_frequent_state_liminf_subsequence U
  let x := PaperStatements.negativeLiminfLogRate
    (N.minimumInvariantLossFamily U)
  let g : Real := N.bestSMWExponent
  have hG :
      PaperStatements.Network.gammaCBSup (N := N) = (g : EReal) := by
    calc
      PaperStatements.Network.gammaCBSup (N := N) =
          PaperStatements.smwExponentSup N :=
        PaperStatements.Network.gammaCBSup_eq_smwExponentSup
          N hflex hcrp
      _ = (N.bestSMWExponent : EReal) :=
        PaperStatements.smwExponentSup_eq_coe_best_for_converse
          N hflex hcrp
  have hg : 0 <= g := by
    have hnonneg :
        (0 : EReal) <=
          PaperStatements.Network.gammaCBSup (N := N) :=
      PaperStatements.Network.gammaCBSup_nonnegative N
    rw [hG, EReal.coe_nonneg] at hnonneg
    exact hnonneg
  rw [hG]
  apply ereal_le_coe_of_forall_pos_le_add
  intro epsilon hepsilon
  let eta : Real := epsilon / (g + 1)
  have hgone : 0 < g + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon hgone
  let alpha := interiorPerturb a eta heta
  have hscaled := N.scaled_loss_le_gammaCB
    U K hK hrealize a ha eta heta
  have hc : (0 : EReal) < ((1 + eta : Real) : EReal) :=
    EReal.coe_pos.2 (by linarith)
  have hctop : Ne (((1 + eta : Real) : EReal)) Top.top :=
    EReal.coe_ne_top _
  have hxgamma :
      x <= ((1 + eta : Real) : EReal) *
        PaperStatements.Network.gammaCB (N := N) alpha := by
    exact (EReal.div_le_iff_le_mul hc hctop).mp hscaled
  have hgamma :
      PaperStatements.Network.gammaCB (N := N) alpha <=
        PaperStatements.Network.gammaCBSup (N := N) := by
    unfold PaperStatements.Network.gammaCBSup
    apply le_sSup
    exact ⟨alpha, interiorPerturb_isInterior a eta heta, rfl⟩
  have hxG :
      x <= ((1 + eta : Real) : EReal) *
        PaperStatements.Network.gammaCBSup (N := N) :=
    hxgamma.trans
      (mul_le_mul_of_nonneg_left hgamma
        (EReal.coe_nonneg.2 (by linarith)))
  rw [hG, <- EReal.coe_mul] at hxG
  have hreal :
      (1 + eta) * g <= g + epsilon := by
    dsimp [eta]
    have hfrac : epsilon * g / (g + 1) <= epsilon := by
      apply (div_le_iff₀ hgone).2
      nlinarith
    calc
      (1 + epsilon / (g + 1)) * g =
          g + epsilon * g / (g + 1) := by ring
      _ <= g + epsilon := by linarith
  exact hxG.trans (EReal.coe_le_coe_iff.mpr hreal)

/-- The exact unconditional pointwise converse for the concrete minimum
invariant loss family. -/
theorem pointwiseConverseStatement
    (N : Network Buffer Server) :
    PaperStatements.PointwiseConverseStatement N := by
  by_cases hflex : N.HasLimitedFlexibility
  · by_cases hcrp : N.HasCRP
    · exact N.pointwiseConverseStatement_of_limited_crp hflex hcrp
    · exact PaperStatements.pointwiseConverseStatement_of_not_hasCRP
        N hcrp
  · intro U
    rw [PaperStatements.Network.gammaCBSup_eq_top_of_not_limited N hflex]
    exact le_top

end Network
end StateDepMOR
