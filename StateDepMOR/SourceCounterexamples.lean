import StateDepMOR.ConcretePerformance
import StateDepMOR.PaperStatements

/-!
# Counterexamples to unrepaired source claims

This module records concrete finite-chain obstructions found while checking the
paper statements.  In particular, Proposition 3, Part 1 cannot hold for every
service-token distribution without a limited-flexibility hypothesis.
-/

open scoped BigOperators

namespace StateDepMOR.SourceCounterexamples

/-- The connected one-buffer, one-server network with full compatibility. -/
def oneBufferNetwork : Network Unit Unit where
  compatible := fun _ _ => True
  compatibleDecidable := fun _ _ => inferInstance
  buffer_has_neighbor := fun _ => Exists.intro () True.intro
  server_has_neighbor := fun _ => Exists.intro () True.intro
  phi := fun _ _ => 1
  phi_nonneg := fun _ _ => zero_le_one
  server_rate_pos := by
    intro j
    simp
  total_rate := by
    simp

theorem oneBufferNetwork_connected : oneBufferNetwork.IsConnected := by
  intro src dst
  exact Relation.ReflTransGen.refl

theorem oneBufferNetwork_not_limited :
    Not oneBufferNetwork.HasLimitedFlexibility := by
  rintro ⟨j, k, hincompatible, _⟩
  exact hincompatible True.intro

/-- With positive population, always serving the unique buffer is legal and
does not inspect the state. -/
def oneBufferPolicy : oneBufferNetwork.DeterministicPolicySequence :=
  fun K =>
    { action := fun _ _ _ => some ()
      legal := by
        intro x j k
        change True /\ 0 < x ()
        constructor
        · trivial
        · have hx : x () = (K : Nat) := by
            simpa using x.total_jobs
          rw [hx]
          exact K.pos }

@[simp]
theorem oneBufferPolicy_apply
    (K : PNat) (x : JobState Unit (K : Nat)) (j k : Unit) :
    oneBufferPolicy K x j k = some () :=
  rfl

theorem oneBufferPolicy_state_independent :
    forall (K : PNat) (x y : JobState Unit (K : Nat)) (j k : Unit),
      oneBufferPolicy K x j k = oneBufferPolicy K y j k := by
  intros
  rfl

@[simp]
theorem oneBuffer_wasteIndicator_eq_zero
    (K : PNat) (x : JobState Unit (K : Nat))
    (jk : Network.TokenType (Buffer := Unit) (Server := Unit)) :
    oneBufferNetwork.wasteIndicator (oneBufferPolicy K) x jk = 0 := by
  simp [Network.wasteIndicator]

@[simp]
theorem oneBuffer_oneStepWaste_eq_zero
    (K : PNat) (x : JobState Unit (K : Nat)) :
    oneBufferNetwork.oneStepWaste (oneBufferPolicy K) x = 0 := by
  unfold Network.oneStepWaste
  apply Finset.sum_eq_zero
  intro jk hjk
  rw [oneBuffer_wasteIndicator_eq_zero]
  simp

@[simp]
theorem oneBuffer_stationaryWaste_eq_zero
    (K : PNat) (pi : PMF (JobState Unit (K : Nat))) :
    oneBufferNetwork.stationaryOneStepWaste (oneBufferPolicy K) pi = 0 := by
  unfold Network.stationaryOneStepWaste
  apply Finset.sum_eq_zero
  intro x hx
  rw [oneBuffer_oneStepWaste_eq_zero]
  simp

@[simp]
theorem oneBuffer_canonicalLoss_eq_zero (K : PNat) :
    (ConcretePerformance.canonical oneBufferNetwork).loss oneBufferPolicy K = 0 := by
  rw [ConcretePerformance.loss_eq_stationaryOneStepWaste]
  exact oneBuffer_stationaryWaste_eq_zero K _

/-- The concrete loss of this state-independent policy is not
`Omega(1 / K^2)`, contrary to Proposition 3, Part 1 as printed. -/
theorem oneBuffer_loss_not_omega :
    Not (IsOmegaOneDivSq
      (fun K =>
        (ConcretePerformance.canonical oneBufferNetwork).loss
          oneBufferPolicy K)) := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨K, hK⟩ := hbound.exists
  change
    c / ((K : Real) ^ 2) <=
      (ConcretePerformance.canonical oneBufferNetwork).loss
        oneBufferPolicy K at hK
  rw [oneBuffer_canonicalLoss_eq_zero] at hK
  have hKpos : 0 < (K : Real) := by
    exact_mod_cast K.pos
  have hquot : 0 < c / ((K : Real) ^ 2) :=
    div_pos hc (sq_pos_of_pos hKpos)
  linarith

end StateDepMOR.SourceCounterexamples
