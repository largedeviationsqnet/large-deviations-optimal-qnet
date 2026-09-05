import StateDepMOR.ConcretePerformance

/-!
# Initial-state dependence of stationary waste

The source's long-run loss cannot be represented by an arbitrary invariant PMF
for a fixed policy.  This concrete connected network has one policy with two
absorbing states whose stationary waste rates differ.
-/

open scoped BigOperators

namespace StateDepMOR.InvariantSelectionCounterexample

/-- One fully flexible server, two buffers, and unequal destination masses. -/
noncomputable def twoBufferNetwork : Network Bool Unit where
  compatible := fun _ _ => True
  compatibleDecidable := fun _ _ => inferInstance
  buffer_has_neighbor := fun _ => Exists.intro () True.intro
  server_has_neighbor := fun _ => Exists.intro false True.intro
  phi := fun _ k => if k then (2 : Real) / 3 else (1 : Real) / 3
  phi_nonneg := by
    intro j k
    cases k <;> norm_num
  server_rate_pos := by
    intro j
    rw [Fintype.sum_bool]
    norm_num
  total_rate := by
    simp only [Fintype.sum_unique, Fintype.sum_bool]
    norm_num

theorem twoBufferNetwork_connected : twoBufferNetwork.IsConnected := by
  intro src dst
  apply Relation.ReflTransGen.single
  refine ⟨(), True.intro, ?_⟩
  cases dst <;> norm_num [twoBufferNetwork]

def falseState : JobState Bool 1 where
  jobs := fun i => if i = false then 1 else 0
  total_jobs := by
    rw [Fintype.sum_bool]
    simp

def trueState : JobState Bool 1 where
  jobs := fun i => if i = true then 1 else 0
  total_jobs := by
    rw [Fintype.sum_bool]
    simp

/-- Serve exactly when the token destination is currently occupied.  Since
there is one job, every successful service is a self-loop. -/
def selfDestinationPolicy :
    twoBufferNetwork.DeterministicStationaryPolicy 1 where
  action := fun x _ k => if 0 < x k then some k else none
  legal := by
    intro x j k
    by_cases hk : 0 < x k
    · simp [Network.IsLegalAction, hk, twoBufferNetwork]
    · simp [Network.IsLegalAction, hk]

theorem moveJob_self {Buffer : Type*} [Fintype Buffer] [DecidableEq Buffer]
    {K : Nat} (x : JobState Buffer K) (i : Buffer) (hi : 0 < x i) :
    x.moveJob i i hi = x := by
  apply JobState.ext
  funext q
  by_cases hqi : q = i
  · subst q
    simp [JobState.moveJob, Function.update,
      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt hi))]
  · simp [JobState.moveJob, Function.update, hqi]

theorem queueStep_eq_self
    (x : JobState Bool 1)
    (jk : Network.TokenType (Buffer := Bool) (Server := Unit)) :
    twoBufferNetwork.queueStep selfDestinationPolicy x jk = x := by
  unfold Network.queueStep
  split
  · rfl
  · rename_i i hsome
    have hk : 0 < x jk.2 := by
      by_contra hnot
      simp [selfDestinationPolicy, hnot] at hsome
    have hi : jk.2 = i := by
      simpa [selfDestinationPolicy, hk] using hsome
    subst i
    exact moveJob_self x jk.2 hk

theorem transitionPMF_eq_pure (x : JobState Bool 1) :
    twoBufferNetwork.transitionPMF selfDestinationPolicy x = PMF.pure x := by
  rw [Network.transitionPMF]
  have hstep :
      twoBufferNetwork.queueStep selfDestinationPolicy x =
        Function.const
          (Network.TokenType (Buffer := Bool) (Server := Unit)) x := by
    funext jk
    exact queueStep_eq_self x jk
  rw [hstep, PMF.map_const]

theorem pure_isInvariant (x : JobState Bool 1) :
    twoBufferNetwork.IsInvariantPMF selfDestinationPolicy (PMF.pure x) := by
  unfold Network.IsInvariantPMF
  rw [PMF.pure_bind, transitionPMF_eq_pure]

@[simp]
theorem oneStepWaste_falseState :
    twoBufferNetwork.oneStepWaste selfDestinationPolicy falseState =
      (2 : Real) / 3 := by
  simp [Network.oneStepWaste, Network.wasteIndicator,
    selfDestinationPolicy, falseState, twoBufferNetwork,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

@[simp]
theorem oneStepWaste_trueState :
    twoBufferNetwork.oneStepWaste selfDestinationPolicy trueState =
      (1 : Real) / 3 := by
  simp [Network.oneStepWaste, Network.wasteIndicator,
    selfDestinationPolicy, trueState, twoBufferNetwork,
    Fintype.sum_prod_type, Fintype.sum_bool]

theorem stationaryWaste_pure_falseState :
    twoBufferNetwork.stationaryOneStepWaste selfDestinationPolicy
      (PMF.pure falseState) =
      (2 : Real) / 3 := by
  unfold Network.stationaryOneStepWaste
  rw [Finset.sum_eq_single falseState]
  · simp
  · intro x hx hne
    simp [PMF.pure_apply, hne]
  · simp

theorem stationaryWaste_pure_trueState :
    twoBufferNetwork.stationaryOneStepWaste selfDestinationPolicy
      (PMF.pure trueState) =
      (1 : Real) / 3 := by
  unfold Network.stationaryOneStepWaste
  rw [Finset.sum_eq_single trueState]
  · simp
  · intro x hx hne
    simp [PMF.pure_apply, hne]
  · simp

theorem invariant_stationary_waste_not_unique :
    exists pi1 pi2 : PMF (JobState Bool 1),
      twoBufferNetwork.IsInvariantPMF selfDestinationPolicy pi1 /\
      twoBufferNetwork.IsInvariantPMF selfDestinationPolicy pi2 /\
      Not
        (twoBufferNetwork.stationaryOneStepWaste selfDestinationPolicy pi1 =
          twoBufferNetwork.stationaryOneStepWaste selfDestinationPolicy pi2) := by
  refine ⟨PMF.pure falseState, PMF.pure trueState,
    pure_isInvariant falseState, pure_isInvariant trueState, ?_⟩
  rw [stationaryWaste_pure_falseState, stationaryWaste_pure_trueState]
  norm_num

end StateDepMOR.InvariantSelectionCounterexample
