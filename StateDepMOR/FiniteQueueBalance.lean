import StateDepMOR.FiniteQueueChain
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Stationary balance for the finite queue chain

This module develops expectation identities for the event-epoch chain and
the elementary cut balance behind the strict-imbalance case of Proposition 2.
-/

open scoped BigOperators ENNReal

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace PMF

theorem sum_map_real
    {Alpha Beta : Type*} [Fintype Alpha] [Fintype Beta]
    (p : PMF Alpha) (f : Alpha -> Beta) (g : Beta -> Real) :
    (Finset.univ.sum fun b => (p.map f b).toReal * g b) =
      Finset.univ.sum fun a => (p a).toReal * g (f a) := by
  letI : MeasurableSpace Alpha := Top.top
  letI : MeasurableSpace Beta := Top.top
  calc
    (Finset.univ.sum fun b => (p.map f b).toReal * g b) =
        MeasureTheory.integral (p.map f).toMeasure g := by
          rw [PMF.integral_eq_sum]
          simp only [smul_eq_mul]
    _ = MeasureTheory.integral p.toMeasure (fun a => g (f a)) := by
          rw [<- PMF.toMeasure_map f p (measurable_of_finite f)]
          exact MeasureTheory.integral_map
            (measurable_of_finite f).aemeasurable
            (measurable_of_finite g).aestronglyMeasurable
    _ = Finset.univ.sum fun a => (p a).toReal * g (f a) := by
          rw [PMF.integral_eq_sum]
          simp only [smul_eq_mul]

theorem sum_bind_real
    {Alpha Beta : Type*} [Fintype Alpha] [Fintype Beta]
    (p : PMF Alpha) (q : Alpha -> PMF Beta) (g : Beta -> Real) :
    (Finset.univ.sum fun b => (p.bind q b).toReal * g b) =
      Finset.univ.sum fun a =>
        (p a).toReal *
          (Finset.univ.sum fun b => (q a b).toReal * g b) := by
  classical
  simp only [PMF.bind_apply, tsum_fintype]
  conv_lhs =>
    enter [2, b]
    rw [ENNReal.toReal_sum (fun a _ =>
      ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b))]
  simp_rw [ENNReal.toReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum, mul_assoc]

theorem sum_toReal {Alpha : Type*} [Fintype Alpha] (p : PMF Alpha) :
    Finset.univ.sum (fun a => (p a).toReal) = 1 := by
  have hsum : Finset.univ.sum (fun a => p a) = 1 := by
    simpa only [tsum_fintype] using p.tsum_coe
  rw [<- ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  rw [hsum]
  norm_num

end PMF

namespace JobState

/-- The number of jobs in a set of buffers, viewed as a real number. -/
noncomputable def jobsIn {K : Nat} (x : JobState Buffer K)
    (s : Finset Buffer) : Real :=
  s.sum fun i => (x i : Real)

private noncomputable def realSum (f : Buffer -> Nat)
    (s : Finset Buffer) : Real :=
  s.sum fun i => (f i : Real)

private theorem realSum_update_sub (f : Buffer -> Nat) (a : Buffer)
    (n : Nat) (s : Finset Buffer) :
    realSum (Function.update f a n) s - realSum f s =
      if a ∈ s then (n : Real) - f a else 0 := by
  classical
  by_cases ha : a ∈ s
  · rw [if_pos ha]
    have hfun : (fun i => ((Function.update f a n) i : Real)) =
        Function.update (fun i => (f i : Real)) a (n : Real) := by
      funext i
      by_cases hia : i = a <;> simp [Function.update, hia]
    unfold realSum
    rw [hfun, Finset.sum_update_of_mem ha]
    have horig := Finset.sum_erase_add s (fun i => (f i : Real)) ha
    rw [Finset.sdiff_singleton_eq_erase]
    linarith
  · rw [if_neg ha]
    unfold realSum
    have heq : s.sum (fun i => ((Function.update f a n) i : Real)) =
        s.sum (fun i => (f i : Real)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hia : Ne i a := by
        intro h
        subst i
        exact ha hi
      simp [Function.update, hia]
    rw [heq]
    norm_num

theorem jobsIn_moveJob {K : Nat} (x : JobState Buffer K)
    (src dst : Buffer) (hsrc : 0 < x src) (s : Finset Buffer) :
    jobsIn (x.moveJob src dst hsrc) s - jobsIn x s =
      (if dst ∈ s then 1 else 0) - (if src ∈ s then 1 else 0) := by
  classical
  unfold jobsIn JobState.moveJob
  let dep := Function.update x.jobs src (x src - 1)
  have hfirst := realSum_update_sub x.jobs src (x src - 1) s
  have hsecond := realSum_update_sub dep dst (dep dst + 1) s
  change
    realSum (Function.update dep dst (dep dst + 1)) s -
        realSum x.jobs s = _
  rw [show
    realSum (Function.update dep dst (dep dst + 1)) s -
        realSum x.jobs s =
      (realSum (Function.update dep dst (dep dst + 1)) s -
          realSum dep s) +
        (realSum dep s - realSum x.jobs s) by ring]
  rw [hsecond, hfirst]
  by_cases hdst : dst ∈ s <;> by_cases hsrcs : src ∈ s
  all_goals simp only [hdst, hsrcs, if_true, if_false]
  all_goals simp [dep, Function.update, hsrc]

end JobState

namespace Network

variable (N : Network Buffer Server)

/-- Real indicator that the current token is used. -/
def usedIndicator {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) : Real :=
  if U x jk.1 jk.2 = none then 0 else 1

/-- Indicator that a token originates in a server set. -/
def tokenOriginIn (_N : Network Buffer Server) (jset : Finset Server)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) : Real :=
  if jk.1 ∈ jset then 1 else 0

/-- Indicator that a token's destination belongs to a buffer set. -/
def tokenDestinationIn (_N : Network Buffer Server) (s : Finset Buffer)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) : Real :=
  if jk.2 ∈ s then 1 else 0

/-- Change in jobs in `s` caused by one token. -/
def cutChange {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (s : Finset Buffer)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) : Real :=
  match U x jk.1 jk.2 with
  | none => 0
  | some i =>
      (if jk.2 ∈ s then 1 else 0) - (if i ∈ s then 1 else 0)

theorem jobsIn_queueStep_sub {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (s : Finset Buffer)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    JobState.jobsIn (N.queueStep U x jk) s - JobState.jobsIn x s =
      N.cutChange U x s jk := by
  classical
  unfold queueStep cutChange
  split <;> rename_i haction
  · simp [haction]
  · rename_i i
    have hmove := JobState.jobsIn_moveJob x i jk.2
      (by
        have hlegal := U.legal x jk.1 jk.2
        rw [haction] at hlegal
        exact hlegal.2) s
    simpa [haction] using hmove

/-- The one-token cut inequality used in the stationary Hall bound. -/
theorem waste_ge_origin_sub_destination_add_cutChange
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (jset : Finset Server)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    N.tokenOriginIn jset jk - N.tokenDestinationIn (N.neighborhood jset) jk +
        N.cutChange U x (N.neighborhood jset) jk <=
      N.wasteIndicator U x jk := by
  classical
  cases haction : U x jk.1 jk.2 with
  | none =>
      unfold tokenOriginIn tokenDestinationIn cutChange wasteIndicator
      simp [haction]
      split <;> split <;> norm_num
  | some i =>
      have hlegal := U.legal x jk.1 jk.2
      rw [haction] at hlegal
      have horigin :
          jk.1 ∈ jset -> i ∈ N.neighborhood jset := by
        intro hj
        exact (N.mem_neighborhood jset i).2
          ⟨jk.1, hj, hlegal.1⟩
      unfold tokenOriginIn tokenDestinationIn cutChange wasteIndicator
      simp only [haction, reduceCtorEq, if_false]
      by_cases hj : jk.1 ∈ jset
      · have hi := horigin hj
        simp [hj, hi]
      · by_cases hi : i ∈ N.neighborhood jset <;> simp [hj, hi]

theorem stationary_expectation
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (hpi : N.IsInvariantPMF U pi)
    (g : JobState Buffer K -> Real) :
    (Finset.univ.sum fun x =>
      (pi x).toReal *
        (Finset.univ.sum fun jk =>
          (N.tokenLaw jk).toReal * g (N.queueStep U x jk))) =
      Finset.univ.sum fun x => (pi x).toReal * g x := by
  have hinv := congrArg
    (fun p : PMF (JobState Buffer K) =>
      Finset.univ.sum fun x => (p x).toReal * g x) hpi
  rw [PMF.sum_bind_real] at hinv
  simpa only [transitionPMF, PMF.sum_map_real] using hinv

theorem stationary_expected_cutChange_eq_zero
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (hpi : N.IsInvariantPMF U pi)
    (s : Finset Buffer) :
    Finset.univ.sum (fun x =>
      (pi x).toReal *
        Finset.univ.sum (fun jk =>
          (N.tokenLaw jk).toReal * N.cutChange U x s jk)) = 0 := by
  have hstationary :=
    N.stationary_expectation U pi hpi (fun x => JobState.jobsIn x s)
  have hdiff :
      Finset.univ.sum (fun x =>
        (pi x).toReal *
          Finset.univ.sum (fun jk =>
            (N.tokenLaw jk).toReal *
              (JobState.jobsIn (N.queueStep U x jk) s -
                JobState.jobsIn x s))) = 0 := by
    calc
      Finset.univ.sum (fun x =>
          (pi x).toReal *
            Finset.univ.sum (fun jk =>
              (N.tokenLaw jk).toReal *
                (JobState.jobsIn (N.queueStep U x jk) s -
                  JobState.jobsIn x s))) =
          Finset.univ.sum (fun x =>
            (pi x).toReal *
                Finset.univ.sum (fun jk =>
                  (N.tokenLaw jk).toReal *
                    JobState.jobsIn (N.queueStep U x jk) s) -
              (pi x).toReal * JobState.jobsIn x s) := by
                apply Finset.sum_congr rfl
                intro x _
                rw [<- mul_sub]
                congr 1
                calc
                  Finset.univ.sum (fun jk =>
                      (N.tokenLaw jk).toReal *
                        (JobState.jobsIn (N.queueStep U x jk) s -
                          JobState.jobsIn x s)) =
                      Finset.univ.sum (fun jk =>
                        (N.tokenLaw jk).toReal *
                            JobState.jobsIn (N.queueStep U x jk) s -
                          (N.tokenLaw jk).toReal *
                            JobState.jobsIn x s) := by
                              apply Finset.sum_congr rfl
                              intro jk _
                              ring
                  _ = Finset.univ.sum (fun jk =>
                        (N.tokenLaw jk).toReal *
                          JobState.jobsIn (N.queueStep U x jk) s) -
                      Finset.univ.sum (fun jk =>
                        (N.tokenLaw jk).toReal *
                          JobState.jobsIn x s) := by
                            rw [Finset.sum_sub_distrib]
                  _ = Finset.univ.sum (fun jk =>
                        (N.tokenLaw jk).toReal *
                          JobState.jobsIn (N.queueStep U x jk) s) -
                      JobState.jobsIn x s := by
                        rw [<- Finset.sum_mul, PMF.sum_toReal]
                        simp
      _ = (Finset.univ.sum (fun x =>
            (pi x).toReal *
              Finset.univ.sum (fun jk =>
                (N.tokenLaw jk).toReal *
                  JobState.jobsIn (N.queueStep U x jk) s))) -
          Finset.univ.sum (fun x =>
            (pi x).toReal * JobState.jobsIn x s) := by
              rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hstationary
  simpa only [N.jobsIn_queueStep_sub U] using hdiff

/-- Stationary waste is bounded below by the token-origin mass of `jset`
minus the token-destination mass of its neighborhood. -/
theorem stationaryOneStepWaste_ge_origin_sub_destination
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (hpi : N.IsInvariantPMF U pi)
    (jset : Finset Server) :
    (Finset.univ.sum fun jk =>
        (N.tokenLaw jk).toReal *
          (N.tokenOriginIn jset jk -
            N.tokenDestinationIn (N.neighborhood jset) jk)) <=
      N.stationaryOneStepWaste U pi := by
  let base : Real :=
    Finset.univ.sum fun jk =>
      (N.tokenLaw jk).toReal *
        (N.tokenOriginIn jset jk -
          N.tokenDestinationIn (N.neighborhood jset) jk)
  let cutAt : JobState Buffer K -> Real := fun x =>
    Finset.univ.sum fun jk =>
      (N.tokenLaw jk).toReal *
        N.cutChange U x (N.neighborhood jset) jk
  have hcut :
      Finset.univ.sum (fun x => (pi x).toReal * cutAt x) = 0 := by
    exact N.stationary_expected_cutChange_eq_zero U pi hpi
      (N.neighborhood jset)
  have hdecomp (x : JobState Buffer K) :
      Finset.univ.sum (fun jk =>
          (N.tokenLaw jk).toReal *
            (N.tokenOriginIn jset jk -
              N.tokenDestinationIn (N.neighborhood jset) jk +
              N.cutChange U x (N.neighborhood jset) jk)) =
        base + cutAt x := by
    unfold base cutAt
    rw [<- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro jk _
    ring
  have hlower :
      Finset.univ.sum (fun x =>
          (pi x).toReal *
            Finset.univ.sum (fun jk =>
              (N.tokenLaw jk).toReal *
                (N.tokenOriginIn jset jk -
                  N.tokenDestinationIn (N.neighborhood jset) jk +
                  N.cutChange U x (N.neighborhood jset) jk))) <=
        N.stationaryOneStepWaste U pi := by
    unfold stationaryOneStepWaste oneStepWaste
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro jk _
      apply mul_le_mul_of_nonneg_left
      · exact N.waste_ge_origin_sub_destination_add_cutChange U x jset jk
      · exact ENNReal.toReal_nonneg
    · exact ENNReal.toReal_nonneg
  have hleft :
      Finset.univ.sum (fun x =>
          (pi x).toReal *
            Finset.univ.sum (fun jk =>
              (N.tokenLaw jk).toReal *
                (N.tokenOriginIn jset jk -
                  N.tokenDestinationIn (N.neighborhood jset) jk +
                  N.cutChange U x (N.neighborhood jset) jk))) =
        base := by
    simp_rw [hdecomp, mul_add]
    rw [Finset.sum_add_distrib, hcut]
    rw [<- Finset.sum_mul, PMF.sum_toReal]
    simp
  change base <= N.stationaryOneStepWaste U pi
  rw [<- hleft]
  exact hlower

/-- The token-origin-minus-destination expression is exactly
`mu_J - lambda_J`. -/
theorem tokenOriginSubDestination_eq_netImbalance
    (jset : Finset Server) :
    (Finset.univ.sum fun jk =>
        (N.tokenLaw jk).toReal *
          (N.tokenOriginIn jset jk -
            N.tokenDestinationIn (N.neighborhood jset) jk)) =
      N.netServiceRate jset - N.netArrivalRate jset := by
  classical
  have hindicator :
      (Finset.univ.sum fun jk :
          TokenType (Buffer := Buffer) (Server := Server) =>
        (N.tokenLaw jk).toReal *
          (N.tokenOriginIn jset jk -
            N.tokenDestinationIn (N.neighborhood jset) jk)) =
        jset.sum (fun j => Finset.univ.sum (fun k => N.phi j k)) -
          Finset.univ.sum (fun j =>
            (N.neighborhood jset).sum (fun k => N.phi j k)) := by
    simp only [N.tokenLaw_toReal, tokenOriginIn, tokenDestinationIn,
      Fintype.sum_prod_type]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    congr 1
    · calc
        Finset.univ.sum (fun j =>
            Finset.univ.sum (fun k =>
              N.phi j k * if j ∈ jset then 1 else 0)) =
            Finset.univ.sum (fun j =>
              if j ∈ jset then
                Finset.univ.sum (fun k => N.phi j k)
              else 0) := by
                apply Finset.sum_congr rfl
                intro j _
                by_cases hj : j ∈ jset <;> simp [hj]
        _ = jset.sum (fun j =>
              Finset.univ.sum (fun k => N.phi j k)) := by
                rw [<- Finset.sum_filter]
                simp only [Finset.filter_mem_eq_inter,
                  Finset.univ_inter]
    · apply Finset.sum_congr rfl
      intro j _
      calc
        Finset.univ.sum (fun k =>
            N.phi j k *
              if k ∈ N.neighborhood jset then 1 else 0) =
            Finset.univ.sum (fun k =>
              if k ∈ N.neighborhood jset then N.phi j k else 0) := by
                apply Finset.sum_congr rfl
                intro k _
                by_cases hk : k ∈ N.neighborhood jset <;> simp [hk]
        _ = (N.neighborhood jset).sum
              (fun k => N.phi j k) := by
                rw [<- Finset.sum_filter]
                simp only [Finset.filter_mem_eq_inter,
                  Finset.univ_inter]
  let inner : Real :=
    jset.sum (fun j =>
      (N.neighborhood jset).sum (fun k => N.phi j k))
  have hrow (j : Server) :
      (N.neighborhood jset).sum (fun k => N.phi j k) +
          (Finset.univ.filter fun k =>
            k ∉ N.neighborhood jset).sum (fun k => N.phi j k) =
        Finset.univ.sum (fun k => N.phi j k) := by
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k => k ∈ N.neighborhood jset) (fun k => N.phi j k))
  have hserver :
      jset.sum (fun j =>
          (N.neighborhood jset).sum (fun k => N.phi j k)) +
          (Finset.univ.filter fun j => j ∉ jset).sum (fun j =>
            (N.neighborhood jset).sum (fun k => N.phi j k)) =
        Finset.univ.sum (fun j =>
          (N.neighborhood jset).sum (fun k => N.phi j k)) := by
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j => j ∈ jset)
        (fun j =>
          (N.neighborhood jset).sum (fun k => N.phi j k)))
  have horigin :
      jset.sum (fun j => Finset.univ.sum (fun k => N.phi j k)) =
        inner + N.netServiceRate jset := by
    unfold inner netServiceRate
    rw [<- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact (hrow j).symm
  have hdestination :
      Finset.univ.sum (fun j =>
          (N.neighborhood jset).sum (fun k => N.phi j k)) =
        inner + N.netArrivalRate jset := by
    unfold inner netArrivalRate
    exact hserver.symm
  rw [hindicator, horigin, hdestination]
  ring

/-- Strict demand/supply imbalance forces a matching stationary loss under
every deterministic stationary policy and every invariant law. -/
theorem stationaryOneStepWaste_ge_netImbalance
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (hpi : N.IsInvariantPMF U pi)
    (jset : Finset Server) :
    N.netServiceRate jset - N.netArrivalRate jset <=
      N.stationaryOneStepWaste U pi := by
  rw [<- N.tokenOriginSubDestination_eq_netImbalance jset]
  exact N.stationaryOneStepWaste_ge_origin_sub_destination U pi hpi jset

end Network

end StateDepMOR
