import StateDepMOR.AchievabilityAssembly

/-!
# Unconditional achievability statement

This module closes the paper-facing achievability bound.  A long calendar
block supplies a one-step return estimate, repeated blocks supply the
renewal power, and one common horizon controls every possible last-near
excursion.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : StateDepMOR.Network Buffer Server)

/-- The unconditional rate bound stated in the repaired paper. -/
theorem achievabilityBoundStatement_proved
    (N : StateDepMOR.Network Buffer Server) :
    AchievabilityBoundStatement N := by
  intro alpha halpha U hnonidle hnegative T hT
  apply ereal_le_of_forall_real_lt
  intro d hdGamma
  by_cases hd : 0 < d
  · obtain ⟨c, hcpos, hdc, hcGamma⟩ :=
      exists_larger_positive_real_below_ereal hd hdGamma
    obtain ⟨rho, hrhopos, hrhoOne, hdExcursion⟩ :=
      exists_excursion_radius hd hdc
    let delta : Real := rho / 2
    have hdelta : 0 < delta := by
      dsimp only [delta]
      linarith
    have hdeltarho : delta < rho := by
      dsimp only [delta]
      linarith
    let e : Real := c * (rho - delta) / 2
    have he : 0 < e := by
      dsimp only [e]
      positivity
    have heExcursion : e < c * (rho - delta) := by
      have hcost : 0 < c * (rho - delta) :=
        mul_pos hcpos (sub_pos.mpr hdeltarho)
      dsimp only [e]
      linarith
    obtain ⟨r, hr⟩ := exists_nat_gt (d / e)
    have hrpos : 0 < r := by
      have hcast : (0 : Real) < (r : Real) :=
        (div_pos hd he).trans hr
      exact_mod_cast hcast
    have hdr : d < (r : Real) * e := by
      have hmul := mul_lt_mul_of_pos_right hr he
      calc
        d = (d / e) * e := by field_simp [ne_of_gt he]
        _ < (r : Real) * e := hmul
    obtain ⟨a, ha, b, haction⟩ :=
      exists_finiteCalendarReturnFailure_varying_upper
        N alpha halpha U hnegative hT hcpos hcGamma
          hdelta hdeltarho
    obtain ⟨H, hH, hTH, hePersistence⟩ :=
      exists_horizon_affine_cost_gt
        (a := a) (b := b) (d := e) (T := T) ha
    let Hstar : Real := ((r + 1 : Nat) : Real) * H
    have hHHstar : H <= Hstar := by
      have hrOne : (1 : Real) <= ((r + 1 : Nat) : Real) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
      dsimp only [Hstar]
      nlinarith
    have hHstar : 0 < Hstar := hH.trans_le hHHstar
    have hTHstar : T <= Hstar := hTH.trans hHHstar
    let p : PNat -> Real :=
      calendarVaryingEventMass N Hstar
        (finiteCalendarExcursionHitEvent
          N alpha U rho Hstar)
    let q : PNat -> Real :=
      calendarVaryingEventMass N H
        (finiteCalendarReturnFailureEvent
          N alpha U rho H)
    have hpNonneg : forall K, 0 <= p K := by
      intro K
      simpa only [p] using
        calendarVaryingEventMass_nonnegative
          N Hstar
            (finiteCalendarExcursionHitEvent
              N alpha U rho Hstar) K
    have hpOne : forall K, p K <= 1 := by
      intro K
      simpa only [p] using
        calendarVaryingEventMass_le_one
          N hHstar
            (finiteCalendarExcursionHitEvent
              N alpha U rho Hstar) K
    have hqNonneg : forall K, 0 <= q K := by
      intro K
      simpa only [q] using
        calendarVaryingEventMass_nonnegative
          N H
            (finiteCalendarReturnFailureEvent
              N alpha U rho H) K
    have hqOne : forall K, q K <= 1 := by
      intro K
      simpa only [q] using
        calendarVaryingEventMass_le_one
          N hH
            (finiteCalendarReturnFailureEvent
              N alpha U rho H) K
    have hpRate :
        limsup (scaledLogLossPNat p) atTop <= -(d : EReal) := by
      simpa only [p] using
        calendarExcursionHitMass_limsup_le
          N alpha halpha U hT hTHstar hrhoOne hcpos hcGamma
            hd.le hdExcursion
    have hqRate :
        limsup (scaledLogLossPNat q) atTop <= -(e : EReal) := by
      simpa only [q] using
        calendarReturnFailureMass_limsup_le
          N alpha halpha U hnegative hT hcpos hcGamma
            hdelta hdeltarho haction hTH he.le
            heExcursion hePersistence
    have hfinite :
        forall K,
          N.minimumInvariantLossFamily U K <=
            ((r + 1 : Nat) : Real) * p K + (q K) ^ r := by
      intro K
      obtain ⟨n, rfl⟩ : exists n : Nat, n.succPNat = K :=
        ⟨K.natPred, PNat.succPNat_natPred K⟩
      classical
      let Near : JobState Buffer (n.succPNat : Nat) -> Prop :=
        fun x =>
          Lyapunov.LAlpha alpha
            (normalizedQueueState n.succPNat x) <= rho
      apply minimumInvariantLoss_le_excursions_add_pow_persistence
        N U hnonidle n.succPNat
          (calendarBlockCountLaw n.succPNat H)
          Near (p n.succPNat) (q n.succPNat)
            (hpNonneg n.succPNat) (hqNonneg n.succPNat) r
      · intro m hm hmle x hx
        rw [
          kernelIterate_randomizedEventEpochKernel_calendarBlockCountLaw
            N hH n.succPNat (U n.succPNat) m x]
        rw [
          pmfEventMass_randomizedEventEpochKernel_eq_calendarBlockEndpoint
            N (mul_pos (Nat.cast_pos.mpr hm) hH)
              n.succPNat (U n.succPNat) x
              StateDepMOR.Achievability.Network.IsQueueBoundary]
        have htimeNonneg : 0 <= (m : Real) * H :=
          mul_nonneg (Nat.cast_nonneg m) hH.le
        have htimeLe : (m : Real) * H <= Hstar := by
          have hmcast :
              (m : Real) <= ((r + 1 : Nat) : Real) := by
            exact_mod_cast hmle
          dsimp only [Hstar]
          exact mul_le_mul_of_nonneg_right hmcast hH.le
        have htime :
            Membership.mem (Set.Icc (0 : Real) Hstar)
              ((m : Real) * H) :=
          And.intro htimeNonneg htimeLe
        have hxNear :
            Lyapunov.LAlpha alpha
              (normalizedQueueState n.succPNat x) <= rho := by
          exact hx
        simpa only [p, calendarVaryingEventMass, measureReal_def,
          Nat.natPred_succPNat, Nat.succPNat_coe] using
          calendarBlockEndpoint_boundary_real_le_excursionHit
            N alpha halpha U rho hHstar htime n x hxNear
      · intro x
        rw [
          pmfEventMass_randomizedEventEpochKernel_eq_calendarBlockEndpoint
            N hH n.succPNat (U n.succPNat) x
              (fun y => Not (Near y))]
        simpa only [q, calendarVaryingEventMass, Near, measureReal_def,
          Nat.natPred_succPNat, Nat.succPNat_coe] using
          calendarBlockEndpoint_notNear_real_le_returnFailure
            N alpha U rho hH n x
    have hbound :
        forall K,
          N.minimumInvariantLossFamily U K <=
            ((r + 2 : Nat) : Real) *
              max (p K) ((q K) ^ r) := by
      intro K
      calc
        N.minimumInvariantLossFamily U K <=
            ((r + 1 : Nat) : Real) * p K + (q K) ^ r :=
          hfinite K
        _ <= ((r + 1 : Nat) : Real) *
              max (p K) ((q K) ^ r) +
              max (p K) ((q K) ^ r) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (le_max_left (p K) ((q K) ^ r)) (by positivity)
          · exact le_max_right (p K) ((q K) ^ r)
        _ = ((r + 2 : Nat) : Real) *
              max (p K) ((q K) ^ r) := by
          push_cast
          ring
    exact
      le_negativeLimsupLogRate_of_le_const_mul_max_pow
        (N.minimumInvariantLossFamily U) p q
        (((r + 2 : Nat) : Real)) r d e
        (by positivity) hrpos hpNonneg hpOne hqNonneg hqOne
        hbound hpRate hqRate hdr.le
  · have hdNonpos : d <= 0 := le_of_not_gt hd
    exact
      (EReal.coe_le_coe_iff.mpr hdNonpos).trans
        (negativeLimsupLogRate_nonnegative_of_le_one
          (N.minimumInvariantLossFamily U)
          (N.minimumInvariantLossFamily_le_one U))

#print axioms achievabilityBoundStatement_proved

end StateDepMOR.PaperStatements.Network
