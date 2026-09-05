import StateDepMOR.AchievabilityCalendarBridge

/-!
# Semigroup law for Poissonized event-epoch kernels

This module proves that iterating the event-epoch kernel Poissonized over a
calendar block of length `H` is the same as Poissonizing once over the total
length.  The proof includes the zero-iteration case: both sides reduce to the
identity kernel because the total Poisson parameter is zero.
-/

open MeasureTheory ProbabilityTheory

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : StateDepMOR.Network Buffer Server)

/-- Convolution of two natural-valued PMFs, represented by independently
drawing one value from each PMF and adding them. -/
noncomputable def natAddConvolution (p q : PMF Nat) : PMF Nat :=
  p.bind fun n => q.map fun k => n + k

/-- PMF addition agrees with additive convolution of the associated
measures. -/
theorem natAddConvolution_toMeasure (p q : PMF Nat) :
    (natAddConvolution p q).toMeasure =
      Measure.conv p.toMeasure q.toMeasure := by
  apply Measure.ext
  intro s hs
  unfold natAddConvolution
  rw [PMF.toMeasure_bind_apply _ _ _ hs]
  rw [<- MeasureTheory.lintegral_indicator_one hs,
    Measure.lintegral_conv (by measurability)]
  simp_rw [MeasureTheory.lintegral_countable']
  simp_rw [PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton _)]
  apply tsum_congr
  intro n
  rw [PMF.toMeasure_map_apply]
  · rw [PMF.toMeasure_apply_eq_tsum]
    rw [mul_comm (p n)]
    apply congrArg (fun z => z * p n)
    apply tsum_congr
    intro k
    by_cases hmem : n + k ∈ s <;> simp [hmem]
  · measurability
  · exact hs

/-- The sum of two independent Poisson PMFs is Poisson with the sum of the
parameters. -/
theorem poissonPMF_natAddConvolution (r1 r2 : NNReal) :
    natAddConvolution
        (ProbabilityTheory.poissonMeasure r1).toPMF
        (ProbabilityTheory.poissonMeasure r2).toPMF =
      (ProbabilityTheory.poissonMeasure (r1 + r2)).toPMF := by
  rw [<- PMF.toMeasure_inj]
  rw [natAddConvolution_toMeasure]
  simp only [Measure.toPMF_toMeasure]
  exact ProbabilityTheory.poissonMeasure_conv_poissonMeasure r1 r2

omit [Nonempty Buffer] [Nonempty Server] in
/-- Markov evolution has the semigroup law in its event count. -/
theorem nStepLaw_add {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (initial : PMF (JobState Buffer K)) (n k : Nat) :
    N.nStepLaw U (N.nStepLaw U initial n) k =
      N.nStepLaw U initial (n + k) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [N.nStepLaw_succ, ih]
      simpa [Nat.add_assoc] using
        (N.nStepLaw_succ U initial (n + k)).symm

/-- Exact event-count blocks compose by addition of their counts. -/
theorem eventEpochBlockKernel_bind
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (n k : Nat) :
    (eventEpochBlockKernel N U n x).bind
        (eventEpochBlockKernel N U k) =
      eventEpochBlockKernel N U (n + k) x := by
  rw [bind_eventEpochBlockKernel]
  exact nStepLaw_add N U (PMF.pure x) n k

/-- Randomized event-count kernels compose by convolution of their count
laws. -/
theorem randomizedEventEpochKernel_bind
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (p q : PMF Nat) (x : JobState Buffer K) :
    (randomizedEventEpochKernel N U p x).bind
        (randomizedEventEpochKernel N U q) =
      randomizedEventEpochKernel N U (natAddConvolution p q) x := by
  unfold randomizedEventEpochKernel natAddConvolution
  calc
    (p.bind fun n => eventEpochBlockKernel N U n x).bind
        (fun y => q.bind fun k => eventEpochBlockKernel N U k y) =
        p.bind fun n =>
          (eventEpochBlockKernel N U n x).bind
            (fun y => q.bind fun k =>
              eventEpochBlockKernel N U k y) := PMF.bind_bind _ _ _
    _ = p.bind fun n =>
        q.bind fun k => eventEpochBlockKernel N U (n + k) x := by
      apply congrArg
      funext n
      rw [PMF.bind_comm
        (eventEpochBlockKernel N U n x) q
        (fun y k => eventEpochBlockKernel N U k y)]
      apply congrArg
      funext k
      exact eventEpochBlockKernel_bind N U x n k
    _ = (p.bind fun n => q.map fun k => n + k).bind
        (fun n => eventEpochBlockKernel N U n x) := by
      rw [PMF.bind_bind]
      apply congrArg
      funext n
      rw [PMF.bind_map]
      rfl

/-- At nonnegative horizons, adjacent calendar count laws convolve to the
count law of the summed horizon. -/
theorem calendarBlockCountLaw_natAddConvolution
    (K : PNat) {H1 H2 : Real} (hH1 : 0 <= H1) (hH2 : 0 <= H2) :
    natAddConvolution (calendarBlockCountLaw K H1)
        (calendarBlockCountLaw K H2) =
      calendarBlockCountLaw K (H1 + H2) := by
  have hparameter :
      calendarBlockCountParameter K H1 +
          calendarBlockCountParameter K H2 =
        calendarBlockCountParameter K (H1 + H2) := by
    apply NNReal.eq
    change
      ((K : Nat) : Real) * max H1 0 +
          ((K : Nat) : Real) * max H2 0 =
        ((K : Nat) : Real) * max (H1 + H2) 0
    rw [max_eq_left hH1, max_eq_left hH2,
      max_eq_left (add_nonneg hH1 hH2)]
    ring
  rw [calendarBlockCountLaw, calendarBlockCountLaw,
    calendarBlockCountLaw]
  rw [poissonPMF_natAddConvolution]
  rw [hparameter]

/-- One calendar-Poissonized kernel followed by another is the kernel for
the sum of their nonnegative calendar horizons. -/
theorem randomizedEventEpochKernel_calendarBlockCountLaw_bind
    {K : PNat} (U : N.DeterministicStationaryPolicy (K : Nat))
    {H1 H2 : Real} (hH1 : 0 <= H1) (hH2 : 0 <= H2)
    (x : JobState Buffer (K : Nat)) :
    (randomizedEventEpochKernel N U (calendarBlockCountLaw K H1) x).bind
        (randomizedEventEpochKernel N U (calendarBlockCountLaw K H2)) =
      randomizedEventEpochKernel N U
        (calendarBlockCountLaw K (H1 + H2)) x := by
  rw [randomizedEventEpochKernel_bind,
    calendarBlockCountLaw_natAddConvolution K hH1 hH2]

/-- Iterating a positive-length calendar-Poissonized event-epoch kernel
`m` times is exactly one event-epoch kernel with Poisson count for total
horizon `(m : Real) * H`.  This includes `m = 0`, where the total horizon
and Poisson parameter are zero and both sides are the identity kernel. -/
theorem kernelIterate_randomizedEventEpochKernel_calendarBlockCountLaw
    {H : Real} (hH : 0 < H)
    (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (m : Nat) (x : JobState Buffer (K : Nat)) :
    kernelIterate
        (randomizedEventEpochKernel N U (calendarBlockCountLaw K H)) m x =
      randomizedEventEpochKernel N U
        (calendarBlockCountLaw K ((m : Real) * H)) x := by
  induction m generalizing x with
  | zero =>
      simp only [kernelIterate, Nat.cast_zero, zero_mul]
      have hparameter : calendarBlockCountParameter K 0 = 0 := by
        apply NNReal.eq
        change ((K : Nat) : Real) * max (0 : Real) 0 = 0
        simp
      have hcountLaw : calendarBlockCountLaw K 0 = PMF.pure 0 := by
        unfold calendarBlockCountLaw
        have hmeasure :
            ProbabilityTheory.poissonMeasure
                (calendarBlockCountParameter K 0) =
              Measure.dirac 0 := by
          rw [hparameter]
          apply Measure.ext_of_singleton
          intro n
          rw [ProbabilityTheory.poissonMeasure_singleton]
          by_cases hn : n = 0
          · subst n
            simp
          · simp [hn]
        apply PMF.ext
        intro n
        change
          ProbabilityTheory.poissonMeasure
              (calendarBlockCountParameter K 0) {n} =
            PMF.pure 0 n
        rw [hmeasure]
        by_cases hn : n = 0 <;> simp [hn]
      rw [hcountLaw]
      unfold randomizedEventEpochKernel
      rw [PMF.pure_bind]
      rfl
  | succ m ih =>
      rw [show kernelIterate
          (randomizedEventEpochKernel N U (calendarBlockCountLaw K H))
            (m + 1) x =
          (randomizedEventEpochKernel N U
            (calendarBlockCountLaw K H) x).bind
            (kernelIterate
              (randomizedEventEpochKernel N U
                (calendarBlockCountLaw K H)) m) by rfl]
      rw [show kernelIterate
          (randomizedEventEpochKernel N U (calendarBlockCountLaw K H)) m =
          randomizedEventEpochKernel N U
            (calendarBlockCountLaw K ((m : Real) * H)) by
        funext y
        exact ih y]
      rw [randomizedEventEpochKernel_calendarBlockCountLaw_bind
        N U hH.le (mul_nonneg (Nat.cast_nonneg m) hH.le)]
      congr 3
      push_cast
      ring

#check natAddConvolution_toMeasure
#check poissonPMF_natAddConvolution
#check nStepLaw_add
#check eventEpochBlockKernel_bind
#check randomizedEventEpochKernel_bind
#check calendarBlockCountLaw_natAddConvolution
#check randomizedEventEpochKernel_calendarBlockCountLaw_bind
#check kernelIterate_randomizedEventEpochKernel_calendarBlockCountLaw

#print axioms natAddConvolution_toMeasure
#print axioms poissonPMF_natAddConvolution
#print axioms nStepLaw_add
#print axioms eventEpochBlockKernel_bind
#print axioms randomizedEventEpochKernel_bind
#print axioms calendarBlockCountLaw_natAddConvolution
#print axioms randomizedEventEpochKernel_calendarBlockCountLaw_bind
#print axioms kernelIterate_randomizedEventEpochKernel_calendarBlockCountLaw

end StateDepMOR.PaperStatements.Network
