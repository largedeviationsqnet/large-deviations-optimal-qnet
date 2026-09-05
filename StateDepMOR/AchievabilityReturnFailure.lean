import StateDepMOR.AchievabilityFinal
import StateDepMOR.FluidAllocationBounds

/-!
# Repaired achievability persistence term

This file treats term (c) from the repaired manuscript: fluid paths start
below `rho`, remain in the positive band `delta <= L_alpha < 1` throughout
the horizon, and hence avoid both the return set and the boundary.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

set_option maxHeartbeats 1600000

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : StateDepMOR.Network Buffer Server)


/-! ## Positive Lyapunov variation is controlled by input variation -/

private theorem fluidInput_deriv_nonnegative
    {U : N.DeterministicPolicySequence} {H : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (alpha : Simplex Buffer) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (j : Server) (k : Buffer) :
    0 <= pathDerivative A t j k := by
  have hmono := s.input_valid.2.1 j k
  have hwithin :=
    hmono.derivWithin_nonneg (x := t)
  have hnhds : Icc (0 : Real) H ∈ nhds t :=
    Icc_mem_nhds hregular.1.1 hregular.1.2
  rw [derivWithin_of_mem_nhds hnhds] at hwithin
  exact hwithin

/-- At a regular time with positive Lyapunov drift, the drift is bounded by
the total instantaneous marked-input rate divided by the least coordinate
of `alpha`. -/
theorem positiveLyapunovDrift_le_inputRate
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence} {H : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (t : Real) (hregular : IsRegularPoint N alpha s t)
    (hpositive : 0 < lyapunovDrift alpha s.X t) :
    lyapunovDrift alpha s.X t <=
      (Finset.sum Finset.univ fun j : Server =>
        Finset.sum Finset.univ fun k : Buffer =>
          pathDerivative A t j k) /
        Lyapunov.minCoordinate (fun i => alpha i) := by
  classical
  let m := Lyapunov.minCoordinate (fun i => alpha i)
  let total :=
    Finset.sum Finset.univ fun j : Server =>
      Finset.sum Finset.univ fun k : Buffer =>
        pathDerivative A t j k
  have hm : 0 < m := Lyapunov.minCoordinate_pos halpha
  obtain ⟨i, hi⟩ := minimumScaledBuffers_nonempty alpha (s.X t)
  have hdrift :=
    lyapunovDrift_eq_neg_deriv_div_of_mem_minimumScaledBuffers
      N alpha halpha s t hregular i hi
  have halpha_m : m <= alpha i :=
    Finset.inf'_le (fun q => alpha q) (Finset.mem_univ i)
  have hA_nonneg :
      forall j k, 0 <= pathDerivative A t j k :=
    fun j k =>
      fluidInput_deriv_nonnegative N s alpha t hregular j k
  have hE_nonneg :
      forall j, j ∈ N.serversOf i ->
        forall k, 0 <= deriv (fun r => s.E r i j k) t := by
    intro j hj k
    have hij : N.compatible i j := (N.mem_serversOf i j).1 hj
    exact allocation_deriv_nonnegative
      N s alpha t hregular i j k hij
  have hsingle :
      forall j, j ∈ N.serversOf i ->
        forall k,
          deriv (fun r => s.E r i j k) t <=
            pathDerivative A t j k := by
    intro j hj k
    have hij : i ∈ N.buffersOf j :=
      (N.mem_buffersOf i j).2 ((N.mem_serversOf i j).1 hj)
    calc
      deriv (fun r => s.E r i j k) t <=
          Finset.sum (N.buffersOf j)
            (fun l => deriv (fun r => s.E r l j k) t) := by
        exact Finset.single_le_sum
          (s := N.buffersOf j)
          (f := fun l => deriv (fun r => s.E r l j k) t)
          (fun l hl =>
            allocation_deriv_nonnegative N s alpha t hregular
              l j k ((N.mem_buffersOf l j).1 hl))
          hij
      _ <= pathDerivative A t j k :=
        total_allocation_deriv_le_input N s alpha t hregular j k
  have hout :
      Finset.sum (N.serversOf i) (fun j =>
          Finset.sum Finset.univ
            (fun k => deriv (fun r => s.E r i j k) t)) <= total := by
    calc
      Finset.sum (N.serversOf i) (fun j =>
          Finset.sum Finset.univ
            (fun k => deriv (fun r => s.E r i j k) t)) <=
          Finset.sum (N.serversOf i) (fun j =>
            Finset.sum Finset.univ
              (fun k => pathDerivative A t j k)) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact hsingle j hj k
      _ <= Finset.sum Finset.univ (fun j =>
          Finset.sum Finset.univ
            (fun k => pathDerivative A t j k)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _)
        intro j hj hnot
        exact Finset.sum_nonneg fun k hk => hA_nonneg j k
      _ = total := rfl
  have hincoming_nonneg :
      0 <= Finset.sum Finset.univ (fun j =>
        Finset.sum (N.buffersOf j)
          (fun l => deriv (fun r => s.E r l j i) t)) := by
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro l hl
    exact allocation_deriv_nonnegative N s alpha t hregular
      l j i ((N.mem_buffersOf l j).1 hl)
  have hstate :=
    state_deriv_eq_allocation_balance N s alpha t hregular i
  have hnegState :
      -deriv (fun r => s.X r i) t <= total := by
    rw [hstate]
    linarith
  have hnegState_pos : 0 < -deriv (fun r => s.X r i) t := by
    rw [hdrift] at hpositive
    rcases div_pos_iff.mp hpositive with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge (halpha i).le) hneg.2)
  have htotal_nonneg : 0 <= total :=
    hnegState_pos.le.trans hnegState
  rw [hdrift]
  apply (div_le_div_iff₀ (halpha i) hm).2
  calc
    (-deriv (fun r => s.X r i) t) * m <= total * m :=
      mul_le_mul_of_nonneg_right hnegState hm.le
    _ <= total * alpha i :=
      mul_le_mul_of_nonneg_left halpha_m htotal_nonneg

/-! ## Persistent fluid paths -/

/-- Repaired term-(c) fluid feasibility.  Such a path neither reaches the
`delta` return set nor hits the queue boundary during the block. -/
def IsPersistentFluidInput
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (delta rho H : Real) (A : MatrixPath Server Buffer) : Prop :=
  exists x0 : Simplex Buffer,
    exists s : N.FluidModelSolution U H x0 A,
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho /\
      forall t, t ∈ Icc (0 : Real) H ->
        delta <=
            Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) /\
          Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1

/-- Boundary-inclusive envelope of repaired term (c).  The strict
persistence event is contained in this set, and this is the envelope needed
when taking a closed J1 upper bound. -/
def IsPersistentFluidInputClosed
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (delta rho H : Real) (A : MatrixPath Server Buffer) : Prop :=
  exists x0 : Simplex Buffer,
    exists s : N.FluidModelSolution U H x0 A,
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho /\
      forall t, t ∈ Icc (0 : Real) H ->
        delta <=
            Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) /\
          Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) <= 1

private theorem isPersistentFluidInput_closed
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence)
    {delta rho H : Real} {A : MatrixPath Server Buffer}
    (h : IsPersistentFluidInput N alpha U delta rho H A) :
    IsPersistentFluidInputClosed N alpha U delta rho H A := by
  obtain ⟨x0, s, hstart, hband⟩ := h
  exact ⟨x0, s, hstart, fun t ht =>
    ⟨(hband t ht).1, (hband t ht).2.le⟩⟩

noncomputable def persistentFluidRateInf
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (delta rho H : Real) : ENNReal :=
  rateInf (fun A : MatrixPath Server Buffer =>
      poissonPathRate N H A)
    {A | IsPersistentFluidInput N alpha U delta rho H A}

private def positivePersistenceTimes
    (alpha : Simplex Buffer)
    {U : N.DeterministicPolicySequence} {H : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (epsilon : Real) : Set Real :=
  persistenceBadTimes N A epsilon H ∩
    {t | 0 < lyapunovDrift alpha s.X t}

private theorem measurableSet_positivePersistenceTimes
    (alpha : Simplex Buffer)
    {U : N.DeterministicPolicySequence} {H : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (epsilon : Real) :
    MeasurableSet
      (positivePersistenceTimes N alpha s epsilon) := by
  apply (measurableSet_persistenceBadTimes N A epsilon H).inter
  exact measurableSet_Ioi.preimage
    (measurable_deriv
      (fun t =>
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t)))

private theorem positivePersistenceTimes_subset_bad
    (alpha : Simplex Buffer)
    {U : N.DeterministicPolicySequence} {H : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (epsilon : Real) :
    positivePersistenceTimes N alpha s epsilon <=
      persistenceBadTimes N A epsilon H :=
  inter_subset_left

private theorem positivePersistenceTimes_subset_Icc
    (alpha : Simplex Buffer)
    {U : N.DeterministicPolicySequence} {H : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (epsilon : Real) :
    positivePersistenceTimes N alpha s epsilon <= Icc (0 : Real) H :=
  (positivePersistenceTimes_subset_bad N alpha s epsilon).trans
    (persistenceBadTimes_subset N A epsilon H)

private theorem persistent_positiveDrift_integral_lower
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {delta rho H eta epsilon : Real}
    (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hnegative :
      forall (T : Real) (x0 : Simplex Buffer)
        (A : MatrixPath Server Buffer)
        (s : N.FluidModelSolution U T x0 A) (t : Real),
        IsRegularPoint N alpha s t ->
        RateNearPhi (N := N) (pathDerivative A t) epsilon ->
        0 < Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) ->
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) <= 1 ->
        lyapunovDrift alpha s.X t <= -eta)
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (hstart :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho)
    (hband :
      forall t, t ∈ Icc (0 : Real) H ->
        delta <=
            Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) /\
          Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) <= 1)
    (hdelta : 0 < delta) :
    eta * (H -
        volume.real (persistenceBadTimes N A epsilon H)) +
        delta - rho <=
      integral
        (volume.restrict
          (positivePersistenceTimes N alpha s epsilon))
        (fun t => lyapunovDrift alpha s.X t) := by
  let g : Real -> Real :=
    fun t => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t)
  let dg : Real -> Real := fun t => deriv g t
  let bad := persistenceBadTimes N A epsilon H
  let pos := positivePersistenceTimes N alpha s epsilon
  let good := Icc (0 : Real) H \ bad
  have hH : 0 < H := s.horizon_pos
  have hgac : AbsolutelyContinuousOnInterval g 0 H :=
    Lyapunov.LAlphaAmbient_comp_absolutelyContinuous
      (fun i => alpha i) s.X s.state_ac
  have hdgInt : IntegrableOn dg (Icc (0 : Real) H) volume := by
    have hi := hgac.intervalIntegrable_deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hH.le] at hi
    exact hi
  have hbadMeas : MeasurableSet bad :=
    measurableSet_persistenceBadTimes N A epsilon H
  have hposMeas : MeasurableSet pos :=
    measurableSet_positivePersistenceTimes N alpha s epsilon
  have hgoodMeas : MeasurableSet good :=
    measurableSet_Icc.diff hbadMeas
  have hbadSub : bad <= Icc (0 : Real) H :=
    persistenceBadTimes_subset N A epsilon H
  have hposSubBad : pos <= bad :=
    positivePersistenceTimes_subset_bad N alpha s epsilon
  have hgoodSub : good <= Icc (0 : Real) H := diff_subset
  have hdgBad : IntegrableOn dg bad volume := hdgInt.mono_set hbadSub
  have hdgPos : IntegrableOn dg pos volume :=
    hdgBad.mono_set hposSubBad
  have hdgGood : IntegrableOn dg good volume :=
    hdgInt.mono_set hgoodSub
  have hregularGood :
      Filter.Eventually
        (fun t => IsRegularPoint N alpha s t)
        (ae (volume.restrict good)) :=
    ae_restrict_of_ae_restrict_of_subset hgoodSub
      (FluidModelSolution.isRegularPoint_ae alpha s)
  have hgoodPoint :
      Filter.Eventually
        (fun t => dg t <= -eta)
        (ae (volume.restrict good)) := by
    filter_upwards
      [hregularGood, ae_restrict_mem hgoodMeas] with t hregular ht
    have htIcc : t ∈ Icc (0 : Real) H := ht.1
    have htNear :
        RateNearPhi (N := N) (pathDerivative A t) epsilon := by
      by_contra hnot
      exact ht.2 ⟨htIcc, hnot⟩
    have htBand := hband t htIcc
    exact hnegative H x0 A s t hregular htNear
      (hdelta.trans_le htBand.1) htBand.2
  have hgoodFinite : Ne (volume good) (Top.top : ENNReal) :=
    ne_top_of_le_ne_top
      (measure_Icc_lt_top :
        volume (Icc (0 : Real) H) < (Top.top : ENNReal)).ne
      (measure_mono hgoodSub)
  have hgoodIntegral :
      integral (volume.restrict good) dg <=
        -eta * volume.real good := by
    calc
      integral (volume.restrict good) dg <=
          integral (volume.restrict good) (fun _ => -eta) :=
        integral_mono_ae hdgGood
          (integrableOn_const (C := -eta) hgoodFinite)
          hgoodPoint
      _ = -eta * volume.real good := by
        rw [setIntegral_const]
        simp [smul_eq_mul, mul_comm]
  have hbadOutsideIntegral :
      integral (volume.restrict (bad \ pos)) dg <= 0 := by
    have hsub : bad \ pos <= Icc (0 : Real) H :=
      diff_subset.trans hbadSub
    have hint : IntegrableOn dg (bad \ pos) volume :=
      hdgInt.mono_set hsub
    have hpoint :
        Filter.Eventually (fun t => dg t <= 0)
          (ae (volume.restrict (bad \ pos))) := by
      filter_upwards
        [ae_restrict_mem (hbadMeas.diff hposMeas)] with t ht
      apply le_of_not_gt
      intro hpositive
      apply ht.2
      exact ⟨ht.1, hpositive⟩
    have hzeroInt :
        IntegrableOn (fun _ : Real => (0 : Real)) (bad \ pos) volume :=
      integrableOn_zero
    simpa using integral_mono_ae hint hzeroInt hpoint
  have hsplitBad :
      integral (volume.restrict pos) dg +
          integral (volume.restrict (bad \ pos)) dg =
        integral (volume.restrict bad) dg := by
    have hsplit :=
      integral_inter_add_sdiff hposMeas hdgBad
    have hinter : bad ∩ pos = pos := inter_eq_right.mpr hposSubBad
    simpa [hinter] using hsplit
  have hbadIntegral_le_pos :
      integral (volume.restrict bad) dg <=
        integral (volume.restrict pos) dg := by
    rw [<- hsplitBad]
    linarith
  have hsplitH :
      integral (volume.restrict bad) dg +
          integral (volume.restrict good) dg =
        integral (volume.restrict (Icc (0 : Real) H)) dg := by
    have hsplit :=
      integral_inter_add_sdiff hbadMeas hdgInt
    have hinter :
        Icc (0 : Real) H ∩ bad = bad :=
      inter_eq_right.mpr hbadSub
    simpa [good, hinter] using hsplit
  have htotal :
      integral (volume.restrict (Icc (0 : Real) H)) dg =
        g H - g 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      <- intervalIntegral.integral_of_le hH.le,
      hgac.integral_deriv_eq_sub]
  have hend : delta <= g H := (hband H ⟨hH.le, le_rfl⟩).1
  have hzero : g 0 <= rho := hstart
  have hmeasure :
      volume.real good =
        H - volume.real bad := by
    rw [show good = Icc (0 : Real) H \ bad by rfl]
    rw [measureReal_sdiff hbadSub hbadMeas
      (measure_Icc_lt_top :
        volume (Icc (0 : Real) H) < (Top.top : ENNReal)).ne]
    rw [Measure.real_def, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal hH.le]
  have htotalLower :
      delta - rho <=
        integral (volume.restrict (Icc (0 : Real) H)) dg := by
    rw [htotal]
    linarith
  change
    eta * (H - volume.real bad) + delta - rho <=
      integral (volume.restrict pos) dg
  rw [<- hmeasure]
  linarith

private theorem positiveDrift_integral_entropy_bound
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence} {H epsilon : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (hepsilon : 0 < epsilon)
    (hfinite : Ne (poissonPathRate N H A) (Top.top : ENNReal)) :
    Lyapunov.minCoordinate (fun i => alpha i) *
        integral
          (volume.restrict
            (positivePersistenceTimes N alpha s epsilon))
          (fun t => lyapunovDrift alpha s.X t) <=
      (Fintype.card Server * Fintype.card Buffer : Nat) *
          (poissonPathRate N H A).toReal +
        (Real.exp 1 - 1) *
          volume.real
            (positivePersistenceTimes N alpha s epsilon) := by
  classical
  let m := Lyapunov.minCoordinate (fun i => alpha i)
  let pos := positivePersistenceTimes N alpha s epsilon
  let dg : Real -> Real :=
    fun t => lyapunovDrift alpha s.X t
  let inputTotal : Real -> Real :=
    fun t => Finset.sum Finset.univ fun j : Server =>
      Finset.sum Finset.univ fun k : Buffer =>
        pathDerivative A t j k
  have hH : 0 < H := s.horizon_pos
  have hm : 0 < m := Lyapunov.minCoordinate_pos halpha
  have hposMeas : MeasurableSet pos :=
    measurableSet_positivePersistenceTimes N alpha s epsilon
  have hposSub : pos <= Icc (0 : Real) H :=
    positivePersistenceTimes_subset_Icc N alpha s epsilon
  have hposFinite : Ne (volume pos) (Top.top : ENNReal) :=
    ne_top_of_le_ne_top
      (measure_Icc_lt_top :
        volume (Icc (0 : Real) H) < (Top.top : ENNReal)).ne
      (measure_mono hposSub)
  have hdgInt : IntegrableOn dg (Icc (0 : Real) H) volume := by
    have hac :=
      Lyapunov.LAlphaAmbient_comp_absolutelyContinuous
        (fun i => alpha i) s.X s.state_ac
    have hi := hac.intervalIntegrable_deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hH.le] at hi
    exact hi
  have hdgPos : IntegrableOn dg pos volume :=
    hdgInt.mono_set hposSub
  have hinputInt :
      forall j k,
        IntegrableOn (fun t => pathDerivative A t j k)
          (Icc (0 : Real) H) volume :=
    fun j k =>
      finiteAction_derivative_integrableOn N hH.le A hfinite j k
  have htotalInt : IntegrableOn inputTotal pos volume := by
    dsimp [inputTotal]
    exact integrable_finsetSum Finset.univ fun j _ =>
      integrable_finsetSum Finset.univ fun k _ =>
        (hinputInt j k).mono_set hposSub
  have hregularPos :
      Filter.Eventually
        (fun t => IsRegularPoint N alpha s t)
        (ae (volume.restrict pos)) :=
    ae_restrict_of_ae_restrict_of_subset hposSub
      (FluidModelSolution.isRegularPoint_ae alpha s)
  have hpoint :
      Filter.Eventually
        (fun t => m * dg t <= inputTotal t)
        (ae (volume.restrict pos)) := by
    filter_upwards
      [hregularPos, ae_restrict_mem hposMeas] with t hregular ht
    have hpositive : 0 < dg t := ht.2
    have hbound :=
      positiveLyapunovDrift_le_inputRate
        N alpha halpha s t hregular hpositive
    dsimp [m, dg, inputTotal] at *
    simpa [mul_comm] using
      (le_div_iff₀ (Lyapunov.minCoordinate_pos halpha)).mp hbound
  have hintegral :
      m * integral (volume.restrict pos) dg <=
        integral (volume.restrict pos) inputTotal := by
    rw [<- integral_const_mul]
    exact integral_mono_ae
      (hdgPos.const_mul m) htotalInt hpoint
  have hactionSub :
      poissonPathRate N H A <=
        ENNReal.ofReal (poissonPathRate N H A).toReal := by
    rw [ENNReal.ofReal_toReal hfinite]
  have hcoordinate (j : Server) (k : Buffer) :
      integral (volume.restrict pos)
          (fun t => pathDerivative A t j k) <=
        (poissonPathRate N H A).toReal +
          N.phi j k * (Real.exp 1 - 1) *
            volume.real pos := by
    rcases (N.phi_nonneg j k).eq_or_lt with hphi0 | hphi
    · have hzero :
          Filter.Eventually
            (fun t => pathDerivative A t j k = 0)
            (ae (volume.restrict pos)) :=
        ae_restrict_of_ae_restrict_of_subset hposSub
          (finiteAction_zeroDerivative_ae
            N H A hfinite j k hphi0.symm)
      have hintZero :
          integral (volume.restrict pos)
              (fun t => pathDerivative A t j k) = 0 := by
        calc
          integral (volume.restrict pos)
                (fun t => pathDerivative A t j k) =
              integral (volume.restrict pos) (fun _ => (0 : Real)) :=
            integral_congr_ae hzero
          _ = 0 := by simp
      rw [hintZero, <- hphi0]
      simpa using ENNReal.toReal_nonneg
    · have hbound :=
        StateDepMOR.PoissonSamplePath.coordinate_setIntegral_derivative_bound
          N hH A hactionSub j k hphi 1 (by norm_num)
          hposMeas hposSub
      simpa only [one_mul, max_eq_left ENNReal.toReal_nonneg] using hbound
  have hsum :
      integral (volume.restrict pos) inputTotal =
        Finset.sum Finset.univ (fun j : Server =>
          Finset.sum Finset.univ (fun k : Buffer =>
            integral (volume.restrict pos)
              (fun t => pathDerivative A t j k))) := by
    dsimp [inputTotal]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_finset_sum]
      intro k hk
      exact (hinputInt j k).mono_set hposSub
    · intro j hj
      exact integrable_finsetSum Finset.univ fun k _ =>
        (hinputInt j k).mono_set hposSub
  rw [hsum] at hintegral
  calc
    m * integral (volume.restrict pos) dg <=
        Finset.sum Finset.univ (fun j : Server =>
          Finset.sum Finset.univ (fun k : Buffer =>
            integral (volume.restrict pos)
              (fun t => pathDerivative A t j k))) := hintegral
    _ <= Finset.sum Finset.univ (fun j : Server =>
          Finset.sum Finset.univ (fun k : Buffer =>
            (poissonPathRate N H A).toReal +
              N.phi j k * (Real.exp 1 - 1) *
                volume.real pos)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      exact hcoordinate j k
    _ = (Fintype.card Server * Fintype.card Buffer : Nat) *
          (poissonPathRate N H A).toReal +
        (Real.exp 1 - 1) * volume.real pos := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul]
      have hphi :
          Finset.sum Finset.univ (fun j : Server =>
            Finset.sum Finset.univ (fun k : Buffer => N.phi j k)) = 1 := by
        simpa only [Fintype.sum_prod_type] using N.total_rate
      have hweighted :
          Finset.sum Finset.univ (fun j : Server =>
            Finset.sum Finset.univ (fun k : Buffer =>
              N.phi j k * (Real.exp 1 - 1) * volume.real pos)) =
            (Real.exp 1 - 1) * volume.real pos := by
        simp_rw [mul_assoc, <- Finset.sum_mul]
        rw [hphi, one_mul]
      rw [hweighted]
      simp only [Finset.card_univ]
      push_cast
      ring

private theorem persistentFluidInput_linear_cost
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    {delta rho H eta epsilon : Real}
    (heta : 0 < eta) (hepsilon : 0 < epsilon)
    (hnegative :
      forall (T : Real) (x0 : Simplex Buffer)
        (A : MatrixPath Server Buffer)
        (s : N.FluidModelSolution U T x0 A) (t : Real),
        IsRegularPoint N alpha s t ->
        RateNearPhi (N := N) (pathDerivative A t) epsilon ->
        0 < Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) ->
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) <= 1 ->
        lyapunovDrift alpha s.X t <= -eta)
    (hdelta : 0 < delta)
    (A : MatrixPath Server Buffer)
    (hpersistent : IsPersistentFluidInputClosed N alpha U delta rho H A)
    (hfinite : Ne (poissonPathRate N H A) (Top.top : ENNReal)) :
    let gap := persistenceTheta epsilon * epsilon / 2
    let m := Lyapunov.minCoordinate (fun i => alpha i)
    let card := (Fintype.card Server * Fintype.card Buffer : Real)
    let overhead := Real.exp 1 - 1
    gap * m * eta * H - gap * m * (rho - delta) <=
      (card * gap + m * eta + overhead) *
        (poissonPathRate N H A).toReal := by
  classical
  obtain ⟨x0, s, hstart, hband⟩ := hpersistent
  let gap := persistenceTheta epsilon * epsilon / 2
  let m := Lyapunov.minCoordinate (fun i => alpha i)
  let card := (Fintype.card Server * Fintype.card Buffer : Real)
  let overhead := Real.exp 1 - 1
  let bad := persistenceBadTimes N A epsilon H
  let pos := positivePersistenceTimes N alpha s epsilon
  let action := (poissonPathRate N H A).toReal
  let driftIntegral :=
    integral (volume.restrict pos)
      (fun t => lyapunovDrift alpha s.X t)
  have hgap : 0 < gap := by
    dsimp [gap]
    exact div_pos (mul_pos (persistenceTheta_pos hepsilon) hepsilon)
      (by norm_num)
  have hm : 0 < m := Lyapunov.minCoordinate_pos halpha
  have hoverhead : 0 <= overhead := by
    dsimp [overhead]
    exact sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hbadCost :
      gap * volume.real bad <= action := by
    simpa only [gap, bad, action] using
      persistenceGap_mul_badTime_le_action
        N s.horizon_pos hepsilon A hfinite
  have hdriftLower :
      eta * (H - volume.real bad) + delta - rho <=
        driftIntegral := by
    simpa only [bad, pos, driftIntegral] using
      persistent_positiveDrift_integral_lower
        N alpha U heta hepsilon hnegative s hstart hband hdelta
  have hentropy :
      m * driftIntegral <=
        card * action + overhead * volume.real pos := by
    simpa only [m, card, overhead, action, pos, driftIntegral,
      Nat.cast_mul] using
      positiveDrift_integral_entropy_bound
        N alpha halpha s hepsilon hfinite
  have hposMeasure :
      volume.real pos <= volume.real bad := by
    have hbadFinite : Ne (volume bad) (Top.top : ENNReal) :=
      ne_top_of_le_ne_top
        (measure_Icc_lt_top :
          volume (Icc (0 : Real) H) < (Top.top : ENNReal)).ne
        (measure_mono (persistenceBadTimes_subset N A epsilon H))
    exact measureReal_mono
      (positivePersistenceTimes_subset_bad N alpha s epsilon) hbadFinite
  have hentropyBad :
      m * driftIntegral <=
        card * action + overhead * volume.real bad := by
    calc
      m * driftIntegral <=
          card * action + overhead * volume.real pos := hentropy
      _ <= card * action + overhead * volume.real bad := by
        gcongr
  have hcore :
      m * (eta * (H - volume.real bad) + delta - rho) <=
        card * action + overhead * volume.real bad := by
    exact (mul_le_mul_of_nonneg_left hdriftLower hm.le).trans hentropyBad
  have hscaledCore :
      gap * (m * (eta * (H - volume.real bad) + delta - rho)) <=
        gap * (card * action + overhead * volume.real bad) :=
    mul_le_mul_of_nonneg_left hcore hgap.le
  have hbadScaled :
      (m * eta + overhead) * (gap * volume.real bad) <=
        (m * eta + overhead) * action := by
    exact mul_le_mul_of_nonneg_left hbadCost
      (add_nonneg (mul_nonneg hm.le heta.le) hoverhead)
  dsimp only [gap, m, card, overhead, action]
  apply (add_le_add_iff_right
    (gap * overhead * volume.real bad)).mp
  calc
    persistenceTheta epsilon * epsilon / 2 *
            Lyapunov.minCoordinate (fun i => alpha i) * eta * H -
          persistenceTheta epsilon * epsilon / 2 *
            Lyapunov.minCoordinate (fun i => alpha i) * (rho - delta) +
        gap * overhead * volume.real bad =
        gap * (m * (eta * (H - volume.real bad) + delta - rho)) +
          (m * eta + overhead) * (gap * volume.real bad) := by ring
    _ <= gap * (card * action + overhead * volume.real bad) +
          (m * eta + overhead) * action :=
      add_le_add hscaledCore hbadScaled
    _ = (card * gap + m * eta + overhead) * action +
          gap * overhead * volume.real bad := by ring

/-- Every input in the boundary-inclusive closed envelope of repaired term
(c) has action bounded below by a common affine function of the block
horizon with positive slope. -/
theorem persistentFluidInputClosed_action_linear_lower
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative : NegativeDriftCondition (N := N) alpha U)
    {delta rho : Real} (hdelta : 0 < delta) :
    exists a : Real, 0 < a /\ exists b : Real,
      forall (H : Real) (A : MatrixPath Server Buffer),
        IsPersistentFluidInputClosed N alpha U delta rho H A ->
        ENNReal.ofReal (a * H - b) <= poissonPathRate N H A := by
  classical
  rcases hnegative with
    ⟨eta, heta, epsilon, hepsilon, hnegative⟩
  let gap := persistenceTheta epsilon * epsilon / 2
  let m := Lyapunov.minCoordinate (fun i => alpha i)
  let card := (Fintype.card Server * Fintype.card Buffer : Real)
  let overhead := Real.exp 1 - 1
  let denominator := card * gap + m * eta + overhead
  let a := gap * m * eta / denominator
  let b := gap * m * (rho - delta) / denominator
  have hgap : 0 < gap := by
    dsimp [gap]
    exact div_pos (mul_pos (persistenceTheta_pos hepsilon) hepsilon)
      (by norm_num)
  have hm : 0 < m := Lyapunov.minCoordinate_pos halpha
  have hcard : 0 < card := by
    dsimp [card]
    positivity
  have hoverhead : 0 <= overhead := by
    dsimp [overhead]
    exact sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  have ha : 0 < a := by
    dsimp [a]
    positivity
  refine ⟨a, ha, b, ?_⟩
  intro H A hpersistent
  by_cases hfinite :
      Ne (poissonPathRate N H A) (Top.top : ENNReal)
  · apply ENNReal.ofReal_le_of_le_toReal
    apply (mul_le_mul_iff_right₀ hdenominator).mp
    calc
      denominator * (a * H - b) =
          gap * m * eta * H - gap * m * (rho - delta) := by
        dsimp [a, b]
        field_simp [hdenominator.ne']
        <;> ring
      _ <= denominator * (poissonPathRate N H A).toReal := by
        simpa only [gap, m, card, overhead, denominator] using
          persistentFluidInput_linear_cost
            N alpha halpha U heta hepsilon hnegative hdelta A
              hpersistent hfinite
  · rw [not_ne_iff] at hfinite
    rw [hfinite]
    exact le_top

/-- The strict repaired term-(c) event inherits the same common positive
affine action lower bound from its boundary-inclusive envelope. -/
theorem persistentFluidInput_action_linear_lower
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative : NegativeDriftCondition (N := N) alpha U)
    {delta rho : Real} (hdelta : 0 < delta) :
    exists a : Real, 0 < a /\ exists b : Real,
      forall (H : Real) (A : MatrixPath Server Buffer),
        IsPersistentFluidInput N alpha U delta rho H A ->
        ENNReal.ofReal (a * H - b) <= poissonPathRate N H A := by
  obtain ⟨a, ha, b, hlower⟩ :=
    persistentFluidInputClosed_action_linear_lower
      N alpha halpha U hnegative hdelta
  exact ⟨a, ha, b, fun H A h =>
    hlower H A (isPersistentFluidInput_closed N alpha U h)⟩

/-- The infimum action of the repaired persistence event has a common
positive affine lower bound in the block horizon. -/
theorem persistentFluidRateInf_linear_lower
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative : NegativeDriftCondition (N := N) alpha U)
    {delta rho : Real} (hdelta : 0 < delta) :
    exists a : Real, 0 < a /\ exists b : Real,
      forall H : Real,
        ENNReal.ofReal (a * H - b) <=
          persistentFluidRateInf N alpha U delta rho H := by
  obtain ⟨a, ha, b, hlower⟩ :=
    persistentFluidInput_action_linear_lower
      N alpha halpha U hnegative hdelta
  refine ⟨a, ha, b, ?_⟩
  intro H
  unfold persistentFluidRateInf rateInf
  apply le_sInf
  intro y hy
  obtain ⟨A, hA, rfl⟩ := hy
  exact hlower H A hA

/-- Under the repaired boundary-inclusive negative drift condition, the
fluid variational cost of term (c) tends to infinity with block horizon. -/
theorem persistentFluidRateInf_tendsto_atTop
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative : NegativeDriftCondition (N := N) alpha U)
    {delta rho : Real} (hdelta : 0 < delta) :
    Tendsto
      (fun H => persistentFluidRateInf N alpha U delta rho H)
      atTop (nhds (Top.top : ENNReal)) := by
  obtain ⟨a, ha, b, hlower⟩ :=
    persistentFluidRateInf_linear_lower
      N alpha halpha U hnegative hdelta
  have hreal :
      Tendsto (fun H : Real => a * H - b) atTop atTop :=
    by
      have hmul : Tendsto (fun H : Real => a * H) atTop atTop :=
        tendsto_id.const_mul_atTop ha
      simpa only [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-b) hmul
  have hofReal :
      Tendsto (fun H : Real => ENNReal.ofReal (a * H - b))
        atTop (nhds (Top.top : ENNReal)) := by
    simpa only [Function.comp_def] using
      ENNReal.tendsto_ofReal_atTop.comp hreal
  exact tendsto_nhds_top_mono' hofReal hlower

/-! ## Concrete closed-J1 upper bound -/

/-- Calendar input paths that support a repaired term-(c) persistent fluid
execution. -/
def persistentFluidInputSet
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (delta rho H : Real) :
    Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H) :=
  {a | IsPersistentFluidInput N alpha U delta rho H
    (StateDepMOR.PoissonSamplePath.asMatrix H a)}

/-- Calendar-path realization of the boundary-inclusive persistence
envelope used for closed upper bounds. -/
def persistentFluidClosedInputSet
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (delta rho H : Real) :
    Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H) :=
  {a | IsPersistentFluidInputClosed N alpha U delta rho H
    (StateDepMOR.PoissonSamplePath.asMatrix H a)}

theorem persistentFluidInputSet_subset_closed
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (delta rho H : Real) :
    persistentFluidInputSet N alpha U delta rho H <=
      persistentFluidClosedInputSet N alpha U delta rho H := by
  intro p hp
  exact isPersistentFluidInput_closed N alpha U hp

/-- A single positive affine action bound controls every closed J1 subset
of the boundary-inclusive persistence envelope, uniformly over the block
horizon. -/
theorem exists_calendarPathLaw_closed_persistence_upper
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative : NegativeDriftCondition (N := N) alpha U)
    {delta rho : Real} (hdelta : 0 < delta) :
    exists a : Real, 0 < a /\ exists b : Real,
      forall (H : Real), 0 < H ->
      forall F : Set (StateDepMOR.PoissonSamplePath.Path
          (Buffer := Buffer) (Server := Server) H),
        IsClosed F ->
        F <= persistentFluidClosedInputSet N alpha U delta rho H ->
        limsup
            (scaledLogMass
              (StateDepMOR.PoissonSamplePath.calendarPathLaw N H) F)
            atTop <=
          -((ENNReal.ofReal (a * H - b) : ENNReal) : EReal) := by
  obtain ⟨a, ha, b, hlower⟩ :=
    persistentFluidInputClosed_action_linear_lower
      N alpha halpha U hnegative hdelta
  refine ⟨a, ha, b, ?_⟩
  intro H hH F hFclosed hFpersistent
  let I :
      StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H -> ENNReal :=
    fun p => poissonPathRate N H
      (StateDepMOR.PoissonSamplePath.asMatrix H p)
  have hrate :
      ENNReal.ofReal (a * H - b) <= rateInf I F := by
    unfold rateInf
    apply le_sInf
    intro y hy
    obtain ⟨p, hpF, rfl⟩ := hy
    exact hlower H
      (StateDepMOR.PoissonSamplePath.asMatrix H p)
      (hFpersistent hpF)
  have hupper :=
    StateDepMOR.PoissonSamplePath.calendarPathLaw_closed_upper_bound
      N hH F hFclosed
  refine hupper.trans (EReal.neg_le_neg_iff.mpr ?_)
  exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr hrate

end StateDepMOR.PaperStatements.Network

#check StateDepMOR.PaperStatements.Network.localRate_ge_of_not_rateNearPhi
#check StateDepMOR.PaperStatements.Network.persistenceGap_mul_badTime_le_action
#check StateDepMOR.PaperStatements.Network.positiveLyapunovDrift_le_inputRate
#check StateDepMOR.PaperStatements.Network.IsPersistentFluidInput
#check StateDepMOR.PaperStatements.Network.IsPersistentFluidInputClosed
#check StateDepMOR.PaperStatements.Network.persistentFluidRateInf
#check StateDepMOR.PaperStatements.Network.persistentFluidInputClosed_action_linear_lower
#check StateDepMOR.PaperStatements.Network.persistentFluidInput_action_linear_lower
#check StateDepMOR.PaperStatements.Network.persistentFluidRateInf_linear_lower
#check StateDepMOR.PaperStatements.Network.persistentFluidRateInf_tendsto_atTop
#check StateDepMOR.PaperStatements.Network.persistentFluidInputSet
#check StateDepMOR.PaperStatements.Network.persistentFluidClosedInputSet
#check StateDepMOR.PaperStatements.Network.exists_calendarPathLaw_closed_persistence_upper
#print axioms StateDepMOR.PaperStatements.Network.localRate_ge_of_not_rateNearPhi
#print axioms StateDepMOR.PaperStatements.Network.persistenceGap_mul_badTime_le_action
#print axioms StateDepMOR.PaperStatements.Network.positiveLyapunovDrift_le_inputRate
#print axioms StateDepMOR.PaperStatements.Network.persistentFluidInput_action_linear_lower
#print axioms StateDepMOR.PaperStatements.Network.persistentFluidRateInf_linear_lower
#print axioms StateDepMOR.PaperStatements.Network.persistentFluidRateInf_tendsto_atTop
#print axioms StateDepMOR.PaperStatements.Network.exists_calendarPathLaw_closed_persistence_upper
