import StateDepMOR.FluidDriftProofs

/-!
# Fluid allocation bounds

This file derives allocation increment bounds from the absolutely
continuous fluid paths and their almost-everywhere allocation equations.
The bounds are then differentiated at an interior regular time to obtain
the aggregate cut-flow inequality used by the Lyapunov drift proof.
-/

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

private theorem action_none_eq_zero_of_nonidle
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (hnonidle : N.IsNonIdlingSequence U)
    (x : Buffer -> Real)
    (hx : forall i, 0 < x i)
    (j : Server) (k : Buffer)
    (q : StateDepMOR.Network.ActionVector Buffer)
    (hq : q ∈ N.fluidPolicyCorrespondence U j k x) :
    q none = 0 := by
  classical
  obtain ⟨i, hij⟩ := N.server_has_neighbor j
  let eps : {e : Real // 0 < e} := ⟨x i / 2, half_pos (hx i)⟩
  let H : Set (StateDepMOR.Network.ActionVector Buffer) :=
    {r | r none = 0}
  have hHclosed : IsClosed H := by
    exact isClosed_eq (continuous_apply none) continuous_const
  have hHconvex : Convex Real H := by
    exact convex_hyperplane (LinearMap.proj none).isLinear 0
  have hbase :
      {r | exists K : PNat, exists z : JobState Buffer (K : Nat),
        eps.1⁻¹ <= (K : Real) /\
        StateDepMOR.Network.IsNearNormalizedState z x eps.1 /\
        r = N.actionDirac (U K z j k)} <= H := by
    intro r hr
    obtain ⟨K, z, _hK, hznear, rfl⟩ := hr
    have hKpos : 0 < ((K : Nat) : Real) := by
      exact_mod_cast K.pos
    have hiratio : 0 < (z i : Real) / (K : Real) := by
      have hi := hznear i
      dsimp [eps] at hi
      rw [abs_lt] at hi
      linarith
    have hiz : 0 < z i := by
      have hizreal : 0 < (z i : Real) := by
        rcases div_pos_iff.mp hiratio with h | h
        · exact h.1
        · exact (not_lt_of_ge hKpos.le h.2).elim
      exact_mod_cast hizreal
    have haction : Not (U K z j k = none) := by
      intro hnone
      have hall := (hnonidle K z j k).1 hnone
      exact (Nat.ne_of_gt hiz) (hall i hij)
    have haction' : Not (none = U K z j k) :=
      fun h => haction h.symm
    simp [H, StateDepMOR.Network.actionDirac, haction']
  unfold StateDepMOR.Network.fluidPolicyCorrespondence at hq
  have hqeps := Set.mem_iInter.1 hq eps
  exact
    (closure_minimal (convexHull_min hbase hHconvex) hHclosed hqeps)

private theorem sum_compatible_fractions_le_one
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    {r : Real} (hr : r ∈ Set.Icc (0 : Real) T)
    (j : Server) (k : Buffer) :
    Finset.sum (N.buffersOf j) (fun i => s.p r j k (some i)) <= 1 := by
  classical
  have hsub :
      Finset.sum (N.buffersOf j) (fun i => s.p r j k (some i)) <=
        Finset.sum Finset.univ (fun i => s.p r j k (some i)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _)
      (fun i _ _ => (s.fractions_in_simplex r hr j k).1 (some i))
  have hnone : 0 <= s.p r j k none :=
    (s.fractions_in_simplex r hr j k).1 none
  have htotal := (s.fractions_in_simplex r hr j k).2
  rw [Fintype.sum_option] at htotal
  linarith

private theorem sum_compatible_fractions_eq_one_of_none_eq_zero
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    {r : Real} (hr : r ∈ Set.Icc (0 : Real) T)
    (j : Server) (k : Buffer)
    (hnone : s.p r j k none = 0) :
    Finset.sum (N.buffersOf j) (fun i => s.p r j k (some i)) = 1 := by
  classical
  have hall :
      Finset.sum (N.buffersOf j) (fun i => s.p r j k (some i)) =
        Finset.sum Finset.univ (fun i => s.p r j k (some i)) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hincompat : Not (N.compatible i j) := by
      intro hij
      exact hi ((N.mem_buffersOf i j).2 hij)
    exact s.fractions_incompatible r hr j k i hincompat
  have htotal := (s.fractions_in_simplex r hr j k).2
  rw [Fintype.sum_option, hnone, zero_add] at htotal
  exact hall.trans htotal

/-- The cumulative allocation equation recovered from absolute continuity
and the almost-everywhere allocation rule. -/
theorem allocation_increment_eq_integral
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    {a b : Real} (ha : 0 <= a) (hab : a <= b) (hb : b <= T)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : N.compatible i j) :
    s.E b i j k - s.E a i j k =
      intervalIntegral (fun r =>
        deriv (fun z => A z j k) r * s.p r j k (some i))
        a b volume := by
  have hsub : Set.uIcc a b <= Set.uIcc (0 : Real) T := by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (ha.trans (hab.trans hb))]
    exact Set.Icc_subset_Icc ha hb
  have hsubIcc : Set.Icc a b <= Set.Icc (0 : Real) T :=
    Set.Icc_subset_Icc ha hb
  have hEac := (s.allocation_ac i j k).mono hsub
  have halloc :
      ∀ᵐ r ∂volume,
        r ∈ Set.Icc (0 : Real) T ->
          deriv (fun z => s.E z i j k) r =
            deriv (fun z => A z j k) r * s.p r j k (some i) := by
    have h := s.allocation_rule
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h
    filter_upwards [h] with r hr
    exact fun hrange => hr hrange i j k hij
  calc
    s.E b i j k - s.E a i j k =
        intervalIntegral (fun r => deriv (fun z => s.E z i j k) r)
          a b volume := by
          exact hEac.integral_deriv_eq_sub.symm
    _ = intervalIntegral (fun r =>
          deriv (fun z => A z j k) r * s.p r j k (some i))
          a b volume := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [halloc] with r hr hrab
        apply hr
        apply hsubIcc
        rw [Set.uIoc_of_le hab] at hrab
        exact ⟨hrab.1.le, hrab.2⟩

private theorem input_deriv_nonnegative
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (j : Server) (k : Buffer)
    {r : Real} (hr : r ∈ Set.Ioo (0 : Real) T) :
    0 <= deriv (fun z => A z j k) r := by
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)]
  exact (s.input_valid.2.1 j k).derivWithin_nonneg

/-- Each compatible cumulative allocation is nondecreasing on an interior
subinterval. -/
theorem allocation_increment_nonnegative
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    {a b : Real} (ha : 0 < a) (hab : a <= b) (hb : b < T)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : N.compatible i j) :
    0 <= s.E b i j k - s.E a i j k := by
  rw [allocation_increment_eq_integral N s ha.le hab hb.le i j k hij]
  apply intervalIntegral.integral_nonneg hab
  intro r hr
  have hrT : r ∈ Set.Icc (0 : Real) T :=
    ⟨ha.le.trans hr.1, hr.2.trans hb.le⟩
  have hrint : r ∈ Set.Ioo (0 : Real) T :=
    ⟨ha.trans_le hr.1, hr.2.trans_lt hb⟩
  exact mul_nonneg
    (input_deriv_nonnegative N s j k hrint)
    ((s.fractions_in_simplex r hrT j k).1 (some i))

/-- Total compatible allocation for one token type cannot exceed the input
increment that generated those service opportunities. -/
theorem total_allocation_increment_le_input
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    {a b : Real} (ha : 0 < a) (hab : a <= b) (hb : b < T)
    (j : Server) (k : Buffer) :
    Finset.sum (N.buffersOf j)
        (fun i => s.E b i j k - s.E a i j k) <=
      A b j k - A a j k := by
  classical
  have hsub : Set.uIcc a b <= Set.uIcc (0 : Real) T := by
    rw [Set.uIcc_of_le hab,
      Set.uIcc_of_le (le_of_lt ((ha.trans_le hab).trans hb))]
    exact Set.Icc_subset_Icc ha.le hb.le
  have hsubIcc : Set.Icc a b <= Set.Icc (0 : Real) T :=
    Set.Icc_subset_Icc ha.le hb.le
  have hAac := (s.input_valid.1 j k).mono hsub
  have hEint :
      forall i, i ∈ N.buffersOf j ->
        IntervalIntegrable (fun r => deriv (fun z => s.E z i j k) r)
          volume a b := by
    intro i _
    exact ((s.allocation_ac i j k).mono hsub).intervalIntegrable_deriv
  have hAint :
      IntervalIntegrable (fun r => deriv (fun z => A z j k) r)
        volume a b :=
    hAac.intervalIntegrable_deriv
  have hsumint :
      IntervalIntegrable
        (fun r => Finset.sum (N.buffersOf j)
          (fun i => deriv (fun z => s.E z i j k) r))
        volume a b := by
    apply (IntervalIntegrable.sum (N.buffersOf j) hEint).congr
    intro r _
    simp only [Finset.sum_apply]
  have hpoint :
      ∀ᵐ r ∂volume.restrict (Set.Icc a b),
        Finset.sum (N.buffersOf j)
            (fun i => deriv (fun z => s.E z i j k) r) <=
          deriv (fun z => A z j k) r := by
    have halloc := s.allocation_rule
    have halloc' :
        ∀ᵐ r ∂volume.restrict (Set.Icc a b),
          forall i j k, N.compatible i j ->
            deriv (fun z => s.E z i j k) r =
              deriv (fun z => A z j k) r * s.p r j k (some i) :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        hsubIcc
        halloc
    filter_upwards [halloc', ae_restrict_mem measurableSet_Icc] with r hrule hrange
    have hrangeT : r ∈ Set.Icc (0 : Real) T := by
      exact hsubIcc hrange
    have hrinterior : r ∈ Set.Ioo (0 : Real) T := by
      exact ⟨ha.trans_le hrange.1, hrange.2.trans_lt hb⟩
    have hrate := input_deriv_nonnegative N s j k hrinterior
    calc
      Finset.sum (N.buffersOf j)
          (fun i => deriv (fun z => s.E z i j k) r) =
          deriv (fun z => A z j k) r *
            Finset.sum (N.buffersOf j)
              (fun i => s.p r j k (some i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        exact hrule i j k ((N.mem_buffersOf i j).1 hi)
      _ <= deriv (fun z => A z j k) r * 1 := by
        exact mul_le_mul_of_nonneg_left
          (sum_compatible_fractions_le_one N s hrangeT j k) hrate
      _ = deriv (fun z => A z j k) r := mul_one _
  calc
    Finset.sum (N.buffersOf j)
        (fun i => s.E b i j k - s.E a i j k) =
        Finset.sum (N.buffersOf j)
          (fun i => intervalIntegral
            (fun r => deriv (fun z => s.E z i j k) r)
            a b volume) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (((s.allocation_ac i j k).mono hsub).integral_deriv_eq_sub).symm
    _ = intervalIntegral
          (fun r => Finset.sum (N.buffersOf j)
            (fun i => deriv (fun z => s.E z i j k) r))
          a b volume := by
      exact (intervalIntegral.integral_finsetSum hEint).symm
    _ <= intervalIntegral (fun r => deriv (fun z => A z j k) r)
          a b volume := by
      exact intervalIntegral.integral_mono_ae_restrict hab
        hsumint hAint hpoint
    _ = A b j k - A a j k := hAac.integral_deriv_eq_sub

/-- At a strictly positive fluid state, non-idling removes the `none`
fraction, so total compatible allocation equals the input increment. -/
theorem total_allocation_increment_eq_input_of_positive
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (hnonidle : N.IsNonIdlingSequence U)
    {a b : Real} (ha : 0 < a) (hab : a <= b) (hb : b < T)
    (hpositive :
      forall r, r ∈ Set.Icc a b -> forall i, 0 < s.X r i)
    (j : Server) (k : Buffer) :
    Finset.sum (N.buffersOf j)
        (fun i => s.E b i j k - s.E a i j k) =
      A b j k - A a j k := by
  classical
  have hsubIcc : Set.Icc a b <= Set.Icc (0 : Real) T :=
    Set.Icc_subset_Icc ha.le hb.le
  have hsub : Set.uIcc a b <= Set.uIcc (0 : Real) T := by
    rw [Set.uIcc_of_le hab,
      Set.uIcc_of_le (le_of_lt ((ha.trans_le hab).trans hb))]
    exact hsubIcc
  have hAac := (s.input_valid.1 j k).mono hsub
  have hEint :
      forall i, i ∈ N.buffersOf j ->
        IntervalIntegrable (fun r => deriv (fun z => s.E z i j k) r)
          volume a b := by
    intro i _
    exact ((s.allocation_ac i j k).mono hsub).intervalIntegrable_deriv
  have halloc :
      ∀ᵐ r ∂volume.restrict (Set.Icc a b),
        forall i j k, N.compatible i j ->
          deriv (fun z => s.E z i j k) r =
            deriv (fun z => A z j k) r * s.p r j k (some i) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      hsubIcc s.allocation_rule
  have hpolicy :
      ∀ᵐ r ∂volume.restrict (Set.Icc a b),
        forall j k,
          (fun a => s.p r j k a) ∈
            N.fluidPolicyCorrespondence U j k (s.X r) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      hsubIcc s.policy_rule
  have hpoint :
      ∀ᵐ r ∂volume.restrict (Set.Icc a b),
        Finset.sum (N.buffersOf j)
            (fun i => deriv (fun z => s.E z i j k) r) =
          deriv (fun z => A z j k) r := by
    filter_upwards [halloc, hpolicy,
      ae_restrict_mem measurableSet_Icc] with r hrule hpol hrange
    have hrangeT := hsubIcc hrange
    have hnone :
        s.p r j k none = 0 :=
      action_none_eq_zero_of_nonidle N U hnonidle (s.X r)
        (hpositive r hrange) j k (fun a => s.p r j k a) (hpol j k)
    have hsum :=
      sum_compatible_fractions_eq_one_of_none_eq_zero
        N s hrangeT j k hnone
    calc
      Finset.sum (N.buffersOf j)
          (fun i => deriv (fun z => s.E z i j k) r) =
          deriv (fun z => A z j k) r *
            Finset.sum (N.buffersOf j)
              (fun i => s.p r j k (some i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        exact hrule i j k ((N.mem_buffersOf i j).1 hi)
      _ = deriv (fun z => A z j k) r := by rw [hsum, mul_one]
  calc
    Finset.sum (N.buffersOf j)
        (fun i => s.E b i j k - s.E a i j k) =
        Finset.sum (N.buffersOf j)
          (fun i => intervalIntegral
            (fun r => deriv (fun z => s.E z i j k) r)
            a b volume) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (((s.allocation_ac i j k).mono hsub).integral_deriv_eq_sub).symm
    _ = intervalIntegral
          (fun r => Finset.sum (N.buffersOf j)
            (fun i => deriv (fun z => s.E z i j k) r))
          a b volume := by
      exact (intervalIntegral.integral_finsetSum hEint).symm
    _ = intervalIntegral (fun r => deriv (fun z => A z j k) r)
          a b volume := by
      apply intervalIntegral.integral_congr_ae
      have hp :
          ∀ᵐ r ∂volume,
            r ∈ Set.uIoc a b ->
              Finset.sum (N.buffersOf j)
                  (fun i => deriv (fun z => s.E z i j k) r) =
                deriv (fun z => A z j k) r := by
        rw [← MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
        apply MeasureTheory.ae_restrict_of_ae_restrict_of_subset
          Set.uIoc_subset_uIcc
        rw [Set.uIcc_of_le hab]
        exact hpoint
      exact hp
    _ = A b j k - A a j k := hAac.integral_deriv_eq_sub

private theorem deriv_le_of_eventually_increment_le_right
    {f g : Real -> Real} {t : Real}
    (hf : DifferentiableAt Real f t)
    (hg : DifferentiableAt Real g t)
    (hinc :
      ∀ᶠ r in nhds t,
        t <= r -> f r - f t <= g r - g t) :
    deriv f t <= deriv g t := by
  let gap : Real -> Real := fun r => g r - f r
  have hlocal : IsLocalMinOn gap (Set.Ici t) t := by
    show ∀ᶠ r in nhdsWithin t (Set.Ici t), gap t <= gap r
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds hinc, self_mem_nhdsWithin] with r hr hrt
    dsimp [gap]
    have h := hr hrt
    linarith
  have hgap :
      HasDerivAt gap (deriv g t - deriv f t) t := by
    exact hg.hasDerivAt.sub hf.hasDerivAt
  have hone : (1 : Real) ∈ posTangentConeAt (Set.Ici t) t := by
    have hseg :
        segment Real t (t + 1) <= Set.Ici t := by
      rw [segment_eq_Icc (by linarith)]
      exact Set.Icc_subset_Ici_self
    convert sub_mem_posTangentConeAt_of_segment_subset hseg using 1 <;>
      ring
  have hnonneg :=
    hlocal.hasFDerivWithinAt_nonneg
      hgap.hasFDerivAt.hasFDerivWithinAt hone
  simpa using hnonneg

/-- Pointwise nonnegativity of compatible allocation derivatives at a
regular interior time. -/
theorem allocation_deriv_nonnegative
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (alpha : Simplex Buffer) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : N.compatible i j) :
    0 <= deriv (fun r => s.E r i j k) t := by
  let f : Real -> Real := fun _ => 0
  let g : Real -> Real := fun r => s.E r i j k
  have hf : DifferentiableAt Real f t := by
    fun_prop
  have hg : DifferentiableAt Real g t := hregular.2.2.2.1 i j k
  have hinc :
      ∀ᶠ r in nhds t,
        t <= r -> f r - f t <= g r - g t := by
    filter_upwards [Iio_mem_nhds hregular.1.2] with r hrT htr
    dsimp [f, g]
    simpa using
      (allocation_increment_nonnegative
        N s hregular.1.1 htr hrT i j k hij)
  have h := deriv_le_of_eventually_increment_le_right hf hg hinc
  simpa [f, g] using h

private theorem allocation_deriv_eq_zero_of_incompatible
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (alpha : Simplex Buffer) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    deriv (fun r => s.E r i j k) t = 0 := by
  have heq :
      (fun r => s.E r i j k) =ᶠ[nhds t] (fun _ => 0) := by
    filter_upwards
      [Icc_mem_nhds hregular.1.1 hregular.1.2] with r hr
    exact s.allocation_incompatible r hr i j k hij
  rw [heq.deriv_eq]
  simp

/-- The cumulative upper bound implies its pointwise derivative analogue
at every regular interior time. -/
theorem total_allocation_deriv_le_input
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (alpha : Simplex Buffer) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (j : Server) (k : Buffer) :
    Finset.sum (N.buffersOf j)
        (fun i => deriv (fun r => s.E r i j k) t) <=
      deriv (fun r => A r j k) t := by
  classical
  let f : Real -> Real :=
    fun r => Finset.sum (N.buffersOf j) (fun i => s.E r i j k)
  let g : Real -> Real := fun r => A r j k
  have hf : DifferentiableAt Real f t := by
    dsimp [f]
    exact DifferentiableAt.fun_sum
      (fun i _ => hregular.2.2.2.1 i j k)
  have hg : DifferentiableAt Real g t := by
    exact hregular.2.1 j k
  have hinc :
      ∀ᶠ r in nhds t,
        t <= r -> f r - f t <= g r - g t := by
    filter_upwards [Iio_mem_nhds hregular.1.2] with r hrT htr
    dsimp [f, g]
    have hbound :=
      total_allocation_increment_le_input N s hregular.1.1 htr hrT j k
    simpa [Finset.sum_sub_distrib] using hbound
  have hderiv := deriv_le_of_eventually_increment_le_right hf hg hinc
  simpa [f, g, deriv_fun_sum
    (fun i _ => hregular.2.2.2.1 i j k)] using hderiv

private theorem state_positive_of_lyapunov_lt_one
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (x : Buffer -> Real)
    (hL : Lyapunov.LAlphaAmbient (fun i => alpha i) x < 1) :
    forall i, 0 < x i := by
  intro i
  have hmin :
      0 < Lyapunov.minCoordinate (fun q => x q / alpha q) := by
    unfold Lyapunov.LAlphaAmbient at hL
    linarith
  have hratio :
      0 < x i / alpha i :=
    hmin.trans_le (Finset.inf'_le _ (Finset.mem_univ i))
  exact ((div_pos_iff.mp hratio).resolve_right
    (fun h => (not_lt_of_ge (halpha i).le h.2))).1

/-- Under non-idling, positivity near a regular state upgrades the total
allocation derivative bound to equality. -/
theorem total_allocation_deriv_eq_input_of_lyapunov_lt_one
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (hnonidle : N.IsNonIdlingSequence U)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (t : Real) (hregular : IsRegularPoint N alpha s t)
    (hL : Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1)
    (j : Server) (k : Buffer) :
    Finset.sum (N.buffersOf j)
        (fun i => deriv (fun r => s.E r i j k) t) =
      deriv (fun r => A r j k) t := by
  classical
  let f : Real -> Real :=
    fun r => Finset.sum (N.buffersOf j) (fun i => s.E r i j k)
  let g : Real -> Real := fun r => A r j k
  have hpositive_t :
      forall i, 0 < s.X t i :=
    state_positive_of_lyapunov_lt_one alpha halpha (s.X t) hL
  have hpositive_event :
      ∀ᶠ r in nhds t, forall i, 0 < s.X r i := by
    rw [Filter.eventually_all]
    intro i
    exact continuousAt_const.eventually_lt
      (hregular.2.2.1 i).continuousAt (hpositive_t i)
  obtain ⟨left, right, htinterval, hinterval⟩ :=
    hpositive_event.exists_Ioo_subset
  have hf : DifferentiableAt Real f t := by
    dsimp [f]
    exact DifferentiableAt.fun_sum
      (fun i _ => hregular.2.2.2.1 i j k)
  have hg : DifferentiableAt Real g t := hregular.2.1 j k
  have hincEq :
      ∀ᶠ r in nhds t,
        t <= r -> f r - f t = g r - g t := by
    filter_upwards [Iio_mem_nhds hregular.1.2,
      Iio_mem_nhds htinterval.2] with r hrT hrright htr
    have hpositive :
        forall z, z ∈ Set.Icc t r -> forall i, 0 < s.X z i := by
      intro z hz i
      apply hinterval
      exact ⟨htinterval.1.trans_le hz.1, hz.2.trans_lt hrright⟩
    have heq :=
      total_allocation_increment_eq_input_of_positive
        N s hnonidle hregular.1.1 htr hrT hpositive j k
    dsimp [f, g]
    simpa [Finset.sum_sub_distrib] using heq
  have hle : deriv f t <= deriv g t :=
    deriv_le_of_eventually_increment_le_right hf hg
      (hincEq.mono (fun r h htr => (h htr).le))
  have hge : deriv g t <= deriv f t :=
    deriv_le_of_eventually_increment_le_right hg hf
      (hincEq.mono (fun r h htr => (h htr).ge))
  have heq : deriv f t = deriv g t := le_antisymm hle hge
  simpa [f, g, deriv_fun_sum
    (fun i _ => hregular.2.2.2.1 i j k)] using heq

/-- Differentiating the exact queue-balance equation at a regular interior
time. -/
theorem state_deriv_eq_allocation_balance
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (alpha : Simplex Buffer) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (i : Buffer) :
    deriv (fun r => s.X r i) t =
      (Finset.sum Finset.univ (fun j =>
        Finset.sum (N.buffersOf j)
          (fun l => deriv (fun r => s.E r l j i) t))) -
      Finset.sum (N.serversOf i) (fun j =>
        Finset.sum Finset.univ
          (fun k => deriv (fun r => s.E r i j k) t)) := by
  classical
  let incoming : Real -> Real :=
    fun r => Finset.sum Finset.univ (fun j =>
      Finset.sum (N.buffersOf j) (fun l => s.E r l j i))
  let outgoing : Real -> Real :=
    fun r => Finset.sum (N.serversOf i) (fun j =>
      Finset.sum Finset.univ (fun k => s.E r i j k))
  have hincoming :
      HasDerivAt incoming
        (Finset.sum Finset.univ (fun j =>
          Finset.sum (N.buffersOf j)
            (fun l => deriv (fun r => s.E r l j i) t))) t := by
    dsimp [incoming]
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.fun_sum
    intro l _
    exact (hregular.2.2.2.1 l j i).hasDerivAt
  have houtgoing :
      HasDerivAt outgoing
        (Finset.sum (N.serversOf i) (fun j =>
          Finset.sum Finset.univ
            (fun k => deriv (fun r => s.E r i j k) t))) t := by
    dsimp [outgoing]
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.fun_sum
    intro k _
    exact (hregular.2.2.2.1 i j k).hasDerivAt
  have hrhs :
      HasDerivAt (fun r => x0 i + incoming r - outgoing r)
        (0 +
          Finset.sum Finset.univ (fun j =>
            Finset.sum (N.buffersOf j)
              (fun l => deriv (fun r => s.E r l j i) t)) -
          Finset.sum (N.serversOf i) (fun j =>
            Finset.sum Finset.univ
              (fun k => deriv (fun r => s.E r i j k) t))) t := by
    exact ((hasDerivAt_const t (x0 i)).add hincoming).sub houtgoing
  have hbalance :
      (fun r => s.X r i) =ᶠ[nhds t]
        (fun r => x0 i + incoming r - outgoing r) := by
    filter_upwards
      [Icc_mem_nhds hregular.1.1 hregular.1.2] with r hr
    exact s.balance r hr i
  have hfromBalance :=
    hrhs.congr_of_eventuallyEq hbalance
  have hunique :=
    (hregular.2.2.1 i).hasDerivAt.unique hfromBalance
  simpa using hunique

/-- Aggregate cut-flow inequality at a regular interior time.  This is the
previously missing premise of `steepestDescentLowerBound_le_of_cutFlow`. -/
theorem aggregate_cut_flow_deriv_le
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (hnonidle : N.IsNonIdlingSequence U)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (t : Real) (hregular : IsRegularPoint N alpha s t)
    (hL : Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1)
    (S : Finset Buffer) :
    Finset.sum S (fun i => deriv (fun r => s.X r i) t) <=
      Finset.sum Finset.univ (fun j =>
        Finset.sum S (fun k => deriv (fun r => A r j k) t)) -
      Finset.sum
        (Finset.univ.filter (fun j => N.buffersOf j <= S))
        (fun j => Finset.sum Finset.univ
          (fun k => deriv (fun r => A r j k) t)) := by
  classical
  have hEnonneg :
      forall i j k, 0 <= deriv (fun r => s.E r i j k) t := by
    intro i j k
    by_cases hij : N.compatible i j
    · exact allocation_deriv_nonnegative N s alpha t hregular i j k hij
    · rw [allocation_deriv_eq_zero_of_incompatible
        N s alpha t hregular i j k hij]
  have hstate :
      Finset.sum S (fun i => deriv (fun r => s.X r i) t) =
        Finset.sum S (fun i =>
          Finset.sum Finset.univ (fun j =>
            Finset.sum (N.buffersOf j)
              (fun l => deriv (fun r => s.E r l j i) t)) -
          Finset.sum (N.serversOf i) (fun j =>
            Finset.sum Finset.univ
              (fun k => deriv (fun r => s.E r i j k) t))) := by
    apply Finset.sum_congr rfl
    intro i _
    exact state_deriv_eq_allocation_balance N s alpha t hregular i
  have hincoming :
      Finset.sum S (fun i =>
          Finset.sum Finset.univ (fun j =>
            Finset.sum (N.buffersOf j)
              (fun l => deriv (fun r => s.E r l j i) t))) <=
        Finset.sum Finset.univ (fun j =>
          Finset.sum S (fun k => deriv (fun r => A r j k) t)) := by
    calc
      Finset.sum S (fun i =>
          Finset.sum Finset.univ (fun j =>
            Finset.sum (N.buffersOf j)
              (fun l => deriv (fun r => s.E r l j i) t))) =
          Finset.sum Finset.univ (fun j =>
            Finset.sum S (fun i =>
              Finset.sum (N.buffersOf j)
                (fun l => deriv (fun r => s.E r l j i) t))) := by
        rw [Finset.sum_comm]
      _ <= Finset.sum Finset.univ (fun j =>
          Finset.sum S (fun k => deriv (fun r => A r j k) t)) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro k _
        exact total_allocation_deriv_le_input
          N s alpha t hregular j k
  have hserverExpand :
      forall i,
        Finset.sum (N.serversOf i) (fun j =>
            Finset.sum Finset.univ
              (fun k => deriv (fun r => s.E r i j k) t)) =
          Finset.sum Finset.univ (fun j =>
            Finset.sum Finset.univ
              (fun k => deriv (fun r => s.E r i j k) t)) := by
    intro i
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hij : Not (N.compatible i j) := by
      intro hcompat
      exact hj ((N.mem_serversOf i j).2 hcompat)
    apply Finset.sum_eq_zero
    intro k _
    exact allocation_deriv_eq_zero_of_incompatible
      N s alpha t hregular i j k hij
  have houtgoing :
      Finset.sum
          (Finset.univ.filter (fun j => N.buffersOf j <= S))
          (fun j => Finset.sum Finset.univ
            (fun k => deriv (fun r => A r j k) t)) <=
        Finset.sum S (fun i =>
          Finset.sum (N.serversOf i) (fun j =>
            Finset.sum Finset.univ
              (fun k => deriv (fun r => s.E r i j k) t))) := by
    calc
      Finset.sum
          (Finset.univ.filter (fun j => N.buffersOf j <= S))
          (fun j => Finset.sum Finset.univ
            (fun k => deriv (fun r => A r j k) t)) =
          Finset.sum
            (Finset.univ.filter (fun j => N.buffersOf j <= S))
            (fun j => Finset.sum Finset.univ (fun k =>
              Finset.sum (N.buffersOf j)
                (fun i => deriv (fun r => s.E r i j k) t))) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        exact (total_allocation_deriv_eq_input_of_lyapunov_lt_one
          N s hnonidle alpha halpha t hregular hL j k).symm
      _ = Finset.sum
            (Finset.univ.filter (fun j => N.buffersOf j <= S))
            (fun j => Finset.sum (N.buffersOf j) (fun i =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t))) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      _ = Finset.sum
            (Finset.univ.filter (fun j => N.buffersOf j <= S))
            (fun j => Finset.sum S (fun i =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t))) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjsub : N.buffersOf j <= S :=
          (Finset.mem_filter.1 hj).2
        apply Finset.sum_subset hjsub
        intro i hiS hiBuffer
        have hij : Not (N.compatible i j) := by
          intro hcompat
          exact hiBuffer ((N.mem_buffersOf i j).2 hcompat)
        apply Finset.sum_eq_zero
        intro k _
        exact allocation_deriv_eq_zero_of_incompatible
          N s alpha t hregular i j k hij
      _ <= Finset.sum Finset.univ (fun j =>
            Finset.sum S (fun i =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t))) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _)
        intro j _ _
        apply Finset.sum_nonneg
        intro i _
        exact Finset.sum_nonneg (fun k _ => hEnonneg i j k)
      _ = Finset.sum S (fun i =>
            Finset.sum Finset.univ (fun j =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t))) := by
        rw [Finset.sum_comm]
      _ = Finset.sum S (fun i =>
            Finset.sum (N.serversOf i) (fun j =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hserverExpand i).symm
  rw [hstate, Finset.sum_sub_distrib]
  exact sub_le_sub hincoming houtgoing

/-- The full non-SMW lower-bound clause of the paper's Lyapunov derivative
lemma, now discharged from the fluid-model fields. -/
theorem steepestDescentLowerBound_le_lyapunovDrift
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence}
    (hnonidle : N.IsNonIdlingSequence U)
    {T : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (hL : Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1) :
    steepestDescentLowerBound (N := N) alpha A s.X t <=
      lyapunovDrift alpha s.X t := by
  let S := minimumDerivativeBuffers alpha (s.X t)
    (fun i => deriv (fun r => s.X r i) t)
  apply steepestDescentLowerBound_le_of_cutFlow
    N alpha halpha s t hregular
  change
    Finset.sum S (fun i => deriv (fun r => s.X r i) t) <=
      Finset.sum Finset.univ (fun j =>
        Finset.sum S (fun k => deriv (fun r => A r j k) t)) -
      Finset.sum
        (Finset.univ.filter (fun j => N.buffersOf j <= S))
        (fun j => Finset.sum Finset.univ
          (fun k => deriv (fun r => A r j k) t))
  exact aggregate_cut_flow_deriv_le
    N s hnonidle alpha halpha t hregular hL S

/-- The two policy-independent conclusions of
`LyapunovDerivativeStatement`, proved together from its printed
hypotheses. -/
theorem lyapunovDerivative_identity_and_lower_bound
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence}
    (hnonidle : N.IsNonIdlingSequence U)
    {T : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (hL : Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1) :
    let S := minimumDerivativeBuffers alpha (s.X t)
      (fun i => deriv (fun r => s.X r i) t)
    (forall k, k ∈ S ->
      lyapunovDrift alpha s.X t =
        -deriv (fun r => s.X r k) t / alpha k) /\
    steepestDescentLowerBound (N := N) alpha A s.X t <=
      lyapunovDrift alpha s.X t := by
  dsimp
  constructor
  · exact lyapunovDerivative_first_clause
      N alpha halpha s t hregular
  · exact steepestDescentLowerBound_le_lyapunovDrift
      N alpha halpha hnonidle s t hregular hL

/-- Minimal obstruction to replacing the missing local SMW correspondence
argument by pointwise specialization of `FluidModelSolution.policy_rule`.

Membership in a closed policy set almost everywhere on the fluid horizon
does not imply membership at a specified regular time.  The SMW equality
therefore needs the source's genuine right-neighborhood strict-gap
argument; the almost-everywhere field alone cannot be evaluated at `t`.
-/
theorem ae_closed_policy_membership_not_pointwise :
    let policySet : Set Real := {0}
    let p : Real -> Real :=
      fun r => if r = (2 : Real)⁻¹ then 1 else 0
    IsClosed policySet /\
    (∀ᵐ r ∂volume.restrict (Set.Icc (0 : Real) 1),
      p r ∈ policySet) /\
    Not (p (2 : Real)⁻¹ ∈ policySet) := by
  dsimp
  constructor
  · exact isClosed_singleton
  constructor
  · apply ae_restrict_of_ae
    filter_upwards [volume.ae_ne (2 : Real)⁻¹] with r hr
    simp [hr]
  · norm_num

end StateDepMOR.PaperStatements.Network
