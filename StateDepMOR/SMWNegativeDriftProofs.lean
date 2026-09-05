import StateDepMOR.FluidSMWProofs
import StateDepMOR.SMWNegativeDriftCore

/-!
# Unconditional SMW negative drift

This module proves the paper's negative-drift statement, including the
boundary case where `LAlphaAmbient = 1`.  At that boundary, the
minimum-scaled queues are exactly the zero queues.  Their derivatives vanish,
while the SMW right-neighborhood allocation rule and the uniform cut gap
force their aggregate derivative to be positive, a contradiction.
-/

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]
variable [LinearOrder Buffer]

private theorem nonidle_correspondence_none_eq_zero_of_positive
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (hnonidle : N.IsNonIdlingSequence U)
    (x : Buffer -> Real)
    (j : Server) (k q : Buffer)
    (hqj : N.compatible q j) (hxq : 0 < x q)
    (p : StateDepMOR.Network.ActionVector Buffer)
    (hp : p ∈ N.fluidPolicyCorrespondence U j k x) :
    p none = 0 := by
  classical
  let eps : {e : Real // 0 < e} := ⟨x q / 2, half_pos hxq⟩
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
    obtain ⟨K, z, _hK, hnear, rfl⟩ := hr
    have hKpos : 0 < ((K : Nat) : Real) := by
      exact_mod_cast K.pos
    have hqnear := hnear q
    rw [abs_lt] at hqnear
    have hzqRatio : 0 < (z q : Real) / (K : Real) := by
      dsimp [eps] at hqnear
      linarith
    have hzq : 0 < z q := by
      have hzqReal : 0 < (z q : Real) := by
        rcases div_pos_iff.mp hzqRatio with h | h
        · exact h.1
        · exact (not_lt_of_ge hKpos.le h.2).elim
      exact_mod_cast hzqReal
    have haction : Not (U K z j k = none) := by
      intro hnone
      have hall := (hnonidle K z j k).1 hnone
      exact (Nat.ne_of_gt hzq) (hall q hqj)
    have haction' : Not (none = U K z j k) :=
      fun h => haction h.symm
    simp [H, StateDepMOR.Network.actionDirac, haction']
  unfold StateDepMOR.Network.fluidPolicyCorrespondence at hp
  have hpeps := Set.mem_iInter.1 hp eps
  exact closure_minimal (convexHull_min hbase hHconvex) hHclosed hpeps

private theorem smw_correspondence_zero_of_strictly_submax
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hsmw : N.IsSMWPolicy alpha U)
    (x : Buffer -> Real)
    (j : Server) (k i q : Buffer)
    (_hij : N.compatible i j)
    (hqj : N.compatible q j)
    (hxq : 0 < x q)
    (hgap : x i / alpha i < x q / alpha q)
    (p : StateDepMOR.Network.ActionVector Buffer)
    (hp : p ∈ N.fluidPolicyCorrespondence U j k x) :
    p (some i) = 0 := by
  classical
  let gap : Real := x q / alpha q - x i / alpha i
  let c : Real := 1 / alpha q + 1 / alpha i
  have hgapPos : 0 < gap := by
    dsimp [gap]
    linarith
  have hcPos : 0 < c := by
    dsimp [c]
    exact add_pos (one_div_pos.mpr (halpha q))
      (one_div_pos.mpr (halpha i))
  let epsVal : Real := min (x q / 2) (gap / (2 * c))
  have hepsPos : 0 < epsVal := by
    dsimp [epsVal]
    exact lt_min (half_pos hxq)
      (div_pos hgapPos (mul_pos two_pos hcPos))
  let eps : {e : Real // 0 < e} := ⟨epsVal, hepsPos⟩
  let H : Set (StateDepMOR.Network.ActionVector Buffer) :=
    {r | r (some i) = 0}
  have hHclosed : IsClosed H := by
    exact isClosed_eq (continuous_apply (some i)) continuous_const
  have hHconvex : Convex Real H := by
    exact convex_hyperplane (LinearMap.proj (some i)).isLinear 0
  have hbase :
      {r | exists K : PNat, exists z : JobState Buffer (K : Nat),
        eps.1⁻¹ <= (K : Real) /\
        StateDepMOR.Network.IsNearNormalizedState z x eps.1 /\
        r = N.actionDirac (U K z j k)} <= H := by
    intro r hr
    obtain ⟨K, z, _hK, hnear, rfl⟩ := hr
    have hKpos : 0 < ((K : Nat) : Real) := by
      exact_mod_cast K.pos
    have hqnear := hnear q
    have hinear := hnear i
    rw [abs_lt] at hqnear hinear
    have hepsQ : epsVal <= x q / 2 := by
      exact min_le_left _ _
    have hepsGap : epsVal <= gap / (2 * c) := by
      exact min_le_right _ _
    have hqNormPos : 0 < (z q : Real) / (K : Real) := by
      dsimp [eps] at hqnear
      linarith
    have herror :
        epsVal / alpha q + epsVal / alpha i <= gap / 2 := by
      have heq :
          epsVal / alpha q + epsVal / alpha i = epsVal * c := by
        dsimp [c]
        ring
      rw [heq]
      have hmul := mul_le_mul_of_nonneg_right hepsGap hcPos.le
      have hcne : Not (c = 0) := ne_of_gt hcPos
      field_simp [hcne] at hmul
      nlinarith
    have hnormGap :
        (z i : Real) / (K : Real) / alpha i <
          (z q : Real) / (K : Real) / alpha q := by
      have hiUpper :
          (z i : Real) / (K : Real) / alpha i <
            (x i + epsVal) / alpha i := by
        apply (div_lt_div_iff_of_pos_right (halpha i)).2
        dsimp [eps] at hinear
        linarith
      have hqLower :
          (x q - epsVal) / alpha q <
            (z q : Real) / (K : Real) / alpha q := by
        apply (div_lt_div_iff_of_pos_right (halpha q)).2
        dsimp [eps] at hqnear
        linarith
      have hmiddle :
          (x i + epsVal) / alpha i <
            (x q - epsVal) / alpha q := by
        dsimp [gap] at hgapPos herror
        have hiExpand :
            (x i + epsVal) / alpha i =
              x i / alpha i + epsVal / alpha i := by ring
        have hqExpand :
            (x q - epsVal) / alpha q =
              x q / alpha q - epsVal / alpha q := by ring
        rw [hiExpand, hqExpand]
        linarith
      exact hiUpper.trans (hmiddle.trans hqLower)
    have hdiscGap :
        (z i : Real) / alpha i < (z q : Real) / alpha q := by
      calc
        (z i : Real) / alpha i =
            (K : Real) * ((z i : Real) / (K : Real) / alpha i) := by
          field_simp [ne_of_gt hKpos]
        _ < (K : Real) * ((z q : Real) / (K : Real) / alpha q) :=
          mul_lt_mul_of_pos_left hnormGap hKpos
        _ = (z q : Real) / alpha q := by
          field_simp [ne_of_gt hKpos]
    have hzq : 0 < z q := by
      have hzqReal : 0 < (z q : Real) := by
        exact (div_pos_iff.mp hqNormPos).resolve_right
          (fun h => (not_lt_of_ge hKpos.le h.2)) |>.1
      exact_mod_cast hzqReal
    have hspec := hsmw.2 K z j k
    unfold StateDepMOR.Network.IsSMWAction at hspec
    rw [if_pos ⟨q, hqj, hzq⟩] at hspec
    obtain ⟨winner, haction, _hwpos, hwinner⟩ := hspec
    have hnotAction : Not (U K z j k = some i) := by
      intro hai
      have hwi : winner = i := Option.some.inj (haction.symm.trans hai)
      subst winner
      have hmax := hwinner.2.1 q hqj
      exact (not_le_of_gt hdiscGap) hmax
    have hnotAction' : Not (some i = U K z j k) :=
      fun h => hnotAction h.symm
    simp [H, StateDepMOR.Network.actionDirac, hnotAction']
  unfold StateDepMOR.Network.fluidPolicyCorrespondence at hp
  have hpeps := Set.mem_iInter.1 hp eps
  exact closure_minimal (convexHull_min hbase hHconvex) hHclosed hpeps

private theorem deriv_eq_zero_of_eventually_eq_right
    {f : Real -> Real} {t : Real}
    (hf : DifferentiableAt Real f t)
    (heq : ∀ᶠ r in nhds t, t <= r -> f r = f t) :
    deriv f t = 0 := by
  have hmin : IsLocalMinOn f (Set.Ici t) t := by
    show ∀ᶠ r in nhdsWithin t (Set.Ici t), f t <= f r
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds heq, self_mem_nhdsWithin] with r hr hrt
    exact (hr hrt).ge
  have hmax : IsLocalMaxOn f (Set.Ici t) t := by
    show ∀ᶠ r in nhdsWithin t (Set.Ici t), f r <= f t
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds heq, self_mem_nhdsWithin] with r hr hrt
    exact (hr hrt).le
  have hone : (1 : Real) ∈ posTangentConeAt (Set.Ici t) t := by
    have hseg :
        segment Real t (t + 1) <= Set.Ici t := by
      rw [segment_eq_Icc (by linarith)]
      exact Set.Icc_subset_Ici_self
    convert sub_mem_posTangentConeAt_of_segment_subset hseg using 1
    all_goals ring
  have hnonneg :=
    hmin.hasFDerivWithinAt_nonneg
      hf.hasFDerivAt.hasFDerivWithinAt hone
  have hnonpos :=
    hmax.hasFDerivWithinAt_nonpos
      hf.hasFDerivAt.hasFDerivWithinAt hone
  have h1 : 0 <= deriv f t := by simpa using hnonneg
  have h2 : deriv f t <= 0 := by simpa using hnonpos
  exact le_antisymm h2 h1

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

private theorem total_allocation_increment_eq_input_of_server_positive
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (hnonidle : N.IsNonIdlingSequence U)
    {a b : Real} (ha : 0 < a) (hab : a <= b) (hb : b < T)
    (j : Server) (q : Buffer) (hqj : N.compatible q j)
    (hpositive : forall r, r ∈ Set.Icc a b -> 0 < s.X r q)
    (k : Buffer) :
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
          (fun c => s.p r j k c) ∈
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
      nonidle_correspondence_none_eq_zero_of_positive
        N U hnonidle (s.X r) j k q hqj (hpositive r hrange)
        (fun c => s.p r j k c) (hpol j k)
    have hall :
        Finset.sum (N.buffersOf j)
            (fun i => s.p r j k (some i)) =
          Finset.sum Finset.univ
            (fun i => s.p r j k (some i)) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      have hincompat : Not (N.compatible i j) := by
        intro hij
        exact hi ((N.mem_buffersOf i j).2 hij)
      exact s.fractions_incompatible r hrangeT j k i hincompat
    have htotal := (s.fractions_in_simplex r hrangeT j k).2
    rw [Fintype.sum_option, hnone, zero_add] at htotal
    have hsum :
        Finset.sum (N.buffersOf j)
            (fun i => s.p r j k (some i)) = 1 :=
      hall.trans htotal
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

private theorem total_allocation_deriv_eq_input_of_server_positive
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (hnonidle : N.IsNonIdlingSequence U)
    (alpha : Simplex Buffer) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (j : Server) (q : Buffer) (hqj : N.compatible q j)
    (hxq : 0 < s.X t q) (k : Buffer) :
    Finset.sum (N.buffersOf j)
        (fun i => deriv (fun r => s.E r i j k) t) =
      deriv (fun r => A r j k) t := by
  classical
  let f : Real -> Real :=
    fun r => Finset.sum (N.buffersOf j) (fun i => s.E r i j k)
  let g : Real -> Real := fun r => A r j k
  let gap : Real -> Real := fun r => g r - f r
  have hpositive :
      ∀ᶠ r in nhds t, 0 < s.X r q :=
    continuousAt_const.eventually_lt
      (hregular.2.2.1 q).continuousAt hxq
  obtain ⟨left, right, htIoo, hIoo⟩ :=
    hpositive.exists_Ioo_subset
  have hevent :
      ∀ᶠ r in nhds t, t <= r -> gap r = gap t := by
    filter_upwards
      [Iio_mem_nhds htIoo.2, Iio_mem_nhds hregular.1.2] with
        r hrRight hrT htr
    have hpositiveIcc :
        forall z, z ∈ Set.Icc t r -> 0 < s.X z q := by
      intro z hz
      exact hIoo ⟨htIoo.1.trans_le hz.1, hz.2.trans_lt hrRight⟩
    have hinc :=
      total_allocation_increment_eq_input_of_server_positive
        N s hnonidle hregular.1.1 htr hrT j q hqj hpositiveIcc k
    dsimp [gap, f, g]
    rw [Finset.sum_sub_distrib] at hinc
    linarith
  have hfdiff : DifferentiableAt Real f t := by
    dsimp [f]
    exact DifferentiableAt.fun_sum
      (fun i _ => hregular.2.2.2.1 i j k)
  have hgdiff : DifferentiableAt Real g t := hregular.2.1 j k
  have hgapHas :
      HasDerivAt gap
        (deriv (fun r => A r j k) t -
          Finset.sum (N.buffersOf j)
            (fun i => deriv (fun r => s.E r i j k) t)) t := by
    dsimp [gap, g, f]
    exact (hregular.2.1 j k).hasDerivAt.sub
      (HasDerivAt.fun_sum
        (fun i _ => (hregular.2.2.2.1 i j k).hasDerivAt))
  have hgapzero :
      deriv gap t = 0 :=
    deriv_eq_zero_of_eventually_eq_right hgapHas.differentiableAt hevent
  have hgapDeriv :
      deriv gap t =
        deriv (fun r => A r j k) t -
          Finset.sum (N.buffersOf j)
            (fun i => deriv (fun r => s.E r i j k) t) := by
    exact hgapHas.deriv
  rw [hgapDeriv] at hgapzero
  linarith

private theorem smw_zero_queue_cross_allocation_deriv_eq_zero
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence}
    (hsmw : N.IsSMWPolicy alpha U)
    {T : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (t : Real) (hregular : IsRegularPoint N alpha s t)
    (i q : Buffer) (hxi : s.X t i = 0) (hxq : 0 < s.X t q)
    (j : Server) (hij : N.compatible i j) (hqj : N.compatible q j)
    (k : Buffer) :
    deriv (fun r => s.E r i j k) t = 0 := by
  have hgapAt :
      s.X t i / alpha i < s.X t q / alpha q := by
    rw [hxi, zero_div]
    exact div_pos hxq (halpha q)
  have hgapEvent :
      ∀ᶠ r in nhds t,
        s.X r i / alpha i < s.X r q / alpha q :=
    ((hregular.2.2.1 i).continuousAt.div_const (alpha i)).eventually_lt
      ((hregular.2.2.1 q).continuousAt.div_const (alpha q)) hgapAt
  have hposEvent :
      ∀ᶠ r in nhds t, 0 < s.X r q :=
    continuousAt_const.eventually_lt
      (hregular.2.2.1 q).continuousAt hxq
  have hgood :
      ∀ᶠ r in nhds t,
        s.X r i / alpha i < s.X r q / alpha q /\
        0 < s.X r q /\
        r < T := by
    filter_upwards
      [hgapEvent, hposEvent, Iio_mem_nhds hregular.1.2] with r hgap hpos hrT
    exact ⟨hgap, hpos, hrT⟩
  obtain ⟨left, right, htIoo, hIoo⟩ := hgood.exists_Ioo_subset
  let b : Real := (t + right) / 2
  have htb : t < b := by
    have htright : t < right := htIoo.2
    dsimp [b]
    nlinarith
  have hbr : b < right := by
    have htright : t < right := htIoo.2
    dsimp [b]
    nlinarith
  have hbT : b < T := by
    exact (hIoo ⟨htIoo.1.trans htb, hbr⟩).2.2
  have hzero :
      ∀ᵐ r ∂volume,
        r ∈ Set.Ioc t b ->
          deriv (fun z => s.E z i j k) r = 0 := by
    have hpolicy := s.policy_rule
    have halloc := s.allocation_rule
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at hpolicy halloc
    filter_upwards [hpolicy, halloc] with r hpol hallocR hr
    have hrGood := hIoo
      ⟨htIoo.1.trans hr.1, hr.2.trans_lt hbr⟩
    have hrT : r ∈ Set.Icc (0 : Real) T :=
      ⟨(hregular.1.1.trans hr.1).le, hrGood.2.2.le⟩
    have hpMem := hpol hrT j k
    have hpZero :=
      smw_correspondence_zero_of_strictly_submax
        N alpha halpha U hsmw (s.X r) j k i q hij hqj
        hrGood.2.1 hrGood.1 (fun c => s.p r j k c) hpMem
    rw [hallocR hrT i j k hij, hpZero, mul_zero]
  have hevent :
      ∀ᶠ r in nhds t,
        t <= r -> s.E r i j k = s.E t i j k := by
    filter_upwards [Iio_mem_nhds htb] with r hrb htr
    by_cases hrt : r = t
    · subst r
      rfl
    · have htrStrict : t < r := lt_of_le_of_ne htr (Ne.symm hrt)
      have hsub : Set.uIcc t r <= Set.uIcc (0 : Real) T := by
        rw [Set.uIcc_of_le htr, Set.uIcc_of_le
          (hregular.1.1.le.trans
            (htr.trans (hrb.le.trans hbT.le)))]
        exact Set.Icc_subset_Icc hregular.1.1.le
          (hrb.le.trans hbT.le)
      have hEac := (s.allocation_ac i j k).mono hsub
      have hintZero :
          intervalIntegral (fun z => deriv (fun y => s.E y i j k) z)
            t r volume = 0 := by
        calc
          intervalIntegral (fun z => deriv (fun y => s.E y i j k) z)
              t r volume =
              intervalIntegral (fun _ => (0 : Real)) t r volume := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [hzero] with z hz hztr
            apply hz
            rw [Set.uIoc_of_le htrStrict.le] at hztr
            exact ⟨hztr.1, hztr.2.trans hrb.le⟩
          _ = 0 := by simp
      have hsubEq := hEac.integral_deriv_eq_sub
      rw [hintZero] at hsubEq
      linarith
  exact deriv_eq_zero_of_eventually_eq_right
    (hregular.2.2.2.1 i j k) hevent

private theorem state_deriv_eq_zero_of_state_eq_zero
    (N : Network Buffer Server)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (alpha : Simplex Buffer) (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (i : Buffer) (hxi : s.X t i = 0) :
    deriv (fun r => s.X r i) t = 0 := by
  have hlocal : IsLocalMin (fun r => s.X r i) t := by
    show ∀ᶠ r in nhds t, s.X t i <= s.X r i
    filter_upwards
      [Icc_mem_nhds hregular.1.1 hregular.1.2] with r hr
    rw [hxi]
    exact (s.state_in_simplex r hr).1 i
  exact hlocal.deriv_eq_zero

private theorem mem_minimumScaledBuffers_iff_state_eq_zero_of_L_eq_one
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (x : Buffer -> Real) (hx : forall i, 0 <= x i)
    (hL : Lyapunov.LAlphaAmbient (fun i => alpha i) x = 1)
    (i : Buffer) :
    i ∈ minimumScaledBuffers alpha x <-> x i = 0 := by
  classical
  have hminzero :
      Lyapunov.minCoordinate (fun q => x q / alpha q) = 0 := by
    unfold Lyapunov.LAlphaAmbient at hL
    linarith
  constructor
  · intro hi
    have hiMin :
        forall k, x i / alpha i <= x k / alpha k :=
      (Finset.mem_filter.1 hi).2
    obtain ⟨q, _hqmem, hq⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun k => x k / alpha k)
    have hiratioNonneg : 0 <= x i / alpha i :=
      div_nonneg (hx i) (halpha i).le
    have hiratioZero : x i / alpha i = 0 := by
      have hle := hiMin q
      change Lyapunov.minCoordinate (fun k => x k / alpha k) =
        x q / alpha q at hq
      rw [← hq, hminzero] at hle
      exact le_antisymm hle hiratioNonneg
    exact (div_eq_zero_iff).1 hiratioZero |>.resolve_right
      (ne_of_gt (halpha i))
  · intro hxi
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ i, ?_⟩
    intro k
    rw [hxi, zero_div]
    have hle :=
      Finset.inf'_le (fun q => x q / alpha q) (Finset.mem_univ k)
    change Lyapunov.minCoordinate (fun q => x q / alpha q) <=
      x k / alpha k at hle
    rwa [hminzero] at hle

private theorem minimumScaledBuffers_nonempty_of_L_eq_one
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (x : Buffer -> Real) (hx : forall i, 0 <= x i)
    (hL : Lyapunov.LAlphaAmbient (fun i => alpha i) x = 1) :
    (minimumScaledBuffers alpha x).Nonempty := by
  classical
  obtain ⟨i, _hi, hmin⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun k => x k / alpha k)
  have hminzero :
      Lyapunov.minCoordinate (fun q => x q / alpha q) = 0 := by
    unfold Lyapunov.LAlphaAmbient at hL
    linarith
  have hratio : x i / alpha i = 0 := by
    change Lyapunov.minCoordinate (fun k => x k / alpha k) =
      x i / alpha i at hmin
    rw [← hmin]
    exact hminzero
  have hxi : x i = 0 :=
    (div_eq_zero_iff).1 hratio |>.resolve_right (ne_of_gt (halpha i))
  exact ⟨i,
    (mem_minimumScaledBuffers_iff_state_eq_zero_of_L_eq_one
      alpha halpha x hx hL i).2 hxi⟩

private theorem minimumScaledBuffers_ne_univ_of_sum_eq_one
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (x : Buffer -> Real) (hx : forall i, 0 <= x i)
    (hsum : Finset.univ.sum x = 1)
    (hL : Lyapunov.LAlphaAmbient (fun i => alpha i) x = 1) :
    Not (minimumScaledBuffers alpha x = Finset.univ) := by
  classical
  intro hS
  have hzero : forall i, x i = 0 := by
    intro i
    apply
      (mem_minimumScaledBuffers_iff_state_eq_zero_of_L_eq_one
        alpha halpha x hx hL i).1
    rw [hS]
    simp
  have : Finset.univ.sum x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hzero i
  linarith

private theorem boundary_cutDrift_le_aggregate_state_deriv
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence}
    (hnonidle : N.IsNonIdlingSequence U)
    (hsmw : N.IsSMWPolicy alpha U)
    {T : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (t : Real) (hregular : IsRegularPoint N alpha s t)
    (S : Finset Buffer)
    (hzero : forall i, i ∈ S -> s.X t i = 0)
    (hpositive : forall i, i ∉ S -> 0 < s.X t i) :
    N.cutDrift S (pathDerivative A t) <=
      Finset.sum S (fun i => deriv (fun r => s.X r i) t) := by
  classical
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
  have hstate :
      Finset.sum S (fun i => deriv (fun r => s.X r i) t) =
        Finset.sum Finset.univ (fun j =>
          Finset.sum S (fun k =>
            Finset.sum (N.buffersOf j)
              (fun i => deriv (fun r => s.E r i j k) t)) -
          Finset.sum S (fun i =>
            Finset.sum Finset.univ
              (fun k => deriv (fun r => s.E r i j k) t))) := by
    calc
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
      _ = Finset.sum S (fun i =>
            Finset.sum Finset.univ (fun j =>
              Finset.sum (N.buffersOf j)
                (fun l => deriv (fun r => s.E r l j i) t))) -
          Finset.sum S (fun i =>
            Finset.sum (N.serversOf i) (fun j =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t))) := by
        rw [Finset.sum_sub_distrib]
      _ = Finset.sum Finset.univ (fun j =>
            Finset.sum S (fun k =>
              Finset.sum (N.buffersOf j)
                (fun i => deriv (fun r => s.E r i j k) t))) -
          Finset.sum S (fun i =>
            Finset.sum Finset.univ (fun j =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t))) := by
        congr 1
        · rw [Finset.sum_comm]
        · apply Finset.sum_congr rfl
          intro i _
          exact hserverExpand i
      _ = Finset.sum Finset.univ (fun j =>
            Finset.sum S (fun k =>
              Finset.sum (N.buffersOf j)
                (fun i => deriv (fun r => s.E r i j k) t))) -
          Finset.sum Finset.univ (fun j =>
            Finset.sum S (fun i =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t))) := by
        congr 1
        rw [Finset.sum_comm]
      _ = Finset.sum Finset.univ (fun j =>
          Finset.sum S (fun k =>
            Finset.sum (N.buffersOf j)
              (fun i => deriv (fun r => s.E r i j k) t)) -
          Finset.sum S (fun i =>
            Finset.sum Finset.univ
              (fun k => deriv (fun r => s.E r i j k) t))) := by
        rw [Finset.sum_sub_distrib]
  have hperServer :
      forall j,
        Finset.sum S (fun k => deriv (fun r => A r j k) t) -
            (if N.buffersOf j <= S then
              Finset.sum Finset.univ
                (fun k => deriv (fun r => A r j k) t)
            else 0) <=
          Finset.sum S (fun k =>
            Finset.sum (N.buffersOf j)
              (fun i => deriv (fun r => s.E r i j k) t)) -
          Finset.sum S (fun i =>
            Finset.sum Finset.univ
              (fun k => deriv (fun r => s.E r i j k) t)) := by
    intro j
    by_cases hj : N.buffersOf j <= S
    · rw [if_pos hj]
      have houtgoing :
          Finset.sum S (fun i =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t)) =
            Finset.sum Finset.univ (fun k =>
              Finset.sum (N.buffersOf j)
                (fun i => deriv (fun r => s.E r i j k) t)) := by
        calc
          Finset.sum S (fun i =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t)) =
              Finset.sum (N.buffersOf j) (fun i =>
                Finset.sum Finset.univ
                  (fun k => deriv (fun r => s.E r i j k) t)) := by
            symm
            apply Finset.sum_subset hj
            intro i hiS hiBuffer
            have hij : Not (N.compatible i j) := by
              intro hcompat
              exact hiBuffer ((N.mem_buffersOf i j).2 hcompat)
            apply Finset.sum_eq_zero
            intro k _
            exact allocation_deriv_eq_zero_of_incompatible
              N s alpha t hregular i j k hij
          _ = Finset.sum Finset.univ (fun k =>
              Finset.sum (N.buffersOf j)
                (fun i => deriv (fun r => s.E r i j k) t)) := by
            rw [Finset.sum_comm]
      let alloc : Buffer -> Real :=
        fun k => Finset.sum (N.buffersOf j)
          (fun i => deriv (fun r => s.E r i j k) t)
      let input : Buffer -> Real :=
        fun k => deriv (fun r => A r j k) t
      have houtside :
          Finset.sum (Finset.univ \ S) alloc <=
            Finset.sum (Finset.univ \ S) input := by
        apply Finset.sum_le_sum
        intro k _
        exact total_allocation_deriv_le_input
          N s alpha t hregular j k
      have hsplitAlloc :=
        Finset.sum_sdiff (Finset.subset_univ S) (f := alloc)
      have hsplitInput :=
        Finset.sum_sdiff (Finset.subset_univ S) (f := input)
      dsimp [alloc, input] at houtside hsplitAlloc hsplitInput
      rw [houtgoing]
      linarith
    · rw [if_neg hj, sub_zero]
      obtain ⟨q, hqBuffer, hqNotS⟩ := Finset.not_subset.mp hj
      have hqj : N.compatible q j := (N.mem_buffersOf q j).1 hqBuffer
      have hqpos : 0 < s.X t q := hpositive q hqNotS
      have hincoming :
          Finset.sum S (fun k =>
              Finset.sum (N.buffersOf j)
                (fun i => deriv (fun r => s.E r i j k) t)) =
            Finset.sum S (fun k => deriv (fun r => A r j k) t) := by
        apply Finset.sum_congr rfl
        intro k _
        exact total_allocation_deriv_eq_input_of_server_positive
          N s hnonidle alpha t hregular j q hqj hqpos k
      have houtgoing :
          Finset.sum S (fun i =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hiS
        apply Finset.sum_eq_zero
        intro k _
        by_cases hij : N.compatible i j
        · exact smw_zero_queue_cross_allocation_deriv_eq_zero
            N alpha halpha hsmw s t hregular i q (hzero i hiS)
              hqpos j hij hqj k
        · exact allocation_deriv_eq_zero_of_incompatible
            N s alpha t hregular i j k hij
      rw [hincoming, houtgoing, sub_zero]
  unfold StateDepMOR.Network.cutDrift
  unfold StateDepMOR.Network.serversContainedIn
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib, hstate]
  exact Finset.sum_le_sum (fun j _ => hperServer j)

private theorem regular_smw_boundary_impossible_of_uniform_cut_gap
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence}
    (hnonidle : N.IsNonIdlingSequence U)
    (hsmw : N.IsSMWPolicy alpha U)
    (g0 epsilon : Real) (hg0 : 0 < g0)
    (hgap :
      forall (f : Server -> Buffer -> Real),
        (forall j k, |f j k - N.phi j k| < epsilon) ->
        forall S : Finset Buffer, S.Nonempty ->
          Not (S = Finset.univ) -> g0 / 2 <= N.cutDrift S f)
    {T : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (t : Real) (hregular : IsRegularPoint N alpha s t)
    (hL : Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) = 1)
    (hf :
      forall j k,
        |pathDerivative A t j k - N.phi j k| < epsilon) :
    False := by
  classical
  let S := minimumScaledBuffers alpha (s.X t)
  have htIcc : t ∈ Set.Icc (0 : Real) T :=
    ⟨hregular.1.1.le, hregular.1.2.le⟩
  have hx := s.state_in_simplex t htIcc
  have hSnonempty : S.Nonempty :=
    minimumScaledBuffers_nonempty_of_L_eq_one
      alpha halpha (s.X t) hx.1 hL
  have hSproper : Not (S = Finset.univ) :=
    minimumScaledBuffers_ne_univ_of_sum_eq_one
      alpha halpha (s.X t) hx.1 hx.2 hL
  have hzero : forall i, i ∈ S -> s.X t i = 0 := by
    intro i hi
    exact
      (mem_minimumScaledBuffers_iff_state_eq_zero_of_L_eq_one
        alpha halpha (s.X t) hx.1 hL i).1 hi
  have hpositive : forall i, i ∉ S -> 0 < s.X t i := by
    intro i hi
    have hne : Not (s.X t i = 0) := by
      intro hxi
      exact hi
        ((mem_minimumScaledBuffers_iff_state_eq_zero_of_L_eq_one
          alpha halpha (s.X t) hx.1 hL i).2 hxi)
    exact lt_of_le_of_ne (hx.1 i) (Ne.symm hne)
  have hsumzero :
      Finset.sum S (fun i => deriv (fun r => s.X r i) t) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact state_deriv_eq_zero_of_state_eq_zero
      N s alpha t hregular i (hzero i hi)
  have hcutLe :
      N.cutDrift S (pathDerivative A t) <= 0 := by
    rw [← hsumzero]
    exact boundary_cutDrift_le_aggregate_state_deriv
      N alpha halpha hnonidle hsmw s t hregular S hzero hpositive
  have hcutGap :
      g0 / 2 <= N.cutDrift S (pathDerivative A t) :=
    hgap (pathDerivative A t) hf S hSnonempty hSproper
  linarith

/-- Unconditional proof of the paper's SMW near-nominal negative-drift
statement, including its repaired `0 < LAlphaAmbient <= 1` boundary. -/
theorem smwNegativeDriftStatement_proved
    (N : Network Buffer Server) :
    SMWNegativeDriftStatement (N := N) := by
  intro hconn hflex hcrp alpha halpha
  letI : Nontrivial Buffer := buffer_nontrivial_of_limited N hflex
  obtain ⟨g0, hg0, epsilon, hepsilon, _hg0eq, hgap⟩ :=
    N.exists_uniform_cutDrift_gap hconn hcrp
  refine ⟨g0 / 2, half_pos hg0, epsilon, hepsilon, ?_⟩
  intro T x0 A s t hregular hrate hLpos hLle
  have hnonidle := N.smwPolicy_nonIdling alpha halpha
  have hsmw := N.smwPolicy_isSMW alpha halpha
  by_cases hLlt :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1
  · have heq :
        lyapunovDrift alpha s.X t =
          steepestDescentLowerBound (N := N) alpha A s.X t :=
      smw_lyapunovDrift_eq_steepestDescentLowerBound
        N alpha halpha hnonidle hsmw s t hregular hLlt
    exact lyapunovDrift_le_neg_half_gap_of_eq_steepest
      N alpha halpha g0 epsilon hg0 hgap s t hregular hLpos heq hrate.2
  · have hLeOne :
        1 <= Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) :=
      le_of_not_gt hLlt
    have hLEq :
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) = 1 :=
      le_antisymm hLle hLeOne
    exact
      (regular_smw_boundary_impossible_of_uniform_cut_gap
        N alpha halpha hnonidle hsmw g0 epsilon hg0 hgap
        s t hregular hLEq hrate.2).elim

end StateDepMOR.PaperStatements.Network
