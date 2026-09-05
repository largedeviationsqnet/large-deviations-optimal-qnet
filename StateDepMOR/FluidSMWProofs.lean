import StateDepMOR.FluidAllocationBounds
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# SMW fluid drift equality

This module proves the SMW-specific equality in the paper's Lyapunov
derivative lemma.  It uses a strict gap on a right neighborhood and applies
the policy correspondence only almost everywhere on that neighborhood.
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

private theorem minimumDerivativeBuffers_strict_gap_right
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (_halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (t : Real) (hregular : IsRegularPoint N alpha s t)
    (i q : Buffer)
    (hi :
      i ∈ minimumDerivativeBuffers alpha (s.X t)
        (fun a => deriv (fun r => s.X r a) t))
    (hq :
      q ∉ minimumDerivativeBuffers alpha (s.X t)
        (fun a => deriv (fun r => s.X r a) t)) :
    ∀ᶠ r in nhds t, t < r ->
      s.X r i / alpha i < s.X r q / alpha q := by
  classical
  let S1 := minimumScaledBuffers alpha (s.X t)
  have hiS1 : i ∈ S1 := (Finset.mem_filter.1 hi).1
  have hiMin :
      forall a, s.X t i / alpha i <= s.X t a / alpha a := by
    exact (Finset.mem_filter.1 hiS1).2
  by_cases hqS1 : q ∈ S1
  · have hqNotMin :
        Not (forall a, a ∈ S1 ->
          deriv (fun r => s.X r q) t / alpha q <=
            deriv (fun r => s.X r a) t / alpha a) := by
      intro h
      exact hq (Finset.mem_filter.2 ⟨hqS1, h⟩)
    push Not at hqNotMin
    obtain ⟨a, haS1, haStrict⟩ := hqNotMin
    have hiDeriv :
        deriv (fun r => s.X r i) t / alpha i <=
          deriv (fun r => s.X r a) t / alpha a :=
      (Finset.mem_filter.1 hi).2 a haS1
    have hderiv :
        deriv (fun r => s.X r i) t / alpha i <
          deriv (fun r => s.X r q) t / alpha q :=
      hiDeriv.trans_lt haStrict
    have hvalue :
        s.X t i / alpha i = s.X t q / alpha q := by
      have hqMin := (Finset.mem_filter.1 hqS1).2 i
      exact le_antisymm (hiMin q) hqMin
    let d : Real -> Real :=
      fun r => s.X r q / alpha q - s.X r i / alpha i
    have hd :
        HasDerivAt d
          (deriv (fun r => s.X r q) t / alpha q -
            deriv (fun r => s.X r i) t / alpha i) t := by
      exact ((hregular.2.2.1 q).hasDerivAt.div_const (alpha q)).sub
        ((hregular.2.2.1 i).hasDerivAt.div_const (alpha i))
    have hdpos : 0 < deriv d t := by
      rw [hd.deriv]
      linarith
    have hdzero : d t = 0 := by
      dsimp [d]
      linarith
    have hsign :=
      eventually_nhdsWithin_sign_eq_of_deriv_pos hdpos hdzero
    filter_upwards [hsign] with r hr htr
    have hrtSign : SignType.sign (r - t) = 1 :=
      sign_pos (sub_pos.mpr htr)
    have hdSign : SignType.sign (d r) = 1 := hr.trans hrtSign
    have hdPos : 0 < d r := sign_eq_one_iff.mp hdSign
    dsimp [d] at hdPos
    linarith
  · have hstrict :
        s.X t i / alpha i < s.X t q / alpha q := by
      have hle := hiMin q
      exact lt_of_le_of_ne hle (fun heq => by
        apply hqS1
        apply Finset.mem_filter.2
        refine ⟨Finset.mem_univ q, ?_⟩
        intro a
        rw [← heq]
        exact hiMin a)
    have hiCont :=
      (hregular.2.2.1 i).continuousAt.div_const (alpha i)
    have hqCont :=
      (hregular.2.2.1 q).continuousAt.div_const (alpha q)
    have hevent := hiCont.eventually_lt hqCont hstrict
    exact hevent.mono (fun r hr _ => hr)

private theorem positive_state_of_lyapunov_lt_one
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

private theorem smw_cross_cut_allocation_deriv_eq_zero
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence}
    (hsmw : N.IsSMWPolicy alpha U)
    {T : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (t : Real) (hregular : IsRegularPoint N alpha s t)
    (hL : Lyapunov.LAlphaAmbient (fun a => alpha a) (s.X t) < 1)
    (S : Finset Buffer)
    (hS :
      S = minimumDerivativeBuffers alpha (s.X t)
        (fun a => deriv (fun r => s.X r a) t))
    (i : Buffer) (hiS : i ∈ S)
    (j : Server) (hjCross : Not (N.buffersOf j <= S))
    (hij : N.compatible i j)
    (k : Buffer) :
    deriv (fun r => s.E r i j k) t = 0 := by
  classical
  obtain ⟨q, hqBuffer, hqNotS⟩ := Finset.not_subset.mp hjCross
  have hqj : N.compatible q j := (N.mem_buffersOf q j).1 hqBuffer
  have hiS' :
      i ∈ minimumDerivativeBuffers alpha (s.X t)
        (fun a => deriv (fun r => s.X r a) t) := by
    rwa [← hS]
  have hqS' :
      q ∉ minimumDerivativeBuffers alpha (s.X t)
        (fun a => deriv (fun r => s.X r a) t) := by
    rwa [← hS]
  have hgapEvent :=
    minimumDerivativeBuffers_strict_gap_right
      N alpha halpha s t hregular i q hiS' hqS'
  have hposAt :
      forall a, 0 < s.X t a :=
    positive_state_of_lyapunov_lt_one alpha halpha (s.X t) hL
  have hposEvent :
      ∀ᶠ r in nhds t, forall a, 0 < s.X r a := by
    rw [Filter.eventually_all]
    intro a
    exact continuousAt_const.eventually_lt
      (hregular.2.2.1 a).continuousAt (hposAt a)
  have hgood :
      ∀ᶠ r in nhds t,
        (t < r ->
          s.X r i / alpha i < s.X r q / alpha q) /\
        (forall a, 0 < s.X r a) /\
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
        (hrGood.2.1 q) (hrGood.1 hr.1) (fun a => s.p r j k a) hpMem
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

private theorem smw_aggregate_cut_flow_deriv_eq
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence}
    (hnonidle : N.IsNonIdlingSequence U)
    (hsmw : N.IsSMWPolicy alpha U)
    {T : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (t : Real) (hregular : IsRegularPoint N alpha s t)
    (hL : Lyapunov.LAlphaAmbient (fun a => alpha a) (s.X t) < 1) :
    let S := minimumDerivativeBuffers alpha (s.X t)
      (fun a => deriv (fun r => s.X r a) t)
    Finset.sum S (fun i => deriv (fun r => s.X r i) t) =
      Finset.sum Finset.univ (fun j =>
        Finset.sum S (fun k => deriv (fun r => A r j k) t)) -
      Finset.sum
        (Finset.univ.filter (fun j => N.buffersOf j <= S))
        (fun j => Finset.sum Finset.univ
          (fun k => deriv (fun r => A r j k) t)) := by
  classical
  dsimp
  let S := minimumDerivativeBuffers alpha (s.X t)
    (fun a => deriv (fun r => s.X r a) t)
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
              (fun l => deriv (fun r => s.E r l j i) t))) =
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
      _ = Finset.sum Finset.univ (fun j =>
          Finset.sum S (fun k => deriv (fun r => A r j k) t)) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        exact total_allocation_deriv_eq_input_of_lyapunov_lt_one
          N s hnonidle alpha halpha t hregular hL j k
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
  have hperServer :
      forall j,
        Finset.sum S (fun i =>
          Finset.sum Finset.univ
            (fun k => deriv (fun r => s.E r i j k) t)) =
        if N.buffersOf j <= S then
          Finset.sum Finset.univ (fun k => deriv (fun r => A r j k) t)
        else 0 := by
    intro j
    by_cases hj : N.buffersOf j <= S
    · rw [if_pos hj]
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
        _ = Finset.sum Finset.univ
              (fun k => deriv (fun r => A r j k) t) := by
          apply Finset.sum_congr rfl
          intro k _
          exact total_allocation_deriv_eq_input_of_lyapunov_lt_one
            N s hnonidle alpha halpha t hregular hL j k
    · rw [if_neg hj]
      apply Finset.sum_eq_zero
      intro i hiS
      apply Finset.sum_eq_zero
      intro k _
      by_cases hij : N.compatible i j
      · exact smw_cross_cut_allocation_deriv_eq_zero
          N alpha halpha hsmw s t hregular hL S rfl i hiS j hj hij k
      · exact allocation_deriv_eq_zero_of_incompatible
          N s alpha t hregular i j k hij
  have houtgoing :
      Finset.sum S (fun i =>
          Finset.sum (N.serversOf i) (fun j =>
            Finset.sum Finset.univ
              (fun k => deriv (fun r => s.E r i j k) t))) =
        Finset.sum
          (Finset.univ.filter (fun j => N.buffersOf j <= S))
          (fun j => Finset.sum Finset.univ
            (fun k => deriv (fun r => A r j k) t)) := by
    calc
      Finset.sum S (fun i =>
          Finset.sum (N.serversOf i) (fun j =>
            Finset.sum Finset.univ
              (fun k => deriv (fun r => s.E r i j k) t))) =
          Finset.sum S (fun i =>
            Finset.sum Finset.univ (fun j =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hserverExpand i
      _ = Finset.sum Finset.univ (fun j =>
            Finset.sum S (fun i =>
              Finset.sum Finset.univ
                (fun k => deriv (fun r => s.E r i j k) t))) := by
        rw [Finset.sum_comm]
      _ = Finset.sum Finset.univ (fun j =>
            if N.buffersOf j <= S then
              Finset.sum Finset.univ
                (fun k => deriv (fun r => A r j k) t)
            else 0) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hperServer j
      _ = Finset.sum
            (Finset.univ.filter (fun j => N.buffersOf j <= S))
            (fun j => Finset.sum Finset.univ
              (fun k => deriv (fun r => A r j k) t)) := by
        rw [Finset.sum_filter]
  rw [hstate, Finset.sum_sub_distrib, hincoming, houtgoing]

/-- The remaining SMW equality clause of the Lyapunov derivative lemma. -/
theorem smw_lyapunovDrift_eq_steepestDescentLowerBound
    (N : Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {U : N.DeterministicPolicySequence}
    (hnonidle : N.IsNonIdlingSequence U)
    (hsmw : N.IsSMWPolicy alpha U)
    {T : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (t : Real) (hregular : IsRegularPoint N alpha s t)
    (hL : Lyapunov.LAlphaAmbient (fun a => alpha a) (s.X t) < 1) :
    lyapunovDrift alpha s.X t =
      steepestDescentLowerBound (N := N) alpha A s.X t := by
  apply lyapunovDrift_eq_steepestDescentLowerBound_of_cutFlowEq
    N alpha halpha s t hregular
  exact smw_aggregate_cut_flow_deriv_eq
    N alpha halpha hnonidle hsmw s t hregular hL

/-- Complete proof of Lemma `lem:lyapunov_derivative` under the current
paper statement and fluid-model definitions. -/
theorem lyapunovDerivativeStatement_proved
    (N : Network Buffer Server) :
    LyapunovDerivativeStatement (N := N) := by
  intro alpha halpha U hnonidle T x0 A s t _ht hregular _hx hL
  dsimp
  refine ⟨lyapunovDerivative_first_clause
    N alpha halpha s t hregular, ?_, ?_⟩
  · exact steepestDescentLowerBound_le_lyapunovDrift
      N alpha halpha hnonidle s t hregular hL
  · intro hsmw
    exact smw_lyapunovDrift_eq_steepestDescentLowerBound
      N alpha halpha hnonidle hsmw s t hregular hL

end StateDepMOR.PaperStatements.Network
