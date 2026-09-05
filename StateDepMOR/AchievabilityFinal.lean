import StateDepMOR.AchievabilityProof
import StateDepMOR.SMWConvergenceProof

/-!
# Unconditional achievability bound

This module proves the repaired statement of Lemma `lem:lower_bound_vj`.
The unsupported assertion that `gammaAB` is literally independent of the
chosen positive horizon is intentionally not part of the theorem.  The core
paper result is the quantified rate inequality at every positive horizon.

The proof uses the attained minimum-loss invariant PMF and the actual
calendar-time Poisson execution.  Its deterministic rate comparison is
kept separate from the stochastic stationary upper bound.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

set_option maxHeartbeats 1600000

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : StateDepMOR.Network Buffer Server)

/-! ## Deterministic local rate comparison -/

/-- Translating a real absolutely continuous path segment to start at zero,
and rebasing its values by a constant, preserves absolute continuity. -/
private theorem absolutelyContinuousOnInterval_shift_sub_const
    {f : Real -> Real} {a T c : Real}
    (hT : 0 <= T)
    (hf : AbsolutelyContinuousOnInterval f a (a + T)) :
    AbsolutelyContinuousOnInterval (fun t => f (a + t) - c) 0 T := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hbound⟩ := hf epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro E hE hlength
  let E' : Nat × (Nat -> Real × Real) :=
    (E.1, fun i => (a + (E.2 i).1, a + (E.2 i).2))
  have hE' :
      E' ∈ AbsolutelyContinuousOnInterval.disjWithin a (a + T) := by
    simp only [AbsolutelyContinuousOnInterval.disjWithin,
      Set.mem_ofPred_eq] at hE ⊢
    rcases hE with ⟨hmem, hdisj⟩
    constructor
    · intro i hi
      have hi' := hmem i hi
      simp only [E', Set.uIcc_of_le hT,
        Set.uIcc_of_le (le_add_of_nonneg_right hT),
        Set.mem_Icc] at hi' ⊢
      constructor <;> constructor <;> linarith
    · intro i hi j hj hij
      have hd := hdisj hi hj hij
      change Disjoint
        (uIoc (E.2 i).1 (E.2 i).2)
        (uIoc (E.2 j).1 (E.2 j).2) at hd
      change Disjoint
        (uIoc (a + (E.2 i).1) (a + (E.2 i).2))
        (uIoc (a + (E.2 j).1) (a + (E.2 j).2))
      rw [Set.disjoint_left] at hd ⊢
      intro x hxi hxj
      have hiMem : x - a ∈ uIoc (E.2 i).1 (E.2 i).2 := by
        rw [Set.mem_uIoc] at hxi ⊢
        rcases hxi with hxi | hxi
        · exact Or.inl ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
        · exact Or.inr ⟨by linarith [hxi.1], by linarith [hxi.2]⟩
      have hjMem : x - a ∈ uIoc (E.2 j).1 (E.2 j).2 := by
        rw [Set.mem_uIoc] at hxj ⊢
        rcases hxj with hxj | hxj
        · exact Or.inl ⟨by linarith [hxj.1], by linarith [hxj.2]⟩
        · exact Or.inr ⟨by linarith [hxj.1], by linarith [hxj.2]⟩
      exact (hd hiMem) hjMem
  have hlength' :
      (Finset.range E'.1).sum
          (fun i => dist (E'.2 i).1 (E'.2 i).2) < delta := by
    simpa [E', Real.dist_eq] using hlength
  have hout := hbound E' hE' hlength'
  simpa [E', Real.dist_eq] using hout

/-- Every interior time of a horizon `H >= T` lies in the interior of an
explicit translated window of length `T`. -/
theorem exists_fixedHorizonWindow
    {T H t : Real} (hT : 0 < T) (hTH : T <= H)
    (ht : t ∈ Ioo (0 : Real) H) :
    exists a u : Real,
      0 <= a /\ a + T <= H /\ u ∈ Ioo (0 : Real) T /\ a + u = t := by
  have hH : 0 < H := hT.trans_le hTH
  let a := (H - T) * t / H
  let u := T * t / H
  have hHT : 0 <= H - T := sub_nonneg.mpr hTH
  have ha0 : 0 <= a := by
    dsimp [a]
    exact div_nonneg (mul_nonneg hHT ht.1.le) hH.le
  have htH : t / H < 1 := (div_lt_one hH).2 ht.2
  have haT : a + T <= H := by
    have ha : a <= H - T := by
      dsimp [a]
      calc
        (H - T) * t / H = (H - T) * (t / H) := by ring
        _ <= (H - T) * 1 :=
          mul_le_mul_of_nonneg_left htH.le hHT
        _ = H - T := mul_one _
    linarith
  have hu0 : 0 < u := by
    dsimp [u]
    exact div_pos (mul_pos hT ht.1) hH
  have huT : u < T := by
    dsimp [u]
    calc
      T * t / H = T * (t / H) := by ring
      _ < T * 1 := mul_lt_mul_of_pos_left htH hT
      _ = T := mul_one _
  have hau : a + u = t := by
    dsimp [a, u]
    field_simp [hH.ne']
    ring
  exact ⟨a, u, ha0, haT, ⟨hu0, huT⟩, hau⟩

/-- The fluid state at a time inside the original horizon, bundled as a
simplex for use as the initial condition of a translated segment. -/
noncomputable def fluidSegmentInitialState
    {U : N.DeterministicPolicySequence} {H : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (a : Real) (ha : a ∈ Icc (0 : Real) H) :
    Simplex Buffer where
  val := s.X a
  nonneg := (s.state_in_simplex a ha).1
  sum_eq_one := (s.state_in_simplex a ha).2

/-- Restrict a fluid solution to `[a, a + T]`, translate the interval to
`[0, T]`, and rebase its cumulative input and allocation paths at zero.
The result has exactly horizon `T`; this is the localization used below and
does not compare `gammaAB` values at different horizons. -/
noncomputable def fluidModelSolution_fixedHorizonSegment
    {U : N.DeterministicPolicySequence} {H : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (a T : Real) (hT : 0 < T) (ha0 : 0 <= a)
    (haT : a + T <= H) :
    N.FluidModelSolution U T
      (fluidSegmentInitialState N s a
        ⟨ha0, (le_add_of_nonneg_right hT.le).trans haT⟩)
      (fun t j k => A (a + t) j k - A a j k) := by
  let xstart : Simplex Buffer :=
    fluidSegmentInitialState N s a
      ⟨ha0, (le_add_of_nonneg_right hT.le).trans haT⟩
  let Ashift : MatrixPath Server Buffer :=
    fun t j k => A (a + t) j k - A a j k
  let Xshift : StateDepMOR.Network.FluidStatePath Buffer :=
    fun t i => s.X (a + t) i
  let Eshift : StateDepMOR.Network.FluidAllocationPath Buffer Server :=
    fun t i j k => s.E (a + t) i j k - s.E a i j k
  let pshift : StateDepMOR.Network.FluidActionFractions Buffer Server :=
    fun t j k b => s.p (a + t) j k b
  have hsegmentSubset :
      Icc a (a + T) <= Icc (0 : Real) H := by
    intro t ht
    exact ⟨ha0.trans ht.1, ht.2.trans haT⟩
  have hsegmentSubsetU :
      uIcc a (a + T) <= uIcc (0 : Real) H := by
    rw [uIcc_of_le (le_add_of_nonneg_right hT.le),
      uIcc_of_le s.horizon_pos.le]
    exact hsegmentSubset
  have htranslate (t : Real) (ht : t ∈ Icc (0 : Real) T) :
      a + t ∈ Icc a (a + T) := by
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hqmp :
      Measure.QuasiMeasurePreserving
        (fun t : Real => a + t)
        (volume.restrict (Icc (0 : Real) T))
        (volume.restrict (Icc a (a + T))) := by
    apply (quasiMeasurePreserving_add_left volume a).restrict
    intro t ht
    exact htranslate t ht
  refine {
    horizon_pos := hT
    input_valid := ?_
    X := Xshift
    E := Eshift
    p := pshift
    state_ac := ?_
    allocation_ac := ?_
    state_initial := ?_
    allocation_initial := ?_
    allocation_incompatible := ?_
    state_in_simplex := ?_
    fractions_measurable := ?_
    fractions_in_simplex := ?_
    fractions_incompatible := ?_
    policy_rule := ?_
    allocation_rule := ?_
    balance := ?_
  }
  · refine ⟨?_, ?_, ?_⟩
    · intro j k
      exact absolutelyContinuousOnInterval_shift_sub_const
        (f := fun t => A t j k) (a := a) (T := T) (c := A a j k)
        hT.le ((s.input_valid.1 j k).mono hsegmentSubsetU)
    · intro j k t ht u hu htu
      dsimp [Ashift]
      apply sub_le_sub_right
      exact s.input_valid.2.1 j k
        (hsegmentSubset (htranslate t ht))
        (hsegmentSubset (htranslate u hu))
        (by linarith)
    · intro j k
      change A (a + 0) j k - A a j k = 0
      rw [add_zero, sub_self]
  · intro i
    have hac := absolutelyContinuousOnInterval_shift_sub_const
      (f := fun t => s.X t i) (a := a) (T := T) (c := 0)
      hT.le ((s.state_ac i).mono hsegmentSubsetU)
    simpa only [sub_zero] using hac
  · intro i j k
    exact absolutelyContinuousOnInterval_shift_sub_const
      (f := fun t => s.E t i j k) (a := a) (T := T)
      (c := s.E a i j k) hT.le
      ((s.allocation_ac i j k).mono hsegmentSubsetU)
  · intro i
    change s.X (a + 0) i =
      (fluidSegmentInitialState N s a
        ⟨ha0, (le_add_of_nonneg_right hT.le).trans haT⟩).val i
    simp only [add_zero, fluidSegmentInitialState]
  · intro i j k
    simp [Eshift]
  · intro t ht i j k hij
    dsimp [Eshift]
    rw [s.allocation_incompatible
      (a + t) (hsegmentSubset (htranslate t ht)) i j k hij,
      s.allocation_incompatible
        a ⟨ha0, (le_add_of_nonneg_right hT.le).trans haT⟩ i j k hij]
    ring
  · intro t ht
    exact s.state_in_simplex
      (a + t) (hsegmentSubset (htranslate t ht))
  · intro j k b
    exact (s.fractions_measurable j k b).comp
      (measurable_const.add measurable_id)
  · intro t ht j k
    exact s.fractions_in_simplex
      (a + t) (hsegmentSubset (htranslate t ht)) j k
  · intro t ht j k i hi
    exact s.fractions_incompatible
      (a + t) (hsegmentSubset (htranslate t ht)) j k i hi
  · have horig :
        Filter.Eventually
          (fun t => forall j k,
            (fun b => s.p t j k b) ∈
              N.fluidPolicyCorrespondence U j k (s.X t))
          (ae (volume.restrict (Icc a (a + T)))) :=
      ae_restrict_of_ae_restrict_of_subset hsegmentSubset s.policy_rule
    simpa [Xshift, pshift] using hqmp.ae horig
  · have horig :
        Filter.Eventually
          (fun t => forall i j k, N.compatible i j ->
            deriv (fun u => s.E u i j k) t =
              deriv (fun u => A u j k) t * s.p t j k (some i))
          (ae (volume.restrict (Icc a (a + T)))) :=
      ae_restrict_of_ae_restrict_of_subset hsegmentSubset s.allocation_rule
    have hpull := hqmp.ae horig
    filter_upwards [hpull] with t ht
    intro i j k hij
    change deriv (fun u => s.E (a + u) i j k - s.E a i j k) t =
      deriv (fun u => A (a + u) j k - A a j k) t *
        s.p (a + t) j k (some i)
    rw [deriv_sub_const, deriv_sub_const]
    calc
      deriv (fun u => s.E (a + u) i j k) t =
          deriv (fun u => s.E u i j k) (a + t) :=
        deriv_comp_const_add (fun u => s.E u i j k) a t
      _ = deriv (fun u => A u j k) (a + t) *
          s.p (a + t) j k (some i) :=
        ht i j k hij
      _ = deriv (fun u => A (a + u) j k) t *
          s.p (a + t) j k (some i) := by
        rw [deriv_comp_const_add (fun u => A u j k) a t]
  · intro t ht i
    have hnow := s.balance
      (a + t) (hsegmentSubset (htranslate t ht)) i
    have hstart := s.balance
      a ⟨ha0, (le_add_of_nonneg_right hT.le).trans haT⟩ i
    dsimp [Xshift, Eshift, xstart, fluidSegmentInitialState]
    rw [hnow, hstart]
    simp_rw [Finset.sum_sub_distrib]
    ring

/-- Regularity at `a + t` transfers to the corresponding point `t` of a
translated fixed-horizon segment. -/
theorem isRegularPoint_fixedHorizonSegment
    (alpha : Simplex Buffer)
    {U : N.DeterministicPolicySequence} {H : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (a T t : Real) (hT : 0 < T) (ha0 : 0 <= a)
    (haT : a + T <= H) (ht : t ∈ Ioo (0 : Real) T)
    (hregular : IsRegularPoint N alpha s (a + t)) :
    IsRegularPoint N alpha
      (fluidModelSolution_fixedHorizonSegment N s a T hT ha0 haT) t := by
  let shift : Real -> Real := fun u => a + u
  have hshift : DifferentiableAt Real shift t :=
    differentiableAt_const a |>.add differentiableAt_id
  refine ⟨ht, ?_, ?_, ?_, ?_⟩
  · intro j k
    have hcomp :=
      (hregular.2.1 j k).comp t hshift
    exact hcomp.sub (differentiableAt_const (c := A a j k))
  · intro i
    exact (hregular.2.2.1 i).comp t hshift
  · intro i j k
    have hcomp :=
      (hregular.2.2.2.1 i j k).comp t hshift
    exact hcomp.sub (differentiableAt_const (c := s.E a i j k))
  · exact hregular.2.2.2.2.comp t hshift

/-- The input derivative of a translated and rebased segment is the
original derivative at the translated time. -/
theorem pathDerivative_fixedHorizonSegment
    {A : MatrixPath Server Buffer} (a t : Real) :
    pathDerivative (fun u j k => A (a + u) j k - A a j k) t =
      pathDerivative A (a + t) := by
  funext j k
  unfold pathDerivative
  rw [deriv_sub_const,
    deriv_comp_const_add (fun u => A u j k) a t]

/-- The Lyapunov derivative of a translated segment is the original
Lyapunov derivative at the translated time. -/
theorem lyapunovDrift_fixedHorizonSegment
    (alpha : Simplex Buffer)
    {U : N.DeterministicPolicySequence} {H : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (a T t : Real) (hT : 0 < T) (ha0 : 0 <= a)
    (haT : a + T <= H) :
    lyapunovDrift alpha
        (fluidModelSolution_fixedHorizonSegment
          N s a T hT ha0 haT).X t =
      lyapunovDrift alpha s.X (a + t) := by
  unfold lyapunovDrift
  change
    deriv
        (fun r =>
          Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X (a + r))) t =
      deriv
        (fun r =>
          Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X r)) (a + t)
  exact deriv_comp_const_add
    (fun r => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X r)) a t

/-- Every positive Lyapunov drift occurring at a regular interior state of
a fluid sample path gives one of the candidates in `gammaAB`. -/
theorem gammaAB_le_localRate_div_lyapunovDrift
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {T : Real} {x0 : Simplex Buffer}
    {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (t : Real)
    (hregular : IsRegularPoint N alpha s t)
    (hinterior :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1)
    (hpositive : 0 < lyapunovDrift alpha s.X t) :
    gammaAB (N := N) U alpha T <=
      (N.localRate (pathDerivative A t) : EReal) /
        (lyapunovDrift alpha s.X t : EReal) := by
  unfold gammaAB
  apply sInf_le
  refine
    ⟨pathDerivative A t, lyapunovDrift alpha s.X t, ?_, rfl⟩
  exact
    ⟨hpositive, x0, A, s, t, hregular, rfl, hinterior, rfl⟩

/-- Fixed-horizon localization stated entirely in the coordinates of the
original longer fluid path. The variational value remains `gammaAB ... T`;
no cross-horizon equality is used. -/
theorem gammaAB_le_localRate_div_lyapunovDrift_fixedHorizonSegment
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {H : Real} {x0 : Simplex Buffer}
    {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (a T t : Real) (hT : 0 < T) (ha0 : 0 <= a)
    (haT : a + T <= H) (ht : t ∈ Ioo (0 : Real) T)
    (hregular : IsRegularPoint N alpha s (a + t))
    (hinterior :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X (a + t)) < 1)
    (hpositive : 0 < lyapunovDrift alpha s.X (a + t)) :
    gammaAB (N := N) U alpha T <=
      (N.localRate (pathDerivative A (a + t)) : EReal) /
        (lyapunovDrift alpha s.X (a + t) : EReal) := by
  let seg :=
    fluidModelSolution_fixedHorizonSegment N s a T hT ha0 haT
  have hregSeg : IsRegularPoint N alpha seg t :=
    isRegularPoint_fixedHorizonSegment
      N alpha s a T t hT ha0 haT ht hregular
  have hstate :
      seg.X t = s.X (a + t) := by
    rfl
  have hinput :
      pathDerivative
          (fun u j k => A (a + u) j k - A a j k) t =
        pathDerivative A (a + t) :=
    pathDerivative_fixedHorizonSegment (A := A) a t
  have hdrift :
      lyapunovDrift alpha seg.X t =
        lyapunovDrift alpha s.X (a + t) :=
    lyapunovDrift_fixedHorizonSegment
      N alpha s a T t hT ha0 haT
  simpa only [hinput, hdrift] using
    gammaAB_le_localRate_div_lyapunovDrift
      N alpha U seg t hregSeg (hstate ▸ hinterior) (hdrift ▸ hpositive)

/-- Direct fixed-target-horizon localization at any regular interior time
of a longer fluid path. -/
theorem gammaAB_le_localRate_div_lyapunovDrift_atTime_fixedHorizon
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {T H : Real} {x0 : Simplex Buffer}
    {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (t : Real) (hT : 0 < T) (hTH : T <= H)
    (hregular : IsRegularPoint N alpha s t)
    (hinterior :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1)
    (hpositive : 0 < lyapunovDrift alpha s.X t) :
    gammaAB (N := N) U alpha T <=
      (N.localRate (pathDerivative A t) : EReal) /
        (lyapunovDrift alpha s.X t : EReal) := by
  obtain ⟨a, u, ha0, haT, hu, hau⟩ :=
    exists_fixedHorizonWindow hT hTH hregular.1
  have hreg' : IsRegularPoint N alpha s (a + u) := by
    simpa only [hau] using hregular
  have hint' :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X (a + u)) < 1 := by
    simpa only [hau] using hinterior
  have hpos' : 0 < lyapunovDrift alpha s.X (a + u) := by
    simpa only [hau] using hpositive
  have h :=
    gammaAB_le_localRate_div_lyapunovDrift_fixedHorizonSegment
      N alpha U s a T u hT ha0 haT hu hreg' hint' hpos'
  simpa only [hau] using h

/-- The local achievability variational value is nonnegative.  This uses
only nonnegativity of the Poisson action and positivity of every admitted
Lyapunov drift. -/
theorem gammaAB_nonnegative
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (T : Real) :
    0 <= gammaAB (N := N) U alpha T := by
  unfold gammaAB
  apply le_sInf
  intro q hq
  obtain ⟨f, v, hdatum, rfl⟩ := hq
  apply EReal.div_nonneg
  · exact_mod_cast N.localRate_nonneg f
  · exact_mod_cast hdatum.1.le

theorem mul_lyapunovDrift_le_localRate_toReal_of_lt_gammaAB
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {T : Real} {x0 : Simplex Buffer}
    {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (c t : Real)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (hregular : IsRegularPoint N alpha s t)
    (hinterior :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1)
    (hpositive : 0 < lyapunovDrift alpha s.X t)
    (hfinite :
      Ne (N.localRate (pathDerivative A t)) (Top.top : ENNReal)) :
    c * lyapunovDrift alpha s.X t <=
      (N.localRate (pathDerivative A t)).toReal := by
  have hratio :
      (c : EReal) <=
        (N.localRate (pathDerivative A t) : EReal) /
          (lyapunovDrift alpha s.X t : EReal) :=
    hc.le.trans
      (gammaAB_le_localRate_div_lyapunovDrift
        N alpha U s t hregular hinterior hpositive)
  have hmul :
      (c : EReal) * (lyapunovDrift alpha s.X t : EReal) <=
        (N.localRate (pathDerivative A t) : EReal) :=
    (EReal.le_div_iff_mul_le
      (EReal.coe_pos.mpr hpositive) (EReal.coe_ne_top _)).mp hratio
  rw [<- EReal.coe_mul, <-
    EReal.coe_ennreal_toReal hfinite] at hmul
  exact EReal.coe_le_coe_iff.mp hmul

/-- Real-valued local cost inequality on a longer path, localized to the
fixed target horizon `T`. -/
theorem mul_lyapunovDrift_le_localRate_toReal_atTime_fixedHorizon
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {T H : Real} {x0 : Simplex Buffer}
    {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (c t : Real) (hT : 0 < T) (hTH : T <= H)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (hregular : IsRegularPoint N alpha s t)
    (hinterior :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1)
    (hpositive : 0 < lyapunovDrift alpha s.X t)
    (hfinite :
      Ne (N.localRate (pathDerivative A t)) (Top.top : ENNReal)) :
    c * lyapunovDrift alpha s.X t <=
      (N.localRate (pathDerivative A t)).toReal := by
  have hratio :
      (c : EReal) <=
        (N.localRate (pathDerivative A t) : EReal) /
          (lyapunovDrift alpha s.X t : EReal) :=
    hc.le.trans
      (gammaAB_le_localRate_div_lyapunovDrift_atTime_fixedHorizon
        N alpha U s t hT hTH hregular hinterior hpositive)
  have hmul :
      (c : EReal) * (lyapunovDrift alpha s.X t : EReal) <=
        (N.localRate (pathDerivative A t) : EReal) :=
    (EReal.le_div_iff_mul_le
      (EReal.coe_pos.mpr hpositive) (EReal.coe_ne_top _)).mp hratio
  rw [<- EReal.coe_mul, <-
    EReal.coe_ennreal_toReal hfinite] at hmul
  exact EReal.coe_le_coe_iff.mp hmul

/-- A same-horizon fluid excursion from Lyapunov level at most `rho` to the
queue boundary has action at least `c * (1 - rho)` whenever `c` is a
positive strict lower approximant of `gammaAB`. -/
theorem poissonPathRate_ge_excursion_cost_same_horizon
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {H : Real} {x0 : Simplex Buffer}
    {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (rho c tau : Real)
    (hrho : rho < 1)
    (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha H)
    (htau : tau ∈ Icc (0 : Real) H)
    (hstart :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho)
    (hhit :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X tau) = 1)
    (hbefore :
      forall t, t ∈ Ico (0 : Real) tau ->
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1) :
    ENNReal.ofReal (c * (1 - rho)) <= poissonPathRate N H A := by
  let g : Real -> Real :=
    fun t => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t)
  have hgacH : AbsolutelyContinuousOnInterval g 0 H := by
    exact Lyapunov.LAlphaAmbient_comp_absolutelyContinuous
      (fun i => alpha i) s.X s.state_ac
  have hsub : Icc (0 : Real) tau <= Icc (0 : Real) H :=
    Icc_subset_Icc le_rfl htau.2
  have hgacTau : AbsolutelyContinuousOnInterval g 0 tau := by
    apply hgacH.mono
    simpa only [uIcc_of_le htau.1, uIcc_of_le s.horizon_pos.le] using hsub
  by_cases hrateTop : poissonPathRate N H A = (Top.top : ENNReal)
  · rw [hrateTop]
    exact le_top
  have hrateFinite :
      Ne (poissonPathRate N H A) (Top.top : ENNReal) := hrateTop
  let cost : Real -> Real :=
    fun t => (N.localRate (pathDerivative A t)).toReal
  have hcostIntH : IntegrableOn cost (Icc (0 : Real) H) volume := by
    exact finiteAction_localRate_toReal_integrableOn N H A hrateFinite
  have hcostIntTau : IntegrableOn cost (Icc (0 : Real) tau) volume :=
    hcostIntH.mono_set hsub
  have hregularH :
      Filter.Eventually
        (fun t => IsRegularPoint N alpha s t)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
    FluidModelSolution.isRegularPoint_ae alpha s
  have hregularTau :
      Filter.Eventually
        (fun t => IsRegularPoint N alpha s t)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) tau))) :=
    ae_restrict_of_ae_restrict_of_subset hsub hregularH
  have hlocalFiniteH :
      Filter.Eventually
        (fun t =>
          N.localRate (pathDerivative A t) < (Top.top : ENNReal))
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
    finiteAction_localRate_lt_top_ae N H A hrateFinite
  have hlocalFiniteTau :
      Filter.Eventually
        (fun t =>
          N.localRate (pathDerivative A t) < (Top.top : ENNReal))
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) tau))) :=
    ae_restrict_of_ae_restrict_of_subset hsub hlocalFiniteH
  have hneTau :
      Filter.Eventually
        (fun t => Ne t tau)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) tau))) :=
    MeasureTheory.ae_restrict_of_ae (volume.ae_ne tau)
  have hpoint :
      Filter.Eventually
        (fun t => c * deriv g t <= cost t)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) tau))) := by
    filter_upwards
      [ae_restrict_mem measurableSet_Icc, hregularTau,
        hlocalFiniteTau, hneTau] with t ht hregular hlocal htne
    by_cases hpositive : 0 < deriv g t
    · have htlt : t < tau := lt_of_le_of_ne ht.2 htne
      have hinterior : g t < 1 :=
        hbefore t ⟨ht.1, htlt⟩
      exact
        mul_lyapunovDrift_le_localRate_toReal_of_lt_gammaAB
          N alpha U s c t hc hregular hinterior hpositive hlocal.ne
    · have hderiv : deriv g t <= 0 := le_of_not_gt hpositive
      exact (mul_nonpos_of_nonneg_of_nonpos hcpos.le hderiv).trans
        ENNReal.toReal_nonneg
  have hgDerivInt :
      IntegrableOn (fun t => deriv g t) (Icc (0 : Real) tau) volume := by
    have hint := hgacTau.intervalIntegrable_deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le htau.1] at hint
    exact hint
  have hint :
      (integral (volume.restrict (Icc (0 : Real) tau))
          (fun t => c * deriv g t)) <=
        integral (volume.restrict (Icc (0 : Real) tau)) cost := by
    exact integral_mono_ae
      (hgDerivInt.const_mul c) hcostIntTau hpoint
  have hderivIntegral :
      integral (volume.restrict (Icc (0 : Real) tau))
          (fun t => deriv g t) =
        g tau - g 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      <- intervalIntegral.integral_of_le htau.1,
      hgacTau.integral_deriv_eq_sub]
  rw [integral_const_mul, hderivIntegral] at hint
  have hincrease : 1 - rho <= g tau - g 0 := by
    dsimp [g] at *
    linarith
  have htargetTau :
      c * (1 - rho) <=
        integral (volume.restrict (Icc (0 : Real) tau)) cost :=
    (mul_le_mul_of_nonneg_left hincrease hcpos.le).trans hint
  have hcostNonneg :
      Filter.Eventually
        (fun t => 0 <= cost t)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hcostMono :
      integral (volume.restrict (Icc (0 : Real) tau)) cost <=
        integral (volume.restrict (Icc (0 : Real) H)) cost :=
    setIntegral_mono_set hcostIntH hcostNonneg
      (Filter.Eventually.of_forall fun _ ht => hsub ht)
  have hvalid :
      IsAbsolutelyContinuousMatrixPath H A /\
        forall j k, A 0 j k = 0 :=
    poissonPathRate_ne_top_implies_valid N H A hrateFinite
  have hglobal :
      integral (volume.restrict (Icc (0 : Real) H)) cost =
        (poissonPathRate N H A).toReal := by
    have hlt :
        Filter.Eventually
          (fun t =>
            N.localRate (pathDerivative A t) < (Top.top : ENNReal))
          (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
      finiteAction_localRate_lt_top_ae N H A hrateFinite
    rw [integral_toReal
      (measurable_localRate_general N A).aemeasurable hlt]
    rw [poissonPathRate, if_pos hvalid]
  have hreal :
      c * (1 - rho) <= (poissonPathRate N H A).toReal :=
    htargetTau.trans (hcostMono.trans_eq hglobal)
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hrateFinite).mp
  rw [ENNReal.toReal_ofReal]
  · exact hreal
  · exact mul_nonneg hcpos.le (sub_nonneg.mpr hrho.le)

/-- A fluid excursion on any longer horizon `H >= T` pays the excursion
cost governed by the fixed target value `gammaAB ... T`. -/
theorem poissonPathRate_ge_excursion_cost_fixed_target_horizon
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {T H : Real} {x0 : Simplex Buffer}
    {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (rho c tau : Real)
    (hT : 0 < T) (hTH : T <= H)
    (hrho : rho < 1)
    (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (htau : tau ∈ Icc (0 : Real) H)
    (hstart :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho)
    (hhit :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X tau) = 1)
    (hbefore :
      forall t, t ∈ Ico (0 : Real) tau ->
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1) :
    ENNReal.ofReal (c * (1 - rho)) <= poissonPathRate N H A := by
  let g : Real -> Real :=
    fun t => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t)
  have hgacH : AbsolutelyContinuousOnInterval g 0 H := by
    exact Lyapunov.LAlphaAmbient_comp_absolutelyContinuous
      (fun i => alpha i) s.X s.state_ac
  have hsub : Icc (0 : Real) tau <= Icc (0 : Real) H :=
    Icc_subset_Icc le_rfl htau.2
  have hgacTau : AbsolutelyContinuousOnInterval g 0 tau := by
    apply hgacH.mono
    simpa only [uIcc_of_le htau.1, uIcc_of_le s.horizon_pos.le] using hsub
  by_cases hrateTop : poissonPathRate N H A = (Top.top : ENNReal)
  · rw [hrateTop]
    exact le_top
  have hrateFinite :
      Ne (poissonPathRate N H A) (Top.top : ENNReal) := hrateTop
  let cost : Real -> Real :=
    fun t => (N.localRate (pathDerivative A t)).toReal
  have hcostIntH : IntegrableOn cost (Icc (0 : Real) H) volume := by
    exact finiteAction_localRate_toReal_integrableOn N H A hrateFinite
  have hcostIntTau : IntegrableOn cost (Icc (0 : Real) tau) volume :=
    hcostIntH.mono_set hsub
  have hregularH :
      Filter.Eventually
        (fun t => IsRegularPoint N alpha s t)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
    FluidModelSolution.isRegularPoint_ae alpha s
  have hregularTau :
      Filter.Eventually
        (fun t => IsRegularPoint N alpha s t)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) tau))) :=
    ae_restrict_of_ae_restrict_of_subset hsub hregularH
  have hlocalFiniteH :
      Filter.Eventually
        (fun t =>
          N.localRate (pathDerivative A t) < (Top.top : ENNReal))
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
    finiteAction_localRate_lt_top_ae N H A hrateFinite
  have hlocalFiniteTau :
      Filter.Eventually
        (fun t =>
          N.localRate (pathDerivative A t) < (Top.top : ENNReal))
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) tau))) :=
    ae_restrict_of_ae_restrict_of_subset hsub hlocalFiniteH
  have hneTau :
      Filter.Eventually
        (fun t => Ne t tau)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) tau))) :=
    MeasureTheory.ae_restrict_of_ae (volume.ae_ne tau)
  have hpoint :
      Filter.Eventually
        (fun t => c * deriv g t <= cost t)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) tau))) := by
    filter_upwards
      [ae_restrict_mem measurableSet_Icc, hregularTau,
        hlocalFiniteTau, hneTau] with t ht hregular hlocal htne
    by_cases hpositive : 0 < deriv g t
    · have htlt : t < tau := lt_of_le_of_ne ht.2 htne
      have hinterior : g t < 1 :=
        hbefore t ⟨ht.1, htlt⟩
      exact
        mul_lyapunovDrift_le_localRate_toReal_atTime_fixedHorizon
          N alpha U s c t hT hTH hc hregular hinterior hpositive hlocal.ne
    · have hderiv : deriv g t <= 0 := le_of_not_gt hpositive
      exact (mul_nonpos_of_nonneg_of_nonpos hcpos.le hderiv).trans
        ENNReal.toReal_nonneg
  have hgDerivInt :
      IntegrableOn (fun t => deriv g t) (Icc (0 : Real) tau) volume := by
    have hint := hgacTau.intervalIntegrable_deriv
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le htau.1] at hint
    exact hint
  have hint :
      (integral (volume.restrict (Icc (0 : Real) tau))
          (fun t => c * deriv g t)) <=
        integral (volume.restrict (Icc (0 : Real) tau)) cost := by
    exact integral_mono_ae
      (hgDerivInt.const_mul c) hcostIntTau hpoint
  have hderivIntegral :
      integral (volume.restrict (Icc (0 : Real) tau))
          (fun t => deriv g t) =
        g tau - g 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      <- intervalIntegral.integral_of_le htau.1,
      hgacTau.integral_deriv_eq_sub]
  rw [integral_const_mul, hderivIntegral] at hint
  have hincrease : 1 - rho <= g tau - g 0 := by
    dsimp [g] at *
    linarith
  have htargetTau :
      c * (1 - rho) <=
        integral (volume.restrict (Icc (0 : Real) tau)) cost :=
    (mul_le_mul_of_nonneg_left hincrease hcpos.le).trans hint
  have hcostNonneg :
      Filter.Eventually
        (fun t => 0 <= cost t)
        (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
    Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hcostMono :
      integral (volume.restrict (Icc (0 : Real) tau)) cost <=
        integral (volume.restrict (Icc (0 : Real) H)) cost :=
    setIntegral_mono_set hcostIntH hcostNonneg
      (Filter.Eventually.of_forall fun _ ht => hsub ht)
  have hvalid :
      IsAbsolutelyContinuousMatrixPath H A /\
        forall j k, A 0 j k = 0 :=
    poissonPathRate_ne_top_implies_valid N H A hrateFinite
  have hglobal :
      integral (volume.restrict (Icc (0 : Real) H)) cost =
        (poissonPathRate N H A).toReal := by
    have hlt :
        Filter.Eventually
          (fun t =>
            N.localRate (pathDerivative A t) < (Top.top : ENNReal))
          (MeasureTheory.ae (volume.restrict (Icc (0 : Real) H))) :=
      finiteAction_localRate_lt_top_ae N H A hrateFinite
    rw [integral_toReal
      (measurable_localRate_general N A).aemeasurable hlt]
    rw [poissonPathRate, if_pos hvalid]
  have hreal :
      c * (1 - rho) <= (poissonPathRate N H A).toReal :=
    htargetTau.trans (hcostMono.trans_eq hglobal)
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top hrateFinite).mp
  rw [ENNReal.toReal_ofReal]
  · exact hreal
  · exact mul_nonneg hcpos.le (sub_nonneg.mpr hrho.le)

/-! ## Concrete J1 upper bound for fluid excursions -/

/-- Input paths that support a fluid execution starting below `rho` and
reaching the queue boundary for the first time within the fixed horizon. -/
def fluidExcursionInputSet
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (rho H : Real) :
    Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H) :=
  {a | exists (x0 : Simplex Buffer)
      (s : N.FluidModelSolution U H x0
        (StateDepMOR.PoissonSamplePath.asMatrix H a))
      (tau : Real),
    tau ∈ Icc (0 : Real) H /\
    Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho /\
    Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X tau) = 1 /\
    forall t, t ∈ Ico (0 : Real) tau ->
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1}

/-- Every input in the fixed-horizon fluid excursion set has at least the
one-dimensional Lyapunov excursion cost. -/
theorem fluidExcursionInputSet_action_lower_same_horizon
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {rho H c : Real}
    (hrho : rho < 1)
    (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha H)
    {a : StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H}
    (ha : a ∈ fluidExcursionInputSet N alpha U rho H) :
    ENNReal.ofReal (c * (1 - rho)) <=
      poissonPathRate N H
        (StateDepMOR.PoissonSamplePath.asMatrix H a) := by
  obtain ⟨x0, s, tau, htau, hstart, hhit, hbefore⟩ := ha
  exact poissonPathRate_ge_excursion_cost_same_horizon
    N alpha U s rho c tau hrho hcpos hc htau hstart hhit hbefore

/-- The same fluid-excursion set on a longer observation horizon has its
action controlled by a separately fixed target horizon `T`. -/
theorem fluidExcursionInputSet_action_lower_fixed_target_horizon
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {rho T H c : Real}
    (hT : 0 < T) (hTH : T <= H)
    (hrho : rho < 1)
    (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    {a : StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H}
    (ha : a ∈ fluidExcursionInputSet N alpha U rho H) :
    ENNReal.ofReal (c * (1 - rho)) <=
      poissonPathRate N H
        (StateDepMOR.PoissonSamplePath.asMatrix H a) := by
  obtain ⟨x0, s, tau, htau, hstart, hhit, hbefore⟩ := ha
  exact poissonPathRate_ge_excursion_cost_fixed_target_horizon
    N alpha U s rho c tau hT hTH hrho hcpos hc
      htau hstart hhit hbefore

/-- The genuine calendar-time J1 LDP gives the desired exponent for every
closed set already known to consist of fixed-horizon fluid excursions. -/
theorem calendarPathLaw_closed_fluidExcursion_upper_same_horizon
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {rho H c : Real}
    (hH : 0 < H)
    (hrho : rho < 1)
    (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha H)
    (F : Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H))
    (hFclosed : IsClosed F)
    (hFexcursion : F <= fluidExcursionInputSet N alpha U rho H) :
    limsup
        (scaledLogMass
          (StateDepMOR.PoissonSamplePath.calendarPathLaw N H) F)
        atTop <=
      -((c * (1 - rho) : Real) : EReal) := by
  let I :
      StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H -> ENNReal :=
    fun a => poissonPathRate N H
      (StateDepMOR.PoissonSamplePath.asMatrix H a)
  have hnonneg : 0 <= c * (1 - rho) :=
    mul_nonneg hcpos.le (sub_nonneg.mpr hrho.le)
  have hrate :
      ENNReal.ofReal (c * (1 - rho)) <= rateInf I F := by
    unfold rateInf
    apply le_sInf
    intro q hq
    obtain ⟨a, haF, rfl⟩ := hq
    exact fluidExcursionInputSet_action_lower_same_horizon
      N alpha U hrho hcpos hc (hFexcursion haF)
  have hupper :=
    StateDepMOR.PoissonSamplePath.calendarPathLaw_closed_upper_bound
      N hH F hFclosed
  refine hupper.trans (EReal.neg_le_neg_iff.mpr ?_)
  have hrateE :
      ((ENNReal.ofReal (c * (1 - rho)) : ENNReal) : EReal) <=
        (rateInf I F : EReal) :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr hrate
  simpa [EReal.coe_ennreal_ofReal, max_eq_left hnonneg] using hrateE

/-- Genuine J1 closed-set upper bound on a longer observation horizon,
with the source exponent localized to the independently fixed horizon
`T`. -/
theorem calendarPathLaw_closed_fluidExcursion_upper_fixed_target_horizon
    (alpha : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    {rho T H c : Real}
    (hT : 0 < T) (hTH : T <= H)
    (hrho : rho < 1)
    (hcpos : 0 < c)
    (hc : (c : EReal) < gammaAB (N := N) U alpha T)
    (F : Set (StateDepMOR.PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H))
    (hFclosed : IsClosed F)
    (hFexcursion : F <= fluidExcursionInputSet N alpha U rho H) :
    limsup
        (scaledLogMass
          (StateDepMOR.PoissonSamplePath.calendarPathLaw N H) F)
        atTop <=
      -((c * (1 - rho) : Real) : EReal) := by
  let I :
      StateDepMOR.PoissonSamplePath.Path
        (Buffer := Buffer) (Server := Server) H -> ENNReal :=
    fun a => poissonPathRate N H
      (StateDepMOR.PoissonSamplePath.asMatrix H a)
  have hnonneg : 0 <= c * (1 - rho) :=
    mul_nonneg hcpos.le (sub_nonneg.mpr hrho.le)
  have hrate :
      ENNReal.ofReal (c * (1 - rho)) <= rateInf I F := by
    unfold rateInf
    apply le_sInf
    intro q hq
    obtain ⟨a, haF, rfl⟩ := hq
    exact fluidExcursionInputSet_action_lower_fixed_target_horizon
      N alpha U hT hTH hrho hcpos hc (hFexcursion haF)
  have hupper :=
    StateDepMOR.PoissonSamplePath.calendarPathLaw_closed_upper_bound
      N (hT.trans_le hTH) F hFclosed
  refine hupper.trans (EReal.neg_le_neg_iff.mpr ?_)
  have hrateE :
      ((ENNReal.ofReal (c * (1 - rho)) : ENNReal) : EReal) <=
        (rateInf I F : EReal) :=
    EReal.coe_ennreal_le_coe_ennreal_iff.mpr hrate
  simpa [EReal.coe_ennreal_ofReal, max_eq_left hnonneg] using hrateE

/-! ## Repaired persistence action estimates -/

/-- A small exponential tilt used to obtain a uniform scalar Poisson-cost
gap outside the strict `epsilon`-box around the nominal rate. -/
noncomputable def persistenceTheta (epsilon : Real) : Real :=
  min 1 (epsilon / 2)

theorem persistenceTheta_pos {epsilon : Real}
    (hepsilon : 0 < epsilon) :
    0 < persistenceTheta epsilon := by
  unfold persistenceTheta
  positivity

theorem persistenceTheta_le_one {epsilon : Real} :
    persistenceTheta epsilon <= 1 :=
  min_le_left _ _

theorem persistenceTheta_le_half {epsilon : Real} :
    persistenceTheta epsilon <= epsilon / 2 :=
  min_le_right _ _

private theorem persistenceTheta_remainder
    {epsilon x : Real} (hepsilon : 0 < epsilon)
    (hx : x = persistenceTheta epsilon \/
      x = -persistenceTheta epsilon) :
    abs (Real.exp x - 1 - x) <= (persistenceTheta epsilon) ^ 2 := by
  have hxabs : abs x <= 1 := by
    rcases hx with rfl | rfl
    · simpa [abs_of_nonneg (persistenceTheta_pos hepsilon).le] using
        (persistenceTheta_le_one (epsilon := epsilon))
    · simpa [abs_of_nonneg (persistenceTheta_pos hepsilon).le] using
        (persistenceTheta_le_one (epsilon := epsilon))
  calc
    abs (Real.exp x - 1 - x) <= x ^ 2 :=
      Real.abs_exp_sub_one_sub_id_le hxabs
    _ = (persistenceTheta epsilon) ^ 2 := by
      rcases hx with rfl | rfl <;> ring

private theorem poissonCost_ge_persistenceGap
    {nominal candidate epsilon : Real}
    (hnominal0 : 0 <= nominal) (hnominal1 : nominal <= 1)
    (hcandidate : 0 <= candidate) (hepsilon : 0 < epsilon)
    (hfar : epsilon <= abs (candidate - nominal)) :
    ENNReal.ofReal
        (persistenceTheta epsilon * epsilon / 2) <=
      poissonCost nominal candidate := by
  let theta := persistenceTheta epsilon
  have htheta : 0 < theta := persistenceTheta_pos hepsilon
  have htheta_le : theta <= epsilon / 2 :=
    persistenceTheta_le_half
  rcases hnominal0.eq_or_lt with rfl | hnominal
  · have hcandidate_pos : 0 < candidate := by
      rw [sub_zero, abs_of_nonneg hcandidate] at hfar
      exact hepsilon.trans_le hfar
    rw [poissonCost_zero_of_pos hcandidate_pos]
    exact le_top
  rw [poissonCost_of_nominal_pos hnominal hcandidate]
  apply ENNReal.ofReal_le_ofReal
  change theta * epsilon / 2 <= poissonCostReal nominal candidate
  rcases le_total nominal candidate with hupper | hlower
  · have hgap : epsilon <= candidate - nominal := by
      rw [abs_of_nonneg (sub_nonneg.mpr hupper)] at hfar
      exact hfar
    have hfenchel :=
      StateDepMOR.PoissonSamplePath.positivePoissonCostReal_fenchel
        hnominal hcandidate (theta := theta)
    rw [StateDepMOR.positivePoissonCostReal_eq
      hnominal hcandidate] at hfenchel
    have hremAbs :
        abs (Real.exp theta - 1 - theta) <= theta ^ 2 := by
      exact persistenceTheta_remainder hepsilon (Or.inl rfl)
    have hrem :
        Real.exp theta - 1 - theta <= theta ^ 2 :=
      (le_abs_self _).trans hremAbs
    have hnomRem :
        nominal * (Real.exp theta - 1 - theta) <= theta ^ 2 := by
      calc
        nominal * (Real.exp theta - 1 - theta) <=
            nominal * theta ^ 2 :=
          mul_le_mul_of_nonneg_left hrem hnominal.le
        _ <= 1 * theta ^ 2 :=
          mul_le_mul_of_nonneg_right hnominal1 (sq_nonneg theta)
        _ = theta ^ 2 := one_mul _
    have hthetaSq : theta ^ 2 <= theta * epsilon / 2 := by
      nlinarith
    have hthetaGap :
        theta * epsilon <= theta * (candidate - nominal) :=
      mul_le_mul_of_nonneg_left hgap htheta.le
    calc
      theta * epsilon / 2 <=
          theta * (candidate - nominal) -
            nominal * (Real.exp theta - 1 - theta) := by
        linarith
      _ = theta * candidate -
          nominal * (Real.exp theta - 1) := by ring
      _ <= poissonCostReal nominal candidate := hfenchel
  · have hgap : epsilon <= nominal - candidate := by
      have hnonpos : candidate - nominal <= 0 := sub_nonpos.mpr hlower
      rw [abs_of_nonpos hnonpos] at hfar
      linarith
    have hfenchel :=
      StateDepMOR.PoissonSamplePath.positivePoissonCostReal_fenchel
        hnominal hcandidate (theta := -theta)
    rw [StateDepMOR.positivePoissonCostReal_eq
      hnominal hcandidate] at hfenchel
    have hremAbs :
        abs (Real.exp (-theta) - 1 - (-theta)) <= theta ^ 2 := by
      exact persistenceTheta_remainder hepsilon (Or.inr rfl)
    have hrem :
        Real.exp (-theta) - 1 + theta <= theta ^ 2 := by
      have h :=
        (le_abs_self
          (Real.exp (-theta) - 1 - (-theta))).trans hremAbs
      simpa only [sub_neg_eq_add] using h
    have hnomRem :
        nominal * (Real.exp (-theta) - 1 + theta) <= theta ^ 2 := by
      calc
        nominal * (Real.exp (-theta) - 1 + theta) <=
            nominal * theta ^ 2 :=
          mul_le_mul_of_nonneg_left hrem hnominal.le
        _ <= 1 * theta ^ 2 :=
          mul_le_mul_of_nonneg_right hnominal1 (sq_nonneg theta)
        _ = theta ^ 2 := one_mul _
    have hthetaSq : theta ^ 2 <= theta * epsilon / 2 := by
      nlinarith
    have hthetaGap :
        theta * epsilon <= theta * (nominal - candidate) :=
      mul_le_mul_of_nonneg_left hgap htheta.le
    calc
      theta * epsilon / 2 <=
          theta * (nominal - candidate) -
            nominal * (Real.exp (-theta) - 1 + theta) := by
        linarith
      _ = -theta * candidate -
          nominal * (Real.exp (-theta) - 1) := by ring
      _ <= poissonCostReal nominal candidate := hfenchel

/-- A nonnegative instantaneous input rate outside `RateNearPhi` has a
strictly positive uniform coordinate Poisson cost. -/
theorem localRate_ge_of_not_rateNearPhi
    (f : Server -> Buffer -> Real) {epsilon : Real}
    (hf : IsNonnegativeRate f) (hepsilon : 0 < epsilon)
    (hfar : Not (RateNearPhi (N := N) f epsilon)) :
    ENNReal.ofReal
        (persistenceTheta epsilon * epsilon / 2) <=
      N.localRate f := by
  classical
  have hcoord : exists j, exists k,
      epsilon <= abs (f j k - N.phi j k) := by
    by_contra hnot
    push Not at hnot
    exact hfar ⟨hf, fun j k => hnot j k⟩
  obtain ⟨j, k, hjk⟩ := hcoord
  exact
    (poissonCost_ge_persistenceGap
      (N.phi_nonneg j k)
      (StateDepMOR.PoissonSamplePath.network_phi_le_one N j k)
      (hf j k) hepsilon hjk).trans
      (poissonCost_le_localRate N f j k)

/-- Times at which an input derivative is in the strict near-nominal box. -/
def rateNearTimes
    (A : MatrixPath Server Buffer) (epsilon : Real) : Set Real :=
  {t | RateNearPhi (N := N) (pathDerivative A t) epsilon}

/-- Non-near times inside a fixed positive horizon. -/
def persistenceBadTimes
    (A : MatrixPath Server Buffer) (epsilon H : Real) : Set Real :=
  Icc (0 : Real) H \ rateNearTimes N A epsilon

theorem measurableSet_rateNearTimes
    (A : MatrixPath Server Buffer) (epsilon : Real) :
    MeasurableSet (rateNearTimes N A epsilon) := by
  classical
  have hderiv (j : Server) (k : Buffer) :
      Measurable (fun t => pathDerivative A t j k) :=
    measurable_deriv (fun t => A t j k)
  have hnonnegative :
      MeasurableSet
        {t | IsNonnegativeRate (pathDerivative A t)} := by
    rw [show
      {t | IsNonnegativeRate (pathDerivative A t)} =
        iInter fun j => iInter fun k =>
          {t | (0 : Real) <= pathDerivative A t j k} by
      ext t
      simp [IsNonnegativeRate]]
    exact MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun k =>
        measurableSet_Ici.preimage (hderiv j k)
  have hclose :
      MeasurableSet
        {t | forall j k,
          abs (pathDerivative A t j k - N.phi j k) < epsilon} := by
    rw [show
      {t | forall j k,
          abs (pathDerivative A t j k - N.phi j k) < epsilon} =
        iInter fun j => iInter fun k =>
          (fun t => abs
            (pathDerivative A t j k - N.phi j k)) ⁻¹' Iio epsilon by
      ext t
      simp]
    exact MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun k =>
        measurableSet_Iio.preimage ((hderiv j k).sub_const _).abs
  change MeasurableSet
    ({t | IsNonnegativeRate (pathDerivative A t)} ∩
      {t | forall j k,
        abs (pathDerivative A t j k - N.phi j k) < epsilon})
  exact hnonnegative.inter hclose

theorem measurableSet_persistenceBadTimes
    (A : MatrixPath Server Buffer) (epsilon H : Real) :
    MeasurableSet (persistenceBadTimes N A epsilon H) :=
  measurableSet_Icc.diff (measurableSet_rateNearTimes N A epsilon)

theorem persistenceBadTimes_subset
    (A : MatrixPath Server Buffer) (epsilon H : Real) :
    persistenceBadTimes N A epsilon H <= Icc (0 : Real) H :=
  sdiff_subset

/-- Every unit of non-near time pays the uniform scalar entropy gap. This is
the first half of the repaired term-(c) dichotomy. -/
theorem persistenceGap_mul_badTime_le_action
    {H epsilon : Real} (_hH : 0 < H) (hepsilon : 0 < epsilon)
    (A : MatrixPath Server Buffer)
    (hfinite : Ne (poissonPathRate N H A) (Top.top : ENNReal)) :
    persistenceTheta epsilon * epsilon / 2 *
        volume.real (persistenceBadTimes N A epsilon H) <=
      (poissonPathRate N H A).toReal := by
  let gap : Real := persistenceTheta epsilon * epsilon / 2
  let cost : Real -> Real :=
    fun t => (N.localRate (pathDerivative A t)).toReal
  let bad := persistenceBadTimes N A epsilon H
  have hbadMeas : MeasurableSet bad :=
    measurableSet_persistenceBadTimes N A epsilon H
  have hbadFinite : Ne (volume bad) (Top.top : ENNReal) := by
    exact ne_top_of_le_ne_top
      (measure_Icc_lt_top :
        volume (Icc (0 : Real) H) < (Top.top : ENNReal)).ne
      (measure_mono (persistenceBadTimes_subset N A epsilon H))
  have hcostInt :
      IntegrableOn cost (Icc (0 : Real) H) volume :=
    finiteAction_localRate_toReal_integrableOn N H A hfinite
  have hcostBad : IntegrableOn cost bad volume :=
    hcostInt.mono_set (persistenceBadTimes_subset N A epsilon H)
  have hall :
      Filter.Eventually
        (fun t => forall j k, 0 <= pathDerivative A t j k)
        (ae (volume.restrict (Icc (0 : Real) H))) := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro k
    exact finiteAction_derivative_nonneg_ae N H A hfinite j k
  have hallBad :
      Filter.Eventually
        (fun t => forall j k, 0 <= pathDerivative A t j k)
        (ae (volume.restrict bad)) :=
    ae_restrict_of_ae_restrict_of_subset
      (persistenceBadTimes_subset N A epsilon H) hall
  have hltBad :
      Filter.Eventually
        (fun t =>
          N.localRate (pathDerivative A t) < (Top.top : ENNReal))
        (ae (volume.restrict bad)) :=
    ae_restrict_of_ae_restrict_of_subset
      (persistenceBadTimes_subset N A epsilon H)
      (finiteAction_localRate_lt_top_ae N H A hfinite)
  have hpoint :
      Filter.Eventually (fun t => gap <= cost t)
        (ae (volume.restrict bad)) := by
    filter_upwards
      [hallBad, hltBad, ae_restrict_mem hbadMeas] with t ht hlt hmem
    have hrate :=
      localRate_ge_of_not_rateNearPhi N
        (pathDerivative A t) ht hepsilon hmem.2
    dsimp [gap, cost]
    rw [<- ENNReal.toReal_ofReal (by
      exact div_nonneg
        (mul_nonneg (persistenceTheta_pos hepsilon).le hepsilon.le)
        (by norm_num) :
      0 <= persistenceTheta epsilon * epsilon / 2)]
    exact ENNReal.toReal_mono hlt.ne hrate
  have hint :
      integral (volume.restrict bad) (fun _ => gap) <=
        integral (volume.restrict bad) cost :=
    integral_mono_ae
      (integrableOn_const (C := gap) hbadFinite) hcostBad hpoint
  have hmono :
      integral (volume.restrict bad) cost <=
        integral (volume.restrict (Icc (0 : Real) H)) cost :=
    setIntegral_mono_set hcostInt
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      (Filter.Eventually.of_forall fun _ ht =>
        persistenceBadTimes_subset N A epsilon H ht)
  have hglobal :
      integral (volume.restrict (Icc (0 : Real) H)) cost =
        (poissonPathRate N H A).toReal := by
    have hvalid := poissonPathRate_ne_top_implies_valid N H A hfinite
    have hlt := finiteAction_localRate_lt_top_ae N H A hfinite
    rw [integral_toReal
      (measurable_localRate_general N A).aemeasurable hlt]
    rw [poissonPathRate, if_pos hvalid]
  calc
    gap * volume.real bad =
        integral (volume.restrict bad) (fun _ => gap) := by
      rw [setIntegral_const]
      simp [smul_eq_mul, mul_comm]
    _ <= integral (volume.restrict bad) cost := hint
    _ <= integral (volume.restrict (Icc (0 : Real) H)) cost := hmono
    _ = (poissonPathRate N H A).toReal := hglobal

/-! ## Finite stationary block reduction -/

/-- A finite queue state divided by its positive population size, regarded
as the paper's simplex type. -/
noncomputable def normalizedQueueState
    (K : PNat) (x : JobState Buffer (K : Nat)) :
    Simplex Buffer where
  val i := (x i : Real) / (K : Nat)
  nonneg i := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  sum_eq_one := by
    rw [<- Finset.sum_div]
    have htotal :
        Finset.univ.sum (fun i => (x i : Real)) = (K : Nat) := by
      exact_mod_cast x.total_jobs
    rw [htotal]
    exact div_self (by positivity)

/-- A finite queue-boundary state is exactly on Lyapunov level one after
population normalization. -/
theorem lAlpha_normalizedQueueState_eq_one_of_boundary
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (K : PNat) (x : JobState Buffer (K : Nat))
    (hx : StateDepMOR.Achievability.Network.IsQueueBoundary x) :
    Lyapunov.LAlpha alpha (normalizedQueueState K x) = 1 := by
  obtain ⟨i, hi⟩ := hx
  have hmin :
      Lyapunov.minCoordinate
          (fun q => normalizedQueueState K x q / alpha q) = 0 := by
    apply le_antisymm
    · calc
        Lyapunov.minCoordinate
            (fun q => normalizedQueueState K x q / alpha q) <=
            normalizedQueueState K x i / alpha i := by
          exact Finset.inf'_le _ (Finset.mem_univ i)
        _ = 0 := by
          simp [normalizedQueueState, hi]
    · unfold Lyapunov.minCoordinate
      apply Finset.le_inf' Finset.univ_nonempty
      intro q _hq
      exact div_nonneg
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (halpha q).le
  unfold Lyapunov.LAlpha Lyapunov.LAlphaAmbient
  rw [hmin]
  norm_num

/-- Real mass assigned by a finite PMF to a predicate. -/
noncomputable def pmfEventMass {A : Type*} [Fintype A]
    (pi : PMF A) (P : A -> Prop) : Real := by
  classical
  exact Finset.univ.sum fun x =>
    (pi x).toReal * if P x then 1 else 0

theorem pmfEventMass_nonnegative {A : Type*} [Fintype A]
    (pi : PMF A) (P : A -> Prop) :
    0 <= pmfEventMass pi P := by
  classical
  unfold pmfEventMass
  apply Finset.sum_nonneg
  intro x _hx
  by_cases hP : P x <;> simp [hP, ENNReal.toReal_nonneg]

theorem pmfEventMass_le_one {A : Type*} [Fintype A]
    (pi : PMF A) (P : A -> Prop) :
    pmfEventMass pi P <= 1 := by
  classical
  unfold pmfEventMass
  calc
    Finset.univ.sum (fun x =>
        (pi x).toReal * if P x then 1 else 0) <=
        Finset.univ.sum (fun x => (pi x).toReal) := by
      apply Finset.sum_le_sum
      intro x _hx
      by_cases hP : P x
      · simp [hP]
      · simp [hP, ENNReal.toReal_nonneg]
    _ = 1 := StateDepMOR.PMF.sum_toReal pi

theorem pmfEventMass_bind {A B : Type*} [Fintype A] [Fintype B]
    (pi : PMF A) (Q : A -> PMF B) (P : B -> Prop) :
    pmfEventMass (pi.bind Q) P =
      Finset.univ.sum fun x =>
        (pi x).toReal * pmfEventMass (Q x) P := by
  classical
  unfold pmfEventMass
  exact StateDepMOR.PMF.sum_bind_real pi Q
    (fun y => if P y then 1 else 0)

/-- The law after exactly `n` applications of a finite Markov kernel,
started from one deterministic state. -/
noncomputable def kernelIterate {A : Type*} [Fintype A]
    (Q : A -> PMF A) : Nat -> A -> PMF A
  | 0, x => PMF.pure x
  | n + 1, x => (Q x).bind (kernelIterate Q n)

/-- Probability of avoiding `Near` at the first `n` states, including the
initial state and excluding the state at epoch `n`. -/
noncomputable def kernelAvoidMass {A : Type*} [Fintype A]
    (Q : A -> PMF A) (Near : A -> Prop) [DecidablePred Near] :
    Nat -> A -> Real
  | 0, _ => 1
  | n + 1, x =>
      if Near x then 0
      else Finset.univ.sum fun y =>
        (Q x y).toReal * kernelAvoidMass Q Near n y

theorem kernelAvoidMass_nonnegative {A : Type*} [Fintype A]
    (Q : A -> PMF A) (Near : A -> Prop) [DecidablePred Near] :
    forall n x, 0 <= kernelAvoidMass Q Near n x := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [kernelAvoidMass]
  | succ n ih =>
      intro x
      simp only [kernelAvoidMass]
      split_ifs
      · exact le_rfl
      · apply Finset.sum_nonneg
        intro y _hy
        exact mul_nonneg ENNReal.toReal_nonneg (ih y)

/-- A fixed-block failure estimate accumulates across every sampled epoch.
The event in `kernelAvoidMass Q Near (n + 1)` checks the initial state and
the next `n` block endpoints, so `n` independent Markov steps contribute to
the power.  This is the persistence/renewal estimate; it does not replace
the sampled-epoch event by one terminal return-failure event. -/
theorem kernelAvoidMass_le_pow_of_complement_bound
    {A : Type*} [Fintype A]
    (Q : A -> PMF A) (Near : A -> Prop) [DecidablePred Near]
    (q : Real) (hq : 0 <= q)
    (hcomplement :
      forall x,
        pmfEventMass (Q x) (fun y => Not (Near y)) <= q) :
    forall n x,
      kernelAvoidMass Q Near (n + 1) x <= q ^ n := by
  classical
  intro n
  induction n with
  | zero =>
      intro x
      by_cases hx : Near x
      · simp [kernelAvoidMass, hx]
      · simp [kernelAvoidMass, hx, StateDepMOR.PMF.sum_toReal]
  | succ n ih =>
      intro x
      by_cases hx : Near x
      · simp [kernelAvoidMass, hx, pow_nonneg hq]
      · rw [kernelAvoidMass]
        simp only [if_neg hx]
        calc
          Finset.univ.sum (fun y =>
              (Q x y).toReal * kernelAvoidMass Q Near (n + 1) y) <=
              Finset.univ.sum (fun y =>
                (Q x y).toReal *
                  ((if Not (Near y) then 1 else 0) * q ^ n)) := by
            apply Finset.sum_le_sum
            intro y _hy
            apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
            by_cases hy : Near y
            · simp [kernelAvoidMass, hy, pow_nonneg hq]
            · simpa [hy] using ih y
          _ = pmfEventMass (Q x) (fun y => Not (Near y)) * q ^ n := by
            unfold pmfEventMass
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro y _hy
            ring
          _ <= q * q ^ n :=
            mul_le_mul_of_nonneg_right
              (hcomplement x) (pow_nonneg hq n)
          _ = q ^ (n + 1) := by
            rw [pow_succ]
            ring

theorem kernelIterate_endpoint_le_avoid_add_excursions
    {A : Type*} [Fintype A]
    (Q : A -> PMF A) (Near Target : A -> Prop) [DecidablePred Near]
    (p : Real) (hp : 0 <= p) (n : Nat)
    (hexcursion :
      forall m, 0 < m -> m <= n ->
        forall x, Near x ->
          pmfEventMass (kernelIterate Q m x) Target <= p) :
    forall x,
      pmfEventMass (kernelIterate Q n x) Target <=
        kernelAvoidMass Q Near n x + (n : Real) * p := by
  induction n with
  | zero =>
      intro x
      simpa only [kernelIterate, kernelAvoidMass, Nat.cast_zero,
        zero_mul, add_zero] using
        (pmfEventMass_le_one (PMF.pure x) Target)
  | succ n ih =>
      intro x
      by_cases hx : Near x
      · have hbound :
          pmfEventMass (kernelIterate Q (n + 1) x) Target <= p :=
        hexcursion (n + 1) (by omega) le_rfl x hx
        calc
          pmfEventMass (kernelIterate Q (n + 1) x) Target <= p :=
            hbound
          _ <= kernelAvoidMass Q Near (n + 1) x +
              ((n + 1 : Nat) : Real) * p := by
            simp only [kernelAvoidMass, if_pos hx, zero_add]
            have hnreal : (1 : Real) <= ((n + 1 : Nat) : Real) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
            nlinarith
      · have ih' :
          forall y,
            pmfEventMass (kernelIterate Q n y) Target <=
              kernelAvoidMass Q Near n y + (n : Real) * p := by
          apply ih
          intro m hm hmn y hy
          exact hexcursion m hm (hmn.trans (Nat.le_succ n)) y hy
        rw [show kernelIterate Q (n + 1) x =
            (Q x).bind (kernelIterate Q n) by rfl,
          pmfEventMass_bind]
        calc
          Finset.univ.sum (fun y =>
              (Q x y).toReal *
                pmfEventMass (kernelIterate Q n y) Target) <=
              Finset.univ.sum (fun y =>
                (Q x y).toReal *
                  (kernelAvoidMass Q Near n y + (n : Real) * p)) := by
            apply Finset.sum_le_sum
            intro y _hy
            exact mul_le_mul_of_nonneg_left (ih' y) ENNReal.toReal_nonneg
          _ = kernelAvoidMass Q Near (n + 1) x + (n : Real) * p := by
            simp only [kernelAvoidMass, if_neg hx, mul_add,
              Finset.sum_add_distrib]
            rw [<- Finset.sum_mul, StateDepMOR.PMF.sum_toReal, one_mul]
          _ <= kernelAvoidMass Q Near (n + 1) x +
              ((n + 1 : Nat) : Real) * p := by
            have hcast :
                (n : Real) <= ((n + 1 : Nat) : Real) := by
              exact_mod_cast Nat.le_succ n
            have hmul :=
              mul_le_mul_of_nonneg_right hcast hp
            linarith

/-- Iterating a kernel preserves every PMF that is stationary for one
kernel step. -/
theorem bind_kernelIterate_eq_of_stationary
    {A : Type*} [Fintype A]
    (pi : PMF A) (Q : A -> PMF A)
    (hstationary : pi.bind Q = pi) :
    forall n, pi.bind (kernelIterate Q n) = pi := by
  intro n
  induction n with
  | zero =>
      exact PMF.bind_pure pi
  | succ n ih =>
      rw [show kernelIterate Q (n + 1) =
          fun x => (Q x).bind (kernelIterate Q n) by
        funext x
        rfl]
      rw [<- PMF.bind_bind, hstationary, ih]

/-- Stationarity plus the last-near-visit decomposition. The second term is
the repaired persistence event: avoidance of `Near` throughout all `n`
preceding epochs, not merely failure to be near at the terminal epoch. -/
theorem stationaryEventMass_le_excursions_add_persistence
    {A : Type*} [Fintype A]
    (pi : PMF A) (Q : A -> PMF A)
    (Near Target : A -> Prop) [DecidablePred Near]
    (p persistence : Real) (hp : 0 <= p) (n : Nat)
    (hstationary : pi.bind Q = pi)
    (hexcursion :
      forall m, 0 < m -> m <= n ->
        forall x, Near x ->
          pmfEventMass (kernelIterate Q m x) Target <= p)
    (hpersistence :
      forall x, kernelAvoidMass Q Near n x <= persistence) :
    pmfEventMass pi Target <= (n : Real) * p + persistence := by
  have hnstationary :
      pi.bind (kernelIterate Q n) = pi :=
    bind_kernelIterate_eq_of_stationary pi Q hstationary n
  calc
    pmfEventMass pi Target =
        pmfEventMass (pi.bind (kernelIterate Q n)) Target :=
      congrArg (fun law => pmfEventMass law Target) hnstationary.symm
    _ = Finset.univ.sum (fun x =>
        (pi x).toReal *
          pmfEventMass (kernelIterate Q n x) Target) :=
      pmfEventMass_bind pi (kernelIterate Q n) Target
    _ <= Finset.univ.sum (fun x =>
        (pi x).toReal *
          (kernelAvoidMass Q Near n x + (n : Real) * p)) := by
      apply Finset.sum_le_sum
      intro x _hx
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      exact kernelIterate_endpoint_le_avoid_add_excursions
        Q Near Target p hp n hexcursion x
    _ <= Finset.univ.sum (fun x =>
        (pi x).toReal * (persistence + (n : Real) * p)) := by
      apply Finset.sum_le_sum
      intro x _hx
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      simpa [add_comm] using add_le_add_right (hpersistence x) ((n : Real) * p)
    _ = (n : Real) * p + persistence := by
      rw [<- Finset.sum_mul, StateDepMOR.PMF.sum_toReal, one_mul]
      ring

/-- Stationary last-near decomposition with the renewal estimate already
inserted.  The exponent in `q ^ n` comes from failure at every one of the
`n` sampled block endpoints, while the excursion term covers every possible
last successful near visit. -/
theorem stationaryEventMass_le_excursions_add_pow_persistence
    {A : Type*} [Fintype A]
    (pi : PMF A) (Q : A -> PMF A)
    (Near Target : A -> Prop) [DecidablePred Near]
    (p q : Real) (hp : 0 <= p) (hq : 0 <= q) (n : Nat)
    (hstationary : pi.bind Q = pi)
    (hexcursion :
      forall m, 0 < m -> m <= n + 1 ->
        forall x, Near x ->
          pmfEventMass (kernelIterate Q m x) Target <= p)
    (hcomplement :
      forall x,
        pmfEventMass (Q x) (fun y => Not (Near y)) <= q) :
    pmfEventMass pi Target <=
      ((n + 1 : Nat) : Real) * p + q ^ n := by
  apply stationaryEventMass_le_excursions_add_persistence
    pi Q Near Target p (q ^ n) hp (n + 1) hstationary hexcursion
  intro x
  exact kernelAvoidMass_le_pow_of_complement_bound
    Q Near q hq hcomplement n x

/-- The transition kernel obtained by running exactly `n` event-epoch
updates from one finite queue state. -/
noncomputable def eventEpochBlockKernel
    {K : Nat} (U : N.DeterministicStationaryPolicy K) (n : Nat)
    (x : JobState Buffer K) : PMF (JobState Buffer K) :=
  N.nStepLaw U (PMF.pure x) n

/-- Evolving a mixed initial law is the same as mixing the corresponding
fixed-initial-state `n`-step laws. -/
theorem bind_eventEpochBlockKernel
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (n : Nat) :
    pi.bind (eventEpochBlockKernel N U n) =
      N.nStepLaw U pi n := by
  induction n with
  | zero =>
      change pi.bind PMF.pure = pi
      exact PMF.bind_pure pi
  | succ n ih =>
      rw [show eventEpochBlockKernel N U (n + 1) =
          fun x => (eventEpochBlockKernel N U n x).bind
            (N.transitionPMF U) by
        funext x
        rfl]
      rw [<- PMF.bind_bind, ih]
      rfl

/-- An independent random event count followed by the matching number of
event-epoch transitions. -/
noncomputable def randomizedEventEpochKernel
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (countLaw : PMF Nat) (x : JobState Buffer K) :
    PMF (JobState Buffer K) :=
  countLaw.bind fun n => eventEpochBlockKernel N U n x

/-- Every invariant event-epoch PMF is stationary under an arbitrary
independent random event count. -/
theorem bind_randomizedEventEpochKernel_eq_of_isInvariant
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (countLaw : PMF Nat)
    (hinvariant : N.IsInvariantPMF U pi) :
    pi.bind (randomizedEventEpochKernel N U countLaw) = pi := by
  unfold randomizedEventEpochKernel
  rw [PMF.bind_comm pi countLaw
    (fun x n => eventEpochBlockKernel N U n x)]
  simp_rw [bind_eventEpochBlockKernel N U pi,
    N.nStepLaw_eq_of_isInvariant U pi hinvariant]
  simp

/-- The boundary-mass definition is the event mass of the queue-boundary
predicate. -/
theorem boundaryMass_eq_pmfEventMass
    {K : Nat} (pi : PMF (JobState Buffer K)) :
    StateDepMOR.Achievability.Network.boundaryMass pi =
      pmfEventMass pi
        StateDepMOR.Achievability.Network.IsQueueBoundary := by
  classical
  unfold StateDepMOR.Achievability.Network.boundaryMass pmfEventMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hboundary :
      StateDepMOR.Achievability.Network.IsQueueBoundary x
  <;> simp [hboundary]

/-- The attained minimum-invariant loss is bounded by the sum of all
last-near excursion contributions and the probability of avoiding `Near` at
every preceding sampling epoch. The second term is path persistence, not a
terminal return-failure event. -/
theorem minimumInvariantLoss_le_excursions_add_persistence
    (U : N.DeterministicPolicySequence)
    (hnonidle : N.IsNonIdlingSequence U)
    (K : PNat) (countLaw : PMF Nat)
    (Near : JobState Buffer (K : Nat) -> Prop) [DecidablePred Near]
    (p persistence : Real) (hp : 0 <= p) (n : Nat)
    (hexcursion :
      forall m, 0 < m -> m <= n ->
        forall x, Near x ->
          pmfEventMass
              (kernelIterate
                (randomizedEventEpochKernel N (U K) countLaw) m x)
              StateDepMOR.Achievability.Network.IsQueueBoundary <= p)
    (hpersistence :
      forall x,
        kernelAvoidMass
            (randomizedEventEpochKernel N (U K) countLaw) Near n x <=
          persistence) :
    N.minimumInvariantLossFamily U K <=
      (n : Real) * p + persistence := by
  let pi := N.minimumInvariantPMF (U K)
  have hstationary :
      pi.bind (randomizedEventEpochKernel N (U K) countLaw) = pi :=
    bind_randomizedEventEpochKernel_eq_of_isInvariant
      N (U K) pi countLaw (N.minimumInvariantPMF_isInvariant (U K))
  calc
    N.minimumInvariantLossFamily U K <=
        StateDepMOR.Achievability.Network.boundaryMass pi :=
      StateDepMOR.Achievability.Network.minimumInvariantLoss_le_boundaryMass
        N U hnonidle K
    _ = pmfEventMass pi
        StateDepMOR.Achievability.Network.IsQueueBoundary :=
      boundaryMass_eq_pmfEventMass pi
    _ <= (n : Real) * p + persistence :=
      stationaryEventMass_le_excursions_add_persistence
        pi (randomizedEventEpochKernel N (U K) countLaw) Near
        StateDepMOR.Achievability.Network.IsQueueBoundary p persistence hp n
        hstationary hexcursion hpersistence

/-- Minimum-invariant loss with the sampled-epoch renewal estimate already
inserted. A one-block complement bound `q` is paid at each of `n`
consecutive avoided near-set endpoints. -/
theorem minimumInvariantLoss_le_excursions_add_pow_persistence
    (U : N.DeterministicPolicySequence)
    (hnonidle : N.IsNonIdlingSequence U)
    (K : PNat) (countLaw : PMF Nat)
    (Near : JobState Buffer (K : Nat) -> Prop) [DecidablePred Near]
    (p q : Real) (hp : 0 <= p) (hq : 0 <= q) (n : Nat)
    (hexcursion :
      forall m, 0 < m -> m <= n + 1 ->
        forall x, Near x ->
          pmfEventMass
              (kernelIterate
                (randomizedEventEpochKernel N (U K) countLaw) m x)
              StateDepMOR.Achievability.Network.IsQueueBoundary <= p)
    (hcomplement :
      forall x,
        pmfEventMass
            (randomizedEventEpochKernel N (U K) countLaw x)
            (fun y => Not (Near y)) <= q) :
    N.minimumInvariantLossFamily U K <=
      ((n + 1 : Nat) : Real) * p + q ^ n := by
  apply minimumInvariantLoss_le_excursions_add_persistence
    N U hnonidle K countLaw Near p (q ^ n) hp (n + 1) hexcursion
  intro x
  exact kernelAvoidMass_le_pow_of_complement_bound
    (randomizedEventEpochKernel N (U K) countLaw) Near q hq
      hcomplement n x

/-! ## Logarithmic-rate assembly -/

/-- The scaled logarithm used by the repaired `PNat` loss exponent. -/
noncomputable def scaledLogLossPNat
    (loss : PNat -> Real) (K : PNat) : EReal :=
  ENNReal.log (ENNReal.ofReal (loss K)) /
    ((((K : Nat) : Real)) : EReal)

theorem scaledLogLossPNat_nonpositive
    (loss : PNat -> Real) (hloss_le_one : forall K, loss K <= 1)
    (K : PNat) :
    scaledLogLossPNat loss K <= 0 := by
  unfold scaledLogLossPNat
  have hofreal :
      ENNReal.ofReal (loss K) <= 1 := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (hloss_le_one K)
  have hlog : ENNReal.log (ENNReal.ofReal (loss K)) <= 0 := by
    simpa using ENNReal.log_le_log hofreal
  exact EReal.div_nonpos_of_nonpos_of_nonneg hlog (by positivity)

/-- Multiplication by a fixed positive real constant does not increase the
scaled-log limsup. -/
theorem limsup_scaledLogLossPNat_le_of_le_const_mul
    (loss mass : PNat -> Real) (C : Real)
    (hC : 0 < C)
    (hmass_le_one : forall K, mass K <= 1)
    (hbound : forall K, loss K <= C * mass K) :
    limsup (scaledLogLossPNat loss) atTop <=
      limsup (scaledLogLossPNat mass) atTop := by
  let w : PNat -> EReal := fun K =>
    ENNReal.log (ENNReal.ofReal C) /
      ((((K : Nat) : Real)) : EReal)
  have hw_tendsto : Tendsto w atTop (nhds 0) := by
    have hreal :
        Tendsto
          (fun K : PNat =>
            Real.log C / (((K : Nat) : Real)))
          atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_natCast_atTop_atTop.comp
          tendsto_PNat_val_atTop_atTop)
    apply (continuous_coe_real_ereal.tendsto 0).comp hreal |>.congr'
    filter_upwards [] with K
    dsimp [w]
    rw [ENNReal.log_ofReal_of_pos hC]
    exact EReal.coe_div (Real.log C) (((K : Nat) : Real))
  have hpoint :
      forall K,
        scaledLogLossPNat loss K <=
          w K + scaledLogLossPNat mass K := by
    intro K
    have hofreal :
        ENNReal.ofReal (loss K) <=
          ENNReal.ofReal C * ENNReal.ofReal (mass K) := by
      rw [<- ENNReal.ofReal_mul hC.le]
      exact ENNReal.ofReal_le_ofReal (hbound K)
    have hlog := ENNReal.log_le_log hofreal
    rw [ENNReal.log_mul_add] at hlog
    unfold scaledLogLossPNat
    dsimp [w]
    have hden :
        (0 : EReal) <= ((((K : Nat) : Real)) : EReal) := by
      exact_mod_cast (show (0 : Real) <= (K : Nat) by positivity)
    have hdiv :=
      EReal.div_le_div_right_of_nonneg hden hlog
    rw [EReal.add_div_of_nonneg_right hden] at hdiv
    exact hdiv
  have hmass_limsup :
      limsup (scaledLogLossPNat mass) atTop <= 0 := by
    calc
      limsup (scaledLogLossPNat mass) atTop <=
          limsup (fun _ : PNat => (0 : EReal)) atTop :=
        limsup_le_limsup
          (Eventually.of_forall
            (scaledLogLossPNat_nonpositive mass hmass_le_one))
      _ = 0 := limsup_const 0
  calc
    limsup (scaledLogLossPNat loss) atTop <=
        limsup (fun K => w K + scaledLogLossPNat mass K) atTop :=
      limsup_le_limsup (Eventually.of_forall hpoint)
    _ <= limsup w atTop +
        limsup (scaledLogLossPNat mass) atTop := by
      apply EReal.limsup_add_le
      · left
        rw [hw_tendsto.limsup_eq]
        exact EReal.zero_ne_bot
      · left
        rw [hw_tendsto.limsup_eq]
        exact EReal.zero_ne_top
    _ = limsup (scaledLogLossPNat mass) atTop := by
      rw [hw_tendsto.limsup_eq, zero_add]

/-- A scaled-log upper estimate is exactly the repaired negative-`limsup`
rate inequality after reversing signs. -/
theorem le_negativeLimsupLogRate_of_limsup_scaledLogLossPNat_le
    (loss : PNat -> Real) (c : Real)
    (h :
      limsup (scaledLogLossPNat loss) atTop <= -(c : EReal)) :
    (c : EReal) <= negativeLimsupLogRate loss := by
  have hneg := EReal.neg_le_neg_iff.mpr h
  change (c : EReal) <= -limsup (scaledLogLossPNat loss) atTop
  simpa only [neg_neg] using hneg

/-- A loss bounded above by one always has a nonnegative negative-log
limsup rate, including when it vanishes at some sizes. -/
theorem negativeLimsupLogRate_nonnegative_of_le_one
    (loss : PNat -> Real) (hloss_le_one : forall K, loss K <= 1) :
    0 <= negativeLimsupLogRate loss := by
  have hlim :
      limsup (scaledLogLossPNat loss) atTop <= 0 := by
    calc
      limsup (scaledLogLossPNat loss) atTop <=
          limsup (fun _ : PNat => (0 : EReal)) atTop :=
        limsup_le_limsup
          (Eventually.of_forall
            (scaledLogLossPNat_nonpositive loss hloss_le_one))
      _ = 0 := limsup_const 0
  change 0 <= -limsup (scaledLogLossPNat loss) atTop
  exact EReal.neg_nonneg.mpr hlim

/-- Real lower approximants determine an arbitrary extended-real lower
bound. -/
theorem ereal_le_of_forall_real_lt
    {x y : EReal}
    (h : forall c : Real, (c : EReal) < x -> (c : EReal) <= y) :
    x <= y :=
  EReal.ge_of_forall_gt_iff_ge.mp h

/-- The repaired paper-facing target, separated from any claim that the
local variational definition is horizon invariant. -/
noncomputable def AchievabilityCoreRateStatement : Prop :=
  forall (alpha : Simplex Buffer), alpha.IsInterior ->
  forall (U : N.DeterministicPolicySequence),
    N.IsNonIdlingSequence U ->
    NegativeDriftCondition (N := N) alpha U ->
    forall T, T > 0 ->
      gammaAB (N := N) U alpha T <=
        negativeLimsupLogRate (N.minimumInvariantLossFamily U)

/-- The repaired ledger statement is exactly the rate-only target proved in
this module. -/
theorem achievabilityCoreRateStatement_iff :
    AchievabilityCoreRateStatement N <->
      AchievabilityBoundStatement N :=
  Iff.rfl

end StateDepMOR.PaperStatements.Network
