import StateDepMOR.PaperStatements
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Uniform attraction from negative fluid drift

Analytic lemmas used by the fluid resting-state and stationary return
arguments.  They turn almost-everywhere derivative bounds for an absolutely
continuous Lyapunov path into a deterministic hitting-time bound.
-/

open MeasureTheory Set

namespace StateDepMOR

private theorem absolutelyContinuousOnInterval_min
    {f g : Real -> Real} {a b : Real}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => min (f t) (g t)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf hg ⊢
  intro epsilon hepsilon
  obtain ⟨deltaf, hdeltaf, hf⟩ :=
    hf (epsilon / 2) (half_pos hepsilon)
  obtain ⟨deltag, hdeltag, hg⟩ :=
    hg (epsilon / 2) (half_pos hepsilon)
  refine ⟨min deltaf deltag, lt_min hdeltaf hdeltag, ?_⟩
  intro E hE hlength
  have hlengthf :
      (∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2) < deltaf :=
    hlength.trans_le (min_le_left _ _)
  have hlengthg :
      (∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2) < deltag :=
    hlength.trans_le (min_le_right _ _)
  have hfE := hf E hE hlengthf
  have hgE := hg E hE hlengthg
  calc
    (∑ i ∈ Finset.range E.1,
        dist (min (f (E.2 i).1) (g (E.2 i).1))
          (min (f (E.2 i).2) (g (E.2 i).2))) <=
        ∑ i ∈ Finset.range E.1,
          (dist (f (E.2 i).1) (f (E.2 i).2) +
            dist (g (E.2 i).1) (g (E.2 i).2)) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Real.dist_eq]
      exact
        (abs_min_sub_min_le_max
          (f (E.2 i).1) (g (E.2 i).1)
          (f (E.2 i).2) (g (E.2 i).2)).trans
          (max_le
            (le_add_of_nonneg_right (abs_nonneg _))
            (le_add_of_nonneg_left (abs_nonneg _)))
    _ =
        (∑ i ∈ Finset.range E.1,
          dist (f (E.2 i).1) (f (E.2 i).2)) +
        ∑ i ∈ Finset.range E.1,
          dist (g (E.2 i).1) (g (E.2 i).2) := by
      rw [Finset.sum_add_distrib]
    _ < epsilon := by linarith

private theorem absolutelyContinuousOnInterval_finset_inf'
    {Index : Type*} [DecidableEq Index]
    (s : Finset Index) (hs : s.Nonempty)
    (f : Index -> Real -> Real)
    (hf : forall i, i ∈ s -> AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval
      (fun t => s.inf' hs (fun i => f i t)) a b := by
  induction s using Finset.cons_induction with
  | empty => simp at hs
  | @cons i s hi ih =>
      by_cases hsempty : s = ∅
      · subst s
        simpa using hf i (by simp)
      · have hsnonempty : s.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hsempty
        have hiac : AbsolutelyContinuousOnInterval (f i) a b :=
          hf i (Finset.mem_cons_self i s)
        have hsac :
            AbsolutelyContinuousOnInterval
              (fun t => s.inf' hsnonempty (fun j => f j t)) a b := by
          apply ih hsnonempty
          intro j hj
          exact hf j (Finset.mem_cons_of_mem hj)
        have hmin :=
          absolutelyContinuousOnInterval_min hiac hsac
        convert hmin using 1
        funext t
        exact Finset.inf'_cons hsnonempty (fun j => f j t)

/-- The ambient Lyapunov function of a componentwise absolutely continuous
finite-dimensional path is absolutely continuous. -/
theorem Lyapunov.LAlphaAmbient_comp_absolutelyContinuous
    {Index : Type*} [Fintype Index] [Nonempty Index]
    (alpha : Index -> Real) (X : Real -> Index -> Real)
    {a b : Real}
    (hX : forall i, AbsolutelyContinuousOnInterval (fun t => X t i) a b) :
    AbsolutelyContinuousOnInterval
      (fun t => Lyapunov.LAlphaAmbient alpha (X t)) a b := by
  classical
  have hratio :
      forall i,
        AbsolutelyContinuousOnInterval (fun t => X t i / alpha i) a b := by
    intro i
    simpa only [div_eq_mul_inv, mul_comm] using
      (hX i).const_mul (alpha i)⁻¹
  have hmin :
      AbsolutelyContinuousOnInterval
        (fun t =>
          Finset.univ.inf' Finset.univ_nonempty
            (fun i => X t i / alpha i)) a b :=
    absolutelyContinuousOnInterval_finset_inf'
      Finset.univ Finset.univ_nonempty
      (fun i t => X t i / alpha i)
      (fun i _hi => hratio i)
  rw [absolutelyContinuousOnInterval_iff] at hmin ⊢
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hbound⟩ := hmin epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro E hE hlength
  have hdist (x y : Real) : dist (1 - x) (1 - y) = dist x y := by
    simp only [Real.dist_eq, sub_sub_sub_cancel_left]
    exact abs_sub_comm y x
  simpa only [Lyapunov.LAlphaAmbient, Lyapunov.minCoordinate, hdist] using
    hbound E hE hlength

namespace PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-- Every fluid-model solution is regular at almost every time in its
interior horizon. -/
theorem FluidModelSolution.isRegularPoint_ae
    {N : StateDepMOR.Network Buffer Server}
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (alpha : Simplex Buffer) (s : N.FluidModelSolution U T x0 A) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T),
      IsRegularPoint N alpha s t := by
  have hT : 0 <= T := s.horizon_pos.le
  have hmem :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T),
        t ∈ Icc (0 : Real) T :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  have hne_zero :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T), Not (t = 0) :=
    MeasureTheory.ae_restrict_of_ae (volume.ae_ne (0 : Real))
  have hne_T :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T), Not (t = T) :=
    MeasureTheory.ae_restrict_of_ae (volume.ae_ne T)
  have hA :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T),
        forall j k, DifferentiableAt Real (fun r => A r j k) t := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    rw [MeasureTheory.ae_all_iff]
    intro k
    filter_upwards
      [MeasureTheory.ae_restrict_of_ae
        (s.input_valid.1 j k).ae_differentiableAt, hmem] with t ht hti
    exact ht (by simpa only [uIcc_of_le hT] using hti)
  have hX :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T),
        forall i, DifferentiableAt Real (fun r => s.X r i) t := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    filter_upwards
      [MeasureTheory.ae_restrict_of_ae
        (s.state_ac i).ae_differentiableAt, hmem] with t ht hti
    exact ht (by simpa only [uIcc_of_le hT] using hti)
  have hE :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T),
        forall i j k, DifferentiableAt Real (fun r => s.E r i j k) t := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    rw [MeasureTheory.ae_all_iff]
    intro j
    rw [MeasureTheory.ae_all_iff]
    intro k
    filter_upwards
      [MeasureTheory.ae_restrict_of_ae
        (s.allocation_ac i j k).ae_differentiableAt, hmem] with t ht hti
    exact ht (by simpa only [uIcc_of_le hT] using hti)
  have hLac :
      AbsolutelyContinuousOnInterval
        (fun t => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t))
        0 T :=
    Lyapunov.LAlphaAmbient_comp_absolutelyContinuous
      (fun i => alpha i) s.X s.state_ac
  have hL :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T),
        DifferentiableAt Real
          (fun r => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X r)) t := by
    filter_upwards
      [MeasureTheory.ae_restrict_of_ae hLac.ae_differentiableAt, hmem]
      with t ht hti
    exact ht (by simpa only [uIcc_of_le hT] using hti)
  filter_upwards
    [hmem, hne_zero, hne_T, hA, hX, hE, hL]
    with t ht ht0 htT hAt hXt hEt hLt
  exact
    ⟨⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
        lt_of_le_of_ne ht.2 htT⟩,
      hAt, hXt, hEt, hLt⟩

/-- A nominal fluid input has the primitive rate matrix as its derivative at
every interior time. -/
theorem FluidModelSolution.pathDerivative_eq_phi_of_isFluidLimit
    {N : StateDepMOR.Network Buffer Server}
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (hnominal : s.IsFluidLimit) {t : Real} (ht : t ∈ Ioo (0 : Real) T) :
    pathDerivative A t = N.phi := by
  funext j k
  have heq :
      (fun r => A r j k) =ᶠ[nhds t] (fun r => N.phi j k * r) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
    exact hnominal r hr j k
  rw [pathDerivative, heq.deriv_eq]
  exact (hasDerivAt_const_mul (N.phi j k)).deriv

end PaperStatements.Network

/-- An absolutely continuous function whose derivative is nonpositive almost
everywhere is antitone on its time interval. -/
theorem antitoneOn_Icc_of_ac_deriv_nonpos_ae
    {g : Real -> Real} {T : Real} (hT : 0 <= T)
    (hac : AbsolutelyContinuousOnInterval g 0 T)
    (hderiv :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T), deriv g t <= 0) :
    AntitoneOn g (Icc (0 : Real) T) := by
  intro a ha b hb hab
  have hsub : Icc a b <= Icc (0 : Real) T :=
    Icc_subset_Icc ha.1 hb.2
  have hacab : AbsolutelyContinuousOnInterval g a b := by
    apply hac.mono
    simpa only [uIcc_of_le hab, uIcc_of_le hT] using hsub
  have hderivab :
      ∀ᵐ t ∂volume.restrict (Icc a b), deriv g t <= 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub hderiv
  have hint :
      (∫ t in a..b, deriv g t) <= ∫ _t in a..b, (0 : Real) := by
    exact intervalIntegral.integral_mono_ae_restrict
      hab hacab.intervalIntegrable_deriv intervalIntegrable_const
      hderivab
  rw [hacab.integral_deriv_eq_sub] at hint
  exact sub_nonpos.mp (by simpa using hint)

/-- If a nonnegative absolutely continuous Lyapunov path starts at most at
one and has drift at most `-eta` whenever it is positive, then it is zero
after time `1 / eta`.  A separate nonpositive-drift premise records the
behavior on the zero set and makes the almost-everywhere argument explicit. -/
theorem ac_eq_zero_of_uniform_negative_drift
    {g : Real -> Real} {T eta : Real}
    (hT : 0 <= T) (heta : 0 < eta)
    (hac : AbsolutelyContinuousOnInterval g 0 T)
    (hnonneg : forall t, t ∈ Icc (0 : Real) T -> 0 <= g t)
    (hg0 : g 0 <= 1)
    (hderiv_nonpos :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T), deriv g t <= 0)
    (hderiv_strict :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T),
        0 < g t -> deriv g t <= -eta)
    {t : Real} (ht : t ∈ Icc (0 : Real) T)
    (htime : 1 / eta <= t) :
    g t = 0 := by
  have hanti : AntitoneOn g (Icc (0 : Real) T) :=
    antitoneOn_Icc_of_ac_deriv_nonpos_ae hT hac hderiv_nonpos
  apply le_antisymm
  · by_contra hnot
    have hgt : 0 < g t := lt_of_not_ge hnot
    have hsub : Icc (0 : Real) t <= Icc (0 : Real) T :=
      Icc_subset_Icc le_rfl ht.2
    have hact : AbsolutelyContinuousOnInterval g 0 t := by
      apply hac.mono
      simpa only [uIcc_of_le ht.1, uIcc_of_le hT] using hsub
    have hstrict_t :
        ∀ᵐ s ∂volume.restrict (Icc (0 : Real) t),
          0 < g s -> deriv g s <= -eta :=
      ae_restrict_of_ae_restrict_of_subset hsub hderiv_strict
    have hpositive :
        forall s, s ∈ Icc (0 : Real) t -> 0 < g s := by
      intro s hs
      exact lt_of_lt_of_le hgt (hanti (hsub hs) ht hs.2)
    have hderiv_t :
        ∀ᵐ s ∂volume.restrict (Icc (0 : Real) t), deriv g s <= -eta := by
      filter_upwards [hstrict_t, ae_restrict_mem measurableSet_Icc] with s hs hmem
      exact hs (hpositive s hmem)
    have hint :
        (∫ s in (0 : Real)..t, deriv g s) <=
          ∫ _s in (0 : Real)..t, -eta := by
      exact intervalIntegral.integral_mono_ae_restrict
        ht.1 hact.intervalIntegrable_deriv intervalIntegrable_const hderiv_t
    rw [hact.integral_deriv_eq_sub] at hint
    have hscaled : 1 <= eta * t := by
      have := (div_le_iff₀ heta).mp htime
      simpa [mul_comm] using this
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
    linarith
  · exact hnonneg t ht

namespace PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

private def fluidStateSimplex
    {N : StateDepMOR.Network Buffer Server}
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U T x0 A)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) : Simplex Buffer where
  val := s.X t
  nonneg := (s.state_in_simplex t ht).1
  sum_eq_one := (s.state_in_simplex t ht).2

private theorem FluidModelSolution.LAlphaAmbient_state_mem_Icc
    {N : StateDepMOR.Network Buffer Server}
    {U : N.DeterministicPolicySequence} {T : Real}
    {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (s : N.FluidModelSolution U T x0 A)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) ∈
      Icc (0 : Real) 1 := by
  let xt : Simplex Buffer := fluidStateSimplex s t ht
  have hnonneg : 0 <= Lyapunov.LAlpha alpha xt :=
    Lyapunov.LAlpha_nonnegative alpha xt halpha
  have hmin :
      0 <= Lyapunov.minCoordinate (fun i => xt i / alpha i) := by
    unfold Lyapunov.minCoordinate
    apply Finset.le_inf' Finset.univ_nonempty
    intro i _hi
    exact div_nonneg (xt.nonneg i) (halpha i).le
  constructor
  · simpa only [Lyapunov.LAlpha, xt, fluidStateSimplex] using hnonneg
  · have hmin' :
        0 <= Lyapunov.minCoordinate (fun i => s.X t i / alpha i) := by
      simpa only [xt, fluidStateSimplex] using hmin
    unfold Lyapunov.LAlphaAmbient
    linarith

/-- The repaired boundary-inclusive negative-drift condition gives a uniform
deterministic attraction time for every nominal fluid-model solution. -/
theorem FluidModelSolution.eq_alpha_of_nominal_negativeDrift
    {N : StateDepMOR.Network Buffer Server}
    {U : N.DeterministicPolicySequence}
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hnegative : NegativeDriftCondition (N := N) alpha U) :
    exists eta, 0 < eta /\
      forall (T : Real) (x0 : Simplex Buffer)
        (A : MatrixPath Server Buffer) (s : N.FluidModelSolution U T x0 A),
        s.IsFluidLimit ->
        forall t, t ∈ Icc (0 : Real) T ->
          1 / eta <= t -> s.X t = fun i => alpha i := by
  rcases hnegative with
    ⟨eta, heta, epsilon, hepsilon, hnegative⟩
  refine ⟨eta, heta, ?_⟩
  intro T x0 A s hnominal
  let g : Real -> Real :=
    fun t => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t)
  have hg_ac : AbsolutelyContinuousOnInterval g 0 T :=
    Lyapunov.LAlphaAmbient_comp_absolutelyContinuous
      (fun i => alpha i) s.X s.state_ac
  have hg_mem :
      forall t, t ∈ Icc (0 : Real) T -> g t ∈ Icc (0 : Real) 1 := by
    intro t ht
    exact FluidModelSolution.LAlphaAmbient_state_mem_Icc
      alpha halpha s t ht
  have hrate :
      forall t, t ∈ Ioo (0 : Real) T ->
        RateNearPhi (N := N) (pathDerivative A t) epsilon := by
    intro t ht
    have hpath :=
      FluidModelSolution.pathDerivative_eq_phi_of_isFluidLimit s hnominal ht
    constructor
    · intro j k
      rw [hpath]
      exact N.phi_nonneg j k
    · intro j k
      rw [hpath]
      simpa using hepsilon
  have hstrict :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T),
        0 < g t -> deriv g t <= -eta := by
    filter_upwards
      [FluidModelSolution.isRegularPoint_ae alpha s] with t hregular
    intro hpositive
    exact hnegative T x0 A s t hregular
      (hrate t hregular.1) hpositive
      (hg_mem t ⟨hregular.1.1.le, hregular.1.2.le⟩).2
  have hnonpos :
      ∀ᵐ t ∂volume.restrict (Icc (0 : Real) T),
        deriv g t <= 0 := by
    filter_upwards
      [FluidModelSolution.isRegularPoint_ae alpha s] with t hregular
    have htIcc : t ∈ Icc (0 : Real) T :=
      ⟨hregular.1.1.le, hregular.1.2.le⟩
    by_cases hzero : g t = 0
    · have hlocal : IsLocalMin g t := by
        filter_upwards [Icc_mem_nhds hregular.1.1 hregular.1.2] with r hr
        rw [hzero]
        exact (hg_mem r hr).1
      exact hlocal.deriv_eq_zero.le
    · have hpositive : 0 < g t :=
        lt_of_le_of_ne (hg_mem t htIcc).1 (Ne.symm hzero)
      exact (hnegative T x0 A s t hregular
        (hrate t hregular.1) hpositive (hg_mem t htIcc).2).trans
        (neg_nonpos.mpr heta.le)
  have hg0 : g 0 <= 1 :=
    (hg_mem 0 ⟨le_rfl, s.horizon_pos.le⟩).2
  intro t ht htime
  have hgzero : g t = 0 :=
    ac_eq_zero_of_uniform_negative_drift
      s.horizon_pos.le heta hg_ac
      (fun r hr => (hg_mem r hr).1) hg0 hnonpos hstrict ht htime
  let xt : Simplex Buffer := fluidStateSimplex s t ht
  have hLzero : Lyapunov.LAlpha alpha xt = 0 := by
    simpa only [Lyapunov.LAlpha, xt, fluidStateSimplex, g] using hgzero
  have hxt : xt = alpha :=
    (Lyapunov.LAlpha_eq_zero_iff alpha xt halpha).1 hLzero
  funext i
  exact congrArg (fun z : Simplex Buffer => z i) hxt

end PaperStatements.Network

end StateDepMOR
