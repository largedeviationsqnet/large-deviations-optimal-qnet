import StateDepMOR.TokenIID
import StateDepMOR.FiniteQueueTrajectories
import StateDepMOR.FiniteQueueLongRun
import StateDepMOR.ConcretePerformance
import StateDepMOR.InitialPerformance
import StateDepMOR.Asymptotics
import StateDepMOR.CutAnalysis
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Critical Hall equality

This module treats the equality case of Proposition `hall_is_necessary`.
For a limited cut with equal net arrival and service rates, its primitive
cut increments form a symmetric lazy walk.  The proof below derives the
finite-horizon probability estimate from second and fourth moments; it does
not assume a random-walk hitting estimate.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

attribute [local instance] tokenTypeMeasurableSpace

variable (N : Network Buffer Server)

private theorem negativeIncrementMass (jset : Finset Server) :
    Finset.univ.sum (fun jk :
        TokenType (Buffer := Buffer) (Server := Server) =>
      N.phi jk.1 jk.2 *
        (if jk.1 ∈ jset /\ jk.2 ∉ N.neighborhood jset then
          (1 : Real)
        else 0)) =
      N.netServiceRate jset := by
  classical
  simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
  calc
    Finset.univ.sum (fun j => Finset.univ.sum (fun k =>
        if j ∈ jset /\ k ∉ N.neighborhood jset then N.phi j k else 0)) =
        Finset.univ.sum (fun j =>
          if j ∈ jset then
            Finset.univ.sum (fun k =>
              if k ∉ N.neighborhood jset then N.phi j k else 0)
          else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : j ∈ jset <;> simp [hj]
    _ = (Finset.univ.filter fun j => j ∈ jset).sum (fun j =>
          Finset.univ.sum (fun k =>
            if k ∉ N.neighborhood jset then N.phi j k else 0)) := by
            rw [Finset.sum_filter]
    _ = jset.sum (fun j =>
          (Finset.univ.filter fun k => k ∉ N.neighborhood jset).sum
            (fun k => N.phi j k)) := by
            rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_filter]
    _ = N.netServiceRate jset := rfl

private theorem positiveIncrementMass (jset : Finset Server) :
    Finset.univ.sum (fun jk :
        TokenType (Buffer := Buffer) (Server := Server) =>
      N.phi jk.1 jk.2 *
        (if jk.1 ∉ jset /\ jk.2 ∈ N.neighborhood jset then
          (1 : Real)
        else 0)) =
      N.netArrivalRate jset := by
  classical
  simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero]
  calc
    Finset.univ.sum (fun j => Finset.univ.sum (fun k =>
        if j ∉ jset /\ k ∈ N.neighborhood jset then N.phi j k else 0)) =
        Finset.univ.sum (fun j =>
          if j ∉ jset then
            Finset.univ.sum (fun k =>
              if k ∈ N.neighborhood jset then N.phi j k else 0)
          else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : j ∈ jset <;> simp [hj]
    _ = (Finset.univ.filter fun j => j ∉ jset).sum (fun j =>
          Finset.univ.sum (fun k =>
            if k ∈ N.neighborhood jset then N.phi j k else 0)) := by
            rw [Finset.sum_filter]
    _ = (Finset.univ.filter fun j => j ∉ jset).sum (fun j =>
          (N.neighborhood jset).sum (fun k => N.phi j k)) := by
            apply Finset.sum_congr rfl
            intro j _
            simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
              (Finset.sum_filter (s := Finset.univ)
                (fun k => k ∈ N.neighborhood jset)
                (fun k => N.phi j k)).symm
    _ = N.netArrivalRate jset := rfl

private theorem primitiveCutIncrement_mem (jset : Finset Server)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    N.primitiveCutIncrement jset jk = -1 \/
      N.primitiveCutIncrement jset jk = 0 \/
      N.primitiveCutIncrement jset jk = 1 := by
  by_cases ho : jk.1 ∈ jset
  <;> by_cases hd : jk.2 ∈ N.neighborhood jset
  <;> simp [primitiveCutIncrement, tokenDestinationIn, tokenOriginIn, ho, hd]

private theorem primitiveCutIncrement_sq (jset : Finset Server)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    (N.primitiveCutIncrement jset jk) ^ 2 =
      (if jk.1 ∈ jset /\ jk.2 ∉ N.neighborhood jset then
        (1 : Real)
      else 0) +
      (if jk.1 ∉ jset /\ jk.2 ∈ N.neighborhood jset then
        (1 : Real)
      else 0) := by
  by_cases ho : jk.1 ∈ jset
  <;> by_cases hd : jk.2 ∈ N.neighborhood jset
  <;> simp [primitiveCutIncrement, tokenDestinationIn, tokenOriginIn, ho, hd]

private theorem primitiveCutIncrement_cube (jset : Finset Server)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    (N.primitiveCutIncrement jset jk) ^ 3 =
      N.primitiveCutIncrement jset jk := by
  by_cases ho : jk.1 ∈ jset
  <;> by_cases hd : jk.2 ∈ N.neighborhood jset
  <;> simp [primitiveCutIncrement, tokenDestinationIn, tokenOriginIn, ho, hd]
  <;> norm_num

private theorem primitiveCutIncrement_fourth (jset : Finset Server)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    (N.primitiveCutIncrement jset jk) ^ 4 =
      (N.primitiveCutIncrement jset jk) ^ 2 := by
  by_cases ho : jk.1 ∈ jset
  <;> by_cases hd : jk.2 ∈ N.neighborhood jset
  <;> simp [primitiveCutIncrement, tokenDestinationIn, tokenOriginIn, ho, hd]
  <;> norm_num

theorem primitiveCutIncrement_mean (jset : Finset Server) :
    Finset.univ.sum (fun jk =>
        (N.tokenLaw jk).toReal * N.primitiveCutIncrement jset jk) =
      N.netArrivalRate jset - N.netServiceRate jset := by
  have h := N.tokenOriginSubDestination_eq_netImbalance jset
  simp only [N.tokenLaw_toReal] at h ⊢
  unfold primitiveCutIncrement at *
  calc
    Finset.univ.sum (fun jk => N.phi jk.1 jk.2 *
        (N.tokenDestinationIn (N.neighborhood jset) jk -
          N.tokenOriginIn jset jk)) =
        -(Finset.univ.sum (fun jk => N.phi jk.1 jk.2 *
          (N.tokenOriginIn jset jk -
            N.tokenDestinationIn (N.neighborhood jset) jk))) := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro jk _
              ring
    _ = -(N.netServiceRate jset - N.netArrivalRate jset) := by rw [h]
    _ = N.netArrivalRate jset - N.netServiceRate jset := by ring

theorem primitiveCutIncrement_secondMoment (jset : Finset Server) :
    Finset.univ.sum (fun jk =>
        (N.tokenLaw jk).toReal *
          (N.primitiveCutIncrement jset jk) ^ 2) =
      N.netArrivalRate jset + N.netServiceRate jset := by
  classical
  simp only [N.tokenLaw_toReal, N.primitiveCutIncrement_sq]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, N.negativeIncrementMass,
    N.positiveIncrementMass]
  ring

theorem primitiveCutIncrement_thirdMoment (jset : Finset Server) :
    Finset.univ.sum (fun jk =>
        (N.tokenLaw jk).toReal *
          (N.primitiveCutIncrement jset jk) ^ 3) =
      N.netArrivalRate jset - N.netServiceRate jset := by
  simp only [N.primitiveCutIncrement_cube]
  exact N.primitiveCutIncrement_mean jset

theorem primitiveCutIncrement_fourthMoment (jset : Finset Server) :
    Finset.univ.sum (fun jk =>
        (N.tokenLaw jk).toReal *
          (N.primitiveCutIncrement jset jk) ^ 4) =
      N.netArrivalRate jset + N.netServiceRate jset := by
  simp only [N.primitiveCutIncrement_fourth]
  exact N.primitiveCutIncrement_secondMoment jset

private theorem tokenLaw_map_apply_toReal
    (f : TokenType (Buffer := Buffer) (Server := Server) -> Real)
    (z : Real) :
    ((N.tokenLaw.map f) z).toReal =
      Finset.univ.sum (fun jk =>
        if z = f jk then (N.tokenLaw jk).toReal else 0) := by
  rw [PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro jk _
    split <;> simp_all
  · intro jk _
    split
    · exact N.tokenLaw.apply_ne_top jk
    · exact ENNReal.zero_ne_top

/-- At critical equality the one-step primitive cut increment has the same
law as its negation. -/
theorem primitiveCutIncrement_map_neg_eq (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset) :
    N.tokenLaw.map (N.primitiveCutIncrement jset) =
      N.tokenLaw.map (fun jk => -N.primitiveCutIncrement jset jk) := by
  classical
  apply PMF.ext
  intro z
  apply (ENNReal.toReal_eq_toReal_iff'
    ((N.tokenLaw.map (N.primitiveCutIncrement jset)).apply_ne_top z)
    ((N.tokenLaw.map
      (fun jk => -N.primitiveCutIncrement jset jk)).apply_ne_top z)).mp
  rw [N.tokenLaw_map_apply_toReal, N.tokenLaw_map_apply_toReal]
  simp only [N.tokenLaw_toReal]
  by_cases hzneg : z = -1
  · subst z
    calc
      Finset.univ.sum (fun jk =>
          if (-1 : Real) = N.primitiveCutIncrement jset jk then
            N.phi jk.1 jk.2
          else 0) =
          N.netServiceRate jset := by
            rw [← N.negativeIncrementMass jset]
            apply Finset.sum_congr rfl
            intro jk _
            by_cases ho : jk.1 ∈ jset
            <;> by_cases hd : jk.2 ∈ N.neighborhood jset
            <;> simp [primitiveCutIncrement, tokenDestinationIn,
              tokenOriginIn, ho, hd]
            <;> norm_num
      _ = N.netArrivalRate jset := hcritical.symm
      _ = Finset.univ.sum (fun jk =>
          if (-1 : Real) = -N.primitiveCutIncrement jset jk then
            N.phi jk.1 jk.2
          else 0) := by
            rw [← N.positiveIncrementMass jset]
            apply Finset.sum_congr rfl
            intro jk _
            by_cases ho : jk.1 ∈ jset
            <;> by_cases hd : jk.2 ∈ N.neighborhood jset
            <;> simp [primitiveCutIncrement, tokenDestinationIn,
              tokenOriginIn, ho, hd]
            <;> norm_num
  · by_cases hzero : z = 0
    · subst z
      apply Finset.sum_congr rfl
      intro jk _
      by_cases hinc : N.primitiveCutIncrement jset jk = 0
      · simp [hinc]
      · have hleft : Not (0 = N.primitiveCutIncrement jset jk) :=
          fun h => hinc h.symm
        have hright : Not (0 = -N.primitiveCutIncrement jset jk) := by
          intro h
          apply hinc
          linarith
        simp [hleft, hright]
    · by_cases hzone : z = 1
      · subst z
        calc
          Finset.univ.sum (fun jk =>
              if (1 : Real) = N.primitiveCutIncrement jset jk then
                N.phi jk.1 jk.2
              else 0) =
              N.netArrivalRate jset := by
                rw [← N.positiveIncrementMass jset]
                apply Finset.sum_congr rfl
                intro jk _
                by_cases ho : jk.1 ∈ jset
                <;> by_cases hd : jk.2 ∈ N.neighborhood jset
                <;> simp [primitiveCutIncrement, tokenDestinationIn,
                  tokenOriginIn, ho, hd]
                <;> norm_num
          _ = N.netServiceRate jset := hcritical
          _ = Finset.univ.sum (fun jk =>
              if (1 : Real) = -N.primitiveCutIncrement jset jk then
                N.phi jk.1 jk.2
              else 0) := by
                rw [← N.negativeIncrementMass jset]
                apply Finset.sum_congr rfl
                intro jk _
                by_cases ho : jk.1 ∈ jset
                <;> by_cases hd : jk.2 ∈ N.neighborhood jset
                <;> simp [primitiveCutIncrement, tokenDestinationIn,
                  tokenOriginIn, ho, hd]
                <;> norm_num
      · apply Finset.sum_congr rfl
        intro jk _
        rcases N.primitiveCutIncrement_mem jset jk with
          hinc | hinc | hinc
        · rw [hinc]
          simp [hzneg, hzone]
        · rw [hinc]
          simp [hzero]
        · rw [hinc]
          simp [hzone, hzneg]

/-- The cut increment observed at event epoch `r` on the canonical IID token
path. -/
def cutIncrementAt (jset : Finset Server) (r : Nat)
    (omega : N.TokenPath) : Real :=
  N.primitiveCutIncrement jset (N.tokenAt r omega)

theorem cutIncrementAt_measurable (jset : Finset Server) (r : Nat) :
    Measurable (N.cutIncrementAt jset r) :=
  Measurable.of_discrete.comp (N.tokenAt_measurable r)

theorem cutIncrementAt_iIndep (jset : Finset Server) :
    iIndepFun (N.cutIncrementAt jset) N.tokenPathMeasure := by
  exact N.tokenAt_iIndep.comp
    (fun _ => N.primitiveCutIncrement jset)
    (fun _ => Measurable.of_discrete)

/-- Primitive cut walk after the first `n` event epochs. -/
def cutWalk (jset : Finset Server) (n : Nat)
    (omega : N.TokenPath) : Real :=
  (Finset.range n).sum (fun r => N.cutIncrementAt jset r omega)

/-- The first `n` canonical IID tokens as the list consumed by
`FiniteQueueTrajectories`. -/
def tokenPrefix (n : Nat) (omega : N.TokenPath) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  List.ofFn (fun r : Fin n => N.tokenAt r omega)

private theorem primitiveCutSum_eq_list_sum (jset : Finset Server)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    N.primitiveCutSum jset tokens =
      (tokens.map (N.primitiveCutIncrement jset)).sum := by
  induction tokens with
  | nil =>
      rfl
  | cons jk rest ih =>
      simp only [primitiveCutSum, List.map_cons, List.sum_cons, ih]

/-- Readback bridge from the canonical IID prefix to the deterministic
trajectory primitive sum. -/
theorem primitiveCutSum_tokenPrefix (jset : Finset Server)
    (n : Nat) (omega : N.TokenPath) :
    N.primitiveCutSum jset (N.tokenPrefix n omega) =
      N.cutWalk jset n omega := by
  rw [N.primitiveCutSum_eq_list_sum]
  unfold tokenPrefix cutWalk cutIncrementAt
  rw [List.map_ofFn, List.sum_ofFn]
  simpa only [Function.comp_apply] using
    Fin.sum_univ_eq_sum_range
      (fun r => N.primitiveCutIncrement jset (N.tokenAt r omega)) n

theorem cutWalk_zero (jset : Finset Server) (omega : N.TokenPath) :
    N.cutWalk jset 0 omega = 0 := by
  simp [cutWalk]

theorem cutWalk_succ (jset : Finset Server) (n : Nat)
    (omega : N.TokenPath) :
    N.cutWalk jset (n + 1) omega =
      N.cutWalk jset n omega + N.cutIncrementAt jset n omega := by
  simp [cutWalk, Finset.sum_range_succ]

theorem cutWalk_measurable (jset : Finset Server) (n : Nat) :
    Measurable (N.cutWalk jset n) := by
  unfold cutWalk
  exact Finset.measurable_fun_sum (Finset.range n)
    (fun r _ => N.cutIncrementAt_measurable jset r)

theorem cutIncrementAt_abs_le_one (jset : Finset Server)
    (r : Nat) (omega : N.TokenPath) :
    abs (N.cutIncrementAt jset r omega) <= 1 := by
  unfold cutIncrementAt
  rcases N.primitiveCutIncrement_mem jset (N.tokenAt r omega) with
    h | h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num
  · rw [h]
    norm_num

theorem cutWalk_abs_le (jset : Finset Server) (n : Nat)
    (omega : N.TokenPath) :
    abs (N.cutWalk jset n omega) <= (n : Real) := by
  unfold cutWalk
  calc
    abs ((Finset.range n).sum
        (fun r => N.cutIncrementAt jset r omega)) <=
        (Finset.range n).sum
          (fun r => abs (N.cutIncrementAt jset r omega)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= (Finset.range n).sum (fun _ => (1 : Real)) := by
      apply Finset.sum_le_sum
      intro r _
      exact N.cutIncrementAt_abs_le_one jset r omega
    _ = (n : Real) := by simp

theorem cutIncrementAt_integrable_pow (jset : Finset Server)
    (r p : Nat) :
    Integrable (fun omega => (N.cutIncrementAt jset r omega) ^ p)
      N.tokenPathMeasure := by
  apply Integrable.of_bound
    ((N.cutIncrementAt_measurable jset r).pow_const p).aestronglyMeasurable
    1
  exact Filter.Eventually.of_forall (fun omega => by
    rw [Real.norm_eq_abs, abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg _)
      (N.cutIncrementAt_abs_le_one jset r omega) p).trans_eq
        (one_pow p))

theorem cutWalk_integrable_pow (jset : Finset Server) (n p : Nat) :
    Integrable (fun omega => (N.cutWalk jset n omega) ^ p)
      N.tokenPathMeasure := by
  apply Integrable.of_bound
    ((N.cutWalk_measurable jset n).pow_const p).aestronglyMeasurable
    ((n : Real) ^ p)
  exact Filter.Eventually.of_forall (fun omega => by
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (N.cutWalk_abs_le jset n omega) p)

private theorem cutWalk_mul_increment_integrable
    (jset : Finset Server) (n a b : Nat) :
    Integrable (fun omega =>
      (N.cutWalk jset n omega) ^ a *
        (N.cutIncrementAt jset n omega) ^ b)
      N.tokenPathMeasure := by
  apply Integrable.of_bound
    (((N.cutWalk_measurable jset n).pow_const a).mul
      ((N.cutIncrementAt_measurable jset n).pow_const b)
      ).aestronglyMeasurable
    ((n : Real) ^ a)
  exact Filter.Eventually.of_forall (fun omega => by
    change abs
      ((N.cutWalk jset n omega) ^ a *
        (N.cutIncrementAt jset n omega) ^ b) <= (n : Real) ^ a
    rw [abs_mul, abs_pow, abs_pow]
    have hwalk := pow_le_pow_left₀ (abs_nonneg _)
      (N.cutWalk_abs_le jset n omega) a
    have hinc := pow_le_pow_left₀ (abs_nonneg _)
      (N.cutIncrementAt_abs_le_one jset n omega) b
    calc
      abs (N.cutWalk jset n omega) ^ a *
          abs (N.cutIncrementAt jset n omega) ^ b <=
          (n : Real) ^ a * 1 ^ b :=
        mul_le_mul hwalk hinc (by positivity) (by positivity)
      _ = (n : Real) ^ a := by simp)

private theorem cutWalk_indep_increment (jset : Finset Server) (n : Nat) :
    IndepFun (N.cutWalk jset n) (N.cutIncrementAt jset n)
      N.tokenPathMeasure := by
  unfold cutWalk
  have h :=
    (N.cutIncrementAt_iIndep jset).indepFun_finsetSum_of_notMem
      (s := Finset.range n) (i := n)
      (fun r => N.cutIncrementAt_measurable jset r)
      Finset.notMem_range_self
  have heq :
      Finset.sum (Finset.range n) (N.cutIncrementAt jset) =
        fun omega => (Finset.range n).sum
          (fun r => N.cutIncrementAt jset r omega) := by
    funext omega
    exact Finset.sum_apply omega (Finset.range n)
      (N.cutIncrementAt jset)
  rw [heq] at h
  exact h

private theorem integral_cutWalk_mul_increment_pow
    (jset : Finset Server) (n a b : Nat) :
    integral N.tokenPathMeasure (fun omega =>
        (N.cutWalk jset n omega) ^ a *
          (N.cutIncrementAt jset n omega) ^ b) =
      integral N.tokenPathMeasure
          (fun omega => (N.cutWalk jset n omega) ^ a) *
        integral N.tokenPathMeasure
          (fun omega => (N.cutIncrementAt jset n omega) ^ b) := by
  have h := (N.cutWalk_indep_increment jset n).comp
    (measurable_id.pow_const a) (measurable_id.pow_const b)
  simpa only [Function.comp_apply, id_eq] using
    h.integral_fun_mul_eq_mul_integral
      ((N.cutWalk_measurable jset n).pow_const a).aestronglyMeasurable
      ((N.cutIncrementAt_measurable jset n).pow_const b
        ).aestronglyMeasurable

private theorem cutIncrementAt_integral_pow
    (jset : Finset Server) (r p : Nat) :
    integral N.tokenPathMeasure
        (fun omega => (N.cutIncrementAt jset r omega) ^ p) =
      Finset.univ.sum (fun jk =>
        (N.tokenLaw jk).toReal *
          (N.primitiveCutIncrement jset jk) ^ p) := by
  have hmap := (N.tokenAt_hasLaw r).integral_comp
    ((Measurable.of_discrete :
      Measurable (fun jk :
        TokenType (Buffer := Buffer) (Server := Server) =>
          (N.primitiveCutIncrement jset jk) ^ p)).aestronglyMeasurable)
  calc
    integral N.tokenPathMeasure
        (fun omega => (N.cutIncrementAt jset r omega) ^ p) =
        integral N.tokenLaw.toMeasure
          (fun jk => (N.primitiveCutIncrement jset jk) ^ p) := by
            simpa only [cutIncrementAt, Function.comp_apply] using hmap
    _ = Finset.univ.sum (fun jk =>
          (N.tokenLaw jk).toReal *
            (N.primitiveCutIncrement jset jk) ^ p) := by
            rw [PMF.integral_eq_sum]
            simp only [smul_eq_mul]

theorem cutIncrementAt_integral_eq_zero_of_critical
    (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (r : Nat) :
    integral N.tokenPathMeasure (N.cutIncrementAt jset r) = 0 := by
  rw [show N.cutIncrementAt jset r =
    fun omega => (N.cutIncrementAt jset r omega) ^ 1 by
      funext omega
      simp]
  rw [N.cutIncrementAt_integral_pow jset r 1]
  simp only [pow_one, N.primitiveCutIncrement_mean jset, hcritical, sub_self]

theorem cutIncrementAt_secondMoment_of_critical
    (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (r : Nat) :
    integral N.tokenPathMeasure
        (fun omega => (N.cutIncrementAt jset r omega) ^ 2) =
      2 * N.netServiceRate jset := by
  rw [N.cutIncrementAt_integral_pow jset r 2]
  rw [N.primitiveCutIncrement_secondMoment jset, hcritical]
  ring

theorem cutIncrementAt_thirdMoment_eq_zero_of_critical
    (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (r : Nat) :
    integral N.tokenPathMeasure
        (fun omega => (N.cutIncrementAt jset r omega) ^ 3) = 0 := by
  rw [N.cutIncrementAt_integral_pow jset r 3]
  simp only [N.primitiveCutIncrement_thirdMoment jset, hcritical, sub_self]

theorem cutIncrementAt_fourthMoment_of_critical
    (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (r : Nat) :
    integral N.tokenPathMeasure
        (fun omega => (N.cutIncrementAt jset r omega) ^ 4) =
      2 * N.netServiceRate jset := by
  rw [N.cutIncrementAt_integral_pow jset r 4]
  rw [N.primitiveCutIncrement_fourthMoment jset, hcritical]
  ring

theorem cutWalk_integral_eq_zero_of_critical
    (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (n : Nat) :
    integral N.tokenPathMeasure (N.cutWalk jset n) = 0 := by
  unfold cutWalk
  rw [integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro r _
    exact N.cutIncrementAt_integral_eq_zero_of_critical
      jset hcritical r
  · intro r _
    simpa only [pow_one] using
      N.cutIncrementAt_integrable_pow jset r 1

theorem cutIncrementAt_identDistrib_neg_of_critical
    (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (r : Nat) :
    IdentDistrib (N.cutIncrementAt jset r)
      (fun omega => -N.cutIncrementAt jset r omega)
      N.tokenPathMeasure N.tokenPathMeasure := by
  let inc :
      TokenType (Buffer := Buffer) (Server := Server) -> Real :=
    N.primitiveCutIncrement jset
  have hinc : Measurable inc := Measurable.of_discrete
  have hneg : Measurable (fun jk => -inc jk) := hinc.neg
  have hincLaw :
      HasLaw inc (N.tokenLaw.map inc).toMeasure N.tokenLaw.toMeasure :=
    ⟨hinc.aemeasurable, PMF.toMeasure_map inc N.tokenLaw hinc⟩
  have hnegLaw :
      HasLaw (fun jk => -inc jk)
        (N.tokenLaw.map inc).toMeasure N.tokenLaw.toMeasure := by
    refine ⟨hneg.aemeasurable, ?_⟩
    rw [PMF.toMeasure_map (fun jk => -inc jk) N.tokenLaw hneg]
    rw [show N.tokenLaw.map (fun jk => -inc jk) =
      N.tokenLaw.map inc by
        exact (N.primitiveCutIncrement_map_neg_eq
          jset hcritical).symm]
  have hleft := hincLaw.comp (N.tokenAt_hasLaw r)
  have hright := hnegLaw.comp (N.tokenAt_hasLaw r)
  change IdentDistrib
    (N.primitiveCutIncrement jset ∘ N.tokenAt r)
    ((fun jk => -N.primitiveCutIncrement jset jk) ∘ N.tokenAt r)
    N.tokenPathMeasure N.tokenPathMeasure
  exact hleft.identDistrib hright

/-- Every finite critical cut-walk sum has a distribution symmetric about
zero. -/
theorem cutWalk_identDistrib_neg_of_critical
    (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (n : Nat) :
    IdentDistrib (N.cutWalk jset n)
      (fun omega => -N.cutWalk jset n omega)
      N.tokenPathMeasure N.tokenPathMeasure := by
  let X : Nat -> N.TokenPath -> Real := N.cutIncrementAt jset
  have hX : iIndepFun X N.tokenPathMeasure :=
    N.cutIncrementAt_iIndep jset
  have hnegX :
      iIndepFun (fun r omega => -X r omega) N.tokenPathMeasure := by
    exact hX.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hseq := IdentDistrib.pi
    (fun r => N.cutIncrementAt_identDistrib_neg_of_critical
      jset hcritical r)
    hX hnegX
  have hsum : Measurable (fun x : Nat -> Real =>
      (Finset.range n).sum (fun r => x r)) :=
    Finset.measurable_fun_sum (Finset.range n)
      (fun r _ => measurable_pi_apply r)
  have h := hseq.comp hsum
  change IdentDistrib
    (fun omega =>
      (Finset.range n).sum (fun r => N.cutIncrementAt jset r omega))
    (fun omega =>
      -(Finset.range n).sum (fun r => N.cutIncrementAt jset r omega))
    N.tokenPathMeasure N.tokenPathMeasure
  convert h using 1 <;> funext omega
  · rfl
  · simp only [Function.comp_apply]
    rw [← Finset.sum_neg_distrib]

/-- Exact variance/second-moment growth of the critical lazy walk. -/
theorem cutWalk_secondMoment_of_critical
    (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (n : Nat) :
    integral N.tokenPathMeasure
        (fun omega => (N.cutWalk jset n omega) ^ 2) =
      (n : Real) * (2 * N.netServiceRate jset) := by
  induction n with
  | zero =>
      simp [cutWalk]
  | succ n ih =>
      have hS2 := N.cutWalk_integrable_pow jset n 2
      have hSX := N.cutWalk_mul_increment_integrable jset n 1 1
      have h2SX : Integrable (fun omega =>
          2 * (N.cutWalk jset n omega *
            N.cutIncrementAt jset n omega))
          N.tokenPathMeasure :=
        by simpa only [pow_one] using hSX.const_mul 2
      have hX2 := N.cutIncrementAt_integrable_pow jset n 2
      have hrest : Integrable (fun omega =>
          2 * (N.cutWalk jset n omega *
            N.cutIncrementAt jset n omega) +
          (N.cutIncrementAt jset n omega) ^ 2)
          N.tokenPathMeasure := by
        change Integrable
          ((fun omega => 2 * (N.cutWalk jset n omega *
              N.cutIncrementAt jset n omega)) +
            (fun omega => (N.cutIncrementAt jset n omega) ^ 2))
          N.tokenPathMeasure
        exact h2SX.add hX2
      have hfactor :=
        N.integral_cutWalk_mul_increment_pow jset n 1 1
      simp only [pow_one] at hfactor
      rw [show (fun omega => (N.cutWalk jset (n + 1) omega) ^ 2) =
          fun omega =>
            (N.cutWalk jset n omega) ^ 2 +
              (2 * (N.cutWalk jset n omega *
                N.cutIncrementAt jset n omega) +
              (N.cutIncrementAt jset n omega) ^ 2) by
        funext omega
        rw [N.cutWalk_succ jset n omega]
        ring]
      rw [show integral N.tokenPathMeasure (fun omega =>
          (N.cutWalk jset n omega) ^ 2 +
            (2 * (N.cutWalk jset n omega *
              N.cutIncrementAt jset n omega) +
            (N.cutIncrementAt jset n omega) ^ 2)) =
          integral N.tokenPathMeasure
              (fun omega => (N.cutWalk jset n omega) ^ 2) +
            integral N.tokenPathMeasure (fun omega =>
              2 * (N.cutWalk jset n omega *
                N.cutIncrementAt jset n omega) +
              (N.cutIncrementAt jset n omega) ^ 2) by
        simpa only [Pi.add_apply] using integral_add hS2 hrest]
      rw [show integral N.tokenPathMeasure (fun omega =>
          2 * (N.cutWalk jset n omega *
            N.cutIncrementAt jset n omega) +
          (N.cutIncrementAt jset n omega) ^ 2) =
          integral N.tokenPathMeasure (fun omega =>
              2 * (N.cutWalk jset n omega *
                N.cutIncrementAt jset n omega)) +
            integral N.tokenPathMeasure
              (fun omega => (N.cutIncrementAt jset n omega) ^ 2) by
        simpa only [Pi.add_apply] using integral_add h2SX hX2]
      rw [integral_const_mul]
      rw [hfactor]
      rw [ih]
      rw [N.cutWalk_integral_eq_zero_of_critical jset hcritical n]
      rw [N.cutIncrementAt_integral_eq_zero_of_critical
        jset hcritical n]
      rw [N.cutIncrementAt_secondMoment_of_critical
        jset hcritical n]
      simp only [pow_one, zero_mul, mul_zero]
      push_cast
      ring

private theorem cutWalk_fourthMoment_succ_of_critical
    (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (n : Nat) :
    integral N.tokenPathMeasure
        (fun omega => (N.cutWalk jset (n + 1) omega) ^ 4) =
      integral N.tokenPathMeasure
          (fun omega => (N.cutWalk jset n omega) ^ 4) +
        6 * ((n : Real) * (2 * N.netServiceRate jset)) *
          (2 * N.netServiceRate jset) +
        2 * N.netServiceRate jset := by
  let S : N.TokenPath -> Real := N.cutWalk jset n
  let X : N.TokenPath -> Real := N.cutIncrementAt jset n
  let t31 : N.TokenPath -> Real := fun omega =>
    4 * (S omega ^ 3 * X omega)
  let t22 : N.TokenPath -> Real := fun omega =>
    6 * (S omega ^ 2 * X omega ^ 2)
  let t13 : N.TokenPath -> Real := fun omega =>
    4 * (S omega * X omega ^ 3)
  have hS4 : Integrable (fun omega => S omega ^ 4)
      N.tokenPathMeasure := by
    exact N.cutWalk_integrable_pow jset n 4
  have ht31 : Integrable t31 N.tokenPathMeasure := by
    have h := N.cutWalk_mul_increment_integrable jset n 3 1
    simpa only [t31, S, X, pow_one] using h.const_mul 4
  have ht22 : Integrable t22 N.tokenPathMeasure := by
    have h := N.cutWalk_mul_increment_integrable jset n 2 2
    simpa only [t22, S, X] using h.const_mul 6
  have ht13 : Integrable t13 N.tokenPathMeasure := by
    have h := N.cutWalk_mul_increment_integrable jset n 1 3
    simpa only [t13, S, X, pow_one] using h.const_mul 4
  have hX4 : Integrable (fun omega => X omega ^ 4)
      N.tokenPathMeasure := by
    exact N.cutIncrementAt_integrable_pow jset n 4
  have htail13 : Integrable (fun omega => t13 omega + X omega ^ 4)
      N.tokenPathMeasure := by
    change Integrable (t13 + fun omega => X omega ^ 4)
      N.tokenPathMeasure
    exact ht13.add hX4
  have htail22 : Integrable (fun omega =>
      t22 omega + (t13 omega + X omega ^ 4))
      N.tokenPathMeasure := by
    change Integrable
      (t22 + fun omega => t13 omega + X omega ^ 4)
      N.tokenPathMeasure
    exact ht22.add htail13
  have htail31 : Integrable (fun omega =>
      t31 omega + (t22 omega + (t13 omega + X omega ^ 4)))
      N.tokenPathMeasure := by
    change Integrable
      (t31 + fun omega =>
        t22 omega + (t13 omega + X omega ^ 4))
      N.tokenPathMeasure
    exact ht31.add htail22
  have h31 := N.integral_cutWalk_mul_increment_pow jset n 3 1
  have h22 := N.integral_cutWalk_mul_increment_pow jset n 2 2
  have h13 := N.integral_cutWalk_mul_increment_pow jset n 1 3
  simp only [pow_one] at h31 h13
  rw [show (fun omega => (N.cutWalk jset (n + 1) omega) ^ 4) =
      fun omega =>
        S omega ^ 4 +
          (t31 omega +
            (t22 omega + (t13 omega + X omega ^ 4))) by
    funext omega
    simp only [S, X, t31, t22, t13]
    rw [N.cutWalk_succ jset n omega]
    ring]
  rw [show integral N.tokenPathMeasure (fun omega =>
      S omega ^ 4 +
        (t31 omega +
          (t22 omega + (t13 omega + X omega ^ 4)))) =
      integral N.tokenPathMeasure (fun omega => S omega ^ 4) +
        integral N.tokenPathMeasure (fun omega =>
          t31 omega +
            (t22 omega + (t13 omega + X omega ^ 4))) by
    simpa only [Pi.add_apply] using integral_add hS4 htail31]
  rw [show integral N.tokenPathMeasure (fun omega =>
      t31 omega + (t22 omega + (t13 omega + X omega ^ 4))) =
      integral N.tokenPathMeasure t31 +
        integral N.tokenPathMeasure (fun omega =>
          t22 omega + (t13 omega + X omega ^ 4)) by
    simpa only [Pi.add_apply] using integral_add ht31 htail22]
  rw [show integral N.tokenPathMeasure (fun omega =>
      t22 omega + (t13 omega + X omega ^ 4)) =
      integral N.tokenPathMeasure t22 +
        integral N.tokenPathMeasure
          (fun omega => t13 omega + X omega ^ 4) by
    simpa only [Pi.add_apply] using integral_add ht22 htail13]
  rw [show integral N.tokenPathMeasure
      (fun omega => t13 omega + X omega ^ 4) =
      integral N.tokenPathMeasure t13 +
        integral N.tokenPathMeasure (fun omega => X omega ^ 4) by
    simpa only [Pi.add_apply] using integral_add ht13 hX4]
  simp only [t31, t22, t13, S, X]
  rw [integral_const_mul, integral_const_mul, integral_const_mul]
  rw [h31, h22, h13]
  rw [N.cutIncrementAt_integral_eq_zero_of_critical
    jset hcritical n]
  rw [N.cutWalk_secondMoment_of_critical jset hcritical n]
  rw [N.cutIncrementAt_secondMoment_of_critical jset hcritical n]
  rw [N.cutWalk_integral_eq_zero_of_critical jset hcritical n]
  rw [N.cutIncrementAt_thirdMoment_eq_zero_of_critical
    jset hcritical n]
  rw [N.cutIncrementAt_fourthMoment_of_critical
    jset hcritical n]
  ring

/-- Fourth-moment estimate used in the finite-horizon lower-tail bound. -/
theorem cutWalk_fourthMoment_le_of_critical
    (jset : Finset Server)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (n : Nat) :
    integral N.tokenPathMeasure
        (fun omega => (N.cutWalk jset n omega) ^ 4) <=
      3 * (((n : Real) * (2 * N.netServiceRate jset)) ^ 2) +
        (n : Real) * (2 * N.netServiceRate jset) := by
  have hrateNonneg :
      0 <= 2 * N.netServiceRate jset := by
    have hmu := N.netServiceRate_nonneg jset
    linarith
  induction n with
  | zero =>
      simp [cutWalk]
  | succ n ih =>
      rw [N.cutWalk_fourthMoment_succ_of_critical
        jset hcritical n]
      push_cast
      nlinarith [sq_nonneg (2 * N.netServiceRate jset)]

private theorem integral_indicator_cauchy_sq
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Y : Omega -> Real) (A : Set Omega) (C : Real)
    (hY : Measurable Y) (hYnonneg : forall omega, 0 <= Y omega)
    (hYle : forall omega, Y omega <= C) (hA : MeasurableSet A) :
    (integral mu (fun omega =>
        Y omega * A.indicator (fun _ => (1 : Real)) omega)) ^ 2 <=
      integral mu (fun omega => Y omega ^ 2) * mu.real A := by
  have hYmem : MemLp Y (ENNReal.ofReal 2) mu := by
    apply MemLp.of_bound hY.aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hYnonneg omega)]
      exact hYle omega)
  have hIndicatorMem :
      MemLp (A.indicator (fun _ => (1 : Real)))
        (ENNReal.ofReal 2) mu :=
    memLp_indicator_const _ hA 1 (Or.inr (measure_ne_top mu A))
  have hIndicatorNonneg :
      ∀ᵐ omega ∂mu,
        0 <= A.indicator (fun _ => (1 : Real)) omega :=
    Filter.Eventually.of_forall (fun omega =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) omega)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hYnonneg) hIndicatorNonneg
    hYmem hIndicatorMem
  have hholder' :
      integral mu (fun omega =>
          Y omega * A.indicator (fun _ => (1 : Real)) omega) <=
        Real.sqrt (integral mu (fun omega => Y omega ^ 2)) *
          Real.sqrt (integral mu (fun omega =>
            A.indicator (fun _ => (1 : Real)) omega ^ 2)) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow, one_div] using hholder
  have hIndicatorSq :
      integral mu (fun omega =>
          A.indicator (fun _ => (1 : Real)) omega ^ 2) =
        mu.real A := by
    rw [show
      (fun omega => A.indicator (fun _ => (1 : Real)) omega ^ 2) =
        A.indicator (fun _ => (1 : Real)) by
          funext omega
          by_cases homega : omega ∈ A <;> simp [homega]]
    exact integral_indicator_one hA
  rw [hIndicatorSq] at hholder'
  have hleftNonneg :
      0 <= integral mu (fun omega =>
        Y omega * A.indicator (fun _ => (1 : Real)) omega) :=
    integral_nonneg (fun omega =>
      mul_nonneg (hYnonneg omega)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) omega))
  have hY2Nonneg : 0 <= integral mu (fun omega => Y omega ^ 2) :=
    integral_nonneg (fun omega => sq_nonneg (Y omega))
  calc
    (integral mu (fun omega =>
        Y omega * A.indicator (fun _ => (1 : Real)) omega)) ^ 2 <=
        (Real.sqrt (integral mu (fun omega => Y omega ^ 2)) *
          Real.sqrt (mu.real A)) ^ 2 :=
      (sq_le_sq₀ hleftNonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
          hholder'
    _ = integral mu (fun omega => Y omega ^ 2) * mu.real A := by
      rw [mul_pow, Real.sq_sqrt hY2Nonneg,
        Real.sq_sqrt measureReal_nonneg]

/-- A bounded-variable Paley--Zygmund estimate at half of the mean. -/
private theorem measureReal_gt_half_integral_ge
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (Y : Omega -> Real) (C m : Real)
    (hY : Measurable Y) (hYnonneg : forall omega, 0 <= Y omega)
    (hYle : forall omega, Y omega <= C) (hC : 0 <= C)
    (hmean : integral mu Y = m) (hmpos : 0 < m)
    (hsecond :
      integral mu (fun omega => Y omega ^ 2) <= 4 * m ^ 2) :
    (1 / 16 : Real) <= mu.real {omega | m / 2 < Y omega} := by
  let A : Set Omega := {omega | m / 2 < Y omega}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hY
  let I : Real := integral mu (fun omega =>
    Y omega * A.indicator (fun _ => (1 : Real)) omega)
  have hYintegrable : Integrable Y mu := by
    apply Integrable.of_bound hY.aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun omega => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hYnonneg omega)]
      exact hYle omega)
  have hIintegrable : Integrable (fun omega =>
      Y omega * A.indicator (fun _ => (1 : Real)) omega) mu := by
    apply Integrable.of_bound
      (hY.mul (measurable_const.indicator hA)).aestronglyMeasurable C
    exact Filter.Eventually.of_forall (fun omega => by
      rw [Real.norm_eq_abs]
      by_cases homega : omega ∈ A
      <;> simp [homega, abs_of_nonneg (hYnonneg omega),
        hYle omega, hC])
  have hpointwise : Y <= fun omega =>
      m / 2 + Y omega * A.indicator (fun _ => (1 : Real)) omega := by
    intro omega
    by_cases homega : omega ∈ A
    · simp [homega]
      linarith
    · have homega' : Y omega <= m / 2 :=
        le_of_not_gt (by simpa [A] using homega)
      simpa [homega] using homega'
  have hconst : Integrable (fun _ : Omega => m / 2) mu :=
    integrable_const _
  have hIlower : m / 2 <= I := by
    have hmono :=
      integral_mono hYintegrable (hconst.add hIintegrable) hpointwise
    rw [hmean] at hmono
    have hsplit :
        integral mu
            ((fun _ : Omega => m / 2) +
              fun omega =>
                Y omega * A.indicator (fun _ => (1 : Real)) omega) =
          integral mu (fun _ : Omega => m / 2) +
            integral mu (fun omega =>
              Y omega * A.indicator (fun _ => (1 : Real)) omega) :=
      integral_add hconst hIintegrable
    rw [hsplit, integral_const] at hmono
    simp only [smul_eq_mul] at hmono
    have huniv : mu.real Set.univ = 1 := by
      simp [measureReal_def]
    rw [huniv, one_mul] at hmono
    dsimp only [I]
    linarith
  have hI2 := integral_indicator_cauchy_sq
    mu Y A C hY hYnonneg hYle hA
  change I ^ 2 <=
    integral mu (fun omega => Y omega ^ 2) * mu.real A at hI2
  have hI2upper : I ^ 2 <= 4 * m ^ 2 * mu.real A :=
    hI2.trans (mul_le_mul_of_nonneg_right hsecond measureReal_nonneg)
  have hlowerSq : (m / 2) ^ 2 <= I ^ 2 :=
    pow_le_pow_left₀ (by linarith) hIlower 2
  have hkey :
      (1 / 4 : Real) * m ^ 2 <= (4 * mu.real A) * m ^ 2 := by
    nlinarith [hlowerSq, hI2upper]
  have hcancel :=
    (mul_le_mul_iff_left₀ (sq_pos_of_pos hmpos)).mp hkey
  change (1 / 16 : Real) <= mu.real A
  linarith

/-- Probability that a critical primitive cut increment is nonzero. -/
def criticalStepRate (jset : Finset Server) : Real :=
  2 * N.netServiceRate jset

/-- Integer event-epoch horizon used for a critical cut. Its network
dependent prefactor is fixed while its size dependence is `(K + 1)^2`. -/
def criticalHorizon (jset : Finset Server) (K : Nat) : Nat :=
  Nat.ceil (2 / N.criticalStepRate jset) * (K + 1) ^ 2

@[simp]
theorem criticalStepRate_eq (jset : Finset Server) :
    N.criticalStepRate jset = 2 * N.netServiceRate jset :=
  rfl

@[simp]
theorem criticalHorizon_eq (jset : Finset Server) (K : Nat) :
    N.criticalHorizon jset K =
      Nat.ceil (2 / N.criticalStepRate jset) * (K + 1) ^ 2 :=
  rfl

private theorem criticalHorizon_variance_ge
    (jset : Finset Server) (hservice : 0 < N.netServiceRate jset)
    (K : Nat) :
    2 * ((K : Real) + 1) ^ 2 <=
      (N.criticalHorizon jset K : Real) * N.criticalStepRate jset := by
  have hq : 0 < N.criticalStepRate jset := by
    rw [N.criticalStepRate_eq]
    linarith
  have hceil :
      2 / N.criticalStepRate jset <=
        (Nat.ceil (2 / N.criticalStepRate jset) : Real) :=
    Nat.le_ceil _
  have hbase :
      2 <=
        (Nat.ceil (2 / N.criticalStepRate jset) : Real) *
          N.criticalStepRate jset := by
    calc
      2 = (2 / N.criticalStepRate jset) *
          N.criticalStepRate jset := by
            field_simp
      _ <= (Nat.ceil (2 / N.criticalStepRate jset) : Real) *
          N.criticalStepRate jset :=
        mul_le_mul_of_nonneg_right hceil hq.le
  have hsq : 0 <= ((K : Real) + 1) ^ 2 := sq_nonneg _
  calc
    2 * ((K : Real) + 1) ^ 2 <=
        ((Nat.ceil (2 / N.criticalStepRate jset) : Real) *
          N.criticalStepRate jset) * ((K : Real) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right hbase hsq
    _ = (N.criticalHorizon jset K : Real) *
        N.criticalStepRate jset := by
      rw [N.criticalHorizon_eq]
      push_cast
      ring

/-- The critical horizon is bounded by a network-dependent constant times
`K^2` for positive system sizes. -/
theorem criticalHorizon_le_four_mul_sq
    (jset : Finset Server) (K : Nat) (hK : 0 < K) :
    (N.criticalHorizon jset K : Real) <=
      4 * (Nat.ceil (2 / N.criticalStepRate jset) : Real) *
        (K : Real) ^ 2 := by
  rw [N.criticalHorizon_eq]
  push_cast
  have hfactor :
      0 <= (Nat.ceil (2 / N.criticalStepRate jset) : Real) :=
    Nat.cast_nonneg _
  have hKreal : 1 <= (K : Real) := by
    exact_mod_cast hK
  have hsq :
      ((K : Real) + 1) ^ 2 <= 4 * (K : Real) ^ 2 := by
    nlinarith
  calc
    (Nat.ceil (2 / N.criticalStepRate jset) : Real) *
        ((K : Real) + 1) ^ 2 <=
        (Nat.ceil (2 / N.criticalStepRate jset) : Real) *
          (4 * (K : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hfactor
    _ = 4 * (Nat.ceil (2 / N.criticalStepRate jset) : Real) *
        (K : Real) ^ 2 := by ring

/-- A critical limited cut has a uniformly positive lower-tail probability
at the quadratic horizon. -/
theorem cutWalk_lt_neg_probability_ge
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (K : Nat) :
    (1 / 32 : Real) <=
      N.tokenPathMeasure.real {omega |
        N.cutWalk jset (N.criticalHorizon jset K) omega < -(K : Real)} := by
  let n := N.criticalHorizon jset K
  let q := N.criticalStepRate jset
  let variance := (n : Real) * q
  let S : N.TokenPath -> Real := N.cutWalk jset n
  let A : Set N.TokenPath := {omega | variance / 2 < S omega ^ 2}
  let lower : Set N.TokenPath := {omega | S omega < -(K : Real)}
  let upper : Set N.TokenPath := {omega | (K : Real) < S omega}
  have hvariance :
      2 * ((K : Real) + 1) ^ 2 <= variance := by
    exact N.criticalHorizon_variance_ge jset hlimited.2 K
  have hvariancePos : 0 < variance := by
    have hKsq : 0 < ((K : Real) + 1) ^ 2 := sq_pos_of_pos (by positivity)
    linarith
  have hmean :
      integral N.tokenPathMeasure (fun omega => S omega ^ 2) =
        variance := by
    simpa only [S, variance, n, q, criticalStepRate] using
      N.cutWalk_secondMoment_of_critical jset hcritical n
  have hfourth :
      integral N.tokenPathMeasure (fun omega => (S omega ^ 2) ^ 2) <=
        4 * variance ^ 2 := by
    calc
      integral N.tokenPathMeasure (fun omega => (S omega ^ 2) ^ 2) =
          integral N.tokenPathMeasure (fun omega => S omega ^ 4) := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun omega => by ring)
      _ <= 3 * variance ^ 2 + variance := by
        simpa only [S, variance, n, q, criticalStepRate] using
          N.cutWalk_fourthMoment_le_of_critical jset hcritical n
      _ <= 4 * variance ^ 2 := by
        have hvone : 1 <= variance := by
          have hKnonneg : 0 <= (K : Real) := Nat.cast_nonneg K
          have hKsq : 1 <= ((K : Real) + 1) ^ 2 := by
            nlinarith
          nlinarith
        nlinarith
  have hSsqMeasurable : Measurable (fun omega => S omega ^ 2) :=
    (N.cutWalk_measurable jset n).pow_const 2
  have hSsqNonneg : forall omega, 0 <= S omega ^ 2 :=
    fun omega => sq_nonneg _
  have hSsqLe : forall omega, S omega ^ 2 <= (n : Real) ^ 2 := by
    intro omega
    have habs := N.cutWalk_abs_le jset n omega
    rw [abs_le] at habs
    nlinarith
  have hpaley : (1 / 16 : Real) <= N.tokenPathMeasure.real A := by
    simpa only [A] using measureReal_gt_half_integral_ge
      N.tokenPathMeasure (fun omega => S omega ^ 2) ((n : Real) ^ 2)
      variance hSsqMeasurable hSsqNonneg hSsqLe (sq_nonneg _)
      hmean hvariancePos hfourth
  have hAsubset : A ⊆ lower ∪ upper := by
    intro omega homega
    by_contra hout
    have hlower : -(K : Real) <= S omega := by
      by_contra h
      exact hout (Or.inl (lt_of_not_ge h))
    have hupper : S omega <= (K : Real) := by
      by_contra h
      exact hout (Or.inr (lt_of_not_ge h))
    have hthreshold :
        ((K : Real) + 1) ^ 2 <= variance / 2 := by
      linarith
    change variance / 2 < S omega ^ 2 at homega
    nlinarith
  have htailEqENN :
      N.tokenPathMeasure lower = N.tokenPathMeasure upper := by
    have hsym :=
      N.cutWalk_identDistrib_neg_of_critical jset hcritical n
    have hmeasure := hsym.measure_mem_eq
      (s := Set.Iio (-(K : Real))) measurableSet_Iio
    change
      N.tokenPathMeasure {omega | S omega < -(K : Real)} =
        N.tokenPathMeasure {omega | -S omega < -(K : Real)}
      at hmeasure
    have hleft : {omega | S omega < -(K : Real)} = lower := rfl
    have hright : {omega | -S omega < -(K : Real)} = upper := by
      ext omega
      change (-S omega < -(K : Real)) ↔ ((K : Real) < S omega)
      constructor <;> intro h <;> linarith
    rw [hleft, hright] at hmeasure
    exact hmeasure
  have htailEq :
      N.tokenPathMeasure.real lower = N.tokenPathMeasure.real upper :=
    congrArg ENNReal.toReal htailEqENN
  have hunion :
      N.tokenPathMeasure.real A <=
        N.tokenPathMeasure.real lower + N.tokenPathMeasure.real upper :=
    (measureReal_mono hAsubset).trans (measureReal_union_le lower upper)
  change (1 / 32 : Real) <= N.tokenPathMeasure.real lower
  rw [← htailEq] at hunion
  linarith

private theorem jobsIn_le_total {K : Nat}
    (x : JobState Buffer K) (s : Finset Buffer) :
    JobState.jobsIn x s <= (K : Real) := by
  unfold JobState.jobsIn
  calc
    s.sum (fun i => (x i : Real)) <=
        Finset.univ.sum (fun i => (x i : Real)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ s
      · intro i _ _
        positivity
    _ = (K : Real) := by
      exact_mod_cast x.total_jobs

/-- For every deterministic stationary policy and every initial queue state,
at least one service opportunity is wasted with probability at least `1/32`
within the critical cut's quadratic event-epoch horizon. -/
theorem finiteHorizon_waste_probability_ge
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) :
    (1 / 32 : Real) <=
      N.tokenPathMeasure.real {omega |
        0 < N.trajectoryWaste U x
          (N.tokenPrefix (N.criticalHorizon jset K) omega)} := by
  let tail : Set N.TokenPath := {omega |
    N.cutWalk jset (N.criticalHorizon jset K) omega < -(K : Real)}
  let waste : Set N.TokenPath := {omega |
    0 < N.trajectoryWaste U x
      (N.tokenPrefix (N.criticalHorizon jset K) omega)}
  have htail :
      (1 / 32 : Real) <= N.tokenPathMeasure.real tail := by
    simpa only [tail] using
      N.cutWalk_lt_neg_probability_ge jset hlimited hcritical K
  have hsubset : tail ⊆ waste := by
    intro omega homega
    apply N.trajectoryWaste_pos_of_primitiveCutSum_lt U x jset
    rw [N.primitiveCutSum_tokenPrefix]
    have hjobs :=
      jobsIn_le_total x (N.neighborhood jset)
    change N.cutWalk jset (N.criticalHorizon jset K) omega <
      -(K : Real) at homega
    linarith
  exact htail.trans (measureReal_mono hsubset)

/-- The joint law of the first `n` IID token coordinates, represented as a
finite vector. -/
noncomputable def tokenVectorLaw (n : Nat) :
    PMF (Fin n ->
      TokenType (Buffer := Buffer) (Server := Server)) :=
  (Measure.pi (fun _ : Fin n => N.tokenLaw.toMeasure)).toPMF

/-- The first `n` coordinates of the canonical token path as a finite
vector. -/
def tokenVector (n : Nat) (omega : N.TokenPath) :
    Fin n -> TokenType (Buffer := Buffer) (Server := Server) :=
  fun r => N.tokenAt r omega

omit [DecidableEq Buffer] [DecidableEq Server] in
theorem tokenVector_hasLaw (n : Nat) :
    HasLaw (N.tokenVector n) (N.tokenVectorLaw n).toMeasure
      N.tokenPathMeasure := by
  have hindep :
      iIndepFun (fun r : Fin n => N.tokenAt r) N.tokenPathMeasure :=
    N.tokenAt_iIndep.precomp Fin.val_injective
  have hlaw :
      forall r : Fin n,
        HasLaw (N.tokenAt r) N.tokenLaw.toMeasure N.tokenPathMeasure :=
    fun r => N.tokenAt_hasLaw r
  have hpi := hindep.hasLaw_pi hlaw
  rw [tokenVectorLaw, Measure.toPMF_toMeasure]
  exact hpi

omit [DecidableEq Buffer] [DecidableEq Server] in
@[simp]
theorem tokenVectorLaw_apply_toReal (n : Nat)
    (tokens : Fin n ->
      TokenType (Buffer := Buffer) (Server := Server)) :
    (N.tokenVectorLaw n tokens).toReal =
      Finset.univ.prod
        (fun r => (N.tokenLaw (tokens r)).toReal) := by
  rw [tokenVectorLaw, Measure.toPMF_apply]
  have hsingleton :
      ({tokens} : Set (Fin n ->
        TokenType (Buffer := Buffer) (Server := Server))) =
        Set.univ.pi (fun r =>
          ({tokens r} :
            Set (TokenType (Buffer := Buffer) (Server := Server)))) := by
    ext candidate
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h
      subst candidate
      exact fun _ => rfl
    · intro h
      funext r
      exact h r
  rw [hsingleton, Measure.pi_pi]
  simp_rw [PMF.toMeasure_apply_singleton N.tokenLaw _
    MeasurableSpace.measurableSet_top]
  rw [ENNReal.toReal_prod]

omit [DecidableEq Buffer] [DecidableEq Server] in
@[simp]
theorem tokenVectorLaw_cons_apply_toReal (n : Nat)
    (jk : TokenType (Buffer := Buffer) (Server := Server))
    (tokens : Fin n ->
      TokenType (Buffer := Buffer) (Server := Server)) :
    (N.tokenVectorLaw (n + 1) (Fin.cons jk tokens)).toReal =
      (N.tokenLaw jk).toReal * (N.tokenVectorLaw n tokens).toReal := by
  rw [N.tokenVectorLaw_apply_toReal, N.tokenVectorLaw_apply_toReal,
    Fin.prod_univ_succ]
  rfl

/-- Expected cumulative waste over a finite IID token vector from one fixed
initial state. -/
noncomputable def expectedTrajectoryWasteFrom {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (n : Nat) : Real :=
  Finset.univ.sum (fun tokens : Fin n ->
      TokenType (Buffer := Buffer) (Server := Server) =>
    (N.tokenVectorLaw n tokens).toReal *
      N.trajectoryWaste U x (List.ofFn tokens))

private theorem expectedTrajectoryWasteFrom_succ {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (n : Nat) :
    N.expectedTrajectoryWasteFrom U x (n + 1) =
      N.oneStepWaste U x +
        Finset.univ.sum (fun jk =>
          (N.tokenLaw jk).toReal *
            N.expectedTrajectoryWasteFrom
              U (N.queueStep U x jk) n) := by
  unfold expectedTrajectoryWasteFrom
  let T := TokenType (Buffer := Buffer) (Server := Server)
  let F : (Fin (n + 1) -> T) -> Real := fun tokens =>
    (N.tokenVectorLaw (n + 1) tokens).toReal *
      N.trajectoryWaste U x (List.ofFn tokens)
  have hsplit :
      Finset.univ.sum F =
        Finset.univ.sum (fun jk : T =>
          Finset.univ.sum (fun tokens : Fin n -> T =>
            F (Fin.cons jk tokens))) := by
    rw [← (Fin.consEquiv
      (fun _ : Fin (n + 1) => T)).sum_comp F]
    rw [Fintype.sum_prod_type]
    rfl
  change Finset.univ.sum F = _
  rw [hsplit]
  simp only [F, N.tokenVectorLaw_cons_apply_toReal, List.ofFn_succ,
    Fin.cons_zero, Fin.cons_succ, trajectoryWaste]
  rw [oneStepWaste]
  simp_rw [mul_add, mul_assoc, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro jk _
    rw [← Finset.mul_sum, ← Finset.sum_mul, PMF.sum_toReal, one_mul]
  · apply Finset.sum_congr rfl
    intro jk _
    rw [← Finset.mul_sum]

/-- Expected cumulative waste when the initial queue state has law `pi`. -/
noncomputable def expectedTrajectoryWaste {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (n : Nat) : Real :=
  Finset.univ.sum (fun x =>
    (pi x).toReal * N.expectedTrajectoryWasteFrom U x n)

private theorem expectedTrajectoryWaste_succ {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (n : Nat) :
    N.expectedTrajectoryWaste U pi (n + 1) =
      N.stationaryOneStepWaste U pi +
        N.expectedTrajectoryWaste
          U (pi.bind (N.transitionPMF U)) n := by
  unfold expectedTrajectoryWaste
  simp_rw [N.expectedTrajectoryWasteFrom_succ U _ n, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [PMF.sum_bind_real]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [transitionPMF, PMF.sum_map_real]

/-- Under an invariant initial queue law, expected block waste is exactly
the block length times stationary one-step waste. -/
theorem expectedTrajectoryWaste_eq_mul_stationary_of_invariant
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (hinvariant : N.IsInvariantPMF U pi)
    (n : Nat) :
    N.expectedTrajectoryWaste U pi n =
      (n : Real) * N.stationaryOneStepWaste U pi := by
  induction n with
  | zero =>
      simp [expectedTrajectoryWaste, expectedTrajectoryWasteFrom,
        trajectoryWaste]
  | succ n ih =>
      rw [N.expectedTrajectoryWaste_succ U pi n, hinvariant, ih]
      push_cast
      ring

private theorem trajectoryWaste_one_le_of_pos {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K)
    (tokens : List
      (TokenType (Buffer := Buffer) (Server := Server)))
    (hpos : 0 < N.trajectoryWaste U x tokens) :
    1 <= N.trajectoryWaste U x tokens := by
  induction tokens generalizing x with
  | nil =>
      simp [trajectoryWaste] at hpos
  | cons jk rest ih =>
      by_cases hwaste : U x jk.1 jk.2 = none
      · simp only [trajectoryWaste, wasteIndicator, if_pos hwaste]
        linarith [N.trajectoryWaste_nonneg
          (U := U) (N.queueStep U x jk) rest]
      · simp only [trajectoryWaste, wasteIndicator, if_neg hwaste,
          zero_add] at hpos ⊢
        exact ih (N.queueStep U x jk) hpos

private theorem waste_probability_le_expectedTrajectoryWasteFrom
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (n : Nat) :
    N.tokenPathMeasure.real {omega |
        0 < N.trajectoryWaste U x (N.tokenPrefix n omega)} <=
      N.expectedTrajectoryWasteFrom U x n := by
  let V : Set (Fin n ->
      TokenType (Buffer := Buffer) (Server := Server)) :=
    {tokens | 0 < N.trajectoryWaste U x (List.ofFn tokens)}
  have hmeasure := (N.tokenVector_hasLaw n).measure_eq
    (p := fun tokens =>
      0 < N.trajectoryWaste U x (List.ofFn tokens))
    MeasurableSet.of_discrete
  have hmeasureReal :
      N.tokenPathMeasure.real {omega |
          0 < N.trajectoryWaste U x (N.tokenPrefix n omega)} =
        (N.tokenVectorLaw n).toMeasure.real V := by
    have hmeasure' :
        N.tokenPathMeasure {omega |
            0 < N.trajectoryWaste U x (N.tokenPrefix n omega)} =
          (N.tokenVectorLaw n).toMeasure V := by
      have hprefix :
          {omega |
              0 < N.trajectoryWaste U x (N.tokenPrefix n omega)} =
            {omega |
              0 < N.trajectoryWaste U x
                (List.ofFn (N.tokenVector n omega))} := by
        rfl
      rw [hprefix]
      simpa only [V] using hmeasure
    exact congrArg ENNReal.toReal hmeasure'
  rw [hmeasureReal]
  calc
    (N.tokenVectorLaw n).toMeasure.real V =
        integral (N.tokenVectorLaw n).toMeasure
          (V.indicator (fun _ => (1 : Real))) :=
      (integral_indicator_one MeasurableSet.of_discrete).symm
    _ = Finset.univ.sum (fun tokens =>
          (N.tokenVectorLaw n tokens).toReal *
            V.indicator (fun _ => (1 : Real)) tokens) := by
      rw [PMF.integral_eq_sum]
      simp only [smul_eq_mul]
    _ <= Finset.univ.sum (fun tokens =>
          (N.tokenVectorLaw n tokens).toReal *
            N.trajectoryWaste U x (List.ofFn tokens)) := by
      apply Finset.sum_le_sum
      intro tokens _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      by_cases hpos :
          0 < N.trajectoryWaste U x (List.ofFn tokens)
      · rw [Set.indicator_of_mem]
        · exact N.trajectoryWaste_one_le_of_pos U x
            (List.ofFn tokens) hpos
        · exact hpos
      · have hnot : tokens ∉ V := hpos
        simp only [Set.indicator, if_neg hnot]
        exact N.trajectoryWaste_nonneg U x (List.ofFn tokens)
    _ = N.expectedTrajectoryWasteFrom U x n := rfl

/-- Averaging the uniform finite-horizon event bound over any initial queue
law gives a uniform lower bound on expected block waste. -/
theorem expectedTrajectoryWaste_ge_one_div_32
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) :
    (1 / 32 : Real) <=
      N.expectedTrajectoryWaste U pi (N.criticalHorizon jset K) := by
  let n := N.criticalHorizon jset K
  have hstate (x : JobState Buffer K) :
      (1 / 32 : Real) <= N.expectedTrajectoryWasteFrom U x n := by
    exact
      (N.finiteHorizon_waste_probability_ge
        jset hlimited hcritical U x).trans
        (N.waste_probability_le_expectedTrajectoryWasteFrom U x n)
  calc
    (1 / 32 : Real) =
        Finset.univ.sum (fun x =>
          (pi x).toReal * (1 / 32 : Real)) := by
      rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]
    _ <= Finset.univ.sum (fun x =>
          (pi x).toReal * N.expectedTrajectoryWasteFrom U x n) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hstate x) ENNReal.toReal_nonneg
    _ = N.expectedTrajectoryWaste U pi n := rfl

private theorem criticalHorizon_pos
    (jset : Finset Server) (hservice : 0 < N.netServiceRate jset)
    (K : Nat) :
    0 < N.criticalHorizon jset K := by
  have hq : 0 < N.criticalStepRate jset := by
    rw [N.criticalStepRate_eq]
    linarith
  have hceil :
      0 < Nat.ceil (2 / N.criticalStepRate jset) :=
    Nat.ceil_pos.mpr (div_pos (by norm_num) hq)
  rw [N.criticalHorizon_eq]
  positivity

/-- Every invariant law has stationary one-step loss at least the uniform
block-event probability divided by the quadratic block length. -/
theorem stationaryOneStepWaste_ge_criticalHorizon
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (hinvariant : N.IsInvariantPMF U pi) :
    (1 / 32 : Real) / (N.criticalHorizon jset K : Real) <=
      N.stationaryOneStepWaste U pi := by
  let n := N.criticalHorizon jset K
  have hnpos : 0 < (n : Real) := by
    exact_mod_cast N.criticalHorizon_pos jset hlimited.2 K
  have hblock :=
    N.expectedTrajectoryWaste_ge_one_div_32
      jset hlimited hcritical U pi
  rw [N.expectedTrajectoryWaste_eq_mul_stationary_of_invariant
    U pi hinvariant n] at hblock
  apply (div_le_iff₀ hnpos).2
  nlinarith

/-- For any policy family and any selected invariant-law witnesses, a
critical limited cut forces stationary loss of order at least `1 / K^2`. -/
theorem stationaryLoss_isOmegaOneDivSq_of_critical_cut
    (U : N.SystemSizePolicyFamily)
    (laws : N.InvariantLawWitnessFamily U)
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset) :
    IsOmegaOneDivSq (N.stationaryLoss U laws) := by
  let factor : Real :=
    (Nat.ceil (2 / N.criticalStepRate jset) : Real)
  have hq : 0 < N.criticalStepRate jset := by
    rw [N.criticalStepRate_eq]
    linarith [hlimited.2]
  have hceilNat :
      0 < Nat.ceil (2 / N.criticalStepRate jset) :=
    Nat.ceil_pos.mpr
      (div_pos (by norm_num : (0 : Real) < 2) hq)
  have hfactor : 0 < factor := by
    dsimp only [factor]
    exact_mod_cast hceilNat
  let c : Real := 1 / (128 * factor)
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  refine ⟨c, hc, Filter.Eventually.of_forall ?_⟩
  intro K
  have hKpos : 0 < (K : Nat) := K.pos
  have hKreal : 0 < (K : Real) := by
    exact_mod_cast hKpos
  have hnpos :
      0 < (N.criticalHorizon jset (K : Nat) : Real) := by
    exact_mod_cast
      N.criticalHorizon_pos jset hlimited.2 (K : Nat)
  have hnupper :=
    N.criticalHorizon_le_four_mul_sq
      jset (K : Nat) hKpos
  have hdivide :
      (1 / 32 : Real) /
          (4 * factor * (K : Real) ^ 2) <=
        (1 / 32 : Real) /
          (N.criticalHorizon jset (K : Nat) : Real) := by
    apply div_le_div_of_nonneg_left
      (by norm_num : (0 : Real) <= 1 / 32) hnpos
    simpa only [factor] using hnupper
  calc
    c / (K : Real) ^ 2 =
        (1 / 32 : Real) / (4 * factor * (K : Real) ^ 2) := by
      dsimp only [c]
      field_simp
      <;> ring
    _ <= (1 / 32 : Real) /
        (N.criticalHorizon jset (K : Nat) : Real) :=
      hdivide
    _ <= N.stationaryLoss U laws K := by
      rw [N.stationaryLoss_eq_stationaryOneStepWaste]
      exact N.stationaryOneStepWaste_ge_criticalHorizon
        jset hlimited hcritical (U K) (laws.law K)
          (laws.isInvariant K)

/-- The initial-law-dependent Cesaro long-run loss obeys the same pointwise
critical-cut lower bound. -/
theorem initialLongRunLoss_ge_criticalHorizon
    (initial : N.InitialLawFamily)
    (U : N.DeterministicPolicySequence)
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset)
    (K : PNat) :
    (1 / 32 : Real) / (N.criticalHorizon jset (K : Nat) : Real) <=
      N.initialLongRunLoss U initial K := by
  rw [N.initialLongRunLoss_eq_stationaryOneStepWaste]
  exact N.stationaryOneStepWaste_ge_criticalHorizon
    jset hlimited hcritical (U K)
      (N.initialCesaroLimitLaw U initial K)
      (N.initialCesaroLimitLaw_isInvariant U initial K)

/-- Every explicit initial-law family has critical-cut long-run loss of order
at least `1 / K^2`. -/
theorem initialLongRunLoss_isOmegaOneDivSq_of_critical_cut
    (initial : N.InitialLawFamily)
    (U : N.DeterministicPolicySequence)
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset) :
    IsOmegaOneDivSq (N.initialLongRunLoss U initial) := by
  let laws : N.InvariantLawWitnessFamily U :=
    { law := fun K => N.initialCesaroLimitLaw U initial K
      isInvariant := fun K =>
        N.initialCesaroLimitLaw_isInvariant U initial K }
  change IsOmegaOneDivSq (N.stationaryLoss U laws)
  exact N.stationaryLoss_isOmegaOneDivSq_of_critical_cut
    U laws jset hlimited hcritical

/-- The critical-cut initial-law long-run loss has zero exponential decay
rate under the concrete event-epoch semantics. -/
theorem initialThroughputLossExponent_eq_zero_of_critical_cut
    (initial : N.InitialLawFamily)
    (U : N.DeterministicPolicySequence)
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset) :
    initial.toPerformanceSemantics.throughputLossExponent U = 0 := by
  exact
    initial.toPerformanceSemantics
      |>.throughputLossExponent_eq_zero_of_isOmegaOneDivSq U
        (N.initialLongRunLoss_isOmegaOneDivSq_of_critical_cut
          initial U jset hlimited hcritical)

end Network

namespace ConcretePerformance

variable {N : Network Buffer Server}

/-- Critical Hall equality forces polynomially large loss for every concrete
stationary finite-chain performance selection. -/
theorem loss_isOmegaOneDivSq_of_critical_cut
    (P : ConcretePerformance N) (U : N.SystemSizePolicyFamily)
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset) :
    IsOmegaOneDivSq (P.loss U) := by
  change IsOmegaOneDivSq
    (N.stationaryLoss U (P.invariantLaws U))
  exact N.stationaryLoss_isOmegaOneDivSq_of_critical_cut
    U (P.invariantLaws U) jset hlimited hcritical

/-- Critical Hall equality gives zero throughput-loss exponent under the
concrete stationary event-epoch semantics. -/
theorem throughputLossExponent_eq_zero_of_critical_cut
    (P : ConcretePerformance N) (U : N.SystemSizePolicyFamily)
    (jset : Finset Server) (hlimited : N.IsLimitedSet jset)
    (hcritical :
      N.netArrivalRate jset = N.netServiceRate jset) :
    P.toPerformanceSemantics.throughputLossExponent U = 0 := by
  exact
    P.toPerformanceSemantics
      |>.throughputLossExponent_eq_zero_of_isOmegaOneDivSq U
        (P.loss_isOmegaOneDivSq_of_critical_cut
          U jset hlimited hcritical)

end ConcretePerformance

end StateDepMOR
