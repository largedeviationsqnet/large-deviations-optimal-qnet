import StateDepMOR.PoissonRateProofs
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Basic

/-!
# Finite-dimensional large deviations for Poisson token counts

This file constructs the independent finite product law of the marked
Poisson token counts over a fixed horizon.  It also proves the local
logarithmic asymptotic of its atoms.  The path-space exponential-tightness
and open/closed-set bounds needed for a sample-path LDP are deliberately
outside the scope of this finite-dimensional module.
-/

open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]

/-- The Poisson parameter accumulated by one token type over horizon `T`
at system size `K`.  `NNReal.ofReal` makes this definition meaningful even
before a network's nonnegativity proof is supplied. -/
noncomputable def scaledPoissonParameter
    (K : Nat) (T : NNReal) (nominal : Real) : NNReal :=
  (K : NNReal) * T * Real.toNNReal nominal

/-- Independent counts for all token types `(j,k)` at system size `K`.

The outer and inner `Measure.pi` are finite products.  Thus the coordinate
maps are independent by construction, including coordinates whose nominal
Poisson parameter is zero. -/
noncomputable def poissonCountLaw
    (N : Network Buffer Server) (K : Nat) (T : NNReal) :
    Measure (Server -> Buffer -> Nat) :=
  Measure.pi fun j =>
    Measure.pi fun k =>
      ProbabilityTheory.poissonMeasure
        (scaledPoissonParameter K T (N.phi j k))

/-- Coordinatewise division of a count array by the system size. -/
noncomputable def scaledCountArray
    (K : Nat) (n : Server -> Buffer -> Nat) :
    Server -> Buffer -> Real :=
  fun j k => (n j k : Real) / K

/-- Law of the coordinatewise scaled count array. -/
noncomputable def poissonScaledCountLaw
    (N : Network Buffer Server) (K : Nat) (T : NNReal) :
    Measure (Server -> Buffer -> Real) :=
  (poissonCountLaw N K T).map (scaledCountArray K)

instance poissonCountLaw_isProbabilityMeasure
    (N : Network Buffer Server) (K : Nat) (T : NNReal) :
    IsProbabilityMeasure (poissonCountLaw N K T) := by
  unfold poissonCountLaw
  infer_instance

instance poissonScaledCountLaw_isProbabilityMeasure
    (N : Network Buffer Server) (K : Nat) (T : NNReal) :
    IsProbabilityMeasure (poissonScaledCountLaw N K T) := by
  unfold poissonScaledCountLaw
  exact Measure.isProbabilityMeasure_map
    (Measurable.aemeasurable (by fun_prop))

/-- Exact atom formula for the finite independent product law. -/
theorem poissonCountLaw_singleton
    (N : Network Buffer Server) (K : Nat) (T : NNReal)
    (n : Server -> Buffer -> Nat) :
    poissonCountLaw N K T {n} =
      ∏ j, ∏ k,
        ENNReal.ofReal
          (Real.exp
            (-(scaledPoissonParameter K T (N.phi j k) : Real)) *
            (scaledPoissonParameter K T (N.phi j k) : Real) ^ n j k /
            Nat.factorial (n j k)) := by
  simp only [poissonCountLaw, Measure.pi_singleton,
    ProbabilityTheory.poissonMeasure_singleton]

/-- Exact mass of an atom of the scaled law.  Positivity of `K` makes
coordinatewise scaling injective on integer count arrays. -/
theorem poissonScaledCountLaw_singleton
    (N : Network Buffer Server) (K : Nat) (T : NNReal)
    (n : Server -> Buffer -> Nat) (hK : 0 < K) :
    poissonScaledCountLaw N K T {scaledCountArray K n} =
      ∏ j, ∏ k,
        ENNReal.ofReal
          (Real.exp
              (-(scaledPoissonParameter K T (N.phi j k) : Real)) *
            (scaledPoissonParameter K T (N.phi j k) : Real) ^ n j k /
            Nat.factorial (n j k)) := by
  classical
  have hscale_injective : Function.Injective
      (scaledCountArray K :
        (Server -> Buffer -> Nat) -> (Server -> Buffer -> Real)) := by
    intro m n hmn
    funext j k
    have hcoord := congrFun (congrFun hmn j) k
    unfold scaledCountArray at hcoord
    have hKreal : Not ((K : Real) = 0) := by exact_mod_cast hK.ne'
    have hcast : (m j k : Real) = n j k :=
      (div_left_inj' hKreal).mp hcoord
    exact_mod_cast hcast
  have hpreimage :
      scaledCountArray K ⁻¹' {scaledCountArray K n} = {n} := by
    ext m
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact hscale_injective.eq_iff
  rw [poissonScaledCountLaw,
    Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    hpreimage, poissonCountLaw_singleton]

/-- Each coordinate projection has the intended Poisson marginal. -/
theorem poissonCountLaw_coordinate_marginal
    (N : Network Buffer Server) (K : Nat) (T : NNReal)
    (j : Server) (k : Buffer) :
    (poissonCountLaw N K T).map (fun n => n j k) =
      ProbabilityTheory.poissonMeasure
        (scaledPoissonParameter K T (N.phi j k)) := by
  classical
  unfold poissonCountLaw
  change
    Measure.map ((fun m : Buffer -> Nat => m k) ∘
        (fun m : Server -> Buffer -> Nat => m j))
        (Measure.pi fun q =>
          Measure.pi fun r =>
            ProbabilityTheory.poissonMeasure
              (scaledPoissonParameter K T (N.phi q r))) = _
  rw [← Measure.map_map]
  · change
      Measure.map (Function.eval k)
          (Measure.map (Function.eval j)
            (Measure.pi fun q =>
              Measure.pi fun r =>
                ProbabilityTheory.poissonMeasure
                  (scaledPoissonParameter K T (N.phi q r)))) = _
    rw [Measure.pi_map_eval]
    simp only [measure_univ, Finset.prod_const_one, one_smul]
    rw [Measure.pi_map_eval]
    simp
  · fun_prop
  · fun_prop

/-- The complete family of coordinate projections is mutually independent. -/
theorem poissonCountLaw_coordinate_independent
    (N : Network Buffer Server) (K : Nat) (T : NNReal) :
    ProbabilityTheory.iIndepFun
      (fun p : Sigma (fun _ : Server => Buffer) =>
        fun n : Server -> Buffer -> Nat => n p.1 p.2)
      (poissonCountLaw N K T) := by
  classical
  unfold poissonCountLaw
  refine ProbabilityTheory.iIndepFun_uncurry
    (P := Measure.pi fun q : Server =>
      Measure.pi fun r : Buffer =>
        ProbabilityTheory.poissonMeasure
          (scaledPoissonParameter K T (N.phi q r)))
    (X := fun j k n => n j k) (by fun_prop) ?_ ?_
  · exact ProbabilityTheory.iIndepFun_pi
      (X := fun _ (m : Buffer -> Nat) => m)
      fun _ => Measurable.aemeasurable (by fun_prop)
  · intro j
    rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun _ => Measurable.aemeasurable (by fun_prop))]
    have hleft :
        Measure.map (fun n : Server -> Buffer -> Nat => n j)
            (Measure.pi fun q : Server =>
              Measure.pi fun r : Buffer =>
                ProbabilityTheory.poissonMeasure
                  (scaledPoissonParameter K T (N.phi q r))) =
          Measure.pi fun r : Buffer =>
            ProbabilityTheory.poissonMeasure
              (scaledPoissonParameter K T (N.phi j r)) := by
      rw [Measure.pi_map_eval]
      simp
    rw [hleft]
    congr 1
    funext k
    simpa only [poissonCountLaw] using
      (poissonCountLaw_coordinate_marginal N K T j k).symm

/-- The coordinatewise scaled counts remain mutually independent under the
underlying product law.  Their joint distribution is
`poissonScaledCountLaw`. -/
theorem poissonCountLaw_scaled_coordinate_independent
    (N : Network Buffer Server) (K : Nat) (T : NNReal) :
    ProbabilityTheory.iIndepFun
      (fun p : Sigma (fun _ : Server => Buffer) =>
        fun n : Server -> Buffer -> Nat => (n p.1 p.2 : Real) / K)
      (poissonCountLaw N K T) := by
  exact (poissonCountLaw_coordinate_independent N K T).comp
    (fun (_ : Sigma (fun _ : Server => Buffer)) (m : Nat) =>
      (m : Real) / K)
    (fun _ => by fun_prop)

/-- The real scalar appearing in one coordinate of the exact atom formula. -/
noncomputable def poissonAtomReal
    (K : Nat) (T nominal : Real) (n : Nat) : Real :=
  Real.exp (-((K : Real) * T * nominal)) *
    ((K : Real) * T * nominal) ^ n / Nat.factorial n

/-- The real product atom formula, useful when all forbidden zero-rate
coordinates carry count zero. -/
noncomputable def poissonCountAtomReal
    (N : Network Buffer Server) (K : Nat) (T : Real)
    (n : Server -> Buffer -> Nat) : Real :=
  ∏ j, ∏ k, poissonAtomReal K T (N.phi j k) (n j k)

/-- Real-valued version of the exact atom formula. -/
theorem poissonCountLaw_real_singleton
    (N : Network Buffer Server) (K : Nat) (T : NNReal)
    (n : Server -> Buffer -> Nat) :
    (poissonCountLaw N K T).real {n} =
      poissonCountAtomReal N K (T : Real) n := by
  classical
  rw [measureReal_def, poissonCountLaw_singleton]
  simp only [ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro j hj
  apply Finset.prod_congr rfl
  intro k hk
  rw [ENNReal.toReal_ofReal (by positivity)]
  unfold poissonAtomReal scaledPoissonParameter
  simp only [NNReal.coe_mul, NNReal.coe_natCast]
  rw [Real.coe_toNNReal _ (N.phi_nonneg j k)]

/-- The sublinear logarithmic error in Stirling's formula. -/
noncomputable def stirlingLogError (n : Nat) : Real :=
  Real.log (Nat.factorial n : Real) -
    (n : Real) * Real.log (n : Real) + n

@[simp]
theorem stirlingLogError_zero : stirlingLogError 0 = 0 := by
  simp [stirlingLogError]

theorem stirlingLogError_eq (n : Nat) (hn : Not (n = 0)) :
    stirlingLogError n =
      Real.log (Stirling.stirlingSeq n) +
        Real.log (2 * (n : Real)) / 2 := by
  have hnpos : (0 : Real) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hlog :
      Real.log ((n : Real) / Real.exp 1) =
        Real.log (n : Real) - 1 := by
    rw [Real.log_div (ne_of_gt hnpos) (Real.exp_ne_zero 1), Real.log_exp]
  rw [stirlingLogError, Stirling.log_stirlingSeq_formula n, hlog]
  ring

theorem stirlingLogError_nonneg (n : Nat) :
    0 <= stirlingLogError n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [stirlingLogError_eq n hn]
  have hpi : (1 : Real) <= Real.sqrt Real.pi := by
    rw [Real.one_le_sqrt]
    linarith [Real.pi_gt_three]
  have hseq : 1 <= Stirling.stirlingSeq n :=
    hpi.trans (Stirling.sqrt_pi_le_stirlingSeq hn)
  have hlogseq : 0 <= Real.log (Stirling.stirlingSeq n) :=
    Real.log_nonneg hseq
  have hlogn : 0 <= Real.log (2 * (n : Real)) := by
    apply Real.log_nonneg
    have hn_one : (1 : Real) <= n := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    linarith
  positivity

theorem stirlingLogError_le (n : Nat) :
    stirlingLogError n <=
      Real.log (Stirling.stirlingSeq 1) +
        Real.log (2 * (n : Real)) / 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Stirling.stirlingSeq_one]
    have : (0 : Real) <= Real.log (Real.exp 1 / Real.sqrt 2) := by
      apply Real.log_nonneg
      rw [one_le_div (by positivity), Real.sqrt_le_left (by positivity)]
      nlinarith [Real.add_one_le_exp 1]
    exact this
  rw [stirlingLogError_eq n hn]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact add_le_add
    (Real.log_le_log (Stirling.stirlingSeq'_pos m)
      (Stirling.stirlingSeq'_antitone (Nat.zero_le m))) le_rfl

/-- Stirling's logarithmic error is `o(K)` along every count sequence whose
count divided by `K` has a finite limit. -/
theorem stirlingLogError_div_tendsto_zero
    (n : Nat -> Nat) (x : Real)
    (h : Tendsto (fun K => (n K : Real) / K) atTop (nhds x)) :
    Tendsto (fun K => stirlingLogError (n K) / (K : Real))
      atTop (nhds 0) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (abs x + 1)
  have hxM : x < (M : Real) := by
    exact lt_trans (lt_add_of_le_of_pos (le_abs_self x) zero_lt_one) hM
  have hratio :
      Filter.Eventually (fun K => (n K : Real) / K < (M : Real)) atTop :=
    h.eventually_lt_const hxM
  have hK : Filter.Eventually (fun K : Nat => 0 < K) atTop :=
    eventually_atTop.2 ⟨1, fun K hK => Nat.zero_lt_of_lt hK⟩
  have hcount :
      Filter.Eventually (fun K => (n K : Real) < (M : Real) * K) atTop := by
    filter_upwards [hratio, hK] with K hratioK hKpos
    exact (div_lt_iff₀ (by exact_mod_cast hKpos)).1 hratioK
  let C := Real.log (Stirling.stirlingSeq 1)
  let upper : Nat -> Real := fun K =>
    (C + Real.log ((2 * M : Nat) : Real) / 2) / K +
      (Real.log (K : Real) / K) / 2
  have hlogdiv :
      Tendsto (fun K : Nat => Real.log (K : Real) / K)
        atTop (nhds 0) := by
    simpa only [Function.comp_apply, id_eq] using
      (Real.isLittleO_log_id_atTop.comp_tendsto
        (tendsto_natCast_atTop_atTop (R := Real))).tendsto_div_nhds_zero
  have hupper : Tendsto upper atTop (nhds 0) := by
    dsimp [upper]
    convert
      (tendsto_const_div_atTop_nhds_zero_nat
        (C + Real.log ((2 * M : Nat) : Real) / 2)).add
        (hlogdiv.div_const 2) using 1 <;> simp
  apply squeeze_zero'
  · filter_upwards [hK] with K hKpos
    exact div_nonneg (stirlingLogError_nonneg (n K))
      (by exact_mod_cast hKpos.le)
  · filter_upwards [hK, hcount] with K hKpos hcountK
    have hMpos : 0 < M := by
      have : (0 : Real) < M := lt_trans (by positivity : 0 < abs x + 1) hM
      exact_mod_cast this
    have hKMpos : (0 : Real) < (2 * M : Nat) * K := by
      positivity
    have hlogbound :
        Real.log (2 * (n K : Real)) <=
          Real.log (((2 * M : Nat) * K : Nat) : Real) := by
      by_cases hnK : n K = 0
      · simp [hnK]
        exact Real.log_nonneg (by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (by decide) hMpos) hKpos)))
      · apply Real.log_le_log
          (mul_pos (by norm_num) (by exact_mod_cast Nat.pos_of_ne_zero hnK))
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        linarith
    have herr :=
      stirlingLogError_le (n K)
    have hdiv :
        stirlingLogError (n K) / (K : Real) <=
          (C + Real.log (((2 * M : Nat) * K : Nat) : Real) / 2) /
            (K : Real) := by
      apply div_le_div_of_nonneg_right
      · dsimp [C]
        linarith
      · exact_mod_cast hKpos.le
    calc
      stirlingLogError (n K) / (K : Real) <=
          (C + Real.log (((2 * M : Nat) * K : Nat) : Real) / 2) /
            (K : Real) := hdiv
      _ = upper K := by
        dsimp [upper, C]
        rw [Nat.cast_mul, Real.log_mul]
        · ring
        · exact_mod_cast Nat.ne_of_gt (Nat.mul_pos (by decide) hMpos)
        · exact_mod_cast Nat.ne_of_gt hKpos
  · exact hupper

theorem continuous_poissonCostReal_right {nominal : Real}
    (hnominal : 0 < nominal) :
    Continuous (poissonCostReal nominal) := by
  have hformula :
      poissonCostReal nominal =
        fun candidate =>
          candidate * Real.log candidate -
            candidate * Real.log nominal - candidate + nominal := by
    funext candidate
    rcases eq_or_ne candidate 0 with rfl | hcandidate
    · simp [poissonCostReal, hnominal.ne']
    · rw [poissonCostReal, Real.log_div hcandidate hnominal.ne']
      ring
  rw [hformula]
  fun_prop

theorem poissonCostReal_scale
    (T nominal candidate : Real) (hT : 0 < T) (hnominal : 0 < nominal) :
    poissonCostReal (T * nominal) (T * candidate) =
      T * poissonCostReal nominal candidate := by
  rw [poissonCostReal, poissonCostReal]
  have hratio : (T * candidate) / (T * nominal) = candidate / nominal := by
    field_simp
  rw [hratio]
  ring

theorem poissonAtomReal_pos
    (K n : Nat) (T nominal : Real)
    (hK : 0 < K) (hT : 0 < T) (hnominal : 0 < nominal) :
    0 < poissonAtomReal K T nominal n := by
  unfold poissonAtomReal
  positivity

/-- Exact decomposition of a positive-rate Poisson atom into its entropy
cost and the Stirling error. -/
theorem neg_log_poissonAtomReal_eq
    (K n : Nat) (T nominal : Real)
    (hK : 0 < K) (hT : 0 < T) (hnominal : 0 < nominal) :
    -Real.log (poissonAtomReal K T nominal n) / (K : Real) =
      poissonCostReal (T * nominal) ((n : Real) / K) +
        stirlingLogError n / K := by
  have hKreal : (0 : Real) < K := by exact_mod_cast hK
  have hrate : (0 : Real) < (K : Real) * T * nominal := by positivity
  rcases eq_or_ne n 0 with rfl | hn
  · simp [poissonAtomReal, poissonCostReal, stirlingLogError,
      Real.log_exp, hKreal.ne', hT.ne', hnominal.ne']
    field_simp
  have hnreal : (0 : Real) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hfac : (0 : Real) < (Nat.factorial n : Real) := by positivity
  have hlograte :
      Real.log ((K : Real) * T * nominal) =
        Real.log (K : Real) + Real.log (T * nominal) := by
    rw [show (K : Real) * T * nominal = (K : Real) * (T * nominal) by ring,
      Real.log_mul hKreal.ne' (mul_ne_zero hT.ne' hnominal.ne')]
  have hlogscaled :
      Real.log ((n : Real) / K) =
        Real.log (n : Real) - Real.log (K : Real) := by
    rw [Real.log_div hnreal.ne' hKreal.ne']
  rw [poissonAtomReal, Real.log_div
    (mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero _ hrate.ne'))
    (ne_of_gt hfac)]
  rw [Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hrate.ne'),
    Real.log_exp, Real.log_pow, hlograte]
  rw [poissonCostReal,
    Real.log_div (div_ne_zero hnreal.ne' hKreal.ne')
      (mul_ne_zero hT.ne' hnominal.ne'),
    hlogscaled]
  unfold stirlingLogError
  field_simp
  ring

/-- One-coordinate local logarithmic asymptotic for a strictly positive
nominal rate.  The candidate rate may be zero. -/
theorem poissonAtomReal_log_asymptotic
    (T nominal candidate : Real) (hT : 0 < T)
    (hnominal : 0 < nominal)
    (n : Nat -> Nat)
    (hn : Tendsto (fun K => (n K : Real) / K)
      atTop (nhds (T * candidate))) :
    Tendsto
      (fun K =>
        -Real.log (poissonAtomReal K T nominal (n K)) / (K : Real))
      atTop (nhds (T * poissonCostReal nominal candidate)) := by
  have hcost :
      Tendsto
        (fun K => poissonCostReal (T * nominal) ((n K : Real) / K))
        atTop
        (nhds (poissonCostReal (T * nominal) (T * candidate))) :=
    ((continuous_poissonCostReal_right (mul_pos hT hnominal)).tendsto
      (T * candidate)).comp hn
  have herror :=
    stirlingLogError_div_tendsto_zero n (T * candidate) hn
  have hsum := hcost.add herror
  rw [poissonCostReal_scale T nominal candidate hT hnominal] at hsum
  simpa only [add_zero] using hsum.congr' (by
    filter_upwards [eventually_atTop.2 ⟨1, fun K hK => hK⟩] with K hK
    exact (neg_log_poissonAtomReal_eq K (n K) T nominal
      (Nat.zero_lt_of_lt hK) hT hnominal).symm)

/-- One-coordinate asymptotic allowing a zero nominal rate.  A zero-rate
Poisson variable is supported at zero, so finite logarithmic cost requires
the count sequence to remain identically zero. -/
theorem poissonAtomReal_log_asymptotic_nonneg
    (T nominal candidate : Real) (hT : 0 < T)
    (hnominal : 0 <= nominal)
    (n : Nat -> Nat)
    (hzero : nominal = 0 -> forall K, n K = 0)
    (hn : Tendsto (fun K => (n K : Real) / K)
      atTop (nhds (T * candidate))) :
    Tendsto
      (fun K =>
        -Real.log (poissonAtomReal K T nominal (n K)) / (K : Real))
      atTop (nhds (T * poissonCostReal nominal candidate)) := by
  rcases hnominal.eq_or_lt with hnominal_zero | hnominal_pos
  · have hnzero : forall K, n K = 0 := hzero hnominal_zero.symm
    have hzero_limit :
        Tendsto (fun K => (n K : Real) / K) atTop (nhds 0) := by
      simpa only [hnzero, Nat.cast_zero, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : Real))
          atTop (nhds 0))
    have hcandidate_scaled : T * candidate = 0 :=
      tendsto_nhds_unique hn hzero_limit
    have hcandidate : candidate = 0 := by
      exact (mul_eq_zero.mp hcandidate_scaled).resolve_left hT.ne'
    subst candidate
    subst nominal
    simpa [poissonAtomReal, poissonCostReal, hnzero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (0 : Real))
        atTop (nhds 0))
  · exact poissonAtomReal_log_asymptotic
      T nominal candidate hT hnominal_pos n hn

/-- Finite-coordinate logarithmic atom asymptotic with zero nominal rates.
The support condition is necessary and exact: every zero-rate coordinate
must carry count zero at every system size. -/
theorem poissonCountAtomReal_log_asymptotic
    (N : Network Buffer Server) (T : Real) (hT : 0 < T)
    (f : Server -> Buffer -> Real)
    (n : Nat -> Server -> Buffer -> Nat)
    (hzero : forall j k, N.phi j k = 0 -> forall K, n K j k = 0)
    (hn : forall j k,
      Tendsto (fun K => (n K j k : Real) / K)
        atTop (nhds (T * f j k))) :
    Tendsto
      (fun K =>
        -Real.log (poissonCountAtomReal N K T (n K)) / (K : Real))
      atTop
      (nhds (T * ∑ j, ∑ k, poissonCostReal (N.phi j k) (f j k))) := by
  classical
  have hinner (j : Server) :
      Tendsto
        (fun K => ∑ k,
          -Real.log (poissonAtomReal K T (N.phi j k) (n K j k)) /
            (K : Real))
        atTop
        (nhds (∑ k, T * poissonCostReal (N.phi j k) (f j k))) := by
    apply tendsto_finset_sum Finset.univ
    intro k hk
    exact poissonAtomReal_log_asymptotic_nonneg T (N.phi j k) (f j k)
      hT (N.phi_nonneg j k) (fun K => n K j k)
      (hzero j k) (hn j k)
  have hsum :
      Tendsto
        (fun K => ∑ j, ∑ k,
          -Real.log (poissonAtomReal K T (N.phi j k) (n K j k)) /
            (K : Real))
        atTop
        (nhds (∑ j, ∑ k,
          T * poissonCostReal (N.phi j k) (f j k))) := by
    apply tendsto_finset_sum Finset.univ
    intro j hj
    exact hinner j
  have htarget :
      (∑ j, ∑ k, T * poissonCostReal (N.phi j k) (f j k)) =
        T * ∑ j, ∑ k, poissonCostReal (N.phi j k) (f j k) := by
    simp only [Finset.mul_sum]
  rw [htarget] at hsum
  apply hsum.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun K hK => hK⟩] with K hK
  have hKpos : 0 < K := Nat.zero_lt_of_lt hK
  have hatom (j : Server) (k : Buffer) :
      0 < poissonAtomReal K T (N.phi j k) (n K j k) :=
    by
      rcases (N.phi_nonneg j k).eq_or_lt with hphi_zero | hphi_pos
      · have hnzero := hzero j k hphi_zero.symm K
        rw [← hphi_zero, hnzero]
        simp [poissonAtomReal]
      · exact poissonAtomReal_pos K (n K j k) T (N.phi j k)
          hKpos hT hphi_pos
  rw [poissonCountAtomReal]
  rw [Real.log_prod (fun j hj => Finset.prod_ne_zero_iff.mpr
    (fun k hk => (hatom j k).ne'))]
  simp_rw [Real.log_prod (fun k hk => (hatom _ k).ne')]
  simp only [div_eq_mul_inv, Finset.sum_mul, Finset.sum_neg_distrib,
    neg_mul]

/-- The preceding asymptotic stated directly for the singleton mass of the
independent product law. -/
theorem poissonCountLaw_log_asymptotic_of_phi_pos
    (N : Network Buffer Server) (T : NNReal) (hT : 0 < T)
    (hphi : forall j k, 0 < N.phi j k)
    (f : Server -> Buffer -> Real)
    (n : Nat -> Server -> Buffer -> Nat)
    (hn : forall j k,
      Tendsto (fun K => (n K j k : Real) / K)
        atTop (nhds ((T : Real) * f j k))) :
    Tendsto
      (fun K =>
        -Real.log ((poissonCountLaw N K T).real {n K}) / (K : Real))
      atTop
      (nhds ((T : Real) *
        ∑ j, ∑ k, poissonCostReal (N.phi j k) (f j k))) := by
  simpa only [poissonCountLaw_real_singleton] using
    poissonCountAtomReal_log_asymptotic N (T : Real)
      (by exact_mod_cast hT) f n
      (fun j k hzero K => False.elim ((hphi j k).ne' hzero))
      hn

/-- Product-law asymptotic with arbitrary nonnegative nominal rates and the
exact support condition on zero-rate coordinates. -/
theorem poissonCountLaw_log_asymptotic
    (N : Network Buffer Server) (T : NNReal) (hT : 0 < T)
    (f : Server -> Buffer -> Real)
    (n : Nat -> Server -> Buffer -> Nat)
    (hzero : forall j k, N.phi j k = 0 -> forall K, n K j k = 0)
    (hn : forall j k,
      Tendsto (fun K => (n K j k : Real) / K)
        atTop (nhds ((T : Real) * f j k))) :
    Tendsto
      (fun K =>
        -Real.log ((poissonCountLaw N K T).real {n K}) / (K : Real))
      atTop
      (nhds ((T : Real) *
        ∑ j, ∑ k, poissonCostReal (N.phi j k) (f j k))) := by
  simpa only [poissonCountLaw_real_singleton] using
    poissonCountAtomReal_log_asymptotic N (T : Real)
      (by exact_mod_cast hT) f n hzero hn

/-- Extended-real negative scaled log mass.  This records zero-probability
atoms as `top`, unlike `Real.log 0`. -/
noncomputable def poissonCountSingletonCost
    (N : Network Buffer Server) (K : Nat) (T : NNReal)
    (n : Server -> Buffer -> Nat) : EReal :=
  -ENNReal.log (poissonCountLaw N K T {n}) / (K : EReal)

theorem poissonCountLaw_singleton_eq_zero_of_zero_rate
    (N : Network Buffer Server) (K : Nat) (T : NNReal)
    (n : Server -> Buffer -> Nat)
    (j : Server) (k : Buffer)
    (hphi : N.phi j k = 0) (hn : 0 < n j k) :
    poissonCountLaw N K T {n} = 0 := by
  classical
  rw [poissonCountLaw_singleton]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [scaledPoissonParameter, hphi, Nat.ne_of_gt hn]

/-- If a zero-nominal token coordinate has a positive limiting candidate
rate, every sufficiently large singleton has zero mass and hence infinite
extended-real scaled log cost. -/
theorem poissonCountSingletonCost_eventually_top_of_zero_rate
    (N : Network Buffer Server) (T : NNReal) (hT : 0 < T)
    (f : Server -> Buffer -> Real)
    (n : Nat -> Server -> Buffer -> Nat)
    (j : Server) (k : Buffer)
    (hphi : N.phi j k = 0) (hf : 0 < f j k)
    (hn : Tendsto (fun K => (n K j k : Real) / K)
      atTop (nhds ((T : Real) * f j k))) :
    Filter.Eventually
      (fun K => poissonCountSingletonCost N K T (n K) = (⊤ : EReal))
      atTop := by
  have hlimit : 0 < (T : Real) * f j k := by
    exact mul_pos (by exact_mod_cast hT) hf
  have hratio :
      Filter.Eventually (fun K => 0 < (n K j k : Real) / K) atTop :=
    hn.eventually_const_lt hlimit
  have hK : Filter.Eventually (fun K : Nat => 0 < K) atTop :=
    eventually_atTop.2 ⟨1, fun K hK => Nat.zero_lt_of_lt hK⟩
  filter_upwards [hratio, hK] with K hratioK hKpos
  have hnreal : (0 : Real) < n K j k := by
    rcases (div_pos_iff.mp hratioK) with hpos | hneg
    · exact hpos.1
    · exact False.elim (not_lt_of_ge (by positivity : (0 : Real) <= K) hneg.2)
  have hnpos : 0 < n K j k := by exact_mod_cast hnreal
  rw [poissonCountSingletonCost,
    poissonCountLaw_singleton_eq_zero_of_zero_rate
      N K T (n K) j k hphi hnpos,
    ENNReal.log_zero, EReal.neg_bot]
  exact EReal.top_div_of_pos_ne_top
    (Nat.cast_pos'.2 hKpos) (EReal.natCast_ne_top K)

theorem poissonCountSingletonCost_tendsto_top_of_zero_rate
    (N : Network Buffer Server) (T : NNReal) (hT : 0 < T)
    (f : Server -> Buffer -> Real)
    (n : Nat -> Server -> Buffer -> Nat)
    (j : Server) (k : Buffer)
    (hphi : N.phi j k = 0) (hf : 0 < f j k)
    (hn : Tendsto (fun K => (n K j k : Real) / K)
      atTop (nhds ((T : Real) * f j k))) :
    Tendsto (fun K => poissonCountSingletonCost N K T (n K))
      atTop (nhds (⊤ : EReal)) := by
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  exact (poissonCountSingletonCost_eventually_top_of_zero_rate
    N T hT f n j k hphi hf hn).mono fun K hK => hK.symm

end StateDepMOR
