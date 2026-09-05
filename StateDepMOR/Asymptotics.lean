import StateDepMOR.Policy
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary asymptotics for throughput-loss exponents

This file proves the elementary implications used in Proposition
`prop:state_ind_no_exp`: a probability sequence bounded below by a positive
multiple of `K⁻²`, or with strictly positive liminf, has zero
`-limsup K⁻¹ log` exponent.  The same convergence also gives the stronger
`-liminf K⁻¹ log` rate used by the converse statements.
-/

open Filter
open scoped Topology

namespace StateDepMOR

/-- Positive integers, coerced to reals, tend to `+∞`. -/
theorem tendsto_pnatCast_atTop :
    Tendsto (fun K : ℕ+ => (((K : ℕ) : ℝ))) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop

/-- Reindexing a sequence on positive naturals by `n + 1` preserves its
`limsup`. -/
theorem limsup_comp_succPNat
    {alpha : Type*} [ConditionallyCompleteLattice alpha]
    (u : PNat -> alpha) :
    limsup (fun n : Nat => u n.succPNat) atTop = limsup u atTop := by
  change limsup (u ∘ OrderIso.pnatIsoNat.symm) atTop = limsup u atTop
  rw [limsup_comp, OrderIso.map_atTop]

/-- Reindexing a sequence on positive naturals by `n + 1` preserves its
`liminf`. -/
theorem liminf_comp_succPNat
    {alpha : Type*} [ConditionallyCompleteLattice alpha]
    (u : PNat -> alpha) :
    liminf (fun n : Nat => u n.succPNat) atTop = liminf u atTop := by
  change liminf (u ∘ OrderIso.pnatIsoNat.symm) atTop = liminf u atTop
  rw [liminf_comp, OrderIso.map_atTop]

/-- The elementary logarithmic rate `log K / K` vanishes along positive
integers. -/
theorem tendsto_log_pnat_div :
    Tendsto (fun K : ℕ+ => Real.log (((K : ℕ) : ℝ)) / (((K : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  change Tendsto
    ((fun x : ℝ => Real.log x / x) ∘ fun K : ℕ+ => (((K : ℕ) : ℝ)))
    atTop (𝓝 0)
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_pnatCast_atTop

/-- A polynomial lower bound squeezes the ordinary real logarithmic rate to
zero.  The positivity conclusion is kept explicit because it is what makes
the later `EReal` readback preserve `log 0 = -∞`. -/
theorem tendsto_real_log_rate_of_isOmegaOneDivSq
    (loss : ℕ+ → ℝ) (hloss_nonneg : ∀ K, 0 ≤ loss K)
    (hloss_le_one : ∀ K, loss K ≤ 1) (hΩ : IsOmegaOneDivSq loss) :
    Tendsto
        (fun K : ℕ+ => Real.log (loss K) / (((K : ℕ) : ℝ)))
        atTop (𝓝 0) ∧
      ∀ᶠ K : ℕ+ in atTop, 0 < loss K := by
  obtain ⟨c, hc, hc_lower⟩ := hΩ
  have hdenom_pos (K : ℕ+) : 0 < (((K : ℕ) : ℝ)) := by
    exact_mod_cast K.pos
  have hpoly_pos (K : ℕ+) : 0 < c / (((K : ℕ) : ℝ) ^ 2) :=
    div_pos hc (sq_pos_of_pos (hdenom_pos K))
  have hloss_pos : ∀ᶠ K : ℕ+ in atTop, 0 < loss K :=
    hc_lower.mono fun K hK => (hpoly_pos K).trans_le hK
  have hlower_tendsto :
      Tendsto
        (fun K : ℕ+ =>
          Real.log (c / (((K : ℕ) : ℝ) ^ 2)) / (((K : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun K : ℕ+ => Real.log c / (((K : ℕ) : ℝ)))
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_pnatCast_atTop
    have hcombined :=
      hconst.sub
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ+ => (2 : ℝ)) atTop (𝓝 2)).mul
          tendsto_log_pnat_div)
    convert hcombined using 1
    · funext K
      rw [Real.log_div hc.ne'
        (pow_ne_zero 2 (ne_of_gt (hdenom_pos K))), Real.log_pow]
      ring
    · norm_num
  refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower_tendsto tendsto_const_nhds ?_ ?_, hloss_pos⟩
  · filter_upwards [hc_lower] with K hK
    apply div_le_div_of_nonneg_right _ (le_of_lt (hdenom_pos K))
    exact Real.log_le_log (hpoly_pos K) hK
  · exact Filter.Eventually.of_forall fun K =>
      div_nonpos_of_nonpos_of_nonneg
        (Real.log_nonpos (hloss_nonneg K) (hloss_le_one K))
        (le_of_lt (hdenom_pos K))

/-- Generic exact `EReal` form of the implication needed in
`prop:state_ind_no_exp`.  In particular, this is not a real-log convention:
`ENNReal.log 0 = ⊥`, and the polynomial lower bound proves that zero cannot
occur eventually before the coercion to a real logarithm is made. -/
theorem negative_limsup_log_rate_eq_zero_of_isOmegaOneDivSq
    (loss : ℕ+ → ℝ) (hloss_nonneg : ∀ K, 0 ≤ loss K)
    (hloss_le_one : ∀ K, loss K ≤ 1) (hΩ : IsOmegaOneDivSq loss) :
    -limsup
        (fun K : ℕ+ =>
          ENNReal.log (ENNReal.ofReal (loss K)) /
            ((((K : ℕ) : ℝ)) : EReal))
        atTop = 0 := by
  obtain ⟨hreal, hloss_pos⟩ :=
    tendsto_real_log_rate_of_isOmegaOneDivSq loss hloss_nonneg hloss_le_one hΩ
  have hereal :
      Tendsto
        (fun K : ℕ+ =>
          ENNReal.log (ENNReal.ofReal (loss K)) /
            ((((K : ℕ) : ℝ)) : EReal))
        atTop (𝓝 0) := by
    apply
      (continuous_coe_real_ereal.tendsto 0 |>.comp hreal).congr'
    filter_upwards [hloss_pos] with K hK
    simp only [Function.comp_apply]
    rw [ENNReal.log_ofReal_of_pos hK, ← EReal.coe_div]
  rw [hereal.limsup_eq]
  exact neg_zero

/-- A polynomial loss lower bound also makes the stronger converse-side
`-liminf` logarithmic rate equal to zero. -/
theorem negative_liminf_log_rate_eq_zero_of_isOmegaOneDivSq
    (loss : ℕ+ → ℝ) (hloss_nonneg : ∀ K, 0 ≤ loss K)
    (hloss_le_one : ∀ K, loss K ≤ 1) (hΩ : IsOmegaOneDivSq loss) :
    -liminf
        (fun K : ℕ+ =>
          ENNReal.log (ENNReal.ofReal (loss K)) /
            ((((K : ℕ) : ℝ)) : EReal))
        atTop = 0 := by
  obtain ⟨hreal, hloss_pos⟩ :=
    tendsto_real_log_rate_of_isOmegaOneDivSq loss hloss_nonneg hloss_le_one hΩ
  have hereal :
      Tendsto
        (fun K : ℕ+ =>
          ENNReal.log (ENNReal.ofReal (loss K)) /
            ((((K : ℕ) : ℝ)) : EReal))
        atTop (𝓝 0) := by
    apply
      (continuous_coe_real_ereal.tendsto 0 |>.comp hreal).congr'
    filter_upwards [hloss_pos] with K hK
    simp only [Function.comp_apply]
    rw [ENNReal.log_ofReal_of_pos hK, ← EReal.coe_div]
  rw [hereal.liminf_eq]
  exact neg_zero

/-- A strictly positive liminf supplies a positive eventual constant lower
bound, hence in particular an `Ω(K⁻²)` lower bound. -/
theorem isOmegaOneDivSq_of_hasPositiveLiminf
    (loss : ℕ+ → ℝ) (hloss_nonneg : ∀ K, 0 ≤ loss K)
    (hliminf : HasPositiveLiminf loss) :
    IsOmegaOneDivSq loss := by
  change 0 < liminf loss atTop at hliminf
  let c := liminf loss atTop / 2
  have hc : 0 < c := div_pos hliminf (by norm_num)
  have hc_lt : c < liminf loss atTop := by
    dsimp [c]
    linarith
  have heventually : ∀ᶠ K : ℕ+ in atTop, c < loss K :=
    eventually_lt_of_lt_liminf hc_lt
      (isBoundedUnder_of_eventually_ge (Filter.Eventually.of_forall hloss_nonneg))
  refine ⟨c, hc, ?_⟩
  filter_upwards [heventually] with K hK
  have hK_one : (1 : ℝ) ≤ (((K : ℕ) : ℝ)) := by
    exact_mod_cast K.pos
  calc
    c / (((K : ℝ) ^ 2)) ≤ c := by
      exact div_le_self (le_of_lt hc) (one_le_pow₀ hK_one)
    _ ≤ loss K := hK.le

/-- Positive liminf therefore also forces the exact `EReal` exponent to
vanish. -/
theorem negative_limsup_log_rate_eq_zero_of_hasPositiveLiminf
    (loss : ℕ+ → ℝ) (hloss_nonneg : ∀ K, 0 ≤ loss K)
    (hloss_le_one : ∀ K, loss K ≤ 1)
    (hliminf : HasPositiveLiminf loss) :
    -limsup
        (fun K : ℕ+ =>
          ENNReal.log (ENNReal.ofReal (loss K)) /
            ((((K : ℕ) : ℝ)) : EReal))
        atTop = 0 :=
  negative_limsup_log_rate_eq_zero_of_isOmegaOneDivSq loss hloss_nonneg
    hloss_le_one (isOmegaOneDivSq_of_hasPositiveLiminf loss hloss_nonneg hliminf)

/-- Positive liminf also forces the stronger converse-side logarithmic rate
to vanish. -/
theorem negative_liminf_log_rate_eq_zero_of_hasPositiveLiminf
    (loss : ℕ+ → ℝ) (hloss_nonneg : ∀ K, 0 ≤ loss K)
    (hloss_le_one : ∀ K, loss K ≤ 1)
    (hliminf : HasPositiveLiminf loss) :
    -liminf
        (fun K : ℕ+ =>
          ENNReal.log (ENNReal.ofReal (loss K)) /
            ((((K : ℕ) : ℝ)) : EReal))
        atTop = 0 :=
  negative_liminf_log_rate_eq_zero_of_isOmegaOneDivSq loss hloss_nonneg
    hloss_le_one (isOmegaOneDivSq_of_hasPositiveLiminf loss hloss_nonneg hliminf)

namespace PerformanceSemantics

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable {N : Network Buffer Server}

/-- Specialization of the polynomial-bound implication to the exact
throughput-loss exponent from `Policy.lean`. -/
theorem throughputLossExponent_eq_zero_of_isOmegaOneDivSq
    (P : PerformanceSemantics N) (U : N.DeterministicPolicySequence)
    (hΩ : IsOmegaOneDivSq (P.loss U)) :
    P.throughputLossExponent U = 0 := by
  exact negative_limsup_log_rate_eq_zero_of_isOmegaOneDivSq
    (P.loss U) (P.loss_nonneg U) (P.loss_le_one U) hΩ

/-- Specialization of the positive-liminf implication to
`PerformanceSemantics.loss`. -/
theorem throughputLossExponent_eq_zero_of_hasPositiveLiminf
    (P : PerformanceSemantics N) (U : N.DeterministicPolicySequence)
    (hliminf : HasPositiveLiminf (P.loss U)) :
    P.throughputLossExponent U = 0 := by
  exact negative_limsup_log_rate_eq_zero_of_hasPositiveLiminf
    (P.loss U) (P.loss_nonneg U) (P.loss_le_one U) hliminf

end PerformanceSemantics

end StateDepMOR
