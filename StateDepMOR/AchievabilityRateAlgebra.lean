import StateDepMOR.AchievabilityBoundProof

/-!
# Analytic rate algebra for achievability

This module isolates the deterministic scaled-log calculation used after a
finite-size estimate of the form

`loss K <= C * max (p K) ((q K) ^ m)`.

The fixed factor `C` disappears on the exponential scale, `max` selects the
slower of the two rates, and the positive integer power multiplies the rate
of `q` by `m`.
-/

open Filter
open scoped ENNReal Topology

namespace StateDepMOR.PaperStatements.Network

private theorem real_pow_le_one_of_nonneg_of_le_one
    (x : Real) (n : Nat) (hx_nonneg : 0 <= x) (hx_le_one : x <= 1) :
    x ^ n <= 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      calc
        x ^ n * x <= 1 * x :=
          mul_le_mul_of_nonneg_right ih hx_nonneg
        _ <= 1 := by simpa using hx_le_one

/-- The scaled logarithm commutes with a pointwise maximum. -/
theorem scaledLogLossPNat_max
    (p q : PNat -> Real) (K : PNat) :
    scaledLogLossPNat (fun J => max (p J) (q J)) K =
      max (scaledLogLossPNat p K) (scaledLogLossPNat q K) := by
  unfold scaledLogLossPNat
  rw [ENNReal.ofReal_max, ENNReal.log_monotone.map_max]
  have hden :
      (0 : EReal) <= ((((K : Nat) : Real)) : EReal) := by
    positivity
  exact
    (show Monotone
        (fun x : EReal => x / ((((K : Nat) : Real)) : EReal)) from
      fun _ _ hxy => EReal.div_le_div_right_of_nonneg hden hxy).map_max

/-- A natural power multiplies the scaled logarithm by its exponent. -/
theorem scaledLogLossPNat_pow
    (q : PNat -> Real) (m : Nat)
    (hq_nonneg : forall K, 0 <= q K) (K : PNat) :
    scaledLogLossPNat (fun J => (q J) ^ m) K =
      (m : EReal) * scaledLogLossPNat q K := by
  unfold scaledLogLossPNat
  rw [ENNReal.ofReal_pow (hq_nonneg K), ENNReal.log_pow, mul_div_assoc]

/-- Pointwise scaled-log identity for the maximum/power expression. -/
theorem scaledLogLossPNat_max_pow
    (p q : PNat -> Real) (m : Nat)
    (hq_nonneg : forall K, 0 <= q K) (K : PNat) :
    scaledLogLossPNat (fun J => max (p J) ((q J) ^ m)) K =
      max (scaledLogLossPNat p K)
        ((m : EReal) * scaledLogLossPNat q K) := by
  rw [scaledLogLossPNat_max, scaledLogLossPNat_pow q m hq_nonneg]

/-- The limsup of the maximum/power expression is the maximum of the
component limsups, with the power multiplying the second one. -/
theorem limsup_scaledLogLossPNat_max_pow
    (p q : PNat -> Real) (m : Nat)
    (hq_nonneg : forall K, 0 <= q K) :
    limsup
        (scaledLogLossPNat (fun K => max (p K) ((q K) ^ m))) atTop =
      max (limsup (scaledLogLossPNat p) atTop)
        ((m : EReal) * limsup (scaledLogLossPNat q) atTop) := by
  have hpoint :
      scaledLogLossPNat (fun K => max (p K) ((q K) ^ m)) =
        fun K =>
          max (scaledLogLossPNat p K)
            ((m : EReal) * scaledLogLossPNat q K) := by
    funext K
    exact scaledLogLossPNat_max_pow p q m hq_nonneg K
  rw [hpoint, limsup_max]
  rw [EReal.limsup_const_mul_of_nonneg_of_ne_top
    (show (0 : EReal) <= (m : EReal) by positivity)
    (EReal.natCast_ne_top m)]

/-- Component rate estimates combine according to the slower of `d` and
`m * e`. -/
theorem limsup_scaledLogLossPNat_max_pow_le
    (p q : PNat -> Real) (m : Nat) (d e : Real)
    (hq_nonneg : forall K, 0 <= q K)
    (hp_rate :
      limsup (scaledLogLossPNat p) atTop <= -(d : EReal))
    (hq_rate :
      limsup (scaledLogLossPNat q) atTop <= -(e : EReal))
    (hde : d <= (m : Real) * e) :
    limsup
        (scaledLogLossPNat (fun K => max (p K) ((q K) ^ m))) atTop <=
      -(d : EReal) := by
  rw [limsup_scaledLogLossPNat_max_pow p q m hq_nonneg]
  apply max_le hp_rate
  calc
    (m : EReal) * limsup (scaledLogLossPNat q) atTop <=
        (m : EReal) * (-(e : EReal)) :=
      mul_le_mul_of_nonneg_left hq_rate (by positivity)
    _ = -((((m : Real) * e : Real)) : EReal) := by
      rw [mul_neg]
      congr 1
    _ <= -(d : EReal) := by
      exact EReal.neg_le_neg_iff.mpr
        (EReal.coe_le_coe_iff.mpr hde)

/-- A finite-size constant times a maximum/power bound inherits the target
scaled-log limsup estimate. All probability-range and positivity hypotheses
are explicit. -/
theorem limsup_scaledLogLossPNat_le_of_le_const_mul_max_pow
    (loss p q : PNat -> Real) (C : Real) (m : Nat) (d e : Real)
    (hC : 0 < C) (_hm : 0 < m)
    (_hp_nonneg : forall K, 0 <= p K)
    (hp_le_one : forall K, p K <= 1)
    (hq_nonneg : forall K, 0 <= q K)
    (hq_le_one : forall K, q K <= 1)
    (hbound :
      forall K, loss K <= C * max (p K) ((q K) ^ m))
    (hp_rate :
      limsup (scaledLogLossPNat p) atTop <= -(d : EReal))
    (hq_rate :
      limsup (scaledLogLossPNat q) atTop <= -(e : EReal))
    (hde : d <= (m : Real) * e) :
    limsup (scaledLogLossPNat loss) atTop <= -(d : EReal) := by
  have hmass_le_one :
      forall K, max (p K) ((q K) ^ m) <= 1 := by
    intro K
    exact max_le (hp_le_one K)
      (real_pow_le_one_of_nonneg_of_le_one
        (q K) m (hq_nonneg K) (hq_le_one K))
  exact
    (limsup_scaledLogLossPNat_le_of_le_const_mul
      loss (fun K => max (p K) ((q K) ^ m)) C
      hC hmass_le_one hbound).trans
      (limsup_scaledLogLossPNat_max_pow_le
        p q m d e hq_nonneg hp_rate hq_rate hde)

/-- Direct negative-limsup-rate form of
`limsup_scaledLogLossPNat_le_of_le_const_mul_max_pow`. -/
theorem le_negativeLimsupLogRate_of_le_const_mul_max_pow
    (loss p q : PNat -> Real) (C : Real) (m : Nat) (d e : Real)
    (hC : 0 < C) (hm : 0 < m)
    (hp_nonneg : forall K, 0 <= p K)
    (hp_le_one : forall K, p K <= 1)
    (hq_nonneg : forall K, 0 <= q K)
    (hq_le_one : forall K, q K <= 1)
    (hbound :
      forall K, loss K <= C * max (p K) ((q K) ^ m))
    (hp_rate :
      limsup (scaledLogLossPNat p) atTop <= -(d : EReal))
    (hq_rate :
      limsup (scaledLogLossPNat q) atTop <= -(e : EReal))
    (hde : d <= (m : Real) * e) :
    (d : EReal) <= negativeLimsupLogRate loss := by
  apply le_negativeLimsupLogRate_of_limsup_scaledLogLossPNat_le
  exact limsup_scaledLogLossPNat_le_of_le_const_mul_max_pow
    loss p q C m d e hC hm hp_nonneg hp_le_one hq_nonneg hq_le_one
    hbound hp_rate hq_rate hde

#print axioms scaledLogLossPNat_max_pow
#print axioms limsup_scaledLogLossPNat_max_pow_le
#print axioms limsup_scaledLogLossPNat_le_of_le_const_mul_max_pow
#print axioms le_negativeLimsupLogRate_of_le_const_mul_max_pow

end StateDepMOR.PaperStatements.Network
