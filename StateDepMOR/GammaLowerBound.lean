import StateDepMOR.GammaUpperBound
import StateDepMOR.NegativeDrift
import Mathlib.Topology.Sion

/-!
# Explicit cut lower bound on gammaCB

This module proves the reverse inequality in the explicit-gamma formula.
The two ingredients absent from `GammaUpperBound` are proved here:

* a finite-dimensional minimax/cut certificate for `vAlpha`;
* the Poisson Fenchel lower bound across a server cut.
-/

open scoped BigOperators ENNReal
open Set

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

private theorem coe_real_finset_sum
    {ι : Type*} (s : Finset ι) (g : ι -> Real) :
    (((Finset.sum s g : Real) : EReal)) =
      Finset.sum s (fun i => (g i : EReal)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, EReal.coe_add]

private theorem coe_ennreal_finset_sum
    {ι : Type*} (s : Finset ι) (g : ι -> ENNReal) :
    (((Finset.sum s g : ENNReal) : EReal)) =
      Finset.sum s (fun i => (g i : EReal)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, EReal.coe_ennreal_add]

private theorem sum_univ_if_and
    {ι κ M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [AddCommMonoid M]
    (P : ι -> Prop) (Q : κ -> Prop) [DecidablePred P] [DecidablePred Q]
    (g : ι -> κ -> M) :
    Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun k =>
          if P i /\ Q k then g i k else 0)) =
      Finset.sum (Finset.univ.filter P) (fun i =>
        Finset.sum (Finset.univ.filter Q) (fun k => g i k)) := by
  classical
  calc
    _ = Finset.sum Finset.univ (fun i =>
        if P i then
          Finset.sum Finset.univ (fun k => if Q k then g i k else 0)
        else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hPi : P i <;> simp [hPi]
    _ = _ := by
      conv_lhs =>
        enter [2, i]
        rw [← Finset.sum_filter]
      rw [← Finset.sum_filter]

private theorem sum_univ_ite_mem
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (S : Finset ι) (g : ι -> M) :
    Finset.sum Finset.univ (fun i => if i ∈ S then g i else 0) =
      Finset.sum S g := by
  symm
  calc
    Finset.sum S g =
        Finset.sum S (fun i => if i ∈ S then g i else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]
    _ = Finset.sum Finset.univ
        (fun i => if i ∈ S then g i else 0) := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i hiUniv hiS
      simp [hiS]

private theorem poissonCost_fenchel
    {nominal candidate theta : Real}
    (hnominal : 0 <= nominal) (hcandidate : 0 <= candidate) :
    ((theta * candidate - nominal * (Real.exp theta - 1) : Real) : EReal) <=
      (poissonCost nominal candidate : EReal) := by
  rcases hnominal.eq_or_lt with rfl | hnominal
  · rcases hcandidate.eq_or_lt with rfl | hcandidate
    · simp
    · rw [poissonCost_zero_of_pos hcandidate]
      exact le_top
  · rw [poissonCost_of_nominal_pos hnominal hcandidate]
    rw [EReal.coe_ennreal_ofReal]
    have hcost :
        0 <= poissonCostReal nominal candidate :=
      poissonCostReal_nonneg hnominal hcandidate
    rw [max_eq_left (by simpa [poissonCostReal] using hcost)]
    apply EReal.coe_le_coe_iff.2
    rcases hcandidate.eq_or_lt with rfl | hcandidate
    · simp only [mul_zero, zero_div, Real.log_zero, zero_mul]
      have hexp : 0 < Real.exp theta := Real.exp_pos theta
      nlinarith
    · have hratio : 0 < candidate / nominal :=
        div_pos hcandidate hnominal
      have hexpBound :=
        Real.add_one_le_exp (theta - Real.log (candidate / nominal))
      have hexpLog :
          Real.exp (theta - Real.log (candidate / nominal)) =
            Real.exp theta * nominal / candidate := by
        rw [Real.exp_sub, Real.exp_log hratio]
        field_simp
      rw [hexpLog] at hexpBound
      have hscaled :=
        mul_le_mul_of_nonneg_left hexpBound hcandidate.le
      have hcancel :
          candidate * (Real.exp theta * nominal / candidate) =
            nominal * Real.exp theta := by
        field_simp
      rw [hcancel] at hscaled
      nlinarith

private noncomputable def cutTheta
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server) (theta : Real) (j : Server) (k : Buffer) : Real :=
  if j ∈ J /\ k ∉ N.neighborhood J then
    theta
  else if j ∉ J /\ k ∈ N.neighborhood J then
    -theta
  else
    0

private theorem sum_cutTheta_candidate
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    (J : Finset Server) (theta : Real) :
    Finset.sum Finset.univ (fun j =>
        Finset.sum Finset.univ (fun k =>
          cutTheta N J theta j k * f j k)) =
      theta * cutGap N f J := by
  classical
  rw [cutGap_eq_crossing]
  have hsplit (j : Server) (k : Buffer) :
      cutTheta N J theta j k * f j k =
        (if j ∈ J /\ k ∉ N.neighborhood J then
            theta * f j k
          else 0) +
        (if j ∉ J /\ k ∈ N.neighborhood J then
            -theta * f j k
          else 0) := by
    unfold cutTheta
    split_ifs with h1 h2 <;> simp_all
  simp_rw [hsplit, Finset.sum_add_distrib]
  rw [mul_sub]
  congr 1
  · rw [sum_univ_if_and]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp_rw [← Finset.mul_sum]
  · rw [sum_univ_if_and]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp_rw [← Finset.mul_sum]
    ring

private theorem sum_cutTheta_nominal_correction
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server) (theta : Real) :
    Finset.sum Finset.univ (fun j =>
        Finset.sum Finset.univ (fun k =>
          N.phi j k * (Real.exp (cutTheta N J theta j k) - 1))) =
      N.netServiceRate J * (Real.exp theta - 1) +
        N.netArrivalRate J * (Real.exp (-theta) - 1) := by
  classical
  have hsplit (j : Server) (k : Buffer) :
      N.phi j k * (Real.exp (cutTheta N J theta j k) - 1) =
        (if j ∈ J /\ k ∉ N.neighborhood J then
            N.phi j k * (Real.exp theta - 1)
          else 0) +
        (if j ∉ J /\ k ∈ N.neighborhood J then
            N.phi j k * (Real.exp (-theta) - 1)
          else 0) := by
    unfold cutTheta
    split_ifs with h1 h2 <;> simp_all
  simp_rw [hsplit, Finset.sum_add_distrib]
  congr 1
  · simp only [StateDepMOR.Network.netServiceRate]
    rw [sum_univ_if_and]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp_rw [← Finset.sum_mul]
  · simp only [StateDepMOR.Network.netArrivalRate]
    rw [sum_univ_if_and]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp_rw [← Finset.sum_mul]

private theorem nominal_correction_eq_zero
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server)
    (hservice : 0 < N.netServiceRate J)
    (harrival : 0 < N.netArrivalRate J) :
    N.netServiceRate J *
          (Real.exp
              (Real.log (N.netArrivalRate J / N.netServiceRate J)) - 1) +
        N.netArrivalRate J *
          (Real.exp
              (-Real.log (N.netArrivalRate J / N.netServiceRate J)) - 1) =
      0 := by
  have hratio : 0 < N.netArrivalRate J / N.netServiceRate J :=
    div_pos harrival hservice
  rw [Real.exp_log hratio, Real.exp_neg,
    Real.exp_log hratio]
  field_simp
  ring

/-- The local Poisson cost dominates the entropy dual functional of every
positive-service cut. -/
theorem cutGap_log_le_localRate
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    (hf : IsNonnegativeRate f)
    (J : Finset Server)
    (hservice : 0 < N.netServiceRate J)
    (harrival : 0 < N.netArrivalRate J) :
    ((Real.log (N.netArrivalRate J / N.netServiceRate J) *
        cutGap N f J : Real) : EReal) <=
      (N.localRate f : EReal) := by
  classical
  let theta := Real.log (N.netArrivalRate J / N.netServiceRate J)
  have hcoordinate (j : Server) (k : Buffer) :
      ((cutTheta N J theta j k * f j k -
          N.phi j k *
            (Real.exp (cutTheta N J theta j k) - 1) : Real) : EReal) <=
        (poissonCost (N.phi j k) (f j k) : EReal) :=
    poissonCost_fenchel (N.phi_nonneg j k) (hf j k)
  have hsum :
      Finset.sum Finset.univ (fun j =>
          Finset.sum Finset.univ (fun k =>
            ((cutTheta N J theta j k * f j k -
                N.phi j k *
                  (Real.exp (cutTheta N J theta j k) - 1) : Real) :
              EReal))) <=
        Finset.sum Finset.univ (fun j =>
          Finset.sum Finset.univ (fun k =>
            (poissonCost (N.phi j k) (f j k) : EReal))) := by
    exact Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum fun k _ => hcoordinate j k
  have hsum' :
      ((Finset.sum Finset.univ (fun j =>
          Finset.sum Finset.univ (fun k =>
            cutTheta N J theta j k * f j k -
              N.phi j k *
                (Real.exp (cutTheta N J theta j k) - 1))) : Real) : EReal) <=
        ((N.localRate f : ENNReal) : EReal) := by
    change
      ((Finset.sum Finset.univ (fun j =>
          Finset.sum Finset.univ (fun k =>
            cutTheta N J theta j k * f j k -
              N.phi j k *
                (Real.exp (cutTheta N J theta j k) - 1))) : Real) : EReal) <=
        ((Finset.sum Finset.univ (fun j =>
          Finset.sum Finset.univ (fun k =>
            poissonCost (N.phi j k) (f j k))) : ENNReal) : EReal)
    rw [coe_real_finset_sum, coe_ennreal_finset_sum]
    simp_rw [coe_real_finset_sum]
    simp_rw [coe_ennreal_finset_sum]
    exact hsum
  simp only [Finset.sum_sub_distrib] at hsum'
  rw [sum_cutTheta_candidate, sum_cutTheta_nominal_correction] at hsum'
  have hcorrection := nominal_correction_eq_zero
    N J hservice harrival
  change
    ((theta * cutGap N f J -
        (N.netServiceRate J * (Real.exp theta - 1) +
          N.netArrivalRate J * (Real.exp (-theta) - 1)) : Real) : EReal) <=
      (N.localRate f : EReal) at hsum'
  rw [hcorrection, sub_zero] at hsum'
  exact hsum'

private theorem buffersOf_nonempty
    (N : StateDepMOR.Network Buffer Server) (j : Server) :
    (N.buffersOf j).Nonempty := by
  obtain ⟨i, hi⟩ := N.server_has_neighbor j
  exact ⟨i, (N.mem_buffersOf i j).2 hi⟩

private noncomputable def serverMin
    (N : StateDepMOR.Network Buffer Server)
    (w : Buffer -> Real) (j : Server) : Real :=
  (N.buffersOf j).inf' (buffersOf_nonempty N j) w

private theorem serverMin_le
    (N : StateDepMOR.Network Buffer Server)
    (w : Buffer -> Real) {j : Server} {i : Buffer}
    (hi : i ∈ N.buffersOf j) :
    serverMin N w j <= w i :=
  Finset.inf'_le w hi

private theorem le_serverMin
    (N : StateDepMOR.Network Buffer Server)
    (w : Buffer -> Real) (j : Server) {a : Real}
    (ha : forall i, i ∈ N.buffersOf j -> a <= w i) :
    a <= serverMin N w j :=
  Finset.le_inf' (buffersOf_nonempty N j) w ha

private def bufferGap
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) (S : Finset Buffer) : Real :=
  Finset.sum (N.serversContainedIn S) (fun j =>
      Finset.sum Finset.univ (fun k => f j k)) -
    Finset.sum Finset.univ (fun j =>
      Finset.sum S (fun i => f j i))

private def bufferMass
    (alpha : Simplex Buffer) (S : Finset Buffer) : Real :=
  Finset.sum S (fun i => alpha i)

private noncomputable def positiveSupport (w : Buffer -> Real) : Finset Buffer :=
  Finset.univ.filter fun i => 0 < w i

private noncomputable def peelWeight (w : Buffer -> Real) : Real :=
  if h : (positiveSupport w).Nonempty then
    (positiveSupport w).inf' h w
  else
    0

private noncomputable def peeledWeight (w : Buffer -> Real) :
    Buffer -> Real :=
  fun i => if i ∈ positiveSupport w then w i - peelWeight w else 0

private theorem not_mem_positiveSupport_eq_zero
    {w : Buffer -> Real} (hw : forall i, 0 <= w i)
    {i : Buffer} (hi : i ∉ positiveSupport w) :
    w i = 0 := by
  unfold positiveSupport at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
  exact le_antisymm hi (hw i)

private theorem peelWeight_pos
    {w : Buffer -> Real} (hS : (positiveSupport w).Nonempty) :
    0 < peelWeight w := by
  rw [peelWeight, dif_pos hS]
  obtain ⟨i, hi, heq⟩ :=
    Finset.exists_mem_eq_inf' hS w
  rw [heq]
  exact (Finset.mem_filter.1 hi).2

private theorem peelWeight_le
    {w : Buffer -> Real} (hS : (positiveSupport w).Nonempty)
    {i : Buffer} (hi : i ∈ positiveSupport w) :
    peelWeight w <= w i := by
  rw [peelWeight, dif_pos hS]
  exact Finset.inf'_le w hi

private theorem peeledWeight_nonnegative
    {w : Buffer -> Real} (hS : (positiveSupport w).Nonempty)
    (i : Buffer) :
    0 <= peeledWeight w i := by
  unfold peeledWeight
  split_ifs with hi
  · exact sub_nonneg.2 (peelWeight_le hS hi)
  · exact le_rfl

private theorem weight_eq_peel_add_peeled
    {w : Buffer -> Real} (hw : forall i, 0 <= w i)
    (hS : (positiveSupport w).Nonempty) (i : Buffer) :
    w i =
      (if i ∈ positiveSupport w then peelWeight w else 0) +
        peeledWeight w i := by
  by_cases hi : i ∈ positiveSupport w
  · simp [peeledWeight, hi]
  · rw [not_mem_positiveSupport_eq_zero hw hi]
    simp [peeledWeight, hi]

private theorem peeled_support_card_lt
    {w : Buffer -> Real} (hS : (positiveSupport w).Nonempty) :
    (positiveSupport (peeledWeight w)).card <
      (positiveSupport w).card := by
  have hsubset :
      positiveSupport (peeledWeight w) ⊆ positiveSupport w := by
    intro i hi
    unfold positiveSupport at hi
    rw [Finset.mem_filter] at hi
    by_contra hiS
    simp [peeledWeight, hiS] at hi
  obtain ⟨i, hi, heq⟩ :=
    Finset.exists_mem_eq_inf' hS w
  have hiZero : peeledWeight w i = 0 := by
    simp only [peeledWeight, hi, if_true]
    rw [peelWeight, dif_pos hS, heq, sub_self]
  have hinot : i ∉ positiveSupport (peeledWeight w) := by
    simp [positiveSupport, hiZero]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsubset, ?_⟩
  intro heqSets
  exact hinot (heqSets ▸ hi)

private theorem serverMin_nonnegative
    (N : StateDepMOR.Network Buffer Server)
    {w : Buffer -> Real} (hw : forall i, 0 <= w i) (j : Server) :
    0 <= serverMin N w j :=
  le_serverMin N w j (fun i hi => hw i)

private theorem serverMin_peel
    (N : StateDepMOR.Network Buffer Server)
    {w : Buffer -> Real} (hw : forall i, 0 <= w i)
    (hS : (positiveSupport w).Nonempty) (j : Server) :
    serverMin N w j =
      (if N.buffersOf j ⊆ positiveSupport w then peelWeight w else 0) +
        serverMin N (peeledWeight w) j := by
  by_cases hjS : N.buffersOf j ⊆ positiveSupport w
  · rw [if_pos hjS]
    apply le_antisymm
    · obtain ⟨i, hi, heq⟩ :=
        Finset.exists_mem_eq_inf'
          (buffersOf_nonempty N j) (peeledWeight w)
      have heq' :
          serverMin N (peeledWeight w) j = peeledWeight w i := heq
      rw [heq']
      have hiS := hjS hi
      simp only [peeledWeight, hiS, if_true]
      have hmin := serverMin_le N w hi
      linarith
    · apply le_serverMin N w j
      intro i hi
      have hiS := hjS hi
      have hpeeledMin :=
        serverMin_le N (peeledWeight w) hi
      simp only [peeledWeight, hiS, if_true] at hpeeledMin
      linarith
  · rw [if_neg hjS]
    obtain ⟨i, hi, hiS⟩ := Finset.not_subset.1 hjS
    have hwi : w i = 0 :=
      not_mem_positiveSupport_eq_zero hw hiS
    have hpeeled : peeledWeight w i = 0 := by
      simp [peeledWeight, hiS]
    have hminZero : serverMin N w j = 0 := by
      apply le_antisymm
      · simpa [hwi] using serverMin_le N w hi
      · exact serverMin_nonnegative N hw j
    have hminPeeledZero :
        serverMin N (peeledWeight w) j = 0 := by
      apply le_antisymm
      · simpa [hpeeled] using serverMin_le N (peeledWeight w) hi
      · exact serverMin_nonnegative N
          (peeledWeight_nonnegative hS) j
    rw [hminZero, hminPeeledZero, zero_add]

private noncomputable def dualCutFunctional
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) (w : Buffer -> Real) : Real :=
  Finset.sum Finset.univ (fun j =>
      (Finset.sum Finset.univ (fun k => f j k)) * serverMin N w j) -
    Finset.sum Finset.univ (fun i =>
      (Finset.sum Finset.univ (fun j => f j i)) * w i)

private theorem dualCutFunctional_peel
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    {w : Buffer -> Real} (hw : forall i, 0 <= w i)
    (hS : (positiveSupport w).Nonempty) :
    dualCutFunctional N f w =
      peelWeight w * bufferGap N f (positiveSupport w) +
        dualCutFunctional N f (peeledWeight w) := by
  classical
  unfold dualCutFunctional bufferGap
  simp_rw [serverMin_peel N hw hS]
  simp_rw [weight_eq_peel_add_peeled hw hS]
  simp only [mul_add, Finset.sum_add_distrib]
  have hservers :
      Finset.sum Finset.univ (fun j =>
          (Finset.sum Finset.univ (fun k => f j k)) *
            if N.buffersOf j ⊆ positiveSupport w then peelWeight w else 0) =
        peelWeight w *
          Finset.sum (N.serversContainedIn (positiveSupport w)) (fun j =>
            Finset.sum Finset.univ (fun k => f j k)) := by
    rw [show N.serversContainedIn (positiveSupport w) =
        Finset.univ.filter
          (fun j => N.buffersOf j ⊆ positiveSupport w) by
      rfl]
    rw [Finset.sum_filter]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  have harrivals :
      Finset.sum Finset.univ (fun i =>
          (Finset.sum Finset.univ (fun j => f j i)) *
            if i ∈ positiveSupport w then peelWeight w else 0) =
        peelWeight w *
          Finset.sum Finset.univ (fun j =>
            Finset.sum (positiveSupport w) (fun i => f j i)) := by
    have hfilter :
        Finset.sum Finset.univ (fun i =>
            (Finset.sum Finset.univ (fun j => f j i)) *
              if i ∈ positiveSupport w then peelWeight w else 0) =
          Finset.sum (positiveSupport w) (fun i =>
            (Finset.sum Finset.univ (fun j => f j i)) *
              peelWeight w) := by
      calc
        _ = Finset.sum Finset.univ (fun i =>
            if i ∈ positiveSupport w then
              (Finset.sum Finset.univ (fun j => f j i)) * peelWeight w
            else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          split_ifs <;> ring
        _ = _ := sum_univ_ite_mem _ _
    rw [hfilter, ← Finset.sum_mul]
    rw [Finset.sum_comm]
    ring
  rw [hservers, harrivals]
  ring

private theorem weightedMass_peel
    (alpha : Simplex Buffer)
    {w : Buffer -> Real} (hw : forall i, 0 <= w i)
    (hS : (positiveSupport w).Nonempty) :
    Finset.sum Finset.univ (fun i => alpha i * w i) =
      peelWeight w * bufferMass alpha (positiveSupport w) +
        Finset.sum Finset.univ (fun i =>
          alpha i * peeledWeight w i) := by
  classical
  simp_rw [weight_eq_peel_add_peeled hw hS, mul_add]
  rw [Finset.sum_add_distrib]
  unfold bufferMass
  have hfirst :
      Finset.sum Finset.univ (fun i =>
          alpha i *
            if i ∈ positiveSupport w then peelWeight w else 0) =
        peelWeight w *
          Finset.sum (positiveSupport w) (fun i => alpha i) := by
    have hfilter :
        Finset.sum Finset.univ (fun i =>
            alpha i *
              if i ∈ positiveSupport w then peelWeight w else 0) =
          Finset.sum (positiveSupport w) (fun i =>
            alpha i * peelWeight w) := by
      calc
        _ = Finset.sum Finset.univ (fun i =>
            if i ∈ positiveSupport w then
              alpha i * peelWeight w
            else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          split_ifs <;> ring
        _ = _ := sum_univ_ite_mem _ _
    rw [hfilter, ← Finset.sum_mul]
    ring
  rw [hfirst]

private theorem dualCutFunctional_le_of_cut_bounds
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer)
    (f : Server -> Buffer -> Real) (c : Real)
    (hcuts : forall S : Finset Buffer, S.Nonempty ->
      bufferGap N f S <= c * bufferMass alpha S)
    (w : Buffer -> Real) (hw : forall i, 0 <= w i) :
    dualCutFunctional N f w <=
      c * Finset.sum Finset.univ (fun i => alpha i * w i) := by
  classical
  induction hcard : (positiveSupport w).card using Nat.strong_induction_on
      generalizing w with
  | h n ih =>
      by_cases hS : (positiveSupport w).Nonempty
      · have hpeelPos : 0 < peelWeight w := peelWeight_pos hS
        have hlt :
            (positiveSupport (peeledWeight w)).card < n := by
          rw [← hcard]
          exact peeled_support_card_lt hS
        have hrec :=
          ih (positiveSupport (peeledWeight w)).card
            hlt
            (peeledWeight w)
            (peeledWeight_nonnegative hS)
            rfl
        rw [dualCutFunctional_peel N f hw hS]
        rw [weightedMass_peel alpha hw hS]
        have hcut := hcuts (positiveSupport w) hS
        nlinarith
      · have hwzero : w = 0 := by
          funext i
          have hi : i ∉ positiveSupport w := fun hi => hS ⟨i, hi⟩
          simpa using not_mem_positiveSupport_eq_zero hw hi
        subst w
        simp [dualCutFunctional, serverMin, bufferMass]

private abbrev AllocationSpace
    (N : StateDepMOR.Network Buffer Server) :=
  (j : Server) -> (N.buffersOf j) -> Real

private def allocationDomain
    (N : StateDepMOR.Network Buffer Server) :
    Set (AllocationSpace N) :=
  Set.univ.pi fun j => stdSimplex Real (N.buffersOf j)

private theorem allocationDomain_nonempty
    (N : StateDepMOR.Network Buffer Server) :
    (allocationDomain N).Nonempty := by
  classical
  let chosen : (j : Server) -> N.buffersOf j :=
    fun j => ⟨Classical.choose (N.server_has_neighbor j),
      (N.mem_buffersOf _ j).2
        (Classical.choose_spec (N.server_has_neighbor j))⟩
  let d : AllocationSpace N :=
    fun j => Pi.single (chosen j) 1
  refine ⟨d, ?_⟩
  rw [allocationDomain, Set.mem_pi]
  intro j hj
  exact single_mem_stdSimplex Real (chosen j)

private theorem allocationDomain_convex
    (N : StateDepMOR.Network Buffer Server) :
    Convex Real (allocationDomain N) := by
  unfold allocationDomain
  exact convex_pi fun j hj => convex_stdSimplex Real _

private theorem allocationDomain_compact
    (N : StateDepMOR.Network Buffer Server) :
    IsCompact (allocationDomain N) := by
  unfold allocationDomain
  exact isCompact_univ_pi fun j => isCompact_stdSimplex Real _

private noncomputable def allocatedService
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) (d : AllocationSpace N)
    (i : Buffer) : Real :=
  Finset.sum Finset.univ (fun j =>
    if h : N.compatible i j then
      d j ⟨i, (N.mem_buffersOf i j).2 h⟩ *
        Finset.sum Finset.univ (fun k => f j k)
    else
      0)

private noncomputable def minimaxPayoff
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real)
    (d : AllocationSpace N) (p : Buffer -> Real) : Real :=
  Finset.sum Finset.univ (fun i =>
    p i *
      ((allocatedService N f d i -
          Finset.sum Finset.univ (fun j => f j i)) / alpha i))

private theorem minimaxPayoff_continuous_left
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real)
    (p : Buffer -> Real) :
    Continuous (fun d : AllocationSpace N =>
      minimaxPayoff N alpha f d p) := by
  unfold minimaxPayoff
  apply continuous_finset_sum
  intro i hi
  apply Continuous.mul continuous_const
  apply Continuous.div_const
  apply Continuous.sub
  · unfold allocatedService
    apply continuous_finset_sum
    intro j hj
    by_cases hcompat : N.compatible i j
    · simp only [hcompat, dite_true]
      fun_prop
    · simp only [hcompat, dite_false]
      fun_prop
  · fun_prop

private theorem minimaxPayoff_continuous_right
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real)
    (d : AllocationSpace N) :
    Continuous (minimaxPayoff N alpha f d) := by
  unfold minimaxPayoff
  fun_prop

private theorem allocatedService_combo
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    (x y : AllocationSpace N) (a b : Real) (i : Buffer) :
    allocatedService N f (a • x + b • y) i =
      a * allocatedService N f x i +
        b * allocatedService N f y i := by
  classical
  unfold allocatedService
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hcompat : N.compatible i j
  · simp only [hcompat, dite_true, Pi.add_apply, Pi.smul_apply]
    ring
  · simp [hcompat]

private theorem minimaxPayoff_convexOn_left
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real)
    (p : Buffer -> Real) :
    ConvexOn Real (allocationDomain N)
      (fun d => minimaxPayoff N alpha f d p) := by
  refine ⟨allocationDomain_convex N, ?_⟩
  intro x hx y hy a b ha hb hab
  have heq :
      minimaxPayoff N alpha f (a • x + b • y) p =
        a * minimaxPayoff N alpha f x p +
          b * minimaxPayoff N alpha f y p := by
    unfold minimaxPayoff
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [allocatedService_combo]
    linear_combination
      (p i * Finset.sum Finset.univ (fun j => f j i) /
        alpha i) * hab
  change minimaxPayoff N alpha f (a • x + b • y) p <=
    a * minimaxPayoff N alpha f x p +
      b * minimaxPayoff N alpha f y p
  exact heq.le

private theorem minimaxPayoff_concaveOn_right
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real)
    (d : AllocationSpace N) :
    ConcaveOn Real (stdSimplex Real Buffer)
      (minimaxPayoff N alpha f d) := by
  refine ⟨convex_stdSimplex Real Buffer, ?_⟩
  intro x hx y hy a b ha hb hab
  have heq :
      minimaxPayoff N alpha f d (a • x + b • y) =
        a * minimaxPayoff N alpha f d x +
          b * minimaxPayoff N alpha f d y := by
    unfold minimaxPayoff
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.add_apply, Pi.smul_apply]
    ring
  change
    a * minimaxPayoff N alpha f d x +
        b * minimaxPayoff N alpha f d y <=
      minimaxPayoff N alpha f d (a • x + b • y)
  exact heq.ge

private theorem exists_allocation_saddle
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real) :
    exists d, d ∈ allocationDomain N /\
      exists p, p ∈ stdSimplex Real Buffer /\
        IsSaddlePointOn (allocationDomain N) (stdSimplex Real Buffer)
          (minimaxPayoff N alpha f) d p := by
  classical
  apply Sion.exists_isSaddlePointOn
      (allocationDomain_nonempty N)
      (allocationDomain_convex N)
      (allocationDomain_compact N)
  · intro p hp
    exact (minimaxPayoff_continuous_left N alpha f p).lowerSemicontinuous
      |>.lowerSemicontinuousOn (allocationDomain N)
  · intro p hp
    exact (minimaxPayoff_convexOn_left N alpha f p).quasiconvexOn
  · exact convex_stdSimplex Real Buffer
  · exact ⟨Pi.single (Classical.arbitrary Buffer) 1,
      single_mem_stdSimplex Real (Classical.arbitrary Buffer)⟩
  · exact isCompact_stdSimplex Real Buffer
  · intro d hd
    exact (minimaxPayoff_continuous_right N alpha f d).upperSemicontinuous
      |>.upperSemicontinuousOn (stdSimplex Real Buffer)
  · intro d hd
    exact (minimaxPayoff_concaveOn_right N alpha f d).quasiconcaveOn

private noncomputable def minimizingAllocation
    (N : StateDepMOR.Network Buffer Server)
    (p : Buffer -> Real) : AllocationSpace N :=
  fun j =>
    let i := Classical.choose
      (Finset.exists_mem_eq_inf' (buffersOf_nonempty N j)
        (fun q : Buffer => p q))
    Pi.single
      ⟨i, (Classical.choose_spec
        (Finset.exists_mem_eq_inf' (buffersOf_nonempty N j)
          (fun q : Buffer => p q))).1⟩ 1

private theorem minimizingAllocation_mem
    (N : StateDepMOR.Network Buffer Server)
    (p : Buffer -> Real) :
    minimizingAllocation N p ∈ allocationDomain N := by
  classical
  rw [allocationDomain, Set.mem_pi]
  intro j hj
  unfold minimizingAllocation
  exact single_mem_stdSimplex Real _

private theorem allocatedService_minimizing
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) (w : Buffer -> Real) :
    Finset.sum Finset.univ (fun i =>
        w i * allocatedService N f (minimizingAllocation N w) i) =
      Finset.sum Finset.univ (fun j =>
        Finset.sum Finset.univ (fun k => f j k) * serverMin N w j) := by
  classical
  unfold allocatedService
  have hexpand :
      Finset.sum Finset.univ (fun i =>
          w i *
            Finset.sum Finset.univ (fun j =>
              if h : N.compatible i j then
                minimizingAllocation N w j
                    ⟨i, (N.mem_buffersOf i j).2 h⟩ *
                  Finset.sum Finset.univ (fun k => f j k)
              else 0)) =
        Finset.sum Finset.univ (fun i =>
          Finset.sum Finset.univ (fun j =>
            w i *
              (if h : N.compatible i j then
                minimizingAllocation N w j
                    ⟨i, (N.mem_buffersOf i j).2 h⟩ *
                  Finset.sum Finset.univ (fun k => f j k)
              else 0))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  rw [hexpand]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoef :
      Finset.sum Finset.univ (fun i =>
        w i *
          (if h : N.compatible i j then
            minimizingAllocation N w j
              ⟨i, (N.mem_buffersOf i j).2 h⟩
          else 0)) =
        serverMin N w j := by
    have hchosen :=
      Classical.choose_spec
        (Finset.exists_mem_eq_inf' (buffersOf_nonempty N j) w)
    unfold minimizingAllocation
    simp only [Pi.single_apply]
    rw [Finset.sum_eq_single
      (Classical.choose
        (Finset.exists_mem_eq_inf' (buffersOf_nonempty N j) w))]
    · have hcompat :
          N.compatible
            (Classical.choose
              (Finset.exists_mem_eq_inf' (buffersOf_nonempty N j) w)) j :=
        (N.mem_buffersOf _ j).1 hchosen.1
      simp only [hcompat, dite_true, if_pos, mul_one]
      exact hchosen.2.symm
    · intro i hi hine
      by_cases hcompat : N.compatible i j
      · simp only [hcompat, dite_true]
        have hsub :
            (⟨i, (N.mem_buffersOf i j).2 hcompat⟩ :
              N.buffersOf j) ≠
              ⟨Classical.choose
                  (Finset.exists_mem_eq_inf'
                    (buffersOf_nonempty N j) w),
                hchosen.1⟩ := by
          intro heq
          exact hine (congrArg Subtype.val heq)
        rw [if_neg hsub, mul_zero]
      · simp [hcompat]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
  calc
    Finset.sum Finset.univ (fun i =>
        w i *
          (if h : N.compatible i j then
            minimizingAllocation N w j
                ⟨i, (N.mem_buffersOf i j).2 h⟩ *
              Finset.sum Finset.univ (fun k => f j k)
          else 0)) =
        (Finset.sum Finset.univ (fun i =>
          w i *
            (if h : N.compatible i j then
              minimizingAllocation N w j
                ⟨i, (N.mem_buffersOf i j).2 h⟩
            else 0))) *
          Finset.sum Finset.univ (fun k => f j k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hcompat : N.compatible i j
      · simp only [hcompat, dite_true]
        ring
      · simp [hcompat]
    _ = Finset.sum Finset.univ (fun k => f j k) *
        serverMin N w j := by
      rw [hcoef]
      ring

private noncomputable def ambientAllocation
    (N : StateDepMOR.Network Buffer Server)
    (d : AllocationSpace N) (i : Buffer) (j : Server) : Real :=
  if h : N.compatible i j then
    d j ⟨i, (N.mem_buffersOf i j).2 h⟩
  else
    0

private theorem ambientAllocation_nonnegative
    (N : StateDepMOR.Network Buffer Server)
    {d : AllocationSpace N} (hd : d ∈ allocationDomain N)
    (i : Buffer) (j : Server) :
    0 <= ambientAllocation N d i j := by
  unfold ambientAllocation
  split_ifs with h
  · have hdj : d j ∈ stdSimplex Real (N.buffersOf j) :=
      (Set.mem_pi.1 hd) j (Set.mem_univ j)
    exact hdj.1 _
  · exact le_rfl

private theorem ambientAllocation_sum
    (N : StateDepMOR.Network Buffer Server)
    {d : AllocationSpace N} (hd : d ∈ allocationDomain N)
    (j : Server) :
    Finset.sum (N.buffersOf j) (fun i =>
      ambientAllocation N d i j) = 1 := by
  have hdj : d j ∈ stdSimplex Real (N.buffersOf j) :=
    (Set.mem_pi.1 hd) j (Set.mem_univ j)
  rw [← hdj.2]
  rw [Finset.sum_subtype
    (p := fun i => i ∈ N.buffersOf j)
    (N.buffersOf j) (fun i => by simp)
    (fun i => ambientAllocation N d i j)]
  apply Finset.sum_congr rfl
  intro i hi
  have hcompat := (N.mem_buffersOf i j).1 i.property
  simp [ambientAllocation, hcompat]

private theorem allocatedService_eq_ambient
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    (d : AllocationSpace N) (i : Buffer) :
    allocatedService N f d i =
      Finset.sum (N.serversOf i) (fun j =>
        ambientAllocation N d i j *
          Finset.sum Finset.univ (fun k => f j k)) := by
  classical
  unfold allocatedService StateDepMOR.Network.serversOf
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hcompat : N.compatible i j <;>
    simp [ambientAllocation, hcompat]

private noncomputable def saddleDrift
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    (d : AllocationSpace N) (i : Buffer) : Real :=
  Finset.sum Finset.univ (fun j => f j i) -
    allocatedService N f d i

private theorem saddleDrift_mem
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    {d : AllocationSpace N} (hd : d ∈ allocationDomain N) :
    saddleDrift N f d ∈ N.noWasteDriftSet f := by
  refine ⟨ambientAllocation N d,
    ambientAllocation_nonnegative N hd,
    ambientAllocation_sum N hd, ?_⟩
  intro i
  unfold saddleDrift
  rw [allocatedService_eq_ambient]

private theorem saddleDrift_continuous
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) :
    Continuous (saddleDrift N f) := by
  classical
  apply continuous_pi
  intro i
  unfold saddleDrift
  apply Continuous.sub continuous_const
  unfold allocatedService
  apply continuous_finset_sum
  intro j hj
  by_cases hcompat : N.compatible i j
  · simp only [hcompat, dite_true]
    fun_prop
  · simp only [hcompat, dite_false]
    fun_prop

private noncomputable def restrictAllocation
    (N : StateDepMOR.Network Buffer Server)
    (d : Buffer -> Server -> Real) : AllocationSpace N :=
  fun j i => d i j

private theorem restrictAllocation_mem
    (N : StateDepMOR.Network Buffer Server)
    {d : Buffer -> Server -> Real}
    (hd_nonneg : forall i j, 0 <= d i j)
    (hd_sum : forall j, Finset.sum (N.buffersOf j) (fun i => d i j) = 1) :
    restrictAllocation N d ∈ allocationDomain N := by
  classical
  rw [allocationDomain, Set.mem_pi]
  intro j hj
  constructor
  · intro i
    exact hd_nonneg i j
  · change Finset.sum Finset.univ
        (fun i : N.buffersOf j => d i j) = 1
    rw [← Finset.sum_subtype
      (p := fun i => i ∈ N.buffersOf j)
      (N.buffersOf j) (fun i => by simp)
      (fun i => d i j)]
    exact hd_sum j

private theorem saddleDrift_restrictAllocation
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    {drift : Buffer -> Real} {d : Buffer -> Server -> Real}
    (hdrift : forall i, drift i =
      Finset.sum Finset.univ (fun j => f j i) -
        Finset.sum (N.serversOf i) (fun j =>
          d i j * Finset.sum Finset.univ (fun k => f j k))) :
    saddleDrift N f (restrictAllocation N d) = drift := by
  classical
  funext i
  rw [hdrift i]
  unfold saddleDrift
  rw [allocatedService_eq_ambient]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hcompat : N.compatible i j := (N.mem_serversOf i j).1 hj
  simp [ambientAllocation, restrictAllocation, hcompat]

private theorem noWasteDriftSet_eq_image_saddleDrift
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) :
    N.noWasteDriftSet f =
      saddleDrift N f '' allocationDomain N := by
  ext drift
  constructor
  · rintro ⟨d, hd_nonneg, hd_sum, hdrift⟩
    let d' := restrictAllocation N d
    have hd' : d' ∈ allocationDomain N :=
      restrictAllocation_mem N hd_nonneg hd_sum
    refine ⟨d', hd', ?_⟩
    exact saddleDrift_restrictAllocation N f hdrift
  · rintro ⟨d, hd, rfl⟩
    exact saddleDrift_mem N f hd

/-- The `sInf` representation of `vAlpha` is attained.  This proves that it
is the minimum printed in the source, rather than merely an infimum. -/
theorem exists_vAlpha_minimizer
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real) :
    exists drift : Buffer -> Real,
      drift ∈ N.noWasteDriftSet f /\
      vAlpha (N := N) alpha f =
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          ((fun i => alpha i) + drift) := by
  classical
  let objective : (Buffer -> Real) -> Real := fun drift =>
    Lyapunov.LAlphaAmbient (fun i => alpha i)
      ((fun i => alpha i) + drift)
  have hobjective : Continuous objective := by
    unfold objective Lyapunov.LAlphaAmbient Lyapunov.minCoordinate
    fun_prop
  have hcomposed :
      Continuous (fun d : AllocationSpace N =>
        objective (saddleDrift N f d)) :=
    hobjective.comp (saddleDrift_continuous N f)
  obtain ⟨d, hd, hminimum⟩ :=
    (allocationDomain_compact N).exists_sInf_image_eq
      (allocationDomain_nonempty N) hcomposed.continuousOn
  refine ⟨saddleDrift N f d, saddleDrift_mem N f hd, ?_⟩
  change sInf (objective '' N.noWasteDriftSet f) =
    objective (saddleDrift N f d)
  rw [noWasteDriftSet_eq_image_saddleDrift]
  simpa only [Set.image_image, Function.comp_apply] using hminimum

private theorem saddleDrift_joint_continuous
    (N : StateDepMOR.Network Buffer Server) :
    Continuous (fun p :
        (Server -> Buffer -> Real) × AllocationSpace N =>
      saddleDrift N p.1 p.2) := by
  classical
  apply continuous_pi
  intro i
  unfold saddleDrift allocatedService
  apply Continuous.sub
  · fun_prop
  · apply continuous_finset_sum
    intro j hj
    by_cases hcompat : N.compatible i j
    · simp only [hcompat, dite_true]
      fun_prop
    · simp only [hcompat, dite_false]
      fun_prop

/-- The minimum no-waste Lyapunov drift varies continuously with the
candidate service-token rate matrix. -/
theorem vAlpha_continuous
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) :
    Continuous (fun f : Server -> Buffer -> Real =>
      vAlpha (N := N) alpha f) := by
  classical
  let objective : (Buffer -> Real) -> Real := fun drift =>
    Lyapunov.LAlphaAmbient (fun i => alpha i)
      ((fun i => alpha i) + drift)
  have hobjective : Continuous objective := by
    unfold objective Lyapunov.LAlphaAmbient Lyapunov.minCoordinate
    fun_prop
  have hjoint :
      Continuous (fun p :
          (Server -> Buffer -> Real) × AllocationSpace N =>
        objective (saddleDrift N p.1 p.2)) :=
    hobjective.comp (saddleDrift_joint_continuous N)
  have hminimum :
      Continuous (fun f : Server -> Buffer -> Real =>
        sInf ((fun d : AllocationSpace N =>
          objective (saddleDrift N f d)) '' allocationDomain N)) :=
    (allocationDomain_compact N).continuous_sInf hjoint
  convert hminimum using 1
  funext f
  change sInf
      ((fun drift =>
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          ((fun i => alpha i) + drift)) '' N.noWasteDriftSet f) =
    sInf ((fun d : AllocationSpace N =>
      objective (saddleDrift N f d)) '' allocationDomain N)
  rw [noWasteDriftSet_eq_image_saddleDrift, Set.image_image]

private theorem vAlpha_le_saddlePayoff
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real)
    (hf : IsNonnegativeRate f)
    (hflex : N.HasLimitedFlexibility)
    {d : AllocationSpace N} (hd : d ∈ allocationDomain N)
    {p : Buffer -> Real} (hp : p ∈ stdSimplex Real Buffer)
    (hsaddle :
      IsSaddlePointOn (allocationDomain N) (stdSimplex Real Buffer)
        (minimaxPayoff N alpha f) d p) :
    vAlpha (N := N) alpha f <= minimaxPayoff N alpha f d p := by
  classical
  let drift := saddleDrift N f d
  have hdrift : drift ∈ N.noWasteDriftSet f :=
    saddleDrift_mem N f hd
  have hv :
      vAlpha (N := N) alpha f <=
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          ((fun i => alpha i) + drift) := by
    unfold vAlpha
    apply csInf_le
    · obtain ⟨J, hJ⟩ := N.limitedSets_nonempty hflex
      refine ⟨cutGap N f J / N.cutMass alpha J, ?_⟩
      intro value hvalue
      obtain ⟨drift', hdrift', rfl⟩ := hvalue
      exact cutGap_div_cutMass_le_lAlpha
        N alpha halpha f hf J ((N.mem_limitedSets J).1 hJ) hdrift'
    exact ⟨drift, hdrift, rfl⟩
  obtain ⟨q, hqmem, hq⟩ :=
    Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun i => drift i / alpha i)
  have hunit :
      Pi.single q 1 ∈ stdSimplex Real Buffer :=
    single_mem_stdSimplex Real q
  have hs :=
    hsaddle d hd (Pi.single q 1) hunit
  have hpayoff :
      minimaxPayoff N alpha f d (Pi.single q 1) =
        -(drift q / alpha q) := by
    unfold minimaxPayoff drift saddleDrift
    rw [Finset.sum_eq_single q]
    · simp [Pi.single_apply]
      ring
    · intro i hi hine
      simp [Pi.single_apply, hine]
    · simp
  have hL :
      Lyapunov.LAlphaAmbient (fun i => alpha i)
          ((fun i => alpha i) + drift) =
        -(drift q / alpha q) := by
    rw [Lyapunov.LAlphaAmbient_centered
      (fun i => alpha i) drift (fun i => ne_of_gt (halpha i))]
    rw [show Lyapunov.minCoordinate (fun i => drift i / alpha i) =
        drift q / alpha q by
      exact hq]
  rw [hL, ← hpayoff] at hv
  exact hv.trans hs

private theorem saddlePayoff_le_dual
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real)
    {d : AllocationSpace N} (hd : d ∈ allocationDomain N)
    {p : Buffer -> Real} (hp : p ∈ stdSimplex Real Buffer)
    (hsaddle :
      IsSaddlePointOn (allocationDomain N) (stdSimplex Real Buffer)
        (minimaxPayoff N alpha f) d p) :
    minimaxPayoff N alpha f d p <=
      dualCutFunctional N f (fun i => p i / alpha i) := by
  let w : Buffer -> Real := fun i => p i / alpha i
  have hdmin : minimizingAllocation N w ∈ allocationDomain N :=
    minimizingAllocation_mem N w
  have hs := hsaddle (minimizingAllocation N w) hdmin p hp
  calc
    minimaxPayoff N alpha f d p <=
        minimaxPayoff N alpha f (minimizingAllocation N w) p := hs
    _ = dualCutFunctional N f w := by
      unfold minimaxPayoff dualCutFunctional
      rw [← allocatedService_minimizing N f w]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [w]
      ring

private def nonemptyBufferCuts : Finset (Finset Buffer) :=
  Finset.univ.filter fun S => S.Nonempty

private theorem nonemptyBufferCuts_nonempty :
    (nonemptyBufferCuts (Buffer := Buffer)).Nonempty := by
  classical
  refine ⟨Finset.univ, ?_⟩
  simp [nonemptyBufferCuts]

private noncomputable def maximumBufferCutRatio
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real) : Real :=
  (nonemptyBufferCuts (Buffer := Buffer)).sup'
    (nonemptyBufferCuts_nonempty (Buffer := Buffer))
    (fun S => bufferGap N f S / bufferMass alpha S)

private theorem bufferCutRatio_le_maximum
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real)
    {S : Finset Buffer} (hS : S.Nonempty) :
    bufferGap N f S / bufferMass alpha S <=
      maximumBufferCutRatio N alpha f := by
  unfold maximumBufferCutRatio
  exact Finset.le_sup'
    (fun S => bufferGap N f S / bufferMass alpha S)
    ((Finset.mem_filter.2 ⟨Finset.mem_univ S, hS⟩ :
      S ∈ nonemptyBufferCuts (Buffer := Buffer)))

private theorem exists_maximumBufferCutRatio
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (f : Server -> Buffer -> Real) :
    exists S : Finset Buffer, S.Nonempty /\
      maximumBufferCutRatio N alpha f =
        bufferGap N f S / bufferMass alpha S := by
  obtain ⟨S, hS, heq⟩ :=
    Finset.exists_mem_eq_sup'
      (nonemptyBufferCuts_nonempty (Buffer := Buffer))
      (fun S => bufferGap N f S / bufferMass alpha S)
  exact ⟨S, (Finset.mem_filter.1 hS).2, heq⟩

/-- Finite max-flow/minimax certificate: positive controller-independent
drift is witnessed by one nonempty buffer cut. -/
theorem exists_bufferCut_vAlpha_le
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real) (hf : IsNonnegativeRate f)
    (hflex : N.HasLimitedFlexibility) :
    exists S : Finset Buffer, S.Nonempty /\
      vAlpha (N := N) alpha f <=
        bufferGap N f S / bufferMass alpha S := by
  classical
  obtain ⟨d, hd, p, hp, hsaddle⟩ :=
    exists_allocation_saddle N alpha f
  let w : Buffer -> Real := fun i => p i / alpha i
  let c := maximumBufferCutRatio N alpha f
  have hw : forall i, 0 <= w i := by
    intro i
    exact div_nonneg (hp.1 i) (halpha i).le
  have hmass (S : Finset Buffer) (hS : S.Nonempty) :
      0 < bufferMass alpha S := by
    unfold bufferMass
    exact Finset.sum_pos (fun i hi => halpha i) hS
  have hcuts (S : Finset Buffer) (hS : S.Nonempty) :
      bufferGap N f S <= c * bufferMass alpha S := by
    apply (div_le_iff₀ (hmass S hS)).1
    exact bufferCutRatio_le_maximum N alpha f hS
  have hweighted :
      Finset.sum Finset.univ (fun i => alpha i * w i) = 1 := by
    calc
      _ = Finset.sum Finset.univ (fun i => p i) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [w]
        field_simp [ne_of_gt (halpha i)]
      _ = 1 := hp.2
  have hdual :
      dualCutFunctional N f w <= c := by
    have h := dualCutFunctional_le_of_cut_bounds
      N alpha f c hcuts w hw
    rw [hweighted, mul_one] at h
    exact h
  obtain ⟨S, hS, hSeq⟩ :=
    exists_maximumBufferCutRatio N alpha f
  refine ⟨S, hS, ?_⟩
  rw [← hSeq]
  exact (vAlpha_le_saddlePayoff
      N alpha halpha f hf hflex hd hp hsaddle).trans
    ((saddlePayoff_le_dual N alpha halpha f hd hp hsaddle).trans hdual)

private theorem bufferGap_univ
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) :
    bufferGap N f Finset.univ = 0 := by
  classical
  have hservers :
      N.serversContainedIn (Finset.univ : Finset Buffer) =
        Finset.univ := by
    ext j
    simp [StateDepMOR.Network.serversContainedIn]
  unfold bufferGap
  rw [hservers]
  rw [Finset.sum_comm]
  ring

private theorem bufferGap_le_cutGap
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) (hf : IsNonnegativeRate f)
    (S : Finset Buffer) :
    bufferGap N f S <= cutGap N f (N.serversContainedIn S) := by
  classical
  unfold bufferGap cutGap
  have hsubset :=
    N.neighborhood_serversContainedIn_subset S
  apply sub_le_sub_left
  apply Finset.sum_le_sum
  intro j hj
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
    (fun i hiS hi => hf j i)

private theorem bufferMass_neighborhood_le
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (S : Finset Buffer) :
    N.cutMass alpha (N.serversContainedIn S) <=
      bufferMass alpha S := by
  unfold StateDepMOR.Network.cutMass bufferMass
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (N.neighborhood_serversContainedIn_subset S)
    (fun i hiS hi => alpha.nonneg i)

private theorem localRate_eq_top_of_zero_service_positive_cutGap
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) (hf : IsNonnegativeRate f)
    (J : Finset Server)
    (hservice : N.netServiceRate J = 0)
    (hgap : 0 < cutGap N f J) :
    N.localRate f = (⊤ : ENNReal) := by
  classical
  rw [cutGap_eq_crossing] at hgap
  let outflow :=
    Finset.sum J (fun j =>
      Finset.sum
        (Finset.univ.filter (fun k => k ∉ N.neighborhood J))
        (fun k => f j k))
  let inflow :=
    Finset.sum (Finset.univ.filter (fun j => j ∉ J)) (fun j =>
      Finset.sum (N.neighborhood J) (fun k => f j k))
  have hinflow : 0 <= inflow := by
    dsimp [inflow]
    exact Finset.sum_nonneg fun j hj =>
      Finset.sum_nonneg fun k hk => hf j k
  have houtflow : 0 < outflow := by
    dsimp [outflow, inflow] at hgap hinflow
    linarith
  have houtRows :
      exists j, j ∈ J /\
        0 < Finset.sum
          (Finset.univ.filter (fun k => k ∉ N.neighborhood J))
          (fun k => f j k) := by
    exact (Finset.sum_pos_iff_of_nonneg
      (fun j hj => Finset.sum_nonneg fun k hk => hf j k)).1 houtflow
  obtain ⟨j, hjJ, hjpos⟩ := houtRows
  have houtCols :
      exists k,
        k ∈ Finset.univ.filter (fun k => k ∉ N.neighborhood J) /\
          0 < f j k := by
    exact (Finset.sum_pos_iff_of_nonneg
      (fun k hk => hf j k)).1 hjpos
  obtain ⟨k, hk, hfk⟩ := houtCols
  have hphi_le : N.phi j k <= N.netServiceRate J := by
    unfold StateDepMOR.Network.netServiceRate
    have hinner :
        N.phi j k <=
          Finset.sum
            (Finset.univ.filter (fun q => q ∉ N.neighborhood J))
            (fun q => N.phi j q) := by
      exact Finset.single_le_sum
        (fun q hq => N.phi_nonneg j q) hk
    exact hinner.trans
      (Finset.single_le_sum
        (fun q hq => Finset.sum_nonneg fun r hr => N.phi_nonneg q r)
        hjJ)
  have hphi : N.phi j k = 0 := by
    have := N.phi_nonneg j k
    rw [hservice] at hphi_le
    exact le_antisymm hphi_le this
  have hcost : poissonCost (N.phi j k) (f j k) = (⊤ : ENNReal) := by
    rw [hphi]
    exact poissonCost_zero_of_pos hfk
  apply top_unique
  rw [StateDepMOR.Network.localRate]
  calc
    (⊤ : ENNReal) = poissonCost (N.phi j k) (f j k) := hcost.symm
    _ <= Finset.sum Finset.univ (fun q =>
          poissonCost (N.phi j q) (f j q)) :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun q => poissonCost (N.phi j q) (f j q))
        (fun q hq => bot_le)
        (Finset.mem_univ k)
    _ <= Finset.sum Finset.univ (fun q =>
          Finset.sum Finset.univ (fun r =>
            poissonCost (N.phi q r) (f q r))) :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun q =>
          Finset.sum Finset.univ (fun r =>
            poissonCost (N.phi q r) (f q r)))
        (fun q hq => bot_le)
        (Finset.mem_univ j)

private theorem explicitExponent_mul_vAlpha_le_localRate
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP)
    (f : Server -> Buffer -> Real) (hf : IsNonnegativeRate f)
    (hv : 0 < vAlpha (N := N) alpha f) :
    (((N.explicitExponent alpha) *
        vAlpha (N := N) alpha f : Real) : EReal) <=
      (N.localRate f : EReal) := by
  classical
  obtain ⟨S, hS, hvS⟩ :=
    exists_bufferCut_vAlpha_le N alpha halpha f hf hflex
  have hmassS : 0 < bufferMass alpha S := by
    unfold bufferMass
    exact Finset.sum_pos (fun i hi => halpha i) hS
  have hratioPos :
      0 < bufferGap N f S / bufferMass alpha S :=
    hv.trans_le hvS
  have hgapS : 0 < bufferGap N f S :=
    (by
      rcases (div_pos_iff.1 hratioPos) with h | h
      · exact h.1
      · exact (not_lt_of_ge hmassS.le h.2).elim)
  have hSproper : S ≠ Finset.univ := by
    intro hSuniv
    rw [hSuniv, bufferGap_univ] at hgapS
    exact lt_irrefl 0 hgapS
  let J := N.serversContainedIn S
  have hJproper : J ≠ Finset.univ :=
    N.serversContainedIn_ne_univ hSproper
  have hgap_le : bufferGap N f S <= cutGap N f J :=
    bufferGap_le_cutGap N f hf S
  have hcutGap : 0 < cutGap N f J :=
    hgapS.trans_le hgap_le
  have hmass_le :
      N.cutMass alpha J <= bufferMass alpha S :=
    bufferMass_neighborhood_le N alpha S
  by_cases hservice : 0 < N.netServiceRate J
  · have hJlimited : N.IsLimitedSet J := ⟨hJproper, hservice⟩
    have hstrict := hcrp J hJlimited
    have harrival : 0 < N.netArrivalRate J :=
      hservice.trans hstrict
    let theta := Real.log (N.netArrivalRate J / N.netServiceRate J)
    have htheta : 0 < theta := by
      exact Real.log_pos ((one_lt_div hservice).2 hstrict)
    have hexplicit :
        N.explicitExponent alpha <= N.cutMass alpha J * theta := by
      exact N.explicitExponent_le_cutExponentTerm
        hflex alpha hJlimited
    have hvMass :
        vAlpha (N := N) alpha f * bufferMass alpha S <=
          bufferGap N f S :=
      (le_div_iff₀ hmassS).1 hvS
    have hexplicitPos :=
      N.explicitExponent_pos halpha hflex hcrp
    have hreal :
        N.explicitExponent alpha * vAlpha (N := N) alpha f <=
          theta * cutGap N f J := by
      calc
        N.explicitExponent alpha * vAlpha (N := N) alpha f <=
            (N.cutMass alpha J * theta) *
              vAlpha (N := N) alpha f :=
          mul_le_mul_of_nonneg_right hexplicit hv.le
        _ <= (bufferMass alpha S * theta) *
              vAlpha (N := N) alpha f := by
          gcongr
        _ <= theta * bufferGap N f S := by
          nlinarith
        _ <= theta * cutGap N f J :=
          mul_le_mul_of_nonneg_left hgap_le htheta.le
    exact (EReal.coe_le_coe_iff.2 hreal).trans
      (cutGap_log_le_localRate N f hf J hservice harrival)
  · have hserviceZero : N.netServiceRate J = 0 := by
      have hnonneg := N.netServiceRate_nonneg J
      linarith
    rw [localRate_eq_top_of_zero_service_positive_cutGap
      N f hf J hserviceZero hcutGap]
    exact le_top

private theorem explicitExponent_le_candidateRatio
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP)
    (f : Server -> Buffer -> Real) (hf : IsNonnegativeRate f)
    (hv : 0 < vAlpha (N := N) alpha f) :
    (N.explicitExponent alpha : EReal) <=
      (N.localRate f : EReal) /
        (vAlpha (N := N) alpha f : EReal) := by
  apply (EReal.le_div_iff_mul_le
    (EReal.coe_pos.2 hv) (EReal.coe_ne_top _)).2
  rw [← EReal.coe_mul]
  exact explicitExponent_mul_vAlpha_le_localRate
    N alpha halpha hflex hcrp f hf hv

/-- The hard direction of the explicit-gamma identity. -/
theorem explicitExponent_le_gammaCB
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    (N.explicitExponent alpha : EReal) <= gammaCB (N := N) alpha := by
  classical
  unfold gammaCB
  apply le_csInf
  · obtain ⟨J, hJmem⟩ := N.limitedSets_nonempty hflex
    have hJ : N.IsLimitedSet J := (N.mem_limitedSets J).1 hJmem
    have harrival : 0 < N.netArrivalRate J :=
      hJ.2.trans (hcrp J hJ)
    let f := tiltedRate N N.phi J
    have hf : IsNonnegativeRate f :=
      tiltedRate_nonnegative N J hJ.2 harrival
    have hgap :
        0 < (N.netArrivalRate J - N.netServiceRate J) /
          N.cutMass alpha J := by
      exact div_pos (sub_pos.2 (hcrp J hJ))
        (N.cutMass_pos halpha hJ)
    have hv :
        0 < vAlpha (N := N) alpha f := by
      exact hgap.trans_le
        (by
          rw [← cutGap_tiltedRate N J hJ.2 harrival]
          exact cutGap_div_cutMass_le_vAlpha
            N alpha halpha f hf J hJ)
    exact ⟨(N.localRate f : EReal) /
      (vAlpha (N := N) alpha f : EReal), f, hf, hv, rfl⟩
  · intro q hq
    obtain ⟨f, hf, hv, rfl⟩ := hq
    exact explicitExponent_le_candidateRatio
      N alpha halpha hflex hcrp f hf hv

/-- Exact equality in the paper's explicit-gamma lemma. -/
theorem explicitGammaEquality
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    gammaCB (N := N) alpha = (N.explicitExponent alpha : EReal) :=
  le_antisymm
    (gammaCB_le_explicitExponent N alpha halpha hflex hcrp)
    (explicitExponent_le_gammaCB N alpha halpha hflex hcrp)

/-- Packaged proof of `ExplicitGammaEqualityStatement`. -/
theorem explicitGammaEqualityStatement
    (N : StateDepMOR.Network Buffer Server)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    ExplicitGammaEqualityStatement (N := N) := by
  intro alpha halpha
  exact explicitGammaEquality N alpha halpha hflex hcrp

end StateDepMOR.PaperStatements.Network
