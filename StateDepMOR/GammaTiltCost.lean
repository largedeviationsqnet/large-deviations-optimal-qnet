import StateDepMOR.GammaCutBounds

/-!
# Poisson cost of the cut tilt

This module evaluates the local Poisson rate of the exponential cut tilt.
The calculation includes zero nominal coordinates and therefore does not
silently assume that every token type has positive probability.
-/

open scoped BigOperators ENNReal

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-- The scalar entropy cost of multiplying a Poisson rate by `c`. -/
noncomputable def multiplierCost (c : Real) : Real :=
  c * Real.log c - c + 1

theorem multiplierCost_nonnegative {c : Real} (hc : 0 <= c) :
    0 <= multiplierCost c := by
  simpa [multiplierCost, poissonCostReal] using
    (poissonCostReal_nonneg (nominal := (1 : Real))
      (candidate := c) zero_lt_one hc)

theorem poissonCost_mul
    {nominal c : Real} (hnominal : 0 <= nominal) (hc : 0 <= c) :
    poissonCost nominal (nominal * c) =
      ENNReal.ofReal (nominal * multiplierCost c) := by
  rcases hnominal.eq_or_lt with rfl | hnominal
  · simp [multiplierCost]
  · rw [poissonCost_of_nominal_pos hnominal
      (mul_nonneg hnominal.le hc)]
    congr 1
    have hratio : nominal * c / nominal = c := by
      field_simp
    rw [hratio]
    unfold multiplierCost
    ring

private noncomputable def tiltCostTerm
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server) (j : Server) (k : Buffer) : Real :=
  if j ∈ J /\ k ∉ N.neighborhood J then
    N.phi j k *
      multiplierCost (N.netArrivalRate J / N.netServiceRate J)
  else if j ∉ J /\ k ∈ N.neighborhood J then
    N.phi j k *
      multiplierCost (N.netServiceRate J / N.netArrivalRate J)
  else
    0

private theorem tiltCostTerm_nonnegative
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server)
    (hservice : 0 < N.netServiceRate J)
    (harrival : 0 < N.netArrivalRate J)
    (j : Server) (k : Buffer) :
    0 <= tiltCostTerm N J j k := by
  unfold tiltCostTerm
  split_ifs
  · exact mul_nonneg (N.phi_nonneg j k)
      (multiplierCost_nonnegative
        (div_nonneg harrival.le hservice.le))
  · exact mul_nonneg (N.phi_nonneg j k)
      (multiplierCost_nonnegative
        (div_nonneg hservice.le harrival.le))
  · exact le_rfl

private theorem poissonCost_tiltedRate
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server)
    (hservice : 0 < N.netServiceRate J)
    (harrival : 0 < N.netArrivalRate J)
    (j : Server) (k : Buffer) :
    poissonCost (N.phi j k) (tiltedRate N N.phi J j k) =
      ENNReal.ofReal (tiltCostTerm N J j k) := by
  unfold tiltedRate tiltCostTerm
  split_ifs with hfirst hsecond
  · have hcand :
        N.phi j k * N.netArrivalRate J / N.netServiceRate J =
          N.phi j k *
            (N.netArrivalRate J / N.netServiceRate J) := by
      ring
    rw [hcand]
    exact poissonCost_mul (N.phi_nonneg j k)
      (div_nonneg harrival.le hservice.le)
  · have hcand :
        N.phi j k * N.netServiceRate J / N.netArrivalRate J =
          N.phi j k *
            (N.netServiceRate J / N.netArrivalRate J) := by
      ring
    rw [hcand]
    exact poissonCost_mul (N.phi_nonneg j k)
      (div_nonneg hservice.le harrival.le)
  · simpa using
      ((poissonCost_eq_zero_iff (N.phi_nonneg j k)).2 rfl)

private theorem sum_first_cut_region
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server) (a : Real) :
    Finset.sum Finset.univ (fun j =>
        Finset.sum Finset.univ (fun k =>
          if j ∈ J /\ k ∉ N.neighborhood J then
            N.phi j k * a
          else
            0)) =
      N.netServiceRate J * a := by
  classical
  calc
    Finset.sum Finset.univ (fun j =>
        Finset.sum Finset.univ (fun k =>
          if j ∈ J /\ k ∉ N.neighborhood J then
            N.phi j k * a
          else
            0)) =
        Finset.sum J (fun j =>
          Finset.sum
            (Finset.univ.filter
              (fun k => k ∉ N.neighborhood J))
            (fun k => N.phi j k * a)) := by
      symm
      apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ J)
      · intro j hj
        have hjnot : j ∉ J := (Finset.mem_sdiff.1 hj).2
        simp [hjnot]
      · intro j hj
        simpa only [hj, true_and] using
          (Finset.sum_filter
            (s := Finset.univ)
            (p := fun k => k ∉ N.neighborhood J)
            (f := fun k => N.phi j k * a))
    _ = N.netServiceRate J * a := by
      simp only [StateDepMOR.Network.netServiceRate]
      simp_rw [← Finset.sum_mul]

private theorem sum_second_cut_region
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server) (a : Real) :
    Finset.sum Finset.univ (fun j =>
        Finset.sum Finset.univ (fun k =>
          if j ∉ J /\ k ∈ N.neighborhood J then
            N.phi j k * a
          else
            0)) =
      N.netArrivalRate J * a := by
  classical
  calc
    Finset.sum Finset.univ (fun j =>
        Finset.sum Finset.univ (fun k =>
          if j ∉ J /\ k ∈ N.neighborhood J then
            N.phi j k * a
          else
            0)) =
        Finset.sum
          (Finset.univ.filter (fun j => j ∉ J))
          (fun j =>
            Finset.sum (N.neighborhood J)
              (fun k => N.phi j k * a)) := by
      conv_rhs =>
        rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjJ : j ∈ J
      · simp [hjJ]
      · simp only [hjJ, not_false_eq_true, true_and, if_true]
        simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
          (Finset.sum_filter
            (s := Finset.univ)
            (p := fun k => k ∈ N.neighborhood J)
            (f := fun k => N.phi j k * a)).symm
    _ = N.netArrivalRate J * a := by
      simp only [StateDepMOR.Network.netArrivalRate]
      simp_rw [← Finset.sum_mul]

private theorem sum_tiltCostTerm
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server) :
    Finset.sum Finset.univ (fun j =>
        Finset.sum Finset.univ (fun k => tiltCostTerm N J j k)) =
      N.netServiceRate J *
          multiplierCost (N.netArrivalRate J / N.netServiceRate J) +
        N.netArrivalRate J *
          multiplierCost (N.netServiceRate J / N.netArrivalRate J) := by
  classical
  let outCost :=
    multiplierCost (N.netArrivalRate J / N.netServiceRate J)
  let inCost :=
    multiplierCost (N.netServiceRate J / N.netArrivalRate J)
  calc
    Finset.sum Finset.univ (fun j =>
        Finset.sum Finset.univ (fun k => tiltCostTerm N J j k)) =
        Finset.sum Finset.univ (fun j =>
          Finset.sum Finset.univ (fun k =>
            (if j ∈ J /\ k ∉ N.neighborhood J then
              N.phi j k * outCost
            else
              0) +
            (if j ∉ J /\ k ∈ N.neighborhood J then
              N.phi j k * inCost
            else
              0))) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      unfold tiltCostTerm
      dsimp [outCost, inCost]
      by_cases hfirst : j ∈ J /\ k ∉ N.neighborhood J
      · have hsecond :
            Not (j ∉ J /\ k ∈ N.neighborhood J) :=
          fun h => h.1 hfirst.1
        simp only [if_pos hfirst, if_neg hsecond, add_zero]
      · by_cases hsecond : j ∉ J /\ k ∈ N.neighborhood J
        · simp only [if_neg hfirst, if_pos hsecond, zero_add]
        · simp only [if_neg hfirst, if_neg hsecond, add_zero]
    _ =
        Finset.sum Finset.univ (fun j =>
          Finset.sum Finset.univ (fun k =>
            if j ∈ J /\ k ∉ N.neighborhood J then
              N.phi j k * outCost
            else
              0)) +
        Finset.sum Finset.univ (fun j =>
          Finset.sum Finset.univ (fun k =>
            if j ∉ J /\ k ∈ N.neighborhood J then
              N.phi j k * inCost
            else
              0)) := by
      simp_rw [Finset.sum_add_distrib]
    _ = N.netServiceRate J * outCost +
        N.netArrivalRate J * inCost := by
      rw [sum_first_cut_region, sum_second_cut_region]
    _ = N.netServiceRate J *
          multiplierCost (N.netArrivalRate J / N.netServiceRate J) +
        N.netArrivalRate J *
          multiplierCost (N.netServiceRate J / N.netArrivalRate J) := by
      rfl

/-- Exact local Poisson cost of the cut tilt. -/
theorem localRate_tiltedRate
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server)
    (hservice : 0 < N.netServiceRate J)
    (harrival : 0 < N.netArrivalRate J) :
    N.localRate (tiltedRate N N.phi J) =
      ENNReal.ofReal
        ((N.netArrivalRate J - N.netServiceRate J) *
          Real.log (N.netArrivalRate J / N.netServiceRate J)) := by
  classical
  rw [StateDepMOR.Network.localRate]
  simp_rw [poissonCost_tiltedRate N J hservice harrival]
  have hinner (j : Server) :
      Finset.sum Finset.univ
          (fun k => ENNReal.ofReal (tiltCostTerm N J j k)) =
        ENNReal.ofReal
          (Finset.sum Finset.univ (fun k => tiltCostTerm N J j k)) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    exact fun k hk =>
      tiltCostTerm_nonnegative N J hservice harrival j k
  simp_rw [hinner]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [sum_tiltCostTerm]
    congr 1
    unfold multiplierCost
    have hservice_ne : Not (N.netServiceRate J = 0) :=
      ne_of_gt hservice
    have harrival_ne : Not (N.netArrivalRate J = 0) :=
      ne_of_gt harrival
    have hlog_inv :
        Real.log (N.netServiceRate J / N.netArrivalRate J) =
          -Real.log (N.netArrivalRate J / N.netServiceRate J) := by
      rw [Real.log_div hservice_ne harrival_ne,
        Real.log_div harrival_ne hservice_ne]
      ring
    rw [hlog_inv]
    field_simp
    ring
  · intro j hj
    exact Finset.sum_nonneg (fun k hk =>
      tiltCostTerm_nonnegative N J hservice harrival j k)

end StateDepMOR.PaperStatements.Network
