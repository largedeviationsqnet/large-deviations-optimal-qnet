import StateDepMOR.PaperStatements
import StateDepMOR.PoissonRateProofs

/-!
# Cut bounds for the fixed-state converse exponent

This module proves the policy-independent cut lower bound on `vAlpha`.
Every no-waste allocation must drain a server cut at least at its net cut
gap, and the ambient Lyapunov function detects that aggregate drain.
-/

open scoped BigOperators

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

private noncomputable def selectedBuffer
    (N : StateDepMOR.Network Buffer Server) (j : Server) : Buffer :=
  Classical.choose (N.server_has_neighbor j)

private theorem selectedBuffer_compatible
    (N : StateDepMOR.Network Buffer Server) (j : Server) :
    N.compatible (selectedBuffer N j) j :=
  Classical.choose_spec (N.server_has_neighbor j)

/-- The no-waste drift polytope is nonempty for every rate matrix. -/
theorem noWasteDriftSet_nonempty
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) :
    (N.noWasteDriftSet f).Nonempty := by
  classical
  let d : Buffer -> Server -> Real :=
    fun i j => if i = selectedBuffer N j then 1 else 0
  let drift : Buffer -> Real :=
    fun i =>
      (Finset.sum Finset.univ (fun j => f j i)) -
        Finset.sum (N.serversOf i) (fun j =>
          d i j * Finset.sum Finset.univ (fun k => f j k))
  refine ⟨drift, d, ?_, ?_, ?_⟩
  · intro i j
    dsimp [d]
    split <;> norm_num
  · intro j
    have hmem : selectedBuffer N j ∈ N.buffersOf j :=
      (N.mem_buffersOf (selectedBuffer N j) j).2
        (selectedBuffer_compatible N j)
    simp [d, hmem]
  · intro i
    rfl

private theorem neighborhood_filter_compatible
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server) {j : Server} (hj : j ∈ J) :
    (N.neighborhood J).filter (fun i => N.compatible i j) =
      N.buffersOf j := by
  ext i
  simp only [Finset.mem_filter, N.mem_neighborhood, N.mem_buffersOf]
  constructor
  · exact fun h => h.2
  · intro hij
    exact ⟨⟨j, hj, hij⟩, hij⟩

private theorem allocatedService_reindex
    (N : StateDepMOR.Network Buffer Server)
    (d : Buffer -> Server -> Real)
    (f : Server -> Buffer -> Real)
    (S : Finset Buffer) :
    Finset.sum S (fun i =>
        Finset.sum (N.serversOf i) (fun j =>
          d i j * Finset.sum Finset.univ (fun k => f j k))) =
      Finset.sum Finset.univ (fun j =>
        Finset.sum (S.filter (fun i => N.compatible i j)) (fun i =>
          d i j * Finset.sum Finset.univ (fun k => f j k))) := by
  classical
  simp only [StateDepMOR.Network.serversOf, Finset.sum_filter]
  rw [Finset.sum_comm]

private theorem cutRows_le_allocatedService
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (J : Finset Server)
    (d : Buffer -> Server -> Real)
    (hd_nonneg : forall i j, 0 <= d i j)
    (hd_sum : forall j,
      Finset.sum (N.buffersOf j) (fun i => d i j) = 1) :
    Finset.sum J (fun j =>
        Finset.sum Finset.univ (fun k => f j k)) <=
      Finset.sum (N.neighborhood J) (fun i =>
        Finset.sum (N.serversOf i) (fun j =>
          d i j * Finset.sum Finset.univ (fun k => f j k))) := by
  classical
  rw [allocatedService_reindex N d f (N.neighborhood J)]
  calc
    Finset.sum J (fun j =>
        Finset.sum Finset.univ (fun k => f j k)) =
        Finset.sum J (fun j =>
          Finset.sum
            ((N.neighborhood J).filter (fun i => N.compatible i j))
            (fun i =>
              d i j * Finset.sum Finset.univ (fun k => f j k))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [neighborhood_filter_compatible N J hj]
      rw [← Finset.sum_mul]
      rw [hd_sum j, one_mul]
    _ <= Finset.sum Finset.univ (fun j =>
        Finset.sum
          ((N.neighborhood J).filter (fun i => N.compatible i j))
          (fun i =>
            d i j * Finset.sum Finset.univ (fun k => f j k))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
      intro j hjUniv hjJ
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hd_nonneg i j)
        (Finset.sum_nonneg (fun k hk => hf j k))

private theorem cutGap_le_neg_sum_drift
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (J : Finset Server)
    {drift : Buffer -> Real}
    (hdrift : drift ∈ N.noWasteDriftSet f) :
    cutGap N f J <=
      -Finset.sum (N.neighborhood J) (fun i => drift i) := by
  classical
  obtain ⟨d, hd_nonneg, hd_sum, hdrift_eq⟩ := hdrift
  have hservice := cutRows_le_allocatedService
    N f hf J d hd_nonneg hd_sum
  simp_rw [hdrift_eq]
  simp only [Finset.sum_sub_distrib]
  have harrivals :
      Finset.sum (N.neighborhood J) (fun i =>
          Finset.sum Finset.univ (fun j => f j i)) =
        Finset.sum Finset.univ (fun j =>
          Finset.sum (N.neighborhood J) (fun i => f j i)) := by
    rw [Finset.sum_comm]
  rw [harrivals]
  dsimp [cutGap]
  linarith

private theorem neg_sum_drift_le_lAlpha_mul_cutMass
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (J : Finset Server) (drift : Buffer -> Real) :
    -Finset.sum (N.neighborhood J) (fun i => drift i) <=
      Lyapunov.LAlphaAmbient (fun i => alpha i)
          ((fun i => alpha i) + drift) *
        N.cutMass alpha J := by
  let minimumRatio :=
    Lyapunov.minCoordinate (fun i => drift i / alpha i)
  have hcoordinate (i : Buffer) :
      minimumRatio * alpha i <= drift i := by
    apply (le_div_iff₀ (halpha i)).1
    exact Finset.inf'_le
      (fun q => drift q / alpha q) (Finset.mem_univ i)
  have hsum :
      minimumRatio * N.cutMass alpha J <=
        Finset.sum (N.neighborhood J) (fun i => drift i) := by
    dsimp [StateDepMOR.Network.cutMass]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => hcoordinate i)
  have hcentered :
      Lyapunov.LAlphaAmbient (fun i => alpha i)
          ((fun i => alpha i) + drift) =
        -minimumRatio := by
    exact Lyapunov.LAlphaAmbient_centered
      (fun i => alpha i) drift (fun i => ne_of_gt (halpha i))
  rw [hcentered]
  linarith

/-- Every no-waste allocation has Lyapunov growth at least the normalized
net drain gap of every limited server cut. -/
theorem cutGap_div_cutMass_le_lAlpha
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (J : Finset Server) (hJ : N.IsLimitedSet J)
    {drift : Buffer -> Real}
    (hdrift : drift ∈ N.noWasteDriftSet f) :
    cutGap N f J / N.cutMass alpha J <=
      Lyapunov.LAlphaAmbient (fun i => alpha i)
        ((fun i => alpha i) + drift) := by
  have hmass : 0 < N.cutMass alpha J :=
    N.cutMass_pos halpha hJ
  apply (div_le_iff₀ hmass).2
  exact (cutGap_le_neg_sum_drift N f hf J hdrift).trans
    (neg_sum_drift_le_lAlpha_mul_cutMass
      N alpha halpha J drift)

/-- Cut lower bound on the controller-independent drift value `vAlpha`. -/
theorem cutGap_div_cutMass_le_vAlpha
    (N : StateDepMOR.Network Buffer Server)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (J : Finset Server) (hJ : N.IsLimitedSet J) :
    cutGap N f J / N.cutMass alpha J <=
      vAlpha (N := N) alpha f := by
  unfold vAlpha
  apply le_csInf
  · exact (noWasteDriftSet_nonempty N f).image
      (fun drift =>
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          ((fun i => alpha i) + drift))
  · intro value hvalue
    obtain ⟨drift, hdrift, rfl⟩ := hvalue
    exact cutGap_div_cutMass_le_lAlpha
      N alpha halpha f hf J hJ hdrift

/-- The cut gap is the crossing outflow minus the crossing inflow. -/
theorem cutGap_eq_crossing
    (N : StateDepMOR.Network Buffer Server)
    (f : Server -> Buffer -> Real) (J : Finset Server) :
    cutGap N f J =
      Finset.sum J (fun j =>
          Finset.sum
            (Finset.univ.filter
              (fun k => k ∉ N.neighborhood J))
            (fun k => f j k)) -
        Finset.sum
          (Finset.univ.filter (fun j => j ∉ J))
          (fun j =>
            Finset.sum (N.neighborhood J) (fun k => f j k)) := by
  classical
  have hrows :
      Finset.sum J (fun j =>
          Finset.sum Finset.univ (fun k => f j k)) =
        Finset.sum J (fun j =>
          Finset.sum (N.neighborhood J) (fun k => f j k)) +
        Finset.sum J (fun j =>
          Finset.sum
            (Finset.univ.filter
              (fun k => k ∉ N.neighborhood J))
            (fun k => f j k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ)
        (p := fun k => k ∈ N.neighborhood J)
        (f := fun k => f j k)).symm
  have harrivals :
      Finset.sum Finset.univ (fun j =>
          Finset.sum (N.neighborhood J) (fun k => f j k)) =
        Finset.sum J (fun j =>
          Finset.sum (N.neighborhood J) (fun k => f j k)) +
        Finset.sum
          (Finset.univ.filter (fun j => j ∉ J))
          (fun j =>
            Finset.sum (N.neighborhood J) (fun k => f j k)) := by
    simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ)
        (p := fun j => j ∈ J)
        (f := fun j =>
          Finset.sum (N.neighborhood J) (fun k => f j k))).symm
  rw [cutGap, hrows, harrivals]
  ring

/-- The exponential tilt is componentwise nonnegative whenever both cut
rates are positive. -/
theorem tiltedRate_nonnegative
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server)
    (hservice : 0 < N.netServiceRate J)
    (harrival : 0 < N.netArrivalRate J) :
    IsNonnegativeRate (tiltedRate N N.phi J) := by
  intro j k
  unfold tiltedRate
  split_ifs
  · exact div_nonneg
      (mul_nonneg (N.phi_nonneg j k) harrival.le) hservice.le
  · exact div_nonneg
      (mul_nonneg (N.phi_nonneg j k) hservice.le) harrival.le
  · exact N.phi_nonneg j k

private theorem tilted_crossing_outflow
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server)
    (hservice : 0 < N.netServiceRate J)
    (harrival : 0 < N.netArrivalRate J) :
    Finset.sum J (fun j =>
        Finset.sum
          (Finset.univ.filter (fun k => k ∉ N.neighborhood J))
          (fun k => tiltedRate N N.phi J j k)) =
      N.netArrivalRate J := by
  classical
  calc
    Finset.sum J (fun j =>
        Finset.sum
          (Finset.univ.filter (fun k => k ∉ N.neighborhood J))
          (fun k => tiltedRate N N.phi J j k)) =
        Finset.sum J (fun j =>
          Finset.sum
            (Finset.univ.filter (fun k => k ∉ N.neighborhood J))
            (fun k =>
              N.phi j k *
                (N.netArrivalRate J / N.netServiceRate J))) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      simp [tiltedRate, hj, hk.2]
      ring
    _ = N.netServiceRate J *
        (N.netArrivalRate J / N.netServiceRate J) := by
      simp only [StateDepMOR.Network.netServiceRate]
      simp_rw [← Finset.sum_mul]
    _ = N.netArrivalRate J := by
      field_simp

private theorem tilted_crossing_inflow
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server)
    (hservice : 0 < N.netServiceRate J)
    (harrival : 0 < N.netArrivalRate J) :
    Finset.sum
        (Finset.univ.filter (fun j => j ∉ J))
        (fun j =>
          Finset.sum (N.neighborhood J)
            (fun k => tiltedRate N N.phi J j k)) =
      N.netServiceRate J := by
  classical
  calc
    Finset.sum
        (Finset.univ.filter (fun j => j ∉ J))
          (fun j =>
            Finset.sum (N.neighborhood J)
              (fun k => tiltedRate N N.phi J j k)) =
        Finset.sum
          (Finset.univ.filter (fun j => j ∉ J))
          (fun j =>
            Finset.sum (N.neighborhood J)
              (fun k =>
                N.phi j k *
                  (N.netServiceRate J / N.netArrivalRate J))) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjnot : j ∉ J := (Finset.mem_filter.1 hj).2
      apply Finset.sum_congr rfl
      intro k hk
      simp [tiltedRate, hjnot, hk]
      ring
    _ = N.netArrivalRate J *
        (N.netServiceRate J / N.netArrivalRate J) := by
      simp only [StateDepMOR.Network.netArrivalRate]
      simp_rw [← Finset.sum_mul]
    _ = N.netServiceRate J := by
      field_simp

/-- The distinguished cut gap under its exponential tilt is
`lambda_J - mu_J`. -/
theorem cutGap_tiltedRate
    (N : StateDepMOR.Network Buffer Server)
    (J : Finset Server)
    (hservice : 0 < N.netServiceRate J)
    (harrival : 0 < N.netArrivalRate J) :
    cutGap N (tiltedRate N N.phi J) J =
      N.netArrivalRate J - N.netServiceRate J := by
  rw [cutGap_eq_crossing]
  rw [tilted_crossing_outflow N J hservice harrival]
  rw [tilted_crossing_inflow N J hservice harrival]

end StateDepMOR.PaperStatements.Network
