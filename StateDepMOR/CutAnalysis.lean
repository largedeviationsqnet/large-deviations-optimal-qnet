import StateDepMOR.Network

/-!
# Finite cut analysis

Elementary consequences of limited flexibility and CRP used in the positivity
part of Theorem 1.
-/

open scoped BigOperators

namespace StateDepMOR.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable (N : Network Buffer Server)

omit [DecidableEq Server] in
theorem netServiceRate_nonneg (J : Finset Server) :
    0 ≤ N.netServiceRate J := by
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro k hk
  exact N.phi_nonneg j k

omit [DecidableEq Buffer] in
theorem netArrivalRate_nonneg (J : Finset Server) :
    0 ≤ N.netArrivalRate J := by
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro k hk
  exact N.phi_nonneg j k

omit [DecidableEq Buffer] [DecidableEq Server] in
theorem cutMass_nonneg (α : Simplex Buffer) (J : Finset Server) :
    0 ≤ N.cutMass α J := by
  apply Finset.sum_nonneg
  intro i hi
  exact α.nonneg i

omit [DecidableEq Buffer] [DecidableEq Server] in
theorem cutMass_le_one (α : Simplex Buffer) (J : Finset Server) :
    N.cutMass α J ≤ 1 := by
  calc
    N.cutMass α J ≤ ∑ i : Buffer, α i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        simp
      · intro i hi hnot
        exact α.nonneg i
    _ = 1 := α.sum_eq_one

theorem limitedSet_nonempty {J : Finset Server} (hJ : N.IsLimitedSet J) :
    J.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty.mp h] at hJ
  simp [IsLimitedSet, netServiceRate] at hJ

theorem neighborhood_nonempty_of_limited {J : Finset Server}
    (hJ : N.IsLimitedSet J) : (N.neighborhood J).Nonempty := by
  obtain ⟨j, hj⟩ := N.limitedSet_nonempty hJ
  obtain ⟨i, hi⟩ := N.server_has_neighbor j
  refine ⟨i, ?_⟩
  simp only [mem_neighborhood]
  exact ⟨j, hj, hi⟩

theorem cutMass_pos {α : Simplex Buffer} (hα : α.IsInterior)
    {J : Finset Server} (hJ : N.IsLimitedSet J) :
    0 < N.cutMass α J := by
  apply Finset.sum_pos
  · intro i hi
    exact hα i
  · exact N.neighborhood_nonempty_of_limited hJ

/-- Limited flexibility produces at least one proper positive-service cut.
This justifies every minimum over `𝒥` in the paper. -/
theorem limitedSets_nonempty (hflex : N.HasLimitedFlexibility) :
    N.limitedSets.Nonempty := by
  obtain ⟨j, k, hjk, hphi⟩ := hflex
  have hproper : ({j} : Finset Server) ≠ Finset.univ := by
    intro heq
    obtain ⟨j₂, hj₂⟩ := N.buffer_has_neighbor k
    have hj₂mem : j₂ ∈ ({j} : Finset Server) := by
      rw [heq]
      simp
    have hj₂eq : j₂ = j := Finset.mem_singleton.mp hj₂mem
    exact hjk (hj₂eq ▸ hj₂)
  have hkoutside :
      k ∈ Finset.univ.filter (fun i => i ∉ N.neighborhood ({j} : Finset Server)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_neighborhood,
      Finset.mem_singleton, not_exists, not_and]
    intro j₂ hj₂eq hcompat
    apply hjk
    simpa [hj₂eq] using hcompat
  have hservice : 0 < N.netServiceRate ({j} : Finset Server) := by
    simp only [netServiceRate, Finset.sum_singleton]
    exact lt_of_lt_of_le hphi
      (Finset.single_le_sum
        (fun i hi => N.phi_nonneg j i) hkoutside)
  refine ⟨{j}, ?_⟩
  rw [mem_limitedSets]
  exact ⟨hproper, hservice⟩

theorem cutExponentTerm_pos
    {α : Simplex Buffer} (hα : α.IsInterior)
    (hcrp : N.HasCRP) {J : Finset Server} (hJ : N.IsLimitedSet J) :
    0 < N.cutExponentTerm α J := by
  rw [cutExponentTerm]
  apply mul_pos (N.cutMass_pos hα hJ)
  apply Real.log_pos
  exact (one_lt_div hJ.2).2 (hcrp J hJ)

theorem explicitExponent_le_cutExponentTerm
    (hflex : N.HasLimitedFlexibility) (α : Simplex Buffer)
    {J : Finset Server} (hJ : N.IsLimitedSet J) :
    N.explicitExponent α ≤ N.cutExponentTerm α J := by
  classical
  have hne := N.limitedSets_nonempty hflex
  rw [explicitExponent, dif_pos hne]
  apply Finset.inf'_le
  exact (N.mem_limitedSets J).2 hJ

/-- Positivity assertion in Part 1 of `thm:main_tight`. -/
theorem explicitExponent_pos
    {α : Simplex Buffer} (hα : α.IsInterior)
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    0 < N.explicitExponent α := by
  classical
  have hne := N.limitedSets_nonempty hflex
  rw [explicitExponent, dif_pos hne]
  obtain ⟨J, hJmem, hmin⟩ :=
    Finset.exists_mem_eq_inf' hne (N.cutExponentTerm α)
  rw [hmin]
  exact N.cutExponentTerm_pos hα hcrp (N.mem_limitedSets J |>.mp hJmem)

theorem interiorExponentSet_nonempty [Nonempty Buffer] :
    N.interiorExponentSet.Nonempty := by
  refine ⟨N.explicitExponent (Simplex.uniform : Simplex Buffer), ?_⟩
  exact ⟨Simplex.uniform, Simplex.uniform_isInterior, rfl⟩

theorem interiorExponentSet_bddAbove [Nonempty Buffer]
    (hflex : N.HasLimitedFlexibility) (hcrp : N.HasCRP) :
    BddAbove N.interiorExponentSet := by
  classical
  obtain ⟨J, hJmem⟩ := N.limitedSets_nonempty hflex
  have hJ : N.IsLimitedSet J := (N.mem_limitedSets J).1 hJmem
  let upper := Real.log (N.netArrivalRate J / N.netServiceRate J)
  refine ⟨upper, ?_⟩
  rintro r ⟨α, hα, rfl⟩
  calc
    N.explicitExponent α ≤ N.cutExponentTerm α J :=
      N.explicitExponent_le_cutExponentTerm hflex α hJ
    _ = N.cutMass α J * upper := rfl
    _ ≤ 1 * upper := by
      apply mul_le_mul_of_nonneg_right (N.cutMass_le_one α J)
      exact (Real.log_pos ((one_lt_div hJ.2).2 (hcrp J hJ))).le
    _ = upper := one_mul upper

/-- The precise "arbitrarily close" conclusion at the end of
`thm:main_tight`; it deliberately does not assert that the supremum is
attained. -/
theorem exists_interior_exponent_gt_best_sub [Nonempty Buffer]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ α : Simplex Buffer, α.IsInterior ∧
      N.bestSMWExponent - δ < N.explicitExponent α := by
  have hne := N.interiorExponentSet_nonempty
  have hlt : N.bestSMWExponent - δ < N.bestSMWExponent := sub_lt_self _ hδ
  obtain ⟨r, hr, hnear⟩ := exists_lt_of_lt_csSup hne hlt
  obtain ⟨α, hα, rfl⟩ := hr
  exact ⟨α, hα, hnear⟩

end StateDepMOR.Network
