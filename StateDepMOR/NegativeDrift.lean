import StateDepMOR.CutAnalysis

/-!
# Negative drift under near-nominal inputs

This module formalizes the deterministic finite-cut core of the appendix
subsection "Negative drift under near-nominal inputs".  Limited flexibility
is not needed for these results: connectivity handles the zero-service-cut
case, while CRP handles the positive-service-cut case.
-/

open scoped BigOperators

namespace StateDepMOR.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable (N : Network Buffer Server)

/-- `A(S) = {j | buffersOf j ⊆ S}` from the appendix. -/
def serversContainedIn (S : Finset Buffer) : Finset Server :=
  Finset.univ.filter fun j => N.buffersOf j ⊆ S

omit [DecidableEq Server] in
@[simp]
theorem mem_serversContainedIn (S : Finset Buffer) (j : Server) :
    j ∈ N.serversContainedIn S ↔ N.buffersOf j ⊆ S := by
  simp [serversContainedIn]

/-- The appendix functional
`D_S(f) = ∑_{j,k∈S} f(j,k) - ∑_{j∈A(S),k} f(j,k)`. -/
def cutDrift (S : Finset Buffer) (f : Server → Buffer → ℝ) : ℝ :=
  (∑ j, ∑ k ∈ S, f j k) -
    ∑ j ∈ N.serversContainedIn S, ∑ k, f j k

/-- The first sum in the crossing representation of `D_S`. -/
private def crossingInflow (S : Finset Buffer)
    (f : Server → Buffer → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => j ∉ N.serversContainedIn S),
    ∑ k ∈ S, f j k

/-- The second sum in the crossing representation of `D_S`. -/
private def crossingOutflow (S : Finset Buffer)
    (f : Server → Buffer → ℝ) : ℝ :=
  ∑ j ∈ N.serversContainedIn S,
    ∑ k ∈ Finset.univ.filter (fun k => k ∉ S), f j k

theorem cutDrift_eq_crossing (S : Finset Buffer)
    (f : Server → Buffer → ℝ) :
    N.cutDrift S f =
      N.crossingInflow S f - N.crossingOutflow S f := by
  classical
  have hservers :
      (∑ j, ∑ k ∈ S, f j k) =
        (∑ j ∈ N.serversContainedIn S, ∑ k ∈ S, f j k) +
          N.crossingInflow S f := by
    simpa only [crossingInflow, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ)
        (p := fun j => j ∈ N.serversContainedIn S)
        (f := fun j => ∑ k ∈ S, f j k)).symm
  have hbuffers :
      (∑ j ∈ N.serversContainedIn S, ∑ k, f j k) =
        (∑ j ∈ N.serversContainedIn S, ∑ k ∈ S, f j k) +
          N.crossingOutflow S f := by
    rw [crossingOutflow, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun k => k ∈ S)
        (f := fun k => f j k)).symm
  rw [cutDrift, hservers, hbuffers]
  ring

theorem neighborhood_serversContainedIn_subset (S : Finset Buffer) :
    N.neighborhood (N.serversContainedIn S) ⊆ S := by
  intro i hi
  rw [N.mem_neighborhood] at hi
  obtain ⟨j, hjA, hij⟩ := hi
  exact (N.mem_serversContainedIn S j).1 hjA
    ((N.mem_buffersOf i j).2 hij)

theorem serversContainedIn_ne_univ {S : Finset Buffer}
    (hS : S ≠ Finset.univ) :
    N.serversContainedIn S ≠ Finset.univ := by
  intro hA
  apply hS
  apply Finset.eq_univ_of_forall
  intro i
  obtain ⟨j, hij⟩ := N.buffer_has_neighbor i
  have hjA : j ∈ N.serversContainedIn S := by
    rw [hA]
    simp
  exact (N.mem_serversContainedIn S j).1 hjA
    ((N.mem_buffersOf i j).2 hij)

private theorem netArrivalRate_le_crossingInflow (S : Finset Buffer) :
    N.netArrivalRate (N.serversContainedIn S) ≤
      N.crossingInflow S N.phi := by
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact N.neighborhood_serversContainedIn_subset S
  · intro k hkS hk
    exact N.phi_nonneg j k

private theorem crossingOutflow_le_netServiceRate (S : Finset Buffer) :
    N.crossingOutflow S N.phi ≤
      N.netServiceRate (N.serversContainedIn S) := by
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    intro hkNeighborhood
    exact hk ((N.neighborhood_serversContainedIn_subset S)
      hkNeighborhood)
  · intro k hk hk'
    exact N.phi_nonneg j k

private theorem cutDifference_le_cutDrift (S : Finset Buffer) :
    N.netArrivalRate (N.serversContainedIn S) -
        N.netServiceRate (N.serversContainedIn S) ≤
      N.cutDrift S N.phi := by
  rw [N.cutDrift_eq_crossing]
  exact sub_le_sub (N.netArrivalRate_le_crossingInflow S)
    (N.crossingOutflow_le_netServiceRate S)

private theorem crossingInflow_pos_of_connected
    (hconn : N.IsConnected) {S : Finset Buffer} (hne : S.Nonempty)
    (hproper : S ≠ Finset.univ) :
    0 < N.crossingInflow S N.phi := by
  classical
  obtain ⟨inside, hinside⟩ := hne
  have houtside : (Finset.univ \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro h
    exact hproper (Finset.univ_subset_iff.1 h)
  obtain ⟨outside, houtsideDiff⟩ := houtside
  have houtsideS : outside ∉ S := (Finset.mem_sdiff.1 houtsideDiff).2
  have hcross :
      ∃ j, j ∉ N.serversContainedIn S ∧
        ∃ k ∈ S, 0 < N.phi j k := by
    by_contra h
    push Not at h
    have hstep :
        ∀ {a b}, N.TokenStep a b → a ∉ S → b ∉ S := by
      intro a b hab ha hb
      obtain ⟨j, haj, hjb⟩ := hab
      have hjA : j ∉ N.serversContainedIn S := by
        intro hjA
        exact ha ((N.mem_serversContainedIn S j).1 hjA
          ((N.mem_buffersOf a j).2 haj))
      exact (not_lt_of_ge (h j hjA b hb)) hjb
    have hpath :
        ∀ {a b}, Relation.ReflTransGen N.TokenStep a b →
          a ∉ S → b ∉ S := by
      intro a b hab
      induction hab with
      | refl =>
          exact fun ha => ha
      | tail hab hbc ih =>
          exact fun ha => hstep hbc (ih ha)
    exact (hpath (hconn outside inside) houtsideS) hinside
  obtain ⟨j, hjA, k, hkS, hjk⟩ := hcross
  have hjmem :
      j ∈ Finset.univ.filter
        (fun j => j ∉ N.serversContainedIn S) := by
    exact Finset.mem_filter.2 ⟨Finset.mem_univ j, hjA⟩
  have hkinner :
      N.phi j k ≤ ∑ q ∈ S, N.phi j q := by
    exact Finset.single_le_sum
      (fun q hq => N.phi_nonneg j q) hkS
  have houter :
      (∑ q ∈ S, N.phi j q) ≤ N.crossingInflow S N.phi := by
    exact Finset.single_le_sum
      (fun j' hj' => Finset.sum_nonneg fun q hq => N.phi_nonneg j' q)
      hjmem
  exact hjk.trans_le (hkinner.trans houter)

/-- Deterministic finite-cut core of the appendix negative-drift argument.

For a nonempty proper buffer set `S`, connectivity and CRP imply
`0 < D_S(phi)`.  The proof follows the source's two cases according to
whether `A(S)` has positive net service rate.  Limited flexibility is not
an assumption because it is not used in either case.
-/
theorem cutDrift_phi_pos
    (hconn : N.IsConnected) (hcrp : N.HasCRP)
    {S : Finset Buffer} (hne : S.Nonempty)
    (hproper : S ≠ Finset.univ) :
    0 < N.cutDrift S N.phi := by
  let A := N.serversContainedIn S
  have hAproper : A ≠ Finset.univ :=
    N.serversContainedIn_ne_univ hproper
  by_cases hmu : 0 < N.netServiceRate A
  · have hlimited : N.IsLimitedSet A := ⟨hAproper, hmu⟩
    have hstrict :
        0 < N.netArrivalRate A - N.netServiceRate A := by
      linarith [hcrp A hlimited]
    exact hstrict.trans_le (N.cutDifference_le_cutDrift S)
  · have hmuzero : N.netServiceRate A = 0 := by
      have hnonneg := N.netServiceRate_nonneg A
      linarith
    have houtzero : N.crossingOutflow S N.phi = 0 := by
      have hle := N.crossingOutflow_le_netServiceRate S
      have hnonneg : 0 ≤ N.crossingOutflow S N.phi := by
        apply Finset.sum_nonneg
        intro j hj
        exact Finset.sum_nonneg fun k hk => N.phi_nonneg j k
      rw [hmuzero] at hle
      exact le_antisymm hle hnonneg
    rw [N.cutDrift_eq_crossing, houtzero, sub_zero]
    exact N.crossingInflow_pos_of_connected hconn hne hproper

/-- The finite family of nonempty proper buffer cuts. -/
def properBufferCuts : Finset (Finset Buffer) :=
  Finset.univ.filter fun S => S.Nonempty ∧ S ≠ Finset.univ

@[simp]
theorem mem_properBufferCuts (S : Finset Buffer) :
    S ∈ properBufferCuts (Buffer := Buffer) ↔
      S.Nonempty ∧ S ≠ Finset.univ := by
  simp [properBufferCuts]

theorem properBufferCuts_nonempty [Nontrivial Buffer] :
    (properBufferCuts (Buffer := Buffer)).Nonempty := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne Buffer
  refine ⟨{a}, ?_⟩
  rw [mem_properBufferCuts]
  refine ⟨Finset.singleton_nonempty a, ?_⟩
  intro h
  have hb : b ∈ ({a} : Finset Buffer) := by
    rw [h]
    simp
  exact hab (Finset.mem_singleton.1 hb).symm

/-- The source's finite minimum `g₀ = min_S D_S(phi)`.

The fallback value only totalizes the definition when there are no nonempty
proper cuts; all gap theorems below assume `Nontrivial Buffer`.
-/
noncomputable def minimumCutDriftGap : ℝ :=
  if h : (properBufferCuts (Buffer := Buffer)).Nonempty then
    (properBufferCuts (Buffer := Buffer)).inf' h
      (fun S => N.cutDrift S N.phi)
  else
    0

theorem minimumCutDriftGap_pos [Nontrivial Buffer]
    (hconn : N.IsConnected) (hcrp : N.HasCRP) :
    0 < N.minimumCutDriftGap := by
  classical
  have hcuts := properBufferCuts_nonempty (Buffer := Buffer)
  rw [minimumCutDriftGap, dif_pos hcuts]
  obtain ⟨S, hSmem, hSeq⟩ :=
    Finset.exists_mem_eq_inf' hcuts (fun S => N.cutDrift S N.phi)
  rw [hSeq]
  exact N.cutDrift_phi_pos hconn hcrp
    ((mem_properBufferCuts S).1 hSmem).1
    ((mem_properBufferCuts S).1 hSmem).2

omit [DecidableEq Server] in
theorem minimumCutDriftGap_le [Nontrivial Buffer]
    {S : Finset Buffer} (hS : S.Nonempty)
    (hproper : S ≠ Finset.univ) :
    N.minimumCutDriftGap ≤ N.cutDrift S N.phi := by
  classical
  have hcuts := properBufferCuts_nonempty (Buffer := Buffer)
  rw [minimumCutDriftGap, dif_pos hcuts]
  exact Finset.inf'_le _ ((mem_properBufferCuts S).2 ⟨hS, hproper⟩)

omit [DecidableEq Server] in
private theorem continuous_cutDrift (S : Finset Buffer) :
    Continuous (N.cutDrift S) := by
  unfold cutDrift
  fun_prop

/-- Robust finite-gap form of the appendix argument.  The pointwise bound
`|f j k - phi j k| < epsilon` is exactly the open infinity-norm
neighborhood in this finite-dimensional matrix space.
-/
theorem exists_uniform_cutDrift_gap [Nontrivial Buffer]
    (hconn : N.IsConnected) (hcrp : N.HasCRP) :
    ∃ g₀ > 0, ∃ ε > 0,
      g₀ = N.minimumCutDriftGap ∧
      ∀ (f : Server → Buffer → ℝ),
        (∀ j k, |f j k - N.phi j k| < ε) →
        ∀ S : Finset Buffer, S.Nonempty → S ≠ Finset.univ →
          g₀ / 2 ≤ N.cutDrift S f := by
  classical
  let cuts := properBufferCuts (Buffer := Buffer)
  let good : Set (Server → Buffer → ℝ) :=
    {f | ∀ S ∈ cuts, N.minimumCutDriftGap / 2 < N.cutDrift S f}
  have hopen : IsOpen good := by
    rw [show good =
        ⋂ S ∈ cuts,
          {f | N.minimumCutDriftGap / 2 < N.cutDrift S f} by
      ext f
      simp [good]]
    exact isOpen_biInter_finset fun S hS =>
      isOpen_lt continuous_const (N.continuous_cutDrift S)
  have hphi : N.phi ∈ good := by
    intro S hS
    have hgap_le : N.minimumCutDriftGap ≤ N.cutDrift S N.phi :=
      N.minimumCutDriftGap_le
        ((mem_properBufferCuts S).1 hS).1
        ((mem_properBufferCuts S).1 hS).2
    have hgap_pos := N.minimumCutDriftGap_pos hconn hcrp
    linarith
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.1 hopen N.phi hphi
  refine ⟨N.minimumCutDriftGap,
    N.minimumCutDriftGap_pos hconn hcrp, ε, hε, rfl, ?_⟩
  intro f hf S hS hproper
  have hdist : dist f N.phi < ε := by
    rw [dist_pi_lt_iff hε]
    intro j
    rw [dist_pi_lt_iff hε]
    intro k
    simpa [Real.dist_eq] using hf j k
  have hfgood : f ∈ good := hball hdist
  exact (hfgood S ((mem_properBufferCuts S).2 ⟨hS, hproper⟩)).le

end StateDepMOR.Network
