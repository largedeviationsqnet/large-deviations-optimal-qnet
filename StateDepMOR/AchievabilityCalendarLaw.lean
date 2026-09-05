import StateDepMOR.AchievabilityCalendarGrid
import StateDepMOR.AchievabilityCalendarPMF

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace StateDepMOR.Achievability.CalendarLaw

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : StateDepMOR.Network Buffer Server)

theorem gridIncrementArray_mem_gridAtoms_of_cell_length_le_one
    (K : PNat) {H : Real} (hH : 0 < H)
    {m : Nat} (hm : 0 < m)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (hself :
      StateDepMOR.Network.totalCalendarPoissonSample omega = omega)
    (hsimple : forall i : Fin m,
      (gridCellTokens N K H m omega i).length <= 1) :
    gridIncrementArray N K H m omega ∈
      gridAtoms (Buffer := Buffer) (Server := Server)
        (N.totalCalendarTokenPrefix K omega H) m := by
  classical
  letI : Inhabited Buffer :=
    ⟨Classical.choice (inferInstance : Nonempty Buffer)⟩
  letI : Inhabited Server :=
    ⟨Classical.choice (inferInstance : Nonempty Server)⟩
  let cells : Fin m ->
      List (Token (Buffer := Buffer) (Server := Server)) :=
    fun i => gridCellTokens N K H m omega i
  let S : Finset (Fin m) :=
    Finset.univ.filter fun i => (cells i).length = 1
  let mark : Fin m ->
      Token (Buffer := Buffer) (Server := Server) :=
    fun i => (cells i).head?.getD default
  have hcell (i : Fin m) :
      cells i = if i ∈ S then [mark i] else [] := by
    by_cases hi : i ∈ S
    · have hlen : (cells i).length = 1 := by
        simpa [S] using hi
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
      rw [if_pos hi, ha]
      simp [mark, ha]
    · have hlen_ne : (cells i).length ≠ 1 := by
        simpa [S] using hi
      have hlen_zero : (cells i).length = 0 := by
        have := hsimple i
        change (cells i).length <= 1 at this
        omega
      rw [if_neg hi, List.eq_nil_of_length_eq_zero hlen_zero]
  have hflat_aux (l : List (Fin m)) :
      (l.map cells).flatten =
        (l.filter fun i => i ∈ S).map mark := by
    induction l with
    | nil => simp
    | cons i l ih =>
        by_cases hi : i ∈ S
        · simp [hcell i, hi, ih]
        · simp [hcell i, hi, ih]
  have hsorted :
      ((Finset.univ : Finset (Fin m)).sort (fun a b => a <= b)).filter
          (fun i => i ∈ S) =
        S.sort (fun a b => a <= b) := by
    apply List.Pairwise.eq_of_mem_iff
      (r := fun a b : Fin m => a < b)
    · exact List.Pairwise.filter _
        (Finset.univ : Finset (Fin m)).sortedLT_sort.pairwise
    · exact S.sortedLT_sort.pairwise
    · intro i
      simp
  have hflat :
      (List.ofFn cells).flatten =
        (S.sort (fun a b => a <= b)).map mark := by
    rw [List.ofFn_eq_map]
    rw [← Fin.sort_univ m]
    rw [hflat_aux, hsorted]
  have hordered (hcard :
      S.card = (N.totalCalendarTokenPrefix K omega H).length) :
      List.ofFn
          (fun r =>
            mark ((S.orderIsoOfFin hcard r : S) : Fin m)) =
        (S.sort (fun a b => a <= b)).map mark := by
    rw [List.ofFn_eq_map]
    change
      (List.finRange
          (N.totalCalendarTokenPrefix K omega H).length).map
          (fun r => mark (S.orderEmbOfFin hcard r)) =
        (S.sort (fun a b => a <= b)).map mark
    rw [show
      (fun r => mark (S.orderEmbOfFin hcard r)) =
        mark ∘ S.orderEmbOfFin hcard by rfl]
    rw [← List.map_map]
    exact congrArg (List.map mark)
      (Finset.listMap_orderEmbOfFin_finRange S hcard)
  have hprefix :
      N.totalCalendarTokenPrefix K omega H =
        (S.sort (fun a b => a <= b)).map mark := by
    rw [← hflat]
    change
      N.totalCalendarTokenPrefix K omega H =
        (List.ofFn fun i : Fin m =>
          gridCellTokens N K H m omega i).flatten
    exact (flatten_gridCellTokens N K hH.le hm omega).symm
  have hcard :
      S.card = (N.totalCalendarTokenPrefix K omega H).length := by
    rw [hprefix, List.length_map, Finset.length_sort]
  have hprefix_ordered :
      N.totalCalendarTokenPrefix K omega H =
        List.ofFn
          (fun r =>
            mark ((S.orderIsoOfFin hcard r : S) : Fin m)) := by
    exact hprefix.trans (hordered hcard).symm
  unfold gridAtoms
  rw [Finset.mem_image]
  let A : {T : Finset (Fin m) //
      T ∈ Finset.univ.powersetCard
        (N.totalCalendarTokenPrefix K omega H).length} :=
    ⟨S, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ S, hcard⟩⟩
  refine ⟨A, Finset.mem_univ A, ?_⟩
  change
    gridAtom (N.totalCalendarTokenPrefix K omega H) m S hcard =
      gridIncrementArray N K H m omega
  funext p i
  have hcount :
      (cells i).count (p.1, p.2) =
        gridIncrementArray N K H m omega p i := by
    simpa [cells, gridIncrementArray, hself] using
      gridCellTokens_count N K hH.le m omega i p.1 p.2
  by_cases hi : i ∈ S
  · have htoken :
        listToken (N.totalCalendarTokenPrefix K omega H)
            ((S.orderIsoOfFin hcard).symm ⟨i, hi⟩) =
          mark i := by
      unfold listToken
      have hget := List.get_of_eq hprefix_ordered
        ((S.orderIsoOfFin hcard).symm ⟨i, hi⟩)
      rw [List.get_ofFn] at hget
      calc
        (N.totalCalendarTokenPrefix K omega H).get
            ((S.orderIsoOfFin hcard).symm ⟨i, hi⟩) =
            _ := hget
        _ = mark
            ((S.orderIsoOfFin hcard
              ((S.orderIsoOfFin hcard).symm ⟨i, hi⟩) : S) :
              Fin m) := by
          congr 3
        _ = mark i := by
          rw [(S.orderIsoOfFin hcard).apply_symm_apply ⟨i, hi⟩]
    simp only [gridAtom, dif_pos hi, htoken]
    rw [← hcount, hcell i, if_pos hi]
    by_cases hp : (p.1, p.2) = mark i
    · simp [hp]
    · have hrev : mark i ≠ (p.1, p.2) := Ne.symm hp
      simp [hp, hrev]
  · simp only [gridAtom, dif_neg hi]
    rw [← hcount, hcell i, if_neg hi]
    simp

theorem gridAtom_injective_tokens
    {m : Nat}
    (tokens tokens' :
      List (Token (Buffer := Buffer) (Server := Server)))
    (S T : Finset (Fin m))
    (hS : S.card = tokens.length)
    (hT : T.card = tokens'.length)
    (h :
      gridAtom tokens m S hS =
        gridAtom tokens' m T hT) :
    tokens = tokens' := by
  have hST : S = T := by
    ext i
    rw [← gridAtom_occupied_iff tokens m S hS i,
      ← gridAtom_occupied_iff tokens' m T hT i]
    constructor
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_⟩
      rw [← h]
      exact hp
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_⟩
      rw [h]
      exact hp
  subst T
  have hlen : tokens.length = tokens'.length := hS.symm.trans hT
  apply List.ext_get hlen
  intro n hn hn'
  let r : Fin tokens.length := ⟨n, hn⟩
  let i : S := S.orderIsoOfFin hS r
  let p : Coord (Buffer := Buffer) (Server := Server) :=
    ⟨(listToken tokens r).1, (listToken tokens r).2⟩
  have hleft : gridAtom tokens m S hS p i = 1 := by
    have hinv : (S.orderIsoOfFin hS).symm i = r :=
      (S.orderIsoOfFin hS).symm_apply_apply r
    simp only [gridAtom, dif_pos i.2, hinv, if_pos, p]
  have hright : gridAtom tokens' m S hT p i = 1 := by
    rw [← h]
    exact hleft
  have hi : (i : Fin m) ∈ S := i.2
  have hmark :
      (p.1, p.2) =
        listToken tokens'
          ((S.orderIsoOfFin hT).symm i) := by
    simp only [gridAtom, dif_pos hi] at hright
    by_contra hne
    simp [hne] at hright
  have hrank :
      (((S.orderIsoOfFin hT).symm i).val : Nat) = n := by
    calc
      (((S.orderIsoOfFin hT).symm i).val : Nat) =
          S.sort.idxOf (i : Fin m) :=
        Finset.orderIsoOfFin_symm_apply S hT i
      _ = (((S.orderIsoOfFin hS).symm i).val : Nat) :=
        (Finset.orderIsoOfFin_symm_apply S hS i).symm
      _ = n := by
        rw [show (S.orderIsoOfFin hS).symm i = r by
          exact (S.orderIsoOfFin hS).symm_apply_apply r]
  have hrankFin :
      (S.orderIsoOfFin hT).symm i = ⟨n, hn'⟩ :=
    Fin.ext hrank
  change listToken tokens r = listToken tokens' ⟨n, hn'⟩
  rw [← hrankFin, ← hmark]

theorem gridAtoms_token_injective
    {m : Nat}
    {tokens tokens' :
      List (Token (Buffer := Buffer) (Server := Server))}
    {z : Coord (Buffer := Buffer) (Server := Server) -> Fin m -> Nat}
    (hz : z ∈
      gridAtoms (Buffer := Buffer) (Server := Server) tokens m)
    (hz' : z ∈
      gridAtoms (Buffer := Buffer) (Server := Server) tokens' m) :
    tokens = tokens' := by
  classical
  unfold gridAtoms at hz hz'
  rw [Finset.mem_image] at hz hz'
  obtain ⟨S, _hS, hSz⟩ := hz
  obtain ⟨T, _hT, hTz⟩ := hz'
  exact gridAtom_injective_tokens
    tokens tokens' S.1 T.1
      ((Finset.mem_powersetCard.mp S.2).2)
      ((Finset.mem_powersetCard.mp T.2).2)
      (hSz.trans hTz.symm)

theorem eventually_gridRealizes_iff_calendarTokenPrefix_eq
    (K : PNat) {H : Real} (hH : 0 < H)
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (hself :
      StateDepMOR.Network.totalCalendarPoissonSample omega = omega)
    (hregular : StateDepMOR.PoissonSamplePath.IsRegularSample omega)
    (hcross : forall j k j' k',
      0 < N.phi j k -> 0 < N.phi j' k' ->
      (j, k) ≠ (j', k') -> forall r q,
        N.calendarEventTime K omega ((j, k), r) ≠
          N.calendarEventTime K omega ((j', k'), q)) :
    Filter.Eventually (fun m : Nat =>
      omega ∈ gridRealizes N K H tokens m <->
        N.calendarTokenPrefix K omega H = tokens) atTop := by
  have horiginal :
      N.totalCalendarTokenPrefix K omega H =
        N.calendarTokenPrefix K omega H :=
    totalCalendarTokenPrefix_eq_original_of_regular
      N K omega H hself hregular hcross
  filter_upwards
    [eventually_gridCellEvents_length_le_one
      N K hH omega hself hregular hcross,
      eventually_ge_atTop 1] with m hsimple hm
  have hcellSimple : forall i : Fin m,
      (gridCellTokens N K H m omega i).length <= 1 := by
    intro i
    simpa [gridCellTokens] using hsimple i
  have hactual :
      gridIncrementArray N K H m omega ∈
        gridAtoms (Buffer := Buffer) (Server := Server)
          (N.totalCalendarTokenPrefix K omega H) m :=
    gridIncrementArray_mem_gridAtoms_of_cell_length_le_one
      N K hH hm omega hself hcellSimple
  change
    gridIncrementArray N K H m omega ∈
        gridAtoms (Buffer := Buffer) (Server := Server) tokens m <->
      N.calendarTokenPrefix K omega H = tokens
  constructor
  · intro htarget
    have heq :
        tokens = N.totalCalendarTokenPrefix K omega H :=
      gridAtoms_token_injective htarget hactual
    exact horiginal.symm.trans heq.symm
  · intro heq
    rw [← heq, ← horiginal]
    exact hactual

theorem gridRealizes_ae_eventually_iff_calendarTokenPrefix_eq
    (K : PNat) {H : Real} (hH : 0 < H)
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) :
    Filter.Eventually
      (fun omega : Sample (Buffer := Buffer) (Server := Server) =>
        Filter.Eventually (fun m : Nat =>
          omega ∈ gridRealizes N K H tokens m <->
            N.calendarTokenPrefix K omega H = tokens) atTop)
      (MeasureTheory.ae N.calendarPoissonMeasure) := by
  letI : LinearOrder Buffer :=
    LinearOrder.lift' (Fintype.equivFin Buffer)
      (Fintype.equivFin Buffer).injective
  filter_upwards
    [N.totalCalendarPoissonSample_ae_eq_apply,
      StateDepMOR.PoissonSamplePath.regularSample_ae N,
      StateDepMOR.PaperStatements.Network.all_calendarEventTime_crossCoordinate_ne_ae
        N] with
      omega hself hregular hcross
  exact eventually_gridRealizes_iff_calendarTokenPrefix_eq
    N K hH tokens omega hself hregular (hcross K)

theorem calendarTokenPrefix_fiber_nullMeasurable
    (K : PNat) {H : Real} (hH : 0 < H)
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) :
    NullMeasurableSet
      {omega : Sample (Buffer := Buffer) (Server := Server) |
        N.calendarTokenPrefix K omega H = tokens}
      N.calendarPoissonMeasure := by
  refine nullMeasurableSet_of_tendsto_indicator
    (A := {omega : Sample (Buffer := Buffer) (Server := Server) |
      N.calendarTokenPrefix K omega H = tokens})
    (As := fun m : Nat => gridRealizes N K H tokens m)
    atTop ?_ ?_
  · intro m
    exact (measurableSet_gridRealizes N K H tokens m).nullMeasurableSet
  · exact gridRealizes_ae_eventually_iff_calendarTokenPrefix_eq
      N K hH tokens

theorem calendarTokenPrefix_fiber_measureReal
    (K : PNat) {H : Real} (hH : 0 < H)
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) :
    N.calendarPoissonMeasure.real
        {omega : Sample (Buffer := Buffer) (Server := Server) |
          N.calendarTokenPrefix K omega H = tokens} =
      Real.exp (-(((K : Nat) : Real) * H)) *
        ((((K : Nat) : Real) * H) ^ tokens.length /
          Nat.factorial tokens.length) *
        tokenWeightProduct N tokens := by
  let A : Set (Sample (Buffer := Buffer) (Server := Server)) :=
    {omega | N.calendarTokenPrefix K omega H = tokens}
  let As : Nat -> Set (Sample (Buffer := Buffer) (Server := Server)) :=
    fun m => gridRealizes N K H tokens m
  have hlim :
      Filter.Eventually
        (fun omega : Sample (Buffer := Buffer) (Server := Server) =>
          Filter.Eventually (fun m : Nat =>
            omega ∈ As m <-> omega ∈ A) atTop)
        (MeasureTheory.ae N.calendarPoissonMeasure) := by
    simpa [A, As] using
      gridRealizes_ae_eventually_iff_calendarTokenPrefix_eq
        N K hH tokens
  have hnull : NullMeasurableSet A N.calendarPoissonMeasure := by
    simpa [A] using
      calendarTokenPrefix_fiber_nullMeasurable N K hH tokens
  let A' := toMeasurable N.calendarPoissonMeasure A
  have hAA' : A' =ᵐ[N.calendarPoissonMeasure] A :=
    hnull.toMeasurable_ae_eq
  have hlim' :
      Filter.Eventually
        (fun omega : Sample (Buffer := Buffer) (Server := Server) =>
          Filter.Eventually (fun m : Nat =>
            omega ∈ As m <-> omega ∈ A') atTop)
        (MeasureTheory.ae N.calendarPoissonMeasure) := by
    filter_upwards [hlim, hAA'.mem_iff] with omega homega hmem
    filter_upwards [homega] with m hm
    exact hm.trans hmem.symm
  have hmeasure :
      Tendsto
        (fun m => N.calendarPoissonMeasure (As m))
        atTop
        (nhds (N.calendarPoissonMeasure A')) :=
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
      atTop
      (measurableSet_toMeasurable N.calendarPoissonMeasure A)
      (fun m => measurableSet_gridRealizes N K H tokens m)
      hlim'
  have hreal :
      Tendsto
        (fun m => N.calendarPoissonMeasure.real (As m))
        atTop
        (nhds (N.calendarPoissonMeasure.real A')) := by
    simpa only [measureReal_def, Function.comp_def] using
      (ENNReal.tendsto_toReal
        (measure_ne_top N.calendarPoissonMeasure A')).comp hmeasure
  have hformula :=
    tendsto_gridRealizes_measureReal N K hH tokens
  have hvalue :
      N.calendarPoissonMeasure.real A' =
        Real.exp (-(((K : Nat) : Real) * H)) *
          ((((K : Nat) : Real) * H) ^ tokens.length /
            Nat.factorial tokens.length) *
          tokenWeightProduct N tokens :=
    tendsto_nhds_unique
      (by simpa [As] using hreal)
      hformula
  change N.calendarPoissonMeasure.real A = _
  have hrealAA' :
      N.calendarPoissonMeasure.real A' =
        N.calendarPoissonMeasure.real A :=
    congrArg ENNReal.toReal (measure_congr hAA')
  exact hrealAA'.symm.trans hvalue

noncomputable def calendarTokenListLaw
    (K : PNat) (H : Real) :
    PMF (List (Token (Buffer := Buffer) (Server := Server))) :=
  StateDepMOR.PaperStatements.Network.calendarBlockCountLaw K H |>.bind
    fun n => (N.tokenVectorLaw n).map List.ofFn

private theorem tokenVectorLaw_map_ofFn_apply_toReal
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) :
    (((N.tokenVectorLaw tokens.length).map List.ofFn) tokens).toReal =
      tokenWeightProduct N tokens := by
  rw [PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single tokens.get]
  · rw [if_pos (List.ofFn_get tokens).symm]
    rw [N.tokenVectorLaw_apply_toReal]
    simp_rw [N.tokenLaw_toReal]
    rfl
  · intro candidate _hcandidate hne
    have hnot : Not (tokens = List.ofFn candidate) := by
      intro heq
      apply hne
      apply List.ofFn_injective
      rw [← heq, List.ofFn_get]
    simp [hnot]
  · simp

private theorem tokenVectorLaw_map_ofFn_apply_eq_zero_of_length_ne
    {n : Nat}
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (hne : Not (n = tokens.length)) :
    ((N.tokenVectorLaw n).map List.ofFn) tokens = 0 := by
  rw [PMF.map_apply]
  rw [ENNReal.tsum_eq_zero]
  intro candidate
  have hnot : Not (tokens = List.ofFn candidate) := by
    intro candidate_eq
    apply hne
    have hlength := congrArg List.length candidate_eq
    simpa using hlength.symm
  simp [hnot]

theorem calendarTokenListLaw_apply_toReal
    (K : PNat) {H : Real} (hH : 0 <= H)
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) :
    (calendarTokenListLaw N K H tokens).toReal =
      Real.exp (-(((K : Nat) : Real) * H)) *
        ((((K : Nat) : Real) * H) ^ tokens.length /
          Nat.factorial tokens.length) *
        tokenWeightProduct N tokens := by
  unfold calendarTokenListLaw
  rw [PMF.bind_apply]
  rw [ENNReal.tsum_toReal_eq (fun n =>
    ENNReal.mul_ne_top
      ((StateDepMOR.PaperStatements.Network.calendarBlockCountLaw K H).apply_ne_top
        n)
      (((N.tokenVectorLaw n).map List.ofFn).apply_ne_top tokens))]
  simp_rw [ENNReal.toReal_mul]
  rw [tsum_eq_single tokens.length]
  · rw [StateDepMOR.PaperStatements.Network.calendarBlockCountLaw_apply_toReal
      K hH]
    rw [tokenVectorLaw_map_ofFn_apply_toReal N tokens]
    ring
  · intro n hne
    rw [tokenVectorLaw_map_ofFn_apply_eq_zero_of_length_ne
      N tokens hne]
    simp

theorem calendarTokenPrefix_aemeasurable
    (K : PNat) {H : Real} (hH : 0 < H) :
    @AEMeasurable
      (Sample (Buffer := Buffer) (Server := Server))
      (List (Token (Buffer := Buffer) (Server := Server)))
      Top.top
      _
      (fun omega => N.calendarTokenPrefix K omega H)
      (by exact N.calendarPoissonMeasure) := by
  letI : MeasurableSpace
      (List (Token (Buffer := Buffer) (Server := Server))) :=
    Top.top
  apply MeasureTheory.NullMeasurable.aemeasurable
  intro s _hs
  have hpreimage :
      (fun omega : Sample (Buffer := Buffer) (Server := Server) =>
        N.calendarTokenPrefix K omega H) ⁻¹' s =
      Set.iUnion fun tokens : s =>
        {omega : Sample (Buffer := Buffer) (Server := Server) |
          N.calendarTokenPrefix K omega H = tokens.1} := by
    ext omega
    simp
  rw [hpreimage]
  apply NullMeasurableSet.iUnion
  intro tokens
  exact calendarTokenPrefix_fiber_nullMeasurable
    N K hH tokens.1

theorem calendarTokenPrefix_hasLaw
    (K : PNat) {H : Real} (hH : 0 < H) :
    @HasLaw
      (Sample (Buffer := Buffer) (Server := Server))
      (List (Token (Buffer := Buffer) (Server := Server)))
      _
      Top.top
      (fun omega => N.calendarTokenPrefix K omega H)
      (@PMF.toMeasure
        (List (Token (Buffer := Buffer) (Server := Server)))
        Top.top
        (calendarTokenListLaw N K H))
      N.calendarPoissonMeasure := by
  letI : MeasurableSpace
      (List (Token (Buffer := Buffer) (Server := Server))) :=
    Top.top
  have hmeas := calendarTokenPrefix_aemeasurable N K hH
  refine ⟨hmeas, ?_⟩
  apply Measure.ext_of_measureReal_singleton
  intro tokens
  rw [measureReal_def,
    Measure.map_apply_of_aemeasurable hmeas (MeasurableSet.singleton tokens)]
  change
    (N.calendarPoissonMeasure
      ((fun omega => N.calendarTokenPrefix K omega H) ⁻¹' {tokens})).toReal =
      ((calendarTokenListLaw N K H).toMeasure {tokens}).toReal
  rw [PMF.toMeasure_apply_singleton
    (calendarTokenListLaw N K H) tokens MeasurableSet.of_discrete]
  change
    N.calendarPoissonMeasure.real
        {omega : Sample (Buffer := Buffer) (Server := Server) |
          N.calendarTokenPrefix K omega H = tokens} =
      (calendarTokenListLaw N K H tokens).toReal
  rw [calendarTokenPrefix_fiber_measureReal N K hH tokens,
    calendarTokenListLaw_apply_toReal N K hH.le tokens]

theorem calendarTokenListLaw_map_runTokens
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (countK : PNat) (H : Real) (x : JobState Buffer K) :
    (calendarTokenListLaw N countK H).map (N.runTokens U x) =
      StateDepMOR.PaperStatements.Network.poissonizedTokenEndpointLaw
        N U
          (StateDepMOR.PaperStatements.Network.calendarBlockCountLaw
            countK H)
          x := by
  unfold calendarTokenListLaw
    StateDepMOR.PaperStatements.Network.poissonizedTokenEndpointLaw
  rw [PMF.map_bind]
  apply congrArg
  funext n
  exact PMF.map_comp List.ofFn (N.tokenVectorLaw n) (N.runTokens U x)

end StateDepMOR.Achievability.CalendarLaw

namespace StateDepMOR.PaperStatements.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : StateDepMOR.Network Buffer Server)

theorem calendarBlockEndpoint_hasLaw
    {H : Real} (hH : 0 < H)
    (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat)) :
    @HasLaw
      (StateDepMOR.Network.CalendarPoissonSample
        (Buffer := Buffer) (Server := Server))
      (JobState Buffer (K : Nat))
      _
      Top.top
      (fun omega => calendarBlockEndpoint N K U x omega H)
      (@PMF.toMeasure
        (JobState Buffer (K : Nat))
        Top.top
        (randomizedEventEpochKernel N U
          (calendarBlockCountLaw K H) x))
      N.calendarPoissonMeasure := by
  letI : MeasurableSpace (List (Server × Buffer)) := Top.top
  letI : MeasurableSpace (JobState Buffer (K : Nat)) := Top.top
  have hprefix :=
    StateDepMOR.Achievability.CalendarLaw.calendarTokenPrefix_hasLaw
      N K hH
  have hrun :
      @Measurable
        (List (Server × Buffer))
        (JobState Buffer (K : Nat))
        Top.top
        _
        (N.runTokens U x) :=
    Measurable.of_discrete
  have hrunAE :
      AEMeasurable (N.runTokens U x)
        (N.calendarPoissonMeasure.map
          (fun omega => N.calendarTokenPrefix K omega H)) :=
    hrun.aemeasurable
  have hmapComp :=
    AEMeasurable.map_map_of_aemeasurable
      hrunAE hprefix.aemeasurable
  refine ⟨?_, ?_⟩
  · change
      AEMeasurable
        (fun omega =>
          N.runTokens U x (N.calendarTokenPrefix K omega H))
        N.calendarPoissonMeasure
    exact hrun.comp_aemeasurable hprefix.aemeasurable
  · change
      N.calendarPoissonMeasure.map
          (fun omega =>
            N.runTokens U x (N.calendarTokenPrefix K omega H)) =
        (randomizedEventEpochKernel N U
          (calendarBlockCountLaw K H) x).toMeasure
    calc
      N.calendarPoissonMeasure.map
          (fun omega =>
            N.runTokens U x (N.calendarTokenPrefix K omega H)) =
          (N.calendarPoissonMeasure.map
            (fun omega => N.calendarTokenPrefix K omega H)).map
              (N.runTokens U x) := hmapComp.symm
      _ =
          (StateDepMOR.Achievability.CalendarLaw.calendarTokenListLaw
            N K H).toMeasure.map (N.runTokens U x) := by
        rw [hprefix.map_eq]
      _ =
          ((StateDepMOR.Achievability.CalendarLaw.calendarTokenListLaw
            N K H).map (N.runTokens U x)).toMeasure :=
        PMF.toMeasure_map (N.runTokens U x)
          (StateDepMOR.Achievability.CalendarLaw.calendarTokenListLaw N K H)
          hrun
      _ =
          (poissonizedTokenEndpointLaw N U
            (calendarBlockCountLaw K H) x).toMeasure := by
        rw [StateDepMOR.Achievability.CalendarLaw.calendarTokenListLaw_map_runTokens
          N U K H x]
      _ =
          (randomizedEventEpochKernel N U
            (calendarBlockCountLaw K H) x).toMeasure := by
        rw [poissonizedTokenEndpointLaw_eq_randomizedEventEpochKernel]

private theorem pmfEventMass_eq_toMeasure_real_calendar
    {A : Type*} [Fintype A] [DecidableEq A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    (pi : PMF A) (P : A -> Prop) [DecidablePred P] :
    pmfEventMass pi P = pi.toMeasure.real {x | P x} := by
  classical
  let s : Finset A := Finset.univ.filter P
  have hset : {x : A | P x} = (s : Set A) := by
    ext x
    simp only [Set.mem_setOf_eq, Finset.mem_coe, s, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [hset, measureReal_def, PMF.toMeasure_apply_finset]
  rw [ENNReal.toReal_sum (fun x _ => pi.apply_ne_top x)]
  unfold pmfEventMass
  simp [s, Finset.sum_filter]

theorem pmfEventMass_randomizedEventEpochKernel_eq_calendarBlockEndpoint
    {H : Real} (hH : 0 < H)
    (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat))
    (Target : JobState Buffer (K : Nat) -> Prop)
    [DecidablePred Target] :
    pmfEventMass
        (randomizedEventEpochKernel N U
          (calendarBlockCountLaw K H) x)
        Target =
      N.calendarPoissonMeasure.real
        {omega | Target (calendarBlockEndpoint N K U x omega H)} := by
  classical
  letI : MeasurableSpace (JobState Buffer (K : Nat)) := Top.top
  rw [pmfEventMass_eq_toMeasure_real_calendar]
  exact
    (calendarBlockEndpoint_hasLaw N hH K U x).measureReal_eq
      MeasurableSet.of_discrete |>.symm

#check calendarBlockEndpoint_hasLaw
#check pmfEventMass_randomizedEventEpochKernel_eq_calendarBlockEndpoint

#print axioms calendarBlockEndpoint_hasLaw
#print axioms pmfEventMass_randomizedEventEpochKernel_eq_calendarBlockEndpoint

end StateDepMOR.PaperStatements.Network
