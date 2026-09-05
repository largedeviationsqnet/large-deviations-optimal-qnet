import StateDepMOR.AchievabilityCalendarBridge
import StateDepMOR.FluidExistenceProof
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace StateDepMOR.Achievability.CalendarLaw

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

variable (N : StateDepMOR.Network Buffer Server)

abbrev Coord := Sigma fun _ : Server => Buffer
abbrev Token := Server × Buffer
abbrev Sample :=
  StateDepMOR.Network.CalendarPoissonSample
    (Buffer := Buffer) (Server := Server)

/-- Uniform grid on `[0,H]`, with `m` positive-length cells. -/
noncomputable def uniformGrid (H : Real) (m : Nat) :
    Fin (m + 1) -> Real :=
  fun i => H * (i : Nat) / m

theorem uniformGrid_zero (H : Real) (m : Nat) :
    uniformGrid H m 0 = 0 := by
  simp [uniformGrid]

theorem uniformGrid_monotone {H : Real} (hH : 0 <= H) (m : Nat) :
    Monotone (uniformGrid H m) := by
  intro i j hij
  unfold uniformGrid
  gcongr
  exact_mod_cast hij

theorem uniformGrid_step (H : Real) (m : Nat) (i : Fin m) :
    uniformGrid H m i.succ - uniformGrid H m i.castSucc = H / m := by
  have hm : (m : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_zero_of_lt i.isLt)
  simp only [uniformGrid, Fin.val_succ, Fin.coe_castSucc,
    Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The mark in position `r` of a target list. -/
def listToken
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (r : Fin tokens.length) :
    Token (Buffer := Buffer) (Server := Server) :=
  tokens.get r

/-- Count array which puts the target marks into the cells in `S`, one mark
per cell and in increasing cell order. -/
def gridAtom
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (m : Nat)
    (S : Finset (Fin m)) (hS : S.card = tokens.length) :
    Coord (Buffer := Buffer) (Server := Server) -> Fin m -> Nat :=
  fun p i =>
    if hi : i ∈ S then
      if (p.1, p.2) =
          listToken tokens ((S.orderIsoOfFin hS).symm ⟨i, hi⟩)
      then 1 else 0
    else 0

@[simp]
theorem gridAtom_eq_zero_of_not_mem
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) (m : Nat)
    (S : Finset (Fin m)) (hS : S.card = tokens.length)
    (p : Coord (Buffer := Buffer) (Server := Server)) (i : Fin m)
    (hi : i ∉ S) :
    gridAtom tokens m S hS p i = 0 := by
  simp [gridAtom, hi]

theorem gridAtom_selected
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) (m : Nat)
    (S : Finset (Fin m)) (hS : S.card = tokens.length)
    (r : Fin tokens.length) :
    gridAtom tokens m S hS
        ⟨(listToken tokens r).1, (listToken tokens r).2⟩
        (S.orderIsoOfFin hS r) = 1 := by
  have hi :
      (((S.orderIsoOfFin hS r : S) : Fin m)) ∈ S :=
    (S.orderIsoOfFin hS r).property
  simp only [gridAtom, dif_pos hi]
  have hidx :
      (S.orderIsoOfFin hS).symm
          ⟨((S.orderIsoOfFin hS r : S) : Fin m), hi⟩ = r := by
    apply (S.orderIsoOfFin hS).injective
    exact
      (S.orderIsoOfFin hS).apply_symm_apply
          ⟨((S.orderIsoOfFin hS r : S) : Fin m), hi⟩ |>.trans
        (Subtype.ext rfl)
  rw [hidx]
  simp

theorem gridAtom_occupied_iff
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) (m : Nat)
    (S : Finset (Fin m)) (hS : S.card = tokens.length) (i : Fin m) :
    (exists p : Coord (Buffer := Buffer) (Server := Server),
        gridAtom tokens m S hS p i = 1) <->
      i ∈ S := by
  constructor
  · rintro ⟨p, hp⟩
    by_contra hi
    rw [gridAtom_eq_zero_of_not_mem tokens m S hS p i hi] at hp
    omega
  · intro hi
    let r : Fin tokens.length :=
      (S.orderIsoOfFin hS).symm ⟨i, hi⟩
    let jk := listToken tokens r
    refine ⟨⟨jk.1, jk.2⟩, ?_⟩
    have hei :
        ((S.orderIsoOfFin hS r : S) : Fin m) = i := by
      exact congrArg Subtype.val
        ((S.orderIsoOfFin hS).apply_symm_apply ⟨i, hi⟩)
    rw [← hei]
    exact gridAtom_selected tokens m S hS r

theorem gridAtom_injective_on_set
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) (m : Nat)
    {S T : Finset (Fin m)}
    (hS : S.card = tokens.length) (hT : T.card = tokens.length)
    (h :
      gridAtom tokens m S hS =
        gridAtom tokens m T hT) :
    S = T := by
  ext i
  rw [← gridAtom_occupied_iff tokens m S hS i,
    ← gridAtom_occupied_iff tokens m T hT i]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rw [← h]
    exact hp
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    rw [h]
    exact hp

/-- The finite set of all simple-grid arrays realizing `tokens`. -/
noncomputable def gridAtoms
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (m : Nat) :
    Finset
      (Coord (Buffer := Buffer) (Server := Server) -> Fin m -> Nat) := by
  classical
  exact (Finset.univ.powersetCard tokens.length).attach.image
    (fun S =>
      gridAtom tokens m S.1
        ((Finset.mem_powersetCard.mp S.2).2))

theorem card_gridAtoms
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (m : Nat) :
    (gridAtoms (Buffer := Buffer) (Server := Server) tokens m).card =
      Nat.choose m tokens.length := by
  classical
  unfold gridAtoms
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_attach, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
  · intro S T h
    apply Subtype.ext
    apply gridAtom_injective_on_set tokens m
      ((Finset.mem_powersetCard.mp S.2).2)
      ((Finset.mem_powersetCard.mp T.2).2)
    exact h

/-- The complete marked-count increment array on the uniform grid. -/
noncomputable def gridIncrementArray
    (K : PNat) (H : Real) (m : Nat) (omega : Sample
      (Buffer := Buffer) (Server := Server)) :
    Coord (Buffer := Buffer) (Server := Server) -> Fin m -> Nat :=
  fun p =>
    N.calendarTokenIncrements K m (uniformGrid H m)
      omega p.1 p.2

/-- A grid realizes a target list when it has exactly one arrival in each
occupied cell, with the occupied-cell marks spelling the list in order. -/
noncomputable def gridRealizes
    (K : PNat) (H : Real)
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (m : Nat) : Set (Sample (Buffer := Buffer) (Server := Server)) :=
  {omega | gridIncrementArray N K H m omega ∈
    gridAtoms (Buffer := Buffer) (Server := Server) tokens m}

noncomputable def gridCellParameter
    (K : PNat) (H : Real) (hH : 0 <= H)
    (m : Nat) (p : Coord (Buffer := Buffer) (Server := Server)) : NNReal :=
  ⟨((K : Nat) : Real) * N.phi p.1 p.2 * (H / m),
    mul_nonneg
      (mul_nonneg (by positivity) (N.phi_nonneg p.1 p.2))
      (div_nonneg hH (Nat.cast_nonneg m))⟩

noncomputable def gridIncrementLaw
    (K : PNat) (H : Real) (hH : 0 <= H) (m : Nat) :
    Measure
      (Coord (Buffer := Buffer) (Server := Server) -> Fin m -> Nat) :=
  Measure.pi fun p =>
    Measure.pi fun _ : Fin m =>
      poissonMeasure (gridCellParameter N K H hH m p)

theorem calendarTokenIncrementParameter_uniformGrid
    (K : PNat) (H : Real) (hH : 0 <= H)
    (m : Nat) (p : Coord (Buffer := Buffer) (Server := Server))
    (i : Fin m) :
    N.calendarTokenIncrementParameter K m (uniformGrid H m)
        (uniformGrid_monotone hH m) p.1 p.2 i =
      gridCellParameter N K H hH m p := by
  apply NNReal.eq
  change
    ((K : Nat) : Real) * N.phi p.1 p.2 *
        (uniformGrid H m i.succ - uniformGrid H m i.castSucc) =
      ((K : Nat) : Real) * N.phi p.1 p.2 * (H / m)
  rw [uniformGrid_step]

theorem gridIncrementArray_hasLaw
    (K : PNat) {H : Real} (hH : 0 <= H) (m : Nat) :
    HasLaw
      (gridIncrementArray N K H m)
      (gridIncrementLaw N K H hH m)
      N.calendarPoissonMeasure := by
  have h :=
    N.calendarTokenIncrements_joint_hasLaw K m
      (uniformGrid H m)
      (by simp [uniformGrid])
      (uniformGrid_monotone hH m)
  have hlaw :
      gridIncrementLaw N K H hH m =
        Measure.pi fun p =>
          Measure.pi fun i =>
            poissonMeasure
              (N.calendarTokenIncrementParameter K m
                (uniformGrid H m) (uniformGrid_monotone hH m)
                p.1 p.2 i) := by
    unfold gridIncrementLaw
    apply congrArg Measure.pi
    funext p
    apply congrArg Measure.pi
    funext i
    rw [calendarTokenIncrementParameter_uniformGrid N K H hH m p i]
  rw [hlaw]
  exact h

theorem measurable_gridIncrementArray
    (K : PNat) (H : Real) (m : Nat) :
    Measurable (gridIncrementArray N K H m) := by
  rw [measurable_pi_iff]
  intro p
  exact N.measurable_calendarTokenIncrements K m
    (uniformGrid H m) p.1 p.2

theorem measurableSet_gridRealizes
    (K : PNat) (H : Real)
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (m : Nat) :
    MeasurableSet (gridRealizes N K H tokens m) := by
  unfold gridRealizes
  exact MeasurableSet.preimage
    MeasurableSet.of_discrete
    (measurable_gridIncrementArray N K H m)

theorem gridRealizes_measureReal_eq_law
    (K : PNat) {H : Real} (hH : 0 <= H)
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (m : Nat) :
    N.calendarPoissonMeasure.real (gridRealizes N K H tokens m) =
      (gridIncrementLaw N K H hH m).real
        (gridAtoms (Buffer := Buffer) (Server := Server) tokens m) := by
  exact (gridIncrementArray_hasLaw N K hH m).measureReal_eq
    MeasurableSet.of_discrete

theorem gridIncrementLaw_real_singleton
    (K : PNat) (H : Real) (hH : 0 <= H) (m : Nat)
    (z : Coord (Buffer := Buffer) (Server := Server) -> Fin m -> Nat) :
    (gridIncrementLaw N K H hH m).real {z} =
      ∏ p : Coord (Buffer := Buffer) (Server := Server),
        ∏ i : Fin m,
          (Real.exp (-(gridCellParameter N K H hH m p : Real)) *
            (gridCellParameter N K H hH m p : Real) ^ z p i /
            Nat.factorial (z p i)) := by
  unfold gridIncrementLaw
  rw [Measure.real_def, Measure.pi_singleton, ENNReal.toReal_prod]
  congr 1
  funext p
  rw [Measure.pi_singleton, ENNReal.toReal_prod]
  congr 1
  funext i
  rw [poissonMeasure_singleton,
    ENNReal.toReal_ofReal (by positivity)]

theorem prod_coord_eq
    (q : Coord (Buffer := Buffer) (Server := Server) -> Real)
    (jk : Token (Buffer := Buffer) (Server := Server)) :
    (∏ p : Coord (Buffer := Buffer) (Server := Server),
        if (p.1, p.2) = jk then q p else 1) =
      q ⟨jk.1, jk.2⟩ := by
  rcases jk with ⟨j, k⟩
  rw [Fintype.prod_sigma]
  simp only [Prod.mk.injEq]
  calc
    (∏ j' : Server, ∏ k' : Buffer,
        if j' = j /\ k' = k then q ⟨j', k'⟩ else 1) =
        ∏ j' : Server,
          if j' = j then
            (∏ k' : Buffer,
              if k' = k then q ⟨j', k'⟩ else 1)
          else 1 := by
      apply Fintype.prod_congr
      intro j'
      by_cases hj : j' = j
      · simp [hj]
      · simp [hj]
    _ = q ⟨j, k⟩ := by simp

theorem prod_ordered_cells
    {M : Type*} [CommMonoid M]
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (m : Nat) (S : Finset (Fin m)) (hS : S.card = tokens.length)
    (q : Token (Buffer := Buffer) (Server := Server) -> M) :
    (∏ i : S,
        q (listToken tokens ((S.orderIsoOfFin hS).symm i))) =
      ∏ r : Fin tokens.length, q (listToken tokens r) := by
  have h :=
    (S.orderIsoOfFin hS).toEquiv.prod_comp
      (fun i : S =>
        q (listToken tokens ((S.orderIsoOfFin hS).symm i)))
  simpa using h.symm

noncomputable def tokenWeightProduct
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) : Real :=
  ∏ r : Fin tokens.length,
    N.phi (listToken tokens r).1 (listToken tokens r).2

theorem sum_gridCellParameter
    (K : PNat) (H : Real) (hH : 0 <= H) (m : Nat) :
    (∑ p : Coord (Buffer := Buffer) (Server := Server),
        (gridCellParameter N K H hH m p : Real)) =
      ((K : Nat) : Real) * H / m := by
  change
    (∑ p : Sigma fun _ : Server => Buffer,
      ((K : Nat) : Real) * N.phi p.1 p.2 * (H / m)) =
        ((K : Nat) : Real) * H / m
  rw [Fintype.sum_sigma]
  calc
    (∑ j : Server, ∑ k : Buffer,
        ((K : Nat) : Real) * N.phi j k * (H / m)) =
        ∑ j : Server,
          (((K : Nat) : Real) *
            (∑ k : Buffer, N.phi j k) * (H / m)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.mul_sum]
    _ =
        ((K : Nat) : Real) *
          (∑ j : Server, ∑ k : Buffer, N.phi j k) *
          (H / m) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.mul_sum]
    _ = ((K : Nat) : Real) * H / m := by
      rw [N.total_rate]
      ring

theorem gridAtom_cell_factor
    (K : PNat) (H : Real) (hH : 0 <= H) (m : Nat)
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (S : Finset (Fin m)) (hS : S.card = tokens.length)
    (p : Coord (Buffer := Buffer) (Server := Server)) (i : Fin m) :
    (Real.exp (-(gridCellParameter N K H hH m p : Real)) *
        (gridCellParameter N K H hH m p : Real) ^
          gridAtom tokens m S hS p i /
        Nat.factorial (gridAtom tokens m S hS p i)) =
      Real.exp (-(gridCellParameter N K H hH m p : Real)) *
        if hi : i ∈ S then
          if (p.1, p.2) =
              listToken tokens ((S.orderIsoOfFin hS).symm ⟨i, hi⟩)
          then (gridCellParameter N K H hH m p : Real)
          else 1
        else 1 := by
  by_cases hi : i ∈ S
  · by_cases hp :
      (p.1, p.2) =
        listToken tokens ((S.orderIsoOfFin hS).symm ⟨i, hi⟩)
    · simp [gridAtom, hi, hp]
    · simp [gridAtom, hi, hp]
  · simp [gridAtom, hi]

theorem prod_gridCell_exp
    (K : PNat) (H : Real) (hH : 0 <= H)
    {m : Nat} (hm : 0 < m) :
    (∏ p : Coord (Buffer := Buffer) (Server := Server),
        ∏ _i : Fin m,
          Real.exp (-(gridCellParameter N K H hH m p : Real))) =
      Real.exp (-(((K : Nat) : Real) * H)) := by
  let q := fun p : Coord (Buffer := Buffer) (Server := Server) =>
    (gridCellParameter N K H hH m p : Real)
  calc
    (∏ p, ∏ _i : Fin m, Real.exp (-q p)) =
        ∏ _i : Fin m, ∏ p, Real.exp (-q p) := by
      exact Finset.prod_comm
    _ = ∏ _i : Fin m, Real.exp (-(∑ p, q p)) := by
      apply Fintype.prod_congr
      intro i
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.sum_neg_distrib]
    _ = (Real.exp (-(((K : Nat) : Real) * H / m))) ^ m := by
      rw [sum_gridCellParameter N K H hH m]
      simp
    _ = Real.exp (-(((K : Nat) : Real) * H)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      have hm0 : (m : Real) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp

theorem prod_gridAtom_selected_factors
    (K : PNat) (H : Real) (hH : 0 <= H)
    {m : Nat} (hm : 0 < m)
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (S : Finset (Fin m)) (hS : S.card = tokens.length) :
    (∏ p : Coord (Buffer := Buffer) (Server := Server),
      ∏ i : Fin m,
        if hi : i ∈ S then
          if (p.1, p.2) =
              listToken tokens ((S.orderIsoOfFin hS).symm ⟨i, hi⟩)
          then (gridCellParameter N K H hH m p : Real)
          else 1
        else 1) =
      ((((K : Nat) : Real) * H / m) ^ tokens.length) *
        tokenWeightProduct N tokens := by
  let q := fun p : Coord (Buffer := Buffer) (Server := Server) =>
    (gridCellParameter N K H hH m p : Real)
  calc
    (∏ p, ∏ i : Fin m,
        if hi : i ∈ S then
          if (p.1, p.2) =
              listToken tokens ((S.orderIsoOfFin hS).symm ⟨i, hi⟩)
          then q p else 1
        else 1) =
        ∏ i : Fin m, ∏ p,
          if hi : i ∈ S then
            if (p.1, p.2) =
                listToken tokens ((S.orderIsoOfFin hS).symm ⟨i, hi⟩)
            then q p else 1
          else 1 := by
      exact Finset.prod_comm
    _ = ∏ i : Fin m,
        if hi : i ∈ S then
          q ⟨(listToken tokens
                ((S.orderIsoOfFin hS).symm ⟨i, hi⟩)).1,
              (listToken tokens
                ((S.orderIsoOfFin hS).symm ⟨i, hi⟩)).2⟩
        else 1 := by
      apply Fintype.prod_congr
      intro i
      by_cases hi : i ∈ S
      · simp only [dif_pos hi]
        exact prod_coord_eq
          (fun p => q p)
          (listToken tokens
            ((S.orderIsoOfFin hS).symm ⟨i, hi⟩))
      · simp [hi]
    _ = ∏ i : S,
        q ⟨(listToken tokens ((S.orderIsoOfFin hS).symm i)).1,
            (listToken tokens ((S.orderIsoOfFin hS).symm i)).2⟩ := by
      symm
      have h := Finset.prod_attach_eq_prod_dite S
        (fun i : S =>
          q ⟨(listToken tokens ((S.orderIsoOfFin hS).symm i)).1,
              (listToken tokens ((S.orderIsoOfFin hS).symm i)).2⟩)
      simpa only [Finset.attach_eq_univ] using h
    _ = ∏ r : Fin tokens.length,
        q ⟨(listToken tokens r).1, (listToken tokens r).2⟩ := by
      exact prod_ordered_cells tokens m S hS
        (fun jk => q ⟨jk.1, jk.2⟩)
    _ = ((((K : Nat) : Real) * H / m) ^ tokens.length) *
        tokenWeightProduct N tokens := by
      have hq (r : Fin tokens.length) :
          q ⟨(listToken tokens r).1, (listToken tokens r).2⟩ =
            (((K : Nat) : Real) * H / m) *
              N.phi (listToken tokens r).1
                (listToken tokens r).2 := by
        change
          ((K : Nat) : Real) *
              N.phi (listToken tokens r).1 (listToken tokens r).2 *
              (H / m) =
            (((K : Nat) : Real) * H / m) *
              N.phi (listToken tokens r).1 (listToken tokens r).2
        ring
      simp_rw [hq]
      rw [Finset.prod_mul_distrib]
      unfold tokenWeightProduct
      congr 1
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem gridIncrementLaw_real_gridAtom
    (K : PNat) (H : Real) (hH : 0 <= H)
    {m : Nat} (hm : 0 < m)
    (tokens : List (Token (Buffer := Buffer) (Server := Server)))
    (S : Finset (Fin m)) (hS : S.card = tokens.length) :
    (gridIncrementLaw N K H hH m).real
        {gridAtom tokens m S hS} =
      Real.exp (-(((K : Nat) : Real) * H)) *
        ((((K : Nat) : Real) * H / m) ^ tokens.length) *
        tokenWeightProduct N tokens := by
  rw [gridIncrementLaw_real_singleton]
  calc
    (∏ p : Coord (Buffer := Buffer) (Server := Server),
      ∏ i : Fin m,
        (Real.exp (-(gridCellParameter N K H hH m p : Real)) *
          (gridCellParameter N K H hH m p : Real) ^
            gridAtom tokens m S hS p i /
          Nat.factorial (gridAtom tokens m S hS p i))) =
        ∏ p : Coord (Buffer := Buffer) (Server := Server),
          ∏ i : Fin m,
            (Real.exp
              (-(gridCellParameter N K H hH m p : Real)) *
              if hi : i ∈ S then
                if (p.1, p.2) =
                    listToken tokens
                      ((S.orderIsoOfFin hS).symm ⟨i, hi⟩)
                then (gridCellParameter N K H hH m p : Real)
                else 1
              else 1) := by
      apply Fintype.prod_congr
      intro p
      apply Fintype.prod_congr
      intro i
      exact gridAtom_cell_factor N K H hH m tokens S hS p i
    _ =
        (∏ p : Coord (Buffer := Buffer) (Server := Server),
          ∏ _i : Fin m,
            Real.exp
              (-(gridCellParameter N K H hH m p : Real))) *
        (∏ p : Coord (Buffer := Buffer) (Server := Server),
          ∏ i : Fin m,
            if hi : i ∈ S then
              if (p.1, p.2) =
                  listToken tokens
                    ((S.orderIsoOfFin hS).symm ⟨i, hi⟩)
              then (gridCellParameter N K H hH m p : Real)
              else 1
            else 1) := by
      simp_rw [Finset.prod_mul_distrib]
    _ = Real.exp (-(((K : Nat) : Real) * H)) *
        ((((K : Nat) : Real) * H / m) ^ tokens.length) *
        tokenWeightProduct N tokens := by
      rw [prod_gridCell_exp N K H hH hm,
        prod_gridAtom_selected_factors N K H hH hm tokens S hS]
      ring

theorem gridIncrementLaw_real_gridAtoms
    (K : PNat) (H : Real) (hH : 0 <= H)
    {m : Nat} (hm : 0 < m)
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) :
    (gridIncrementLaw N K H hH m).real
        (gridAtoms (Buffer := Buffer) (Server := Server) tokens m) =
      (Nat.choose m tokens.length : Real) *
        (Real.exp (-(((K : Nat) : Real) * H)) *
          ((((K : Nat) : Real) * H / m) ^ tokens.length) *
          tokenWeightProduct N tokens) := by
  let mu := gridIncrementLaw N K H hH m
  let atoms :=
    gridAtoms (Buffer := Buffer) (Server := Server) tokens m
  letI : IsProbabilityMeasure (gridIncrementLaw N K H hH m) := by
    unfold gridIncrementLaw
    infer_instance
  rw [← sum_measureReal_singleton]
  calc
    (∑ z ∈ atoms, mu.real {z}) =
        ∑ _z ∈ atoms,
          (Real.exp (-(((K : Nat) : Real) * H)) *
            ((((K : Nat) : Real) * H / m) ^ tokens.length) *
            tokenWeightProduct N tokens) := by
      apply Finset.sum_congr rfl
      intro z hz
      unfold atoms gridAtoms at hz
      rcases Finset.mem_image.mp hz with ⟨S, hS, rfl⟩
      unfold mu
      exact gridIncrementLaw_real_gridAtom N K H hH hm tokens
        S.1 ((Finset.mem_powersetCard.mp S.2).2)
    _ = (atoms.card : Real) *
        (Real.exp (-(((K : Nat) : Real) * H)) *
          ((((K : Nat) : Real) * H / m) ^ tokens.length) *
          tokenWeightProduct N tokens) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.choose m tokens.length : Real) *
        (Real.exp (-(((K : Nat) : Real) * H)) *
          ((((K : Nat) : Real) * H / m) ^ tokens.length) *
          tokenWeightProduct N tokens) := by
      rw [show atoms.card = Nat.choose m tokens.length by
        exact card_gridAtoms tokens m]

theorem gridRealizes_measureReal
    (K : PNat) (H : Real) (hH : 0 <= H)
    {m : Nat} (hm : 0 < m)
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) :
    N.calendarPoissonMeasure.real (gridRealizes N K H tokens m) =
      (Nat.choose m tokens.length : Real) *
        (Real.exp (-(((K : Nat) : Real) * H)) *
          ((((K : Nat) : Real) * H / m) ^ tokens.length) *
          tokenWeightProduct N tokens) := by
  rw [gridRealizes_measureReal_eq_law N K hH tokens m]
  exact gridIncrementLaw_real_gridAtoms N K H hH hm tokens

theorem tendsto_gridRealizes_measureReal
    (K : PNat) {H : Real} (hH : 0 < H)
    (tokens : List (Token (Buffer := Buffer) (Server := Server))) :
    Tendsto
      (fun m =>
        N.calendarPoissonMeasure.real
          (gridRealizes N K H tokens m))
      atTop
      (nhds
        (Real.exp (-(((K : Nat) : Real) * H)) *
          ((((K : Nat) : Real) * H) ^ tokens.length /
            Nat.factorial tokens.length) *
          tokenWeightProduct N tokens)) := by
  let lambda : Real := ((K : Nat) : Real) * H
  let p : Nat -> Real := fun m => lambda / m
  have hp :
      Tendsto (fun m : Nat => (m : Real) * p m)
        atTop (nhds lambda) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hm)
    dsimp only [p]
    field_simp
  have hchoose :=
    ProbabilityTheory.tendsto_choose_mul_pow_atTop
      tokens.length hp
  have hlim :
      Tendsto
        (fun m =>
          Real.exp (-lambda) *
            ((Nat.choose m tokens.length : Real) *
              (p m) ^ tokens.length) *
            tokenWeightProduct N tokens)
        atTop
        (nhds
          (Real.exp (-lambda) *
            (lambda ^ tokens.length /
              Nat.factorial tokens.length) *
            tokenWeightProduct N tokens)) :=
    (tendsto_const_nhds.mul hchoose).mul_const _
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [gridRealizes_measureReal N K H hH.le hm tokens]
  dsimp only [p, lambda]
  ring

private theorem sum_map_toList
    {A : Type*} [DecidableEq A] (s : Finset A) (f : A -> Nat) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  have h := congrArg
    (fun u : Multiset A => (u.map f).sum)
    (Finset.coe_toList s)
  calc
    (s.toList.map f).sum =
        (Multiset.map f (↑s.toList : Multiset A)).sum := by
      rw [← Multiset.sum_coe]
      rfl
    _ = (Multiset.map f s.val).sum := h
    _ = ∑ x ∈ s, f x := rfl

theorem calendarTokenPrefix_count
    (K : PNat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) :
    (N.calendarTokenPrefix K omega t).count (j, k) =
      N.calendarTokenCount K omega t j k := by
  classical
  unfold StateDepMOR.Network.calendarTokenPrefix
    StateDepMOR.Network.chronologicalCalendarEvents
  have hp :=
    List.Perm.map (fun event => event.1)
      (List.perm_insertionSort
        (fun a b =>
          N.calendarEventTime K omega a <=
            N.calendarEventTime K omega b)
        (N.rawCalendarEvents K omega t))
  rw [hp.count_eq]
  unfold StateDepMOR.Network.rawCalendarEvents
  simp only [List.count_eq_countP, List.countP_map,
    List.countP_flatMap]
  rw [sum_map_toList]
  rw [Finset.sum_eq_single j]
  · dsimp only [Function.comp_apply]
    rw [List.countP_flatMap, sum_map_toList]
    rw [Finset.sum_eq_single k]
    · simp only [Function.comp_apply]
      rw [List.countP_map]
      have hb : ((j, k) == (j, k)) = true :=
        beq_self_eq_true (j, k)
      refine (List.countP_congr (q := fun _ : Nat => true) ?_).trans ?_
      · intro x hx
        simp only [Function.comp_apply, hb]
      · rw [List.countP_true, Finset.length_toList,
          Finset.card_range]
    · intro k' hk' hk
      have hpair : (j, k') ≠ (j, k) := by
        intro h
        exact hk (congrArg Prod.snd h)
      simp [hpair]
    · simp
  · intro j' hj' hj
    dsimp only [Function.comp_apply]
    rw [List.countP_flatMap, sum_map_toList]
    apply Finset.sum_eq_zero
    intro k' hk'
    have hpair : (j', k') ≠ (j, k) := by
      intro h
      exact hj (congrArg Prod.fst h)
    simp [hpair]
  · simp

theorem rawCalendarEvents_positive_rate
    (K : PNat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (t : Real)
    (event : StateDepMOR.Network.CalendarEvent
      (Buffer := Buffer) (Server := Server))
    (hevent : event ∈ N.rawCalendarEvents K omega t) :
    0 < N.phi event.1.1 event.1.2 := by
  by_contra hnot
  have hzero : N.phi event.1.1 event.1.2 = 0 :=
    le_antisymm (le_of_not_gt hnot)
      (N.phi_nonneg event.1.1 event.1.2)
  rcases event with ⟨⟨j, k⟩, r⟩
  simp [StateDepMOR.Network.rawCalendarEvents, hzero] at hevent

theorem chronologicalCalendarEvents_pairwise_time
    (K : PNat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (t : Real) :
    (N.chronologicalCalendarEvents K omega t).Pairwise
      (fun a b =>
        N.calendarEventTime K omega a <=
          N.calendarEventTime K omega b) := by
  classical
  let r :=
    fun a b : StateDepMOR.Network.CalendarEvent
        (Buffer := Buffer) (Server := Server) =>
      N.calendarEventTime K omega a <= N.calendarEventTime K omega b
  letI : Std.Total r := ⟨fun a b => le_total _ _⟩
  letI : IsTrans _ r := ⟨fun _ _ _ hab hbc => hab.trans hbc⟩
  exact List.pairwise_insertionSort r _

theorem totalCalendarTokenPrefix_eq_original_of_regular
    (K : PNat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (t : Real)
    (hself :
      StateDepMOR.Network.totalCalendarPoissonSample omega = omega)
    (hregular : StateDepMOR.PoissonSamplePath.IsRegularSample omega)
    (hcross : forall j k j' k',
      0 < N.phi j k -> 0 < N.phi j' k' ->
      (j, k) ≠ (j', k') -> forall r q,
        N.calendarEventTime K omega ((j, k), r) ≠
          N.calendarEventTime K omega ((j', k'), q)) :
    N.totalCalendarTokenPrefix K omega t =
      N.calendarTokenPrefix K omega t := by
  classical
  let totalEvents :=
    N.totalChronologicalCalendarEvents K omega t
  let originalEvents :=
    N.chronologicalCalendarEvents K omega t
  have hperm :
      List.Perm totalEvents originalEvents := by
    dsimp only [totalEvents, originalEvents]
    have h :=
      N.totalChronologicalCalendarEvents_perm_original K omega t
    simpa [hself] using h
  have htotalPairwise :
      totalEvents.Pairwise
        (fun a b =>
          N.calendarEventTime K omega a <=
            N.calendarEventTime K omega b) := by
    have h :=
      N.totalChronologicalCalendarEvents_pairwise K omega t
    simpa [totalEvents, StateDepMOR.Network.totalCalendarEventTime,
      hself] using h
  have horiginalPairwise :
      originalEvents.Pairwise
        (fun a b =>
          N.calendarEventTime K omega a <=
            N.calendarEventTime K omega b) := by
    exact chronologicalCalendarEvents_pairwise_time N K omega t
  have hpositive :
      forall e, e ∈ originalEvents ->
        0 < N.phi e.1.1 e.1.2 := by
    intro e he
    apply rawCalendarEvents_positive_rate N K omega t e
    exact
      (List.perm_insertionSort
        (fun a b =>
          N.calendarEventTime K omega a <=
            N.calendarEventTime K omega b)
        (N.rawCalendarEvents K omega t)).mem_iff.mp he
  have hinjective :
      Set.InjOn (N.calendarEventTime K omega)
        {e | 0 < N.phi e.1.1 e.1.2} :=
    StateDepMOR.PoissonSamplePath.calendarEventTime_injective_on_positive
      N K omega hregular.1 hcross
  have hevents : totalEvents = originalEvents := by
    apply hperm.eq_of_pairwise
    · intro a b ha hb hab hba
      apply hinjective
      · exact hpositive a (hperm.mem_iff.mp ha)
      · exact hpositive b hb
      · exact le_antisymm hab hba
    · exact htotalPairwise
    · exact horiginalPairwise
  unfold StateDepMOR.Network.totalCalendarTokenPrefix
    StateDepMOR.Network.calendarTokenPrefix
  exact congrArg (List.map fun event => event.1) hevents

theorem totalCalendarTokenPrefix_count
    (K : PNat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) :
    (N.totalCalendarTokenPrefix K omega t).count (j, k) =
      N.totalCalendarTokenCount K omega t j k := by
  classical
  unfold StateDepMOR.Network.totalCalendarTokenPrefix
  have hp :=
    (N.totalChronologicalCalendarEvents_perm_original K omega t).map
      (fun event => event.1)
  rw [hp.count_eq]
  exact calendarTokenPrefix_count N K
    (StateDepMOR.Network.totalCalendarPoissonSample omega) t j k

/-- Events contributed by one uniform-grid cell, in chronological order. -/
noncomputable def gridCellEvents
    (K : PNat) (H : Real) (m : Nat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (i : Fin m) :
    List (StateDepMOR.Network.CalendarEvent
      (Buffer := Buffer) (Server := Server)) :=
  (N.totalChronologicalCalendarEvents K omega (uniformGrid H m i.succ)).drop
    (N.totalChronologicalCalendarEvents K omega
      (uniformGrid H m i.castSucc)).length

/-- Mark list contributed by one uniform-grid cell. -/
noncomputable def gridCellTokens
    (K : PNat) (H : Real) (m : Nat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (i : Fin m) :
    List (Token (Buffer := Buffer) (Server := Server)) :=
  (gridCellEvents N K H m omega i).map fun event => event.1

theorem totalChronologicalCalendarEvents_cell_append
    (K : PNat) {H : Real} (hH : 0 <= H) (m : Nat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (i : Fin m) :
    N.totalChronologicalCalendarEvents K omega (uniformGrid H m i.succ) =
      N.totalChronologicalCalendarEvents K omega
          (uniformGrid H m i.castSucc) ++
        gridCellEvents N K H m omega i := by
  obtain ⟨suffix, hsuffix⟩ :=
    N.totalChronologicalCalendarEvents_append K omega
      (uniformGrid_monotone hH m i.castSucc_le_succ)
  unfold gridCellEvents
  rw [hsuffix, List.drop_left]

theorem totalCalendarTokenPrefix_cell_append
    (K : PNat) {H : Real} (hH : 0 <= H) (m : Nat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (i : Fin m) :
    N.totalCalendarTokenPrefix K omega (uniformGrid H m i.succ) =
      N.totalCalendarTokenPrefix K omega
          (uniformGrid H m i.castSucc) ++
        gridCellTokens N K H m omega i := by
  unfold StateDepMOR.Network.totalCalendarTokenPrefix gridCellTokens
  rw [totalChronologicalCalendarEvents_cell_append N K hH m omega i,
    List.map_append]

theorem gridCellTokens_count
    (K : PNat) {H : Real} (hH : 0 <= H) (m : Nat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (i : Fin m) (j : Server) (k : Buffer) :
    (gridCellTokens N K H m omega i).count (j, k) =
      N.calendarTokenIncrements K m (uniformGrid H m)
        (StateDepMOR.Network.totalCalendarPoissonSample omega) j k i := by
  have happend :=
    totalCalendarTokenPrefix_cell_append N K hH m omega i
  have hcount := congrArg (fun l =>
    l.count (j, k)) happend
  rw [List.count_append,
    totalCalendarTokenPrefix_count N K omega,
    totalCalendarTokenPrefix_count N K omega] at hcount
  unfold StateDepMOR.Network.totalCalendarTokenCount at hcount
  unfold StateDepMOR.Network.calendarTokenIncrements
  omega

theorem flatten_successiveDrops
    {A : Type*} (n : Nat) (f : Fin (n + 1) -> List A)
    (happend : forall i j, i <= j ->
      exists suffix, f j = f i ++ suffix) :
    (List.ofFn fun i : Fin n =>
      (f i.succ).drop (f i.castSucc).length).flatten =
        (f (Fin.last n)).drop (f 0).length := by
  induction n with
  | zero => simp
  | succ n ih =>
      let g : Fin (n + 1) -> List A := fun i => f i.succ
      have hgappend : forall i j, i <= j ->
          exists suffix, g j = g i ++ suffix := by
        intro i j hij
        exact happend i.succ j.succ (Fin.succ_le_succ_iff.mpr hij)
      have hi := ih g hgappend
      have hzero :
          exists suffix, f (0 : Fin (n + 1)).succ =
            f (0 : Fin (n + 1)).castSucc ++ suffix :=
        happend _ _ Fin.castSucc_lt_succ.le
      obtain ⟨first, hfirst⟩ := hzero
      have htail :
          exists suffix, f (Fin.last (n + 1)) =
            f (0 : Fin (n + 1)).succ ++ suffix :=
        happend _ _ (Fin.le_last _)
      obtain ⟨tail, htail⟩ := htail
      rw [List.ofFn_succ, List.flatten_cons]
      have hi' :
          (List.ofFn fun i : Fin n =>
            (f i.succ.succ).drop
              (f i.succ.castSucc).length).flatten =
            (f (Fin.last (n + 1))).drop
              (f (0 : Fin (n + 1)).succ).length := by
        simpa [g] using hi
      rw [hi']
      rw [hfirst, htail]
      rw [hfirst]
      simp

theorem uniformGrid_last
    (H : Real) {m : Nat} (hm : 0 < m) :
    uniformGrid H m (Fin.last m) = H := by
  unfold uniformGrid
  have hm0 : (m : Real) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Fin.val_last]
  field_simp

theorem totalChronologicalCalendarEvents_zero
    (K : PNat)
    (omega : Sample (Buffer := Buffer) (Server := Server)) :
    N.totalChronologicalCalendarEvents K omega 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro event hevent
  have hindex :=
    (N.mem_totalChronologicalCalendarEvents_iff K omega 0 event).mp
      hevent
  have hcount :
      N.totalCalendarTokenCount K omega 0
        event.1.1 event.1.2 = 0 := by
    unfold StateDepMOR.Network.totalCalendarTokenCount
    exact N.calendarTokenCount_of_nonpos K
      (StateDepMOR.Network.totalCalendarPoissonSample omega)
      le_rfl event.1.1 event.1.2
  rw [hcount] at hindex
  omega

theorem flatten_gridCellEvents
    (K : PNat) {H : Real} (hH : 0 <= H)
    {m : Nat} (hm : 0 < m)
    (omega : Sample (Buffer := Buffer) (Server := Server)) :
    (List.ofFn fun i : Fin m =>
      gridCellEvents N K H m omega i).flatten =
        N.totalChronologicalCalendarEvents K omega H := by
  let f : Fin (m + 1) ->
      List (StateDepMOR.Network.CalendarEvent
        (Buffer := Buffer) (Server := Server)) :=
    fun i =>
      N.totalChronologicalCalendarEvents K omega (uniformGrid H m i)
  have happend : forall i j, i <= j ->
      exists suffix, f j = f i ++ suffix := by
    intro i j hij
    exact N.totalChronologicalCalendarEvents_append K omega
      (uniformGrid_monotone hH m hij)
  have hflatten := flatten_successiveDrops m f happend
  change
    (List.ofFn fun i : Fin m =>
      (f i.succ).drop (f i.castSucc).length).flatten =
        N.totalChronologicalCalendarEvents K omega H
  rw [hflatten]
  change
    (N.totalChronologicalCalendarEvents K omega
      (uniformGrid H m (Fin.last m))).drop
        (N.totalChronologicalCalendarEvents K omega
          (uniformGrid H m 0)).length =
      N.totalChronologicalCalendarEvents K omega H
  rw [uniformGrid_last H hm, uniformGrid_zero,
    totalChronologicalCalendarEvents_zero N]
  simp

theorem flatten_gridCellTokens
    (K : PNat) {H : Real} (hH : 0 <= H)
    {m : Nat} (hm : 0 < m)
    (omega : Sample (Buffer := Buffer) (Server := Server)) :
    (List.ofFn fun i : Fin m =>
      gridCellTokens N K H m omega i).flatten =
        N.totalCalendarTokenPrefix K omega H := by
  unfold gridCellTokens StateDepMOR.Network.totalCalendarTokenPrefix
  let mark :
      StateDepMOR.Network.CalendarEvent
        (Buffer := Buffer) (Server := Server) ->
          Token (Buffer := Buffer) (Server := Server) :=
    fun event => event.1
  calc
    (List.ofFn fun i : Fin m =>
        (gridCellEvents N K H m omega i).map mark).flatten =
        (List.map (List.map mark)
          (List.ofFn fun i : Fin m =>
            gridCellEvents N K H m omega i)).flatten := by
      rw [List.map_ofFn]
      rfl
    _ = List.map mark
        (List.ofFn fun i : Fin m =>
          gridCellEvents N K H m omega i).flatten := by
      rw [List.map_flatten]
    _ = List.map mark
        (N.totalChronologicalCalendarEvents K omega H) := by
      rw [flatten_gridCellEvents N K hH hm omega]

theorem gridCellEvents_nodup
    (K : PNat) {H : Real} (hH : 0 <= H) (m : Nat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (i : Fin m) :
    (gridCellEvents N K H m omega i).Nodup := by
  have hnodup :=
    N.totalChronologicalCalendarEvents_nodup K omega
      (uniformGrid H m i.succ)
  rw [totalChronologicalCalendarEvents_cell_append
    N K hH m omega i] at hnodup
  exact (List.nodup_append.mp hnodup).2.1

theorem gridCellEvents_mem_interval
    (K : PNat) {H : Real} (hH : 0 <= H) (m : Nat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (i : Fin m)
    {event : StateDepMOR.Network.CalendarEvent
      (Buffer := Buffer) (Server := Server)}
    (hevent : event ∈ gridCellEvents N K H m omega i) :
    N.totalCalendarEventTime K omega event ∈
      Ioc (uniformGrid H m i.castSucc)
        (uniformGrid H m i.succ) := by
  let earlier :=
    N.totalChronologicalCalendarEvents K omega
      (uniformGrid H m i.castSucc)
  let later :=
    N.totalChronologicalCalendarEvents K omega
      (uniformGrid H m i.succ)
  have happend :
      later = earlier ++ gridCellEvents N K H m omega i := by
    exact totalChronologicalCalendarEvents_cell_append
      N K hH m omega i
  have hlater : event ∈ later := by
    rw [happend]
    simp [hevent]
  have hnotEarlier : event ∉ earlier := by
    have hnodup :=
      N.totalChronologicalCalendarEvents_nodup K omega
        (uniformGrid H m i.succ)
    rw [show
      N.totalChronologicalCalendarEvents K omega
          (uniformGrid H m i.succ) = later by rfl,
      happend] at hnodup
    intro hearlier
    exact (List.nodup_append.mp hnodup).2.2
      event hearlier event hevent rfl
  have hindexLater :
      event.2 <
        N.totalCalendarTokenCount K omega
          (uniformGrid H m i.succ) event.1.1 event.1.2 :=
    (N.mem_totalChronologicalCalendarEvents_iff K omega
      (uniformGrid H m i.succ) event).mp hlater
  have hphi : 0 < N.phi event.1.1 event.1.2 := by
    rcases (N.phi_nonneg event.1.1 event.1.2).eq_or_lt with
      hzero | hpos
    · have hzero' : N.phi event.1.1 event.1.2 = 0 := hzero.symm
      have hc :
          N.totalCalendarTokenCount K omega
            (uniformGrid H m i.succ) event.1.1 event.1.2 = 0 := by
        simp [StateDepMOR.Network.totalCalendarTokenCount, hzero']
      rw [hc] at hindexLater
      omega
    · exact hpos
  have hright :
      N.totalCalendarEventTime K omega event <=
        uniformGrid H m i.succ := by
    have h :=
      (N.lt_totalCalendarTokenCount_iff_eventTime_le K omega
        (uniformGrid H m i.succ) event.1.1 event.1.2 event.2 hphi).mp
        hindexLater
    have hnonneg : 0 <= uniformGrid H m i.succ := by
      have hg :=
        uniformGrid_monotone hH m (Fin.zero_le i.succ)
      rw [uniformGrid_zero] at hg
      exact hg
    rw [max_eq_left
      hnonneg] at h
    exact h
  have hleft :
      uniformGrid H m i.castSucc <
        N.totalCalendarEventTime K omega event := by
    by_contra hnot
    have hnonneg : 0 <= uniformGrid H m i.castSucc := by
      have hg :=
        uniformGrid_monotone hH m (Fin.zero_le i.castSucc)
      rw [uniformGrid_zero] at hg
      exact hg
    have htime :
        N.totalCalendarEventTime K omega event <=
          max (uniformGrid H m i.castSucc) 0 := by
      rw [max_eq_left hnonneg]
      exact le_of_not_gt hnot
    have hindexEarlier :=
      (N.lt_totalCalendarTokenCount_iff_eventTime_le K omega
        (uniformGrid H m i.castSucc)
        event.1.1 event.1.2 event.2 hphi).mpr htime
    exact hnotEarlier
      ((N.mem_totalChronologicalCalendarEvents_iff K omega
        (uniformGrid H m i.castSucc) event).mpr hindexEarlier)
  exact ⟨hleft, hright⟩

theorem totalChronologicalCalendarEvents_positive_rate
    (K : PNat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (H : Real)
    {event : StateDepMOR.Network.CalendarEvent
      (Buffer := Buffer) (Server := Server)}
    (hevent :
      event ∈ N.totalChronologicalCalendarEvents K omega H) :
    0 < N.phi event.1.1 event.1.2 := by
  have hindex :=
    (N.mem_totalChronologicalCalendarEvents_iff K omega H event).mp
      hevent
  rcases (N.phi_nonneg event.1.1 event.1.2).eq_or_lt with
    hzero | hpos
  · have hzero' : N.phi event.1.1 event.1.2 = 0 := hzero.symm
    have hc :
        N.totalCalendarTokenCount K omega H
          event.1.1 event.1.2 = 0 := by
      simp [StateDepMOR.Network.totalCalendarTokenCount, hzero']
    rw [hc] at hindex
    omega
  · exact hpos

theorem gridCellEvents_mem_horizon
    (K : PNat) {H : Real} (hH : 0 <= H) (m : Nat)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (i : Fin m)
    {event : StateDepMOR.Network.CalendarEvent
      (Buffer := Buffer) (Server := Server)}
    (hevent : event ∈ gridCellEvents N K H m omega i) :
    event ∈ N.totalChronologicalCalendarEvents K omega H := by
  have hinterval :=
    gridCellEvents_mem_interval N K hH m omega i hevent
  have hrightH :
      uniformGrid H m i.succ <= H := by
    calc
      uniformGrid H m i.succ <=
          uniformGrid H m (Fin.last m) :=
        uniformGrid_monotone hH m (Fin.le_last _)
      _ = H := uniformGrid_last H (Nat.zero_lt_of_lt i.isLt)
  have hphi :
      0 < N.phi event.1.1 event.1.2 := by
    have hrightMem :
        event ∈ N.totalChronologicalCalendarEvents K omega
          (uniformGrid H m i.succ) := by
      have happend :=
        totalChronologicalCalendarEvents_cell_append
          N K hH m omega i
      rw [happend]
      simp [hevent]
    exact totalChronologicalCalendarEvents_positive_rate
      N K omega (uniformGrid H m i.succ) hrightMem
  apply
    (N.mem_totalChronologicalCalendarEvents_iff K omega H event).mpr
  apply
    (N.lt_totalCalendarTokenCount_iff_eventTime_le
      K omega H event.1.1 event.1.2 event.2 hphi).mpr
  rw [max_eq_left hH]
  exact hinterval.2.trans hrightH

theorem eventually_gridCellEvents_length_le_one
    (K : PNat) {H : Real} (hH : 0 < H)
    (omega : Sample (Buffer := Buffer) (Server := Server))
    (hself :
      StateDepMOR.Network.totalCalendarPoissonSample omega = omega)
    (hregular : StateDepMOR.PoissonSamplePath.IsRegularSample omega)
    (hcross : forall j k j' k',
      0 < N.phi j k -> 0 < N.phi j' k' ->
      (j, k) ≠ (j', k') -> forall r q,
        N.calendarEventTime K omega ((j, k), r) ≠
          N.calendarEventTime K omega ((j', k'), q)) :
    ∀ᶠ m in atTop, forall i : Fin m,
      (gridCellEvents N K H m omega i).length <= 1 := by
  classical
  let events :=
    N.totalChronologicalCalendarEvents K omega H
  have hinjective :
      Set.InjOn (N.totalCalendarEventTime K omega)
        {event | 0 < N.phi event.1.1 event.1.2} := by
    have h :=
      StateDepMOR.PoissonSamplePath.calendarEventTime_injective_on_positive
        N K omega hregular.1 hcross
    intro a ha b hb heq
    apply h ha hb
    simpa [StateDepMOR.Network.totalCalendarEventTime, hself] using heq
  have hmesh :
      Tendsto (fun m : Nat => H / (m : Real))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat H
  have hseparated :
      ∀ᶠ m : Nat in atTop,
        forall a, a ∈ events.toFinset ->
        forall b, b ∈ events.toFinset ->
          a ≠ b ->
            H / (m : Real) <
              |N.totalCalendarEventTime K omega a -
                N.totalCalendarEventTime K omega b| := by
    rw [Finset.eventually_all]
    intro a ha
    rw [Finset.eventually_all]
    intro b hb
    by_cases hab : a = b
    · exact Eventually.of_forall fun _ hne => False.elim (hne hab)
    · have htime :
          N.totalCalendarEventTime K omega a ≠
            N.totalCalendarEventTime K omega b := by
        intro heq
        apply hab
        apply hinjective
        · exact totalChronologicalCalendarEvents_positive_rate
            N K omega H (by simpa [events] using ha)
        · exact totalChronologicalCalendarEvents_positive_rate
            N K omega H (by simpa [events] using hb)
        · exact heq
      exact (hmesh.eventually_lt_const
        (abs_pos.mpr (sub_ne_zero.mpr htime))).mono
          (fun _ hm _ => hm)
  filter_upwards [hseparated, eventually_ge_atTop 1] with
    m hsep hm
  intro i
  have hnodup := gridCellEvents_nodup N K hH.le m omega i
  cases hcell : gridCellEvents N K H m omega i with
  | nil => simp
  | cons a tail =>
      cases tail with
      | nil => simp
      | cons b rest =>
          exfalso
          have ha :
              a ∈ gridCellEvents N K H m omega i := by
            rw [hcell]
            simp
          have hb :
              b ∈ gridCellEvents N K H m omega i := by
            rw [hcell]
            simp
          have hne : a ≠ b := by
            rw [hcell] at hnodup
            simp only [List.nodup_cons] at hnodup
            exact fun hab => hnodup.1 (by simp [hab])
          have haH :=
            gridCellEvents_mem_horizon N K hH.le m omega i ha
          have hbH :=
            gridCellEvents_mem_horizon N K hH.le m omega i hb
          have hgap := hsep a (by simpa [events] using haH)
            b (by simpa [events] using hbH) hne
          have haI :=
            gridCellEvents_mem_interval N K hH.le m omega i ha
          have hbI :=
            gridCellEvents_mem_interval N K hH.le m omega i hb
          rcases haI with ⟨haLeft, haRight⟩
          rcases hbI with ⟨hbLeft, hbRight⟩
          have habs :
              |N.totalCalendarEventTime K omega a -
                N.totalCalendarEventTime K omega b| <=
                  H / (m : Real) := by
            rw [← uniformGrid_step H m i, abs_sub_le_iff]
            constructor <;> linarith
          exact (not_lt_of_ge habs) hgap

end StateDepMOR.Achievability.CalendarLaw
