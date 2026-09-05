import StateDepMOR.FluidExistenceProof
import StateDepMOR.SMWConvergenceProof
import StateDepMOR.PoissonSamplePathLDP

open scoped BigOperators ENNReal NNReal Topology
open Filter MeasureTheory Set

set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

namespace StateDepMOR.PoissonSamplePath

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]
variable [Nonempty Buffer] [Nonempty Server]
variable [Nonempty Buffer]

private theorem time_displacement_lt_of_j1Cost_lt
    {H eta : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) H)
    (e : TimeChange H) (heta : 0 < eta)
    (he : j1Cost x y e < ENNReal.ofReal eta)
    (t : Horizon H) :
    |((e t : Horizon H) : Real) - (t : Real)| < eta := by
  have hpoint :
      ENNReal.ofReal
          |((e t : Horizon H) : Real) - (t : Real)| <= timeError e :=
    le_iSup
      (fun s : Horizon H =>
        ENNReal.ofReal
          |((e s : Horizon H) : Real) - (s : Real)|) t
  have hlt :
      ENNReal.ofReal |((e t : Horizon H) : Real) - (t : Real)| <
        ENNReal.ofReal eta :=
    hpoint.trans_lt ((le_max_left _ _).trans_lt he)
  exact (ENNReal.ofReal_lt_ofReal_iff heta).mp hlt

private theorem coordinate_error_lt_of_j1Cost_lt
    {H eta : Real}
    (x y : Path (Buffer := Buffer) (Server := Server) H)
    (e : TimeChange H) (heta : 0 < eta)
    (he : j1Cost x y e < ENNReal.ofReal eta)
    (t : Horizon H) (j : Server) (k : Buffer) :
    |x (e t) j k - y t j k| < eta := by
  have hk :
      ENNReal.ofReal |x (e t) j k - y t j k| <=
        iSup fun q : Buffer =>
          ENNReal.ofReal |x (e t) j q - y t j q| :=
    le_iSup
      (fun q : Buffer =>
        ENNReal.ofReal |x (e t) j q - y t j q|) k
  have hj :
      (iSup fun q : Buffer =>
          ENNReal.ofReal |x (e t) j q - y t j q|) <=
        iSup fun i : Server =>
          iSup fun q : Buffer =>
            ENNReal.ofReal |x (e t) i q - y t i q| :=
    le_iSup
      (fun i : Server =>
        iSup fun q : Buffer =>
          ENNReal.ofReal |x (e t) i q - y t i q|) j
  have ht :
      (iSup fun i : Server =>
          iSup fun q : Buffer =>
            ENNReal.ofReal |x (e t) i q - y t i q|) <=
        pathError x y e :=
    le_iSup
      (fun s : Horizon H =>
        iSup fun i : Server =>
          iSup fun q : Buffer =>
            ENNReal.ofReal |x (e s) i q - y s i q|) t
  have hlt :
      ENNReal.ofReal |x (e t) j k - y t j k| <
        ENNReal.ofReal eta :=
    (hk.trans (hj.trans ht)).trans_lt
      ((le_max_right _ _).trans_lt he)
  exact (ENNReal.ofReal_lt_ofReal_iff heta).mp hlt

/-- J1 convergence to a finite-action path is uniform in every coordinate.
The statement is deliberately epsilon-explicit so it can feed the
deterministic fluid compactness API directly. -/
theorem j1_tendsto_uniform_of_finite_poissonPathRate
    (N : Network Buffer Server) {H : Real} (hH : 0 < H)
    (f : Nat -> Path (Buffer := Buffer) (Server := Server) H)
    (a : Path (Buffer := Buffer) (Server := Server) H)
    (hfinite :
      Ne (poissonPathRate N H (asMatrix H a)) (Top.top : ENNReal))
    (hJ1 : Tendsto f atTop (nhds a)) :
    forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall t : Horizon H, forall j k,
          |f n t j k - a t j k| < epsilon := by
  have hcont :
      Continuous (fun t : Horizon H => a t) := by
    exact continuous_pi fun j =>
      continuous_pi fun k =>
        finiteRate_coordinate_continuous N hH a hfinite j k
  have huc :
      UniformContinuous (fun t : Horizon H => a t) :=
    CompactSpace.uniformContinuous_of_continuous hcont
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuous_iff.mp huc (epsilon / 2) (by positivity)
  let eta : Real := min (min delta (epsilon / 2)) (1 / 2)
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (lt_min hdelta (by positivity)) (by norm_num)
  obtain ⟨n0, hn0⟩ :=
    Metric.tendsto_atTop.mp hJ1 eta heta
  refine ⟨n0, fun n hn t j k => ?_⟩
  have hdist := hn0 n hn
  have hj1Real :
      ENNReal.toReal (j1EDist a (f n)) < eta := by
    change ENNReal.toReal (j1EDist (f n) a) < eta at hdist
    simpa only [j1EDist_comm] using hdist
  have hj1 :
      j1EDist a (f n) < ENNReal.ofReal eta := by
    rw [<- ENNReal.toReal_ofReal heta.le] at hj1Real
    exact (ENNReal.toReal_lt_toReal
      (ne_of_lt ((j1EDist_le_one a (f n)).trans_lt ENNReal.one_lt_top))
      (ENNReal.ofReal_ne_top)).mp hj1Real
  obtain ⟨e, he⟩ :=
    (j1EDist_lt_iff_exists_timeChange
      (show ENNReal.ofReal eta <= 1 by
        rw [ENNReal.ofReal_le_one]
        exact (min_le_right (min delta (epsilon / 2)) (1 / 2)).trans
          (by norm_num))).mp hj1
  have htime :=
    time_displacement_lt_of_j1Cost_lt a (f n) e heta he t
  have hpath :=
    coordinate_error_lt_of_j1Cost_lt a (f n) e heta he t j k
  have htimeDist : dist (e t) t < delta := by
    rw [Subtype.dist_eq, Real.dist_eq]
    exact htime.trans_le
      ((min_le_left (min delta (epsilon / 2)) (1 / 2)).trans
        (min_le_left delta (epsilon / 2)))
  have haClose := hdeltaWorks htimeDist
  have haCoord :
      |a (e t) j k - a t j k| < epsilon / 2 := by
    have hrow :
        dist (a (e t) j) (a t j) <=
          dist (a (e t)) (a t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (a (e t)) (a t) <= dist (a (e t)) (a t)) j
    have hcoord :
        dist (a (e t) j k) (a t j k) <=
          dist (a (e t)) (a t) :=
      ((dist_pi_le_iff dist_nonneg).mp
          (le_rfl :
            dist (a (e t) j) (a t j) <=
              dist (a (e t) j) (a t j)) k).trans hrow
    simpa only [Real.dist_eq] using hcoord.trans_lt haClose
  rw [abs_sub_comm] at hpath
  calc
    |f n t j k - a t j k| <=
        |f n t j k - a (e t) j k| +
          |a (e t) j k - a t j k| := abs_sub_le _ _ _
    _ < eta + epsilon / 2 := add_lt_add hpath haCoord
    _ <= epsilon / 2 + epsilon / 2 := by
      gcongr
      exact (min_le_left (min delta (epsilon / 2)) (1 / 2)).trans
        (min_le_right delta (epsilon / 2))
    _ = epsilon := by ring

end StateDepMOR.PoissonSamplePath

namespace FluidControlledCompactness

/-- Arzela-Ascoli extraction when increments are bounded by a finite family
of uniformly convergent continuous real controls. -/
private theorem exists_uniformly_convergent_subsequence_of_controlled_increments
    {X J : Type*} [MetricSpace X] [ProperSpace X] [Fintype J]
    {f : Nat -> Real -> X} {g : Nat -> J -> Real -> Real}
    {control : J -> Real -> Real} {a b M : Real} {center : X}
    (hf : forall n, ContinuousOn (f n) (Icc a b))
    (hbound : forall n t, t ∈ Icc a b -> dist (f n t) center <= M)
    (hcontrol : forall j, ContinuousOn (control j) (Icc a b))
    (hgconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j t, t ∈ Icc a b ->
          dist (g n j t) (control j t) < epsilon)
    (hdom : forall n x, x ∈ Icc a b ->
      forall y, y ∈ Icc a b ->
        dist (f n x) (f n y) <=
          Finset.univ.sum (fun j => dist (g n j x) (g n j y))) :
    exists q : Nat -> Nat, StrictMono q /\
      exists limit : Real -> X,
        ContinuousOn limit (Icc a b) /\
        forall epsilon, 0 < epsilon ->
          exists n0, forall n, n0 <= n ->
            forall t, t ∈ Icc a b ->
              dist (f (q n) t) (limit t) < epsilon := by
  let D := Icc a b
  letI : CompactSpace D :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let F : Nat -> BoundedContinuousFunction D X := fun n =>
    BoundedContinuousFunction.mkOfCompact
      (ContinuousMap.mk
        (fun t : D => f n t.1)
        ((hf n).domRestrict))
  have hcontrols :
      UniformEquicontinuous
        (fun j : J => fun t : D => control j t.1) := by
    rw [uniformEquicontinuous_finite]
    intro j
    exact CompactSpace.uniformContinuous_of_continuous
      ((hcontrol j).domRestrict)
  have hfamily :
      UniformEquicontinuous (fun n : Nat => fun t : D => f n t.1) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro epsilon hepsilon
    let C : Real := (Fintype.card J : Real) + 1
    have hC : 0 < C := by
      dsimp [C]
      positivity
    let eta : Real := epsilon / (8 * C)
    have heta : 0 < eta := by
      dsimp [eta]
      positivity
    obtain ⟨N, hN⟩ := hgconv eta heta
    have hprefix :
        UniformEquicontinuous
          (fun n : Fin N => fun t : D => f n.1 t.1) := by
      rw [uniformEquicontinuous_finite]
      intro n
      exact CompactSpace.uniformContinuous_of_continuous
        ((hf n.1).domRestrict)
    obtain ⟨deltaControl, hdeltaControl, hdeltaControlWorks⟩ :=
      (Metric.uniformEquicontinuous_iff.mp hcontrols)
        (epsilon / (4 * C)) (by positivity)
    obtain ⟨deltaPrefix, hdeltaPrefix, hdeltaPrefixWorks⟩ :=
      (Metric.uniformEquicontinuous_iff.mp hprefix)
        epsilon hepsilon
    refine ⟨min deltaControl deltaPrefix,
      lt_min hdeltaControl hdeltaPrefix, ?_⟩
    intro x y hxy n
    have hxyControl : dist x y < deltaControl :=
      hxy.trans_le (min_le_left _ _)
    have hxyPrefix : dist x y < deltaPrefix :=
      hxy.trans_le (min_le_right _ _)
    by_cases hn : N <= n
    · have hterm (j : J) :
          dist (g n j x.1) (g n j y.1) <= epsilon / C := by
        have hxapprox := hN n hn j x.1 x.2
        have hyapprox := hN n hn j y.1 y.2
        have hmiddle :=
          hdeltaControlWorks x y hxyControl j
        apply le_of_lt
        calc
          dist (g n j x.1) (g n j y.1)
              <= dist (g n j x.1) (control j x.1) +
                  dist (control j x.1) (control j y.1) +
                  dist (control j y.1) (g n j y.1) := by
                calc
                  _ <= dist (g n j x.1) (control j x.1) +
                      dist (control j x.1) (g n j y.1) :=
                    dist_triangle _ _ _
                  _ <= dist (g n j x.1) (control j x.1) +
                      (dist (control j x.1) (control j y.1) +
                        dist (control j y.1) (g n j y.1)) :=
                    by
                      have htri :=
                        dist_triangle (control j x.1) (control j y.1)
                          (g n j y.1)
                      linarith
                  _ = _ := by ring
          _ < eta + epsilon / (4 * C) + eta := by
                have hyapprox' :
                    dist (control j y.1) (g n j y.1) < eta := by
                  simpa [dist_comm] using hyapprox
                gcongr
          _ <= epsilon / C := by
                dsimp [eta]
                have h8C : 0 < 8 * C := by positivity
                have h4C : 0 < 4 * C := by positivity
                field_simp
                linarith
      have hcard_lt : (Fintype.card J : Real) / C < 1 := by
        apply (div_lt_one hC).2
        dsimp [C]
        linarith
      calc
        dist (f n x.1) (f n y.1)
            <= Finset.univ.sum
                (fun j => dist (g n j x.1) (g n j y.1)) :=
              hdom n x.1 x.2 y.1 y.2
        _ <= Finset.univ.sum (fun _ : J => epsilon / C) :=
              Finset.sum_le_sum (fun j _ => hterm j)
        _ = (Fintype.card J : Real) * (epsilon / C) := by simp
        _ = epsilon * ((Fintype.card J : Real) / C) := by ring
        _ < epsilon * 1 :=
              mul_lt_mul_of_pos_left hcard_lt hepsilon
        _ = epsilon := by ring
    · have hnlt : n < N := Nat.lt_of_not_ge hn
      exact hdeltaPrefixWorks x y hxyPrefix ⟨n, hnlt⟩
  let A : Set (BoundedContinuousFunction D X) := range F
  have hcompact : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall center M) (isCompact_closedBall center M) A
    · intro p t hp
      obtain ⟨n, rfl⟩ := hp
      exact hbound n t.1 t.2
    · let index : A -> Nat := fun p => Classical.choose p.2
      have hindex (p : A) : F (index p) = p.1 :=
        Classical.choose_spec p.2
      intro t
      rw [Metric.equicontinuousAt_iff]
      intro epsilon hepsilon
      have hnat := hfamily.equicontinuous t
      rw [Metric.equicontinuousAt_iff] at hnat
      obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
        hnat epsilon hepsilon
      refine ⟨delta, hdelta, fun x hx p => ?_⟩
      rw [show p.1 t = F (index p) t by rw [hindex]]
      rw [show p.1 x = F (index p) x by rw [hindex]]
      exact hdeltaWorks x hx (index p)
  obtain ⟨limitB, _hlimit_mem, q, hqmono, hqconv⟩ :=
    hcompact.tendsto_subseq
      (fun n => subset_closure
        (show F n ∈ A from mem_range_self n))
  let limit : Real -> X := fun t =>
    if ht : t ∈ Icc a b then
      limitB (show D from ⟨t, ht⟩)
    else center
  refine ⟨q, hqmono, limit, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq :
        (Icc a b).domRestrict limit = fun t : D => limitB t := by
      funext t
      exact dif_pos t.2
    rw [heq]
    exact limitB.continuous
  · intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ :=
      Metric.tendsto_atTop.mp hqconv epsilon hepsilon
    refine ⟨n0, fun n hn t ht => ?_⟩
    have hdist := BoundedContinuousFunction.dist_coe_le_dist
      (f := F (q n)) (g := limitB) (show D from ⟨t, ht⟩)
    have hlt := lt_of_le_of_lt hdist (by
      simpa [Function.comp_apply] using hn0 n hn)
    have hlimit :
        limit t = limitB (show D from ⟨t, ht⟩) :=
      dif_pos ht
    rw [hlimit]
    exact hlt

/-- Real-valued specialization of controlled-increment compactness. -/
private theorem exists_uniformly_convergent_subsequence_real
    {J : Type*} [Fintype J]
    {f : Nat -> Real -> Real} {g : Nat -> J -> Real -> Real}
    {control : J -> Real -> Real} {a b M : Real}
    (hf : forall n, ContinuousOn (f n) (Icc a b))
    (hbound : forall n t, t ∈ Icc a b -> abs (f n t) <= M)
    (hcontrol : forall j, ContinuousOn (control j) (Icc a b))
    (hgconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j t, t ∈ Icc a b ->
          dist (g n j t) (control j t) < epsilon)
    (hdom : forall n x, x ∈ Icc a b ->
      forall y, y ∈ Icc a b ->
        dist (f n x) (f n y) <=
          Finset.univ.sum (fun j => dist (g n j x) (g n j y))) :
    exists q : Nat -> Nat, StrictMono q /\
      exists limit : Real -> Real,
        ContinuousOn limit (Icc a b) /\
        forall epsilon, 0 < epsilon ->
          exists n0, forall n, n0 <= n ->
            forall t, t ∈ Icc a b ->
              dist (f (q n) t) (limit t) < epsilon := by
  apply exists_uniformly_convergent_subsequence_of_controlled_increments
    (J := J) (f := f) (g := g) (control := control)
    (center := (0 : Real)) hf
  · simpa [Real.dist_eq] using hbound
  · exact hcontrol
  · exact hgconv
  · exact hdom

/-- A single subsequence converges uniformly in every coordinate of a
finite family of controlled real paths. -/
private theorem exists_uniformly_convergent_subsequence_finite
    {I J : Type*} [Fintype I] [Fintype J]
    {f : Nat -> I -> Real -> Real}
    {g : Nat -> J -> Real -> Real}
    {control : J -> Real -> Real} {a b M : Real}
    (hf : forall n i, ContinuousOn (f n i) (Icc a b))
    (hbound : forall n i t, t ∈ Icc a b -> abs (f n i t) <= M)
    (hcontrol : forall j, ContinuousOn (control j) (Icc a b))
    (hgconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j t, t ∈ Icc a b ->
          dist (g n j t) (control j t) < epsilon)
    (hdom : forall n i x, x ∈ Icc a b ->
      forall y, y ∈ Icc a b ->
        dist (f n i x) (f n i y) <=
          Finset.univ.sum (fun j => dist (g n j x) (g n j y))) :
    exists q : Nat -> Nat, StrictMono q /\
      exists limit : I -> Real -> Real,
        (forall i, ContinuousOn (limit i) (Icc a b)) /\
        forall epsilon, 0 < epsilon ->
          exists n0, forall n, n0 <= n ->
            forall i t, t ∈ Icc a b ->
              dist (f (q n) i t) (limit i t) < epsilon := by
  let fPi : Nat -> Real -> (I -> Real) :=
    fun n t i => f n i t
  have hfPi (n : Nat) :
      ContinuousOn (fPi n) (Icc a b) := by
    rw [continuousOn_pi]
    exact hf n
  have hboundPi (n : Nat) (t : Real) (ht : t ∈ Icc a b) :
      dist (fPi n t) (0 : I -> Real) <= max M 0 := by
    apply (dist_pi_le_iff (le_max_right _ _)).2
    intro i
    have hi : dist (fPi n t i) 0 <= M := by
      simpa [fPi, Real.dist_eq] using hbound n i t ht
    exact hi.trans (le_max_left _ _)
  have hdomPi (n : Nat) (x : Real) (hx : x ∈ Icc a b)
      (y : Real) (hy : y ∈ Icc a b) :
      dist (fPi n x) (fPi n y) <=
        Finset.univ.sum (fun j => dist (g n j x) (g n j y)) := by
    apply (dist_pi_le_iff (Finset.sum_nonneg
      (fun _ _ => dist_nonneg))).2
    intro i
    exact hdom n i x hx y hy
  obtain ⟨q, hq, limitPi, hlimitPi, hconv⟩ :=
    exists_uniformly_convergent_subsequence_of_controlled_increments
      (f := fPi) (g := g) (control := control)
      (center := (0 : I -> Real))
      hfPi hboundPi hcontrol hgconv hdomPi
  let limit : I -> Real -> Real := fun i t => limitPi t i
  refine ⟨q, hq, limit, ?_, ?_⟩
  · intro i
    exact (continuousOn_pi.mp hlimitPi) i
  · intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := hconv epsilon hepsilon
    refine ⟨n0, fun n hn i t ht => ?_⟩
    have hall := hn0 n hn t ht
    exact lt_of_le_of_lt
      ((dist_pi_le_iff dist_nonneg).mp (le_rfl : dist (fPi (q n) t) (limitPi t) <= _) i)
      hall

end FluidControlledCompactness

open Filter Set

namespace FluidCompactness

variable {X Y : Type*} [PseudoMetricSpace X]

/-- A path whose increments are bounded by finitely many absolutely
continuous control paths is absolutely continuous. -/
private theorem absolutelyContinuousOnInterval_of_dist_le_finset
    {f : Real -> X} {g : Y -> Real -> Real} {s : Finset Y} {a b : Real}
    (hg : forall j, Membership.mem s j ->
      AbsolutelyContinuousOnInterval (g j) a b)
    (hdom : forall x, Membership.mem (uIcc a b) x ->
      forall y, Membership.mem (uIcc a b) y ->
      dist (f x) (f y) <=
        s.sum (fun j => dist (g j x) (g j y))) :
    AbsolutelyContinuousOnInterval f a b := by
  unfold AbsolutelyContinuousOnInterval at hg
  unfold AbsolutelyContinuousOnInterval
  have hcontrols :
      Tendsto
        (fun E : Prod Nat (Nat -> Prod Real Real) =>
          s.sum (fun j =>
            (Finset.range E.1).sum
              (fun i => dist (g j (E.2 i).1) (g j (E.2 i).2))))
        (Min.min AbsolutelyContinuousOnInterval.totalLengthFilter
          (principal (AbsolutelyContinuousOnInterval.disjWithin a b)))
        (nhds 0) := by
    simpa using
      (tendsto_finsetSum s (fun j hj => hg j hj))
  apply squeeze_zero'
    (Eventually.of_forall
      (fun E : Prod Nat (Nat -> Prod Real Real) =>
        Finset.sum_nonneg (fun i hi => dist_nonneg)))
    ?_
    hcontrols
  rw [eventually_inf_principal]
  filter_upwards with E hE
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i hi
  exact hdom _ (hE.1 i hi).1 _ (hE.1 i hi).2

/-- A common increment bound passes to a uniform limit on an interval. -/
private theorem dist_le_finset_of_uniform_limit
    {f : Nat -> Real -> X} {limit : Real -> X}
    {g : Y -> Real -> Real} {s : Finset Y} {a b : Real}
    (hconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall t, Membership.mem (uIcc a b) t ->
          dist (f n t) (limit t) < epsilon)
    (hdom : forall n, forall x, Membership.mem (uIcc a b) x ->
      forall y, Membership.mem (uIcc a b) y ->
        dist (f n x) (f n y) <=
          s.sum (fun j => dist (g j x) (g j y)))
    {x y : Real} (hx : Membership.mem (uIcc a b) x)
    (hy : Membership.mem (uIcc a b) y) :
    dist (limit x) (limit y) <=
      s.sum (fun j => dist (g j x) (g j y)) := by
  have hxlim : Tendsto (fun n => f n x) atTop (nhds (limit x)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    let n0 := Classical.choose (hconv epsilon hepsilon)
    have hn0 := Classical.choose_spec (hconv epsilon hepsilon)
    exact Exists.intro n0 (fun n hn => hn0 n hn x hx)
  have hylim : Tendsto (fun n => f n y) atTop (nhds (limit y)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    let n0 := Classical.choose (hconv epsilon hepsilon)
    have hn0 := Classical.choose_spec (hconv epsilon hepsilon)
    exact Exists.intro n0 (fun n hn => hn0 n hn y hy)
  exact le_of_tendsto (hxlim.dist hylim)
    (Eventually.of_forall (fun n => hdom n x hx y hy))

/-- An increment bound passes to the limit when both the path and its
finitely many control paths converge uniformly. -/
private theorem dist_le_finset_of_uniform_limits
    {f : Nat -> Real -> X} {limit : Real -> X}
    {g : Nat -> Y -> Real -> Real} {control : Y -> Real -> Real}
    {s : Finset Y} {a b : Real}
    (hfconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall t, Membership.mem (uIcc a b) t ->
          dist (f n t) (limit t) < epsilon)
    (hgconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j, Membership.mem s j ->
          forall t, Membership.mem (uIcc a b) t ->
            dist (g n j t) (control j t) < epsilon)
    (hdom : forall n, forall x, Membership.mem (uIcc a b) x ->
      forall y, Membership.mem (uIcc a b) y ->
        dist (f n x) (f n y) <=
          s.sum (fun j => dist (g n j x) (g n j y)))
    {x y : Real} (hx : Membership.mem (uIcc a b) x)
    (hy : Membership.mem (uIcc a b) y) :
    dist (limit x) (limit y) <=
      s.sum (fun j => dist (control j x) (control j y)) := by
  have hpointF (t : Real) (ht : Membership.mem (uIcc a b) t) :
      Tendsto (fun n => f n t) atTop (nhds (limit t)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    let n0 := Classical.choose (hfconv epsilon hepsilon)
    have hn0 := Classical.choose_spec (hfconv epsilon hepsilon)
    exact Exists.intro n0 (fun n hn => hn0 n hn t ht)
  have hpointG (j : Y) (hj : Membership.mem s j)
      (t : Real) (ht : Membership.mem (uIcc a b) t) :
      Tendsto (fun n => g n j t) atTop (nhds (control j t)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    let n0 := Classical.choose (hgconv epsilon hepsilon)
    have hn0 := Classical.choose_spec (hgconv epsilon hepsilon)
    exact Exists.intro n0 (fun n hn => hn0 n hn j hj t ht)
  have hleft :
      Tendsto (fun n => dist (f n x) (f n y)) atTop
        (nhds (dist (limit x) (limit y))) :=
    (hpointF x hx).dist (hpointF y hy)
  have hright :
      Tendsto
        (fun n => s.sum (fun j => dist (g n j x) (g n j y)))
        atTop
        (nhds (s.sum (fun j =>
          dist (control j x) (control j y)))) := by
    apply tendsto_finsetSum
    intro j hj
    exact (hpointG j hj x hx).dist (hpointG j hj y hy)
  exact le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall (fun n => hdom n x hx y hy))

/-- Uniform limits dominated by uniformly converging finite AC controls are
absolutely continuous. -/
private theorem absolutelyContinuousOnInterval_of_uniform_limits_finset
    {f : Nat -> Real -> X} {limit : Real -> X}
    {g : Nat -> Y -> Real -> Real} {control : Y -> Real -> Real}
    {s : Finset Y} {a b : Real}
    (hfconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall t, Membership.mem (uIcc a b) t ->
          dist (f n t) (limit t) < epsilon)
    (hgconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j, Membership.mem s j ->
          forall t, Membership.mem (uIcc a b) t ->
            dist (g n j t) (control j t) < epsilon)
    (hac : forall j, Membership.mem s j ->
      AbsolutelyContinuousOnInterval (control j) a b)
    (hdom : forall n, forall x, Membership.mem (uIcc a b) x ->
      forall y, Membership.mem (uIcc a b) y ->
        dist (f n x) (f n y) <=
          s.sum (fun j => dist (g n j x) (g n j y))) :
    AbsolutelyContinuousOnInterval limit a b := by
  apply absolutelyContinuousOnInterval_of_dist_le_finset hac
  intro x hx y hy
  exact dist_le_finset_of_uniform_limits
    hfconv hgconv hdom hx hy

/-- Uniform limits with increments controlled by finitely many fixed
absolutely continuous paths are absolutely continuous. -/
private theorem absolutelyContinuousOnInterval_of_uniform_limit_finset
    {f : Nat -> Real -> X} {limit : Real -> X}
    {g : Y -> Real -> Real} {s : Finset Y} {a b : Real}
    (hconv : forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall t, Membership.mem (uIcc a b) t ->
          dist (f n t) (limit t) < epsilon)
    (hg : forall j, Membership.mem s j ->
      AbsolutelyContinuousOnInterval (g j) a b)
    (hdom : forall n, forall x, Membership.mem (uIcc a b) x ->
      forall y, Membership.mem (uIcc a b) y ->
        dist (f n x) (f n y) <=
          s.sum (fun j => dist (g j x) (g j y))) :
    AbsolutelyContinuousOnInterval limit a b := by
  apply absolutelyContinuousOnInterval_of_dist_le_finset hg
  intro x hx y hy
  exact dist_le_finset_of_uniform_limit hconv hdom hx hy

/-- Arzela-Ascoli extraction for real paths on a compact interval.  The
conclusion is stated as explicit uniform convergence on the interval. -/
private theorem exists_uniformly_convergent_subsequence_of_lipschitzOn
    {f : Nat -> Real -> Real} {a b : Real} {K : NNReal} {M : Real}
    (hlip : forall n, LipschitzOnWith K (f n) (Icc a b))
    (hbound : forall n, forall t, Membership.mem (Icc a b) t ->
      abs (f n t) <= M) :
    exists q : Nat -> Nat, StrictMono q /\
      exists limit : Real -> Real,
        forall epsilon, 0 < epsilon ->
          exists n0, forall n, n0 <= n ->
            forall t, Membership.mem (Icc a b) t ->
              dist (f (q n) t) (limit t) < epsilon := by
  let D := Icc a b
  letI : CompactSpace D :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let F : Nat -> BoundedContinuousFunction D Real := fun n =>
    BoundedContinuousFunction.mkOfCompact
      (ContinuousMap.mk
        (fun t : D => f n t.1)
        ((hlip n).continuousOn.domRestrict))
  let A : Set (BoundedContinuousFunction D Real) := range F
  have hcompact : IsCompact (closure A) := by
    apply BoundedContinuousFunction.arzela_ascoli
      (Icc (-M) M) isCompact_Icc A
    next =>
      intro p t hp
      let n := Classical.choose hp
      have hn := Classical.choose_spec hp
      change -M <= p t /\ p t <= M
      rw [<- hn]
      exact abs_le.mp (hbound n t.1 t.2)
    next =>
      apply UniformEquicontinuous.equicontinuous
      apply LipschitzWith.uniformEquicontinuous
        (fun p : A => fun t : D => p.1 t) K
      intro p
      let n := Classical.choose p.2
      have hn := Classical.choose_spec p.2
      change LipschitzWith K (fun t : D => p.1 t)
      rw [<- hn]
      exact (hlip n).to_restrict
  have hextract :=
    hcompact.tendsto_subseq
      (fun n => subset_closure (show Membership.mem A (F n) from
        mem_range_self n))
  let limitB := Classical.choose hextract
  have hlimitB := Classical.choose_spec hextract
  let q := Classical.choose hlimitB.2
  have hq := Classical.choose_spec hlimitB.2
  let limit : Real -> Real := fun t =>
    if ht : Membership.mem (Icc a b) t then
      limitB (show D from Subtype.mk t ht)
    else 0
  refine Exists.intro q (And.intro hq.1 (Exists.intro limit ?_))
  intro epsilon hepsilon
  have hmetric := Metric.tendsto_atTop.mp hq.2 epsilon hepsilon
  let n0 := Classical.choose hmetric
  have hn0 := Classical.choose_spec hmetric
  exact Exists.intro n0 (fun n hn t ht => by
    have hdist := BoundedContinuousFunction.dist_coe_le_dist
      (f := F (q n)) (g := limitB) (Subtype.mk t ht)
    have hlt := lt_of_le_of_lt hdist (by
      simpa [Function.comp_apply] using hn0 n hn)
    have ht' : a <= t /\ t <= b := ht
    have hlimit :
        limit t = limitB (Subtype.mk t ht) := by
      simp [limit, ht']
    rw [hlimit]
    have hFeval :
        F (q n) (Subtype.mk t ht) = f (q n) t := by
      rfl
    rw [hFeval] at hlt
    exact hlt)

/-- Linear interpolation of data on the fluid grid with mesh `1 / K`.
Negative times are clamped to the initial grid point. -/
private noncomputable def fluidGridInterpolate
    (K : PNat) (u : Nat -> Real) (t : Real) : Real :=
  let r := max t 0 * ((K : Nat) : Real)
  let n := Nat.floor r
  u n + (r - (n : Real)) * (u (n + 1) - u n)

/-- The polygonal interpolation agrees with the data at every grid node. -/
private theorem fluidGridInterpolate_nat_div
    (K : PNat) (u : Nat -> Real) (n : Nat) :
    fluidGridInterpolate K u
      ((n : Real) / ((K : Nat) : Real)) = u n := by
  have hK : (0 : Real) < ((K : Nat) : Real) := by
    exact_mod_cast K.property
  have hn : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
  simp [fluidGridInterpolate, max_eq_left (div_nonneg hn hK.le),
    ne_of_gt hK]

/-- At every nonnegative time, polygonal interpolation differs from the
corresponding step path by at most one adjacent grid increment. -/
private theorem fluidGridInterpolate_sub_step_abs_le
    (K : PNat) (u : Nat -> Real) {C t : Real} (ht : 0 <= t)
    (hadj : forall n, abs (u (n + 1) - u n) <= C) :
    abs (fluidGridInterpolate K u t -
      u (Nat.floor (t * ((K : Nat) : Real)))) <= C := by
  let r := t * ((K : Nat) : Real)
  let n := Nat.floor r
  have hr : 0 <= r := by
    exact mul_nonneg ht (Nat.cast_nonneg (K : Nat))
  have hnle : (n : Real) <= r := Nat.floor_le hr
  have hrlt : r < (n : Real) + 1 := Nat.lt_floor_add_one r
  have hw0 : 0 <= r - (n : Real) := sub_nonneg.mpr hnle
  have hw1 : r - (n : Real) <= 1 := by linarith
  rw [fluidGridInterpolate, max_eq_left ht]
  change abs (u n + (r - (n : Real)) * (u (n + 1) - u n) - u n) <= C
  rw [add_sub_cancel_left, abs_mul]
  have hwabs : abs (r - (n : Real)) <= 1 := by
    rw [abs_of_nonneg hw0]
    exact hw1
  calc
    abs (r - (n : Real)) * abs (u (n + 1) - u n)
        <= 1 * abs (u (n + 1) - u n) := by
          exact mul_le_mul_of_nonneg_right hwabs (abs_nonneg _)
    _ <= C := by simpa using hadj n

end FluidCompactness

namespace StateDepMOR.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-- A genuinely triangular calendar sample: every population size may use
its own independent-clock realization. -/
abbrev TriangularCalendarSample :=
  PNat -> CalendarPoissonSample (Buffer := Buffer) (Server := Server)

noncomputable def triangularCalendarExecutionFrom
    (N : Network Buffer Server)
    (initial : forall K : PNat, JobState Buffer (K : Nat)) :
    N.ScaledStochasticExecution
      (TriangularCalendarSample (Buffer := Buffer) (Server := Server)) where
  probability := MeasureTheory.diracProba (fun _ _ _ _ => 1)
  input := fun K omega t j k =>
    N.totalCalendarScaledInput K (omega K) t j k
  state := fun U K omega t i =>
    N.totalCalendarScaledQueueStateFrom U K (initial K) (omega K) t i
  allocation := fun U K omega t i j k =>
    N.totalCalendarScaledAllocationFrom initial U K (omega K) t i j k

noncomputable section

variable (N : Network Buffer Server)

private theorem ff_runTokens_append {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (xs ys : List (TokenType (Buffer := Buffer) (Server := Server))) :
    N.runTokens U x (xs ++ ys) =
      N.runTokens U (N.runTokens U x xs) ys := by
  induction xs generalizing x with
  | nil => simp [runTokens]
  | cons jk xs ih =>
      simp only [List.cons_append, runTokens]
      exact ih (N.queueStep U x jk)

private theorem ff_runAllocationCount_append {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (xs ys : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer) :
    N.runAllocationCount U x (xs ++ ys) i j k =
      N.runAllocationCount U x xs i j k +
        N.runAllocationCount U (N.runTokens U x xs) ys i j k := by
  induction xs generalizing x with
  | nil => simp [runAllocationCount, runTokens]
  | cons jk xs ih =>
      simp only [List.cons_append, runAllocationCount, runTokens]
      rw [ih]
      omega

private theorem ff_runAllocationCount_incompatible {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    N.runAllocationCount U x tokens i j k = 0 := by
  induction tokens generalizing x with
  | nil => rfl
  | cons jk rest ih =>
      simp only [runAllocationCount]
      have hne : Not (U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k) := by
        rintro ⟨haction, hj, _⟩
        have hlegal := U.legal x jk.1 jk.2
        rw [haction] at hlegal
        exact hij (hj ▸ hlegal.1)
      simp [hne, ih (N.queueStep U x jk)]

private theorem ff_runAllocationCount_le_count {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer) :
    N.runAllocationCount U x tokens i j k <= tokens.count (j, k) := by
  induction tokens generalizing x with
  | nil => simp [runAllocationCount]
  | cons jk rest ih =>
      have htail := ih (N.queueStep U x jk)
      by_cases hmatch : jk = (j, k)
      · subst jk
        simp only [runAllocationCount, List.count_cons, beq_self_eq_true,
          if_true]
        by_cases haction : U x j k = some i
        · simp only [haction, true_and, if_true]
          simpa [Nat.add_comm] using Nat.add_le_add_left htail 1
        · simp only [haction, false_and, if_false, zero_add]
          omega
      · have hbeq : (jk == (j, k)) = false := by
          exact beq_eq_false_iff_ne.mpr hmatch
        have halloc :
            Not (U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k) := by
          rintro ⟨_, hj, hk⟩
          apply hmatch
          exact Prod.ext hj hk
        simp only [runAllocationCount, List.count_cons, hbeq, if_false,
          halloc, zero_add]
        exact htail

private theorem ff_oneStep_incoming {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun q : Buffer =>
        if U x jk.1 jk.2 = some q /\ jk.1 = j /\ jk.2 = i
        then (1 : Real) else 0) =
      match U x jk.1 jk.2 with
      | none => 0
      | some _ => if jk.2 = i then 1 else 0 := by
  classical
  cases haction : U x jk.1 jk.2 with
  | none => simp [haction]
  | some q =>
      by_cases hki : jk.2 = i
      · subst i
        rw [Finset.sum_eq_single jk.1]
        · rw [Finset.sum_eq_single q]
          · simp [haction]
          · intro b _ hb
            simp [haction, hb, Ne.symm hb]
          · simp
        · intro s _ hs
          simp [haction, hs, Ne.symm hs]
        · simp
      · simp only [haction, hki, if_false]
        apply Finset.sum_eq_zero
        intro s _
        apply Finset.sum_eq_zero
        intro q' _
        simp [hki]

private theorem ff_oneStep_outgoing {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        if U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k
        then (1 : Real) else 0) =
      if U x jk.1 jk.2 = some i then 1 else 0 := by
  classical
  by_cases hi : U x jk.1 jk.2 = some i
  · rw [Finset.sum_eq_single jk.1]
    · rw [Finset.sum_eq_single jk.2]
      · simp [hi]
      · intro k _ hk
        simp [hi, hk, Ne.symm hk]
      · simp
    · intro j _ hj
      simp [hi, hj, Ne.symm hj]
    · simp
  · simp [hi]

private theorem ff_queueStep_coordinate_sub {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    ((N.queueStep U x jk i : Nat) : Real) - (x i : Real) =
      (match U x jk.1 jk.2 with
        | none => 0
        | some _ => if jk.2 = i then 1 else 0) -
      (if U x jk.1 jk.2 = some i then 1 else 0) := by
  have h :=
    N.jobsIn_queueStep_sub U x ({i} : Finset Buffer) jk
  cases haction : U x jk.1 jk.2 with
  | none => simpa [JobState.jobsIn, cutChange, haction] using h
  | some q =>
      by_cases hqi : q = i
      · subst q
        simpa [JobState.jobsIn, cutChange, haction] using h
      · simpa [JobState.jobsIn, cutChange, haction, hqi] using h

private theorem ff_runTokens_runAllocationCount_balance {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) :
    ((N.runTokens U x tokens i : Nat) : Real) - (x i : Real) =
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          (N.runAllocationCount U x tokens q j i : Nat)) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (N.runAllocationCount U x tokens i j k : Nat)) := by
  classical
  induction tokens generalizing x with
  | nil => simp [runTokens, runAllocationCount]
  | cons jk rest ih =>
      let xnext := N.queueStep U x jk
      have htail := ih xnext
      have hstep := ff_queueStep_coordinate_sub N U x jk i
      have hin := ff_oneStep_incoming N U x jk i
      have hout := ff_oneStep_outgoing N U x jk i
      simp only [runTokens, runAllocationCount, Nat.cast_add,
        Finset.sum_add_distrib]
      change
        ((N.runTokens U xnext rest i : Nat) : Real) - (x i : Real) = _
      change
        ((N.runTokens U xnext rest i : Nat) : Real) -
            ((xnext i : Nat) : Real) = _ at htail
      change
        ((xnext i : Nat) : Real) - (x i : Real) = _ at hstep
      rw [show
        ((N.runTokens U xnext rest i : Nat) : Real) - (x i : Real) =
          (((N.runTokens U xnext rest i : Nat) : Real) -
            ((xnext i : Nat) : Real)) +
          (((xnext i : Nat) : Real) - (x i : Real)) by ring]
      rw [htail, hstep, <- hin, <- hout]
      push_cast
      ring

private theorem ff_oneStep_total {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (jk : TokenType (Buffer := Buffer) (Server := Server)) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        Finset.univ.sum fun i : Buffer =>
          if U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k
          then 1 else 0) <= 1 := by
  classical
  cases haction : U x jk.1 jk.2 with
  | none => simp [haction]
  | some q =>
      rw [Finset.sum_eq_single jk.1]
      · rw [Finset.sum_eq_single jk.2]
        · rw [Finset.sum_eq_single q]
          · simp [haction]
          · intro i _ hi
            simp [haction, hi, Ne.symm hi]
          · simp
        · intro k _ hk
          simp [haction, hk, Ne.symm hk]
        · simp
      · intro j _ hj
        simp [haction, hj, Ne.symm hj]
      · simp

private theorem ff_sum_runAllocationCount_le_length {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        Finset.univ.sum fun i : Buffer =>
          N.runAllocationCount U x tokens i j k) <= tokens.length := by
  classical
  induction tokens generalizing x with
  | nil => simp [runAllocationCount]
  | cons jk rest ih =>
      simp only [runAllocationCount, Finset.sum_add_distrib,
        List.length_cons]
      have htail := ih (N.queueStep U x jk)
      have hone :
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer =>
              Finset.univ.sum fun i : Buffer =>
                if U x jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k
                then 1 else 0) <= 1 :=
        ff_oneStep_total N U x jk
      omega

private theorem ff_runTokens_l1_le_two_mul_length {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    (Finset.univ.sum fun i : Buffer =>
      abs (((N.runTokens U x tokens i : Nat) : Real) - (x i : Real))) <=
      2 * tokens.length := by
  classical
  let incoming : Buffer -> Real := fun i =>
    Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun q : Buffer =>
        (N.runAllocationCount U x tokens q j i : Nat)
  let outgoing : Buffer -> Real := fun i =>
    Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        (N.runAllocationCount U x tokens i j k : Nat)
  have hcoord (i : Buffer) :
      abs (((N.runTokens U x tokens i : Nat) : Real) - (x i : Real)) <=
        incoming i + outgoing i := by
    rw [ff_runTokens_runAllocationCount_balance N U x tokens i]
    push_cast
    change abs (incoming i - outgoing i) <= incoming i + outgoing i
    rw [abs_sub_le_iff]
    have hin_nonneg : 0 <= incoming i := by
      dsimp [incoming]
      positivity
    have hout_nonneg : 0 <= outgoing i := by
      dsimp [outgoing]
      positivity
    constructor <;> linarith
  calc
    (Finset.univ.sum fun i : Buffer =>
        abs (((N.runTokens U x tokens i : Nat) : Real) - (x i : Real))) <=
        Finset.univ.sum fun i : Buffer => incoming i + outgoing i :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = 2 * (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer =>
            Finset.univ.sum fun i : Buffer =>
              (N.runAllocationCount U x tokens i j k : Nat)) := by
      have hin :
          (Finset.univ.sum fun i : Buffer => incoming i) =
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer =>
                Finset.univ.sum fun i : Buffer =>
                  (N.runAllocationCount U x tokens i j k : Nat)) := by
        dsimp [incoming]
        push_cast
        rw [Finset.sum_comm]
      have hout :
          (Finset.univ.sum fun i : Buffer => outgoing i) =
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer =>
                Finset.univ.sum fun i : Buffer =>
                  (N.runAllocationCount U x tokens i j k : Nat)) := by
        dsimp [outgoing]
        push_cast
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
      rw [Finset.sum_add_distrib, hin, hout]
      ring
    _ <= 2 * tokens.length := by
      exact_mod_cast
        (Nat.mul_le_mul_left 2
          (ff_sum_runAllocationCount_le_length N U x tokens))

private theorem ff_runAllocationCount_batch_increment_le_length {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (pre batch :
      List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer) :
    N.runAllocationCount U x (pre ++ batch) i j k -
        N.runAllocationCount U x pre i j k <= batch.length := by
  rw [ff_runAllocationCount_append]
  have hcount :=
    ff_runAllocationCount_le_count N U
      (N.runTokens U x pre) batch i j k
  have hlength := hcount.trans List.count_le_length
  omega

private theorem ff_runTokens_batch_l1_le_two_mul_length {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (pre batch :
      List (TokenType (Buffer := Buffer) (Server := Server))) :
    (Finset.univ.sum fun i : Buffer =>
      abs (((N.runTokens U x (pre ++ batch) i : Nat) : Real) -
        ((N.runTokens U x pre i : Nat) : Real))) <=
      2 * batch.length := by
  rw [ff_runTokens_append]
  exact ff_runTokens_l1_le_two_mul_length N U
    (N.runTokens U x pre) batch

private noncomputable def ff_gridTime
    (T : Real) (K : PNat) (l : Nat) : Real :=
  T * ((min l (K : Nat) : Nat) : Real) / (K : Nat)

private noncomputable def ff_gridInputCount
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) (j : Server) (k : Buffer) : Nat :=
  Nat.floor (((K : Nat) : Real) * A (ff_gridTime T K l) j k)

private noncomputable def ff_gridTokenBatch
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  (Finset.univ :
      Finset (TokenType (Buffer := Buffer) (Server := Server))).toList.flatMap
    fun jk =>
      List.replicate
        (ff_gridInputCount T A K (l + 1) jk.1 jk.2 -
          ff_gridInputCount T A K l jk.1 jk.2)
        jk

private noncomputable def ff_gridTokenPrefix
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) : Nat ->
      List (TokenType (Buffer := Buffer) (Server := Server))
  | 0 => []
  | l + 1 =>
      ff_gridTokenPrefix T A K l ++ ff_gridTokenBatch T A K l

private theorem ff_gridTime_mem_Icc
    (T : Real) (hT : 0 < T) (K : PNat) (l : Nat) :
    ff_gridTime T K l ∈ Set.Icc (0 : Real) T := by
  have hK : 0 < ((K : Nat) : Real) := by positivity
  have hmin : ((min l (K : Nat) : Nat) : Real) <= (K : Nat) := by
    exact_mod_cast Nat.min_le_right l (K : Nat)
  constructor
  · unfold ff_gridTime
    positivity
  · unfold ff_gridTime
    apply (div_le_iff₀ hK).2
    exact mul_le_mul_of_nonneg_left hmin (le_of_lt hT)

private theorem ff_gridTime_mono
    (T : Real) (hT : 0 < T) (K : PNat) :
    Monotone (ff_gridTime T K) := by
  intro l m hlm
  unfold ff_gridTime
  have hmin : min l (K : Nat) <= min m (K : Nat) :=
    min_le_min_right (K : Nat) hlm
  have hcast :
      ((min l (K : Nat) : Nat) : Real) <= min m (K : Nat) := by
    exact_mod_cast hmin
  gcongr

private theorem ff_gridInputCount_mono
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat) (j : Server) (k : Buffer) :
    Monotone (fun l => ff_gridInputCount T A K l j k) := by
  intro l m hlm
  unfold ff_gridInputCount
  apply Nat.floor_mono
  apply mul_le_mul_of_nonneg_left
  · exact hA.2.1 j k
      (ff_gridTime_mem_Icc T hT K l)
      (ff_gridTime_mem_Icc T hT K m)
      (ff_gridTime_mono T hT K hlm)
  · positivity

private theorem ff_gridInputCount_zero
    (T : Real) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat) (j : Server) (k : Buffer) :
    ff_gridInputCount T A K 0 j k = 0 := by
  simp [ff_gridInputCount, ff_gridTime, hA.2.2 j k]

private theorem ff_count_flatMap_replicate_of_nodup
    {Alpha : Type*} [BEq Alpha] [LawfulBEq Alpha]
    (a : Alpha) (l : List Alpha) (f : Alpha -> Nat)
    (hnodup : l.Nodup) (ha : a ∈ l) :
    (l.flatMap fun b => List.replicate (f b) b).count a = f a := by
  induction l with
  | nil => simp at ha
  | cons b rest ih =>
      rw [List.nodup_cons] at hnodup
      rcases hnodup with ⟨hb, hrest⟩
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · have hz :
            (rest.flatMap fun c => List.replicate (f c) c).count a = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          rw [List.mem_flatMap] at hmem
          obtain ⟨c, hc, hrep⟩ := hmem
          rw [List.mem_replicate] at hrep
          exact hb (hrep.2 ▸ hc)
        simp [List.count_append, List.count_replicate, hz]
      · have hba : b ≠ a := by
          intro h
          subst b
          exact hb ha
        simpa [List.count_append, List.count_replicate, hba] using
          ih hrest ha

private theorem ff_gridTokenBatch_count
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) (j : Server) (k : Buffer) :
    (ff_gridTokenBatch T A K l).count (j, k) =
      ff_gridInputCount T A K (l + 1) j k -
        ff_gridInputCount T A K l j k := by
  classical
  unfold ff_gridTokenBatch
  refine ff_count_flatMap_replicate_of_nodup
    (j, k)
    (Finset.univ :
      Finset (TokenType (Buffer := Buffer) (Server := Server))).toList
    (fun jk =>
      ff_gridInputCount T A K (l + 1) jk.1 jk.2 -
        ff_gridInputCount T A K l jk.1 jk.2) ?_ ?_
  · exact Finset.nodup_toList _
  · simp

private theorem ff_gridTokenPrefix_count
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat) (l : Nat)
    (j : Server) (k : Buffer) :
    (ff_gridTokenPrefix T A K l).count (j, k) =
      ff_gridInputCount T A K l j k := by
  induction l with
  | zero =>
      simp [ff_gridTokenPrefix,
        ff_gridInputCount_zero T A hA K j k]
  | succ l ih =>
      rw [show ff_gridTokenPrefix T A K (l + 1) =
        ff_gridTokenPrefix T A K l ++ ff_gridTokenBatch T A K l by rfl]
      rw [List.count_append, ih, ff_gridTokenBatch_count]
      exact Nat.add_sub_of_le
        (ff_gridInputCount_mono T hT A hA K j k
          (Nat.le_succ l))

private def ff_clamp01 (r : Real) : Real :=
  max 0 (min 1 r)

private theorem ff_clamp01_monotone : Monotone ff_clamp01 := by
  intro r s hrs
  unfold ff_clamp01
  exact max_le_max_left 0 (min_le_min_left 1 hrs)

private theorem ff_clamp01_of_nonpos {r : Real} (hr : r <= 0) :
    ff_clamp01 r = 0 := by
  unfold ff_clamp01
  simp [min_eq_right hr, hr]

private theorem ff_clamp01_of_one_le {r : Real} (hr : 1 <= r) :
    ff_clamp01 r = 1 := by
  unfold ff_clamp01
  simp [min_eq_left hr, hr]

private noncomputable def ff_rampInterpolate
    (K : PNat) (values : Nat -> Real) (t T : Real) : Real :=
  values 0 +
    Finset.sum (Finset.range (K : Nat)) fun l =>
      (values (l + 1) - values l) *
        ff_clamp01 (((K : Nat) : Real) * t / T - l)

private noncomputable def ff_polygonalInputPath
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) : MatrixPath Server Buffer :=
  fun t j k =>
    ff_rampInterpolate K
      (fun l => (ff_gridInputCount T A K l j k : Real) / (K : Nat))
      t T

private theorem ff_sum_range_sub
    (values : Nat -> Real) (l : Nat) :
    values 0 +
      Finset.sum (Finset.range l) (fun q => values (q + 1) - values q) =
      values l := by
  induction l with
  | zero => simp
  | succ l ih =>
      simp only [Finset.sum_range_succ]
      linarith

private theorem ff_rampInterpolate_grid
    (K : PNat) (values : Nat -> Real) (T : Real) (hT : 0 < T)
    (l : Nat) (hl : l <= (K : Nat)) :
    ff_rampInterpolate K values
      (T * (l : Real) / (K : Nat)) T = values l := by
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hscale :
      ((K : Nat) : Real) * (T * (l : Real) / (K : Nat)) / T =
        (l : Real) := by
    field_simp
  unfold ff_rampInterpolate
  rw [hscale]
  have hsum :
      (Finset.sum (Finset.range (K : Nat)) fun q =>
        (values (q + 1) - values q) *
          ff_clamp01 ((l : Real) - (q : Real))) =
        Finset.sum (Finset.range l) fun q =>
          (values (q + 1) - values q) := by
    rw [<- Finset.sum_subset
      (show Finset.range l <= Finset.range (K : Nat) by
        exact Finset.range_mono hl)]
    · apply Finset.sum_congr rfl
      intro q hq
      have hql : q < l := Finset.mem_range.mp hq
      have hone : (1 : Real) <= (l : Real) - (q : Real) := by
        have hcast : (q : Real) + 1 <= (l : Real) := by
          exact_mod_cast (show q + 1 <= l by omega)
        linarith
      rw [ff_clamp01_of_one_le hone, mul_one]
    · intro q hqK hql
      have hlq : l <= q := by
        simpa only [Finset.mem_range, not_lt] using hql
      have hcast : (l : Real) <= (q : Real) := by exact_mod_cast hlq
      have hzero : (l : Real) - (q : Real) <= 0 := by linarith
      rw [ff_clamp01_of_nonpos hzero, mul_zero]
  rw [hsum]
  exact ff_sum_range_sub values l

private theorem ff_gridTime_eq_gridPoint
    (T : Real) (K : PNat) (l : Nat) (hl : l <= (K : Nat)) :
    ff_gridTime T K l = T * (l : Real) / (K : Nat) := by
  simp [ff_gridTime, Nat.min_eq_left hl]

private theorem ff_polygonalInputPath_grid
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) (hl : l <= (K : Nat))
    (j : Server) (k : Buffer) :
    ff_polygonalInputPath T A K (ff_gridTime T K l) j k =
      (ff_gridInputCount T A K l j k : Real) / (K : Nat) := by
  rw [ff_gridTime_eq_gridPoint T K l hl]
  exact ff_rampInterpolate_grid K _ T hT l hl

private theorem ff_rampInterpolate_monotoneOn
    (K : PNat) (values : Nat -> Real) (T : Real) (hT : 0 < T)
    (hvalues : forall l, l < (K : Nat) ->
      values l <= values (l + 1)) :
    MonotoneOn (fun t => ff_rampInterpolate K values t T)
      (Set.Icc (0 : Real) T) := by
  intro s _ t _ hst
  unfold ff_rampInterpolate
  change values 0 + _ <= values 0 + _
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro l hl
  apply mul_le_mul_of_nonneg_left
  · apply ff_clamp01_monotone
    apply sub_le_sub_right
    apply div_le_div_of_nonneg_right _ (le_of_lt hT)
    exact mul_le_mul_of_nonneg_left hst (by positivity)
  · exact sub_nonneg.mpr (hvalues l (Finset.mem_range.mp hl))

private theorem ff_polygonalInputPath_monotoneOn
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat) (j : Server) (k : Buffer) :
    MonotoneOn (fun t => ff_polygonalInputPath T A K t j k)
      (Set.Icc (0 : Real) T) := by
  apply ff_rampInterpolate_monotoneOn K _ T hT
  intro l hl
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    (ff_gridInputCount_mono T hT A hA K j k (Nat.le_succ l))

private theorem ff_gridInputCount_approx
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat) (l : Nat)
    (j : Server) (k : Buffer) :
    abs ((ff_gridInputCount T A K l j k : Real) / (K : Nat) -
      A (ff_gridTime T K l) j k) < 1 / (K : Nat) := by
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hnonneg : 0 <= A (ff_gridTime T K l) j k := by
    have hzero := hA.2.2 j k
    rw [<- hzero]
    exact hA.2.1 j k
      (by
        constructor
        · rfl
        · exact le_of_lt hT)
      (ff_gridTime_mem_Icc T hT K l)
      (ff_gridTime_mem_Icc T hT K l).1
  have hlo :
      ((ff_gridInputCount T A K l j k : Nat) : Real) <=
        (K : Real) * A (ff_gridTime T K l) j k := by
    exact Nat.floor_le (mul_nonneg (le_of_lt hK) hnonneg)
  have hhi :
      (K : Real) * A (ff_gridTime T K l) j k <
        (ff_gridInputCount T A K l j k : Real) + 1 := by
    exact Nat.lt_floor_add_one _
  rw [show
    (ff_gridInputCount T A K l j k : Real) / (K : Nat) -
        A (ff_gridTime T K l) j k =
      ((ff_gridInputCount T A K l j k : Real) -
        (K : Real) * A (ff_gridTime T K l) j k) / (K : Nat) by
          field_simp]
  rw [abs_div, abs_of_pos hK]
  apply (div_lt_iff₀ hK).2
  rw [abs_lt]
  have hone : 1 / (K : Real) * (K : Real) = 1 := by
    field_simp
  rw [hone]
  constructor <;> linarith

private theorem ff_polygonalInputPath_between_grid
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat)
    {l : Nat} (hl : l < (K : Nat)) {t : Real}
    (ht : t ∈ Set.Icc
      (ff_gridTime T K l) (ff_gridTime T K (l + 1)))
    (j : Server) (k : Buffer) :
    ff_polygonalInputPath T A K t j k ∈ Set.Icc
      ((ff_gridInputCount T A K l j k : Real) / (K : Nat))
      ((ff_gridInputCount T A K (l + 1) j k : Real) / (K : Nat)) := by
  have hmono := ff_polygonalInputPath_monotoneOn T hT A hA K j k
  have hlt : l + 1 <= (K : Nat) := by omega
  have hleftmem := ff_gridTime_mem_Icc T hT K l
  have hrightmem := ff_gridTime_mem_Icc T hT K (l + 1)
  constructor
  · rw [<- ff_polygonalInputPath_grid T hT A K l (le_of_lt hl) j k]
    exact hmono hleftmem
      ⟨hleftmem.1.trans ht.1, ht.2.trans hrightmem.2⟩ ht.1
  · rw [<- ff_polygonalInputPath_grid T hT A K (l + 1) hlt j k]
    exact hmono
      ⟨hleftmem.1.trans ht.1, ht.2.trans hrightmem.2⟩
      hrightmem ht.2

private theorem ff_polygonalInputPath_uniform_error
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat)
    (j : Server) (k : Buffer) (eta : Real)
    (hosc : forall s, s ∈ Set.Icc (0 : Real) T ->
      forall t, t ∈ Set.Icc (0 : Real) T ->
        abs (s - t) <= T / (K : Nat) ->
        abs (A s j k - A t j k) <= eta)
    (t : Real) (ht : t ∈ Set.Icc (0 : Real) T) :
    abs (ff_polygonalInputPath T A K t j k - A t j k) <
      eta + 1 / (K : Nat) := by
  have hK : (0 : Real) < (K : Nat) := by positivity
  let r : Real := (K : Real) * t / T
  let l : Nat := Nat.floor r
  by_cases htT : t = T
  · subst t
    have hgrid : ff_gridTime T K (K : Nat) = T := by
      simp [ff_gridTime]
    have hpath :=
      ff_polygonalInputPath_grid T hT A K (K : Nat) le_rfl j k
    rw [hgrid] at hpath
    rw [hpath]
    have hfloor := ff_gridInputCount_approx T hT A hA K (K : Nat) j k
    rw [hgrid] at hfloor
    have heta : 0 <= eta := by
      have hz := hosc T ⟨le_of_lt hT, le_rfl⟩
        T ⟨le_of_lt hT, le_rfl⟩ (by
          simp only [sub_self, abs_zero]
          exact div_nonneg (le_of_lt hT) (le_of_lt hK))
      simpa using hz
    exact hfloor.trans_le (by linarith)
  · have htlt : t < T := lt_of_le_of_ne ht.2 htT
    have hr0 : 0 <= r := by
      dsimp [r]
      exact div_nonneg
        (mul_nonneg (le_of_lt hK) ht.1) (le_of_lt hT)
    have hrK : r < (K : Nat) := by
      dsimp [r]
      apply (div_lt_iff₀ hT).2
      nlinarith
    have hlK : l < (K : Nat) := (Nat.floor_lt hr0).2 hrK
    have hlfloor : (l : Real) <= r := Nat.floor_le hr0
    have hfloorlt : r < (l : Real) + 1 := Nat.lt_floor_add_one r
    have hleft : ff_gridTime T K l <= t := by
      rw [ff_gridTime_eq_gridPoint T K l (le_of_lt hlK)]
      apply (div_le_iff₀ hK).2
      dsimp [r] at hlfloor
      have hmul := (le_div_iff₀ hT).1 hlfloor
      nlinarith
    have hright : t <= ff_gridTime T K (l + 1) := by
      rw [ff_gridTime_eq_gridPoint T K (l + 1) (by omega)]
      apply (le_div_iff₀ hK).2
      dsimp [r] at hfloorlt
      have hmul := (div_lt_iff₀ hT).1 hfloorlt
      calc
        t * (K : Real) = (K : Real) * t := mul_comm _ _
        _ <= ((l : Real) + 1) * T := le_of_lt hmul
        _ = T * ((l + 1 : Nat) : Real) := by
          push_cast
          ring
    have hbetween :=
      ff_polygonalInputPath_between_grid T hT A hA K hlK
        ⟨hleft, hright⟩ j k
    have hstep :
        ff_gridTime T K (l + 1) - ff_gridTime T K l =
          T / (K : Nat) := by
      rw [ff_gridTime_eq_gridPoint T K l (le_of_lt hlK),
        ff_gridTime_eq_gridPoint T K (l + 1) (by omega)]
      push_cast
      field_simp
      ring
    have hdistLeft :
        abs (ff_gridTime T K l - t) <= T / (K : Nat) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hleft)]
      linarith
    have hdistRight :
        abs (ff_gridTime T K (l + 1) - t) <= T / (K : Nat) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hright)]
      linarith
    have hoscLeft := hosc (ff_gridTime T K l)
      (ff_gridTime_mem_Icc T hT K l) t ht hdistLeft
    have hoscRight := hosc (ff_gridTime T K (l + 1))
      (ff_gridTime_mem_Icc T hT K (l + 1)) t ht hdistRight
    have happLeft := ff_gridInputCount_approx T hT A hA K l j k
    have happRight :=
      ff_gridInputCount_approx T hT A hA K (l + 1) j k
    rw [abs_lt]
    constructor
    · rw [neg_lt_sub_iff_lt_add]
      have hlower := hbetween.1
      rw [abs_lt] at happLeft
      rw [abs_le] at hoscLeft
      linarith
    · rw [sub_lt_iff_lt_add]
      have hupper := hbetween.2
      rw [abs_lt] at happRight
      rw [abs_le] at hoscRight
      linarith

private theorem ff_polygonalInputPath_uniform_approx
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (j : Server) (k : Buffer)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists K0 : Nat, forall K : PNat, K0 <= (K : Nat) ->
      forall t, t ∈ Set.Icc (0 : Real) T ->
        abs (ff_polygonalInputPath T A K t j k - A t j k) <
          epsilon := by
  have hcontinuous :
      ContinuousOn (fun t => A t j k) (Set.Icc (0 : Real) T) := by
    simpa [Set.uIcc_of_le (le_of_lt hT)] using
      (hA.1 j k).continuousOn
  have huniform :
      UniformContinuousOn (fun t => A t j k) (Set.Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcontinuous
  obtain ⟨delta, hdelta, hmodulus⟩ :=
    (Metric.uniformContinuousOn_iff.mp huniform)
      (epsilon / 2) (by positivity)
  obtain ⟨K0, hK0⟩ :=
    exists_nat_gt (max (T / delta) (2 / epsilon))
  refine ⟨K0, ?_⟩
  intro K hKK t ht
  have hK0real : (K0 : Real) <= (K : Nat) := by exact_mod_cast hKK
  have hTdelta : T / delta < (K : Real) :=
    lt_of_le_of_lt (le_max_left _ _) hK0 |>.trans_le hK0real
  have h2epsilon : 2 / epsilon < (K : Real) :=
    lt_of_le_of_lt (le_max_right _ _) hK0 |>.trans_le hK0real
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hmesh : T / (K : Nat) < delta := by
    apply (div_lt_iff₀ hK).2
    apply (div_lt_iff₀ hdelta).1 at hTdelta
    nlinarith
  have hround : 1 / (K : Nat) < epsilon / 2 := by
    apply (div_lt_iff₀ hK).2
    apply (div_lt_iff₀ hepsilon).1 at h2epsilon
    nlinarith
  have hosc :
      forall s, s ∈ Set.Icc (0 : Real) T ->
      forall t, t ∈ Set.Icc (0 : Real) T ->
        abs (s - t) <= T / (K : Nat) ->
        abs (A s j k - A t j k) <= epsilon / 2 := by
    intro s hs t ht hdist
    have hclose : dist s t < delta := by
      rw [Real.dist_eq]
      exact hdist.trans_lt hmesh
    have hout := hmodulus s hs t ht hclose
    simpa [Real.dist_eq] using le_of_lt hout
  have herr :=
    ff_polygonalInputPath_uniform_error T hT A hA K j k
      (epsilon / 2) hosc t ht
  linarith

private def fi_hatWeight (r : Real) (l : Nat) : Real :=
  max 0 (1 - abs (r - l))

private noncomputable def fi_polygonalInterpolate
    (K : PNat) (values : Nat -> Real) (t T : Real) : Real :=
  Finset.sum (Finset.range ((K : Nat) + 1)) fun l =>
    fi_hatWeight (((K : Nat) : Real) * t / T) l * values l

private theorem fi_hatWeight_nat_self (l : Nat) :
    fi_hatWeight (l : Real) l = 1 := by
  simp [fi_hatWeight]

private theorem fi_hatWeight_nat_ne {l q : Nat} (hql : q ≠ l) :
    fi_hatWeight (l : Real) q = 0 := by
  have hgap : (1 : Real) <= abs ((l : Real) - q) := by
    rcases lt_or_gt_of_ne (Ne.symm hql) with hlq | hql'
    · rw [abs_of_nonpos]
      · have hcast : (l : Real) + 1 <= q := by
          exact_mod_cast (show l + 1 <= q by omega)
        linarith
      · have hcast : (l : Real) <= q := by exact_mod_cast (show l <= q by omega)
        linarith
    · rw [abs_of_nonneg]
      · have hcast : (q : Real) + 1 <= l := by
          exact_mod_cast (show q + 1 <= l by omega)
        linarith
      · have hcast : (q : Real) <= l := by exact_mod_cast (show q <= l by omega)
        linarith
  simp [fi_hatWeight, max_eq_left (by linarith : 1 - abs ((l : Real) - q) <= 0)]

private theorem fi_polygonalInterpolate_grid
    (K : PNat) (values : Nat -> Real) (T : Real) (hT : 0 < T)
    (l : Nat) (hl : l <= (K : Nat)) :
    fi_polygonalInterpolate K values
      (T * (l : Real) / (K : Nat)) T = values l := by
  have hscale :
      ((K : Nat) : Real) * (T * (l : Real) / (K : Nat)) / T =
        (l : Real) := by
    have hK : ((K : Nat) : Real) ≠ 0 := by positivity
    field_simp
  unfold fi_polygonalInterpolate
  rw [hscale, Finset.sum_eq_single l]
  · simp [fi_hatWeight]
  · intro q hq hql
    simp [fi_hatWeight_nat_ne hql]
  · simp only [Finset.mem_range]
    omega

private theorem fi_hatWeight_nonnegative (r : Real) (l : Nat) :
    0 <= fi_hatWeight r l :=
  le_max_left _ _

private theorem fi_hatWeight_eq_zero_of_one_le_abs
    {r : Real} {l : Nat} (h : 1 <= abs (r - l)) :
    fi_hatWeight r l = 0 := by
  simp [fi_hatWeight, max_eq_left (by linarith : 1 - abs (r - l) <= 0)]

private theorem fi_sum_hatWeight_eq_one
    (K : PNat) {r : Real}
    (hr0 : 0 <= r) (hrK : r <= (K : Nat)) :
    Finset.sum (Finset.range ((K : Nat) + 1)) (fi_hatWeight r) = 1 := by
  classical
  let n : Nat := Nat.floor r
  have hn_le : (n : Real) <= r := Nat.floor_le hr0
  have hr_lt : r < (n : Real) + 1 := Nat.lt_floor_add_one r
  by_cases heq : r = (K : Nat)
  · subst r
    rw [Finset.sum_eq_single (K : Nat)]
    · simp [fi_hatWeight]
    · intro l hl hlne
      have hlK : l < (K : Nat) + 1 := Finset.mem_range.mp hl
      have hl_le : l <= (K : Nat) := by omega
      have hgap : (1 : Real) <= abs (((K : Nat) : Real) - l) := by
        rw [abs_of_nonneg]
        · have hcast : (l : Real) + 1 <= (K : Nat) := by
            exact_mod_cast (show l + 1 <= (K : Nat) by omega)
          linarith
        · have hcast : (l : Real) <= (K : Nat) := by
            exact_mod_cast hl_le
          linarith
      exact fi_hatWeight_eq_zero_of_one_le_abs hgap
    · simp
  · have hrKlt : r < (K : Nat) := lt_of_le_of_ne hrK heq
    have hnK : n < (K : Nat) := (Nat.floor_lt hr0).2 hrKlt
    have hsubset :
        ({n, n + 1} : Finset Nat) <=
          Finset.range ((K : Nat) + 1) := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact Finset.mem_range.mpr (by omega)
      · exact Finset.mem_range.mpr (by omega)
    have hzero :
        forall l, l ∈ Finset.range ((K : Nat) + 1) ->
          l ∉ ({n, n + 1} : Finset Nat) -> fi_hatWeight r l = 0 := by
      intro l hl hlpair
      have hln : l ≠ n := by simpa using fun h => hlpair (by simp [h])
      have hln1 : l ≠ n + 1 := by simpa using fun h => hlpair (by simp [h])
      apply fi_hatWeight_eq_zero_of_one_le_abs
      by_cases hlt : l < n
      · rw [abs_of_nonneg]
        · have hcast : (l : Real) + 1 <= n := by exact_mod_cast (show l + 1 <= n by omega)
          linarith
        · have hcast : (l : Real) <= n := by
            exact_mod_cast (show l <= n by omega)
          linarith
      · have hnlt : n + 1 < l := by omega
        rw [abs_of_nonpos]
        · have hcast : (n : Real) + 2 <= l := by exact_mod_cast (show n + 2 <= l by omega)
          linarith
        · have hcast : (n : Real) + 1 <= l := by exact_mod_cast (show n + 1 <= l by omega)
          linarith
    rw [<- Finset.sum_subset hsubset hzero]
    rw [Finset.sum_pair (by omega : n ≠ n + 1)]
    have hleft : 0 <= 1 - abs (r - (n : Real)) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hn_le)]
      linarith
    have hright :
        0 <= 1 - abs (r - ((n + 1 : Nat) : Real)) := by
      rw [abs_of_nonpos]
      · norm_num at *
        linarith
      · norm_num at *
        linarith
    simp only [fi_hatWeight, max_eq_right hleft, max_eq_right hright]
    rw [abs_of_nonneg (sub_nonneg.mpr hn_le), abs_of_nonpos]
    · norm_num at *
      ring
    · norm_num at *
      linarith

private theorem fi_polygonalInterpolate_nonnegative
    (K : PNat) (values : Nat -> Real) (t T : Real)
    (hvalues : forall l, l < (K : Nat) + 1 -> 0 <= values l) :
    0 <= fi_polygonalInterpolate K values t T := by
  unfold fi_polygonalInterpolate
  apply Finset.sum_nonneg
  intro l hl
  exact mul_nonneg (fi_hatWeight_nonnegative _ _)
    (hvalues l (Finset.mem_range.mp hl))

private theorem fi_polygonalInterpolate_const
    (K : PNat) (c t T : Real) (hT : 0 < T)
    (ht : t ∈ Icc (0 : Real) T) :
    fi_polygonalInterpolate K (fun _ => c) t T = c := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) ht.1)
      (le_of_lt hT)
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  unfold fi_polygonalInterpolate
  rw [<- Finset.sum_mul, fi_sum_hatWeight_eq_one K hr0 hrK, one_mul]

private theorem fi_polygonalInterpolate_add
    (K : PNat) (a b : Nat -> Real) (t T : Real) :
    fi_polygonalInterpolate K (fun l => a l + b l) t T =
      fi_polygonalInterpolate K a t T +
        fi_polygonalInterpolate K b t T := by
  simp only [fi_polygonalInterpolate, mul_add, Finset.sum_add_distrib]

private theorem fi_polygonalInterpolate_sub
    (K : PNat) (a b : Nat -> Real) (t T : Real) :
    fi_polygonalInterpolate K (fun l => a l - b l) t T =
      fi_polygonalInterpolate K a t T -
        fi_polygonalInterpolate K b t T := by
  simp only [fi_polygonalInterpolate, mul_sub, Finset.sum_sub_distrib]

private theorem fi_polygonalInterpolate_sum
    {I : Type w} [Fintype I]
    (K : PNat) (a : Nat -> I -> Real) (t T : Real) :
    fi_polygonalInterpolate K (fun l => Finset.univ.sum (a l)) t T =
      Finset.univ.sum (fun i =>
        fi_polygonalInterpolate K (fun l => a l i) t T) := by
  classical
  unfold fi_polygonalInterpolate
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem fi_polygonal_state_simplex
    (K : PNat) (x : Nat -> Buffer -> Real) {t T : Real}
    (hT : 0 < T) (ht : t ∈ Icc (0 : Real) T)
    (hx : forall l, l < (K : Nat) + 1 -> IsFluidState (x l)) :
    IsFluidState (fun i => fi_polygonalInterpolate K (fun l => x l i) t T) := by
  constructor
  · intro i
    apply fi_polygonalInterpolate_nonnegative
    intro l hl
    exact (hx l hl).1 i
  · rw [<- fi_polygonalInterpolate_sum K x t T]
    rw [show
      fi_polygonalInterpolate K (fun l => Finset.univ.sum (x l)) t T =
        fi_polygonalInterpolate K (fun _ => (1 : Real)) t T by
          unfold fi_polygonalInterpolate
          apply Finset.sum_congr rfl
          intro l hl
          dsimp only
          rw [(hx l (Finset.mem_range.mp hl)).2]]
    exact fi_polygonalInterpolate_const K 1 t T hT ht

private theorem fi_polygonal_zero
    (K : PNat) (values : Nat -> Real) (t T : Real)
    (hzero : forall l, l < (K : Nat) + 1 -> values l = 0) :
    fi_polygonalInterpolate K values t T = 0 := by
  unfold fi_polygonalInterpolate
  apply Finset.sum_eq_zero
  intro l hl
  rw [hzero l (Finset.mem_range.mp hl), mul_zero]

private theorem fi_polygonal_allocation_incompatible
    (K : PNat) (e : Nat -> Buffer -> Server -> Buffer -> Real)
    (t T : Real) (i : Buffer) (j : Server) (k : Buffer)
    (hzero : forall l, l < (K : Nat) + 1 -> e l i j k = 0) :
    fi_polygonalInterpolate K (fun l => e l i j k) t T = 0 :=
  fi_polygonal_zero K _ t T hzero

private theorem fi_polygonal_initial
    (K : PNat) (values : Nat -> Real) (T : Real) (hT : 0 < T) :
    fi_polygonalInterpolate K values 0 T = values 0 := by
  convert fi_polygonalInterpolate_grid K values T hT 0 (Nat.zero_le _) using 1
  simp

private theorem fi_polygonal_balance
    {J Q R : Type*} [Fintype J] [Fintype Q] [Fintype R]
    (K : PNat) (x : Nat -> Real) (x0 : Real)
    (incoming : Nat -> J -> Real) (outgoing : Nat -> Q -> Real)
    {t T : Real} (hT : 0 < T) (ht : t ∈ Icc (0 : Real) T)
    (hbalance : forall l, l < (K : Nat) + 1 ->
      x l = x0 + Finset.univ.sum (incoming l) -
        Finset.univ.sum (outgoing l)) :
    fi_polygonalInterpolate K x t T =
      x0 +
        Finset.univ.sum (fun j =>
          fi_polygonalInterpolate K (fun l => incoming l j) t T) -
        Finset.univ.sum (fun q =>
          fi_polygonalInterpolate K (fun l => outgoing l q) t T) := by
  let rhs : Nat -> Real := fun l =>
    x0 + Finset.univ.sum (incoming l) - Finset.univ.sum (outgoing l)
  have hpoly : fi_polygonalInterpolate K x t T =
      fi_polygonalInterpolate K rhs t T := by
    unfold fi_polygonalInterpolate
    apply Finset.sum_congr rfl
    intro l hl
    rw [hbalance l (Finset.mem_range.mp hl)]
  rw [hpoly]
  dsimp [rhs]
  rw [fi_polygonalInterpolate_sub, fi_polygonalInterpolate_add]
  rw [fi_polygonalInterpolate_const K x0 t T hT ht]
  rw [fi_polygonalInterpolate_sum, fi_polygonalInterpolate_sum]

private noncomputable def fi_polygonalInputPath
    (T : Real) (A : MatrixPath Server Buffer) (K : PNat) :
    MatrixPath Server Buffer :=
  fun t j k =>
    fi_polygonalInterpolate K
      (fun l => (ff_gridInputCount T A K l j k : Real) / (K : Nat))
      t T

private theorem fi_polygonalInputPath_grid
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) (hl : l <= (K : Nat))
    (j : Server) (k : Buffer) :
    fi_polygonalInputPath T A K (ff_gridTime T K l) j k =
      (ff_gridInputCount T A K l j k : Real) / (K : Nat) := by
  rw [ff_gridTime_eq_gridPoint T K l hl]
  exact fi_polygonalInterpolate_grid K _ T hT l hl

private theorem fi_hatWeight_ne_zero_distance
    (K : PNat) {T t : Real} (hT : 0 < T)
    {l : Nat} (hl : l < (K : Nat) + 1)
    (hw : fi_hatWeight (((K : Nat) : Real) * t / T) l ≠ 0) :
    abs (ff_gridTime T K l - t) <= T / (K : Nat) := by
  have hlK : l <= (K : Nat) := by omega
  rw [ff_gridTime_eq_gridPoint T K l hlK]
  have habs :
      abs (((K : Nat) : Real) * t / T - l) < 1 := by
    by_contra h
    have hone : 1 <= abs (((K : Nat) : Real) * t / T - l) :=
      le_of_not_gt h
    exact hw (fi_hatWeight_eq_zero_of_one_le_abs hone)
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [show T * (l : Real) / (K : Nat) - t =
      (T * (l : Real) - t * (K : Nat)) / (K : Nat) by
        field_simp
        <;> ring]
  rw [abs_div, abs_of_pos hK]
  apply (div_le_iff₀ hK).2
  rw [div_mul_cancel₀ T (ne_of_gt hK)]
  rw [abs_le]
  rw [abs_lt] at habs
  have hu :
      ((K : Nat) : Real) * t / T < (l : Real) + 1 := by linarith
  have hlo :
      (l : Real) - 1 < ((K : Nat) : Real) * t / T := by linarith
  have hupper := (div_lt_iff₀ hT).1 hu
  have hlower := (lt_div_iff₀ hT).1 hlo
  constructor <;> push_cast at * <;> nlinarith

private theorem fi_polygonalInputPath_uniform_error
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat)
    (j : Server) (k : Buffer) (eta : Real)
    (hosc : forall s, s ∈ Icc (0 : Real) T ->
      forall t, t ∈ Icc (0 : Real) T ->
        abs (s - t) <= T / (K : Nat) ->
        abs (A s j k - A t j k) <= eta)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    abs (fi_polygonalInputPath T A K t j k - A t j k) <=
      eta + 1 / (K : Nat) := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) ht.1)
      (le_of_lt hT)
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hsum :
      Finset.sum (Finset.range ((K : Nat) + 1)) (fi_hatWeight r) = 1 :=
    fi_sum_hatWeight_eq_one K hr0 hrK
  have hterm (l : Nat) (hl : l ∈ Finset.range ((K : Nat) + 1)) :
      abs (fi_hatWeight r l *
        ((ff_gridInputCount T A K l j k : Real) / (K : Nat) -
          A t j k)) <=
        fi_hatWeight r l * (eta + 1 / (K : Nat)) := by
    by_cases hw : fi_hatWeight r l = 0
    · simp [hw]
    · rw [abs_mul, abs_of_nonneg (fi_hatWeight_nonnegative r l)]
      apply mul_le_mul_of_nonneg_left _ (fi_hatWeight_nonnegative r l)
      have hdist := fi_hatWeight_ne_zero_distance K hT
          (Finset.mem_range.mp hl) hw
      have hosc' := hosc (ff_gridTime T K l)
        (ff_gridTime_mem_Icc T hT K l) t ht hdist
      have happ := ff_gridInputCount_approx T hT A hA K l j k
      calc
        abs ((ff_gridInputCount T A K l j k : Real) / (K : Nat) -
            A t j k) <=
            abs ((ff_gridInputCount T A K l j k : Real) / (K : Nat) -
              A (ff_gridTime T K l) j k) +
            abs (A (ff_gridTime T K l) j k - A t j k) := by
              simpa only [sub_add_sub_cancel] using
                abs_add_le
                  ((ff_gridInputCount T A K l j k : Real) / (K : Nat) -
                    A (ff_gridTime T K l) j k)
                  (A (ff_gridTime T K l) j k - A t j k)
        _ <= 1 / (K : Nat) + eta := add_le_add (le_of_lt happ) hosc'
        _ = eta + 1 / (K : Nat) := add_comm _ _
  rw [show fi_polygonalInputPath T A K t j k - A t j k =
      Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
        fi_hatWeight r l *
          ((ff_gridInputCount T A K l j k : Real) / (K : Nat) -
            A t j k)) by
      unfold fi_polygonalInputPath fi_polygonalInterpolate
      dsimp [r]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, <- Finset.sum_mul, hsum, one_mul]]
  calc
    abs (Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
        fi_hatWeight r l *
          ((ff_gridInputCount T A K l j k : Real) / (K : Nat) -
            A t j k))) <=
        Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
          abs (fi_hatWeight r l *
            ((ff_gridInputCount T A K l j k : Real) / (K : Nat) -
              A t j k))) := Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
          fi_hatWeight r l * (eta + 1 / (K : Nat))) :=
      Finset.sum_le_sum hterm
    _ = eta + 1 / (K : Nat) := by
      rw [<- Finset.sum_mul, hsum, one_mul]

private theorem fi_polygonalInputPath_uniform_convergence
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) :
    forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall j k t, t ∈ Icc (0 : Real) T ->
          abs (fi_polygonalInputPath T A
            ⟨n + 1, by omega⟩ t j k - A t j k) < epsilon := by
  let Avec : Real -> Server -> Buffer -> Real := fun t j k => A t j k
  have hcont : ContinuousOn Avec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro j
    rw [continuousOn_pi]
    intro k
    simpa [uIcc_of_le (le_of_lt hT)] using (hA.1 j k).continuousOn
  have huc : UniformContinuousOn Avec (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  have hrecip :
      Tendsto (fun n : Nat => (1 : Real) / ((n : Real) + 1))
        atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmesh :
      Tendsto (fun n : Nat => T / ((n : Real) + 1))
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hrecip
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp huc (epsilon / 2) (by positivity)
  obtain ⟨nRecip, hnRecip⟩ :=
    Metric.tendsto_atTop.mp hrecip (epsilon / 2) (by positivity)
  obtain ⟨nMesh, hnMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh delta hdelta
  refine ⟨max nRecip nMesh, fun n hn j k t ht => ?_⟩
  have hnR : nRecip <= n := (le_max_left _ _).trans hn
  have hnM : nMesh <= n := (le_max_right _ _).trans hn
  have hrecipSmall :
      (1 : Real) / ((n : Real) + 1) < epsilon / 2 := by
    have h := hnRecip n hnR
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (by positivity : 0 <= (1 : Real) / ((n : Real) + 1))] at h
    exact h
  have hmeshSmall :
      T / ((n : Real) + 1) < delta := by
    have h := hnMesh n hnM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg (le_of_lt hT) (by positivity))] at h
    exact h
  let K : PNat := ⟨n + 1, by omega⟩
  have hosc :
      forall s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T ->
          abs (s - t) <= T / (K : Nat) ->
          abs (A s j k - A t j k) <= epsilon / 2 := by
    intro s hs t ht' hst
    have hdistTime : dist s t < delta := by
      rw [Real.dist_eq]
      exact hst.trans_lt (by simpa [K, Nat.cast_add, Nat.cast_one] using hmeshSmall)
    have hvec := hdeltaWorks s hs t ht' hdistTime
    have hj :
        dist (Avec s j) (Avec t j) <= dist (Avec s) (Avec t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s) (Avec t) <= dist (Avec s) (Avec t)) j
    have hk :
        dist (Avec s j k) (Avec t j k) <=
          dist (Avec s j) (Avec t j) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s j) (Avec t j) <=
          dist (Avec s j) (Avec t j)) k
    have hcoord := (hk.trans hj).trans (le_of_lt hvec)
    simpa [Avec, Real.dist_eq] using hcoord
  have herr :=
    fi_polygonalInputPath_uniform_error T hT A hA K j k
      (epsilon / 2) hosc t ht
  have hrecipK :
      (1 : Real) / (K : Nat) < epsilon / 2 := by
    simpa [K, Nat.cast_add, Nat.cast_one] using hrecipSmall
  change abs (fi_polygonalInputPath T A K t j k - A t j k) < epsilon
  exact herr.trans_lt (by linarith)

private noncomputable def fi_gridQueueState
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat)) (A : MatrixPath Server Buffer)
    (l : Nat) : JobState Buffer (K : Nat) :=
  N.runTokens U x (ff_gridTokenPrefix T A K l)

private noncomputable def fi_gridAllocationCount
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat)) (A : MatrixPath Server Buffer)
    (l : Nat) (i : Buffer) (j : Server) (k : Buffer) : Nat :=
  N.runAllocationCount U x (ff_gridTokenPrefix T A K l) i j k

private theorem fi_gridTokenBatch_length
    (T : Real) (A : MatrixPath Server Buffer) (K : PNat) (l : Nat) :
    (ff_gridTokenBatch T A K l).length =
      Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (ff_gridInputCount T A K (l + 1) j k -
            ff_gridInputCount T A K l j k) := by
  classical
  let d : Server × Buffer -> Nat := fun jk =>
    ff_gridInputCount T A K (l + 1) jk.1 jk.2 -
      ff_gridInputCount T A K l jk.1 jk.2
  calc
    (ff_gridTokenBatch T A K l).length =
        Finset.univ.sum d := by
      simp [ff_gridTokenBatch, d]
    _ = Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (ff_gridInputCount T A K (l + 1) j k -
            ff_gridInputCount T A K l j k) := by
      have hprod :
          (Finset.univ : Finset (Server × Buffer)) =
            (Finset.univ : Finset Server).product
              (Finset.univ : Finset Buffer) := by
        ext jk
        simp
      rw [hprod]
      simpa [d] using
        Finset.sum_product
          (Finset.univ : Finset Server)
          (Finset.univ : Finset Buffer) d

private theorem fi_gridTokenBatch_scaled_length
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat) (l : Nat) :
    ((ff_gridTokenBatch T A K l).length : Real) / (K : Nat) =
      Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          ((ff_gridInputCount T A K (l + 1) j k : Real) / (K : Nat) -
            (ff_gridInputCount T A K l j k : Real) / (K : Nat)) := by
  classical
  rw [fi_gridTokenBatch_length]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.cast_sub
    (ff_gridInputCount_mono T hT A hA K j k (Nat.le_succ l))]
  ring

private theorem fi_gridAllocationCount_step_le_input_sum
    (N : Network Buffer Server) (T : Real) (hT : 0 < T) (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat)) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    abs ((fi_gridAllocationCount N T K U x A (l + 1) i j k : Real) /
          (K : Nat) -
        (fi_gridAllocationCount N T K U x A l i j k : Real) /
          (K : Nat)) <=
      Finset.univ.sum fun j' : Server =>
        Finset.univ.sum fun k' : Buffer =>
          ((ff_gridInputCount T A K (l + 1) j' k' : Real) / (K : Nat) -
            (ff_gridInputCount T A K l j' k' : Real) / (K : Nat)) := by
  have happ :=
    ff_runAllocationCount_append N U x
      (ff_gridTokenPrefix T A K l) (ff_gridTokenBatch T A K l) i j k
  have hmono :
      fi_gridAllocationCount N T K U x A l i j k <=
        fi_gridAllocationCount N T K U x A (l + 1) i j k := by
    unfold fi_gridAllocationCount
    rw [show ff_gridTokenPrefix T A K (l + 1) =
      ff_gridTokenPrefix T A K l ++ ff_gridTokenBatch T A K l by rfl]
    omega
  have hnat :=
    ff_runAllocationCount_batch_increment_le_length N U x
      (ff_gridTokenPrefix T A K l) (ff_gridTokenBatch T A K l) i j k
  have hreal :
      (fi_gridAllocationCount N T K U x A (l + 1) i j k : Real) -
          (fi_gridAllocationCount N T K U x A l i j k : Real) <=
        (ff_gridTokenBatch T A K l).length := by
    rw [<- Nat.cast_sub hmono]
    exact_mod_cast hnat
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [<- fi_gridTokenBatch_scaled_length T hT A hA K l]
  rw [<- sub_div, abs_div, abs_of_pos hK,
    abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmono))]
  exact (div_le_div_iff_of_pos_right hK).2 hreal

private theorem fi_gridQueueState_step_le_two_input_sum
    (N : Network Buffer Server) (T : Real) (hT : 0 < T) (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat)) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (l : Nat) (i : Buffer) :
    abs ((fi_gridQueueState N T K U x A (l + 1) i : Real) / (K : Nat) -
        (fi_gridQueueState N T K U x A l i : Real) / (K : Nat)) <=
      2 * (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          ((ff_gridInputCount T A K (l + 1) j k : Real) / (K : Nat) -
            (ff_gridInputCount T A K l j k : Real) / (K : Nat))) := by
  have htotal :=
    ff_runTokens_batch_l1_le_two_mul_length N U x
      (ff_gridTokenPrefix T A K l) (ff_gridTokenBatch T A K l)
  have hcoord :
      abs (((fi_gridQueueState N T K U x A (l + 1) i : Nat) : Real) -
        ((fi_gridQueueState N T K U x A l i : Nat) : Real)) <=
          2 * (ff_gridTokenBatch T A K l).length := by
    unfold fi_gridQueueState
    rw [show ff_gridTokenPrefix T A K (l + 1) =
      ff_gridTokenPrefix T A K l ++ ff_gridTokenBatch T A K l by rfl]
    exact (Finset.single_le_sum
      (fun q _ => abs_nonneg
        (((N.runTokens U x
          (ff_gridTokenPrefix T A K l ++ ff_gridTokenBatch T A K l) q :
            Nat) : Real) -
          (N.runTokens U x (ff_gridTokenPrefix T A K l) q : Real)))
      (Finset.mem_univ i)).trans htotal
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [<- fi_gridTokenBatch_scaled_length T hT A hA K l]
  rw [<- sub_div, abs_div, abs_of_pos hK]
  calc
    abs ((fi_gridQueueState N T K U x A (l + 1) i : Real) -
        (fi_gridQueueState N T K U x A l i : Real)) / (K : Nat) <=
        (2 * (ff_gridTokenBatch T A K l).length : Real) / (K : Nat) :=
      (div_le_div_iff_of_pos_right hK).2 hcoord
    _ = 2 * ((ff_gridTokenBatch T A K l).length : Real) / (K : Nat) := by
      norm_num
    _ = 2 * (((ff_gridTokenBatch T A K l).length : Real) /
        (K : Nat)) := by ring

private noncomputable def fi_polygonalStatePath
    (K : PNat) (x : Nat -> Buffer -> Real) (T : Real) :
    FluidStatePath Buffer :=
  fun t i => fi_polygonalInterpolate K (fun l => x l i) t T

private noncomputable def fi_polygonalAllocationPath
    (K : PNat) (e : Nat -> Buffer -> Server -> Buffer -> Real) (T : Real) :
    FluidAllocationPath Buffer Server :=
  fun t i j k => fi_polygonalInterpolate K (fun l => e l i j k) t T

private theorem fi_polygonalStatePath_in_simplex
    (K : PNat) (x : Nat -> Buffer -> Real) {t T : Real}
    (hT : 0 < T) (ht : t ∈ Icc (0 : Real) T)
    (hx : forall l, l < (K : Nat) + 1 -> IsFluidState (x l)) :
    IsFluidState (fi_polygonalStatePath K x T t) :=
  fi_polygonal_state_simplex K x hT ht hx

private theorem fi_polygonalStatePath_initial
    (K : PNat) (x : Nat -> Buffer -> Real) (T : Real) (hT : 0 < T)
    (i : Buffer) :
    fi_polygonalStatePath K x T 0 i = x 0 i :=
  fi_polygonal_initial K _ T hT

private theorem fi_polygonalAllocationPath_initial
    (K : PNat) (e : Nat -> Buffer -> Server -> Buffer -> Real)
    (T : Real) (hT : 0 < T)
    (he0 : forall i j k, e 0 i j k = 0) (i : Buffer) (j : Server)
    (k : Buffer) :
    fi_polygonalAllocationPath K e T 0 i j k = 0 := by
  rw [fi_polygonalAllocationPath, fi_polygonal_initial K _ T hT, he0]

private theorem fi_polygonalAllocationPath_incompatible
    (N : Network Buffer Server) (K : PNat)
    (e : Nat -> Buffer -> Server -> Buffer -> Real)
    (T t : Real)
    (he : forall l, l < (K : Nat) + 1 ->
      forall i j k, Not (N.compatible i j) -> e l i j k = 0)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    fi_polygonalAllocationPath K e T t i j k = 0 :=
  fi_polygonal_allocation_incompatible K e t T i j k
    (fun l hl => he l hl i j k hij)

private theorem fi_polygonal_paths_balance
    (K : PNat) (x : Nat -> Buffer -> Real)
    (e : Nat -> Buffer -> Server -> Buffer -> Real)
    (x0 : Buffer -> Real) {t T : Real} (hT : 0 < T)
    (ht : t ∈ Icc (0 : Real) T)
    (hbalance : forall l, l < (K : Nat) + 1 -> forall i,
      x l i = x0 i +
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun q : Buffer => e l q j i) -
        (Finset.univ.sum fun j : Server =>
          Finset.univ.sum fun k : Buffer => e l i j k))
    (i : Buffer) :
    fi_polygonalStatePath K x T t i = x0 i +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          fi_polygonalAllocationPath K e T t q j i) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          fi_polygonalAllocationPath K e T t i j k) := by
  unfold fi_polygonalStatePath fi_polygonalAllocationPath
  have h := fi_polygonal_balance
    (J := Server) (Q := Server) (R := Unit)
    K (fun l => x l i) (x0 i)
    (fun l j => Finset.univ.sum fun q : Buffer => e l q j i)
    (fun l j => Finset.univ.sum fun k : Buffer => e l i j k)
    hT ht (fun l hl => hbalance l hl i)
  simpa only [fi_polygonalInterpolate_sum] using h

private theorem fi_sum_range_sub
    (values : Nat -> Real) (l : Nat) :
    values 0 +
      Finset.sum (Finset.range l) (fun q => values (q + 1) - values q) =
      values l := by
  induction l with
  | zero => simp
  | succ l ih =>
      simp only [Finset.sum_range_succ]
      linarith

private theorem fi_polygonalInterpolate_eq_ramp
    (K : PNat) (values : Nat -> Real) {t T : Real}
    (hT : 0 < T) (ht : t ∈ Icc (0 : Real) T) :
    fi_polygonalInterpolate K values t T =
      ff_rampInterpolate K values t T := by
  classical
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) ht.1) (le_of_lt hT)
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  by_cases heq : r = (K : Nat)
  · have htT : t = T := by
      dsimp [r] at heq
      have hdiv := (div_eq_iff (ne_of_gt hT)).1 heq
      have hK : (0 : Real) < (K : Nat) := by positivity
      nlinarith
    subst t
    simpa using
      (fi_polygonalInterpolate_grid K values T hT (K : Nat) le_rfl).trans
        (ff_rampInterpolate_grid K values T hT (K : Nat) le_rfl).symm
  · let n : Nat := Nat.floor r
    let theta : Real := r - n
    have hrKlt : r < (K : Nat) := lt_of_le_of_ne hrK heq
    have hnK : n < (K : Nat) := (Nat.floor_lt hr0).2 hrKlt
    have hn_le : (n : Real) <= r := Nat.floor_le hr0
    have hr_lt : r < (n : Real) + 1 := Nat.lt_floor_add_one r
    have htheta0 : 0 <= theta := by dsimp [theta]; linarith
    have htheta1 : theta <= 1 := by dsimp [theta]; linarith
    have hpair :
        ({n, n + 1} : Finset Nat) <=
          Finset.range ((K : Nat) + 1) := by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact Finset.mem_range.mpr (by omega)
      · exact Finset.mem_range.mpr (by omega)
    have hhatZero :
        forall l, l ∈ Finset.range ((K : Nat) + 1) ->
          l ∉ ({n, n + 1} : Finset Nat) -> fi_hatWeight r l = 0 := by
      intro l hl hlpair
      apply fi_hatWeight_eq_zero_of_one_le_abs
      by_cases hlt : l < n
      · rw [abs_of_nonneg]
        · have hcast : (l : Real) + 1 <= n := by
            exact_mod_cast (show l + 1 <= n by omega)
          linarith
        · have hcast : (l : Real) <= n := by
            exact_mod_cast (show l <= n by omega)
          linarith
      · have hnlt : n + 1 < l := by
          have hneN : l ≠ n := by
            intro h
            exact hlpair (by simp [h])
          have hneN1 : l ≠ n + 1 := by
            intro h
            exact hlpair (by simp [h])
          omega
        rw [abs_of_nonpos]
        · have hcast : (n : Real) + 2 <= l := by
            exact_mod_cast (show n + 2 <= l by omega)
          linarith
        · have hcast : (n : Real) + 1 <= l := by
            exact_mod_cast (show n + 1 <= l by omega)
          linarith
    have hhat :
        fi_polygonalInterpolate K values t T =
          (1 - theta) * values n + theta * values (n + 1) := by
      unfold fi_polygonalInterpolate
      change
        Finset.sum (Finset.range ((K : Nat) + 1))
          (fun l => fi_hatWeight r l * values l) = _
      rw [<- Finset.sum_subset hpair]
      · rw [Finset.sum_pair (by omega : n ≠ n + 1)]
        have hnabs : abs (r - (n : Real)) = theta := by
          rw [abs_of_nonneg (sub_nonneg.mpr hn_le)]
        have hn1abs :
            abs (r - ((n + 1 : Nat) : Real)) = 1 - theta := by
          rw [abs_of_nonpos]
          · dsimp [theta]
            push_cast
            ring
          · push_cast
            linarith
        rw [show fi_hatWeight r n = 1 - theta by
          simp [fi_hatWeight, hnabs, max_eq_right (by linarith : 0 <= 1 - theta)]]
        rw [show fi_hatWeight r (n + 1) = theta by
          unfold fi_hatWeight
          rw [hn1abs]
          have hsimp : 1 - (1 - theta) = theta := by ring
          rw [hsimp, max_eq_right htheta0]]
      · intro l hl hlpair
        rw [hhatZero l hl hlpair, zero_mul]
    have hrange :
        Finset.range (n + 1) <= Finset.range (K : Nat) :=
      Finset.range_mono (by omega)
    have hrampZero :
        forall l, l ∈ Finset.range (K : Nat) ->
          l ∉ Finset.range (n + 1) ->
          (values (l + 1) - values l) *
            ff_clamp01 (r - l) = 0 := by
      intro l hlK hln
      have hnl : n + 1 <= l := by
        simpa only [Finset.mem_range, not_lt] using hln
      have hcast : (n : Real) + 1 <= l := by exact_mod_cast hnl
      have hnonpos : r - (l : Real) <= 0 := by linarith
      rw [ff_clamp01_of_nonpos hnonpos, mul_zero]
    have hbefore :
        Finset.sum (Finset.range n) (fun l =>
          (values (l + 1) - values l) * ff_clamp01 (r - l)) =
        Finset.sum (Finset.range n) (fun l =>
          values (l + 1) - values l) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hln : l < n := Finset.mem_range.mp hl
      have hcast : (l : Real) + 1 <= n := by
        exact_mod_cast (show l + 1 <= n by omega)
      have hone : (1 : Real) <= r - l := by linarith
      rw [ff_clamp01_of_one_le hone, mul_one]
    have hthetaClamp : ff_clamp01 (r - n) = theta := by
      dsimp [ff_clamp01]
      rw [min_eq_right htheta1, max_eq_right htheta0]
    have hramp :
        ff_rampInterpolate K values t T =
          (1 - theta) * values n + theta * values (n + 1) := by
      unfold ff_rampInterpolate
      change values 0 +
        Finset.sum (Finset.range (K : Nat)) (fun l =>
          (values (l + 1) - values l) * ff_clamp01 (r - l)) = _
      rw [<- Finset.sum_subset hrange hrampZero]
      rw [Finset.sum_range_succ, hbefore, hthetaClamp]
      rw [<- add_assoc, fi_sum_range_sub]
      ring
    rw [hhat, hramp]

private theorem fi_ramp_increment_domination
    {J : Type w} [Fintype J]
    (K : PNat) (values : Nat -> Real) (control : J -> Nat -> Real)
    {s t T : Real} (hT : 0 < T) (hst : s <= t)
    (hcontrol : forall j l, l < (K : Nat) ->
      control j l <= control j (l + 1))
    (hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun j => control j (l + 1) - control j l)) :
    abs (ff_rampInterpolate K values t T -
      ff_rampInterpolate K values s T) <=
      Finset.univ.sum (fun j =>
        abs (ff_rampInterpolate K (control j) t T -
          ff_rampInterpolate K (control j) s T)) := by
  classical
  let d : Nat -> Real := fun l =>
    ff_clamp01 (((K : Nat) : Real) * t / T - l) -
      ff_clamp01 (((K : Nat) : Real) * s / T - l)
  have hd (l : Nat) : 0 <= d l := by
    dsimp [d]
    apply sub_nonneg.mpr
    apply ff_clamp01_monotone
    apply sub_le_sub_right
    apply div_le_div_of_nonneg_right _ (le_of_lt hT)
    exact mul_le_mul_of_nonneg_left hst (by positivity)
  have hvalue :
      ff_rampInterpolate K values t T -
          ff_rampInterpolate K values s T =
        Finset.sum (Finset.range (K : Nat)) (fun l =>
          (values (l + 1) - values l) * d l) := by
    unfold ff_rampInterpolate
    dsimp [d]
    rw [add_sub_add_left_eq_sub, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hcontrolDiff (j : J) :
      ff_rampInterpolate K (control j) t T -
          ff_rampInterpolate K (control j) s T =
        Finset.sum (Finset.range (K : Nat)) (fun l =>
          (control j (l + 1) - control j l) * d l) := by
    unfold ff_rampInterpolate
    dsimp [d]
    rw [add_sub_add_left_eq_sub, <- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hvalue]
  calc
    abs (Finset.sum (Finset.range (K : Nat)) (fun l =>
        (values (l + 1) - values l) * d l)) <=
        Finset.sum (Finset.range (K : Nat)) (fun l =>
          abs ((values (l + 1) - values l) * d l)) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (Finset.range (K : Nat)) (fun l =>
          (Finset.univ.sum (fun j =>
            control j (l + 1) - control j l)) * d l) := by
      apply Finset.sum_le_sum
      intro l hl
      rw [abs_mul, abs_of_nonneg (hd l)]
      exact mul_le_mul_of_nonneg_right
        (hstep l (Finset.mem_range.mp hl)) (hd l)
    _ = Finset.univ.sum (fun j =>
          Finset.sum (Finset.range (K : Nat)) (fun l =>
            (control j (l + 1) - control j l) * d l)) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = Finset.univ.sum (fun j =>
          abs (ff_rampInterpolate K (control j) t T -
            ff_rampInterpolate K (control j) s T)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hcontrolDiff]
      rw [abs_of_nonneg]
      apply Finset.sum_nonneg
      intro l hl
      exact mul_nonneg
        (sub_nonneg.mpr (hcontrol j l (Finset.mem_range.mp hl))) (hd l)

private theorem fi_ramp_increment_domination_symmetric
    {J : Type w} [Fintype J]
    (K : PNat) (values : Nat -> Real) (control : J -> Nat -> Real)
    {s t T : Real} (hT : 0 < T)
    (hcontrol : forall j l, l < (K : Nat) ->
      control j l <= control j (l + 1))
    (hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun j => control j (l + 1) - control j l)) :
    dist (ff_rampInterpolate K values s T)
        (ff_rampInterpolate K values t T) <=
      Finset.univ.sum (fun j =>
        dist (ff_rampInterpolate K (control j) s T)
          (ff_rampInterpolate K (control j) t T)) := by
  rcases le_total s t with hst | hts
  · simpa [Real.dist_eq, abs_sub_comm] using
      fi_ramp_increment_domination K values control hT hst hcontrol hstep
  · simpa [Real.dist_eq, abs_sub_comm] using
      fi_ramp_increment_domination K values control hT hts hcontrol hstep

private theorem fi_polygonal_increment_domination
    {J : Type w} [Fintype J]
    (K : PNat) (values : Nat -> Real) (control : J -> Nat -> Real)
    {s t T : Real} (hT : 0 < T)
    (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T)
    (hcontrol : forall j l, l < (K : Nat) ->
      control j l <= control j (l + 1))
    (hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun j => control j (l + 1) - control j l)) :
    dist (fi_polygonalInterpolate K values s T)
        (fi_polygonalInterpolate K values t T) <=
      Finset.univ.sum (fun j =>
        dist (fi_polygonalInterpolate K (control j) s T)
          (fi_polygonalInterpolate K (control j) t T)) := by
  rw [fi_polygonalInterpolate_eq_ramp K values hT hs,
    fi_polygonalInterpolate_eq_ramp K values hT ht]
  simp_rw [fi_polygonalInterpolate_eq_ramp K _ hT hs,
    fi_polygonalInterpolate_eq_ramp K _ hT ht]
  exact fi_ramp_increment_domination_symmetric
    K values control hT hcontrol hstep

private theorem fi_polygonalAllocationPath_increment_domination
    (N : Network Buffer Server) (T : Real) (hT : 0 < T) (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat)) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (i : Buffer) (j : Server) (k : Buffer)
    {s t : Real} (hs : s ∈ Icc (0 : Real) T)
    (ht : t ∈ Icc (0 : Real) T) :
    dist
        (fi_polygonalInterpolate K (fun l =>
          (fi_gridAllocationCount N T K U x A l i j k : Real) /
            (K : Nat)) s T)
        (fi_polygonalInterpolate K (fun l =>
          (fi_gridAllocationCount N T K U x A l i j k : Real) /
            (K : Nat)) t T) <=
      Finset.univ.sum (fun jk : Server × Buffer =>
        dist
          (fi_polygonalInterpolate K (fun l =>
            (ff_gridInputCount T A K l jk.1 jk.2 : Real) / (K : Nat)) s T)
          (fi_polygonalInterpolate K (fun l =>
            (ff_gridInputCount T A K l jk.1 jk.2 : Real) / (K : Nat)) t T)) := by
  let values : Nat -> Real := fun l =>
    (fi_gridAllocationCount N T K U x A l i j k : Real) / (K : Nat)
  let control : Server × Buffer -> Nat -> Real := fun jk l =>
    (ff_gridInputCount T A K l jk.1 jk.2 : Real) / (K : Nat)
  have hcontrol : forall jk l, l < (K : Nat) ->
      control jk l <= control jk (l + 1) := by
    intro jk l hl
    dsimp [control]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast
      (ff_gridInputCount_mono T hT A hA K jk.1 jk.2 (Nat.le_succ l))
  have hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun jk =>
          control jk (l + 1) - control jk l) := by
    intro l hl
    have h :=
      fi_gridAllocationCount_step_le_input_sum
        N T hT K U x A hA l i j k
    let d : Server × Buffer -> Real := fun jk =>
      control jk (l + 1) - control jk l
    have hprod :
        (Finset.univ : Finset (Server × Buffer)) =
          (Finset.univ : Finset Server).product
            (Finset.univ : Finset Buffer) := by
      ext jk
      simp
    have hsum :
        Finset.univ.sum d =
          Finset.univ.sum (fun j' : Server =>
            Finset.univ.sum fun k' : Buffer =>
              (ff_gridInputCount T A K (l + 1) j' k' : Real) / (K : Nat) -
                (ff_gridInputCount T A K l j' k' : Real) / (K : Nat)) := by
      rw [hprod]
      simpa [d, control] using
        (Finset.sum_product
          (Finset.univ : Finset Server)
          (Finset.univ : Finset Buffer) d)
    dsimp [values]
    change _ <= Finset.univ.sum d
    rw [hsum]
    exact h
  exact fi_polygonal_increment_domination K values control hT hs ht
    hcontrol hstep


private def existenceClamp01 (r : Real) : Real :=
  min 1 (max 0 r)

private theorem existenceClamp01_monotone : Monotone existenceClamp01 := by
  intro a b hab
  simp only [existenceClamp01]
  exact min_le_min le_rfl (max_le_max le_rfl hab)

private theorem existenceClamp01_of_nonpos {r : Real} (hr : r <= 0) :
    existenceClamp01 r = 0 := by
  simp [existenceClamp01, max_eq_left hr]

private theorem existenceClamp01_of_one_le {r : Real} (hr : 1 <= r) :
    existenceClamp01 r = 1 := by
  rw [existenceClamp01, max_eq_right (le_trans zero_le_one hr),
    min_eq_left hr]

private noncomputable def existenceRampInterpolate
    (K : PNat) (values : Nat -> Real) (t T : Real) : Real :=
  values 0 +
    Finset.sum (Finset.range (K : Nat)) fun l =>
      (values (l + 1) - values l) *
        existenceClamp01 (((K : Nat) : Real) * t / T - l)

private theorem existenceRampInterpolate_grid
    (K : PNat) (values : Nat -> Real) (T : Real) (hT : 0 < T)
    (l : Nat) (hl : l <= (K : Nat)) :
    existenceRampInterpolate K values
      (T * (l : Real) / (K : Nat)) T = values l := by
  have hscale :
      ((K : Nat) : Real) * (T * (l : Real) / (K : Nat)) / T =
        (l : Real) := by
    have hK : ((K : Nat) : Real) ≠ 0 := by positivity
    field_simp
  unfold existenceRampInterpolate
  rw [hscale]
  have hbefore :
      Finset.sum (Finset.range l) (fun q =>
        (values (q + 1) - values q) *
          existenceClamp01 ((l : Real) - q)) =
        Finset.sum (Finset.range l) (fun q =>
          values (q + 1) - values q) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hq : q < l := Finset.mem_range.mp hq
    have hone : (1 : Real) <= (l : Real) - q := by
      have hcast : (q : Real) + 1 <= l := by
        exact_mod_cast (show q + 1 <= l by omega)
      linarith
    rw [existenceClamp01_of_one_le hone, mul_one]
  have hafter :
      forall q, q ∈ Finset.range (K : Nat) ->
        q ∉ Finset.range l ->
        (values (q + 1) - values q) *
          existenceClamp01 ((l : Real) - q) = 0 := by
    intro q hq hnot
    have hlq : l <= q := by
      simpa only [Finset.mem_range, not_lt] using hnot
    have hcast : (l : Real) <= q := by exact_mod_cast hlq
    have hnonpos : (l : Real) - q <= 0 := sub_nonpos.mpr hcast
    rw [existenceClamp01_of_nonpos hnonpos, mul_zero]
  rw [<- Finset.sum_subset (Finset.range_mono hl) hafter, hbefore]
  rw [Finset.sum_range_sub]
  ring

private theorem ff_clamp01_eq_existenceClamp01 (r : Real) :
    ff_clamp01 r = existenceClamp01 r := by
  unfold ff_clamp01 existenceClamp01
  rcases le_total r 0 with h | h
  · simp [max_eq_left h, min_eq_right (h.trans zero_le_one)]
  · by_cases h1 : r <= 1
    · simp [max_eq_right h, min_eq_right h1]
    · have h1' : 1 <= r := le_of_not_ge h1
      simp [max_eq_right h, min_eq_left h1']

private theorem ff_rampInterpolate_eq_existenceRampInterpolate
    (K : PNat) (values : Nat -> Real) (t T : Real) :
    ff_rampInterpolate K values t T =
      existenceRampInterpolate K values t T := by
  unfold ff_rampInterpolate existenceRampInterpolate
  apply congrArg (fun z => values 0 + z)
  apply Finset.sum_congr rfl
  intro l hl
  rw [ff_clamp01_eq_existenceClamp01]

private theorem fi_polygonalQueuePath_increment_domination
    (N : Network Buffer Server) (T : Real) (hT : 0 < T) (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat)) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (i : Buffer)
    {s t : Real} (hs : s ∈ Icc (0 : Real) T)
    (ht : t ∈ Icc (0 : Real) T) :
    dist
        (fi_polygonalInterpolate K (fun l =>
          (fi_gridQueueState N T K U x A l i : Real) / (K : Nat)) s T)
        (fi_polygonalInterpolate K (fun l =>
          (fi_gridQueueState N T K U x A l i : Real) / (K : Nat)) t T) <=
      Finset.univ.sum (fun jk : (Server × Buffer) × Fin 2 =>
        dist
          (fi_polygonalInterpolate K (fun l =>
            (ff_gridInputCount T A K l jk.1.1 jk.1.2 : Real) /
              (K : Nat)) s T)
          (fi_polygonalInterpolate K (fun l =>
            (ff_gridInputCount T A K l jk.1.1 jk.1.2 : Real) /
              (K : Nat)) t T)) := by
  let values : Nat -> Real := fun l =>
    (fi_gridQueueState N T K U x A l i : Real) / (K : Nat)
  let control : (Server × Buffer) × Fin 2 -> Nat -> Real := fun jk l =>
    (ff_gridInputCount T A K l jk.1.1 jk.1.2 : Real) / (K : Nat)
  have hcontrol : forall jk l, l < (K : Nat) ->
      control jk l <= control jk (l + 1) := by
    intro jk l hl
    dsimp [control]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast
      (ff_gridInputCount_mono T hT A hA K jk.1.1 jk.1.2
        (Nat.le_succ l))
  have hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun jk =>
          control jk (l + 1) - control jk l) := by
    intro l hl
    have h :=
      fi_gridQueueState_step_le_two_input_sum N T hT K U x A hA l i
    let d : Server × Buffer -> Real := fun jk =>
      (ff_gridInputCount T A K (l + 1) jk.1 jk.2 : Real) / (K : Nat) -
        (ff_gridInputCount T A K l jk.1 jk.2 : Real) / (K : Nat)
    have hprod :
        (Finset.univ : Finset (Server × Buffer)) =
          (Finset.univ : Finset Server).product
            (Finset.univ : Finset Buffer) := by
      ext jk
      simp
    have hsum :
        Finset.univ.sum d =
          Finset.univ.sum (fun j : Server =>
            Finset.univ.sum fun k : Buffer =>
              (ff_gridInputCount T A K (l + 1) j k : Real) / (K : Nat) -
                (ff_gridInputCount T A K l j k : Real) / (K : Nat)) := by
      rw [hprod]
      simpa [d] using
        (Finset.sum_product
          (Finset.univ : Finset Server)
          (Finset.univ : Finset Buffer) d)
    dsimp [values]
    have hdup :
      Finset.univ.sum (fun jk : (Server × Buffer) × Fin 2 =>
        control jk (l + 1) - control jk l) =
          2 * Finset.univ.sum d := by
      have hprod2 :
          (Finset.univ : Finset ((Server × Buffer) × Fin 2)) =
            (Finset.univ : Finset (Server × Buffer)).product
              (Finset.univ : Finset (Fin 2)) := by
        ext jk
        simp
      rw [hprod2]
      rw [show
        Finset.sum
            ((Finset.univ : Finset (Server × Buffer)).product
              (Finset.univ : Finset (Fin 2)))
            (fun jk => control jk (l + 1) - control jk l) =
          Finset.univ.sum (fun ab : Server × Buffer =>
            Finset.univ.sum (fun z : Fin 2 =>
              control (ab, z) (l + 1) - control (ab, z) l)) by
        exact Finset.sum_product _ _ _]
      simp [control, d, <- Finset.mul_sum]
      ring
    rw [hdup, hsum]
    exact h
  exact fi_polygonal_increment_domination K values control hT hs ht
    hcontrol hstep

private noncomputable def tri_floorJobs
    (x : Simplex Buffer) (K : Nat) (i : Buffer) : Nat :=
  Nat.floor ((K : Real) * x i)

private theorem tri_sum_tri_floorJobs_le (x : Simplex Buffer) (K : Nat) :
    (Finset.univ.sum fun i => tri_floorJobs x K i) <= K := by
  have hterm (i : Buffer) :
      ((tri_floorJobs x K i : Nat) : Real) <= (K : Real) * x i := by
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) (x.nonneg i))
  have hreal :
      ((Finset.univ.sum fun i => tri_floorJobs x K i : Nat) : Real) <= K := by
    calc
      ((Finset.univ.sum fun i => tri_floorJobs x K i : Nat) : Real) =
          Finset.univ.sum (fun i => ((tri_floorJobs x K i : Nat) : Real)) := by
            exact Nat.cast_sum (f := fun i => tri_floorJobs x K i) Finset.univ
      _ <= Finset.univ.sum (fun i => (K : Real) * x i) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = (K : Real) * Finset.univ.sum (fun i => x i) := by
        rw [Finset.mul_sum]
      _ = K := by rw [x.sum_eq_one, mul_one]
  exact_mod_cast hreal

private noncomputable def tri_roundedJobs
    (x : Simplex Buffer) (K : Nat) (i0 : Buffer) :
    Buffer -> Nat :=
  Function.update (tri_floorJobs x K) i0
    (tri_floorJobs x K i0 +
      (K - Finset.univ.sum fun i => tri_floorJobs x K i))

private theorem tri_sum_tri_roundedJobs (x : Simplex Buffer) (K : Nat) (i0 : Buffer) :
    Finset.univ.sum (tri_roundedJobs x K i0) = K := by
  classical
  let base : Buffer -> Nat := tri_floorJobs x K
  let remainder := K - Finset.univ.sum base
  have hbase : Finset.univ.sum base <= K := tri_sum_tri_floorJobs_le x K
  have hsum :=
    Finset.sum_erase_add Finset.univ base (Finset.mem_univ i0)
  unfold tri_roundedJobs
  change
    Finset.univ.sum (Function.update base i0 (base i0 + remainder)) = K
  rw [Finset.sum_update_of_mem (Finset.mem_univ i0)]
  simp only [Finset.sdiff_singleton_eq_erase]
  calc
    base i0 + remainder + (Finset.univ.erase i0).sum base =
        ((Finset.univ.erase i0).sum base + base i0) + remainder := by
          omega
    _ = Finset.univ.sum base + remainder := by rw [hsum]
    _ = K := Nat.add_sub_of_le hbase

private noncomputable def tri_roundedState
    (x : Simplex Buffer) (K : Nat) (i0 : Buffer) :
    JobState Buffer K where
  jobs := tri_roundedJobs x K i0
  total_jobs := tri_sum_tri_roundedJobs x K i0

private theorem tri_roundingRemainder_le_card (x : Simplex Buffer) (K : Nat) :
    K - Finset.univ.sum (fun i => tri_floorJobs x K i) <=
      Fintype.card Buffer := by
  let S := Finset.univ.sum fun i => tri_floorJobs x K i
  have hsumlt :
      (K : Real) <
        (S : Real) + Fintype.card Buffer := by
    calc
      (K : Real) =
          Finset.univ.sum (fun i => (K : Real) * x i) := by
            rw [<- Finset.mul_sum, x.sum_eq_one, mul_one]
      _ < Finset.univ.sum
          (fun i => ((tri_floorJobs x K i : Nat) : Real) + 1) := by
            apply Finset.sum_lt_sum
            · intro i _
              exact le_of_lt (Nat.lt_floor_add_one ((K : Real) * x i))
            · let i0 : Buffer :=
                Classical.choice (inferInstance : Nonempty Buffer)
              exact ⟨i0, Finset.mem_univ _, Nat.lt_floor_add_one _⟩
      _ = (S : Real) + Fintype.card Buffer := by
            rw [Finset.sum_add_distrib]
            simp [S, Nat.cast_sum]
  have hnat : K < S + Fintype.card Buffer := by
    exact_mod_cast hsumlt
  omega

private theorem tri_tri_roundedState_error_bound
    (x : Simplex Buffer) (K : Nat) (hK : 0 < K) (i0 i : Buffer) :
    abs (((tri_roundedState x K i0 i : Nat) : Real) / K - x i) <
      (((Fintype.card Buffer : Nat) : Real) + 1) / (K : Real) := by
  classical
  let b : Nat := tri_floorJobs x K i
  let r : Nat := K - Finset.univ.sum (fun q => tri_floorJobs x K q)
  have hb_le : (b : Real) <= (K : Real) * x i := by
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) (x.nonneg i))
  have hlt_b : (K : Real) * x i < (b : Real) + 1 :=
    Nat.lt_floor_add_one ((K : Real) * x i)
  have hr : r <= Fintype.card Buffer :=
    tri_roundingRemainder_le_card x K
  have hb_jobs : b <= tri_roundedState x K i0 i := by
    by_cases hi : i = i0
    · subst i
      simp [tri_roundedState, tri_roundedJobs, b, r]
    · simp [tri_roundedState, tri_roundedJobs, b, hi]
  have hjobs_le : tri_roundedState x K i0 i <= b + r := by
    by_cases hi : i = i0
    · subst i
      simp [tri_roundedState, tri_roundedJobs, b, r]
    · simp [tri_roundedState, tri_roundedJobs, b, hi]
  have hdiff_lower :
      -1 < ((tri_roundedState x K i0 i : Nat) : Real) - (K : Real) * x i := by
    have hb_jobs_real :
        (b : Real) <= ((tri_roundedState x K i0 i : Nat) : Real) := by
      exact_mod_cast hb_jobs
    linarith
  have hdiff_upper :
      ((tri_roundedState x K i0 i : Nat) : Real) - (K : Real) * x i <=
        (Fintype.card Buffer : Real) := by
    have hjobs_le_real :
        ((tri_roundedState x K i0 i : Nat) : Real) <= (b : Real) + r := by
      exact_mod_cast hjobs_le
    have hrreal : (r : Real) <= Fintype.card Buffer := by
      exact_mod_cast hr
    linarith
  have habs :
      abs (((tri_roundedState x K i0 i : Nat) : Real) - (K : Real) * x i) <
        (Fintype.card Buffer : Real) + 1 := by
    rw [abs_lt]
    constructor
    · have hc : 0 <= (Fintype.card Buffer : Real) := Nat.cast_nonneg _
      linarith
    · linarith
  have hKreal : 0 < (K : Real) := Nat.cast_pos.mpr hK
  rw [show
      ((tri_roundedState x K i0 i : Nat) : Real) / K - x i =
        (((tri_roundedState x K i0 i : Nat) : Real) - (K : Real) * x i) / K by
      field_simp]
  rw [abs_div, abs_of_pos hKreal]
  exact div_lt_div_of_pos_right habs hKreal

private theorem tri_exists_near_normalized_state
    (x : Simplex Buffer) (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists K : PNat, exists z : JobState Buffer (K : Nat),
      epsilon ^ (-1 : Int) <= (K : Real) /\
      IsNearNormalizedState z x epsilon := by
  let c : Real := (Fintype.card Buffer : Real) + 1
  obtain ⟨K : Nat, hKlarge⟩ :=
    exists_nat_gt (max (epsilon ^ (-1 : Int)) (c / epsilon))
  have hKpos : 0 < K := by
    have hnonneg : 0 <= epsilon ^ (-1 : Int) := by positivity
    exact_mod_cast
      lt_of_le_of_lt hnonneg
        (lt_of_le_of_lt (le_max_left _ _) hKlarge)
  let Kp : PNat := ⟨K, hKpos⟩
  let i0 : Buffer := Classical.choice (inferInstance : Nonempty Buffer)
  let z : JobState Buffer K := tri_roundedState x K i0
  refine ⟨Kp, z, ?_, ?_⟩
  · exact le_of_lt (lt_of_le_of_lt (le_max_left _ _) hKlarge)
  · intro i
    have hbound := tri_tri_roundedState_error_bound x K hKpos i0 i
    have hKc : c / epsilon < (K : Real) :=
      lt_of_le_of_lt (le_max_right _ _) hKlarge
    have hratio : c / (K : Real) < epsilon := by
      apply (div_lt_iff₀ (Nat.cast_pos.mpr hKpos)).2
      apply (div_lt_iff₀ hepsilon).1 at hKc
      nlinarith
    exact hbound.trans hratio

private theorem tri_exists_actionDirac_mem_fluidPolicyCorrespondence
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Simplex Buffer) :
    exists a : N.ServiceAction,
      (forall i, a = some i -> N.compatible i j) /\
      Membership.mem (N.fluidPolicyCorrespondence U j k x)
        (N.actionDirac a) := by
  classical
  let epsilon : Nat -> Real := fun n => 1 / ((n : Real) + 1)
  have hepsilon (n : Nat) : 0 < epsilon n := by
    dsimp [epsilon]
    positivity
  have happrox :
      forall n : Nat, exists K : PNat,
        exists z : JobState Buffer (K : Nat),
          (epsilon n) ^ (-1 : Int) <= (K : Real) /\
          IsNearNormalizedState z x (epsilon n) := by
    intro n
    exact tri_exists_near_normalized_state x (epsilon n) (hepsilon n)
  choose K z hK hnear using happrox
  let action : Nat -> N.ServiceAction := fun n => U (K n) (z n) j k
  have hfrequent :
      exists a : N.ServiceAction,
        Filter.Frequently (fun n => action n = a) atTop := by
    rw [<- Filter.frequently_exists]
    exact Filter.Frequently.of_forall fun n => ⟨action n, rfl⟩
  obtain ⟨a, ha⟩ := hfrequent
  have hone : forall i, a = some i -> N.compatible i j := by
    intro i hai
    obtain ⟨n, _hn, hna⟩ := Filter.frequently_atTop.mp ha 0
    have hlegal := (U (K n)).legal (z n) j k
    have haction : U (K n) (z n) j k = some i := by
      change action n = some i
      rw [hna, hai]
    rw [haction] at hlegal
    exact hlegal.1
  refine ⟨a, hone, ?_⟩
  unfold fluidPolicyCorrespondence
  rw [Set.mem_iInter]
  intro e
  obtain ⟨m : Nat, hm⟩ := exists_nat_one_div_lt e.property
  obtain ⟨n, hmn, hna⟩ := Filter.frequently_atTop.mp ha m
  have hepsilon_le : epsilon n <= 1 / ((m : Real) + 1) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hmn 1
  have hsmall : epsilon n < e.1 := hepsilon_le.trans_lt hm
  apply subset_closure
  apply subset_convexHull Real
  refine ⟨K n, z n, ?_, ?_, ?_⟩
  · have hinv : e.1⁻¹ <= (epsilon n)⁻¹ :=
      (inv_le_inv₀ e.property (hepsilon n)).2 (le_of_lt hsmall)
    exact hinv.trans (by simpa [zpow_neg_one] using hK n)
  · intro i
    exact (hnear n i).trans hsmall
  · change N.actionDirac a = N.actionDirac (action n)
    rw [hna]

private theorem tri_fluidPolicyCorrespondence_isActionDistribution
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real)
    (q : ActionVector Buffer)
    (hq : Membership.mem (N.fluidPolicyCorrespondence U j k x) q) :
    IsActionDistribution q := by
  classical
  let e : {r : Real // 0 < r} := ⟨1, one_pos⟩
  have hqe :
      q ∈ closure (convexHull Real
        {r | exists K : PNat, exists z : JobState Buffer (K : Nat),
          e.1⁻¹ <= (K : Real) /\
          IsNearNormalizedState z x e.1 /\
          r = N.actionDirac (U K z j k)}) := by
    exact Set.mem_iInter.mp hq e
  constructor
  · intro a
    let H : Set (ActionVector Buffer) := {r | 0 <= r a}
    have hHclosed : IsClosed H :=
      isClosed_le continuous_const (continuous_apply a)
    have hHconvex : Convex Real H := by
      intro r hr s hs c d hc hd hcd
      change 0 <= (c • r + d • s) a
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg hc hr) (mul_nonneg hd hs)
    have hbase :
        {r | exists K : PNat, exists z : JobState Buffer (K : Nat),
          e.1⁻¹ <= (K : Real) /\
          IsNearNormalizedState z x e.1 /\
          r = N.actionDirac (U K z j k)} <= H := by
      rintro r ⟨K, z, _hK, _hz, rfl⟩
      exact (N.actionDirac_isDistribution (U K z j k)).1 a
    exact closure_minimal (convexHull_min hbase hHconvex) hHclosed hqe
  · let H : Set (ActionVector Buffer) := {r | Finset.univ.sum r = 1}
    have hHclosed : IsClosed H := by
      exact isClosed_eq
        (continuous_finset_sum _ fun a _ => continuous_apply a)
        continuous_const
    have hHconvex : Convex Real H := by
      intro r hr s hs c d hc hd hcd
      change Finset.univ.sum r = 1 at hr
      change Finset.univ.sum s = 1 at hs
      change Finset.univ.sum (c • r + d • s) = 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_add_distrib, <- Finset.mul_sum, hr, hs]
      linarith
    have hbase :
        {r | exists K : PNat, exists z : JobState Buffer (K : Nat),
          e.1⁻¹ <= (K : Real) /\
          IsNearNormalizedState z x e.1 /\
          r = N.actionDirac (U K z j k)} <= H := by
      rintro r ⟨K, z, _hK, _hz, rfl⟩
      exact (N.actionDirac_isDistribution (U K z j k)).2
    exact closure_minimal (convexHull_min hbase hHconvex) hHclosed hqe

private theorem tri_fluidPolicyCorrespondence_incompatible
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k i : Buffer) (x : Buffer -> Real)
    (q : ActionVector Buffer)
    (hq : Membership.mem (N.fluidPolicyCorrespondence U j k x) q)
    (hij : Not (N.compatible i j)) :
    q (some i) = 0 := by
  classical
  let e : {r : Real // 0 < r} := ⟨1, one_pos⟩
  let H : Set (ActionVector Buffer) := {r | r (some i) = 0}
  have hHclosed : IsClosed H :=
    isClosed_eq (continuous_apply (some i)) continuous_const
  have hHconvex : Convex Real H :=
    convex_hyperplane (LinearMap.proj (some i)).isLinear 0
  have hbase :
      {r | exists K : PNat, exists z : JobState Buffer (K : Nat),
        e.1⁻¹ <= (K : Real) /\
        IsNearNormalizedState z x e.1 /\
        r = N.actionDirac (U K z j k)} <= H := by
    rintro r ⟨K, z, _hK, _hz, rfl⟩
    have hne : Not (some i = U K z j k) := by
      intro heq
      have hlegal := (U K).legal z j k
      rw [<- heq] at hlegal
      exact hij hlegal.1
    simp [H, actionDirac, hne]
  unfold fluidPolicyCorrespondence at hq
  have hqe := Set.mem_iInter.mp hq e
  exact closure_minimal (convexHull_min hbase hHconvex) hHclosed hqe

private theorem tri_fluidPolicyCorrespondence_convex
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) :
    Convex Real (N.fluidPolicyCorrespondence U j k x) := by
  unfold fluidPolicyCorrespondence
  exact convex_iInter fun _ => (convex_convexHull Real _).closure

private def tri_fluidPolicyCorrespondenceGraph
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    Set ((Buffer -> Real) × ActionVector Buffer) :=
  {xp | Membership.mem (N.fluidPolicyCorrespondence U j k xp.1) xp.2}

private theorem tri_tri_fluidPolicyCorrespondenceGraph_isClosed
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    IsClosed (N.tri_fluidPolicyCorrespondenceGraph U j k) := by
  rw [<- isSeqClosed_iff_isClosed]
  intro s xp hs hsxp
  rcases xp with ⟨x, p⟩
  have hx : Tendsto (fun n => (s n).1) atTop (nhds x) :=
    hsxp.fst_nhds
  have hp : Tendsto (fun n => (s n).2) atTop (nhds p) :=
    hsxp.snd_nhds
  unfold tri_fluidPolicyCorrespondenceGraph at hs ⊢
  simp only [Set.mem_setOf_eq] at hs ⊢
  unfold fluidPolicyCorrespondence
  rw [Set.mem_iInter]
  intro e
  let d : {epsilon : Real // 0 < epsilon} :=
    ⟨e.1 / 2, half_pos e.property⟩
  have hcoord :
      forall i : Buffer,
        Filter.Eventually (fun n => abs ((s n).1 i - x i) < d.1)
          atTop := by
    intro i
    have hi : Tendsto (fun n => (s n).1 i) atTop (nhds (x i)) :=
      tendsto_pi_nhds.mp hx i
    simpa [Real.dist_eq] using
      (Metric.tendsto_nhds.mp hi d.1 d.property)
  have hall :
      Filter.Eventually (fun n => forall i : Buffer,
        abs ((s n).1 i - x i) < d.1) atTop :=
    Filter.eventually_all.mpr hcoord
  have hfixed :
      Filter.Eventually
        (fun n => (s n).2 ∈ closure (convexHull Real
          {q | exists K : PNat, exists z : JobState Buffer (K : Nat),
            e.1⁻¹ <= (K : Real) /\
            IsNearNormalizedState z x e.1 /\
            q = actionDirac N (U K z j k)})) atTop := by
    filter_upwards [hall] with n hn
    have hnd :
        (s n).2 ∈ closure (convexHull Real
          {q | exists K : PNat, exists z : JobState Buffer (K : Nat),
            d.1⁻¹ <= (K : Real) /\
            IsNearNormalizedState z (s n).1 d.1 /\
            q = actionDirac N (U K z j k)}) := by
      have hsn := hs n
      unfold fluidPolicyCorrespondence at hsn
      exact Set.mem_iInter.mp hsn d
    apply closure_mono (convexHull_mono ?_) hnd
    rintro q ⟨K, z, hK, hnear, hq⟩
    refine ⟨K, z, ?_, ?_, hq⟩
    · have hed : d.1 <= e.1 := by
        dsimp [d]
        linarith [e.property]
      exact ((inv_le_inv₀ e.property d.property).2 hed).trans hK
    · intro i
      calc
        abs ((z i : Real) / (K : Nat) - x i) =
            abs (((z i : Real) / (K : Nat) - (s n).1 i) +
              ((s n).1 i - x i)) := by ring_nf
        _ <= abs ((z i : Real) / (K : Nat) - (s n).1 i) +
            abs ((s n).1 i - x i) := abs_add_le _ _
        _ < d.1 + d.1 := add_lt_add (hnear i) (hn i)
        _ = e.1 := by
          dsimp [d]
          ring
  exact isClosed_closure.mem_of_tendsto hp hfixed

private theorem tri_actionDirac_feasibleSet_isClosed
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (a : N.ServiceAction) :
    IsClosed {x : Buffer -> Real |
      N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x} := by
  let f : (Buffer -> Real) ->
      (Buffer -> Real) × ActionVector Buffer :=
    fun x => (x, N.actionDirac a)
  have hf : Continuous f := continuous_id.prodMk continuous_const
  exact (N.tri_tri_fluidPolicyCorrespondenceGraph_isClosed U j k).preimage hf

private noncomputable def tri_feasiblePureActionMass
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) : Real := by
  classical
  exact Finset.univ.sum fun a : N.ServiceAction =>
    if N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x then 1 else 0

private noncomputable def tri_feasiblePureActionSum
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) :
    ActionVector Buffer := by
  classical
  exact fun b =>
    Finset.univ.sum fun a : N.ServiceAction =>
      if N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x then
        N.actionDirac a b
      else 0

private noncomputable def tri_measurableFluidPolicySelector
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) :
    ActionVector Buffer := by
  classical
  exact
    if N.tri_feasiblePureActionMass U j k x = 0 then
      N.actionDirac none
    else
      (N.tri_feasiblePureActionMass U j k x)⁻¹ •
        N.tri_feasiblePureActionSum U j k x

private theorem tri_tri_feasiblePureActionMass_measurable
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    Measurable (N.tri_feasiblePureActionMass U j k) := by
  classical
  unfold tri_feasiblePureActionMass
  apply Finset.measurable_fun_sum
  intro a _ha
  apply Measurable.ite
  · exact (tri_actionDirac_feasibleSet_isClosed N U j k a).measurableSet
  · exact measurable_const
  · exact measurable_const

private theorem tri_tri_feasiblePureActionSum_coordinate_measurable
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (b : Option Buffer) :
    Measurable (fun x => N.tri_feasiblePureActionSum U j k x b) := by
  classical
  unfold tri_feasiblePureActionSum
  apply Finset.measurable_fun_sum
  intro a _ha
  apply Measurable.ite
  · exact (tri_actionDirac_feasibleSet_isClosed N U j k a).measurableSet
  · exact measurable_const
  · exact measurable_const

private theorem tri_tri_measurableFluidPolicySelector_measurable
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    Measurable (N.tri_measurableFluidPolicySelector U j k) := by
  rw [measurable_pi_iff]
  intro b
  unfold tri_measurableFluidPolicySelector
  simp only [ite_apply, Pi.smul_apply, smul_eq_mul]
  apply Measurable.ite
  · exact measurableSet_eq_fun
      (tri_tri_feasiblePureActionMass_measurable N U j k) measurable_const
  · exact measurable_const
  · exact (tri_tri_feasiblePureActionMass_measurable N U j k).inv.mul
      (tri_tri_feasiblePureActionSum_coordinate_measurable N U j k b)

private theorem tri_tri_measurableFluidPolicySelector_mem
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real)
    (hx : IsFluidState x) :
    N.tri_measurableFluidPolicySelector U j k x ∈
      N.fluidPolicyCorrespondence U j k x := by
  classical
  let s : Finset N.ServiceAction :=
    Finset.univ.filter fun a =>
      N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x
  have hs : s.Nonempty := by
    let sx : Simplex Buffer := {
      val := x
      nonneg := hx.1
      sum_eq_one := hx.2
    }
    obtain ⟨a, _hcompat, ha⟩ :=
      tri_exists_actionDirac_mem_fluidPolicyCorrespondence N U j k sx
    refine ⟨a, ?_⟩
    simp [s, sx] at ha ⊢
    exact ha
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  have hmass :
      N.tri_feasiblePureActionMass U j k x = (s.card : Real) := by
    unfold tri_feasiblePureActionMass
    rw [<- Finset.sum_filter]
    change Finset.sum s (fun _a => (1 : Real)) = (s.card : Real)
    simp
  have hmass_ne : Ne (N.tri_feasiblePureActionMass U j k x) 0 := by
    rw [hmass]
    exact_mod_cast Nat.ne_of_gt hcard
  have hsum :
      N.tri_feasiblePureActionSum U j k x =
        Finset.sum s fun a => N.actionDirac a := by
    funext b
    unfold tri_feasiblePureActionSum
    rw [<- Finset.sum_filter]
    rw [Finset.sum_apply]
  have hweights :
      Finset.sum s (fun _a => (s.card : Real)⁻¹) = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hcard)
  have havg :
      (Finset.sum s fun a =>
        (s.card : Real)⁻¹ • N.actionDirac a) ∈
        N.fluidPolicyCorrespondence U j k x := by
    apply (N.tri_fluidPolicyCorrespondence_convex U j k x).sum_mem
    · intro a ha
      positivity
    · exact hweights
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
  rw [tri_measurableFluidPolicySelector, if_neg hmass_ne, hmass, hsum]
  simpa only [Finset.smul_sum] using havg

private def tri_fluidPolicyEpsilonCorrespondence
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (epsilon : Real) : Set (ActionVector Buffer) :=
  closure (convexHull Real
    {q | exists K : PNat, exists z : JobState Buffer (K : Nat),
      epsilon⁻¹ <= (K : Real) /\
      IsNearNormalizedState z x epsilon /\
      q = N.actionDirac (U K z j k)})

private noncomputable def tri_finiteDifferenceRatio
    (N : Network Buffer Server)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t h : Real) : ActionVector Buffer :=
  fun a => (E (t + h) a - E t a) / (A (t + h) - A t)

private noncomputable def tri_verifiedPatchedFluidPolicy
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) : ActionVector Buffer := by
  classical
  let q : ActionVector Buffer :=
    fun a => deriv (fun s => E s a) t / deriv A t
  exact if q ∈ N.fluidPolicyCorrespondence U j k (X t) then q
    else N.tri_measurableFluidPolicySelector U j k (X t)

private theorem tri_tri_measurableFluidPolicySelector_comp
    {Time : Type*} [MeasurableSpace Time]
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Time -> Buffer -> Real)
    (hX : forall i, Measurable (fun t => X t i))
    (a : Option Buffer) :
    Measurable
      (fun t => N.tri_measurableFluidPolicySelector U j k (X t) a) := by
  exact
    (measurable_pi_iff.mp
      (N.tri_tri_measurableFluidPolicySelector_measurable U j k) a).comp
      (measurable_pi_lambda X hX)

private theorem tri_tri_fluidPolicyEpsilonCorrespondence_isClosed
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (epsilon : Real) :
    IsClosed (N.tri_fluidPolicyEpsilonCorrespondence U j k x epsilon) :=
  isClosed_closure

private theorem tri_mem_fluidPolicyCorrespondence_iff_epsilon
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (q : ActionVector Buffer) :
    q ∈ N.fluidPolicyCorrespondence U j k x <->
      forall epsilon : {r : Real // 0 < r},
        q ∈ N.tri_fluidPolicyEpsilonCorrespondence U j k x epsilon.1 := by
  unfold fluidPolicyCorrespondence tri_fluidPolicyEpsilonCorrespondence
  rw [Set.mem_iInter]

private theorem tri_weightedEmpiricalActionAverage_mem_epsilon
    {I : Type w} (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    (s : Finset I) (weight : I -> Real)
    (K : I -> PNat)
    (z : (r : I) -> JobState Buffer (K r : Nat))
    (hweight_nonneg : forall r, r ∈ s -> 0 <= weight r)
    (hweight_sum : Finset.sum s weight = 1)
    (hK : forall r, r ∈ s -> epsilon⁻¹ <= ((K r : Nat) : Real))
    (hz : forall r, r ∈ s -> IsNearNormalizedState (z r) x epsilon) :
    (Finset.sum s fun r =>
      (weight r) • N.actionDirac (U (K r) (z r) j k)) ∈
        N.tri_fluidPolicyEpsilonCorrespondence U j k x epsilon := by
  apply subset_closure
  apply (convex_convexHull Real _).sum_mem hweight_nonneg hweight_sum
  intro r hr
  apply subset_convexHull Real
  exact ⟨K r, z r, hK r hr, hz r hr, rfl⟩

private theorem tri_closed_mem_of_tri_finiteDifferenceRatio_limit
    {C : Set (ActionVector Buffer)}
    (hC : IsClosed C)
    (Aseq : Nat -> Real -> Real) (A : Real -> Real)
    (Eseq : Nat -> Real -> ActionVector Buffer)
    (E : Real -> ActionVector Buffer)
    (s t : Real)
    (hAs : Tendsto (fun n => Aseq n s) atTop (nhds (A s)))
    (hAt : Tendsto (fun n => Aseq n t) atTop (nhds (A t)))
    (hEs : forall a,
      Tendsto (fun n => Eseq n s a) atTop (nhds (E s a)))
    (hEt : forall a,
      Tendsto (fun n => Eseq n t a) atTop (nhds (E t a)))
    (hden : Ne (A t - A s) 0)
    (hmem : Filter.Eventually
      (fun n => (fun a => (Eseq n t a - Eseq n s a) /
          (Aseq n t - Aseq n s)) ∈ C) atTop) :
    (fun a => (E t a - E s a) / (A t - A s)) ∈ C := by
  apply hC.mem_of_tendsto _ hmem
  rw [tendsto_pi_nhds]
  intro a
  exact ((hEt a).sub (hEs a)).div (hAt.sub hAs) hden

private theorem tri_derivativeRatio_mem_closed_of_right_finiteDifferences
    {C : Set (ActionVector Buffer)}
    (hC : IsClosed C)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t Adot : Real) (Edot : ActionVector Buffer)
    (hA : HasDerivAt A Adot t)
    (hE : forall a, HasDerivAt (fun s => E s a) (Edot a) t)
    (hAdot : 0 < Adot)
    (hmem : Filter.Eventually
      (fun h => N.tri_finiteDifferenceRatio A E t h ∈ C)
      (nhdsWithin 0 (Ioi 0))) :
    (fun a => Edot a / Adot) ∈ C := by
  have htendsto :
      Tendsto (N.tri_finiteDifferenceRatio A E t)
        (nhdsWithin 0 (Ioi 0)) (nhds (fun a => Edot a / Adot)) := by
    let slopeRatio : Real -> ActionVector Buffer :=
      fun h a =>
        (h⁻¹ * (E (t + h) a - E t a)) /
          (h⁻¹ * (A (t + h) - A t))
    have hslope :
        Tendsto slopeRatio (nhdsWithin 0 (Ioi 0))
          (nhds (fun a => Edot a / Adot)) := by
      rw [tendsto_pi_nhds]
      intro a
      exact ((hE a).tendsto_slope_zero_right).div
        hA.tendsto_slope_zero_right (ne_of_gt hAdot)
    apply hslope.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    funext a
    have hh0 : Ne h 0 := ne_of_gt hh
    dsimp [slopeRatio, tri_finiteDifferenceRatio]
    field_simp
  exact hC.mem_of_tendsto htendsto hmem

private theorem tri_derivativeRatio_mem_fluidPolicyCorrespondence
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t Adot : Real) (Edot : ActionVector Buffer)
    (hA : HasDerivAt A Adot t)
    (hE : forall a, HasDerivAt (fun s => E s a) (Edot a) t)
    (hAdot : 0 < Adot)
    (hfinite : forall epsilon : {r : Real // 0 < r},
      Filter.Eventually
        (fun h => N.tri_finiteDifferenceRatio A E t h ∈
          N.tri_fluidPolicyEpsilonCorrespondence U j k x epsilon.1)
        (nhdsWithin 0 (Ioi 0))) :
    (fun a => Edot a / Adot) ∈
      N.fluidPolicyCorrespondence U j k x := by
  rw [N.tri_mem_fluidPolicyCorrespondence_iff_epsilon]
  intro epsilon
  exact N.tri_derivativeRatio_mem_closed_of_right_finiteDifferences
    (N.tri_tri_fluidPolicyEpsilonCorrespondence_isClosed U j k x epsilon.1)
    A E t Adot Edot hA hE hAdot (hfinite epsilon)

private theorem tri_ae_tri_derivativeRatio_mem_fluidPolicyCorrespondence
    {TimeMeasure : Measure Real}
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (hA : Filter.Eventually (fun t => DifferentiableAt Real A t)
      (ae TimeMeasure))
    (hE : forall a, Filter.Eventually
      (fun t => DifferentiableAt Real (fun s => E s a) t)
      (ae TimeMeasure))
    (hfinite : Filter.Eventually
      (fun t => 0 < deriv A t ->
        forall epsilon : {r : Real // 0 < r},
          Filter.Eventually
            (fun h =>
              N.tri_finiteDifferenceRatio A E t h ∈
                N.tri_fluidPolicyEpsilonCorrespondence
                  U j k (X t) epsilon.1)
            (nhdsWithin 0 (Ioi 0)))
      (ae TimeMeasure)) :
    Filter.Eventually
      (fun t => 0 < deriv A t ->
        (fun a => deriv (fun s => E s a) t / deriv A t) ∈
          N.fluidPolicyCorrespondence U j k (X t))
      (ae TimeMeasure) := by
  have hEall :
      Filter.Eventually
        (fun t => forall a, DifferentiableAt Real (fun s => E s a) t)
        (ae TimeMeasure) :=
    ae_all_iff.mpr hE
  filter_upwards [hA, hEall, hfinite] with t hAt hEt hft
  intro hpos
  exact N.tri_derivativeRatio_mem_fluidPolicyCorrespondence
    U j k (X t) A E t (deriv A t)
    (fun a => deriv (fun s => E s a) t)
    hAt.hasDerivAt (fun a => (hEt a).hasDerivAt) hpos (hft hpos)

private theorem tri_tri_verifiedPatchedFluidPolicy_coordinate_measurable
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (hX : forall i, Measurable (fun t => X t i))
    (a : Option Buffer) :
    Measurable
      (fun t => N.tri_verifiedPatchedFluidPolicy U j k X A E t a) := by
  classical
  let q : Real -> ActionVector Buffer :=
    fun t a => deriv (fun s => E s a) t / deriv A t
  have hq : Measurable q := by
    rw [measurable_pi_iff]
    intro b
    exact (measurable_deriv (fun s => E s b)).div (measurable_deriv A)
  have hpair : Measurable (fun t => (X t, q t)) :=
    (measurable_pi_lambda X hX).prodMk hq
  have hcondition :
      MeasurableSet {t |
        q t ∈ N.fluidPolicyCorrespondence U j k (X t)} := by
    have hgraph :=
      (N.tri_tri_fluidPolicyCorrespondenceGraph_isClosed U j k).measurableSet.preimage
        hpair
    change MeasurableSet {t |
      q t ∈ N.fluidPolicyCorrespondence U j k (X t)} at hgraph
    exact hgraph
  dsimp [q] at hcondition
  unfold tri_verifiedPatchedFluidPolicy
  simp only [ite_apply]
  apply Measurable.ite hcondition
  · exact (measurable_deriv (fun s => E s a)).div (measurable_deriv A)
  · exact N.tri_tri_measurableFluidPolicySelector_comp U j k X hX a

private theorem tri_tri_verifiedPatchedFluidPolicy_mem
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) (hstate : IsFluidState (X t)) :
    N.tri_verifiedPatchedFluidPolicy U j k X A E t ∈
      N.fluidPolicyCorrespondence U j k (X t) := by
  classical
  let q : ActionVector Buffer :=
    fun a => deriv (fun s => E s a) t / deriv A t
  by_cases hq : q ∈ N.fluidPolicyCorrespondence U j k (X t)
  · simpa [tri_verifiedPatchedFluidPolicy, q, hq] using hq
  · simp only [tri_verifiedPatchedFluidPolicy, q, if_neg hq]
    exact N.tri_tri_measurableFluidPolicySelector_mem U j k (X t) hstate

private theorem tri_tri_verifiedPatchedFluidPolicy_isActionDistribution
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) (hstate : IsFluidState (X t)) :
    IsActionDistribution
      (N.tri_verifiedPatchedFluidPolicy U j k X A E t) :=
  tri_fluidPolicyCorrespondence_isActionDistribution N U j k (X t) _
    (N.tri_tri_verifiedPatchedFluidPolicy_mem U j k X A E t hstate)

private theorem tri_tri_verifiedPatchedFluidPolicy_incompatible_zero
    (U : N.DeterministicPolicySequence) (j : Server) (k i : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) (hstate : IsFluidState (X t))
    (hi : Not (N.compatible i j)) :
    N.tri_verifiedPatchedFluidPolicy U j k X A E t (some i) = 0 :=
  tri_fluidPolicyCorrespondence_incompatible N U j k i (X t) _
    (N.tri_tri_verifiedPatchedFluidPolicy_mem U j k X A E t hstate) hi

private theorem tri_tri_verifiedPatchedFluidPolicy_allocation_rule_ae
    {TimeMeasure : Measure Real}
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (hAnonneg : Filter.Eventually (fun t => 0 <= deriv A t)
      (ae TimeMeasure))
    (hpositive : Filter.Eventually
      (fun t => 0 < deriv A t ->
        (fun a => deriv (fun s => E s a) t / deriv A t) ∈
          N.fluidPolicyCorrespondence U j k (X t))
      (ae TimeMeasure))
    (hzero : Filter.Eventually
      (fun t => deriv A t = 0 ->
        forall a, deriv (fun s => E s a) t = 0)
      (ae TimeMeasure)) :
    Filter.Eventually
      (fun t => forall a,
        deriv (fun s => E s a) t =
          deriv A t *
            N.tri_verifiedPatchedFluidPolicy U j k X A E t a)
      (ae TimeMeasure) := by
  classical
  filter_upwards [hAnonneg, hpositive, hzero] with t hnonneg hpt hzt
  intro a
  by_cases hpos : 0 < deriv A t
  · have hmem := hpt hpos
    simp only [tri_verifiedPatchedFluidPolicy, if_pos hmem]
    field_simp
  · have hz : deriv A t = 0 :=
      le_antisymm (not_lt.mp hpos) hnonneg
    simp [tri_verifiedPatchedFluidPolicy, hz, hzt hz a]


private def edgeProgress (r : Real) (l : Nat) : Real :=
  max 0 (min 1 (r - l))

private theorem edgeProgress_nonneg (r : Real) (l : Nat) :
    0 <= edgeProgress r l := by
  unfold edgeProgress
  exact le_max_left _ _

private theorem edgeProgress_mono {r q : Real} (hrq : r <= q) (l : Nat) :
    edgeProgress r l <= edgeProgress q l := by
  unfold edgeProgress
  exact max_le_max (le_refl 0)
    (min_le_min (le_refl 1) (sub_le_sub_right hrq _))

/-- Fraction of edge `edge i` traversed by the interval `[s,t]`. -/
private def edgeWindowWeight {I : Type w} (edge : I -> Nat)
    (s t : Real) (i : I) : Real :=
  edgeProgress t (edge i) - edgeProgress s (edge i)

private theorem edgeWindowWeight_nonneg {I : Type w} (edge : I -> Nat)
    {s t : Real} (hst : s <= t) (i : I) :
    0 <= edgeWindowWeight edge s t i := by
  exact sub_nonneg.mpr (edgeProgress_mono hst (edge i))

/-- Common linear interpolation of cumulative input, represented directly
by its finite action occurrences and their grid edges. -/
private def finiteActionInputInterpolate {I : Type w}
    (ids : Finset I) (edge : I -> Nat) (r : Real) : Real :=
  Finset.sum ids fun i => edgeProgress r (edge i)

/-- Common linear interpolation of the cumulative all-action vector.
The action `none` is retained as an ordinary coordinate. -/
private def finiteActionVectorInterpolate {I : Type w}
    (ids : Finset I) (edge : I -> Nat) (action : I -> Option Buffer)
    (r : Real) : ActionVector Buffer :=
  fun a =>
    Finset.sum ids fun i =>
      edgeProgress r (edge i) * N.actionDirac (action i) a

private theorem finiteActionInputInterpolate_increment {I : Type w}
    (ids : Finset I) (edge : I -> Nat) (s t : Real) :
    finiteActionInputInterpolate ids edge t -
        finiteActionInputInterpolate ids edge s =
      Finset.sum ids (edgeWindowWeight edge s t) := by
  rw [finiteActionInputInterpolate, finiteActionInputInterpolate,
    <- Finset.sum_sub_distrib]
  rfl

private theorem finiteActionVectorInterpolate_increment {I : Type w}
    (ids : Finset I) (edge : I -> Nat) (action : I -> Option Buffer)
    (s t : Real) (a : Option Buffer) :
    finiteActionVectorInterpolate N ids edge action t a -
        finiteActionVectorInterpolate N ids edge action s a =
      Finset.sum ids fun i =>
        edgeWindowWeight edge s t i * N.actionDirac (action i) a := by
  rw [finiteActionVectorInterpolate, finiteActionVectorInterpolate,
    <- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  unfold edgeWindowWeight
  ring

/-- Positive finite differences of the common interpolation are exactly
convex weighted averages of the finite actions, including `none`. -/
private theorem finiteActionInterpolate_ratio_eq_weightedAverage
    {I : Type w} (ids : Finset I) (edge : I -> Nat)
    (action : I -> Option Buffer) (s t : Real)
    (_hpos :
      0 < finiteActionInputInterpolate ids edge t -
        finiteActionInputInterpolate ids edge s) :
    (fun a =>
      (finiteActionVectorInterpolate N ids edge action t a -
          finiteActionVectorInterpolate N ids edge action s a) /
        (finiteActionInputInterpolate ids edge t -
          finiteActionInputInterpolate ids edge s)) =
      Finset.sum ids fun i =>
        ((edgeWindowWeight edge s t i) /
          (finiteActionInputInterpolate ids edge t -
            finiteActionInputInterpolate ids edge s)) •
          N.actionDirac (action i) := by
  funext a
  rw [finiteActionVectorInterpolate_increment]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_div_right_comm _ _ _

private theorem finiteActionInterpolate_normalizedWeights_nonneg
    {I : Type w} (ids : Finset I) (edge : I -> Nat)
    {s t : Real} (hst : s <= t)
    (hpos :
      0 < finiteActionInputInterpolate ids edge t -
        finiteActionInputInterpolate ids edge s) :
    forall i, i ∈ ids ->
      0 <= edgeWindowWeight edge s t i /
        (finiteActionInputInterpolate ids edge t -
          finiteActionInputInterpolate ids edge s) := by
  intro i hi
  exact div_nonneg (edgeWindowWeight_nonneg edge hst i) (le_of_lt hpos)

private theorem finiteActionInterpolate_normalizedWeights_sum
    {I : Type w} (ids : Finset I) (edge : I -> Nat)
    (s t : Real)
    (hpos :
      0 < finiteActionInputInterpolate ids edge t -
        finiteActionInputInterpolate ids edge s) :
    Finset.sum ids (fun i =>
      edgeWindowWeight edge s t i /
        (finiteActionInputInterpolate ids edge t -
          finiteActionInputInterpolate ids edge s)) = 1 := by
  rw [<- Finset.sum_div, <- finiteActionInputInterpolate_increment]
  exact div_self (ne_of_gt hpos)

/-- Scheduling-verification bridge for one arbitrary positive interval.
Every indexed occurrence is an exact finite policy action at its own
pre-action state; all occurrences used by the window must be epsilon-near. -/
private theorem finiteActionInterpolate_ratio_mem_epsilon
    {I : Type w} (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    (ids : Finset I) (edge : I -> Nat)
    (K : I -> PNat)
    (z : (r : I) -> JobState Buffer (K r : Nat))
    {s t : Real} (hst : s <= t)
    (hpos :
      0 < finiteActionInputInterpolate ids edge t -
        finiteActionInputInterpolate ids edge s)
    (hK : forall r, r ∈ ids ->
      0 < edgeWindowWeight edge s t r ->
        epsilon⁻¹ <= ((K r : Nat) : Real))
    (hz : forall r, r ∈ ids ->
      0 < edgeWindowWeight edge s t r ->
        IsNearNormalizedState (z r) x epsilon) :
    (fun a =>
      (finiteActionVectorInterpolate N ids edge
            (fun r => U (K r) (z r) j k) t a -
          finiteActionVectorInterpolate N ids edge
            (fun r => U (K r) (z r) j k) s a) /
        (finiteActionInputInterpolate ids edge t -
          finiteActionInputInterpolate ids edge s)) ∈
      N.tri_fluidPolicyEpsilonCorrespondence U j k x epsilon := by
  classical
  let used := ids.filter fun r => 0 < edgeWindowWeight edge s t r
  have hused_subset : used ⊆ ids := Finset.filter_subset _ _
  have hzero (r : I) (hr : r ∈ ids) (hru : r ∉ used) :
      edgeWindowWeight edge s t r = 0 := by
    apply le_antisymm
    · apply not_lt.mp
      intro hpositive
      exact hru (Finset.mem_filter.mpr ⟨hr, hpositive⟩)
    · exact edgeWindowWeight_nonneg edge hst r
  have hweight_sum :
      Finset.sum used (fun r =>
        edgeWindowWeight edge s t r /
          (finiteActionInputInterpolate ids edge t -
            finiteActionInputInterpolate ids edge s)) = 1 := by
    rw [Finset.sum_subset hused_subset]
    · exact finiteActionInterpolate_normalizedWeights_sum
        ids edge s t hpos
    · intro r hr hru
      rw [hzero r hr hru, zero_div]
  have hvector_sum :
      (Finset.sum used fun r =>
          (edgeWindowWeight edge s t r /
            (finiteActionInputInterpolate ids edge t -
              finiteActionInputInterpolate ids edge s)) •
            N.actionDirac (U (K r) (z r) j k)) =
        Finset.sum ids fun r =>
          (edgeWindowWeight edge s t r /
            (finiteActionInputInterpolate ids edge t -
              finiteActionInputInterpolate ids edge s)) •
            N.actionDirac (U (K r) (z r) j k) := by
    apply Finset.sum_subset hused_subset
    intro r hr hru
    rw [hzero r hr hru, zero_div, zero_smul]
  rw [finiteActionInterpolate_ratio_eq_weightedAverage N ids edge
    (fun r => U (K r) (z r) j k) s t hpos]
  rw [<- hvector_sum]
  apply N.tri_weightedEmpiricalActionAverage_mem_epsilon
  · intro r hr
    exact div_nonneg
      (edgeWindowWeight_nonneg edge hst r) (le_of_lt hpos)
  · exact hweight_sum
  · intro r hr
    have hfilter := Finset.mem_filter.mp hr
    simpa using hK r hfilter.1 hfilter.2
  · intro r hr
    have hfilter := Finset.mem_filter.mp hr
    exact hz r hfilter.1 hfilter.2

/-- The same bridge in the `tri_finiteDifferenceRatio` syntax consumed by
`tri_derivativeRatio_mem_fluidPolicyCorrespondence`. -/
private theorem tri_finiteDifferenceRatio_finiteActionInterpolate_mem_epsilon
    {I : Type w} (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    (ids : Finset I) (edge : I -> Nat)
    (K : I -> PNat)
    (z : (r : I) -> JobState Buffer (K r : Nat))
    (t h : Real) (hh : 0 < h)
    (hpos :
      0 < finiteActionInputInterpolate ids edge (t + h) -
        finiteActionInputInterpolate ids edge t)
    (hK : forall r, r ∈ ids ->
      0 < edgeWindowWeight edge t (t + h) r ->
        epsilon⁻¹ <= ((K r : Nat) : Real))
    (hz : forall r, r ∈ ids ->
      0 < edgeWindowWeight edge t (t + h) r ->
        IsNearNormalizedState (z r) x epsilon) :
    N.tri_finiteDifferenceRatio
        (finiteActionInputInterpolate ids edge)
        (finiteActionVectorInterpolate N ids edge
          (fun r => U (K r) (z r) j k))
        t h ∈
      N.tri_fluidPolicyEpsilonCorrespondence U j k x epsilon := by
  apply N.finiteActionInterpolate_ratio_mem_epsilon
      U j k x epsilon ids edge K z
  · linarith
  · exact hpos
  · exact hK
  · exact hz

/-- Finite index of all occurrences in a family of edge batches. -/
private abbrev BatchedOccurrence {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) :=
  Sigma fun l : Fin gridEdges => Fin (states l).length

/-- Input interpolation obtained by assigning every occurrence in batch
`l` to grid edge `l`. -/
private noncomputable def batchedInputInterpolate {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) (r : Real) : Real :=
  finiteActionInputInterpolate
    (Finset.univ : Finset (BatchedOccurrence states))
    (fun q => q.1.val) r

/-- All-action interpolation for batched finite pre-action states. -/
private noncomputable def batchedPolicyActionInterpolate
    {gridEdges : Nat} (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin gridEdges -> List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (r : Real) : ActionVector Buffer :=
  finiteActionVectorInterpolate N
    (Finset.univ : Finset (BatchedOccurrence states))
    (fun q => q.1.val)
    (fun q => U K ((states q.1).get q.2) j k) r

private theorem batchedInputInterpolate_eq_batch_sum
    {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) (r : Real) :
    batchedInputInterpolate states r =
      Finset.univ.sum fun l : Fin gridEdges =>
        Finset.univ.sum fun _q : Fin (states l).length =>
          edgeProgress r l.val := by
  classical
  unfold batchedInputInterpolate finiteActionInputInterpolate
  rw [Fintype.sum_sigma]

private theorem batchedPolicyActionInterpolate_eq_batch_sum
    {gridEdges : Nat} (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin gridEdges -> List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (r : Real) (a : Option Buffer) :
    batchedPolicyActionInterpolate N U K states j k r a =
      Finset.univ.sum fun l : Fin gridEdges =>
        Finset.univ.sum fun q : Fin (states l).length =>
          edgeProgress r l.val *
            N.actionDirac (U K ((states l).get q) j k) a := by
  classical
  unfold batchedPolicyActionInterpolate finiteActionVectorInterpolate
  rw [Fintype.sum_sigma]

/-- Adapter to a cumulative scalar ramp path. -/
private theorem batchedInputInterpolate_eq_cumulativeRamp
    {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) (values : Nat -> Real)
    (r : Real) (hzero : values 0 = 0)
    (hstep : forall l : Fin gridEdges,
      values (l.val + 1) - values l.val = (states l).length) :
    batchedInputInterpolate states r =
      values 0 +
        Finset.sum (Finset.range gridEdges) fun l =>
          (values (l + 1) - values l) * edgeProgress r l := by
  classical
  rw [batchedInputInterpolate_eq_batch_sum]
  rw [hzero, zero_add]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro l hl
  rw [hstep l]
  simp

/-- Adapter to a cumulative all-action coordinate ramp path. -/
private theorem batchedPolicyActionInterpolate_eq_cumulativeRamp
    {gridEdges : Nat} (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin gridEdges -> List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (values : Nat -> ActionVector Buffer)
    (r : Real) (hzero : values 0 = 0)
    (hstep : forall l : Fin gridEdges,
      values (l.val + 1) - values l.val =
        ((states l).map
          (fun y => N.actionDirac (U K y j k))).sum) :
    batchedPolicyActionInterpolate N U K states j k r =
      fun a =>
        values 0 a +
          Finset.sum (Finset.range gridEdges) (fun l =>
            (values (l + 1) a - values l a) * edgeProgress r l) := by
  classical
  funext a
  rw [batchedPolicyActionInterpolate_eq_batch_sum]
  rw [show values 0 a = 0 by rw [hzero]; rfl, zero_add]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro l hl
  have hcoord := congrFun (hstep l) a
  simp only [Pi.sub_apply] at hcoord
  rw [hcoord]
  have hsum :
      ((states l).map
        (fun y => N.actionDirac (U K y j k))).sum =
        Finset.univ.sum (fun q : Fin (states l).length =>
          N.actionDirac (U K ((states l).get q) j k)) := by
    rw [<- List.sum_ofFn]
    change
      ((states l).map
          (fun y => N.actionDirac (U K y j k))).sum =
        (List.ofFn
          ((fun y => N.actionDirac (U K y j k)) ∘
            (states l).get)).sum
    rw [<- List.map_ofFn, List.ofFn_get]
  rw [hsum, Finset.sum_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- User-facing batch form of the scheduling bridge. Each list should be
the sequential pre-action states for `(j,k)` in one coarse-grid batch. -/
private theorem batchedPolicyActionInterpolate_ratio_mem_epsilon
    {gridEdges : Nat} (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin gridEdges -> List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    {s t : Real} (hst : s <= t)
    (hpos :
      0 < batchedInputInterpolate states t -
        batchedInputInterpolate states s)
    (hK : epsilon⁻¹ <= (K : Real))
    (hnear : forall l y, y ∈ states l ->
      0 < edgeProgress t l.val - edgeProgress s l.val ->
        IsNearNormalizedState y x epsilon) :
    (fun a =>
      (batchedPolicyActionInterpolate N U K states j k t a -
          batchedPolicyActionInterpolate N U K states j k s a) /
        (batchedInputInterpolate states t -
          batchedInputInterpolate states s)) ∈
      N.tri_fluidPolicyEpsilonCorrespondence U j k x epsilon := by
  classical
  apply N.finiteActionInterpolate_ratio_mem_epsilon
      U j k x epsilon
      (Finset.univ : Finset (BatchedOccurrence states))
      (fun q => q.1.val) (fun _ => K)
      (fun q => (states q.1).get q.2)
  · exact hst
  · exact hpos
  · intro r hr hused
    simpa using hK
  · intro r hr hused
    exact hnear r.1 ((states r.1).get r.2)
      (List.get_mem (states r.1) r.2) hused

/-- Time-rescaled and population-scaled batch input path, in the same
normalization as the coarse-grid paths. -/
private noncomputable def scaledBatchedInputInterpolate
    {Z : Type*} (gridK : PNat)
    (states : Fin (gridK : Nat) -> List Z) (T t : Real) : Real :=
  batchedInputInterpolate states
      (((gridK : Nat) : Real) * t / T) /
    (gridK : Nat)

/-- Time-rescaled and population-scaled all-action path. -/
private noncomputable def scaledBatchedPolicyActionInterpolate
    (gridK : PNat) (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin (gridK : Nat) ->
      List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (T t : Real) : ActionVector Buffer :=
  fun a =>
    batchedPolicyActionInterpolate N U K states j k
        (((gridK : Nat) : Real) * t / T) a /
      (gridK : Nat)

/-- Scaled finite-difference scheduling bridge for the current coarse grid. -/
private theorem tri_finiteDifferenceRatio_scaledBatched_mem_epsilon
    (gridK : PNat) (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin (gridK : Nat) ->
      List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    (T t h : Real) (hT : 0 < T) (hh : 0 < h)
    (hpos :
      0 <
        scaledBatchedInputInterpolate gridK states T (t + h) -
          scaledBatchedInputInterpolate gridK states T t)
    (hK : epsilon⁻¹ <= (K : Real))
    (hnear : forall l y, y ∈ states l ->
      0 <
        edgeProgress (((gridK : Nat) : Real) * (t + h) / T) l.val -
          edgeProgress (((gridK : Nat) : Real) * t / T) l.val ->
        IsNearNormalizedState y x epsilon) :
    N.tri_finiteDifferenceRatio
        (scaledBatchedInputInterpolate gridK states T)
        (scaledBatchedPolicyActionInterpolate
          N gridK U K states j k T)
        t h ∈
      N.tri_fluidPolicyEpsilonCorrespondence U j k x epsilon := by
  let r0 : Real := ((gridK : Nat) : Real) * t / T
  let r1 : Real := ((gridK : Nat) : Real) * (t + h) / T
  have hgrid : (0 : Real) < (gridK : Nat) := by positivity
  have hr : r0 <= r1 := by
    dsimp [r0, r1]
    apply (div_le_div_iff_of_pos_right hT).2
    exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hgrid)
  have hscaled :
      scaledBatchedInputInterpolate gridK states T (t + h) -
          scaledBatchedInputInterpolate gridK states T t =
        (batchedInputInterpolate states r1 -
          batchedInputInterpolate states r0) / (gridK : Nat) := by
    dsimp [scaledBatchedInputInterpolate, r0, r1]
    ring
  have hraw :
      0 < batchedInputInterpolate states r1 -
        batchedInputInterpolate states r0 := by
    rw [hscaled] at hpos
    have hmul := mul_pos hpos hgrid
    rw [div_mul_cancel₀ _ (ne_of_gt hgrid)] at hmul
    exact hmul
  have hm :=
    N.batchedPolicyActionInterpolate_ratio_mem_epsilon
      U K states j k x epsilon hr hraw hK hnear
  convert hm using 1
  funext a
  unfold tri_finiteDifferenceRatio
  dsimp [scaledBatchedInputInterpolate,
    scaledBatchedPolicyActionInterpolate, r0, r1]
  field_simp


/-- Sequential pre-action states at occurrences of one fixed token type. -/
private def fluidEmpiricalPreActionStates {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    JobState Buffer K ->
      List (TokenType (Buffer := Buffer) (Server := Server)) ->
      Server -> Buffer -> List (JobState Buffer K)
  | _, [], _, _ => []
  | z, jk :: rest, j, k =>
      if jk = (j, k) then
        z :: fluidEmpiricalPreActionStates U (N.queueStep U z jk) rest j k
      else
        fluidEmpiricalPreActionStates U (N.queueStep U z jk) rest j k

/-- Counts every action, including `none`, at occurrences of `(j,k)`. -/
private def fluidEmpiricalActionCount {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    JobState Buffer K ->
      List (TokenType (Buffer := Buffer) (Server := Server)) ->
      Server -> Buffer -> ActionVector Buffer
  | _, [], _, _ => 0
  | z, jk :: rest, j, k =>
      (if jk = (j, k) then N.actionDirac (U z jk.1 jk.2) else 0) +
        fluidEmpiricalActionCount U (N.queueStep U z jk) rest j k

/-- Natural-valued count of wasted occurrences of one fixed token type. -/
private def fluidEmpiricalMatchingWasteCount {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    JobState Buffer K ->
      List (TokenType (Buffer := Buffer) (Server := Server)) ->
      Server -> Buffer -> Nat
  | _, [], _, _ => 0
  | z, jk :: rest, j, k =>
      (if U z jk.1 jk.2 = none /\ jk = (j, k) then 1 else 0) +
        fluidEmpiricalMatchingWasteCount U
          (N.queueStep U z jk) rest j k

/-- The matching pre-action state list has one entry per matching token. -/
private theorem fluidEmpiricalPreActionStates_length {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) :
    (N.fluidEmpiricalPreActionStates U z tokens j k).length =
      tokens.count (j, k) := by
  induction tokens generalizing z with
  | nil =>
      simp [fluidEmpiricalPreActionStates]
  | cons jk rest ih =>
      by_cases hmatch : jk = (j, k)
      · subst jk
        simp [fluidEmpiricalPreActionStates, ih]
      · simp [fluidEmpiricalPreActionStates, hmatch, ih]

/-- The recursive count is the sum of Dirac actions at matching
sequential pre-action states. -/
private theorem fluidEmpiricalActionCount_eq_preActionState_sum {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) :
    N.fluidEmpiricalActionCount U z tokens j k =
      ((N.fluidEmpiricalPreActionStates U z tokens j k).map
        (fun y => N.actionDirac (U y j k))).sum := by
  induction tokens generalizing z with
  | nil =>
      simp [fluidEmpiricalActionCount, fluidEmpiricalPreActionStates]
  | cons jk rest ih =>
      by_cases hmatch : jk = (j, k)
      · subst jk
        simp [fluidEmpiricalActionCount, fluidEmpiricalPreActionStates, ih]
      · simp [fluidEmpiricalActionCount, fluidEmpiricalPreActionStates,
          hmatch, ih]

/-- Every successful-action coordinate is the existing allocation count. -/
private theorem fluidEmpiricalActionCount_some_eq_runAllocationCount {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer) :
    N.fluidEmpiricalActionCount U z tokens j k (some i) =
      (N.runAllocationCount U z tokens i j k : Real) := by
  induction tokens generalizing z with
  | nil =>
      simp [fluidEmpiricalActionCount, runAllocationCount]
  | cons jk rest ih =>
      by_cases hmatch : jk = (j, k)
      · subst jk
        by_cases haction : U z j k = some i
        · simp [fluidEmpiricalActionCount, runAllocationCount,
            actionDirac, haction, ih]
        · have haction' : Not (some i = U z j k) :=
            fun h => haction h.symm
          simp [fluidEmpiricalActionCount, runAllocationCount,
            actionDirac, haction, haction', ih]
      · have halloc :
          Not (U z jk.1 jk.2 = some i /\ jk.1 = j /\ jk.2 = k) := by
          rintro ⟨_, hj, hk⟩
          exact hmatch (Prod.ext hj hk)
        simp [fluidEmpiricalActionCount, runAllocationCount,
          hmatch, halloc, ih]

/-- The `none` coordinate is exactly the matching-token waste count. -/
private theorem fluidEmpiricalActionCount_none_eq_matchingWasteCount {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) :
    N.fluidEmpiricalActionCount U z tokens j k none =
      (N.fluidEmpiricalMatchingWasteCount U z tokens j k : Real) := by
  induction tokens generalizing z with
  | nil =>
      simp [fluidEmpiricalActionCount, fluidEmpiricalMatchingWasteCount]
  | cons jk rest ih =>
      by_cases hmatch : jk = (j, k)
      · subst jk
        by_cases haction : U z j k = none
        · simp [fluidEmpiricalActionCount,
            fluidEmpiricalMatchingWasteCount, actionDirac, haction, ih]
        · have haction' : Not (none = U z j k) :=
            fun h => haction h.symm
          simp [fluidEmpiricalActionCount,
            fluidEmpiricalMatchingWasteCount, actionDirac, haction,
            haction', ih]
      · simp [fluidEmpiricalActionCount,
          fluidEmpiricalMatchingWasteCount, hmatch, ih]

/-- Summing all action coordinates counts all matching tokens, including
wasted ones. -/
private theorem fluidEmpiricalActionCount_sum_eq_count {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) :
    Finset.univ.sum (N.fluidEmpiricalActionCount U z tokens j k) =
      (tokens.count (j, k) : Real) := by
  rw [N.fluidEmpiricalActionCount_eq_preActionState_sum]
  have hsum (states : List (JobState Buffer K)) :
      Finset.univ.sum
          ((states.map (fun y => N.actionDirac (U y j k))).sum) =
        (states.length : Real) := by
    induction states with
    | nil =>
        simp
    | cons y ys ih =>
        simp only [List.map_cons, List.sum_cons, Pi.add_apply,
          Finset.sum_add_distrib]
        rw [(N.actionDirac_isDistribution (U y j k)).2, ih]
        norm_num
        ring
  rw [hsum]
  exact_mod_cast
    N.fluidEmpiricalPreActionStates_length U z tokens j k

/-- Every coordinate of the all-action count is nonnegative. -/
private theorem fluidEmpiricalActionCount_nonneg {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) (a : Option Buffer) :
    0 <= N.fluidEmpiricalActionCount U z tokens j k a := by
  rw [N.fluidEmpiricalActionCount_eq_preActionState_sum]
  induction
    (N.fluidEmpiricalPreActionStates U z tokens j k) with
  | nil =>
      simp
  | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons, Pi.add_apply]
      exact add_nonneg
        ((N.actionDirac_isDistribution (U y j k)).1 a) ih

/-- Uniform empirical action vector over occurrences of `(j,k)`. -/
private def fluidEmpiricalActionAverage {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) : ActionVector Buffer :=
  (tokens.count (j, k) : Real)⁻¹ •
    N.fluidEmpiricalActionCount U z tokens j k

/-- The empirical vector is the uniform average of the matching
pre-action-state Dirac vectors. -/
private theorem fluidEmpiricalActionAverage_eq_preActionState_average {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) :
    N.fluidEmpiricalActionAverage U z tokens j k =
      (tokens.count (j, k) : Real)⁻¹ •
        ((N.fluidEmpiricalPreActionStates U z tokens j k).map
          (fun y => N.actionDirac (U y j k))).sum := by
  rw [fluidEmpiricalActionAverage,
    N.fluidEmpiricalActionCount_eq_preActionState_sum]

/-- Successful coordinates of the empirical vector are normalized
`runAllocationCount` coordinates. -/
private theorem fluidEmpiricalActionAverage_some_eq_runAllocationCount_div {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (i : Buffer) (j : Server) (k : Buffer) :
    N.fluidEmpiricalActionAverage U z tokens j k (some i) =
      (N.runAllocationCount U z tokens i j k : Real) /
        tokens.count (j, k) := by
  rw [fluidEmpiricalActionAverage, Pi.smul_apply, smul_eq_mul,
    N.fluidEmpiricalActionCount_some_eq_runAllocationCount]
  rw [div_eq_mul_inv, mul_comm]

/-- The empirical vector's `none` coordinate is the normalized matching
waste count. -/
private theorem fluidEmpiricalActionAverage_none_eq_matchingWasteCount_div {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) :
    N.fluidEmpiricalActionAverage U z tokens j k none =
      (N.fluidEmpiricalMatchingWasteCount U z tokens j k : Real) /
        tokens.count (j, k) := by
  rw [fluidEmpiricalActionAverage, Pi.smul_apply, smul_eq_mul,
    N.fluidEmpiricalActionCount_none_eq_matchingWasteCount]
  rw [div_eq_mul_inv, mul_comm]

/-- With at least one matching token, the empirical vector sums to one. -/
private theorem fluidEmpiricalActionAverage_sum_eq_one {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer)
    (hcount : 0 < tokens.count (j, k)) :
    Finset.univ.sum (N.fluidEmpiricalActionAverage U z tokens j k) = 1 := by
  simp only [fluidEmpiricalActionAverage, Pi.smul_apply, smul_eq_mul]
  rw [<- Finset.mul_sum, N.fluidEmpiricalActionCount_sum_eq_count]
  have hne : Ne (tokens.count (j, k) : Real) 0 := by
    exact_mod_cast (Nat.ne_of_gt hcount)
  exact inv_mul_cancel₀ hne

/-- A nonempty type-restricted empirical action vector is a probability
distribution on `Option Buffer`. -/
private theorem fluidEmpiricalActionAverage_isActionDistribution {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer)
    (hcount : 0 < tokens.count (j, k)) :
    IsActionDistribution
      (N.fluidEmpiricalActionAverage U z tokens j k) := by
  constructor
  · intro a
    rw [fluidEmpiricalActionAverage, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (N.fluidEmpiricalActionCount_nonneg U z tokens j k a)
  · exact N.fluidEmpiricalActionAverage_sum_eq_one
      U z tokens j k hcount

/-- Fixed-epsilon closed convex set from the fluid policy correspondence. -/
private def fluidEmpiricalEpsilonCorrespondence
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (epsilon : Real) : Set (ActionVector Buffer) :=
  closure (convexHull Real
    {q | exists K : PNat, exists z : JobState Buffer (K : Nat),
      epsilon⁻¹ <= (K : Real) /\
      IsNearNormalizedState z x epsilon /\
      q = N.actionDirac (U K z j k)})

/-- A nonempty empirical action vector from uniformly epsilon-near
pre-action states belongs to the fixed-epsilon fluid policy set. -/
private theorem fluidEmpiricalActionAverage_mem_epsilonCorrespondence
    (U : N.DeterministicPolicySequence)
    (K : PNat) (z : JobState Buffer (K : Nat))
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) (x : Buffer -> Real) (epsilon : Real)
    (hcount : 0 < tokens.count (j, k))
    (hK : epsilon⁻¹ <= (K : Real))
    (hnear : forall y,
      y ∈ N.fluidEmpiricalPreActionStates (U K) z tokens j k ->
        IsNearNormalizedState y x epsilon) :
    N.fluidEmpiricalActionAverage (U K) z tokens j k ∈
      N.fluidEmpiricalEpsilonCorrespondence U j k x epsilon := by
  let states :=
    N.fluidEmpiricalPreActionStates (U K) z tokens j k
  have hstates_length : 0 < states.length := by
    rw [N.fluidEmpiricalPreActionStates_length (U K) z tokens j k]
    exact hcount
  have hlength_ne : Ne (states.length : Real) 0 := by
    exact_mod_cast (Nat.ne_of_gt hstates_length)
  apply subset_closure
  rw [fluidEmpiricalActionAverage,
    N.fluidEmpiricalActionCount_eq_preActionState_sum]
  change
    (tokens.count (j, k) : Real)⁻¹ •
        (states.map (fun y => N.actionDirac (U K y j k))).sum ∈
      convexHull Real
        {q | exists L : PNat, exists y : JobState Buffer (L : Nat),
          epsilon⁻¹ <= (L : Real) /\
          IsNearNormalizedState y x epsilon /\
          q = N.actionDirac (U L y j k)}
  rw [<- N.fluidEmpiricalPreActionStates_length (U K) z tokens j k]
  have hsum :
      (states.map (fun y => N.actionDirac (U K y j k))).sum =
        Finset.univ.sum
          (fun r : Fin states.length =>
            N.actionDirac (U K (states.get r) j k)) := by
    rw [<- List.sum_ofFn]
    change
      (states.map (fun y => N.actionDirac (U K y j k))).sum =
        (List.ofFn
          ((fun y => N.actionDirac (U K y j k)) ∘ states.get)).sum
    rw [<- List.map_ofFn, List.ofFn_get]
  rw [hsum]
  change
    (states.length : Real)⁻¹ •
        Finset.univ.sum
          (fun r : Fin states.length =>
            N.actionDirac (U K (states.get r) j k)) ∈
      convexHull Real
        {q | exists L : PNat, exists y : JobState Buffer (L : Nat),
          epsilon⁻¹ <= (L : Real) /\
          IsNearNormalizedState y x epsilon /\
          q = N.actionDirac (U L y j k)}
  rw [Finset.smul_sum]
  apply (convex_convexHull Real _).sum_mem
  · intro r hr
    positivity
  · simp
    exact mul_inv_cancel₀ hlength_ne
  · intro r hr
    apply subset_convexHull Real
    refine ⟨K, states.get r, hK, ?_, rfl⟩
    apply hnear
    exact List.get_mem states r


variable (initial : forall K : PNat, JobState Buffer (K : Nat))

private theorem triangular_pnat_val_tendsto_atTop
    {K : Nat -> PNat} (hK : StrictMono K) :
    Tendsto (fun r => (K r : Nat)) atTop atTop :=
  (show StrictMono (fun r => (K r : Nat)) from fun _ _ h => hK h)
    |>.tendsto_atTop

private noncomputable def calendarScaledQueueStateFromInitial
    (U : N.DeterministicPolicySequence) (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (t : Real) (i : Buffer) : Real :=
  N.totalCalendarScaledQueueStateFrom U K (initial K) (omega K) t i

private noncomputable def calendarScaledAllocationFromInitial
    (U : N.DeterministicPolicySequence) (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (t : Real) (i : Buffer) (j : Server) (k : Buffer) : Real :=
  N.totalCalendarScaledAllocationFrom initial U K (omega K) t i j k

private theorem totalRawCalendarEvents_token_count
    (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) :
    ((N.totalRawCalendarEvents K (omega K) t).map fun event => event.1).count
        (j, k) =
      N.totalCalendarTokenCount K (omega K) t j k := by
  classical
  simp only [totalRawCalendarEvents, rawCalendarEvents,
    List.map_flatMap, List.map_map]
  simp [Function.comp_def]
  have hinner (a : Server) :
      List.count (j, k)
          (Finset.univ.toList.flatMap fun b =>
            List.replicate (N.totalCalendarTokenCount K (omega K) t a b)
              (a, b)) =
        if a = j then N.totalCalendarTokenCount K (omega K) t a k else 0 := by
    rw [List.count_flatMap]
    by_cases ha : a = j
    · subst a
      simp [List.count_replicate]
    · simp [List.count_replicate, ha]
  rw [List.count_flatMap]
  change (Finset.univ.toList.map (fun a => List.count (j, k)
    (Finset.univ.toList.flatMap fun b =>
      List.replicate (N.totalCalendarTokenCount K (omega K) t a b)
        (a, b)))).sum =
      N.totalCalendarTokenCount K (omega K) t j k
  simp_rw [hinner]
  simp

private theorem totalCalendarTokenPrefix_count
    (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (t : Real) (j : Server) (k : Buffer) :
    (N.totalCalendarTokenPrefix K (omega K) t).count (j, k) =
      N.totalCalendarTokenCount K (omega K) t j k := by
  classical
  unfold totalCalendarTokenPrefix
  calc
    ((N.totalChronologicalCalendarEvents K (omega K) t).map
        fun event => event.1).count (j, k) =
        ((N.totalRawCalendarEvents K (omega K) t).map
          fun event => event.1).count (j, k) :=
      ((N.totalChronologicalCalendarEvents_perm_raw K (omega K) t).map
        fun event => event.1).count_eq _
    _ = N.totalCalendarTokenCount K (omega K) t j k :=
      totalRawCalendarEvents_token_count N K omega t j k

private theorem calendarScaledInput_eq_prefix_count
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (t : Real)
    (j : Server) (k : Buffer) :
    N.totalCalendarScaledInput K (omega K) t j k =
      ((N.totalCalendarTokenPrefix K (omega K) t).count (j, k) : Real) /
        (K : Nat) := by
  unfold totalCalendarScaledInput calendarScaledInput
  rw [totalCalendarTokenPrefix_count N]
  rfl

private theorem totalCalendarTokenPrefix_zero
    (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) :
    N.totalCalendarTokenPrefix K (omega K) 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro jk hjk
  have hpositive :
      0 < (N.totalCalendarTokenPrefix K (omega K) 0).count jk :=
    List.count_pos_iff.2 hjk
  rcases jk with ⟨j, k⟩
  rw [totalCalendarTokenPrefix_count N] at hpositive
  simpa [totalCalendarTokenCount] using hpositive

private def calendarGridTime (T : Real) (K : PNat) (l : Nat) : Real :=
  T * (l : Real) / (K : Nat)

private theorem calendarGridTime_zero (T : Real) (K : PNat) :
    calendarGridTime T K 0 = 0 := by
  simp [calendarGridTime]

private theorem calendarGridTime_succ_sub
    (T : Real) (K : PNat) (l : Nat) :
    calendarGridTime T K (l + 1) - calendarGridTime T K l =
      T / (K : Nat) := by
  unfold calendarGridTime
  push_cast
  ring

private theorem calendarGridTime_mem_Icc
    {T : Real} (hT : 0 < T) (K : PNat) {l : Nat}
    (hl : l <= (K : Nat)) :
    calendarGridTime T K l ∈ Icc (0 : Real) T := by
  have hK : (0 : Real) < (K : Nat) := by positivity
  constructor
  · exact div_nonneg
      (mul_nonneg hT.le (Nat.cast_nonneg l)) hK.le
  · apply (div_le_iff₀ hK).2
    have hl' : (l : Real) <= (K : Nat) := by exact_mod_cast hl
    nlinarith

private theorem calendarGridTime_mono
    {T : Real} (hT : 0 < T) (K : PNat) {l m : Nat}
    (hlm : l <= m) :
    calendarGridTime T K l <= calendarGridTime T K m := by
  unfold calendarGridTime
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlm) hT.le

private def calendarGridPrefix
    (T : Real) (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  N.totalCalendarTokenPrefix K (omega K) (calendarGridTime T K l)

private def calendarGridBatch
  (T : Real) (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  (N.calendarGridPrefix T K omega (l + 1)).drop
    (N.calendarGridPrefix T K omega l).length

private theorem calendarGridPrefix_succ
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    N.calendarGridPrefix T K omega (l + 1) =
      N.calendarGridPrefix T K omega l ++
        N.calendarGridBatch T K omega l := by
  unfold calendarGridPrefix calendarGridBatch
  obtain ⟨suffix, hsuffix⟩ :=
    N.totalCalendarTokenPrefix_append K (omega K)
      (calendarGridTime_mono hT K (Nat.le_succ l))
  change
    N.totalCalendarTokenPrefix K (omega K) (calendarGridTime T K (l + 1)) =
      N.totalCalendarTokenPrefix K (omega K) (calendarGridTime T K l) ++
        (N.totalCalendarTokenPrefix K (omega K)
          (calendarGridTime T K (l + 1))).drop
            (N.totalCalendarTokenPrefix K (omega K)
              (calendarGridTime T K l)).length
  rw [hsuffix, List.drop_left]

private theorem calendarGridBatch_length
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    (N.calendarGridBatch T K omega l).length =
      (N.calendarGridPrefix T K omega (l + 1)).length -
        (N.calendarGridPrefix T K omega l).length := by
  unfold calendarGridBatch
  rw [List.length_drop]

private theorem calendarGridBatch_count
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (j : Server) (k : Buffer) :
    (N.calendarGridBatch T K omega l).count (j, k) =
      (N.calendarGridPrefix T K omega (l + 1)).count (j, k) -
        (N.calendarGridPrefix T K omega l).count (j, k) := by
  have hp := calendarGridPrefix_succ N hT K omega l
  rw [hp, List.count_append, Nat.add_sub_cancel_left]

private def calendarGridState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    JobState Buffer (K : Nat) :=
  N.runTokens (U K) (initial K)
    (N.calendarGridPrefix T K omega l)

private def calendarGridAllocation
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) : Nat :=
  N.runAllocationCount (U K) (initial K)
    (N.calendarGridPrefix T K omega l) i j k

private def calendarGridInput
    (T : Real) (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (j : Server) (k : Buffer) : Nat :=
  (N.calendarGridPrefix T K omega l).count (j, k)

private noncomputable def calendarPolygonalState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) : FluidStatePath Buffer :=
  fun t i =>
    fi_polygonalInterpolate K
      (fun l => (N.calendarGridState initial T U K omega l i : Real) / (K : Nat))
      t T

private noncomputable def calendarPolygonalAllocation
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) :
    FluidAllocationPath Buffer Server :=
  fun t i j k =>
    fi_polygonalInterpolate K
      (fun l =>
        (N.calendarGridAllocation initial T U K omega l i j k : Real) / (K : Nat))
      t T

private noncomputable def calendarPolygonalInput
    (T : Real) (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) :
    MatrixPath Server Buffer :=
  fun t j k =>
    fi_polygonalInterpolate K
      (fun l => (N.calendarGridInput T K omega l j k : Real) / (K : Nat))
      t T

private theorem continuous_calendarPolygonalState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    Continuous (fun t => N.calendarPolygonalState initial T U K omega t i) := by
  unfold calendarPolygonalState fi_polygonalInterpolate fi_hatWeight
  fun_prop

private theorem continuous_calendarPolygonalAllocation
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (i : Buffer) (j : Server) (k : Buffer) :
    Continuous
      (fun t => N.calendarPolygonalAllocation initial T U K omega t i j k) := by
  unfold calendarPolygonalAllocation fi_polygonalInterpolate fi_hatWeight
  fun_prop

private theorem continuous_calendarPolygonalInput
    (T : Real) (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) :
    Continuous (fun t => N.calendarPolygonalInput T K omega t j k) := by
  unfold calendarPolygonalInput fi_polygonalInterpolate fi_hatWeight
  fun_prop

private theorem calendarGridState_succ
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    N.calendarGridState initial T U K omega (l + 1) =
      N.runTokens (U K) (N.calendarGridState initial T U K omega l)
        (N.calendarGridBatch T K omega l) := by
  unfold calendarGridState
  rw [calendarGridPrefix_succ N hT K omega l]
  exact ff_runTokens_append N _ _ _ _

private theorem calendarGridAllocation_succ
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    N.calendarGridAllocation initial T U K omega (l + 1) i j k =
      N.calendarGridAllocation initial T U K omega l i j k +
        N.runAllocationCount (U K)
          (N.calendarGridState initial T U K omega l)
          (N.calendarGridBatch T K omega l) i j k := by
  unfold calendarGridAllocation calendarGridState
  rw [calendarGridPrefix_succ N hT K omega l]
  exact ff_runAllocationCount_append N _ _ _ _ _ _ _

private theorem calendarGridInput_mono
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) {l m : Nat} (hlm : l <= m)
    (j : Server) (k : Buffer) :
    N.calendarGridInput T K omega l j k <=
      N.calendarGridInput T K omega m j k := by
  unfold calendarGridInput calendarGridPrefix
  obtain ⟨suffix, hprefix⟩ :=
    N.totalCalendarTokenPrefix_append K (omega K)
      (calendarGridTime_mono hT K hlm)
  rw [hprefix, List.count_append]
  omega

private theorem calendarGridInput_succ_sub
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) (j : Server) (k : Buffer) :
    N.calendarGridInput T K omega (l + 1) j k -
        N.calendarGridInput T K omega l j k =
      (N.calendarGridBatch T K omega l).count (j, k) := by
  exact (calendarGridBatch_count N hT K omega l j k).symm

private theorem allTokenCounts_sum
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server))) :
    (Finset.univ.sum fun jk : Server × Buffer => tokens.count jk) =
      tokens.length := by
  classical
  induction tokens with
  | nil =>
      simp
  | cons a tokens ih =>
      simp only [List.count_cons, List.length_cons]
      rw [Finset.sum_add_distrib, ih]
      have hone :
          Finset.univ.sum
              (fun jk : Server × Buffer =>
                if a == jk then 1 else 0) = 1 := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro b hb hba
          have hab : Not (a = b) := Ne.symm hba
          simp [hab]
        · simp
      rw [hone]

private theorem calendarGridInput_sum
    (T : Real) (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        N.calendarGridInput T K omega l j k) =
      (N.calendarGridPrefix T K omega l).length := by
  classical
  let tokens := N.calendarGridPrefix T K omega l
  calc
    (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          N.calendarGridInput T K omega l j k) =
        Finset.univ.sum fun jk : Server × Buffer =>
          tokens.count jk := by
      have hprod :
          (Finset.univ : Finset (Server × Buffer)) =
            (Finset.univ : Finset Server).product
              (Finset.univ : Finset Buffer) := by
        ext jk
        simp
      rw [hprod]
      simpa [tokens, calendarGridInput] using
        (Finset.sum_product
          (Finset.univ : Finset Server)
          (Finset.univ : Finset Buffer)
          (fun jk : Server × Buffer => tokens.count jk)).symm
    _ = tokens.length := allTokenCounts_sum (Buffer := Buffer)
      (Server := Server) tokens

private theorem calendarGridBatch_length_eq_input_sum
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    (N.calendarGridBatch T K omega l).length =
      Finset.univ.sum (fun jk : Server × Buffer =>
          N.calendarGridInput T K omega (l + 1) jk.1 jk.2 -
          N.calendarGridInput T K omega l jk.1 jk.2) := by
  classical
  rw [<- allTokenCounts_sum (Buffer := Buffer) (Server := Server)
    (N.calendarGridBatch T K omega l)]
  apply Finset.sum_congr rfl
  intro jk hjk
  exact (calendarGridInput_succ_sub N hT K omega l jk.1 jk.2).symm

private theorem calendarGridState_isFluidState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) :
    IsFluidState (fun i =>
      (N.calendarGridState initial T U K omega l i : Real) / (K : Nat)) := by
  constructor
  · intro i
    positivity
  · rw [<- Finset.sum_div]
    rw [show
      Finset.univ.sum
          (fun i => ((N.calendarGridState initial T U K omega l i : Nat) : Real)) =
        ((K : Nat) : Real) by
      exact_mod_cast (N.calendarGridState initial T U K omega l).total_jobs]
    exact div_self (by positivity)

private theorem calendarGridAllocation_incompatible
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    N.calendarGridAllocation initial T U K omega l i j k = 0 := by
  unfold calendarGridAllocation
  exact ff_runAllocationCount_incompatible N _ _ _ _ _ _ hij

private theorem calendarGridAllocation_le_input
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    N.calendarGridAllocation initial T U K omega l i j k <=
      N.calendarGridInput T K omega l j k := by
  unfold calendarGridAllocation calendarGridInput
  exact ff_runAllocationCount_le_count N _ _ _ _ _ _

private theorem calendarGrid_balance
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat) (i : Buffer) :
    (N.calendarGridState initial T U K omega l i : Real) / (K : Nat) =
      (initial K i : Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          (N.calendarGridAllocation initial T U K omega l q j i : Real) /
            (K : Nat)) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (N.calendarGridAllocation initial T U K omega l i j k : Real) /
            (K : Nat)) := by
  have h := runTokens_runAllocationCount_balance N (U K)
    (initial K) (N.calendarGridPrefix T K omega l) i
  unfold calendarGridState calendarGridAllocation
  have hK : ((K : Nat) : Real) ≠ 0 := by positivity
  push_cast at h
  simp_rw [← Finset.sum_div]
  field_simp [hK]
  linarith

private theorem calendarPolygonalState_in_simplex
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    IsFluidState (N.calendarPolygonalState initial T U K omega t) := by
  exact fi_polygonal_state_simplex K _ hT ht
    (fun l _ => calendarGridState_isFluidState N initial T U K omega l)

private theorem calendarPolygonalAllocation_incompatible
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (t : Real)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    N.calendarPolygonalAllocation initial T U K omega t i j k = 0 := by
  unfold calendarPolygonalAllocation
  apply fi_polygonal_allocation_incompatible
    (e := fun l i j k =>
      (N.calendarGridAllocation initial T U K omega l i j k : Real) / (K : Nat))
  intro l hl
  rw [calendarGridAllocation_incompatible N initial T U K omega l i j k hij]
  simp

private theorem calendarPolygonalState_initial
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (i : Buffer) :
    N.calendarPolygonalState initial T U K omega 0 i =
      (initial K i : Real) / (K : Nat) := by
  rw [calendarPolygonalState, fi_polygonal_initial K _ T hT]
  unfold calendarGridState calendarGridPrefix
  rw [calendarGridTime_zero, totalCalendarTokenPrefix_zero N]
  simp [runTokens]

private theorem calendarPolygonalAllocation_initial
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (i : Buffer) (j : Server) (k : Buffer) :
    N.calendarPolygonalAllocation initial T U K omega 0 i j k = 0 := by
  rw [calendarPolygonalAllocation, fi_polygonal_initial K _ T hT]
  unfold calendarGridAllocation calendarGridPrefix
  rw [calendarGridTime_zero, totalCalendarTokenPrefix_zero N]
  simp [runAllocationCount]

private theorem calendarPolygonal_balance
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) (i : Buffer) :
    N.calendarPolygonalState initial T U K omega t i =
      (initial K i : Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          N.calendarPolygonalAllocation initial T U K omega t q j i) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          N.calendarPolygonalAllocation initial T U K omega t i j k) := by
  unfold calendarPolygonalState calendarPolygonalAllocation
  change
    fi_polygonalStatePath K
        (fun l i =>
          (N.calendarGridState initial T U K omega l i : Real) / (K : Nat))
        T t i =
      (initial K i : Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          fi_polygonalAllocationPath K
            (fun l i j k =>
              (N.calendarGridAllocation initial T U K omega l i j k : Real) /
                (K : Nat))
            T t q j i) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          fi_polygonalAllocationPath K
            (fun l i j k =>
              (N.calendarGridAllocation initial T U K omega l i j k : Real) /
                (K : Nat))
            T t i j k)
  exact fi_polygonal_paths_balance
    (K := K)
    (x := fun l i =>
      (N.calendarGridState initial T U K omega l i : Real) / (K : Nat))
    (e := fun l i j k =>
      (N.calendarGridAllocation initial T U K omega l i j k : Real) / (K : Nat))
    (x0 := fun i => (initial K i : Real) / (K : Nat))
    hT ht (fun l _ i => calendarGrid_balance N initial T U K omega l i) i

private def calendarIntervalBatch
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (s t : Real) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  (N.totalCalendarTokenPrefix K (omega K) t).drop
    (N.totalCalendarTokenPrefix K (omega K) s).length

private theorem calendarTokenPrefix_interval
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t) :
    N.totalCalendarTokenPrefix K (omega K) t =
      N.totalCalendarTokenPrefix K (omega K) s ++
        N.calendarIntervalBatch K omega s t := by
  unfold calendarIntervalBatch
  obtain ⟨suffix, hsuffix⟩ :=
    N.totalCalendarTokenPrefix_append K (omega K) hst
  rw [hsuffix, List.drop_left]

private theorem calendarIntervalBatch_count
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t)
    (j : Server) (k : Buffer) :
    (N.calendarIntervalBatch K omega s t).count (j, k) =
      (N.totalCalendarTokenPrefix K (omega K) t).count (j, k) -
        (N.totalCalendarTokenPrefix K (omega K) s).count (j, k) := by
  rw [calendarTokenPrefix_interval N K omega hst, List.count_append,
    Nat.add_sub_cancel_left]

private theorem calendarIntervalBatch_length
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t) :
    (N.calendarIntervalBatch K omega s t).length =
      (N.totalCalendarTokenPrefix K (omega K) t).length -
        (N.totalCalendarTokenPrefix K (omega K) s).length := by
  unfold calendarIntervalBatch
  rw [List.length_drop]

private theorem calendarScaledInput_mono
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t)
    (j : Server) (k : Buffer) :
    N.totalCalendarScaledInput K (omega K) s j k <=
      N.totalCalendarScaledInput K (omega K) t j k := by
  rw [calendarScaledInput_eq_prefix_count N,
    calendarScaledInput_eq_prefix_count N]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    (show
      (N.totalCalendarTokenPrefix K (omega K) s).count (j, k) <=
        (N.totalCalendarTokenPrefix K (omega K) t).count (j, k) by
      rw [calendarTokenPrefix_interval N K omega hst, List.count_append]
      omega)

private theorem calendarIntervalBatch_scaled_length
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t) :
    ((N.calendarIntervalBatch K omega s t).length : Real) / (K : Nat) =
      Finset.univ.sum (fun jk : Server × Buffer =>
        N.totalCalendarScaledInput K (omega K) t jk.1 jk.2 -
          N.totalCalendarScaledInput K (omega K) s jk.1 jk.2) := by
  rw [show
    (N.calendarIntervalBatch K omega s t).length =
      Finset.univ.sum (fun jk : Server × Buffer =>
        (N.calendarIntervalBatch K omega s t).count jk) by
    exact (allTokenCounts_sum (Buffer := Buffer) (Server := Server)
      (N.calendarIntervalBatch K omega s t)).symm]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro jk hjk
  rw [calendarScaledInput_eq_prefix_count N,
    calendarScaledInput_eq_prefix_count N,
    calendarIntervalBatch_count N K omega hst]
  have hle :
      (N.totalCalendarTokenPrefix K (omega K) s).count jk <=
        (N.totalCalendarTokenPrefix K (omega K) t).count jk := by
    rw [calendarTokenPrefix_interval N K omega hst, List.count_append]
    omega
  push_cast
  rw [Nat.cast_sub hle]
  ring

private theorem calendarScaledQueueStateFromInitial_ordered_dist_le
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t)
    (i : Buffer) :
    dist (N.calendarScaledQueueStateFromInitial initial U K omega s i)
        (N.calendarScaledQueueStateFromInitial initial U K omega t i) <=
      2 * Finset.univ.sum (fun jk : Server × Buffer =>
        (N.totalCalendarScaledInput K (omega K) t jk.1 jk.2 -
          N.totalCalendarScaledInput K (omega K) s jk.1 jk.2)) := by
  have hrun :=
    ff_runTokens_batch_l1_le_two_mul_length N (U K)
      (initial K)
      (N.totalCalendarTokenPrefix K (omega K) s)
      (N.calendarIntervalBatch K omega s t)
  rw [<- calendarTokenPrefix_interval N K omega hst] at hrun
  have hcoord :
      abs (((N.runTokens (U K) (initial K)
          (N.totalCalendarTokenPrefix K (omega K) t) i : Nat) :
            Real) -
        ((N.runTokens (U K) (initial K)
          (N.totalCalendarTokenPrefix K (omega K) s) i : Nat) :
            Real)) <=
        2 * (N.calendarIntervalBatch K omega s t).length := by
    exact (Finset.single_le_sum
      (fun q _ => abs_nonneg
        (((N.runTokens (U K) (initial K)
            (N.totalCalendarTokenPrefix K (omega K) t) q : Nat) :
              Real) -
          ((N.runTokens (U K) (initial K)
            (N.totalCalendarTokenPrefix K (omega K) s) q : Nat) :
              Real)))
      (Finset.mem_univ i)).trans hrun
  unfold calendarScaledQueueStateFromInitial
    totalCalendarScaledQueueStateFrom
  rw [Real.dist_eq]
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [<- sub_div, abs_div, abs_of_pos hK]
  calc
    abs
          (((N.runTokens (U K) (initial K)
              (N.totalCalendarTokenPrefix K (omega K) s) i :
                Nat) : Real) -
            ((N.runTokens (U K) (initial K)
              (N.totalCalendarTokenPrefix K (omega K) t) i :
                Nat) : Real)) /
        (K : Nat) <=
        (2 * (N.calendarIntervalBatch K omega s t).length : Real) /
          (K : Nat) := by
      apply div_le_div_of_nonneg_right _ hK.le
      simpa [abs_sub_comm] using hcoord
    _ = 2 * Finset.univ.sum (fun jk : Server × Buffer =>
          (N.totalCalendarScaledInput K (omega K) t jk.1 jk.2 -
            N.totalCalendarScaledInput K (omega K) s jk.1 jk.2)) := by
      rw [show
        (2 * (N.calendarIntervalBatch K omega s t).length : Real) /
            (K : Nat) =
          2 * (((N.calendarIntervalBatch K omega s t).length : Real) /
            (K : Nat)) by ring]
      rw [calendarIntervalBatch_scaled_length N K omega hst]

private theorem calendarScaledQueueStateFromInitial_dist_le
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (s t : Real) (i : Buffer) :
    dist (N.calendarScaledQueueStateFromInitial initial U K omega s i)
        (N.calendarScaledQueueStateFromInitial initial U K omega t i) <=
      2 * Finset.univ.sum (fun jk : Server × Buffer =>
        dist (N.totalCalendarScaledInput K (omega K) s jk.1 jk.2)
          (N.totalCalendarScaledInput K (omega K) t jk.1 jk.2)) := by
  rcases le_total s t with hst | hts
  · have h := calendarScaledQueueStateFromInitial_ordered_dist_le N initial U K omega hst i
    convert h using 1
    apply congrArg
    apply Finset.sum_congr rfl
    intro jk hjk
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (calendarScaledInput_mono N K omega hst jk.1 jk.2))]
  · rw [dist_comm]
    have h := calendarScaledQueueStateFromInitial_ordered_dist_le N initial U K omega hts i
    convert h using 1
    apply congrArg
    apply Finset.sum_congr rfl
    intro jk hjk
    rw [Real.dist_eq, abs_of_nonneg
      (sub_nonneg.mpr (calendarScaledInput_mono N K omega hts jk.1 jk.2))]

private theorem calendarScaledAllocationFromInitial_ordered_increment
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) {s t : Real} (hst : s <= t)
    (i : Buffer) (j : Server) (k : Buffer) :
    0 <= N.calendarScaledAllocationFromInitial initial U K omega t i j k -
        N.calendarScaledAllocationFromInitial initial U K omega s i j k /\
      N.calendarScaledAllocationFromInitial initial U K omega t i j k -
          N.calendarScaledAllocationFromInitial initial U K omega s i j k <=
        N.totalCalendarScaledInput K (omega K) t j k -
          N.totalCalendarScaledInput K (omega K) s j k := by
  have happend :=
    ff_runAllocationCount_append N (U K) (initial K)
      (N.totalCalendarTokenPrefix K (omega K) s)
      (N.calendarIntervalBatch K omega s t) i j k
  rw [<- calendarTokenPrefix_interval N K omega hst] at happend
  have hle :=
    ff_runAllocationCount_le_count N (U K)
      (N.runTokens (U K) (initial K)
        (N.totalCalendarTokenPrefix K (omega K) s))
      (N.calendarIntervalBatch K omega s t) i j k
  unfold calendarScaledAllocationFromInitial
    totalCalendarScaledAllocationFrom
  have hK : (0 : Real) < (K : Nat) := by positivity
  constructor
  · apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ hK.le
    exact_mod_cast (show
      N.runAllocationCount (U K) (initial K)
          (N.totalCalendarTokenPrefix K (omega K) s) i j k <=
        N.runAllocationCount (U K) (initial K)
          (N.totalCalendarTokenPrefix K (omega K) t) i j k by
      omega)
  · rw [calendarScaledInput_eq_prefix_count N,
      calendarScaledInput_eq_prefix_count N]
    have halloc_le :
        N.runAllocationCount (U K) (initial K)
            (N.totalCalendarTokenPrefix K (omega K) s) i j k <=
          N.runAllocationCount (U K) (initial K)
            (N.totalCalendarTokenPrefix K (omega K) t) i j k := by
      omega
    have hcount_le :
        (N.totalCalendarTokenPrefix K (omega K) s).count (j, k) <=
          (N.totalCalendarTokenPrefix K (omega K) t).count (j, k) := by
      rw [calendarTokenPrefix_interval N K omega hst, List.count_append]
      omega
    have hnat :
        N.runAllocationCount (U K) (initial K)
              (N.totalCalendarTokenPrefix K (omega K) t) i j k -
            N.runAllocationCount (U K) (initial K)
              (N.totalCalendarTokenPrefix K (omega K) s) i j k <=
          (N.totalCalendarTokenPrefix K (omega K) t).count (j, k) -
            (N.totalCalendarTokenPrefix K (omega K) s).count
              (j, k) := by
      rw [calendarIntervalBatch_count N K omega hst] at hle
      omega
    rw [<- sub_div, <- sub_div]
    apply div_le_div_of_nonneg_right _ hK.le
    rw [← Nat.cast_sub halloc_le, ← Nat.cast_sub hcount_le]
    exact_mod_cast hnat

private theorem calendarScaledAllocationFromInitial_dist_le
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (s t : Real)
    (i : Buffer) (j : Server) (k : Buffer) :
    dist (N.calendarScaledAllocationFromInitial initial U K omega s i j k)
        (N.calendarScaledAllocationFromInitial initial U K omega t i j k) <=
      dist (N.totalCalendarScaledInput K (omega K) s j k)
        (N.totalCalendarScaledInput K (omega K) t j k) := by
  rcases le_total s t with hst | hts
  · have h := calendarScaledAllocationFromInitial_ordered_increment N initial U K omega hst i j k
    rw [Real.dist_eq, Real.dist_eq]
    rw [abs_sub_comm, abs_of_nonneg h.1]
    rw [abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (calendarScaledInput_mono N K omega hst j k))]
    exact h.2
  · rw [dist_comm, dist_comm
      (N.totalCalendarScaledInput K (omega K) s j k)]
    have h := calendarScaledAllocationFromInitial_ordered_increment N initial U K omega hts i j k
    rw [Real.dist_eq, Real.dist_eq]
    rw [abs_sub_comm, abs_of_nonneg h.1]
    rw [abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (calendarScaledInput_mono N K omega hts j k))]
    exact h.2

private theorem calendarStateLimit_continuousOn
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall i, ContinuousOn (fun t => X t i) (Icc (0 : Real) T) := by
  have hinput := hconverges.1
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  change UniformlyOnIcc T
      (fun r t i => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
      X at hstate
  let Avec : Real -> (Server × Buffer -> Real) :=
    fun t jk => A t jk.1 jk.2
  have hAvec_cont : ContinuousOn Avec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro jk
    simpa [Avec, uIcc_of_le hT.le] using
      (hA jk.1 jk.2).continuousOn
  have hAvec_uc : UniformContinuousOn Avec (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hAvec_cont
  intro i
  apply UniformContinuousOn.continuousOn
  rw [Metric.uniformContinuousOn_iff]
  intro epsilon hepsilon
  let C : Real := (Fintype.card (Server × Buffer) : Real) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let eta : Real := epsilon / (16 * C)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp hAvec_uc eta heta
  obtain ⟨rInput, hrInput⟩ := hinput eta heta
  obtain ⟨rState, hrState⟩ := hstate (epsilon / 8) (by positivity)
  refine ⟨delta, hdelta, fun s hs t ht hst => ?_⟩
  let r := max rInput rState
  have hrI : rInput <= r := le_max_left _ _
  have hrS : rState <= r := le_max_right _ _
  have hsState :
      dist (X s i) (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i) <
        epsilon / 8 := by
    rw [Real.dist_eq, abs_sub_comm]
    exact hrState r hrS s hs i
  have htState :
      dist (N.calendarScaledQueueStateFromInitial initial U (K r) omega t i) (X t i) <
        epsilon / 8 := by
    rw [Real.dist_eq]
    exact hrState r hrS t ht i
  have hAmetric : dist (Avec s) (Avec t) < eta :=
    hdeltaWorks s hs t ht hst
  have hterm (jk : Server × Buffer) :
      dist (N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2)
          (N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2) <
        3 * eta := by
    have hsInput := hrInput r hrI s hs jk
    have htInput := hrInput r hrI t ht jk
    have hcoord :
        dist (Avec s jk) (Avec t jk) <= dist (Avec s) (Avec t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s) (Avec t) <= dist (Avec s) (Avec t)) jk
    rw [Real.dist_eq]
    calc
      abs (N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2) <=
          abs (N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2 -
            A s jk.1 jk.2) +
          abs (A s jk.1 jk.2 - A t jk.1 jk.2) +
          abs (A t jk.1 jk.2 -
            N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2) := by
        calc
          _ <= abs (N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2 -
                A s jk.1 jk.2) +
              abs (A s jk.1 jk.2 -
                N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2) :=
            abs_sub_le _ _ _
          _ <= _ := by
            have htri :=
              abs_sub_le (A s jk.1 jk.2) (A t jk.1 jk.2)
                (N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
            linarith
      _ < eta + eta + eta := by
        have hcoord' :
            abs (A s jk.1 jk.2 - A t jk.1 jk.2) < eta := by
          simpa [Avec, Real.dist_eq] using hcoord.trans_lt hAmetric
        have htInput' :
            abs (A t jk.1 jk.2 -
              N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2) < eta := by
          simpa [abs_sub_comm] using htInput
        gcongr
      _ = 3 * eta := by ring
  have hraw :=
    calendarScaledQueueStateFromInitial_dist_le N initial U (K r) omega s t i
  have hsum :
      Finset.univ.sum (fun jk : Server × Buffer =>
        dist (N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2)
          (N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)) <
        (Fintype.card (Server × Buffer) : Real) * (3 * eta) := by
    calc
      _ < Finset.univ.sum (fun _ : Server × Buffer => 3 * eta) :=
        Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty : (Finset.univ :
            Finset (Server × Buffer)).Nonempty)
          (fun jk _ => hterm jk)
      _ = _ := by simp
  calc
    dist (X s i) (X t i) <=
        dist (X s i) (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i) +
        dist (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i)
          (N.calendarScaledQueueStateFromInitial initial U (K r) omega t i) +
        dist (N.calendarScaledQueueStateFromInitial initial U (K r) omega t i) (X t i) := by
      calc
        _ <= dist (X s i) (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i) +
            dist (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i) (X t i) :=
          dist_triangle _ _ _
        _ <= _ := by
          have htri :=
            dist_triangle
              (N.calendarScaledQueueStateFromInitial initial U (K r) omega s i)
              (N.calendarScaledQueueStateFromInitial initial U (K r) omega t i) (X t i)
          linarith
    _ < epsilon / 8 +
        2 * ((Fintype.card (Server × Buffer) : Real) * (3 * eta)) +
        epsilon / 8 := by
      gcongr
      exact hraw.trans_lt (mul_lt_mul_of_pos_left hsum (by positivity))
    _ < epsilon := by
      dsimp [eta, C]
      have hcard : 0 <= (Fintype.card (Server × Buffer) : Real) := by
        positivity
      have hcardC :
          (Fintype.card (Server × Buffer) : Real) <
            (Fintype.card (Server × Buffer) : Real) + 1 := by linarith
      have hratio :
          (Fintype.card (Server × Buffer) : Real) /
              ((Fintype.card (Server × Buffer) : Real) + 1) < 1 := by
        exact (div_lt_one (by linarith)).2 hcardC
      field_simp
      nlinarith

private theorem calendarGridTime_eq_ffGridTime
    (T : Real) (K : PNat) {l : Nat} (hl : l <= (K : Nat)) :
    calendarGridTime T K l = ff_gridTime T K l := by
  simp [calendarGridTime, ff_gridTime, min_eq_left hl]

private theorem fi_polygonalInterpolate_error_of_nodes
    {T : Real} (hT : 0 < T) (K : PNat)
    (values : Nat -> Real) (g : Real -> Real)
    (delta eta : Real)
    (hnode : forall l, l <= (K : Nat) ->
      abs (values l - g (calendarGridTime T K l)) <= delta)
    (hosc : forall s, s ∈ Icc (0 : Real) T ->
      forall t, t ∈ Icc (0 : Real) T ->
        abs (s - t) <= T / (K : Nat) ->
        abs (g s - g t) <= eta)
    (t : Real) (ht : t ∈ Icc (0 : Real) T) :
    abs (fi_polygonalInterpolate K values t T - g t) <= delta + eta := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) ht.1) hT.le
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hsum :
      Finset.sum (Finset.range ((K : Nat) + 1)) (fi_hatWeight r) = 1 :=
    fi_sum_hatWeight_eq_one K hr0 hrK
  have hterm (l : Nat) (hl : l ∈ Finset.range ((K : Nat) + 1)) :
      abs (fi_hatWeight r l * (values l - g t)) <=
        fi_hatWeight r l * (delta + eta) := by
    by_cases hw : fi_hatWeight r l = 0
    · simp [hw]
    · rw [abs_mul, abs_of_nonneg (fi_hatWeight_nonnegative r l)]
      apply mul_le_mul_of_nonneg_left _ (fi_hatWeight_nonnegative r l)
      have hlK : l <= (K : Nat) := by
        have := Finset.mem_range.mp hl
        omega
      have hdistFF :=
        fi_hatWeight_ne_zero_distance K hT (Finset.mem_range.mp hl) hw
      have hdist :
          abs (calendarGridTime T K l - t) <= T / (K : Nat) := by
        rw [calendarGridTime_eq_ffGridTime T K hlK]
        exact hdistFF
      have hosc' := hosc (calendarGridTime T K l)
        (calendarGridTime_mem_Icc hT K hlK) t ht hdist
      calc
        abs (values l - g t) <=
            abs (values l - g (calendarGridTime T K l)) +
              abs (g (calendarGridTime T K l) - g t) := abs_sub_le _ _ _
        _ <= delta + eta := add_le_add (hnode l hlK) hosc'
  rw [show fi_polygonalInterpolate K values t T - g t =
      Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
        fi_hatWeight r l * (values l - g t)) by
    unfold fi_polygonalInterpolate
    dsimp [r]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, <- Finset.sum_mul, hsum, one_mul]]
  calc
    abs (Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
        fi_hatWeight r l * (values l - g t))) <=
        Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
          abs (fi_hatWeight r l * (values l - g t))) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
          fi_hatWeight r l * (delta + eta)) :=
      Finset.sum_le_sum hterm
    _ = delta + eta := by
      rw [<- Finset.sum_mul, hsum, one_mul]

private theorem polygonal_converges_of_nodes
    {T : Real} (hT : 0 < T)
    (K : Nat -> PNat) (hK : StrictMono K)
    (values : Nat -> Nat -> Real) (g : Real -> Real)
    (hg : ContinuousOn g (Icc (0 : Real) T))
    (hnode : forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall l, l <= (K r : Nat) ->
          abs (values r l - g (calendarGridTime T (K r) l)) < epsilon) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall t, t ∈ Icc (0 : Real) T ->
          abs (fi_polygonalInterpolate (K r) (values r) t T - g t) <
            epsilon := by
  have huc : UniformContinuousOn g (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  have hKreal :
      Tendsto (fun r => (((K r : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (triangular_pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun r => T / (((K r : Nat) : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp huc (epsilon / 3) (by positivity)
  obtain ⟨rMesh, hrMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh delta hdelta
  obtain ⟨rNode, hrNode⟩ := hnode (epsilon / 3) (by positivity)
  refine ⟨max rMesh rNode, fun r hr t ht => ?_⟩
  have hrM : rMesh <= r := (le_max_left _ _).trans hr
  have hrN : rNode <= r := (le_max_right _ _).trans hr
  have hmeshSmall : T / (((K r : Nat) : Real)) < delta := by
    have h := hrMesh r hrM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at h
    exact h
  have hosc :
      forall s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T ->
          abs (s - t) <= T / (K r : Nat) ->
          abs (g s - g t) <= epsilon / 3 := by
    intro s hs t ht' hst
    have hdist : dist s t < delta := by
      rw [Real.dist_eq]
      exact hst.trans_lt hmeshSmall
    have h := hdeltaWorks s hs t ht' hdist
    simpa [Real.dist_eq] using le_of_lt h
  have herr :=
    fi_polygonalInterpolate_error_of_nodes hT (K r) (values r) g
      (epsilon / 3) (epsilon / 3)
      (fun l hl => le_of_lt (hrNode r hrN l hl)) hosc t ht
  exact herr.trans_lt (by linarith)

private theorem exists_common_nat_bound
    {I : Type*} [Fintype I]
    {P : I -> Nat -> Prop}
    (h : forall i, exists n0, forall n, n0 <= n -> P i n) :
    exists n0, forall n, n0 <= n -> forall i, P i n := by
  classical
  choose bound hbound using h
  refine ⟨Finset.univ.sup bound, fun n hn i => hbound i n ?_⟩
  exact (Finset.le_sup (Finset.mem_univ i)).trans hn

private theorem calendarPolygonalInput_converges
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall jk : Server × Buffer, forall t, t ∈ Icc (0 : Real) T ->
          dist (N.calendarPolygonalInput T (K r) omega t jk.1 jk.2)
            (A t jk.1 jk.2) < epsilon := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  intro epsilon hepsilon
  have hcoord (jk : Server × Buffer) :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall t, t ∈ Icc (0 : Real) T ->
            abs (N.calendarPolygonalInput T (K r) omega t jk.1 jk.2 -
              A t jk.1 jk.2) < epsilon := by
    apply polygonal_converges_of_nodes hT K hK
      (fun r l =>
        (N.calendarGridInput T (K r) omega l jk.1 jk.2 : Real) /
          (K r : Nat))
      (fun t => A t jk.1 jk.2)
    · simpa [uIcc_of_le hT.le] using (hA jk.1 jk.2).continuousOn
    · intro eta heta
      obtain ⟨r0, hr0⟩ := hinput eta heta
      refine ⟨r0, fun r hr l hl => ?_⟩
      have hnode := hr0 r hr (calendarGridTime T (K r) l)
        (calendarGridTime_mem_Icc hT (K r) hl) jk
      change
        abs (N.totalCalendarScaledInput (K r) (omega (K r))
          (calendarGridTime T (K r) l) jk.1 jk.2 -
            A (calendarGridTime T (K r) l) jk.1 jk.2) < eta at hnode
      rw [calendarScaledInput_eq_prefix_count N] at hnode
      simpa only [calendarGridInput, calendarGridPrefix] using hnode
  obtain ⟨r0, hr0⟩ :=
    exists_common_nat_bound (P := fun jk : Server × Buffer => fun r =>
        forall t, t ∈ Icc (0 : Real) T ->
          abs (N.calendarPolygonalInput T (K r) omega t jk.1 jk.2 -
            A t jk.1 jk.2) < epsilon)
      (fun jk => hcoord jk epsilon hepsilon)
  refine ⟨r0, fun r hr jk t ht => ?_⟩
  rw [Real.dist_eq]
  exact hr0 r hr jk t ht

private theorem calendarPolygonalState_converges
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall i : Buffer, forall t, t ∈ Icc (0 : Real) T ->
          dist (N.calendarPolygonalState initial T U (K r) omega t i)
            (X t i) < epsilon := by
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t i => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
      X at hstate
  have hXcont :=
    calendarStateLimit_continuousOn N initial hT U K omega A X hA hconverges
  intro epsilon hepsilon
  have hcoord (i : Buffer) :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall t, t ∈ Icc (0 : Real) T ->
            abs (N.calendarPolygonalState initial T U (K r) omega t i -
              X t i) < epsilon := by
    apply polygonal_converges_of_nodes hT K hK
      (fun r l =>
        (N.calendarGridState initial T U (K r) omega l i : Real) / (K r : Nat))
      (fun t => X t i) (hXcont i)
    intro eta heta
    obtain ⟨r0, hr0⟩ := hstate eta heta
    refine ⟨r0, fun r hr l hl => ?_⟩
    exact hr0 r hr (calendarGridTime T (K r) l)
      (calendarGridTime_mem_Icc hT (K r) hl) i
  obtain ⟨r0, hr0⟩ :=
    exists_common_nat_bound (P := fun i : Buffer => fun r =>
        forall t, t ∈ Icc (0 : Real) T ->
          abs (N.calendarPolygonalState initial T U (K r) omega t i -
            X t i) < epsilon)
      (fun i => hcoord i epsilon hepsilon)
  refine ⟨r0, fun r hr i t ht => ?_⟩
  rw [Real.dist_eq]
  exact hr0 r hr i t ht

private theorem calendarGridAllocation_step_le
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server)) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    abs
        ((N.calendarGridAllocation initial T U K omega (l + 1) i j k : Real) /
            (K : Nat) -
          (N.calendarGridAllocation initial T U K omega l i j k : Real) /
            (K : Nat)) <=
      Finset.univ.sum (fun jk : Server × Buffer =>
        (N.calendarGridInput T K omega (l + 1) jk.1 jk.2 : Real) /
            (K : Nat) -
          (N.calendarGridInput T K omega l jk.1 jk.2 : Real) /
            (K : Nat)) := by
  have happend :=
    calendarGridAllocation_succ N initial hT U K omega l i j k
  have htail :=
    ff_runAllocationCount_le_count N (U K)
      (N.calendarGridState initial T U K omega l)
      (N.calendarGridBatch T K omega l) i j k
  have hmono :
      N.calendarGridAllocation initial T U K omega l i j k <=
        N.calendarGridAllocation initial T U K omega (l + 1) i j k := by
    omega
  have hdiff :
      N.calendarGridAllocation initial T U K omega (l + 1) i j k -
          N.calendarGridAllocation initial T U K omega l i j k <=
        (N.calendarGridBatch T K omega l).length := by
    have htailLength := htail.trans List.count_le_length
    omega
  have hsum :=
    calendarGridBatch_length_eq_input_sum N hT K omega l
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [abs_of_nonneg (sub_nonneg.mpr
    (div_le_div_of_nonneg_right (by exact_mod_cast hmono) hK.le))]
  rw [<- sub_div]
  simp_rw [<- sub_div]
  rw [<- Finset.sum_div]
  apply div_le_div_of_nonneg_right _ hK.le
  rw [← Nat.cast_sub hmono]
  conv_rhs =>
    enter [2, jk]
    rw [← Nat.cast_sub
      (calendarGridInput_mono N hT K omega (Nat.le_succ l) jk.1 jk.2)]
  rw [← Nat.cast_sum]
  exact_mod_cast hdiff.trans_eq hsum

private theorem calendarPolygonalAllocation_increment_domination
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (i : Buffer) (j : Server) (k : Buffer)
    {s t : Real} (hs : s ∈ Icc (0 : Real) T)
    (ht : t ∈ Icc (0 : Real) T) :
    dist (N.calendarPolygonalAllocation initial T U K omega s i j k)
        (N.calendarPolygonalAllocation initial T U K omega t i j k) <=
      Finset.univ.sum (fun jk : Server × Buffer =>
        dist (N.calendarPolygonalInput T K omega s jk.1 jk.2)
          (N.calendarPolygonalInput T K omega t jk.1 jk.2)) := by
  let values : Nat -> Real := fun l =>
    (N.calendarGridAllocation initial T U K omega l i j k : Real) / (K : Nat)
  let control : Server × Buffer -> Nat -> Real := fun jk l =>
    (N.calendarGridInput T K omega l jk.1 jk.2 : Real) / (K : Nat)
  change
    dist (fi_polygonalInterpolate K values s T)
        (fi_polygonalInterpolate K values t T) <=
      Finset.univ.sum (fun jk : Server × Buffer =>
        dist (fi_polygonalInterpolate K (control jk) s T)
          (fi_polygonalInterpolate K (control jk) t T))
  have hcontrol : forall jk l, l < (K : Nat) ->
      control jk l <= control jk (l + 1) := by
    intro jk l hl
    dsimp [control]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast calendarGridInput_mono N hT K omega
      (Nat.le_succ l) jk.1 jk.2
  have hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun jk =>
          control jk (l + 1) - control jk l) := by
    intro l hl
    exact calendarGridAllocation_step_le N initial hT U K omega l i j k
  exact fi_polygonal_increment_domination K values control hT hs ht
    hcontrol hstep

private theorem calendarGridAllocation_scaled_le_input
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    (N.calendarGridAllocation initial T U K omega l i j k : Real) /
        (K : Nat) <=
      (N.calendarGridInput T K omega l j k : Real) / (K : Nat) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    calendarGridAllocation_le_input N initial T U K omega l i j k

private theorem calendarPolygonalAllocation_abs_le_input
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (i : Buffer) (j : Server) (k : Buffer)
    {t : Real} (ht : t ∈ Icc (0 : Real) T) :
    abs (N.calendarPolygonalAllocation initial T U K omega t i j k) <=
      N.calendarPolygonalInput T K omega t j k := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) ht.1) hT.le
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hnonneg :
      0 <= N.calendarPolygonalAllocation initial T U K omega t i j k := by
    unfold calendarPolygonalAllocation fi_polygonalInterpolate
    apply Finset.sum_nonneg
    intro l hl
    exact mul_nonneg (fi_hatWeight_nonnegative _ _)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [abs_of_nonneg hnonneg]
  unfold calendarPolygonalAllocation calendarPolygonalInput
    fi_polygonalInterpolate
  change
    Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
      fi_hatWeight r l *
        (((N.calendarGridAllocation initial T U K omega l i j k : Nat) : Real) /
          (K : Nat))) <=
      Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
        fi_hatWeight r l *
          ((N.calendarGridInput T K omega l j k : Real) / (K : Nat)))
  apply Finset.sum_le_sum
  intro l hl
  exact mul_le_mul_of_nonneg_left
    (calendarGridAllocation_scaled_le_input N initial T U K omega
      l i j k)
    (fi_hatWeight_nonnegative r l)

private theorem exists_calendarPolygonalAllocation_limit
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X) :
    exists q : Nat -> Nat, StrictMono q /\
      exists E : FluidAllocationPath Buffer Server,
        (forall i j k, ContinuousOn (fun t => E t i j k)
          (Icc (0 : Real) T)) /\
        (forall epsilon, 0 < epsilon ->
          exists r0, forall r, r0 <= r ->
            forall i j k t, t ∈ Icc (0 : Real) T ->
              dist
                (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
                (E t i j k) < epsilon) := by
  let f : Nat -> (Buffer × Server × Buffer) -> Real -> Real :=
    fun r ijk t =>
      N.calendarPolygonalAllocation initial T U (K r) omega t
        ijk.1 ijk.2.1 ijk.2.2
  let g : Nat -> (Server × Buffer) -> Real -> Real :=
    fun r jk t => N.calendarPolygonalInput T (K r) omega t jk.1 jk.2
  let control : (Server × Buffer) -> Real -> Real :=
    fun jk t => A t jk.1 jk.2
  have hf :
      forall r ijk, ContinuousOn (f r ijk) (Icc (0 : Real) T) := by
    intro r ijk
    exact (continuous_calendarPolygonalAllocation N initial T U (K r) omega
      ijk.1 ijk.2.1 ijk.2.2).continuousOn
  have hcontrol :
      forall jk, ContinuousOn (control jk) (Icc (0 : Real) T) := by
    intro jk
    simpa [control, uIcc_of_le hT.le] using
      (hA jk.1 jk.2).continuousOn
  have hgconv :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall jk t, t ∈ Icc (0 : Real) T ->
            dist (g r jk t) (control jk t) < epsilon := by
    intro epsilon hepsilon
    simpa [g, control] using
      calendarPolygonalInput_converges N initial hT U K hK omega A X hA
        hconverges epsilon hepsilon
  obtain ⟨rStart, hrStart⟩ := hgconv 1 (by norm_num)
  have hcontrolBound (jk : Server × Buffer) :
      exists C : Real, forall t, t ∈ Icc (0 : Real) T ->
        abs (control jk t) <= C := by
    obtain ⟨C, hC⟩ :=
      isCompact_Icc.bddAbove_image (hcontrol jk).abs
    refine ⟨C, fun t ht => hC ?_⟩
    exact mem_image_of_mem (fun s => abs (control jk s)) ht
  choose C hC using hcontrolBound
  let M : Real :=
    Finset.univ.sum (fun jk : Server × Buffer => max (C jk) 0 + 1)
  have hcoordBound (jk : Server × Buffer) :
      max (C jk) 0 + 1 <= M := by
    dsimp [M]
    exact Finset.single_le_sum
      (f := fun b : Server × Buffer => max (C b) 0 + 1)
      (fun b _ => by positivity) (Finset.mem_univ jk)
  have hbound :
      forall r ijk t, t ∈ Icc (0 : Real) T ->
        abs (f (rStart + r) ijk t) <= M := by
    intro r ijk t ht
    let jk : Server × Buffer := (ijk.2.1, ijk.2.2)
    have hf_le :
        abs (f (rStart + r) ijk t) <= g (rStart + r) jk t := by
      exact calendarPolygonalAllocation_abs_le_input
        N initial hT U (K (rStart + r)) omega
          ijk.1 ijk.2.1 ijk.2.2 ht
    have hg := hrStart (rStart + r) (Nat.le_add_right rStart r) jk t ht
    rw [Real.dist_eq] at hg
    calc
      abs (f (rStart + r) ijk t) <= g (rStart + r) jk t := hf_le
      _ <= abs (control jk t) +
          abs (g (rStart + r) jk t - control jk t) := by
        calc
          g (rStart + r) jk t =
              control jk t +
                (g (rStart + r) jk t - control jk t) := by ring
          _ <= _ := add_le_add (le_abs_self _) (le_abs_self _)
      _ <= C jk + 1 := by
        gcongr
        exact hC jk t ht
      _ <= max (C jk) 0 + 1 := by
        gcongr
        exact le_max_left _ _
      _ <= M := hcoordBound jk
  have hdom :
      forall r ijk s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T ->
          dist (f r ijk s) (f r ijk t) <=
            Finset.univ.sum (fun jk =>
              dist (g r jk s) (g r jk t)) := by
    intro r ijk s hs t ht
    exact calendarPolygonalAllocation_increment_domination N initial hT U (K r)
      omega ijk.1 ijk.2.1 ijk.2.2 hs ht
  obtain ⟨q, hq, limit, hlimitCont, hlimitConv⟩ :=
    FluidControlledCompactness.exists_uniformly_convergent_subsequence_finite
      (f := fun r ijk t => f (rStart + r) ijk t)
      (g := fun r jk t => g (rStart + r) jk t)
      (control := control)
      (a := (0 : Real)) (b := T) (M := M)
      (fun r => hf (rStart + r)) hbound hcontrol
      (by
        intro epsilon hepsilon
        obtain ⟨r0, hr0⟩ := hgconv epsilon hepsilon
        refine ⟨r0, fun r hr => hr0 (rStart + r) ?_⟩
        exact hr.trans (Nat.le_add_left r rStart))
      (fun r => hdom (rStart + r))
  let E : FluidAllocationPath Buffer Server :=
    fun t i j k => limit (i, j, k) t
  let q' : Nat -> Nat := fun r => rStart + q r
  have hq' : StrictMono q' := fun _ _ hrs =>
    Nat.add_lt_add_left (hq hrs) rStart
  refine ⟨q', hq', E, ?_, ?_⟩
  · intro i j k
    exact hlimitCont (i, j, k)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hlimitConv epsilon hepsilon
    refine ⟨r0, fun r hr i j k t ht => ?_⟩
    exact hr0 r hr (i, j, k) t ht

private theorem calendarPolygonalAllocation_approximates_scaled
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (N.calendarPolygonalAllocation initial T U (K r) omega t i j k)
            (N.calendarScaledAllocationFromInitial initial U (K r) omega t i j k) < epsilon := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  let Avec : Real -> (Server × Buffer -> Real) :=
    fun t jk => A t jk.1 jk.2
  have hAvecCont : ContinuousOn Avec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro jk
    simpa [Avec, uIcc_of_le hT.le] using
      (hA jk.1 jk.2).continuousOn
  have hAvecUC : UniformContinuousOn Avec (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hAvecCont
  have hKreal :
      Tendsto (fun r => (((K r : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (triangular_pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun r => T / (((K r : Nat) : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp hAvecUC
      (epsilon / 4) (by positivity)
  obtain ⟨rMesh, hrMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh delta hdelta
  obtain ⟨rInput, hrInput⟩ := hinput (epsilon / 4) (by positivity)
  refine ⟨max rMesh rInput, fun r hr i j k t ht => ?_⟩
  have hrM : rMesh <= r := (le_max_left _ _).trans hr
  have hrI : rInput <= r := (le_max_right _ _).trans hr
  have hmeshSmall : T / (((K r : Nat) : Real)) < delta := by
    have hm := hrMesh r hrM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at hm
    exact hm
  have hosc :
      forall s, s ∈ Icc (0 : Real) T ->
        forall u, u ∈ Icc (0 : Real) T ->
          abs (s - u) <= T / (K r : Nat) ->
          abs
            (N.calendarScaledAllocationFromInitial initial U (K r) omega s i j k -
              N.calendarScaledAllocationFromInitial initial U (K r) omega u i j k) <=
            3 * (epsilon / 4) := by
    intro s hs u hu hsu
    have hAu : dist (Avec s) (Avec u) < epsilon / 4 := by
      apply hdeltaWorks s hs u hu
      rw [Real.dist_eq]
      exact hsu.trans_lt hmeshSmall
    have hcoord :
        dist (A s j k) (A u j k) <= dist (Avec s) (Avec u) := by
      exact (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s) (Avec u) <= dist (Avec s) (Avec u)) (j, k)
    have hsInput := hrInput r hrI s hs (j, k)
    have huInput := hrInput r hrI u hu (j, k)
    have htoken :
        dist (N.totalCalendarScaledInput (K r) (omega (K r)) s j k)
          (N.totalCalendarScaledInput (K r) (omega (K r)) u j k) <
            3 * (epsilon / 4) := by
      calc
        _ <= dist (N.totalCalendarScaledInput (K r) (omega (K r)) s j k) (A s j k) +
              dist (A s j k) (A u j k) +
              dist (A u j k)
                (N.totalCalendarScaledInput (K r) (omega (K r)) u j k) := by
          calc
            _ <= dist (N.totalCalendarScaledInput (K r) (omega (K r)) s j k) (A s j k) +
                dist (A s j k)
                  (N.totalCalendarScaledInput (K r) (omega (K r)) u j k) :=
              dist_triangle _ _ _
            _ <= _ := by
              have htri := dist_triangle (A s j k) (A u j k)
                (N.totalCalendarScaledInput (K r) (omega (K r)) u j k)
              linarith
        _ < epsilon / 4 + epsilon / 4 + epsilon / 4 := by
          have huInput' :
              dist (A u j k)
                (N.totalCalendarScaledInput (K r) (omega (K r)) u j k) < epsilon / 4 := by
            simpa [Real.dist_eq, abs_sub_comm] using huInput
          exact add_lt_add (add_lt_add hsInput
            (hcoord.trans_lt hAu)) huInput'
        _ = _ := by ring
    have halloc :=
      calendarScaledAllocationFromInitial_dist_le N initial U (K r) omega s u i j k
    rw [Real.dist_eq] at halloc
    exact halloc.trans (le_of_lt htoken)
  have hnode :
      forall l, l <= (K r : Nat) ->
        abs
          (((N.calendarGridAllocation initial T U (K r) omega l i j k : Real) /
              (K r : Nat)) -
            N.calendarScaledAllocationFromInitial initial U (K r) omega
              (calendarGridTime T (K r) l) i j k) <= 0 := by
    intro l hl
    have heq :
        N.calendarScaledAllocationFromInitial initial U (K r) omega
            (calendarGridTime T (K r) l) i j k =
          (N.calendarGridAllocation initial T U (K r) omega l i j k : Real) /
            (K r : Nat) := by
      rfl
    rw [heq, sub_self, abs_zero]
  have herr :=
    fi_polygonalInterpolate_error_of_nodes hT (K r)
      (fun l =>
        (N.calendarGridAllocation initial T U (K r) omega l i j k : Real) /
          (K r : Nat))
      (fun s => N.calendarScaledAllocationFromInitial initial U (K r) omega s i j k)
      0 (3 * (epsilon / 4)) hnode hosc t ht
  rw [Real.dist_eq]
  exact herr.trans_lt (by nlinarith)

private theorem calendarInput_isFluidInput
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X) :
    IsFluidInput T A := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  have hpoint (t : Real) (ht : t ∈ Icc (0 : Real) T)
      (j : Server) (k : Buffer) :
      Tendsto (fun r => N.totalCalendarScaledInput (K r) (omega (K r)) t j k)
        atTop (nhds (A t j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hinput epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr t ht (j, k)⟩
  refine ⟨hA, ?_, ?_⟩
  · intro j k s hs t ht hst
    exact le_of_tendsto_of_tendsto
      (hpoint s hs j k) (hpoint t ht j k)
      (Eventually.of_forall fun r =>
        calendarScaledInput_mono N (K r) omega hst j k)
  · intro j k
    have hzero :
        (fun r => N.totalCalendarScaledInput (K r) (omega (K r)) 0 j k) =
          fun _ => 0 := by
      funext r
      simp [totalCalendarScaledInput, calendarScaledInput]
    apply tendsto_nhds_unique (hpoint 0 ⟨le_rfl, hT.le⟩ j k)
    rw [hzero]
    exact tendsto_const_nhds

private theorem calendarAllocation_raw_converges
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    (N.triangularCalendarExecutionFrom initial).AllocationConvergesOn T U K q omega E := by
  have happ :=
    calendarPolygonalAllocation_approximates_scaled N initial hT U K hK omega A X hA hconverges
  change UniformlyOnIcc T
      (fun r t (ijk : Buffer × Server × Buffer) =>
        N.calendarScaledAllocationFromInitial initial U (K (q r)) omega t
          ijk.1 ijk.2.1 ijk.2.2)
      (fun t ijk => E t ijk.1 ijk.2.1 ijk.2.2)
  intro epsilon hepsilon
  obtain ⟨rPoly, hrPoly⟩ := hpoly (epsilon / 2) (by positivity)
  obtain ⟨rApprox, hrApprox⟩ := happ (epsilon / 2) (by positivity)
  refine ⟨max rPoly rApprox, fun r hr t ht ijk => ?_⟩
  have hrP : rPoly <= r := (le_max_left _ _).trans hr
  have hrAq : rApprox <= q r := by
    exact (le_max_right rPoly rApprox).trans
      (hr.trans (hq.id_le r))
  have hp := hrPoly r hrP ijk.1 ijk.2.1 ijk.2.2 t ht
  have ha := hrApprox (q r) hrAq
    ijk.1 ijk.2.1 ijk.2.2 t ht
  have ha' :
      dist
          (N.calendarScaledAllocationFromInitial initial U (K (q r)) omega t
            ijk.1 ijk.2.1 ijk.2.2)
          (N.calendarPolygonalAllocation initial T U (K (q r)) omega t
            ijk.1 ijk.2.1 ijk.2.2) < epsilon / 2 := by
    simpa [dist_comm] using ha
  change
    dist
      (N.calendarScaledAllocationFromInitial initial U (K (q r)) omega t
        ijk.1 ijk.2.1 ijk.2.2)
      (E t ijk.1 ijk.2.1 ijk.2.2) < epsilon
  calc
    _ <= _ := dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add ha' hp
    _ = epsilon := by ring

private noncomputable def calendarGridPreActionStates
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) (l : Fin (K : Nat)) :
    List (JobState Buffer (K : Nat)) :=
  N.fluidEmpiricalPreActionStates (U K)
    (N.calendarGridState initial T U K omega l.val)
    (N.calendarGridBatch T K omega l.val) j k

private noncomputable def calendarPolygonalAction
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) (t : Real) : ActionVector Buffer :=
  scaledBatchedPolicyActionInterpolate N K U K
    (N.calendarGridPreActionStates initial T U K omega j k) j k T t

private theorem edgeProgress_eq_ff_clamp (r : Real) (l : Nat) :
    edgeProgress r l = existenceClamp01 (r - l) := by
  unfold edgeProgress existenceClamp01
  rcases le_total (r - l) 0 with h | h
  · simp [max_eq_left h, min_eq_right (h.trans zero_le_one)]
  · by_cases h1 : r - l <= 1
    · simp [max_eq_right h, min_eq_right h1]
    · have h1' : 1 <= r - l := le_of_not_ge h1
      simp [max_eq_right h, min_eq_left h1']

private theorem existenceRampInterpolate_div
    (K : PNat) (values : Nat -> Real) (c t T : Real) :
    existenceRampInterpolate K (fun l => values l / c) t T =
      existenceRampInterpolate K values t T / c := by
  unfold existenceRampInterpolate
  rw [show
    Finset.sum (Finset.range (K : Nat)) (fun l =>
      (values (l + 1) / c - values l / c) *
        existenceClamp01 (((K : Nat) : Real) * t / T - l)) =
      (Finset.sum (Finset.range (K : Nat)) (fun l =>
        (values (l + 1) - values l) *
          existenceClamp01 (((K : Nat) : Real) * t / T - l))) / c by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l hl
    ring]
  ring

private theorem calendarGridPreActionStates_length
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) (l : Fin (K : Nat)) :
    (N.calendarGridPreActionStates initial T U K omega j k l).length =
      N.calendarGridInput T K omega (l.val + 1) j k -
        N.calendarGridInput T K omega l.val j k := by
  unfold calendarGridPreActionStates
  rw [N.fluidEmpiricalPreActionStates_length]
  exact calendarGridBatch_count N hT K omega l.val j k

private theorem calendarGridPreAction_sum_some
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (l : Fin (K : Nat)) (i : Buffer) (j : Server) (k : Buffer) :
    ((N.calendarGridPreActionStates initial T U K omega j k l).map
      (fun y => N.actionDirac (U K y j k))).sum (some i) =
      (N.calendarGridAllocation initial T U K omega (l.val + 1) i j k : Real) -
        (N.calendarGridAllocation initial T U K omega l.val i j k : Real) := by
  let z := N.calendarGridState initial T U K omega l.val
  let batch := N.calendarGridBatch T K omega l.val
  have hemp := congrFun
    (N.fluidEmpiricalActionCount_eq_preActionState_sum
      (U K) z batch j k) (some i)
  rw [N.fluidEmpiricalActionCount_some_eq_runAllocationCount] at hemp
  change
    ((N.fluidEmpiricalPreActionStates (U K) z batch j k).map
      (fun y => N.actionDirac (U K y j k))).sum (some i) = _
  rw [<- hemp]
  have hsucc :=
    calendarGridAllocation_succ N initial hT U K omega l.val i j k
  dsimp [z, batch]
  rw [hsucc, Nat.cast_add]
  ring

private theorem calendarPolygonalInput_eq_batched
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    N.calendarPolygonalInput T K omega t j k =
      scaledBatchedInputInterpolate K
        (N.calendarGridPreActionStates initial T U K omega j k) T t := by
  let states := N.calendarGridPreActionStates initial T U K omega j k
  let values : Nat -> Real :=
    fun l => (N.calendarGridInput T K omega l j k : Real)
  let r : Real := ((K : Nat) : Real) * t / T
  have hbatch :
      batchedInputInterpolate states r =
        existenceRampInterpolate K values t T := by
    rw [batchedInputInterpolate_eq_cumulativeRamp states values r]
    · unfold existenceRampInterpolate
      dsimp [r]
      apply congrArg (fun x => values 0 + x)
      apply Finset.sum_congr rfl
      intro l hl
      rw [edgeProgress_eq_ff_clamp]
    · rw [show values 0 = 0 by
        simp [values, calendarGridInput, calendarGridPrefix,
          calendarGridTime_zero, totalCalendarTokenPrefix_zero N]]
    · intro l
      rw [calendarGridPreActionStates_length N initial hT U K omega j k l]
      dsimp [values]
      rw [Nat.cast_sub
        (calendarGridInput_mono N hT K omega
          (Nat.le_succ l.val) j k)]
  unfold calendarPolygonalInput scaledBatchedInputInterpolate
  rw [fi_polygonalInterpolate_eq_ramp K _ hT ht]
  rw [ff_rampInterpolate_eq_existenceRampInterpolate]
  change existenceRampInterpolate K (fun l =>
      (N.calendarGridInput T K omega l j k : Real) / (K : Nat)) t T =
    batchedInputInterpolate states r / (K : Nat)
  rw [hbatch]
  exact existenceRampInterpolate_div K values (K : Nat) t T

private theorem calendarPolygonalAction_some
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (i : Buffer) (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    N.calendarPolygonalAction initial T U K omega j k t (some i) =
      N.calendarPolygonalAllocation initial T U K omega t i j k := by
  let states := N.calendarGridPreActionStates initial T U K omega j k
  let values : Nat -> Real :=
    fun l => (N.calendarGridAllocation initial T U K omega l i j k : Real)
  let r : Real := ((K : Nat) : Real) * t / T
  have hbatch :
      batchedPolicyActionInterpolate N U K states j k r (some i) =
        existenceRampInterpolate K values t T := by
    rw [batchedPolicyActionInterpolate_eq_batch_sum]
    unfold existenceRampInterpolate
    rw [show values 0 = 0 by
      simp [values, calendarGridAllocation, calendarGridPrefix,
        calendarGridTime_zero, totalCalendarTokenPrefix_zero N,
        runAllocationCount]]
    simp only [zero_add]
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro l hl
    rw [show
      Finset.univ.sum (fun q : Fin (states l).length =>
        edgeProgress r l.val *
          N.actionDirac (U K ((states l).get q) j k) (some i)) =
        (((states l).map
          (fun y => N.actionDirac (U K y j k))).sum (some i)) *
            edgeProgress r l.val by
      have hsum :
          ((states l).map
            (fun y => N.actionDirac (U K y j k))).sum =
            Finset.univ.sum (fun q : Fin (states l).length =>
              N.actionDirac (U K ((states l).get q) j k)) := by
        rw [<- List.sum_ofFn]
        change _ = (List.ofFn
          ((fun y => N.actionDirac (U K y j k)) ∘
            (states l).get)).sum
        rw [<- List.map_ofFn, List.ofFn_get]
      rw [hsum, Finset.sum_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring]
    rw [calendarGridPreAction_sum_some N initial hT U K omega l i j k]
    rw [edgeProgress_eq_ff_clamp]
  unfold calendarPolygonalAction scaledBatchedPolicyActionInterpolate
  change
    batchedPolicyActionInterpolate N U K states j k r (some i) /
        (K : Nat) =
      fi_polygonalInterpolate K
        (fun l => (N.calendarGridAllocation initial T U K omega l i j k : Real) /
          (K : Nat)) t T
  rw [hbatch, fi_polygonalInterpolate_eq_ramp K _ hT ht]
  rw [ff_rampInterpolate_eq_existenceRampInterpolate]
  exact (existenceRampInterpolate_div K values (K : Nat) t T).symm

private theorem calendarPolygonalAction_sum
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    Finset.univ.sum (N.calendarPolygonalAction initial T U K omega j k t) =
      N.calendarPolygonalInput T K omega t j k := by
  rw [calendarPolygonalInput_eq_batched N initial hT U K omega j k ht]
  unfold calendarPolygonalAction scaledBatchedPolicyActionInterpolate
    scaledBatchedInputInterpolate
  rw [<- Finset.sum_div]
  unfold batchedPolicyActionInterpolate finiteActionVectorInterpolate
    batchedInputInterpolate finiteActionInputInterpolate
  field_simp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [<- Finset.mul_sum]
  rw [(N.actionDirac_isDistribution
    (U K
      ((N.calendarGridPreActionStates initial T U K omega j k q.1).get q.2)
      j k)).2]
  rw [mul_one]

private theorem calendarPolygonalAction_none
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    N.calendarPolygonalAction initial T U K omega j k t none =
      N.calendarPolygonalInput T K omega t j k -
        Finset.univ.sum (fun i : Buffer =>
          N.calendarPolygonalAllocation initial T U K omega t i j k) := by
  have hsum := calendarPolygonalAction_sum N initial hT U K omega j k ht
  rw [show
    Finset.univ.sum (N.calendarPolygonalAction initial T U K omega j k t) =
      N.calendarPolygonalAction initial T U K omega j k t none +
        Finset.univ.sum (fun i : Buffer =>
          N.calendarPolygonalAction initial T U K omega j k t (some i)) by
    rw [Fintype.sum_option]] at hsum
  simp_rw [calendarPolygonalAction_some N initial hT U K omega _ _ _ ht] at hsum
  linarith

private theorem calendar_fluidEmpiricalPreActionStates_mem_dist_le {Knat : Nat}
    (U0 : N.DeterministicStationaryPolicy Knat)
    (z : JobState Buffer Knat)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer)
    {y : JobState Buffer Knat}
    (hy : y ∈ N.fluidEmpiricalPreActionStates U0 z tokens j k)
    (i : Buffer) :
    abs ((y i : Real) - (z i : Real)) <= 2 * tokens.length := by
  induction tokens generalizing z with
  | nil =>
      simp [fluidEmpiricalPreActionStates] at hy
  | cons jk rest ih =>
      by_cases hm : jk = (j, k)
      · subst jk
        simp only [fluidEmpiricalPreActionStates, if_pos,
          List.mem_cons] at hy
        rcases hy with rfl | hy
        · rw [sub_self, abs_zero]
          exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
        · have htail :=
            ih (N.queueStep U0 z (j, k)) hy
          have hone :=
            ff_runTokens_l1_le_two_mul_length N U0 z [(j, k)]
          have hcoord :
              abs (((N.queueStep U0 z (j, k) i : Nat) : Real) -
                (z i : Real)) <= 2 := by
            have hsingle :=
              Finset.single_le_sum
                (fun q _ => abs_nonneg
                  (((N.runTokens U0 z [(j, k)] q : Nat) : Real) -
                    (z q : Real)))
                (Finset.mem_univ i)
            have hrun :
                N.runTokens U0 z [(j, k)] =
                  N.queueStep U0 z (j, k) := by
              rfl
            rw [hrun] at hsingle
            rw [hrun] at hone
            exact hsingle.trans (by simpa using hone)
          calc
            abs ((y i : Real) - (z i : Real)) <=
                abs ((y i : Real) -
                  (N.queueStep U0 z (j, k) i : Real)) +
                abs ((N.queueStep U0 z (j, k) i : Real) -
                  (z i : Real)) := abs_sub_le _ _ _
            _ <= 2 * rest.length + 2 := add_le_add htail hcoord
            _ = 2 * ((j, k) :: rest).length := by simp; ring
      · simp only [fluidEmpiricalPreActionStates, hm, if_neg] at hy
        have htail := ih (N.queueStep U0 z jk) hy
        have hone :=
          ff_runTokens_l1_le_two_mul_length N U0 z [jk]
        have hcoord :
            abs (((N.queueStep U0 z jk i : Nat) : Real) -
              (z i : Real)) <= 2 := by
          have hsingle :=
            Finset.single_le_sum
              (fun q _ => abs_nonneg
                (((N.runTokens U0 z [jk] q : Nat) : Real) -
                  (z q : Real)))
              (Finset.mem_univ i)
          have hrun :
              N.runTokens U0 z [jk] = N.queueStep U0 z jk := by
            rfl
          rw [hrun] at hsingle
          rw [hrun] at hone
          exact hsingle.trans (by simpa using hone)
        calc
          abs ((y i : Real) - (z i : Real)) <=
              abs ((y i : Real) -
                (N.queueStep U0 z jk i : Real)) +
              abs ((N.queueStep U0 z jk i : Real) -
                (z i : Real)) := abs_sub_le _ _ _
          _ <= 2 * rest.length + 2 := add_le_add htail hcoord
          _ = 2 * (jk :: rest).length := by simp; ring

private theorem calendarGridBatch_scaled_length
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (l : Nat) :
    ((N.calendarGridBatch T K omega l).length : Real) / (K : Nat) =
      Finset.univ.sum (fun jk : Server × Buffer =>
        N.totalCalendarScaledInput K (omega K)
            (calendarGridTime T K (l + 1)) jk.1 jk.2 -
          N.totalCalendarScaledInput K (omega K)
            (calendarGridTime T K l) jk.1 jk.2) := by
  rw [calendarGridBatch_length_eq_input_sum N hT K omega l,
    Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro jk hjk
  rw [calendarScaledInput_eq_prefix_count N,
    calendarScaledInput_eq_prefix_count N]
  simp only [calendarGridInput, calendarGridPrefix]
  have hmono := calendarGridInput_mono N hT K omega
    (Nat.le_succ l) jk.1 jk.2
  have hmono' :
      (N.totalCalendarTokenPrefix K (omega K)
          (calendarGridTime T K l)).count jk <=
        (N.totalCalendarTokenPrefix K (omega K)
          (calendarGridTime T K (l + 1))).count jk := by
    simpa only [calendarGridInput, calendarGridPrefix] using hmono
  rw [Nat.cast_sub hmono']
  ring

private theorem calendarGridBatch_scaled_length_small
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn
        T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall l, l < (K r : Nat) ->
          2 * (((N.calendarGridBatch T (K r) omega l).length : Real) /
            (K r : Nat)) < epsilon := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  let Avec : Real -> (Server × Buffer -> Real) :=
    fun t jk => A t jk.1 jk.2
  have hAvecCont : ContinuousOn Avec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro jk
    simpa [Avec, uIcc_of_le hT.le] using
      (hA jk.1 jk.2).continuousOn
  have hAvecUC : UniformContinuousOn Avec (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hAvecCont
  have hKreal :
      Tendsto (fun r => (((K r : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (triangular_pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun r => T / (((K r : Nat) : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  intro epsilon hepsilon
  let C : Real := (Fintype.card (Server × Buffer) : Real) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let eta : Real := epsilon / (8 * C)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp hAvecUC eta heta
  obtain ⟨rMesh, hrMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh delta hdelta
  obtain ⟨rInput, hrInput⟩ := hinput eta heta
  refine ⟨max rMesh rInput, fun r hr l hl => ?_⟩
  have hrM : rMesh <= r := (le_max_left _ _).trans hr
  have hrI : rInput <= r := (le_max_right _ _).trans hr
  let s := calendarGridTime T (K r) l
  let t := calendarGridTime T (K r) (l + 1)
  have hls : l <= (K r : Nat) := Nat.le_of_lt hl
  have hlt : l + 1 <= (K r : Nat) := hl
  have hsMem : s ∈ Icc (0 : Real) T :=
    calendarGridTime_mem_Icc hT (K r) hls
  have htMem : t ∈ Icc (0 : Real) T :=
    calendarGridTime_mem_Icc hT (K r) hlt
  have hmeshSmall : T / (((K r : Nat) : Real)) < delta := by
    have hm := hrMesh r hrM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at hm
    exact hm
  have hst : dist s t < delta := by
    rw [Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr
        (calendarGridTime_mono hT (K r) (Nat.le_succ l)))]
    simpa [s, t, calendarGridTime_succ_sub] using hmeshSmall
  have hAvecNear : dist (Avec s) (Avec t) < eta :=
    hdeltaWorks s hsMem t htMem hst
  have hterm (jk : Server × Buffer) :
      N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2 <
        3 * eta := by
    have hsInput := hrInput r hrI s hsMem jk
    have htInput := hrInput r hrI t htMem jk
    have hcoord :
        dist (Avec s jk) (Avec t jk) <= dist (Avec s) (Avec t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s) (Avec t) <= dist (Avec s) (Avec t)) jk
    have hmiddle : abs (A t jk.1 jk.2 - A s jk.1 jk.2) < eta := by
      simpa [Avec, Real.dist_eq, abs_sub_comm] using
        hcoord.trans_lt hAvecNear
    calc
      N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2 <=
        abs (N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2 -
          A t jk.1 jk.2) +
        abs (A t jk.1 jk.2 - A s jk.1 jk.2) +
        abs (A s jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2) := by
            linarith [le_abs_self
              (N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2 -
                A t jk.1 jk.2),
              le_abs_self (A t jk.1 jk.2 - A s jk.1 jk.2),
              le_abs_self (A s jk.1 jk.2 -
                N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2)]
      _ < eta + eta + eta := by
        exact add_lt_add (add_lt_add htInput hmiddle)
          (by simpa [abs_sub_comm] using hsInput)
      _ = 3 * eta := by ring
  have hsum :
      Finset.univ.sum (fun jk : Server × Buffer =>
        N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2) <
        (Fintype.card (Server × Buffer) : Real) * (3 * eta) := by
    calc
      _ < Finset.univ.sum (fun _ : Server × Buffer => 3 * eta) :=
        Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty : (Finset.univ :
            Finset (Server × Buffer)).Nonempty)
          (fun jk _ => hterm jk)
      _ = _ := by simp
  rw [calendarGridBatch_scaled_length N hT (K r) omega l]
  calc
    2 * Finset.univ.sum (fun jk : Server × Buffer =>
        N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2 -
          N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2) <
        2 * ((Fintype.card (Server × Buffer) : Real) * (3 * eta)) :=
      mul_lt_mul_of_pos_left hsum (by norm_num)
    _ < epsilon := by
      dsimp [eta, C]
      have hcard : 0 <= (Fintype.card (Server × Buffer) : Real) := by
        positivity
      have hcardC :
          (Fintype.card (Server × Buffer) : Real) <
            (Fintype.card (Server × Buffer) : Real) + 1 := by linarith
      have hratio :
          (Fintype.card (Server × Buffer) : Real) /
              ((Fintype.card (Server × Buffer) : Real) + 1) < 1 :=
        (div_lt_one (by linarith)).2 hcardC
      field_simp
      nlinarith

private theorem calendar_edgeProgress_le_one (r : Real) (l : Nat) :
    edgeProgress r l <= 1 := by
  unfold edgeProgress
  exact max_le (by norm_num) (min_le_left _ _)

private theorem calendar_edgeProgress_pos_imp (r : Real) (l : Nat)
    (h : 0 < edgeProgress r l) :
    (l : Real) < r := by
  unfold edgeProgress at h
  have hm : 0 < min 1 (r - (l : Real)) := by
    by_contra hn
    have hmle : min 1 (r - (l : Real)) <= 0 := le_of_not_gt hn
    rw [max_eq_left hmle] at h
    exact (lt_irrefl 0 h)
  exact sub_pos.mp ((lt_min_iff.mp hm).2)

private theorem calendar_edgeProgress_lt_one_imp (r : Real) (l : Nat)
    (h : edgeProgress r l < 1) :
    r < (l : Real) + 1 := by
  by_contra hn
  have hr : 1 <= r - (l : Real) := by linarith
  unfold edgeProgress at h
  rw [min_eq_left hr, max_eq_right zero_le_one] at h
  exact (lt_irrefl 1 h)

private theorem calendar_used_edge_ff_gridTime_close
    {T : Real} (hT : 0 < T) (K : PNat)
    {t h : Real} (hh : 0 < h) (l : Nat)
    (hused :
      0 <
        edgeProgress (((K : Nat) : Real) * (t + h) / T) l -
          edgeProgress (((K : Nat) : Real) * t / T) l) :
    abs (calendarGridTime T K l - t) <
      h + T / (K : Nat) := by
  let r0 : Real := ((K : Nat) : Real) * t / T
  let r1 : Real := ((K : Nat) : Real) * (t + h) / T
  have hp : edgeProgress r0 l < edgeProgress r1 l := sub_pos.mp hused
  have hr1pos : 0 < edgeProgress r1 l :=
    lt_of_le_of_lt (edgeProgress_nonneg r0 l) hp
  have hr0lt : edgeProgress r0 l < 1 :=
    hp.trans_le (calendar_edgeProgress_le_one r1 l)
  have hlr1 := calendar_edgeProgress_pos_imp r1 l hr1pos
  have hr0l := calendar_edgeProgress_lt_one_imp r0 l hr0lt
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hcancel :
      T / (K : Nat) * (K : Nat) = T :=
    div_mul_cancel₀ T (ne_of_gt hK)
  have hlower : t - T / (K : Nat) < calendarGridTime T K l := by
    dsimp [r0] at hr0l
    unfold calendarGridTime
    apply (lt_div_iff₀ hK).2
    apply (div_lt_iff₀ hT).1 at hr0l
    nlinarith [hcancel]
  have hupper : calendarGridTime T K l < t + h := by
    dsimp [r1] at hlr1
    unfold calendarGridTime
    apply (div_lt_iff₀ hK).2
    apply (lt_div_iff₀ hT).1 at hlr1
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith [div_pos hT hK]

private theorem calendarPreActionStates_near
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X)
    {t epsilon : Real} (ht : t ∈ Ioo (0 : Real) T)
    (hepsilon : 0 < epsilon) :
    exists delta, 0 < delta /\
      exists r0, forall r, r0 <= r ->
        forall h, 0 < h -> h < delta ->
          forall j k (l : Fin (K r : Nat))
            (y : JobState Buffer (K r : Nat)),
            y ∈ N.calendarGridPreActionStates initial T U (K r) omega j k l ->
            0 <
              edgeProgress
                  (((K r : Nat) : Real) * (t + h) / T) l.val -
                edgeProgress
                  (((K r : Nat) : Real) * t / T) l.val ->
            IsNearNormalizedState y (X t) epsilon := by
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t i => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
      X at hstate
  let Xvec : Real -> (Buffer -> Real) := fun s i => X s i
  have hXcont : ContinuousOn Xvec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    exact calendarStateLimit_continuousOn N initial hT U K omega A X hA hconverges
  have hXuc : UniformContinuousOn Xvec (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hXcont
  obtain ⟨deltaX, hdeltaX, hdeltaXWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp hXuc
      (epsilon / 3) (by positivity)
  let delta := min (deltaX / 2) ((T - t) / 2)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by positivity) (by linarith [ht.2])
  have hKreal :
      Tendsto (fun r => (((K r : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (triangular_pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun r => T / (((K r : Nat) : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  obtain ⟨rMesh, hrMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh (deltaX / 2) (by positivity)
  obtain ⟨rBatch, hrBatch⟩ :=
    calendarGridBatch_scaled_length_small N initial hT U K hK omega
      A X hA hconverges (epsilon / 3) (by positivity)
  obtain ⟨rState, hrState⟩ := hstate (epsilon / 3) (by positivity)
  refine ⟨delta, hdelta, max rMesh (max rBatch rState),
    fun r hr h hh hhdelta j k l y hy hused => ?_⟩
  have hrM : rMesh <= r :=
    (le_max_left rMesh (max rBatch rState)).trans hr
  have hrB : rBatch <= r :=
    (le_max_left rBatch rState).trans
      ((le_max_right rMesh (max rBatch rState)).trans hr)
  have hrS : rState <= r :=
    (le_max_right rBatch rState).trans
      ((le_max_right rMesh (max rBatch rState)).trans hr)
  have hmeshSmall : T / (((K r : Nat) : Real)) < deltaX / 2 := by
    have hm := hrMesh r hrM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at hm
    exact hm
  have hbatchSmall :
      2 * (((N.calendarGridBatch T (K r) omega l.val).length : Real) /
        (K r : Nat)) < epsilon / 3 :=
    hrBatch r hrB l.val l.isLt
  have hlK : l.val <= (K r : Nat) := Nat.le_of_lt l.isLt
  have hgridMem :
      calendarGridTime T (K r) l.val ∈ Icc (0 : Real) T :=
    calendarGridTime_mem_Icc hT (K r) hlK
  have hgridClose :
      dist (calendarGridTime T (K r) l.val) t < deltaX := by
    rw [Real.dist_eq]
    have hc :=
      calendar_used_edge_ff_gridTime_close hT (K r) hh l.val hused
    exact hc.trans_le (by
      have hdX : delta <= deltaX / 2 := min_le_left _ _
      linarith)
  have hXclose :
      dist (Xvec (calendarGridTime T (K r) l.val)) (Xvec t) <
        epsilon / 3 :=
    hdeltaXWorks _ hgridMem _ ⟨ht.1.le, ht.2.le⟩ hgridClose
  have hfiniteState (i : Buffer) :
      abs
        (((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
            (K r : Nat) -
          X (calendarGridTime T (K r) l.val) i) < epsilon / 3 := by
    exact hrState r hrS _ hgridMem i
  intro i
  have hyraw :=
    calendar_fluidEmpiricalPreActionStates_mem_dist_le N (U (K r))
      (N.calendarGridState initial T U (K r) omega l.val)
      (N.calendarGridBatch T (K r) omega l.val) j k hy i
  have hygrid :
      abs
        (((y i : Nat) : Real) / (K r : Nat) -
          ((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
            (K r : Nat)) < epsilon / 3 := by
    have hKpos : (0 : Real) < (K r : Nat) := by positivity
    rw [<- sub_div, abs_div, abs_of_pos hKpos]
    calc
      _ <= (2 * (N.calendarGridBatch T (K r) omega l.val).length : Real) /
          (K r : Nat) := div_le_div_of_nonneg_right hyraw hKpos.le
      _ = 2 *
          (((N.calendarGridBatch T (K r) omega l.val).length : Real) /
            (K r : Nat)) := by ring
      _ < epsilon / 3 := hbatchSmall
  have hXcoord :
      abs
        (X (calendarGridTime T (K r) l.val) i - X t i) <
          epsilon / 3 := by
    have hc :
        dist
            (Xvec (calendarGridTime T (K r) l.val) i)
            (Xvec t i) <=
          dist
            (Xvec (calendarGridTime T (K r) l.val))
            (Xvec t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl :
          dist (Xvec (calendarGridTime T (K r) l.val)) (Xvec t) <= _) i
    simpa [Xvec, Real.dist_eq] using hc.trans_lt hXclose
  calc
    abs (((y i : Nat) : Real) / (K r : Nat) - X t i) <=
        abs
          (((y i : Nat) : Real) / (K r : Nat) -
            ((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
              (K r : Nat)) +
        abs
          (((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
              (K r : Nat) -
            X (calendarGridTime T (K r) l.val) i) +
        abs (X (calendarGridTime T (K r) l.val) i - X t i) := by
      calc
        _ <= abs
            (((y i : Nat) : Real) / (K r : Nat) -
              ((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
                (K r : Nat)) +
            abs
              (((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
                (K r : Nat) - X t i) := abs_sub_le _ _ _
        _ <= _ := by
          have htri := abs_sub_le
            (((N.calendarGridState initial T U (K r) omega l.val i : Nat) : Real) /
              (K r : Nat))
            (X (calendarGridTime T (K r) l.val) i) (X t i)
          linarith
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 :=
      add_lt_add (add_lt_add hygrid (hfiniteState i)) hXcoord
    _ = epsilon := by ring

private noncomputable def calendarLimitAction
    (A : MatrixPath Server Buffer) (E : FluidAllocationPath Buffer Server)
    (j : Server) (k : Buffer) (t : Real) : ActionVector Buffer
  | none => A t j k - Finset.univ.sum (fun i : Buffer => E t i j k)
  | some i => E t i j k

private theorem calendarPolygonalAction_tendsto
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon)
    {t : Real} (ht : t ∈ Icc (0 : Real) T)
    (j : Server) (k : Buffer) (a : Option Buffer) :
    Tendsto
      (fun r => N.calendarPolygonalAction initial T U (K (q r)) omega j k t a)
      atTop (nhds (calendarLimitAction A E j k t a)) := by
  have hinputConv :=
    calendarPolygonalInput_converges N initial hT U K hK omega A X hA hconverges
  have hApoint :
      Tendsto
        (fun r => N.calendarPolygonalInput T (K (q r)) omega t j k)
        atTop (nhds (A t j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hinputConv epsilon hepsilon
    refine ⟨r0, fun r hr => ?_⟩
    exact hr0 (q r) (hr.trans (hq.id_le r)) (j, k) t ht
  have hEpoint (i : Buffer) :
      Tendsto
        (fun r =>
          N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
        atTop (nhds (E t i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i j k t ht⟩
  cases a with
  | none =>
      rw [show
        (fun r =>
          N.calendarPolygonalAction initial T U (K (q r)) omega j k t none) =
        fun r =>
          N.calendarPolygonalInput T (K (q r)) omega t j k -
            Finset.univ.sum (fun i : Buffer =>
              N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k) by
        funext r
        exact calendarPolygonalAction_none N initial hT U (K (q r)) omega j k ht]
      exact hApoint.sub (tendsto_finsetSum _ (fun i _ => hEpoint i))
  | some i =>
      rw [show
        (fun r =>
          N.calendarPolygonalAction initial T U (K (q r)) omega j k t (some i)) =
        fun r =>
          N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k by
        funext r
        exact calendarPolygonalAction_some N initial hT U (K (q r)) omega i j k ht]
      exact hEpoint i

private theorem calendarLimit_finiteDifference_mem_epsilon
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon)
    {t epsilon h : Real} (ht : t ∈ Ioo (0 : Real) T)
    (hepsilon : 0 < epsilon) (hh : 0 < h)
    (hth : t + h ∈ Icc (0 : Real) T)
    (hden : 0 < A (t + h) j k - A t j k)
    (hnearWindow :
      exists r0, forall r, r0 <= r ->
        forall l
          (y : JobState Buffer (K (q r) : Nat)),
          y ∈ N.calendarGridPreActionStates initial
            T U (K (q r)) omega j k l ->
          0 <
            edgeProgress
                (((K (q r) : Nat) : Real) * (t + h) / T) l.val -
              edgeProgress
                (((K (q r) : Nat) : Real) * t / T) l.val ->
          IsNearNormalizedState y (X t) epsilon) :
    N.tri_finiteDifferenceRatio
        (fun s => A s j k)
        (fun s => calendarLimitAction A E j k s)
        t h ∈
      N.tri_fluidPolicyEpsilonCorrespondence U j k (X t) epsilon := by
  have hinputConv :=
    calendarPolygonalInput_converges N initial hT U K hK omega A X hA hconverges
  have hApoint (s : Real) (hs : s ∈ Icc (0 : Real) T) :
      Tendsto
        (fun r => N.calendarPolygonalInput T (K (q r)) omega s j k)
        atTop (nhds (A s j k)) := by
    rw [Metric.tendsto_atTop]
    intro eta heta
    obtain ⟨r0, hr0⟩ := hinputConv eta heta
    exact ⟨r0, fun r hr =>
      hr0 (q r) (hr.trans (hq.id_le r)) (j, k) s hs⟩
  have hdenConv :
      Tendsto
        (fun r =>
          N.calendarPolygonalInput T (K (q r)) omega (t + h) j k -
            N.calendarPolygonalInput T (K (q r)) omega t j k)
        atTop (nhds (A (t + h) j k - A t j k)) :=
    (hApoint (t + h) hth).sub
      (hApoint t ⟨ht.1.le, ht.2.le⟩)
  have hdenEventually :
      Filter.Eventually
        (fun r =>
          0 <
            N.calendarPolygonalInput T (K (q r)) omega (t + h) j k -
              N.calendarPolygonalInput T (K (q r)) omega t j k)
        atTop := by
    exact (tendsto_order.mp hdenConv).1 0 hden
  have hKreal :
      Tendsto (fun r => (((K (q r) : Nat) : Real))) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      ((show StrictMono (fun r => (K r : Nat)) from
          fun _ _ hrs => hK hrs).comp hq).tendsto_atTop
  have hKEventually :
      Filter.Eventually
        (fun r => epsilon⁻¹ <= ((K (q r) : Nat) : Real)) atTop :=
    (tendsto_atTop.1 hKreal epsilon⁻¹)
  obtain ⟨rNear, hrNear⟩ := hnearWindow
  have hnearEventually :
      Filter.Eventually
        (fun r =>
          forall l
            (y : JobState Buffer (K (q r) : Nat)),
            y ∈ N.calendarGridPreActionStates initial
              T U (K (q r)) omega j k l ->
            0 <
              edgeProgress
                  (((K (q r) : Nat) : Real) * (t + h) / T) l.val -
                edgeProgress
                  (((K (q r) : Nat) : Real) * t / T) l.val ->
            IsNearNormalizedState y (X t) epsilon)
        atTop :=
    eventually_atTop.2 ⟨rNear, hrNear⟩
  have hmem :
      Filter.Eventually
        (fun r =>
          N.tri_finiteDifferenceRatio
              (fun s =>
                N.calendarPolygonalInput T (K (q r)) omega s j k)
              (fun s =>
                N.calendarPolygonalAction initial T U (K (q r)) omega j k s)
              t h ∈
            N.tri_fluidPolicyEpsilonCorrespondence U j k (X t) epsilon)
        atTop := by
    filter_upwards [hdenEventually, hKEventually, hnearEventually] with
      r hpos hsize hnear
    unfold tri_finiteDifferenceRatio
    change
      (fun a =>
        (N.calendarPolygonalAction initial T U (K (q r)) omega j k (t + h) a -
            N.calendarPolygonalAction initial T U (K (q r)) omega j k t a) /
          (N.calendarPolygonalInput T (K (q r)) omega (t + h) j k -
            N.calendarPolygonalInput T (K (q r)) omega t j k)) ∈
        N.tri_fluidPolicyEpsilonCorrespondence U j k (X t) epsilon
    rw [calendarPolygonalInput_eq_batched N initial hT U (K (q r)) omega j k ⟨ht.1.le, ht.2.le⟩]
    rw [calendarPolygonalInput_eq_batched N initial hT U (K (q r)) omega j k hth]
    have hpos' :
        0 <
          scaledBatchedInputInterpolate (K (q r))
              (N.calendarGridPreActionStates initial T U (K (q r)) omega j k)
              T (t + h) -
            scaledBatchedInputInterpolate (K (q r))
              (N.calendarGridPreActionStates initial T U (K (q r)) omega j k)
              T t := by
      simpa only [
        calendarPolygonalInput_eq_batched N initial hT U (K (q r)) omega j k hth,
        calendarPolygonalInput_eq_batched N initial hT U (K (q r)) omega j k ⟨ht.1.le, ht.2.le⟩] using hpos
    exact N.tri_finiteDifferenceRatio_scaledBatched_mem_epsilon
      (K (q r)) U (K (q r))
      (N.calendarGridPreActionStates initial T U (K (q r)) omega j k)
      j k (X t) epsilon T t h hT hh hpos' hsize hnear
  apply tri_closed_mem_of_tri_finiteDifferenceRatio_limit
    (N.tri_tri_fluidPolicyEpsilonCorrespondence_isClosed U j k (X t) epsilon)
    (fun r s => N.calendarPolygonalInput T (K (q r)) omega s j k)
    (fun s => A s j k)
    (fun r s => N.calendarPolygonalAction initial T U (K (q r)) omega j k s)
    (fun s => calendarLimitAction A E j k s)
    t (t + h)
  · exact hApoint t ⟨ht.1.le, ht.2.le⟩
  · exact hApoint (t + h) hth
  · intro a
    exact calendarPolygonalAction_tendsto N initial hT U K hK omega A X hA
      hconverges q hq E hpoly ⟨ht.1.le, ht.2.le⟩ j k a
  · intro a
    exact calendarPolygonalAction_tendsto N initial hT U K hK omega A X hA
      hconverges q hq E hpoly hth j k a
  · exact ne_of_gt hden
  · filter_upwards [hmem] with n hn
    change
      (fun a =>
        (N.calendarPolygonalAction initial T U (K (q n)) omega j k (t + h) a -
            N.calendarPolygonalAction initial T U (K (q n)) omega j k t a) /
          (N.calendarPolygonalInput T (K (q n)) omega (t + h) j k -
            N.calendarPolygonalInput T (K (q n)) omega t j k)) ∈
        N.tri_fluidPolicyEpsilonCorrespondence U j k (X t) epsilon at hn
    exact hn

private theorem calendarLimit_allocation_initial
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (q : Nat -> Nat) (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall i j k, E 0 i j k = 0 := by
  intro i j k
  have hlim :
      Tendsto
        (fun r =>
          N.calendarPolygonalAllocation initial T U (K (q r)) omega 0 i j k)
        atTop (nhds (E 0 i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i j k 0 ⟨le_rfl, hT.le⟩⟩
  have heq :
      (fun r =>
        N.calendarPolygonalAllocation initial T U (K (q r)) omega 0 i j k) =
        fun _ => 0 := by
    funext r
    exact calendarPolygonalAllocation_initial N initial hT U (K (q r)) omega i j k
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem calendarLimit_allocation_incompatible
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (q : Nat -> Nat) (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall t, t ∈ Icc (0 : Real) T ->
      forall i j k, Not (N.compatible i j) -> E t i j k = 0 := by
  intro t ht i j k hij
  have hlim :
      Tendsto
        (fun r =>
          N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
        atTop (nhds (E t i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i j k t ht⟩
  have heq :
      (fun r =>
        N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k) =
        fun _ => 0 := by
    funext r
    exact calendarPolygonalAllocation_incompatible N initial T U (K (q r)) omega t i j k hij
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem calendarLimit_state_in_simplex
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall t, t ∈ Icc (0 : Real) T -> IsFluidState (X t) := by
  have hstate :=
    calendarPolygonalState_converges N initial hT U K hK omega A X hA hconverges
  intro t ht
  have hpoint (i : Buffer) :
      Tendsto (fun r => N.calendarPolygonalState initial T U (K r) omega t i)
        atTop (nhds (X t i)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hstate epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i t ht⟩
  constructor
  · intro i
    have hneg := (hpoint i).neg
    have hle : -X t i <= 0 :=
      le_of_tendsto' hneg (fun r => by
        have hn :=
          (calendarPolygonalState_in_simplex N initial hT U (K r) omega ht).1 i
        linarith)
    linarith
  · apply tendsto_nhds_unique
      (tendsto_finsetSum _ (fun i _ => hpoint i))
    have heq :
        (fun r =>
          Finset.univ.sum (N.calendarPolygonalState initial T U (K r) omega t)) =
          fun _ => 1 := by
      funext r
      exact (calendarPolygonalState_in_simplex N initial hT U (K r) omega ht).2
    rw [heq]
    exact tendsto_const_nhds

private theorem calendarLimit_balance
    {T : Real} (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hX0 : forall i, X 0 i = x0 i)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall t, t ∈ Icc (0 : Real) T ->
      forall i,
        X t i = x0 i +
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun l : Buffer => E t l j i) -
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer => E t i j k) := by
  have hstate :=
    calendarPolygonalState_converges N initial hT U K hK omega A X hA hconverges
  intro t ht i
  have hXpoint :
      Tendsto
        (fun r => N.calendarPolygonalState initial T U (K (q r)) omega t i)
        atTop (nhds (X t i)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hstate epsilon hepsilon
    exact ⟨r0, fun r hr =>
      hr0 (q r) (hr.trans (hq.id_le r)) i t ht⟩
  have hEpoint (l : Buffer) (j : Server) (k : Buffer) :
      Tendsto
        (fun r =>
          N.calendarPolygonalAllocation initial T U (K (q r)) omega t l j k)
        atTop (nhds (E t l j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr l j k t ht⟩
  have hinit :
      Tendsto
        (fun r => ((initial (K (q r)) i : Nat) : Real) /
          (K (q r) : Nat))
        atTop (nhds (x0 i)) := by
    have hzeroState := hconverges.2
    change UniformlyOnIcc T
        (fun r t i => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
        X at hzeroState
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hzeroState epsilon hepsilon
    refine ⟨r0, fun r hr => ?_⟩
    have hz := hr0 (q r) (hr.trans (hq.id_le r))
      0 ⟨le_rfl, hT.le⟩ i
    simpa [Real.dist_eq, calendarScaledQueueStateFromInitial,
      totalCalendarScaledQueueStateFrom, totalCalendarTokenPrefix_zero N,
      runTokens, hX0 i] using hz
  have hrhs :
      Tendsto
        (fun r =>
          ((initial (K (q r)) i : Nat) : Real) /
              (K (q r) : Nat) +
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun l : Buffer =>
                N.calendarPolygonalAllocation initial
                  T U (K (q r)) omega t l j i) -
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer =>
                N.calendarPolygonalAllocation initial
                  T U (K (q r)) omega t i j k))
        atTop
        (nhds
          (x0 i +
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun l : Buffer => E t l j i) -
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer => E t i j k))) :=
    (hinit.add
      (tendsto_finsetSum _ (fun j _ =>
        tendsto_finsetSum _ (fun l _ => hEpoint l j i)))).sub
      (tendsto_finsetSum _ (fun j _ =>
        tendsto_finsetSum _ (fun k _ => hEpoint i j k)))
  apply tendsto_nhds_unique hXpoint
  apply hrhs.congr'
  filter_upwards [] with r
  exact (calendarPolygonal_balance N initial hT U (K (q r)) omega ht i).symm

private theorem calendarLimit_allocation_ac
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T := by
  intro i j k
  apply FluidCompactness.absolutelyContinuousOnInterval_of_uniform_limits_finset
    (f := fun r t =>
      N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
    (limit := fun t => E t i j k)
    (g := fun r (jk : Server × Buffer) t =>
      N.calendarPolygonalInput T (K (q r)) omega t jk.1 jk.2)
    (control := fun (jk : Server × Buffer) t => A t jk.1 jk.2)
    (s := Finset.univ)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    refine ⟨r0, fun r hr t ht => ?_⟩
    exact hr0 r hr i j k t (by simpa [uIcc_of_le hT.le] using ht)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ :=
      calendarPolygonalInput_converges N initial hT U K hK omega A X hA
        hconverges epsilon hepsilon
    refine ⟨r0, fun r hr jk hjk t ht => ?_⟩
    exact hr0 (q r) (hr.trans (hq.id_le r)) jk t
      (by simpa [uIcc_of_le hT.le] using ht)
  · intro jk hjk
    exact hA jk.1 jk.2
  · intro r s hs t ht
    exact calendarPolygonalAllocation_increment_domination N initial hT U (K (q r)) omega i j k
      (by simpa [uIcc_of_le hT.le] using hs)
      (by simpa [uIcc_of_le hT.le] using ht)

private theorem calendarLimit_allocation_increment
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hinput :
      UniformlyOnIcc T
        (fun r t (jk : Server × Buffer) =>
          N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
        (fun t jk => A t jk.1 jk.2))
    (hraw :
      (N.triangularCalendarExecutionFrom initial).AllocationConvergesOn T U K q omega E) :
    forall i j k s, s ∈ Icc (0 : Real) T ->
      forall t, t ∈ Icc (0 : Real) T -> s <= t ->
        0 <= E t i j k - E s i j k /\
        E t i j k - E s i j k <= A t j k - A s j k := by
  intro i j k s hs t ht hst
  have hEpoint (u : Real) (hu : u ∈ Icc (0 : Real) T) :
      Tendsto (fun r => N.calendarScaledAllocationFromInitial initial U (K (q r)) omega u i j k)
        atTop (nhds (E u i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hraw epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr u hu (i, j, k)⟩
  have hApoint (u : Real) (hu : u ∈ Icc (0 : Real) T) :
      Tendsto (fun r => N.totalCalendarScaledInput (K (q r)) (omega (K (q r))) u j k)
        atTop (nhds (A u j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hinput epsilon hepsilon
    exact ⟨r0, fun r hr =>
      hr0 (q r) (hr.trans (hq.id_le r)) u hu (j, k)⟩
  constructor
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds
      ((hEpoint t ht).sub (hEpoint s hs))
      (Eventually.of_forall fun r =>
        (calendarScaledAllocationFromInitial_ordered_increment N initial U (K (q r)) omega hst i j k).1)
  · exact le_of_tendsto_of_tendsto
      ((hEpoint t ht).sub (hEpoint s hs))
      ((hApoint t ht).sub (hApoint s hs))
      (Eventually.of_forall fun r =>
        (calendarScaledAllocationFromInitial_ordered_increment N initial U (K (q r)) omega hst i j k).2)

private theorem calendarLimit_state_ac
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall i, AbsolutelyContinuousOnInterval (fun t => X t i) 0 T := by
  intro i
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t i => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
      X at hstate
  apply FluidCompactness.absolutelyContinuousOnInterval_of_uniform_limits_finset
    (f := fun r t => N.calendarScaledQueueStateFromInitial initial U (K r) omega t i)
    (limit := fun t => X t i)
    (g := fun r (jk : Server × Buffer) t =>
      2 * N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
    (control := fun (jk : Server × Buffer) t =>
      2 * A t jk.1 jk.2)
    (s := Finset.univ)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hstate epsilon hepsilon
    refine ⟨r0, fun r hr t ht => ?_⟩
    exact hr0 r hr t (by simpa [uIcc_of_le hT.le] using ht) i
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hconverges.1 (epsilon / 2) (by positivity)
    refine ⟨r0, fun r hr b hb t ht => ?_⟩
    have h := hr0 r hr t
      (by simpa [uIcc_of_le hT.le] using ht) b
    change
      abs (N.totalCalendarScaledInput (K r) (omega (K r)) t b.1 b.2 -
        A t b.1 b.2) < epsilon / 2 at h
    rw [Real.dist_eq, <- mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    nlinarith
  · intro b hb
    have hac := (hA b.1 b.2).const_mul 2
    unfold AbsolutelyContinuousOnInterval at hac ⊢
    simpa only using hac
  · intro r s hs t ht
    have hdom := calendarScaledQueueStateFromInitial_dist_le N initial U (K r) omega s t i
    calc
      _ <= 2 * Finset.univ.sum (fun jk : Server × Buffer =>
          dist (N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2)
            (N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)) := hdom
      _ = Finset.univ.sum (fun jk : Server × Buffer =>
          dist (2 * N.totalCalendarScaledInput (K r) (omega (K r)) s jk.1 jk.2)
            (2 * N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)) := by
        simp_rw [Real.dist_eq, <- mul_sub, abs_mul,
          abs_of_pos (by norm_num : (0 : Real) < 2)]
        rw [Finset.mul_sum]

private theorem calendarLimit_balance_restricted
    {T : Real} (x0 : Simplex Buffer) (X : FluidStatePath Buffer)
    (E : FluidAllocationPath Buffer Server)
    (hbalance :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i,
          X t i = x0 i +
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun l : Buffer => E t l j i) -
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer => E t i j k))
    (hincompat :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i j k, Not (N.compatible i j) -> E t i j k = 0) :
    forall t, t ∈ Icc (0 : Real) T ->
      forall i,
        X t i = x0 i
          + (Finset.univ.sum fun j : Server =>
              Finset.sum (N.buffersOf j) fun l => E t l j i)
          - (Finset.sum (N.serversOf i) fun j =>
              Finset.univ.sum fun k : Buffer => E t i j k) := by
  intro t ht i
  rw [hbalance t ht i]
  have hin (j : Server) :
      Finset.univ.sum (fun l : Buffer => E t l j i) =
        Finset.sum (N.buffersOf j) (fun l => E t l j i) := by
    simp only [buffersOf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlj : N.compatible l j
    · simp [hlj]
    · simp [hlj, hincompat t ht l j i hlj]
  have hout :
      Finset.univ.sum
          (fun j : Server => Finset.univ.sum fun k : Buffer => E t i j k) =
        Finset.sum (N.serversOf i)
          (fun j => Finset.univ.sum fun k : Buffer => E t i j k) := by
    simp only [serversOf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : N.compatible i j
    · simp [hij]
    · simp [hij, hincompat t ht i j]
  simp_rw [hin]
  rw [hout]

private theorem calendar_absolutelyContinuousOnInterval_finset_sum
    {I : Type*} (s : Finset I) (f : I -> Real -> Real)
    {a b : Real}
    (hf : forall i, i ∈ s ->
      AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => s.sum fun i => f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (LipschitzWith.const (0 : Real)).lipschitzOnWith
          |>.absolutelyContinuousOnInterval
  | @insert i s hi ih =>
      have hai := hf i (Finset.mem_insert_self i s)
      have has : forall j, j ∈ s ->
          AbsolutelyContinuousOnInterval (f j) a b := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have hfun :
          (fun t => Finset.sum (insert i s) fun j => f j t) =
            fun t => f i t + Finset.sum s fun j => f j t := by
        funext t
        rw [Finset.sum_insert hi]
      rw [hfun]
      have hsum := hai.add (ih has)
      unfold AbsolutelyContinuousOnInterval at hsum ⊢
      simpa only [Real.dist_eq, Pi.add_apply] using hsum

private theorem calendarLimitAction_ac
    {T : Real} (A : MatrixPath Server Buffer)
    (E : FluidAllocationPath Buffer Server)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hE : forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T) :
    forall j k a,
      AbsolutelyContinuousOnInterval
        (fun t => calendarLimitAction A E j k t a) 0 T := by
  intro j k a
  cases a with
  | some i =>
      exact hE i j k
  | none =>
      have hsum :
          AbsolutelyContinuousOnInterval
            (fun t => Finset.univ.sum fun i : Buffer => E t i j k)
            0 T := by
        apply calendar_absolutelyContinuousOnInterval_finset_sum
        intro i hi
        exact hE i j k
      have hsub := (hA j k).sub hsum
      unfold AbsolutelyContinuousOnInterval at hsub ⊢
      simpa only [calendarLimitAction, Pi.sub_apply] using hsub

private theorem calendar_hasDerivAt_eq_zero_of_increment_domination_Icc
    {T : Real} (A E : Real -> Real) {t Edot : Real}
    (ht : t ∈ Ioo (0 : Real) T)
    (hA : HasDerivAt A 0 t) (hE : HasDerivAt E Edot t)
    (hdom : forall s, s ∈ Icc (0 : Real) T ->
      forall u, u ∈ Icc (0 : Real) T -> s <= u ->
        0 <= E u - E s /\ E u - E s <= A u - A s) :
    Edot = 0 := by
  have hsmall :
      Filter.Eventually (fun h => t + h ∈ Icc (0 : Real) T)
        (nhdsWithin 0 (Ioi 0)) := by
    have hlt : 0 < T - t := sub_pos.mpr ht.2
    have hev : Filter.Eventually (fun h : Real => h < T - t) (nhds 0) :=
      eventually_lt_nhds hlt
    filter_upwards [self_mem_nhdsWithin, hev.filter_mono inf_le_left] with
      h hh hupper
    have hhpos : 0 < h := hh
    exact ⟨add_nonneg ht.1.le hhpos.le, by linarith⟩
  have hsqueeze :
      Tendsto (fun h => h⁻¹ * (E (t + h) - E t))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hA.tendsto_slope_zero_right
    next =>
      filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hth
      exact mul_nonneg (inv_nonneg.mpr hh.le)
        (hdom t ⟨ht.1.le, ht.2.le⟩ (t + h) hth
          (le_add_of_nonneg_right hh.le)).1
    next =>
      filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hth
      exact mul_le_mul_of_nonneg_left
        (hdom t ⟨ht.1.le, ht.2.le⟩ (t + h) hth
          (le_add_of_nonneg_right hh.le)).2
        (inv_nonneg.mpr hh.le)
  exact tendsto_nhds_unique hE.tendsto_slope_zero_right hsqueeze

private theorem calendarLimit_zero_derivative_ae
    {T : Real} (hT : 0 < T)
    (A : MatrixPath Server Buffer) (E : FluidAllocationPath Buffer Server)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hE : forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T)
    (hdom : forall i j k s, s ∈ Icc (0 : Real) T ->
      forall t, t ∈ Icc (0 : Real) T -> s <= t ->
        0 <= E t i j k - E s i j k /\
        E t i j k - E s i j k <= A t j k - A s j k) :
    Filter.Eventually
      (fun t => forall j k, deriv (fun s => A s j k) t = 0 ->
        forall i, deriv (fun s => E s i j k) t = 0)
      (ae (volume.restrict (Icc (0 : Real) T))) := by
  rw [<- Measure.restrict_congr_set
    (Ioo_ae_eq_Icc (μ := volume) (a := (0 : Real)) (b := T))]
  have hAdiff (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => t ∈ Icc (0 : Real) T ->
          DifferentiableAt Real (fun s => A s j k) t)
        (ae (volume.restrict (Ioo (0 : Real) T))) := by
    have hv := (hA j k).ae_differentiableAt.filter_mono
      (MeasureTheory.ae_restrict_le
        (μ := volume) (s := Ioo (0 : Real) T))
    filter_upwards [hv] with t ht hmem
    exact ht (by simpa [uIcc_of_le hT.le] using hmem)
  have hEdiff (i : Buffer) (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => t ∈ Icc (0 : Real) T ->
          DifferentiableAt Real (fun s => E s i j k) t)
        (ae (volume.restrict (Ioo (0 : Real) T))) := by
    have hv := (hE i j k).ae_differentiableAt.filter_mono
      (MeasureTheory.ae_restrict_le
        (μ := volume) (s := Ioo (0 : Real) T))
    filter_upwards [hv] with t ht hmem
    exact ht (by simpa [uIcc_of_le hT.le] using hmem)
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => hAdiff j k)),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      ae_all_iff.mpr (fun k => hEdiff i j k)))] with
      t ht hAt hEt
  intro j k hzero i
  apply calendar_hasDerivAt_eq_zero_of_increment_domination_Icc
    (fun s => A s j k) (fun s => E s i j k) ht
  · simpa [hzero] using (hAt j k (Set.Ioo_subset_Icc_self ht)).hasDerivAt
  · exact (hEt i j k (Set.Ioo_subset_Icc_self ht)).hasDerivAt
  · intro s hs u hu hsu
    exact hdom i j k s hs u hu hsu

private theorem calendarLimit_positive_policy_ae
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.triangularCalendarExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.calendarPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon)
    (hEac : forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T) :
    forall j k,
      Filter.Eventually
        (fun t => 0 < deriv (fun s => A s j k) t ->
          Membership.mem
            (N.fluidPolicyCorrespondence U j k (X t))
            (fun a =>
              deriv (fun s => calendarLimitAction A E j k s a) t /
                deriv (fun s => A s j k) t))
        (ae (volume.restrict (Icc (0 : Real) T))) := by
  intro j k
  let mu := volume.restrict (Icc (0 : Real) T)
  have hAdiff :
      Filter.Eventually
        (fun t => DifferentiableAt Real (fun s => A s j k) t)
        (ae mu) := by
    have hv :=
      (hA j k).ae_differentiableAt.filter_mono
        (MeasureTheory.ae_restrict_le
          (μ := volume) (s := Icc (0 : Real) T))
    filter_upwards [ae_restrict_mem measurableSet_Icc, hv] with t ht hdt
    exact hdt (by simpa [uIcc_of_le hT.le] using ht)
  have hActionAc :=
    calendarLimitAction_ac A E hA hEac
  have hActionDiff (a : Option Buffer) :
      Filter.Eventually
        (fun t =>
          DifferentiableAt Real
            (fun s => calendarLimitAction A E j k s a) t)
        (ae mu) := by
    have hv :=
      (hActionAc j k a).ae_differentiableAt.filter_mono
        (MeasureTheory.ae_restrict_le
          (μ := volume) (s := Icc (0 : Real) T))
    filter_upwards [ae_restrict_mem measurableSet_Icc, hv] with t ht hdt
    exact hdt (by simpa [uIcc_of_le hT.le] using ht)
  have hfinite :
      Filter.Eventually
        (fun t => 0 < deriv (fun s => A s j k) t ->
          forall epsilon : {r : Real // 0 < r},
            Filter.Eventually
              (fun h =>
                N.tri_finiteDifferenceRatio
                    (fun s => A s j k)
                    (fun s => calendarLimitAction A E j k s) t h ∈
                  N.tri_fluidPolicyEpsilonCorrespondence
                    U j k (X t) epsilon.1)
              (nhdsWithin 0 (Ioi 0)))
        (ae mu) := by
    rw [show mu =
      volume.restrict (Ioo (0 : Real) T) by
        dsimp [mu]
        exact Measure.restrict_congr_set
          (Ioo_ae_eq_Icc (μ := volume) (a := (0 : Real)) (b := T)).symm]
    have hAdiffIoo :
        Filter.Eventually
          (fun t => t ∈ Icc (0 : Real) T ->
            DifferentiableAt Real (fun s => A s j k) t)
          (ae (volume.restrict (Ioo (0 : Real) T))) := by
      have hv := (hA j k).ae_differentiableAt.filter_mono
        (MeasureTheory.ae_restrict_le
          (μ := volume) (s := Ioo (0 : Real) T))
      filter_upwards [hv] with t ht hmem
      exact ht (by simpa [uIcc_of_le hT.le] using hmem)
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hAdiffIoo] with
      t ht hAt
    intro hpos epsilon
    obtain ⟨deltaNear, hdeltaNear, rNear, hrNear⟩ :=
      calendarPreActionStates_near N initial hT U K hK omega A X hA hconverges
        ht epsilon.2
    let delta := min deltaNear (T - t)
    have hdelta : 0 < delta := by
      exact lt_min hdeltaNear (sub_pos.mpr ht.2)
    have hslope :
        Filter.Eventually
          (fun h =>
            deriv (fun s => A s j k) t / 2 <
              h⁻¹ * (A (t + h) j k - A t j k))
          (nhdsWithin 0 (Ioi 0)) := by
      have hslopeT :=
        (hAt (Set.Ioo_subset_Icc_self ht)).hasDerivAt
          |>.tendsto_slope_zero_right
      exact (tendsto_order.mp hslopeT).1
        (deriv (fun s => A s j k) t / 2) (by linarith)
    have hsmall :
        Filter.Eventually (fun h : Real => h < delta)
          (nhdsWithin 0 (Ioi 0)) :=
      (eventually_lt_nhds hdelta).filter_mono inf_le_left
    filter_upwards [self_mem_nhdsWithin, hsmall, hslope] with
      h hh hhd hs
    have hhpos : 0 < h := hh
    have hhNear : h < deltaNear := hhd.trans_le (min_le_left _ _)
    have hth : t + h ∈ Icc (0 : Real) T := by
      have hhT : h < T - t := hhd.trans_le (min_le_right _ _)
      exact ⟨by linarith [ht.1], by linarith⟩
    have hden : 0 < A (t + h) j k - A t j k := by
      have hprod :
          0 < h⁻¹ * (A (t + h) j k - A t j k) :=
        (by linarith)
      exact pos_of_mul_pos_right hprod (inv_nonneg.mpr hh.le)
    apply calendarLimit_finiteDifference_mem_epsilon N initial hT U K hK omega A X hA hconverges q hq E hpoly ht
        epsilon.2 hhpos hth hden
    refine ⟨rNear, fun r hr l y hy hused => ?_⟩
    exact hrNear (q r) (hr.trans (hq.id_le r)) h hhpos hhNear
      j k l y hy hused
  exact N.tri_ae_tri_derivativeRatio_mem_fluidPolicyCorrespondence
    (TimeMeasure := mu) U j k X
    (fun s => A s j k)
    (fun s => calendarLimitAction A E j k s)
    hAdiff hActionDiff hfinite

theorem triangularCalendarExecutionFrom_stochasticFluidExtension :
    N.StochasticFluidExtensionReadback
      (N.triangularCalendarExecutionFrom initial) := by
  intro T hT x0 U K hK omega A X hX0 hA hconverges
  obtain ⟨q, hq, E, hEcont, hpoly⟩ :=
    exists_calendarPolygonalAllocation_limit N initial hT U K hK omega A X hA hconverges
  have hinput : IsFluidInput T A :=
    calendarInput_isFluidInput N initial hT U K omega A X hA hconverges
  have hraw :
      (N.triangularCalendarExecutionFrom initial).AllocationConvergesOn T U K q omega E :=
    calendarAllocation_raw_converges N initial hT U K hK omega A X hA hconverges q hq E hpoly
  have hE0 : forall i j k, E 0 i j k = 0 :=
    calendarLimit_allocation_initial N initial hT U K omega q E hpoly
  have hEincompat :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i j k, Not (N.compatible i j) -> E t i j k = 0 :=
    calendarLimit_allocation_incompatible N initial hT U K omega q E hpoly
  have hstate :
      forall t, t ∈ Icc (0 : Real) T -> IsFluidState (X t) :=
    calendarLimit_state_in_simplex N initial hT U K hK omega A X hA hconverges
  have hbalance :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i,
          X t i = x0 i
            + (Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun l : Buffer => E t l j i)
            - (Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun k : Buffer => E t i j k) :=
    calendarLimit_balance N initial hT x0 U K hK omega A X hX0 hA hconverges q hq E hpoly
  have hEac :
      forall i j k,
        AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T :=
    calendarLimit_allocation_ac N initial hT U K hK omega A X hA hconverges q hq E hpoly
  have hXac :
      forall i, AbsolutelyContinuousOnInterval (fun t => X t i) 0 T :=
    calendarLimit_state_ac N initial hT U K omega A X hA hconverges
  have hinc :
      forall i j k s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T -> s <= t ->
          0 <= E t i j k - E s i j k /\
          E t i j k - E s i j k <= A t j k - A s j k :=
    calendarLimit_allocation_increment N initial hT U K omega A q hq E hconverges.1 hraw
  have hbalanceRestricted :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i,
          X t i = x0 i
            + (Finset.univ.sum fun j : Server =>
                Finset.sum (N.buffersOf j) fun l => E t l j i)
            - (Finset.sum (N.serversOf i) fun j =>
                Finset.univ.sum fun k : Buffer => E t i j k) :=
    calendarLimit_balance_restricted N x0 X E hbalance hEincompat
  let Xclip : FluidStatePath Buffer :=
    fun t i => X (Set.projIcc (0 : Real) T hT.le t) i
  have hXclip_eq (t : Real) (ht : t ∈ Icc (0 : Real) T) :
      Xclip t = X t := by
    funext i
    simp only [Xclip, Set.projIcc_of_mem hT.le ht]
  have hXclipMeas (i : Buffer) : Measurable (fun t => Xclip t i) := by
    apply Continuous.measurable
    exact (hXac i).continuousOn.comp_continuous
      (continuous_subtype_val.comp
        (continuous_projIcc (a := (0 : Real)) (b := T)))
      (fun t => by
        simpa [uIcc_of_le hT.le] using
          (Set.projIcc (0 : Real) T hT.le t).property)
  let p : FluidActionFractions Buffer Server :=
    fun t j k =>
      N.tri_verifiedPatchedFluidPolicy U j k Xclip
        (fun s => A s j k)
        (fun s => calendarLimitAction A E j k s) t
  have hpositive (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => 0 < deriv (fun s => A s j k) t ->
          Membership.mem
            (N.fluidPolicyCorrespondence U j k (Xclip t))
            (fun a =>
              deriv (fun s => calendarLimitAction A E j k s a) t /
                deriv (fun s => A s j k) t))
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    have hp :=
      calendarLimit_positive_policy_ae N initial hT U K hK omega A X hA hconverges q hq E hpoly hEac j k
    filter_upwards [ae_restrict_mem measurableSet_Icc, hp] with t ht hpt
    simpa only [hXclip_eq t ht] using hpt
  have hzeroE :=
    calendarLimit_zero_derivative_ae hT A E hA hEac hinc
  have hAdiff (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => DifferentiableAt Real (fun s => A s j k) t)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    have hv := (hA j k).ae_differentiableAt.filter_mono
      (MeasureTheory.ae_restrict_le
        (μ := volume) (s := Icc (0 : Real) T))
    filter_upwards [ae_restrict_mem measurableSet_Icc, hv] with t ht hdt
    exact hdt (by simpa [uIcc_of_le hT.le] using ht)
  have hEdiff (i : Buffer) (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => DifferentiableAt Real (fun s => E s i j k) t)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    have hv := (hEac i j k).ae_differentiableAt.filter_mono
      (MeasureTheory.ae_restrict_le
        (μ := volume) (s := Icc (0 : Real) T))
    filter_upwards [ae_restrict_mem measurableSet_Icc, hv] with t ht hdt
    exact hdt (by simpa [uIcc_of_le hT.le] using ht)
  have hzero :
      Filter.Eventually
        (fun t => forall j k, deriv (fun s => A s j k) t = 0 ->
          forall a,
            deriv (fun s => calendarLimitAction A E j k s a) t = 0)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    filter_upwards [hzeroE,
      ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => hAdiff j k)),
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
        ae_all_iff.mpr (fun k => hEdiff i j k)))] with
        t hzeroEt hAdifft hEdifft
    intro j k hAzero a
    cases a with
    | some i =>
        simpa only [calendarLimitAction] using hzeroEt j k hAzero i
    | none =>
        have hA0 : HasDerivAt (fun s => A s j k) 0 t := by
          simpa only [hAzero] using (hAdifft j k).hasDerivAt
        have hsum0 :
            HasDerivAt
              (fun s => Finset.univ.sum fun i : Buffer => E s i j k)
              0 t := by
          have hs :=
            HasDerivAt.fun_sum (u := Finset.univ) fun i hi => by
              simpa only [hzeroEt j k hAzero i] using
                (hEdifft i j k).hasDerivAt
          exact hs.congr_deriv (by simp)
        change
          deriv
            ((fun s => A s j k) -
              (fun s => Finset.univ.sum fun i : Buffer => E s i j k)) t = 0
        simpa using (hA0.sub hsum0).deriv
  have hAnonneg (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => 0 <= deriv (fun s => A s j k) t)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    rw [<- Measure.restrict_congr_set
      (Ioo_ae_eq_Icc (μ := volume) (a := (0 : Real)) (b := T))]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [<- derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact (hinput.2.1 j k).derivWithin_nonneg
  have hAllocationRule (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => forall a,
          deriv (fun s => calendarLimitAction A E j k s a) t =
            deriv (fun s => A s j k) t * p t j k a)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    exact N.tri_tri_verifiedPatchedFluidPolicy_allocation_rule_ae
      (TimeMeasure := volume.restrict (Icc (0 : Real) T))
      U j k Xclip
      (fun s => A s j k)
      (fun s => calendarLimitAction A E j k s)
      (hAnonneg j k) (hpositive j k)
      (by
        filter_upwards [hzero] with t hzt
        exact hzt j k)
  refine ⟨q, hq, ?_⟩
  refine ⟨{
    horizon_pos := hT
    input_valid := hinput
    X := X
    E := E
    p := p
    state_ac := hXac
    allocation_ac := hEac
    state_initial := hX0
    allocation_initial := hE0
    allocation_incompatible := hEincompat
    state_in_simplex := hstate
    fractions_measurable := ?_
    fractions_in_simplex := ?_
    fractions_incompatible := ?_
    policy_rule := ?_
    allocation_rule := ?_
    balance := hbalanceRestricted
  }, rfl, ?_⟩
  · intro j k a
    exact N.tri_tri_verifiedPatchedFluidPolicy_coordinate_measurable
      U j k Xclip
      (fun s => A s j k)
      (fun s => calendarLimitAction A E j k s)
      hXclipMeas a
  · intro t ht j k
    apply N.tri_tri_verifiedPatchedFluidPolicy_isActionDistribution
    rw [hXclip_eq t ht]
    exact hstate t ht
  · intro t ht j k i hi
    apply N.tri_tri_verifiedPatchedFluidPolicy_incompatible_zero
    · rw [hXclip_eq t ht]
      exact hstate t ht
    · exact hi
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro j k
    rw [show X t = Xclip t by exact (hXclip_eq t ht).symm]
    exact N.tri_tri_verifiedPatchedFluidPolicy_mem U j k Xclip
      (fun s => A s j k)
      (fun s => calendarLimitAction A E j k s) t
      (by
        rw [hXclip_eq t ht]
        exact hstate t ht)
  · filter_upwards [
      ae_all_iff.mpr (fun j =>
        ae_all_iff.mpr (fun k => hAllocationRule j k))] with t ht
    intro i j k hij
    simpa only [calendarLimitAction] using ht j k (some i)
  · exact hraw

private theorem triangularInput_sum_dist_eventually_small
    {T epsilon : Real} (hT : 0 < T)
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hinput :
      UniformlyOnIcc T
        (fun r t (jk : Server × Buffer) =>
          N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
        (fun t jk => A t jk.1 jk.2))
    (hepsilon : 0 < epsilon) :
    exists n0 delta, 0 < delta /\
      forall n, n0 <= n ->
        forall s, s ∈ Icc (0 : Real) T ->
          forall t, t ∈ Icc (0 : Real) T ->
            |s - t| < delta ->
              Finset.univ.sum (fun jk : Server × Buffer =>
                dist
                  (N.totalCalendarScaledInput
                    (K n) (omega (K n)) s jk.1 jk.2)
                  (N.totalCalendarScaledInput
                    (K n) (omega (K n)) t jk.1 jk.2)) < epsilon := by
  let Avec : Real -> (Server × Buffer -> Real) :=
    fun t jk => A t jk.1 jk.2
  have hAvec : ContinuousOn Avec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro jk
    simpa [Avec, uIcc_of_le hT.le] using
      (hA jk.1 jk.2).continuousOn
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous hAvec
  let C : Real := (Fintype.card (Server × Buffer) : Real) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let eta := epsilon / (4 * C)
  have heta : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨delta, hdelta, hdeltaWorks⟩ :=
    Metric.uniformContinuousOn_iff.mp huc eta heta
  obtain ⟨n0, hn0⟩ := hinput eta heta
  refine ⟨n0, delta, hdelta, fun n hn s hs t ht hst => ?_⟩
  have hvec : dist (Avec s) (Avec t) < eta :=
    hdeltaWorks s hs t ht (by simpa [Real.dist_eq] using hst)
  have hterm (jk : Server × Buffer) :
      dist
          (N.totalCalendarScaledInput (K n) (omega (K n))
            s jk.1 jk.2)
          (N.totalCalendarScaledInput (K n) (omega (K n))
            t jk.1 jk.2) < 3 * eta := by
    have hs' := hn0 n hn s hs jk
    have ht' := hn0 n hn t ht jk
    have hcoord :
        dist (A s jk.1 jk.2) (A t jk.1 jk.2) < eta := by
      have hle :
          dist (Avec s jk) (Avec t jk) <= dist (Avec s) (Avec t) :=
        (dist_pi_le_iff dist_nonneg).mp
          (le_rfl : dist (Avec s) (Avec t) <= dist (Avec s) (Avec t)) jk
      simpa [Avec] using hle.trans_lt hvec
    calc
      _ <=
          dist
              (N.totalCalendarScaledInput (K n) (omega (K n))
                s jk.1 jk.2) (A s jk.1 jk.2) +
            dist (A s jk.1 jk.2) (A t jk.1 jk.2) +
            dist (A t jk.1 jk.2)
              (N.totalCalendarScaledInput (K n) (omega (K n))
                t jk.1 jk.2) := by
        calc
          _ <=
              dist
                  (N.totalCalendarScaledInput (K n) (omega (K n))
                    s jk.1 jk.2) (A s jk.1 jk.2) +
                dist (A s jk.1 jk.2)
                  (N.totalCalendarScaledInput (K n) (omega (K n))
                    t jk.1 jk.2) :=
            dist_triangle _ _ _
          _ <= _ := by
            have htri := dist_triangle
              (A s jk.1 jk.2)
              (A t jk.1 jk.2)
              (N.totalCalendarScaledInput (K n) (omega (K n))
                t jk.1 jk.2)
            linarith
      _ < eta + eta + eta := by
        exact add_lt_add (add_lt_add hs' hcoord)
          (by simpa [Real.dist_eq, abs_sub_comm] using ht')
      _ = 3 * eta := by ring
  calc
    _ < Finset.univ.sum (fun _ : Server × Buffer => 3 * eta) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun jk _ => hterm jk)
    _ = (Fintype.card (Server × Buffer) : Real) * (3 * eta) := by simp
    _ < epsilon := by
      dsimp [eta, C]
      have hc : (0 : Real) <= Fintype.card (Server × Buffer) := by positivity
      field_simp
      nlinarith

private theorem triangularCalendarPolygonalState_close
    {T : Real} (hT : 0 < T)
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hinput :
      UniformlyOnIcc T
        (fun r t (jk : Server × Buffer) =>
          N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
        (fun t jk => A t jk.1 jk.2)) :
    forall epsilon, 0 < epsilon ->
      exists n0, forall n, n0 <= n ->
        forall t, t ∈ Icc (0 : Real) T -> forall i,
          dist (N.calendarPolygonalState initial T U (K n) omega t i)
            (N.calendarScaledQueueStateFromInitial
              initial U (K n) omega t i) < epsilon := by
  intro epsilon hepsilon
  obtain ⟨nInput, delta, hdelta, hinput⟩ :=
    triangularInput_sum_dist_eventually_small
      N hT U K omega A hA hinput (by positivity : 0 < epsilon / 4)
  have hKreal :
      Tendsto (fun n => ((K n : Nat) : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (triangular_pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun n => T / ((K n : Nat) : Real)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  obtain ⟨nMesh, hnMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh delta hdelta
  refine ⟨max nInput nMesh, fun n hn t ht i => ?_⟩
  have hnI : nInput <= n := (le_max_left _ _).trans hn
  have hnM : nMesh <= n := (le_max_right _ _).trans hn
  have hmeshSmall : T / ((K n : Nat) : Real) < delta := by
    have h := hnMesh n hnM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at h
    exact h
  let r : Real := ((K n : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg (mul_nonneg (by positivity) ht.1) hT.le
  have hrK : r <= (K n : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hsum := fi_sum_hatWeight_eq_one (K n) hr0 hrK
  let raw := N.calendarScaledQueueStateFromInitial initial U (K n) omega t i
  have hterm (l : Nat) (hl : l ∈ Finset.range ((K n : Nat) + 1)) :
      |fi_hatWeight r l *
          (N.calendarScaledQueueStateFromInitial initial U (K n) omega
            (calendarGridTime T (K n) l) i - raw)| <=
        fi_hatWeight r l * (epsilon / 2) := by
    by_cases hw : fi_hatWeight r l = 0
    · simp [hw]
    · rw [abs_mul, abs_of_nonneg (fi_hatWeight_nonnegative r l)]
      apply mul_le_mul_of_nonneg_left _ (fi_hatWeight_nonnegative r l)
      apply le_of_lt
      have hlK : l <= (K n : Nat) := by
        have := Finset.mem_range.mp hl
        omega
      have hclose :
          |calendarGridTime T (K n) l - t| < delta := by
        have hd := fi_hatWeight_ne_zero_distance
          (K n) hT (Finset.mem_range.mp hl) hw
        rw [calendarGridTime_eq_ffGridTime T (K n) hlK]
        exact hd.trans_lt hmeshSmall
      have hs :=
        calendarScaledQueueStateFromInitial_dist_le
          N initial U (K n) omega (calendarGridTime T (K n) l) t i
      have hi := hinput n hnI
        (calendarGridTime T (K n) l)
        (calendarGridTime_mem_Icc hT (K n) hlK) t ht hclose
      rw [<- Real.dist_eq]
      exact hs.trans_lt (by nlinarith [hi])
  rw [Real.dist_eq]
  unfold calendarPolygonalState
  change
    |(Finset.sum (Finset.range ((K n : Nat) + 1)) fun l =>
        fi_hatWeight r l *
          N.calendarScaledQueueStateFromInitial initial U (K n) omega
            (calendarGridTime T (K n) l) i) - raw| < epsilon
  rw [show
    (Finset.sum (Finset.range ((K n : Nat) + 1)) fun l =>
      fi_hatWeight r l *
        N.calendarScaledQueueStateFromInitial initial U (K n) omega
          (calendarGridTime T (K n) l) i) - raw =
      Finset.sum (Finset.range ((K n : Nat) + 1)) (fun l =>
        fi_hatWeight r l *
          (N.calendarScaledQueueStateFromInitial initial U (K n) omega
            (calendarGridTime T (K n) l) i - raw)) by
      simp_rw [mul_sub, Finset.sum_sub_distrib, <- Finset.sum_mul,
        hsum, one_mul]]
  calc
    _ <= Finset.sum (Finset.range ((K n : Nat) + 1)) (fun l =>
        |fi_hatWeight r l *
          (N.calendarScaledQueueStateFromInitial initial U (K n) omega
            (calendarGridTime T (K n) l) i - raw)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum (Finset.range ((K n : Nat) + 1))
        (fun l => fi_hatWeight r l * (epsilon / 2)) :=
      Finset.sum_le_sum hterm
    _ = epsilon / 2 := by rw [<- Finset.sum_mul, hsum, one_mul]
    _ < epsilon := by linarith

/-- Compactness of genuinely triangular totalized calendar queue paths. -/
theorem triangularCalendarExecutionFrom_pairCompactness
    (T : Real) (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K)
    (omega : TriangularCalendarSample (Buffer := Buffer) (Server := Server))
    (A : MatrixPath Server Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hinput :
      UniformlyOnIcc T
        (fun r t (jk : Server × Buffer) =>
          N.totalCalendarScaledInput (K r) (omega (K r)) t jk.1 jk.2)
        (fun t jk => A t jk.1 jk.2)) :
    exists q : Nat -> Nat, StrictMono q /\
      exists X : FluidStatePath Buffer,
        (N.triangularCalendarExecutionFrom initial).PairConvergesOn
          T U (K ∘ q) omega A X := by
  let D := Icc (0 : Real) T
  letI : CompactSpace D := isCompact_iff_compactSpace.mp isCompact_Icc
  let f : Nat -> Real -> (Buffer -> Real) := fun n t =>
    N.calendarPolygonalState initial T U (K n) omega t
  have hf (n : Nat) : ContinuousOn (f n) (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    intro i
    exact (continuous_calendarPolygonalState
      N initial T U (K n) omega i).continuousOn
  have hclose := triangularCalendarPolygonalState_close
    N initial hT U K hK omega A hA hinput
  have hfamily :
      UniformEquicontinuous (fun n : Nat => fun t : D => f n t.1) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro epsilon hepsilon
    obtain ⟨nClose, hnClose⟩ := hclose (epsilon / 8) (by positivity)
    obtain ⟨nInput, deltaInput, hdeltaInput, hnInput⟩ :=
      triangularInput_sum_dist_eventually_small
        N hT U K omega A hA hinput
          (epsilon := epsilon / 4) (by positivity)
    let nTail := max nClose nInput
    have hprefix :
        UniformEquicontinuous
          (fun n : Fin nTail => fun t : D => f n.1 t.1) := by
      rw [uniformEquicontinuous_finite]
      intro n
      exact CompactSpace.uniformContinuous_of_continuous ((hf n.1).domRestrict)
    obtain ⟨deltaPrefix, hdeltaPrefix, hprefixWorks⟩ :=
      (Metric.uniformEquicontinuous_iff.mp hprefix) epsilon hepsilon
    refine ⟨min deltaInput deltaPrefix,
      lt_min hdeltaInput hdeltaPrefix, ?_⟩
    intro s t hst n
    by_cases hn : nTail <= n
    · have hsClose := hnClose n ((le_max_left _ _).trans hn) s.1 s.2
      have htClose := hnClose n ((le_max_left _ _).trans hn) t.1 t.2
      have hraw := calendarScaledQueueStateFromInitial_dist_le
        N initial U (K n) omega s.1 t.1
      have hin := hnInput n ((le_max_right _ _).trans hn)
        s.1 s.2 t.1 t.2 (by
          rw [<- Real.dist_eq]
          exact hst.trans_le (min_le_left _ _))
      apply (dist_pi_lt_iff (by positivity)).2
      intro i
      calc
        dist (f n s.1 i) (f n t.1 i) <=
            dist (f n s.1 i)
                (N.calendarScaledQueueStateFromInitial
                  initial U (K n) omega s.1 i) +
              dist
                (N.calendarScaledQueueStateFromInitial
                  initial U (K n) omega s.1 i)
                (N.calendarScaledQueueStateFromInitial
                  initial U (K n) omega t.1 i) +
              dist
                (N.calendarScaledQueueStateFromInitial
                  initial U (K n) omega t.1 i) (f n t.1 i) := by
          calc
            _ <= dist (f n s.1 i)
                  (N.calendarScaledQueueStateFromInitial
                    initial U (K n) omega s.1 i) +
                dist
                  (N.calendarScaledQueueStateFromInitial
                    initial U (K n) omega s.1 i) (f n t.1 i) :=
              dist_triangle _ _ _
            _ <= _ := by
              have htri := dist_triangle
                (N.calendarScaledQueueStateFromInitial
                  initial U (K n) omega s.1 i)
                (N.calendarScaledQueueStateFromInitial
                  initial U (K n) omega t.1 i)
                (f n t.1 i)
              linarith
        _ < epsilon / 8 + epsilon / 2 + epsilon / 8 := by
          exact add_lt_add
            (add_lt_add (hsClose i)
              ((hraw i).trans_lt (by nlinarith [hin])))
            (by simpa [dist_comm] using htClose i)
        _ < epsilon := by linarith
    · exact hprefixWorks s t
        (hst.trans_le (min_le_right _ _)) ⟨n, Nat.lt_of_not_ge hn⟩
  let F : Nat -> BoundedContinuousFunction D (Buffer -> Real) := fun n =>
    BoundedContinuousFunction.mkOfCompact
      (ContinuousMap.mk (fun t : D => f n t.1) ((hf n).domRestrict))
  let S : Set (BoundedContinuousFunction D (Buffer -> Real)) := Set.range F
  have hcompact : IsCompact (closure S) := by
    apply BoundedContinuousFunction.arzela_ascoli
      (Metric.closedBall (0 : Buffer -> Real) 1)
      (isCompact_closedBall (0 : Buffer -> Real) 1) S
    · intro p t hp
      obtain ⟨n, rfl⟩ := hp
      apply (dist_pi_le_iff (by norm_num)).2
      intro i
      have hi := (calendarPolygonalState_in_simplex
        N initial hT U (K n) omega t.2).1 i
      change
        |N.calendarPolygonalState initial T U (K n) omega t.1 i - 0| <= 1
      rw [sub_zero, abs_of_nonneg hi]
      calc
        _ <= Finset.univ.sum (fun b =>
              N.calendarPolygonalState initial T U (K n) omega t.1 b) :=
          Finset.single_le_sum
            (fun b _ => (calendarPolygonalState_in_simplex
              N initial hT U (K n) omega t.2).1 b)
            (Finset.mem_univ i)
        _ = 1 := (calendarPolygonalState_in_simplex
          N initial hT U (K n) omega t.2).2
    · let index : S -> Nat := fun p => Classical.choose p.2
      have hindex (p : S) : F (index p) = p.1 := Classical.choose_spec p.2
      intro t
      rw [Metric.equicontinuousAt_iff]
      intro epsilon hepsilon
      obtain ⟨delta, hdelta, hworks⟩ :=
        (Metric.equicontinuousAt_iff.mp (hfamily.equicontinuous t))
          epsilon hepsilon
      refine ⟨delta, hdelta, fun s hs p => ?_⟩
      rw [show p.1 t = F (index p) t by rw [hindex]]
      rw [show p.1 s = F (index p) s by rw [hindex]]
      exact hworks s hs (index p)
  obtain ⟨limitB, _, q, hq, hqconv⟩ :=
    hcompact.tendsto_subseq
      (fun n => subset_closure (show F n ∈ S from Set.mem_range_self n))
  let X : FluidStatePath Buffer := fun t =>
    if ht : t ∈ Icc (0 : Real) T then limitB ⟨t, ht⟩ else 0
  have hpoly :
      UniformlyOnIcc T
        (fun n t i => f (q n) t i) X := by
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := Metric.tendsto_atTop.mp hqconv epsilon hepsilon
    refine ⟨n0, fun n hn t ht i => ?_⟩
    have hcoord :=
      (dist_pi_le_iff dist_nonneg).mp
        (BoundedContinuousFunction.dist_coe_le_dist
          (f := F (q n)) (g := limitB) ⟨t, ht⟩) i
    have hXt : X t = limitB ⟨t, ht⟩ := by
      dsimp [X]
      rw [dif_pos ht]
    rw [hXt]
    change
      dist (f (q n) t i) (limitB ⟨t, ht⟩ i) <=
        dist (F (q n)) limitB at hcoord
    rw [Real.dist_eq] at hcoord
    exact hcoord.trans_lt (hn0 n hn)
  refine ⟨q, hq, X, ?_⟩
  constructor
  · intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := hinput epsilon hepsilon
    exact ⟨n0, fun n hn => hn0 (q n) (hn.trans (hq.id_le n))⟩
  · intro epsilon hepsilon
    obtain ⟨nC, hnC⟩ := hclose (epsilon / 2) (by positivity)
    obtain ⟨nP, hnP⟩ := hpoly (epsilon / 2) (by positivity)
    refine ⟨max nC nP, fun n hn t ht i => ?_⟩
    have hc := hnC (q n)
      ((le_max_left _ _).trans hn |>.trans (hq.id_le n)) t ht i
    have hp := hnP n ((le_max_right _ _).trans hn) t ht i
    rw [Real.dist_eq] at hc
    change
      |N.calendarScaledQueueStateFromInitial
          initial U (K (q n)) omega t i - X t i| < epsilon
    apply (abs_sub_le
      (N.calendarScaledQueueStateFromInitial
        initial U (K (q n)) omega t i)
      (f (q n) t i) (X t i)).trans_lt
    have hc' :
        |N.calendarScaledQueueStateFromInitial
            initial U (K (q n)) omega t i - f (q n) t i| <
          epsilon / 2 := by
      simpa [f, abs_sub_comm] using hc
    have hp' : |f (q n) t i - X t i| < epsilon / 2 := by
      simpa using hp
    nlinarith


end

end StateDepMOR.Network

namespace StateDepMOR.Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

/-- A varying sequence of regular calendar samples whose scaled calendar
paths converge in J1 to a finite-action path has a fluid-model subsequential
limit. The queue paths use the totalized execution that is defined on every
sample; regularity identifies it with the raw samples appearing in
`calendarPath`. -/
theorem exists_triangular_calendar_fluid_limit
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (H : Real) (hH : 0 < H)
    (K : Nat -> PNat) (hK : StrictMono K)
    (z : forall n, JobState Buffer (K n : Nat))
    (omega : Nat ->
      CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (a : PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H)
    (hregular :
      forall n, PoissonSamplePath.IsRegularSample (omega n))
    (hJ1 :
      Tendsto
        (fun n => PoissonSamplePath.calendarPath N H (K n) (omega n))
        atTop (nhds a))
    (hfinite :
      Ne
        (poissonPathRate N H (PoissonSamplePath.asMatrix H a))
        (Top.top : ENNReal)) :
    exists q : Nat -> Nat, StrictMono q /\
      exists (x0 : Simplex Buffer) (X : FluidStatePath Buffer)
        (s : N.FluidModelSolution U H x0
          (PoissonSamplePath.asMatrix H a)),
        Tendsto
            (fun r i =>
              ((z (q r) i : Nat) : Real) /
                ((K (q r) : Nat) : Real))
            atTop (nhds (fun i => x0 i)) /\
          UniformlyOnIcc H
            (fun r t i =>
              N.totalCalendarScaledQueueStateFrom
                U (K (q r)) (z (q r)) (omega (q r)) t i)
            X /\
          s.X = X := by
  let initial : forall L : PNat, JobState Buffer (L : Nat) :=
    fun L => by
      classical
      let jobs : Buffer -> Nat :=
        Function.extend K (fun n => (z n).jobs)
          (fun M => (N.eventInitialState M).jobs) L
      refine { jobs := jobs, total_jobs := ?_ }
      dsimp [jobs]
      rw [Function.extend_def]
      split_ifs with h
      · rw [(z (Classical.choose h)).total_jobs]
        exact congrArg Subtype.val (Classical.choose_spec h)
      · exact (N.eventInitialState L).total_jobs
  let clocks :
      TriangularCalendarSample (Buffer := Buffer) (Server := Server) :=
    Function.extend K omega (fun _ => default)
  have hinitial (n : Nat) : initial (K n) = z n := by
    classical
    apply JobState.ext
    funext i
    change
      Function.extend K (fun m => (z m).jobs)
          (fun M => (N.eventInitialState M).jobs) (K n) i =
        (z n).jobs i
    rw [hK.injective.extend_apply]
  have hclocks (n : Nat) : clocks (K n) = omega n := by
    dsimp [clocks]
    exact hK.injective.extend_apply omega (fun _ => default) n
  have htotal (n : Nat) :
      totalCalendarPoissonSample (omega n) = omega n := by
    funext j k
    exact totalUnitRateClock_eq_self
      ⟨(hregular n).1 j k, (hregular n).2 j k⟩
  have huniform :=
    PoissonSamplePath.j1_tendsto_uniform_of_finite_poissonPathRate
      N hH
      (fun n => PoissonSamplePath.calendarPath N H (K n) (omega n))
      a hfinite hJ1
  let A : MatrixPath Server Buffer := PoissonSamplePath.asMatrix H a
  have hA : IsAbsolutelyContinuousMatrixPath H A :=
    (poissonPathRate_ne_top_implies_valid N H A hfinite).1
  have hinput :
      UniformlyOnIcc H
        (fun r t (jk : Server × Buffer) =>
          N.totalCalendarScaledInput
            (K r) (clocks (K r)) t jk.1 jk.2)
        (fun t jk => A t jk.1 jk.2) := by
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := huniform epsilon hepsilon
    refine ⟨n0, fun n hn t ht jk => ?_⟩
    have hpath :=
      PoissonSamplePath.calendarPath_toFun_eq
        N H (K n) (omega n) (hregular n)
    have happ :
        PoissonSamplePath.calendarPath N H (K n) (omega n)
              ⟨t, ht⟩ jk.1 jk.2 =
            N.calendarScaledInput (K n) (omega n) t jk.1 jk.2 := by
      exact congrFun (congrFun (congrFun hpath ⟨t, ht⟩) jk.1) jk.2
    have hnear := hn0 n hn ⟨t, ht⟩ jk.1 jk.2
    change
      |N.totalCalendarScaledInput
          (K n) (clocks (K n)) t jk.1 jk.2 -
        A t jk.1 jk.2| < epsilon
    rw [show clocks (K n) = omega n from hclocks n,
      totalCalendarScaledInput, htotal n, <- happ]
    simpa only [A, PoissonSamplePath.asMatrix_apply_of_mem hH.le ht]
      using hnear
  obtain ⟨q0, hq0, X, hpair⟩ :=
    triangularCalendarExecutionFrom_pairCompactness
      N initial H hH U K hK clocks A hA hinput
  have hstate0 : IsFluidState (X 0) :=
    calendarLimit_state_in_simplex
      N initial hH U (K ∘ q0) (hK.comp hq0) clocks A X hA hpair
      0 ⟨le_rfl, hH.le⟩
  let x0 : Simplex Buffer :=
    { val := X 0
      nonneg := hstate0.1
      sum_eq_one := hstate0.2 }
  have hX0 : forall i, X 0 i = x0 i := by
    intro i
    rfl
  obtain ⟨q1, hq1, s, hsX, _⟩ :=
    triangularCalendarExecutionFrom_stochasticFluidExtension
      N initial H hH x0 U (K ∘ q0) (hK.comp hq0)
      clocks A X hX0 hA hpair
  let q : Nat -> Nat := q0 ∘ q1
  have hq : StrictMono q := hq0.comp hq1
  have hqueue :
      UniformlyOnIcc H
        (fun r t i =>
          N.totalCalendarScaledQueueStateFrom
            U (K (q r)) (z (q r)) (omega (q r)) t i)
        X := by
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := hpair.2 epsilon hepsilon
    refine ⟨n0, fun n hn t ht i => ?_⟩
    have hnear :=
      hn0 (q1 n) (hn.trans (hq1.id_le n)) t ht i
    change
      |N.totalCalendarScaledQueueStateFrom
          U (K (q0 (q1 n))) (initial (K (q0 (q1 n))))
            (clocks (K (q0 (q1 n)))) t i -
        X t i| < epsilon at hnear
    rw [hinitial (q0 (q1 n)), hclocks (q0 (q1 n))] at hnear
    change
      |N.totalCalendarScaledQueueStateFrom
          U (K (q n)) (z (q n)) (omega (q n)) t i - X t i| <
        epsilon
    simpa only [q, Function.comp_apply] using hnear
  have hinitialConv :
      Tendsto
        (fun r i =>
          ((z (q r) i : Nat) : Real) /
            ((K (q r) : Nat) : Real))
        atTop (nhds (fun i => x0 i)) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨n0, hn0⟩ := hpair.2 epsilon hepsilon
    refine ⟨n0, fun n hn => ?_⟩
    have hzero :=
      hn0 (q1 n) (hn.trans (hq1.id_le n))
        0 ⟨le_rfl, hH.le⟩ i
    change
      |N.totalCalendarScaledQueueStateFrom
          U (K (q0 (q1 n))) (initial (K (q0 (q1 n))))
            (clocks (K (q0 (q1 n)))) 0 i -
        X 0 i| < epsilon at hzero
    simpa [q, Function.comp_apply,
      StateDepMOR.Network.totalCalendarScaledQueueStateFrom,
      totalCalendarTokenPrefix_zero N,
      StateDepMOR.Network.runTokens, hinitial, hX0 i,
      Real.dist_eq] using hzero
  exact ⟨q, hq, x0, X, s, hinitialConv, hqueue, hsX⟩

private theorem totalCalendarPoissonSample_idempotent
    (omega : CalendarPoissonSample
      (Buffer := Buffer) (Server := Server)) :
    totalCalendarPoissonSample (totalCalendarPoissonSample omega) =
      totalCalendarPoissonSample omega := by
  funext j k
  exact totalUnitRateClock_eq_self
    (totalUnitRateClock_isUsable (omega j k))

private theorem totalCalendarScaledQueueStateFrom_totalized
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (K : PNat) (z : JobState Buffer (K : Nat))
    (omega : CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (t : Real) (i : Buffer) :
    N.totalCalendarScaledQueueStateFrom U K z
        (totalCalendarPoissonSample omega) t i =
      N.totalCalendarScaledQueueStateFrom U K z omega t i := by
  simp only [totalCalendarScaledQueueStateFrom, totalCalendarTokenPrefix,
    totalChronologicalCalendarEvents, totalRawCalendarEvents,
    totalCalendarEventOrderKey, totalCalendarEventTime,
    totalCalendarPoissonSample_idempotent]
  rfl

/-- Unconditional triangular fluid extraction for arbitrary calendar samples.
The J1 premise uses the same totalization as the queue execution. This is the
literal pathwise statement available without regularity: a raw exceptional
sample may produce the fallback zero `calendarPath`, while execution replaces
its unusable clocks by unit clocks. -/
theorem exists_triangular_totalized_calendar_fluid_limit
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (H : Real) (hH : 0 < H)
    (K : Nat -> PNat) (hK : StrictMono K)
    (z : forall n, JobState Buffer (K n : Nat))
    (omega : Nat ->
      CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (a : PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H)
    (hJ1 :
      Tendsto
        (fun n =>
          PoissonSamplePath.calendarPath N H (K n)
            (totalCalendarPoissonSample (omega n)))
        atTop (nhds a))
    (hfinite :
      Ne
        (poissonPathRate N H (PoissonSamplePath.asMatrix H a))
        (Top.top : ENNReal)) :
    exists q : Nat -> Nat, StrictMono q /\
      exists (x0 : Simplex Buffer) (X : FluidStatePath Buffer)
        (s : N.FluidModelSolution U H x0
          (PoissonSamplePath.asMatrix H a)),
        Tendsto
            (fun r i =>
              ((z (q r) i : Nat) : Real) /
                ((K (q r) : Nat) : Real))
            atTop (nhds (fun i => x0 i)) /\
          UniformlyOnIcc H
            (fun r t i =>
              N.totalCalendarScaledQueueStateFrom
                U (K (q r)) (z (q r)) (omega (q r)) t i)
            X /\
          s.X = X := by
  let omegaTotal : Nat ->
      CalendarPoissonSample (Buffer := Buffer) (Server := Server) :=
    fun n => totalCalendarPoissonSample (omega n)
  have hregular :
      forall n, PoissonSamplePath.IsRegularSample (omegaTotal n) := by
    intro n
    constructor
    · exact fun j k r => totalCalendarPoissonSample_pos (omega n) j k r
    · exact fun j k =>
        totalCalendarPoissonSample_ratio_tendsto (omega n) j k
  obtain ⟨q, hq, x0, X, s, hinitial, hqueue, hsX⟩ :=
    exists_triangular_calendar_fluid_limit
      N U H hH K hK z omegaTotal a hregular hJ1 hfinite
  refine ⟨q, hq, x0, X, s, hinitial, ?_, hsX⟩
  intro epsilon hepsilon
  obtain ⟨n0, hn0⟩ := hqueue epsilon hepsilon
  refine ⟨n0, fun n hn t ht i => ?_⟩
  simpa only [omegaTotal,
    totalCalendarScaledQueueStateFrom_totalized] using
      hn0 n hn t ht i

private theorem triangular_queue_tendsto_at
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    {H : Real} {K : Nat -> PNat}
    {z : forall n, JobState Buffer (K n : Nat)}
    {omega : Nat ->
      CalendarPoissonSample (Buffer := Buffer) (Server := Server)}
    {q : Nat -> Nat} {X : FluidStatePath Buffer}
    (hqueue :
      UniformlyOnIcc H
        (fun r t i =>
          N.totalCalendarScaledQueueStateFrom
            U (K (q r)) (z (q r)) (omega (q r)) t i)
        X)
    {t : Real} (ht : t ∈ Icc (0 : Real) H) :
    Tendsto
      (fun r i =>
        N.totalCalendarScaledQueueStateFrom
          U (K (q r)) (z (q r)) (omega (q r)) t i)
      atTop (nhds (X t)) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨r0, hr0⟩ := hqueue epsilon hepsilon
  exact ⟨r0, fun r hr => by
    simpa [Real.dist_eq] using hr0 r hr t ht i⟩

private theorem continuous_lAlphaAmbient
    (alpha : Simplex Buffer) :
    Continuous
      (fun x : Buffer -> Real =>
        Lyapunov.LAlphaAmbient (fun i => alpha i) x) := by
  unfold Lyapunov.LAlphaAmbient Lyapunov.minCoordinate
  fun_prop

private theorem lAlphaAmbient_le_one_of_nonneg
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (x : Buffer -> Real) (hx : forall i, 0 <= x i) :
    Lyapunov.LAlphaAmbient (fun i => alpha i) x <= 1 := by
  have hmin :
      0 <= Lyapunov.minCoordinate (fun i => x i / alpha i) := by
    unfold Lyapunov.minCoordinate
    apply Finset.le_inf' Finset.univ_nonempty
    intro i _hi
    exact div_nonneg (hx i) (halpha i).le
  unfold Lyapunov.LAlphaAmbient
  linarith

/-- A continuous fluid path that starts strictly below the queue boundary
and reaches it at the horizon has a first boundary hit. Selecting the first
hit restores the strict pre-hit condition, which is not itself closed under
uniform convergence. -/
private theorem exists_first_lAlpha_boundary_hit
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    {H : Real} {x0 : Simplex Buffer} {A : MatrixPath Server Buffer}
    (s : N.FluidModelSolution U H x0 A)
    (hstart :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) < 1)
    (hitAt : Real) (hhitAt : hitAt ∈ Icc (0 : Real) H)
    (hend :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X hitAt) = 1) :
    exists tau : Real,
      tau ∈ Icc (0 : Real) H /\
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X tau) = 1 /\
        forall t, t ∈ Ico (0 : Real) tau ->
          Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1 := by
  let g : Real -> Real :=
    fun t => Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t)
  have hXcont : ContinuousOn s.X (Icc (0 : Real) H) := by
    rw [continuousOn_pi]
    intro i
    simpa only [uIcc_of_le s.horizon_pos.le] using
      (s.state_ac i).continuousOn
  have hgcont : ContinuousOn g (Icc (0 : Real) H) :=
    (continuous_lAlphaAmbient alpha).comp_continuousOn hXcont
  let hit : Set Real :=
    Icc (0 : Real) H ∩ {t | g t = 1}
  have hhitClosed : IsClosed hit := by
    change IsClosed (Icc (0 : Real) H ∩ g ⁻¹' ({1} : Set Real))
    exact hgcont.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_singleton
  have hhitCompact : IsCompact hit :=
    isCompact_Icc.of_isClosed_subset hhitClosed inter_subset_left
  have hhitNonempty : hit.Nonempty := by
    refine ⟨hitAt, ⟨hhitAt, ?_⟩⟩
    exact hend
  obtain ⟨tau, htauLeast⟩ :=
    hhitCompact.exists_isLeast hhitNonempty
  have htauMem : tau ∈ Icc (0 : Real) H := htauLeast.1.1
  have htauHit : g tau = 1 := htauLeast.1.2
  have htauPos : 0 < tau := by
    by_contra hnot
    have htauZero : tau = 0 := le_antisymm (not_lt.mp hnot) htauMem.1
    subst tau
    exact (ne_of_lt hstart) htauHit
  refine ⟨tau, htauMem, htauHit, ?_⟩
  intro t ht
  have htMem : t ∈ Icc (0 : Real) H :=
    ⟨ht.1, (le_of_lt ht.2).trans htauMem.2⟩
  have hupper : g t <= 1 :=
    lAlphaAmbient_le_one_of_nonneg alpha halpha (s.X t)
      (s.state_in_simplex t htMem).1
  have hne : Not (g t = 1) := by
    intro heq
    have htHit : t ∈ hit := ⟨htMem, heq⟩
    exact (not_le_of_gt ht.2) (htauLeast.2 htHit)
  exact lt_of_le_of_ne hupper hne

/-- Tail closure for term (b), with arbitrary varying calendar samples and
row-dependent boundary-hit times. Compactness of `[0,H]` supplies a limiting
hit time. The resulting fluid path is then stopped at its first boundary hit,
which gives the strict pre-hit condition used by the excursion rate bound. -/
theorem exists_triangular_totalized_calendar_fluid_excursion
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (rho H : Real) (hrho : rho < 1) (hH : 0 < H)
    (K : Nat -> PNat) (hK : StrictMono K)
    (z : forall n, JobState Buffer (K n : Nat))
    (omega : Nat ->
      CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (a : PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H)
    (hitTime : Nat -> Real)
    (hhitTime : forall n, hitTime n ∈ Icc (0 : Real) H)
    (hJ1 :
      Tendsto
        (fun n =>
          PoissonSamplePath.calendarPath N H (K n)
            (totalCalendarPoissonSample (omega n)))
        atTop (nhds a))
    (hfinite :
      Ne
        (poissonPathRate N H (PoissonSamplePath.asMatrix H a))
        (Top.top : ENNReal))
    (hstart :
      forall n,
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U (K n) (z n) (omega n) 0 i) <= rho)
    (hhit :
      forall n,
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U (K n) (z n) (omega n) (hitTime n) i) = 1) :
    exists (x0 : Simplex Buffer)
      (s : N.FluidModelSolution U H x0
        (PoissonSamplePath.asMatrix H a))
      (tau : Real),
      tau ∈ Icc (0 : Real) H /\
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho /\
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X tau) = 1 /\
        forall t, t ∈ Ico (0 : Real) tau ->
          Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1 := by
  let finiteHit : Nat -> PoissonSamplePath.Horizon H :=
    fun n => ⟨hitTime n, hhitTime n⟩
  obtain ⟨limitHit, p, hp, hpconv⟩ :=
    CompactSpace.tendsto_subseq finiteHit
  let K1 : Nat -> PNat := K ∘ p
  let z1 : forall n, JobState Buffer (K1 n : Nat) :=
    fun n => z (p n)
  let omega1 : Nat ->
      CalendarPoissonSample (Buffer := Buffer) (Server := Server) :=
    fun n => omega (p n)
  have hJ1sub :
      Tendsto
        (fun n =>
          PoissonSamplePath.calendarPath N H (K1 n)
            (totalCalendarPoissonSample (omega1 n)))
        atTop (nhds a) := by
    convert hJ1.comp hp.tendsto_atTop using 1
    funext n
    rfl
  obtain ⟨q, hq, x0, X, s, _hinitial, hqueue, hsX⟩ :=
    exists_triangular_totalized_calendar_fluid_limit
      N U H hH K1 (hK.comp hp) z1 omega1 a hJ1sub hfinite
  have hL0 :
      Tendsto
        (fun r =>
          Lyapunov.LAlphaAmbient (fun i => alpha i)
            (fun i =>
              N.totalCalendarScaledQueueStateFrom
                U (K1 (q r)) (z1 (q r)) (omega1 (q r)) 0 i))
        atTop
        (nhds (Lyapunov.LAlphaAmbient (fun i => alpha i) (X 0))) :=
    (continuous_lAlphaAmbient alpha).continuousAt.tendsto.comp
      (triangular_queue_tendsto_at N U hqueue
        ⟨le_rfl, hH.le⟩)
  have hstartLimit :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (X 0) <= rho :=
    le_of_tendsto' hL0 (fun r => hstart (p (q r)))
  let movingHit : Nat -> PoissonSamplePath.Horizon H :=
    fun r => finiteHit (p (q r))
  have hmovingHit :
      Tendsto movingHit atTop (nhds limitHit) := by
    convert hpconv.comp hq.tendsto_atTop using 1
    funext r
    rfl
  have hXcont : ContinuousOn X (Icc (0 : Real) H) := by
    rw [<- hsX, continuousOn_pi]
    intro i
    simpa only [uIcc_of_le hH.le] using (s.state_ac i).continuousOn
  have hXmoving :
      Tendsto (fun r => X (movingHit r)) atTop (nhds (X limitHit)) :=
    hXcont.domRestrict.continuousAt.tendsto.comp hmovingHit
  have hqueueMoving :
      Tendsto
        (fun r i =>
          N.totalCalendarScaledQueueStateFrom
            U (K1 (q r)) (z1 (q r)) (omega1 (q r))
              (movingHit r) i)
        atTop (nhds (X limitHit)) := by
    rw [tendsto_pi_nhds]
    intro i
    have hXcoord :
        Tendsto (fun r => X (movingHit r) i) atTop
          (nhds (X limitHit i)) :=
      (continuous_apply i).continuousAt.tendsto.comp hXmoving
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨nQueue, hnQueue⟩ := hqueue (epsilon / 2) (by positivity)
    obtain ⟨nX, hnX⟩ :=
      Metric.tendsto_atTop.mp hXcoord (epsilon / 2) (by positivity)
    refine ⟨max nQueue nX, fun r hr => ?_⟩
    have hqclose :=
      hnQueue r ((le_max_left _ _).trans hr)
        (movingHit r) (movingHit r).property i
    have hxclose := hnX r ((le_max_right _ _).trans hr)
    rw [Real.dist_eq] at hxclose ⊢
    apply (abs_sub_le
      (N.totalCalendarScaledQueueStateFrom
        U (K1 (q r)) (z1 (q r)) (omega1 (q r)) (movingHit r) i)
      (X (movingHit r) i) (X limitHit i)).trans_lt
    linarith
  have hLHit :
      Tendsto
        (fun r =>
          Lyapunov.LAlphaAmbient (fun i => alpha i)
            (fun i =>
              N.totalCalendarScaledQueueStateFrom
                U (K1 (q r)) (z1 (q r)) (omega1 (q r))
                  (movingHit r) i))
        atTop
        (nhds
          (Lyapunov.LAlphaAmbient (fun i => alpha i) (X limitHit))) :=
    (continuous_lAlphaAmbient alpha).continuousAt.tendsto.comp
      hqueueMoving
  have hhitLimit :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (X limitHit) = 1 := by
    apply tendsto_nhds_unique hLHit
    simpa only [K1, z1, omega1, movingHit, finiteHit,
      Function.comp_apply, hhit] using
      (tendsto_const_nhds :
        Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1))
  have hsStart :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho := by
    simpa only [hsX] using hstartLimit
  have hsHit :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X limitHit) = 1 := by
    simpa only [hsX] using hhitLimit
  obtain ⟨tau, htau, hhitFirst, hbefore⟩ :=
    exists_first_lAlpha_boundary_hit
      N U alpha halpha s (hsStart.trans_lt hrho)
        limitHit limitHit.property hsHit
  exact ⟨x0, s, tau, htau, hsStart, hhitFirst, hbefore⟩

/-- Tail closure for the repaired term (c), with arbitrary varying calendar
samples. Strict finite avoidance `L < 1` closes to `L <= 1`; retaining a
strict upper bound here would be false under uniform convergence. -/
theorem exists_triangular_totalized_calendar_fluid_persistence
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (alpha : Simplex Buffer)
    (delta rho H : Real) (hH : 0 < H)
    (K : Nat -> PNat) (hK : StrictMono K)
    (z : forall n, JobState Buffer (K n : Nat))
    (omega : Nat ->
      CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (a : PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H)
    (hJ1 :
      Tendsto
        (fun n =>
          PoissonSamplePath.calendarPath N H (K n)
            (totalCalendarPoissonSample (omega n)))
        atTop (nhds a))
    (hfinite :
      Ne
        (poissonPathRate N H (PoissonSamplePath.asMatrix H a))
        (Top.top : ENNReal))
    (hstart :
      forall n,
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U (K n) (z n) (omega n) 0 i) <= rho)
    (hband :
      forall n t, t ∈ Icc (0 : Real) H ->
        delta <=
            Lyapunov.LAlphaAmbient (fun i => alpha i)
              (fun i =>
                N.totalCalendarScaledQueueStateFrom
                  U (K n) (z n) (omega n) t i) /\
          Lyapunov.LAlphaAmbient (fun i => alpha i)
              (fun i =>
                N.totalCalendarScaledQueueStateFrom
                  U (K n) (z n) (omega n) t i) < 1) :
    exists (x0 : Simplex Buffer)
      (s : N.FluidModelSolution U H x0
        (PoissonSamplePath.asMatrix H a)),
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho /\
        forall t, t ∈ Icc (0 : Real) H ->
          delta <= Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) /\
            Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) <= 1 := by
  obtain ⟨q, _hq, x0, X, s, _hinitial, hqueue, hsX⟩ :=
    exists_triangular_totalized_calendar_fluid_limit
      N U H hH K hK z omega a hJ1 hfinite
  have hL (t : Real) (ht : t ∈ Icc (0 : Real) H) :
      Tendsto
        (fun r =>
          Lyapunov.LAlphaAmbient (fun i => alpha i)
            (fun i =>
              N.totalCalendarScaledQueueStateFrom
                U (K (q r)) (z (q r)) (omega (q r)) t i))
        atTop
        (nhds (Lyapunov.LAlphaAmbient (fun i => alpha i) (X t))) :=
    (continuous_lAlphaAmbient alpha).continuousAt.tendsto.comp
      (triangular_queue_tendsto_at N U hqueue ht)
  have hstartLimit :
      Lyapunov.LAlphaAmbient (fun i => alpha i) (X 0) <= rho :=
    le_of_tendsto' (hL 0 ⟨le_rfl, hH.le⟩) (fun r => hstart (q r))
  refine ⟨x0, s, ?_, ?_⟩
  · simpa only [hsX] using hstartLimit
  · intro t ht
    have hlo :
        delta <= Lyapunov.LAlphaAmbient (fun i => alpha i) (X t) :=
      ge_of_tendsto' (hL t ht) (fun r => (hband (q r) t ht).1)
    have hhi :
        Lyapunov.LAlphaAmbient (fun i => alpha i) (X t) <= 1 :=
      le_of_tendsto' (hL t ht) (fun r => (hband (q r) t ht).2.le)
    simpa only [hsX] using And.intro hlo hhi

private theorem totalCalendarPoissonSample_eq_self_of_regular
    (omega : CalendarPoissonSample
      (Buffer := Buffer) (Server := Server))
    (hregular : PoissonSamplePath.IsRegularSample omega) :
    totalCalendarPoissonSample omega = omega := by
  funext j k
  exact totalUnitRateClock_eq_self
    ⟨hregular.1 j k, hregular.2 j k⟩

/-- Raw-path form of the excursion tail closure. The explicit regularity
hypothesis is exactly what identifies raw `calendarPath` with the totalized
execution used for finite queue trajectories. -/
theorem exists_triangular_calendar_fluid_excursion
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (rho H : Real) (hrho : rho < 1) (hH : 0 < H)
    (K : Nat -> PNat) (hK : StrictMono K)
    (z : forall n, JobState Buffer (K n : Nat))
    (omega : Nat ->
      CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (a : PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H)
    (hitTime : Nat -> Real)
    (hhitTime : forall n, hitTime n ∈ Icc (0 : Real) H)
    (hregular :
      forall n, PoissonSamplePath.IsRegularSample (omega n))
    (hJ1 :
      Tendsto
        (fun n => PoissonSamplePath.calendarPath N H (K n) (omega n))
        atTop (nhds a))
    (hfinite :
      Ne
        (poissonPathRate N H (PoissonSamplePath.asMatrix H a))
        (Top.top : ENNReal))
    (hstart :
      forall n,
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U (K n) (z n) (omega n) 0 i) <= rho)
    (hhit :
      forall n,
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U (K n) (z n) (omega n) (hitTime n) i) = 1) :
    exists (x0 : Simplex Buffer)
      (s : N.FluidModelSolution U H x0
        (PoissonSamplePath.asMatrix H a))
      (tau : Real),
      tau ∈ Icc (0 : Real) H /\
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho /\
        Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X tau) = 1 /\
        forall t, t ∈ Ico (0 : Real) tau ->
          Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) < 1 := by
  have hJ1total :
      Tendsto
        (fun n =>
          PoissonSamplePath.calendarPath N H (K n)
            (totalCalendarPoissonSample (omega n)))
        atTop (nhds a) := by
    convert hJ1 using 1
    funext n
    rw [totalCalendarPoissonSample_eq_self_of_regular
      (omega n) (hregular n)]
  exact exists_triangular_totalized_calendar_fluid_excursion
    N U alpha halpha rho H hrho hH K hK z omega a hitTime hhitTime
      hJ1total hfinite hstart hhit

/-- Raw-path form of the boundary-inclusive persistence tail closure. -/
theorem exists_triangular_calendar_fluid_persistence
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence)
    (alpha : Simplex Buffer)
    (delta rho H : Real) (hH : 0 < H)
    (K : Nat -> PNat) (hK : StrictMono K)
    (z : forall n, JobState Buffer (K n : Nat))
    (omega : Nat ->
      CalendarPoissonSample (Buffer := Buffer) (Server := Server))
    (a : PoissonSamplePath.Path
      (Buffer := Buffer) (Server := Server) H)
    (hregular :
      forall n, PoissonSamplePath.IsRegularSample (omega n))
    (hJ1 :
      Tendsto
        (fun n => PoissonSamplePath.calendarPath N H (K n) (omega n))
        atTop (nhds a))
    (hfinite :
      Ne
        (poissonPathRate N H (PoissonSamplePath.asMatrix H a))
        (Top.top : ENNReal))
    (hstart :
      forall n,
        Lyapunov.LAlphaAmbient (fun i => alpha i)
          (fun i =>
            N.totalCalendarScaledQueueStateFrom
              U (K n) (z n) (omega n) 0 i) <= rho)
    (hband :
      forall n t, t ∈ Icc (0 : Real) H ->
        delta <=
            Lyapunov.LAlphaAmbient (fun i => alpha i)
              (fun i =>
                N.totalCalendarScaledQueueStateFrom
                  U (K n) (z n) (omega n) t i) /\
          Lyapunov.LAlphaAmbient (fun i => alpha i)
              (fun i =>
                N.totalCalendarScaledQueueStateFrom
                  U (K n) (z n) (omega n) t i) < 1) :
    exists (x0 : Simplex Buffer)
      (s : N.FluidModelSolution U H x0
        (PoissonSamplePath.asMatrix H a)),
      Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X 0) <= rho /\
        forall t, t ∈ Icc (0 : Real) H ->
          delta <= Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) /\
            Lyapunov.LAlphaAmbient (fun i => alpha i) (s.X t) <= 1 := by
  have hJ1total :
      Tendsto
        (fun n =>
          PoissonSamplePath.calendarPath N H (K n)
            (totalCalendarPoissonSample (omega n)))
        atTop (nhds a) := by
    convert hJ1 using 1
    funext n
    rw [totalCalendarPoissonSample_eq_self_of_regular
      (omega n) (hregular n)]
  exact exists_triangular_totalized_calendar_fluid_persistence
    N U alpha delta rho H hH K hK z omega a hJ1total hfinite
      hstart hband

end StateDepMOR.Network
