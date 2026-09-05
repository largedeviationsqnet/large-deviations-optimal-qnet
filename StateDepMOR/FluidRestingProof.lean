import StateDepMOR.ConverseProofs
import StateDepMOR.FluidConsistency
import StateDepMOR.FiniteQueueTrajectories
import StateDepMOR.EventEpochExecution
import StateDepMOR.PoissonProcessExecution
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fin.Tuple.Take

open Filter Set

namespace FluidControlledCompactness

/-- Arzela-Ascoli extraction when increments are bounded by a finite family
of uniformly convergent continuous real controls. -/
theorem exists_uniformly_convergent_subsequence_of_controlled_increments
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
theorem exists_uniformly_convergent_subsequence_real
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
theorem exists_uniformly_convergent_subsequence_finite
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
theorem absolutelyContinuousOnInterval_of_dist_le_finset
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
theorem dist_le_finset_of_uniform_limit
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
theorem dist_le_finset_of_uniform_limits
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
theorem absolutelyContinuousOnInterval_of_uniform_limits_finset
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
theorem absolutelyContinuousOnInterval_of_uniform_limit_finset
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
theorem exists_uniformly_convergent_subsequence_of_lipschitzOn
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
noncomputable def fluidGridInterpolate
    (K : PNat) (u : Nat -> Real) (t : Real) : Real :=
  let r := max t 0 * ((K : Nat) : Real)
  let n := Nat.floor r
  u n + (r - (n : Real)) * (u (n + 1) - u n)

/-- The polygonal interpolation agrees with the data at every grid node. -/
theorem fluidGridInterpolate_nat_div
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
theorem fluidGridInterpolate_sub_step_abs_le
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

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

namespace Network

variable (N : Network Buffer Server)

theorem ff_runTokens_append {K : Nat}
    (U : N.DeterministicStationaryPolicy K) (x : JobState Buffer K)
    (xs ys : List (TokenType (Buffer := Buffer) (Server := Server))) :
    N.runTokens U x (xs ++ ys) =
      N.runTokens U (N.runTokens U x xs) ys := by
  induction xs generalizing x with
  | nil => simp [runTokens]
  | cons jk xs ih =>
      simp only [List.cons_append, runTokens]
      exact ih (N.queueStep U x jk)

theorem ff_runAllocationCount_append {K : Nat}
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

theorem ff_runAllocationCount_incompatible {K : Nat}
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

theorem ff_runAllocationCount_le_count {K : Nat}
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

theorem ff_runTokens_runAllocationCount_balance {K : Nat}
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

theorem ff_sum_runAllocationCount_le_length {K : Nat}
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

theorem ff_runTokens_l1_le_two_mul_length {K : Nat}
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

theorem ff_runAllocationCount_batch_increment_le_length {K : Nat}
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

theorem ff_runTokens_batch_l1_le_two_mul_length {K : Nat}
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

noncomputable def ff_gridTime
    (T : Real) (K : PNat) (l : Nat) : Real :=
  T * ((min l (K : Nat) : Nat) : Real) / (K : Nat)

noncomputable def ff_gridInputCount
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) (j : Server) (k : Buffer) : Nat :=
  Nat.floor (((K : Nat) : Real) * A (ff_gridTime T K l) j k)

noncomputable def ff_gridTokenBatch
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

noncomputable def ff_gridTokenPrefix
    (T : Real) (A : MatrixPath Server Buffer)
    (K : PNat) : Nat ->
      List (TokenType (Buffer := Buffer) (Server := Server))
  | 0 => []
  | l + 1 =>
      ff_gridTokenPrefix T A K l ++ ff_gridTokenBatch T A K l

theorem ff_gridTime_mem_Icc
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

theorem ff_gridTime_mono
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

theorem ff_gridInputCount_mono
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

theorem ff_gridInputCount_zero
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

theorem ff_gridTokenBatch_count
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

theorem ff_gridTokenPrefix_count
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

def ff_clamp01 (r : Real) : Real :=
  max 0 (min 1 r)

theorem ff_clamp01_monotone : Monotone ff_clamp01 := by
  intro r s hrs
  unfold ff_clamp01
  exact max_le_max_left 0 (min_le_min_left 1 hrs)

theorem ff_clamp01_of_nonpos {r : Real} (hr : r <= 0) :
    ff_clamp01 r = 0 := by
  unfold ff_clamp01
  simp [min_eq_right hr, hr]

theorem ff_clamp01_of_one_le {r : Real} (hr : 1 <= r) :
    ff_clamp01 r = 1 := by
  unfold ff_clamp01
  simp [min_eq_left hr, hr]

noncomputable def ff_rampInterpolate
    (K : PNat) (values : Nat -> Real) (t T : Real) : Real :=
  values 0 +
    Finset.sum (Finset.range (K : Nat)) fun l =>
      (values (l + 1) - values l) *
        ff_clamp01 (((K : Nat) : Real) * t / T - l)

noncomputable def ff_polygonalInputPath
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

theorem ff_rampInterpolate_grid
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

theorem ff_gridTime_eq_gridPoint
    (T : Real) (K : PNat) (l : Nat) (hl : l <= (K : Nat)) :
    ff_gridTime T K l = T * (l : Real) / (K : Nat) := by
  simp [ff_gridTime, Nat.min_eq_left hl]

theorem ff_polygonalInputPath_grid
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) (hl : l <= (K : Nat))
    (j : Server) (k : Buffer) :
    ff_polygonalInputPath T A K (ff_gridTime T K l) j k =
      (ff_gridInputCount T A K l j k : Real) / (K : Nat) := by
  rw [ff_gridTime_eq_gridPoint T K l hl]
  exact ff_rampInterpolate_grid K _ T hT l hl

theorem ff_rampInterpolate_monotoneOn
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

theorem ff_polygonalInputPath_monotoneOn
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (hA : IsFluidInput T A) (K : PNat) (j : Server) (k : Buffer) :
    MonotoneOn (fun t => ff_polygonalInputPath T A K t j k)
      (Set.Icc (0 : Real) T) := by
  apply ff_rampInterpolate_monotoneOn K _ T hT
  intro l hl
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    (ff_gridInputCount_mono T hT A hA K j k (Nat.le_succ l))

theorem ff_gridInputCount_approx
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

theorem ff_polygonalInputPath_between_grid
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

theorem ff_polygonalInputPath_uniform_error
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

theorem ff_polygonalInputPath_uniform_approx
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

end Network

end StateDepMOR

open scoped BigOperators Topology
open Filter MeasureTheory Set

namespace StateDepMOR

universe u v w

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

namespace Network

def fi_hatWeight (r : Real) (l : Nat) : Real :=
  max 0 (1 - abs (r - l))

noncomputable def fi_polygonalInterpolate
    (K : PNat) (values : Nat -> Real) (t T : Real) : Real :=
  Finset.sum (Finset.range ((K : Nat) + 1)) fun l =>
    fi_hatWeight (((K : Nat) : Real) * t / T) l * values l

theorem fi_hatWeight_nat_self (l : Nat) :
    fi_hatWeight (l : Real) l = 1 := by
  simp [fi_hatWeight]

theorem fi_hatWeight_nat_ne {l q : Nat} (hql : q ≠ l) :
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

theorem fi_polygonalInterpolate_grid
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

theorem fi_hatWeight_nonnegative (r : Real) (l : Nat) :
    0 <= fi_hatWeight r l :=
  le_max_left _ _

theorem fi_hatWeight_eq_zero_of_one_le_abs
    {r : Real} {l : Nat} (h : 1 <= abs (r - l)) :
    fi_hatWeight r l = 0 := by
  simp [fi_hatWeight, max_eq_left (by linarith : 1 - abs (r - l) <= 0)]

theorem fi_sum_hatWeight_eq_one
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

theorem fi_polygonalInterpolate_nonnegative
    (K : PNat) (values : Nat -> Real) (t T : Real)
    (hvalues : forall l, l < (K : Nat) + 1 -> 0 <= values l) :
    0 <= fi_polygonalInterpolate K values t T := by
  unfold fi_polygonalInterpolate
  apply Finset.sum_nonneg
  intro l hl
  exact mul_nonneg (fi_hatWeight_nonnegative _ _)
    (hvalues l (Finset.mem_range.mp hl))

theorem fi_polygonalInterpolate_const
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

theorem fi_polygonalInterpolate_add
    (K : PNat) (a b : Nat -> Real) (t T : Real) :
    fi_polygonalInterpolate K (fun l => a l + b l) t T =
      fi_polygonalInterpolate K a t T +
        fi_polygonalInterpolate K b t T := by
  simp only [fi_polygonalInterpolate, mul_add, Finset.sum_add_distrib]

theorem fi_polygonalInterpolate_sub
    (K : PNat) (a b : Nat -> Real) (t T : Real) :
    fi_polygonalInterpolate K (fun l => a l - b l) t T =
      fi_polygonalInterpolate K a t T -
        fi_polygonalInterpolate K b t T := by
  simp only [fi_polygonalInterpolate, mul_sub, Finset.sum_sub_distrib]

theorem fi_polygonalInterpolate_sum
    {I : Type w} [Fintype I]
    (K : PNat) (a : Nat -> I -> Real) (t T : Real) :
    fi_polygonalInterpolate K (fun l => Finset.univ.sum (a l)) t T =
      Finset.univ.sum (fun i =>
        fi_polygonalInterpolate K (fun l => a l i) t T) := by
  classical
  unfold fi_polygonalInterpolate
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem fi_polygonal_state_simplex
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

theorem fi_polygonal_zero
    (K : PNat) (values : Nat -> Real) (t T : Real)
    (hzero : forall l, l < (K : Nat) + 1 -> values l = 0) :
    fi_polygonalInterpolate K values t T = 0 := by
  unfold fi_polygonalInterpolate
  apply Finset.sum_eq_zero
  intro l hl
  rw [hzero l (Finset.mem_range.mp hl), mul_zero]

theorem fi_polygonal_allocation_incompatible
    (K : PNat) (e : Nat -> Buffer -> Server -> Buffer -> Real)
    (t T : Real) (i : Buffer) (j : Server) (k : Buffer)
    (hzero : forall l, l < (K : Nat) + 1 -> e l i j k = 0) :
    fi_polygonalInterpolate K (fun l => e l i j k) t T = 0 :=
  fi_polygonal_zero K _ t T hzero

theorem fi_polygonal_initial
    (K : PNat) (values : Nat -> Real) (T : Real) (hT : 0 < T) :
    fi_polygonalInterpolate K values 0 T = values 0 := by
  convert fi_polygonalInterpolate_grid K values T hT 0 (Nat.zero_le _) using 1
  simp

theorem fi_polygonal_balance
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

noncomputable def fi_polygonalInputPath
    (T : Real) (A : MatrixPath Server Buffer) (K : PNat) :
    MatrixPath Server Buffer :=
  fun t j k =>
    fi_polygonalInterpolate K
      (fun l => (ff_gridInputCount T A K l j k : Real) / (K : Nat))
      t T

theorem fi_polygonalInputPath_grid
    (T : Real) (hT : 0 < T) (A : MatrixPath Server Buffer)
    (K : PNat) (l : Nat) (hl : l <= (K : Nat))
    (j : Server) (k : Buffer) :
    fi_polygonalInputPath T A K (ff_gridTime T K l) j k =
      (ff_gridInputCount T A K l j k : Real) / (K : Nat) := by
  rw [ff_gridTime_eq_gridPoint T K l hl]
  exact fi_polygonalInterpolate_grid K _ T hT l hl

theorem fi_hatWeight_ne_zero_distance
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

theorem fi_polygonalInputPath_uniform_error
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

theorem fi_polygonalInputPath_uniform_convergence
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

noncomputable def fi_gridQueueState
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat)) (A : MatrixPath Server Buffer)
    (l : Nat) : JobState Buffer (K : Nat) :=
  N.runTokens U x (ff_gridTokenPrefix T A K l)

noncomputable def fi_gridAllocationCount
    (N : Network Buffer Server) (T : Real) (K : PNat)
    (U : N.DeterministicStationaryPolicy (K : Nat))
    (x : JobState Buffer (K : Nat)) (A : MatrixPath Server Buffer)
    (l : Nat) (i : Buffer) (j : Server) (k : Buffer) : Nat :=
  N.runAllocationCount U x (ff_gridTokenPrefix T A K l) i j k

theorem fi_gridTokenBatch_length
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

theorem fi_gridTokenBatch_scaled_length
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

theorem fi_gridAllocationCount_step_le_input_sum
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

theorem fi_gridQueueState_step_le_two_input_sum
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

noncomputable def fi_polygonalStatePath
    (K : PNat) (x : Nat -> Buffer -> Real) (T : Real) :
    FluidStatePath Buffer :=
  fun t i => fi_polygonalInterpolate K (fun l => x l i) t T

noncomputable def fi_polygonalAllocationPath
    (K : PNat) (e : Nat -> Buffer -> Server -> Buffer -> Real) (T : Real) :
    FluidAllocationPath Buffer Server :=
  fun t i j k => fi_polygonalInterpolate K (fun l => e l i j k) t T

theorem fi_polygonalStatePath_in_simplex
    (K : PNat) (x : Nat -> Buffer -> Real) {t T : Real}
    (hT : 0 < T) (ht : t ∈ Icc (0 : Real) T)
    (hx : forall l, l < (K : Nat) + 1 -> IsFluidState (x l)) :
    IsFluidState (fi_polygonalStatePath K x T t) :=
  fi_polygonal_state_simplex K x hT ht hx

theorem fi_polygonalStatePath_initial
    (K : PNat) (x : Nat -> Buffer -> Real) (T : Real) (hT : 0 < T)
    (i : Buffer) :
    fi_polygonalStatePath K x T 0 i = x 0 i :=
  fi_polygonal_initial K _ T hT

theorem fi_polygonalAllocationPath_initial
    (K : PNat) (e : Nat -> Buffer -> Server -> Buffer -> Real)
    (T : Real) (hT : 0 < T)
    (he0 : forall i j k, e 0 i j k = 0) (i : Buffer) (j : Server)
    (k : Buffer) :
    fi_polygonalAllocationPath K e T 0 i j k = 0 := by
  rw [fi_polygonalAllocationPath, fi_polygonal_initial K _ T hT, he0]

theorem fi_polygonalAllocationPath_incompatible
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

theorem fi_polygonal_paths_balance
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

theorem fi_polygonalInterpolate_eq_ramp
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

theorem fi_ramp_increment_domination
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

theorem fi_ramp_increment_domination_symmetric
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

theorem fi_polygonal_increment_domination
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

theorem fi_polygonalAllocationPath_increment_domination
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

theorem fi_polygonalQueuePath_increment_domination
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

end Network

end StateDepMOR

open scoped BigOperators Topology
open Set

namespace StateDepMOR

universe u v w

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

namespace Network

noncomputable section

variable (N : Network Buffer Server)

private noncomputable def floorJobs
    (x : Simplex Buffer) (K : Nat) (i : Buffer) : Nat :=
  Nat.floor ((K : Real) * x i)

private theorem sum_floorJobs_le (x : Simplex Buffer) (K : Nat) :
    (Finset.univ.sum fun i => floorJobs x K i) <= K := by
  have hterm (i : Buffer) :
      ((floorJobs x K i : Nat) : Real) <= (K : Real) * x i := by
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) (x.nonneg i))
  have hreal :
      ((Finset.univ.sum fun i => floorJobs x K i : Nat) : Real) <= K := by
    calc
      ((Finset.univ.sum fun i => floorJobs x K i : Nat) : Real) =
          Finset.univ.sum (fun i => ((floorJobs x K i : Nat) : Real)) := by
            exact Nat.cast_sum (f := fun i => floorJobs x K i) Finset.univ
      _ <= Finset.univ.sum (fun i => (K : Real) * x i) :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = (K : Real) * Finset.univ.sum (fun i => x i) := by
        rw [Finset.mul_sum]
      _ = K := by rw [x.sum_eq_one, mul_one]
  exact_mod_cast hreal

private noncomputable def roundedJobs
    (x : Simplex Buffer) (K : Nat) (i0 : Buffer) :
    Buffer -> Nat :=
  Function.update (floorJobs x K) i0
    (floorJobs x K i0 +
      (K - Finset.univ.sum fun i => floorJobs x K i))

private theorem sum_roundedJobs (x : Simplex Buffer) (K : Nat) (i0 : Buffer) :
    Finset.univ.sum (roundedJobs x K i0) = K := by
  classical
  let base : Buffer -> Nat := floorJobs x K
  let remainder := K - Finset.univ.sum base
  have hbase : Finset.univ.sum base <= K := sum_floorJobs_le x K
  have hsum :=
    Finset.sum_erase_add Finset.univ base (Finset.mem_univ i0)
  unfold roundedJobs
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

private noncomputable def roundedState
    (x : Simplex Buffer) (K : Nat) (i0 : Buffer) :
    JobState Buffer K where
  jobs := roundedJobs x K i0
  total_jobs := sum_roundedJobs x K i0

private theorem roundingRemainder_le_card (x : Simplex Buffer) (K : Nat) :
    K - Finset.univ.sum (fun i => floorJobs x K i) <=
      Fintype.card Buffer := by
  let S := Finset.univ.sum fun i => floorJobs x K i
  have hsumlt :
      (K : Real) <
        (S : Real) + Fintype.card Buffer := by
    calc
      (K : Real) =
          Finset.univ.sum (fun i => (K : Real) * x i) := by
            rw [<- Finset.mul_sum, x.sum_eq_one, mul_one]
      _ < Finset.univ.sum
          (fun i => ((floorJobs x K i : Nat) : Real) + 1) := by
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

private theorem roundedState_error_bound
    (x : Simplex Buffer) (K : Nat) (hK : 0 < K) (i0 i : Buffer) :
    abs (((roundedState x K i0 i : Nat) : Real) / K - x i) <
      (((Fintype.card Buffer : Nat) : Real) + 1) / (K : Real) := by
  classical
  let b : Nat := floorJobs x K i
  let r : Nat := K - Finset.univ.sum (fun q => floorJobs x K q)
  have hb_le : (b : Real) <= (K : Real) * x i := by
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg K) (x.nonneg i))
  have hlt_b : (K : Real) * x i < (b : Real) + 1 :=
    Nat.lt_floor_add_one ((K : Real) * x i)
  have hr : r <= Fintype.card Buffer :=
    roundingRemainder_le_card x K
  have hb_jobs : b <= roundedState x K i0 i := by
    by_cases hi : i = i0
    · subst i
      simp [roundedState, roundedJobs, b, r]
    · simp [roundedState, roundedJobs, b, hi]
  have hjobs_le : roundedState x K i0 i <= b + r := by
    by_cases hi : i = i0
    · subst i
      simp [roundedState, roundedJobs, b, r]
    · simp [roundedState, roundedJobs, b, hi]
  have hdiff_lower :
      -1 < ((roundedState x K i0 i : Nat) : Real) - (K : Real) * x i := by
    have hb_jobs_real :
        (b : Real) <= ((roundedState x K i0 i : Nat) : Real) := by
      exact_mod_cast hb_jobs
    linarith
  have hdiff_upper :
      ((roundedState x K i0 i : Nat) : Real) - (K : Real) * x i <=
        (Fintype.card Buffer : Real) := by
    have hjobs_le_real :
        ((roundedState x K i0 i : Nat) : Real) <= (b : Real) + r := by
      exact_mod_cast hjobs_le
    have hrreal : (r : Real) <= Fintype.card Buffer := by
      exact_mod_cast hr
    linarith
  have habs :
      abs (((roundedState x K i0 i : Nat) : Real) - (K : Real) * x i) <
        (Fintype.card Buffer : Real) + 1 := by
    rw [abs_lt]
    constructor
    · have hc : 0 <= (Fintype.card Buffer : Real) := Nat.cast_nonneg _
      linarith
    · linarith
  have hKreal : 0 < (K : Real) := Nat.cast_pos.mpr hK
  rw [show
      ((roundedState x K i0 i : Nat) : Real) / K - x i =
        (((roundedState x K i0 i : Nat) : Real) - (K : Real) * x i) / K by
      field_simp]
  rw [abs_div, abs_of_pos hKreal]
  exact div_lt_div_of_pos_right habs hKreal

private theorem exists_near_normalized_state
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
  let z : JobState Buffer K := roundedState x K i0
  refine ⟨Kp, z, ?_, ?_⟩
  · exact le_of_lt (lt_of_le_of_lt (le_max_left _ _) hKlarge)
  · intro i
    have hbound := roundedState_error_bound x K hKpos i0 i
    have hKc : c / epsilon < (K : Real) :=
      lt_of_le_of_lt (le_max_right _ _) hKlarge
    have hratio : c / (K : Real) < epsilon := by
      apply (div_lt_iff₀ (Nat.cast_pos.mpr hKpos)).2
      apply (div_lt_iff₀ hepsilon).1 at hKc
      nlinarith
    exact hbound.trans hratio

private theorem exists_actionDirac_mem_fluidPolicyCorrespondence
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
    exact exists_near_normalized_state x (epsilon n) (hepsilon n)
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

private theorem fluidPolicyCorrespondence_isActionDistribution
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

private theorem fluidPolicyCorrespondence_incompatible
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

private theorem fluidPolicyCorrespondence_convex
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) :
    Convex Real (N.fluidPolicyCorrespondence U j k x) := by
  unfold fluidPolicyCorrespondence
  exact convex_iInter fun _ => (convex_convexHull Real _).closure

private def fluidPolicyCorrespondenceGraph
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    Set ((Buffer -> Real) × ActionVector Buffer) :=
  {xp | Membership.mem (N.fluidPolicyCorrespondence U j k xp.1) xp.2}

private theorem fluidPolicyCorrespondenceGraph_isClosed
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    IsClosed (N.fluidPolicyCorrespondenceGraph U j k) := by
  rw [<- isSeqClosed_iff_isClosed]
  intro s xp hs hsxp
  rcases xp with ⟨x, p⟩
  have hx : Tendsto (fun n => (s n).1) atTop (nhds x) :=
    hsxp.fst_nhds
  have hp : Tendsto (fun n => (s n).2) atTop (nhds p) :=
    hsxp.snd_nhds
  unfold fluidPolicyCorrespondenceGraph at hs ⊢
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

private theorem actionDirac_feasibleSet_isClosed
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (a : N.ServiceAction) :
    IsClosed {x : Buffer -> Real |
      N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x} := by
  let f : (Buffer -> Real) ->
      (Buffer -> Real) × ActionVector Buffer :=
    fun x => (x, N.actionDirac a)
  have hf : Continuous f := continuous_id.prodMk continuous_const
  exact (N.fluidPolicyCorrespondenceGraph_isClosed U j k).preimage hf

private noncomputable def feasiblePureActionMass
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) : Real := by
  classical
  exact Finset.univ.sum fun a : N.ServiceAction =>
    if N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x then 1 else 0

private noncomputable def feasiblePureActionSum
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) :
    ActionVector Buffer := by
  classical
  exact fun b =>
    Finset.univ.sum fun a : N.ServiceAction =>
      if N.actionDirac a ∈ N.fluidPolicyCorrespondence U j k x then
        N.actionDirac a b
      else 0

private noncomputable def measurableFluidPolicySelector
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real) :
    ActionVector Buffer := by
  classical
  exact
    if N.feasiblePureActionMass U j k x = 0 then
      N.actionDirac none
    else
      (N.feasiblePureActionMass U j k x)⁻¹ •
        N.feasiblePureActionSum U j k x

private theorem feasiblePureActionMass_measurable
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    Measurable (N.feasiblePureActionMass U j k) := by
  classical
  unfold feasiblePureActionMass
  apply Finset.measurable_fun_sum
  intro a _ha
  apply Measurable.ite
  · exact (actionDirac_feasibleSet_isClosed N U j k a).measurableSet
  · exact measurable_const
  · exact measurable_const

private theorem feasiblePureActionSum_coordinate_measurable
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (b : Option Buffer) :
    Measurable (fun x => N.feasiblePureActionSum U j k x b) := by
  classical
  unfold feasiblePureActionSum
  apply Finset.measurable_fun_sum
  intro a _ha
  apply Measurable.ite
  · exact (actionDirac_feasibleSet_isClosed N U j k a).measurableSet
  · exact measurable_const
  · exact measurable_const

private theorem measurableFluidPolicySelector_measurable
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) :
    Measurable (N.measurableFluidPolicySelector U j k) := by
  rw [measurable_pi_iff]
  intro b
  unfold measurableFluidPolicySelector
  simp only [ite_apply, Pi.smul_apply, smul_eq_mul]
  apply Measurable.ite
  · exact measurableSet_eq_fun
      (feasiblePureActionMass_measurable N U j k) measurable_const
  · exact measurable_const
  · exact (feasiblePureActionMass_measurable N U j k).inv.mul
      (feasiblePureActionSum_coordinate_measurable N U j k b)

private theorem measurableFluidPolicySelector_mem
    (N : Network Buffer Server) (U : N.DeterministicPolicySequence)
    (j : Server) (k : Buffer) (x : Buffer -> Real)
    (hx : IsFluidState x) :
    N.measurableFluidPolicySelector U j k x ∈
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
      exists_actionDirac_mem_fluidPolicyCorrespondence N U j k sx
    refine ⟨a, ?_⟩
    simp [s, sx] at ha ⊢
    exact ha
  have hcard : 0 < s.card := Finset.card_pos.mpr hs
  have hmass :
      N.feasiblePureActionMass U j k x = (s.card : Real) := by
    unfold feasiblePureActionMass
    rw [<- Finset.sum_filter]
    change Finset.sum s (fun _a => (1 : Real)) = (s.card : Real)
    simp
  have hmass_ne : Ne (N.feasiblePureActionMass U j k x) 0 := by
    rw [hmass]
    exact_mod_cast Nat.ne_of_gt hcard
  have hsum :
      N.feasiblePureActionSum U j k x =
        Finset.sum s fun a => N.actionDirac a := by
    funext b
    unfold feasiblePureActionSum
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
    apply (N.fluidPolicyCorrespondence_convex U j k x).sum_mem
    · intro a ha
      positivity
    · exact hweights
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
  rw [measurableFluidPolicySelector, if_neg hmass_ne, hmass, hsum]
  simpa only [Finset.smul_sum] using havg

private def fluidPolicyEpsilonCorrespondence
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (epsilon : Real) : Set (ActionVector Buffer) :=
  closure (convexHull Real
    {q | exists K : PNat, exists z : JobState Buffer (K : Nat),
      epsilon⁻¹ <= (K : Real) /\
      IsNearNormalizedState z x epsilon /\
      q = N.actionDirac (U K z j k)})

private noncomputable def finiteDifferenceRatio
    (N : Network Buffer Server)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t h : Real) : ActionVector Buffer :=
  fun a => (E (t + h) a - E t a) / (A (t + h) - A t)

private noncomputable def verifiedPatchedFluidPolicy
    (N : Network Buffer Server)
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) : ActionVector Buffer := by
  classical
  let q : ActionVector Buffer :=
    fun a => deriv (fun s => E s a) t / deriv A t
  exact if q ∈ N.fluidPolicyCorrespondence U j k (X t) then q
    else N.measurableFluidPolicySelector U j k (X t)

private theorem measurableFluidPolicySelector_comp
    {Time : Type*} [MeasurableSpace Time]
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Time -> Buffer -> Real)
    (hX : forall i, Measurable (fun t => X t i))
    (a : Option Buffer) :
    Measurable
      (fun t => N.measurableFluidPolicySelector U j k (X t) a) := by
  exact
    (measurable_pi_iff.mp
      (N.measurableFluidPolicySelector_measurable U j k) a).comp
      (measurable_pi_lambda X hX)

private theorem fluidPolicyEpsilonCorrespondence_isClosed
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (epsilon : Real) :
    IsClosed (N.fluidPolicyEpsilonCorrespondence U j k x epsilon) :=
  isClosed_closure

private theorem mem_fluidPolicyCorrespondence_iff_epsilon
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (q : ActionVector Buffer) :
    q ∈ N.fluidPolicyCorrespondence U j k x <->
      forall epsilon : {r : Real // 0 < r},
        q ∈ N.fluidPolicyEpsilonCorrespondence U j k x epsilon.1 := by
  unfold fluidPolicyCorrespondence fluidPolicyEpsilonCorrespondence
  rw [Set.mem_iInter]

private theorem weightedEmpiricalActionAverage_mem_epsilon
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
        N.fluidPolicyEpsilonCorrespondence U j k x epsilon := by
  apply subset_closure
  apply (convex_convexHull Real _).sum_mem hweight_nonneg hweight_sum
  intro r hr
  apply subset_convexHull Real
  exact ⟨K r, z r, hK r hr, hz r hr, rfl⟩

private theorem closed_mem_of_finiteDifferenceRatio_limit
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

private theorem derivativeRatio_mem_closed_of_right_finiteDifferences
    {C : Set (ActionVector Buffer)}
    (hC : IsClosed C)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t Adot : Real) (Edot : ActionVector Buffer)
    (hA : HasDerivAt A Adot t)
    (hE : forall a, HasDerivAt (fun s => E s a) (Edot a) t)
    (hAdot : 0 < Adot)
    (hmem : Filter.Eventually
      (fun h => N.finiteDifferenceRatio A E t h ∈ C)
      (nhdsWithin 0 (Ioi 0))) :
    (fun a => Edot a / Adot) ∈ C := by
  have htendsto :
      Tendsto (N.finiteDifferenceRatio A E t)
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
    dsimp [slopeRatio, finiteDifferenceRatio]
    field_simp
  exact hC.mem_of_tendsto htendsto hmem

private theorem derivativeRatio_mem_fluidPolicyCorrespondence
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t Adot : Real) (Edot : ActionVector Buffer)
    (hA : HasDerivAt A Adot t)
    (hE : forall a, HasDerivAt (fun s => E s a) (Edot a) t)
    (hAdot : 0 < Adot)
    (hfinite : forall epsilon : {r : Real // 0 < r},
      Filter.Eventually
        (fun h => N.finiteDifferenceRatio A E t h ∈
          N.fluidPolicyEpsilonCorrespondence U j k x epsilon.1)
        (nhdsWithin 0 (Ioi 0))) :
    (fun a => Edot a / Adot) ∈
      N.fluidPolicyCorrespondence U j k x := by
  rw [N.mem_fluidPolicyCorrespondence_iff_epsilon]
  intro epsilon
  exact N.derivativeRatio_mem_closed_of_right_finiteDifferences
    (N.fluidPolicyEpsilonCorrespondence_isClosed U j k x epsilon.1)
    A E t Adot Edot hA hE hAdot (hfinite epsilon)

private theorem ae_derivativeRatio_mem_fluidPolicyCorrespondence
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
              N.finiteDifferenceRatio A E t h ∈
                N.fluidPolicyEpsilonCorrespondence
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
  exact N.derivativeRatio_mem_fluidPolicyCorrespondence
    U j k (X t) A E t (deriv A t)
    (fun a => deriv (fun s => E s a) t)
    hAt.hasDerivAt (fun a => (hEt a).hasDerivAt) hpos (hft hpos)

private theorem verifiedPatchedFluidPolicy_coordinate_measurable
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (hX : forall i, Measurable (fun t => X t i))
    (a : Option Buffer) :
    Measurable
      (fun t => N.verifiedPatchedFluidPolicy U j k X A E t a) := by
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
      (N.fluidPolicyCorrespondenceGraph_isClosed U j k).measurableSet.preimage
        hpair
    change MeasurableSet {t |
      q t ∈ N.fluidPolicyCorrespondence U j k (X t)} at hgraph
    exact hgraph
  dsimp [q] at hcondition
  unfold verifiedPatchedFluidPolicy
  simp only [ite_apply]
  apply Measurable.ite hcondition
  · exact (measurable_deriv (fun s => E s a)).div (measurable_deriv A)
  · exact N.measurableFluidPolicySelector_comp U j k X hX a

private theorem verifiedPatchedFluidPolicy_mem
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) (hstate : IsFluidState (X t)) :
    N.verifiedPatchedFluidPolicy U j k X A E t ∈
      N.fluidPolicyCorrespondence U j k (X t) := by
  classical
  let q : ActionVector Buffer :=
    fun a => deriv (fun s => E s a) t / deriv A t
  by_cases hq : q ∈ N.fluidPolicyCorrespondence U j k (X t)
  · simpa [verifiedPatchedFluidPolicy, q, hq] using hq
  · simp only [verifiedPatchedFluidPolicy, q, if_neg hq]
    exact N.measurableFluidPolicySelector_mem U j k (X t) hstate

private theorem verifiedPatchedFluidPolicy_isActionDistribution
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) (hstate : IsFluidState (X t)) :
    IsActionDistribution
      (N.verifiedPatchedFluidPolicy U j k X A E t) :=
  fluidPolicyCorrespondence_isActionDistribution N U j k (X t) _
    (N.verifiedPatchedFluidPolicy_mem U j k X A E t hstate)

private theorem verifiedPatchedFluidPolicy_incompatible_zero
    (U : N.DeterministicPolicySequence) (j : Server) (k i : Buffer)
    (X : Real -> Buffer -> Real)
    (A : Real -> Real) (E : Real -> ActionVector Buffer)
    (t : Real) (hstate : IsFluidState (X t))
    (hi : Not (N.compatible i j)) :
    N.verifiedPatchedFluidPolicy U j k X A E t (some i) = 0 :=
  fluidPolicyCorrespondence_incompatible N U j k i (X t) _
    (N.verifiedPatchedFluidPolicy_mem U j k X A E t hstate) hi

private theorem verifiedPatchedFluidPolicy_allocation_rule_ae
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
            N.verifiedPatchedFluidPolicy U j k X A E t a)
      (ae TimeMeasure) := by
  classical
  filter_upwards [hAnonneg, hpositive, hzero] with t hnonneg hpt hzt
  intro a
  by_cases hpos : 0 < deriv A t
  · have hmem := hpt hpos
    simp only [verifiedPatchedFluidPolicy, if_pos hmem]
    field_simp
  · have hz : deriv A t = 0 :=
      le_antisymm (not_lt.mp hpos) hnonneg
    simp [verifiedPatchedFluidPolicy, hz, hzt hz a]

/-- Progress through grid edge `l` at continuous grid coordinate `r`.
It is zero before the edge, affine on the edge, and one after it. -/
def edgeProgress (r : Real) (l : Nat) : Real :=
  max 0 (min 1 (r - l))

theorem edgeProgress_nonneg (r : Real) (l : Nat) :
    0 <= edgeProgress r l := by
  unfold edgeProgress
  exact le_max_left _ _

theorem edgeProgress_mono {r q : Real} (hrq : r <= q) (l : Nat) :
    edgeProgress r l <= edgeProgress q l := by
  unfold edgeProgress
  exact max_le_max (le_refl 0)
    (min_le_min (le_refl 1) (sub_le_sub_right hrq _))

/-- Fraction of edge `edge i` traversed by the interval `[s,t]`. -/
def edgeWindowWeight {I : Type w} (edge : I -> Nat)
    (s t : Real) (i : I) : Real :=
  edgeProgress t (edge i) - edgeProgress s (edge i)

theorem edgeWindowWeight_nonneg {I : Type w} (edge : I -> Nat)
    {s t : Real} (hst : s <= t) (i : I) :
    0 <= edgeWindowWeight edge s t i := by
  exact sub_nonneg.mpr (edgeProgress_mono hst (edge i))

/-- Common linear interpolation of cumulative input, represented directly
by its finite action occurrences and their grid edges. -/
def finiteActionInputInterpolate {I : Type w}
    (ids : Finset I) (edge : I -> Nat) (r : Real) : Real :=
  Finset.sum ids fun i => edgeProgress r (edge i)

/-- Common linear interpolation of the cumulative all-action vector.
The action `none` is retained as an ordinary coordinate. -/
def finiteActionVectorInterpolate {I : Type w}
    (ids : Finset I) (edge : I -> Nat) (action : I -> Option Buffer)
    (r : Real) : ActionVector Buffer :=
  fun a =>
    Finset.sum ids fun i =>
      edgeProgress r (edge i) * N.actionDirac (action i) a

theorem finiteActionInputInterpolate_increment {I : Type w}
    (ids : Finset I) (edge : I -> Nat) (s t : Real) :
    finiteActionInputInterpolate ids edge t -
        finiteActionInputInterpolate ids edge s =
      Finset.sum ids (edgeWindowWeight edge s t) := by
  rw [finiteActionInputInterpolate, finiteActionInputInterpolate,
    <- Finset.sum_sub_distrib]
  rfl

theorem finiteActionVectorInterpolate_increment {I : Type w}
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
theorem finiteActionInterpolate_ratio_eq_weightedAverage
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

theorem finiteActionInterpolate_normalizedWeights_nonneg
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

theorem finiteActionInterpolate_normalizedWeights_sum
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
theorem finiteActionInterpolate_ratio_mem_epsilon
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
      N.fluidPolicyEpsilonCorrespondence U j k x epsilon := by
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
  apply N.weightedEmpiricalActionAverage_mem_epsilon
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

/-- The same bridge in the `finiteDifferenceRatio` syntax consumed by
`derivativeRatio_mem_fluidPolicyCorrespondence`. -/
theorem finiteDifferenceRatio_finiteActionInterpolate_mem_epsilon
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
    N.finiteDifferenceRatio
        (finiteActionInputInterpolate ids edge)
        (finiteActionVectorInterpolate N ids edge
          (fun r => U (K r) (z r) j k))
        t h ∈
      N.fluidPolicyEpsilonCorrespondence U j k x epsilon := by
  apply N.finiteActionInterpolate_ratio_mem_epsilon
      U j k x epsilon ids edge K z
  · linarith
  · exact hpos
  · exact hK
  · exact hz

/-- Finite index of all occurrences in a family of edge batches. -/
abbrev BatchedOccurrence {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) :=
  Sigma fun l : Fin gridEdges => Fin (states l).length

/-- Input interpolation obtained by assigning every occurrence in batch
`l` to grid edge `l`. -/
noncomputable def batchedInputInterpolate {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) (r : Real) : Real :=
  finiteActionInputInterpolate
    (Finset.univ : Finset (BatchedOccurrence states))
    (fun q => q.1.val) r

/-- All-action interpolation for batched finite pre-action states. -/
noncomputable def batchedPolicyActionInterpolate
    {gridEdges : Nat} (U : N.DeterministicPolicySequence)
    (K : PNat)
    (states : Fin gridEdges -> List (JobState Buffer (K : Nat)))
    (j : Server) (k : Buffer) (r : Real) : ActionVector Buffer :=
  finiteActionVectorInterpolate N
    (Finset.univ : Finset (BatchedOccurrence states))
    (fun q => q.1.val)
    (fun q => U K ((states q.1).get q.2) j k) r

theorem batchedInputInterpolate_eq_batch_sum
    {Z : Type*} {gridEdges : Nat}
    (states : Fin gridEdges -> List Z) (r : Real) :
    batchedInputInterpolate states r =
      Finset.univ.sum fun l : Fin gridEdges =>
        Finset.univ.sum fun _q : Fin (states l).length =>
          edgeProgress r l.val := by
  classical
  unfold batchedInputInterpolate finiteActionInputInterpolate
  rw [Fintype.sum_sigma]

theorem batchedPolicyActionInterpolate_eq_batch_sum
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
theorem batchedInputInterpolate_eq_cumulativeRamp
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
theorem batchedPolicyActionInterpolate_eq_cumulativeRamp
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
theorem batchedPolicyActionInterpolate_ratio_mem_epsilon
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
      N.fluidPolicyEpsilonCorrespondence U j k x epsilon := by
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
noncomputable def scaledBatchedInputInterpolate
    {Z : Type*} (gridK : PNat)
    (states : Fin (gridK : Nat) -> List Z) (T t : Real) : Real :=
  batchedInputInterpolate states
      (((gridK : Nat) : Real) * t / T) /
    (gridK : Nat)

/-- Time-rescaled and population-scaled all-action path. -/
noncomputable def scaledBatchedPolicyActionInterpolate
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
theorem finiteDifferenceRatio_scaledBatched_mem_epsilon
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
    N.finiteDifferenceRatio
        (scaledBatchedInputInterpolate gridK states T)
        (scaledBatchedPolicyActionInterpolate
          N gridK U K states j k T)
        t h ∈
      N.fluidPolicyEpsilonCorrespondence U j k x epsilon := by
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
  unfold finiteDifferenceRatio
  dsimp [scaledBatchedInputInterpolate,
    scaledBatchedPolicyActionInterpolate, r0, r1]
  field_simp

end

end Network

end StateDepMOR

open scoped BigOperators Topology
open Set

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]

namespace Network

noncomputable section

variable (N : Network Buffer Server)

/-- Sequential pre-action states at occurrences of one fixed token type. -/
def fluidEmpiricalPreActionStates {K : Nat}
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
def fluidEmpiricalActionCount {K : Nat}
    (U : N.DeterministicStationaryPolicy K) :
    JobState Buffer K ->
      List (TokenType (Buffer := Buffer) (Server := Server)) ->
      Server -> Buffer -> ActionVector Buffer
  | _, [], _, _ => 0
  | z, jk :: rest, j, k =>
      (if jk = (j, k) then N.actionDirac (U z jk.1 jk.2) else 0) +
        fluidEmpiricalActionCount U (N.queueStep U z jk) rest j k

/-- Natural-valued count of wasted occurrences of one fixed token type. -/
def fluidEmpiricalMatchingWasteCount {K : Nat}
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
theorem fluidEmpiricalPreActionStates_length {K : Nat}
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
theorem fluidEmpiricalActionCount_eq_preActionState_sum {K : Nat}
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
theorem fluidEmpiricalActionCount_some_eq_runAllocationCount {K : Nat}
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
theorem fluidEmpiricalActionCount_none_eq_matchingWasteCount {K : Nat}
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
theorem fluidEmpiricalActionCount_sum_eq_count {K : Nat}
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
theorem fluidEmpiricalActionCount_nonneg {K : Nat}
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
def fluidEmpiricalActionAverage {K : Nat}
    (U : N.DeterministicStationaryPolicy K)
    (z : JobState Buffer K)
    (tokens : List (TokenType (Buffer := Buffer) (Server := Server)))
    (j : Server) (k : Buffer) : ActionVector Buffer :=
  (tokens.count (j, k) : Real)⁻¹ •
    N.fluidEmpiricalActionCount U z tokens j k

/-- The empirical vector is the uniform average of the matching
pre-action-state Dirac vectors. -/
theorem fluidEmpiricalActionAverage_eq_preActionState_average {K : Nat}
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
theorem fluidEmpiricalActionAverage_some_eq_runAllocationCount_div {K : Nat}
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
theorem fluidEmpiricalActionAverage_none_eq_matchingWasteCount_div {K : Nat}
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
theorem fluidEmpiricalActionAverage_sum_eq_one {K : Nat}
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
theorem fluidEmpiricalActionAverage_isActionDistribution {K : Nat}
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
def fluidEmpiricalEpsilonCorrespondence
    (U : N.DeterministicPolicySequence) (j : Server) (k : Buffer)
    (x : Buffer -> Real) (epsilon : Real) : Set (ActionVector Buffer) :=
  closure (convexHull Real
    {q | exists K : PNat, exists z : JobState Buffer (K : Nat),
      epsilon⁻¹ <= (K : Real) /\
      IsNearNormalizedState z x epsilon /\
      q = N.actionDirac (U K z j k)})

/-- A nonempty empirical action vector from uniformly epsilon-near
pre-action states belongs to the fixed-epsilon fluid policy set. -/
theorem fluidEmpiricalActionAverage_mem_epsilonCorrespondence
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

end

end Network

end StateDepMOR

open scoped BigOperators Topology
open Filter MeasureTheory Set

set_option maxHeartbeats 800000

namespace StateDepMOR

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]
variable [DecidableEq Buffer] [DecidableEq Server]
variable [Nonempty Buffer] [Nonempty Server]

namespace Network

noncomputable section

attribute [local instance] tokenTypeMeasurableSpace

variable (N : Network Buffer Server)
variable (initial : forall K : PNat, JobState Buffer (K : Nat))

/-- Fluid-scaled queue state generated from an arbitrary initial state. -/
noncomputable def scaledQueueStateFrom
    (initial : forall K : PNat, JobState Buffer (K : Nat))
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (t : Real) (i : Buffer) : Real :=
  ((N.runTokens (U K) (initial K)
      (N.eventTokenPrefix (N.eventEpochCount K t) omega) i : Nat) : Real) /
    ((K : Nat) : Real)

/-- Fluid-scaled cumulative allocation generated from arbitrary initials. -/
noncomputable def scaledAllocationFrom
    (initial : forall K : PNat, JobState Buffer (K : Nat))
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (t : Real)
    (i : Buffer) (j : Server) (k : Buffer) : Real :=
  (N.runAllocationCount (U K) (initial K)
      (N.eventTokenPrefix (N.eventEpochCount K t) omega) i j k : Real) /
    ((K : Nat) : Real)

/-- Event-epoch execution from an arbitrary initial state at every size. -/
noncomputable def eventEpochExecutionFrom
    (initial : forall K : PNat, JobState Buffer (K : Nat)) :
    N.ScaledStochasticExecution N.TokenPath where
  probability :=
    (show ProbabilityMeasure N.TokenPath from
      ⟨N.tokenPathMeasure, inferInstance⟩)
  input := fun K omega t j k => N.scaledTokenInput K omega t j k
  state := fun U K omega t i =>
    N.scaledQueueStateFrom initial U K omega t i
  allocation := fun U K omega t i j k =>
    N.scaledAllocationFrom initial U K omega t i j k

/-- At nonnegative time `T`, the execution state is exactly the queue after
the first `floor (T * K)` tokens. -/
theorem eventEpochExecutionFrom_state_at
    (initial : forall K : PNat, JobState Buffer (K : Nat))
    (U : N.DeterministicPolicySequence) (K : PNat)
    (omega : N.TokenPath) (T : Real) (hT : 0 <= T) (i : Buffer) :
    (N.eventEpochExecutionFrom initial).state U K omega T i =
      ((N.runTokens (U K) (initial K)
          (N.eventTokenPrefix
            (Nat.floor (T * ((K : Nat) : Real))) omega) i : Nat) : Real) /
        ((K : Nat) : Real) := by
  simp [eventEpochExecutionFrom, scaledQueueStateFrom, eventEpochCount,
    max_eq_left hT]

private theorem pnat_val_strictMono
    {K : Nat -> PNat} (hK : StrictMono K) :
    StrictMono (fun r => (K r : Nat)) := by
  intro r s hrs
  exact hK hrs

private theorem pnat_val_tendsto_atTop
    {K : Nat -> PNat} (hK : StrictMono K) :
    Tendsto (fun r => (K r : Nat)) atTop atTop :=
  (pnat_val_strictMono hK).tendsto_atTop

private theorem eventTokenPrefix_length
    (n : Nat) (omega : N.TokenPath) :
    (N.eventTokenPrefix n omega).length = n := by
  simp [eventTokenPrefix]

private theorem eventTokenPrefix_take
    {a b : Nat} (hab : a <= b) (omega : N.TokenPath) :
    (N.eventTokenPrefix b omega).take a =
      N.eventTokenPrefix a omega := by
  unfold eventTokenPrefix
  rw [<- Fin.ofFn_take_eq_take_ofFn hab]
  apply List.ofFn_inj.2
  rfl

private theorem eventTokenPrefix_append_drop
    {a b : Nat} (hab : a <= b) (omega : N.TokenPath) :
    N.eventTokenPrefix a omega ++
        (N.eventTokenPrefix b omega).drop a =
      N.eventTokenPrefix b omega := by
  rw [<- eventTokenPrefix_take N hab omega]
  exact List.take_append_drop _ _

private theorem tokenIndicator_sum_eq_prefix_count
    (jk : TokenType (Buffer := Buffer) (Server := Server))
    (n : Nat) (omega : N.TokenPath) :
    (Finset.range n).sum (fun r => N.tokenIndicator jk r omega) =
      ((N.eventTokenPrefix n omega).count jk : Real) := by
  induction n with
  | zero =>
      simp [eventTokenPrefix]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show
        N.eventTokenPrefix (n + 1) omega =
          N.eventTokenPrefix n omega ++ [N.tokenAt n omega] by
        unfold eventTokenPrefix
        rw [List.ofFn_succ']
        rw [List.concat_eq_append]
        congr]
      rw [List.count_append]
      by_cases h : N.tokenAt n omega = jk
      · simp [tokenIndicator, tokenIndicatorValue, h]
      · have h' : jk != N.tokenAt n omega := by
          exact bne_iff_ne.mpr (Ne.symm h)
        simp [tokenIndicator, tokenIndicatorValue, h, h']

private theorem scaledTokenInput_eq_prefix_count
    (K : PNat) (omega : N.TokenPath) (t : Real)
    (j : Server) (k : Buffer) :
    N.scaledTokenInput K omega t j k =
      ((N.eventTokenPrefix (N.eventEpochCount K t) omega).count (j, k) :
          Real) / (K : Nat) := by
  rw [scaledTokenInput, empiricalFrequency]
  rw [tokenIndicator_sum_eq_prefix_count N]
  by_cases hn : N.eventEpochCount K t = 0
  · simp [hn, eventTokenPrefix]
  · field_simp

private theorem eventEpochCount_mono
    (K : PNat) {s t : Real} (hst : s <= t) :
    N.eventEpochCount K s <= N.eventEpochCount K t := by
  unfold eventEpochCount
  apply Nat.floor_mono
  apply mul_le_mul_of_nonneg_right
  · exact max_le_max_right 0 hst
  · positivity

private theorem eventEpochCount_zero (K : PNat) :
    N.eventEpochCount K 0 = 0 := by
  simp [eventEpochCount]

private def eventGridTime (T : Real) (K : PNat) (l : Nat) : Real :=
  T * (l : Real) / (K : Nat)

private theorem eventGridTime_zero (T : Real) (K : PNat) :
    eventGridTime T K 0 = 0 := by
  simp [eventGridTime]

private theorem eventGridTime_succ_sub
    (T : Real) (K : PNat) (l : Nat) :
    eventGridTime T K (l + 1) - eventGridTime T K l =
      T / (K : Nat) := by
  unfold eventGridTime
  push_cast
  ring

private theorem eventGridTime_mem_Icc
    {T : Real} (hT : 0 < T) (K : PNat) {l : Nat}
    (hl : l <= (K : Nat)) :
    eventGridTime T K l ∈ Icc (0 : Real) T := by
  have hK : (0 : Real) < (K : Nat) := by positivity
  constructor
  · exact div_nonneg
      (mul_nonneg hT.le (Nat.cast_nonneg l)) hK.le
  · apply (div_le_iff₀ hK).2
    have hl' : (l : Real) <= (K : Nat) := by exact_mod_cast hl
    nlinarith

private theorem eventGridTime_mono
    {T : Real} (hT : 0 < T) (K : PNat) {l m : Nat}
    (hlm : l <= m) :
    eventGridTime T K l <= eventGridTime T K m := by
  unfold eventGridTime
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlm) hT.le

private def eventGridCount
    (T : Real) (K : PNat) (l : Nat) : Nat :=
  N.eventEpochCount K (eventGridTime T K l)

private theorem eventGridCount_mono
    {T : Real} (hT : 0 < T) (K : PNat) {l m : Nat}
    (hlm : l <= m) :
    N.eventGridCount T K l <= N.eventGridCount T K m :=
  eventEpochCount_mono N K (eventGridTime_mono hT K hlm)

private theorem eventGridCount_zero (T : Real) (K : PNat) :
    N.eventGridCount T K 0 = 0 := by
  simp [eventGridCount, eventGridTime, eventEpochCount]

private def eventGridPrefix
    (T : Real) (K : PNat) (omega : N.TokenPath) (l : Nat) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  N.eventTokenPrefix (N.eventGridCount T K l) omega

private def eventGridBatch
    (T : Real) (K : PNat) (omega : N.TokenPath) (l : Nat) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  (N.eventGridPrefix T K omega (l + 1)).drop
    (N.eventGridCount T K l)

private theorem eventGridPrefix_succ
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : N.TokenPath) (l : Nat) :
    N.eventGridPrefix T K omega (l + 1) =
      N.eventGridPrefix T K omega l ++
        N.eventGridBatch T K omega l := by
  unfold eventGridPrefix eventGridBatch
  exact (eventTokenPrefix_append_drop N
    (eventGridCount_mono N hT K (Nat.le_succ l)) omega).symm

private theorem eventGridBatch_length
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : N.TokenPath) (l : Nat) :
    (N.eventGridBatch T K omega l).length =
      N.eventGridCount T K (l + 1) - N.eventGridCount T K l := by
  unfold eventGridBatch eventGridPrefix
  rw [List.length_drop, eventTokenPrefix_length N]

private theorem eventGridBatch_count
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : N.TokenPath) (l : Nat)
    (j : Server) (k : Buffer) :
    (N.eventGridBatch T K omega l).count (j, k) =
      (N.eventGridPrefix T K omega (l + 1)).count (j, k) -
        (N.eventGridPrefix T K omega l).count (j, k) := by
  have hp := eventGridPrefix_succ N hT K omega l
  rw [hp, List.count_append, Nat.add_sub_cancel_left]

private def eventGridState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (l : Nat) :
    JobState Buffer (K : Nat) :=
  N.runTokens (U K) (initial K)
    (N.eventGridPrefix T K omega l)

private def eventGridAllocation
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) : Nat :=
  N.runAllocationCount (U K) (initial K)
    (N.eventGridPrefix T K omega l) i j k

private def eventGridInput
    (T : Real) (K : PNat) (omega : N.TokenPath) (l : Nat)
    (j : Server) (k : Buffer) : Nat :=
  (N.eventGridPrefix T K omega l).count (j, k)

private noncomputable def eventPolygonalState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) : FluidStatePath Buffer :=
  fun t i =>
    fi_polygonalInterpolate K
      (fun l => (N.eventGridState initial T U K omega l i : Real) / (K : Nat))
      t T

private noncomputable def eventPolygonalAllocation
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) :
    FluidAllocationPath Buffer Server :=
  fun t i j k =>
    fi_polygonalInterpolate K
      (fun l =>
        (N.eventGridAllocation initial T U K omega l i j k : Real) / (K : Nat))
      t T

private noncomputable def eventPolygonalInput
    (T : Real) (K : PNat) (omega : N.TokenPath) :
    MatrixPath Server Buffer :=
  fun t j k =>
    fi_polygonalInterpolate K
      (fun l => (N.eventGridInput T K omega l j k : Real) / (K : Nat))
      t T

private theorem continuous_eventPolygonalState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (i : Buffer) :
    Continuous (fun t => N.eventPolygonalState initial T U K omega t i) := by
  unfold eventPolygonalState fi_polygonalInterpolate fi_hatWeight
  fun_prop

private theorem continuous_eventPolygonalAllocation
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (i : Buffer) (j : Server) (k : Buffer) :
    Continuous
      (fun t => N.eventPolygonalAllocation initial T U K omega t i j k) := by
  unfold eventPolygonalAllocation fi_polygonalInterpolate fi_hatWeight
  fun_prop

private theorem continuous_eventPolygonalInput
    (T : Real) (K : PNat) (omega : N.TokenPath)
    (j : Server) (k : Buffer) :
    Continuous (fun t => N.eventPolygonalInput T K omega t j k) := by
  unfold eventPolygonalInput fi_polygonalInterpolate fi_hatWeight
  fun_prop

private theorem eventGridState_succ
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (l : Nat) :
    N.eventGridState initial T U K omega (l + 1) =
      N.runTokens (U K) (N.eventGridState initial T U K omega l)
        (N.eventGridBatch T K omega l) := by
  unfold eventGridState
  rw [eventGridPrefix_succ N hT K omega l]
  exact ff_runTokens_append N _ _ _ _

private theorem eventGridAllocation_succ
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    N.eventGridAllocation initial T U K omega (l + 1) i j k =
      N.eventGridAllocation initial T U K omega l i j k +
        N.runAllocationCount (U K)
          (N.eventGridState initial T U K omega l)
          (N.eventGridBatch T K omega l) i j k := by
  unfold eventGridAllocation eventGridState
  rw [eventGridPrefix_succ N hT K omega l]
  exact ff_runAllocationCount_append N _ _ _ _ _ _ _

private theorem eventGridInput_mono
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : N.TokenPath) {l m : Nat} (hlm : l <= m)
    (j : Server) (k : Buffer) :
    N.eventGridInput T K omega l j k <=
      N.eventGridInput T K omega m j k := by
  unfold eventGridInput eventGridPrefix
  have hprefix := eventTokenPrefix_append_drop N
    (eventGridCount_mono N hT K hlm) omega
  rw [<- hprefix, List.count_append]
  omega

private theorem eventGridInput_succ_sub
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : N.TokenPath) (l : Nat) (j : Server) (k : Buffer) :
    N.eventGridInput T K omega (l + 1) j k -
        N.eventGridInput T K omega l j k =
      (N.eventGridBatch T K omega l).count (j, k) := by
  exact (eventGridBatch_count N hT K omega l j k).symm

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

private theorem eventGridInput_sum
    (T : Real) (K : PNat) (omega : N.TokenPath) (l : Nat) :
    (Finset.univ.sum fun j : Server =>
      Finset.univ.sum fun k : Buffer =>
        N.eventGridInput T K omega l j k) =
      (N.eventGridPrefix T K omega l).length := by
  classical
  let tokens := N.eventGridPrefix T K omega l
  calc
    (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          N.eventGridInput T K omega l j k) =
        Finset.univ.sum fun jk : Server × Buffer =>
          tokens.count jk := by
      have hprod :
          (Finset.univ : Finset (Server × Buffer)) =
            (Finset.univ : Finset Server).product
              (Finset.univ : Finset Buffer) := by
        ext jk
        simp
      rw [hprod]
      simpa [tokens, eventGridInput] using
        (Finset.sum_product
          (Finset.univ : Finset Server)
          (Finset.univ : Finset Buffer)
          (fun jk : Server × Buffer => tokens.count jk)).symm
    _ = tokens.length := allTokenCounts_sum (Buffer := Buffer)
      (Server := Server) tokens

private theorem eventGridBatch_length_eq_input_sum
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : N.TokenPath) (l : Nat) :
    (N.eventGridBatch T K omega l).length =
      Finset.univ.sum (fun jk : Server × Buffer =>
        N.eventGridInput T K omega (l + 1) jk.1 jk.2 -
          N.eventGridInput T K omega l jk.1 jk.2) := by
  classical
  rw [eventGridBatch_length N hT]
  rw [show N.eventGridCount T K (l + 1) =
      (N.eventGridPrefix T K omega (l + 1)).length by
        simp [eventGridPrefix, eventTokenPrefix_length N]]
  rw [show N.eventGridCount T K l =
      (N.eventGridPrefix T K omega l).length by
        simp [eventGridPrefix, eventTokenPrefix_length N]]
  rw [<- eventGridInput_sum N T K omega (l + 1),
    <- eventGridInput_sum N T K omega l]
  rw [show
    (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          N.eventGridInput T K omega (l + 1) j k) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          N.eventGridInput T K omega l j k) =
      Finset.univ.sum (fun jk : Server × Buffer =>
        (N.eventGridBatch T K omega l).count jk) by
    rw [allTokenCounts_sum (Buffer := Buffer) (Server := Server)]
    rw [eventGridInput_sum N T K omega (l + 1),
      eventGridInput_sum N T K omega l]
    simpa [eventGridPrefix, eventTokenPrefix_length N] using
      (eventGridBatch_length N hT K omega l).symm]
  apply Finset.sum_congr rfl
  intro jk hjk
  exact (eventGridInput_succ_sub N hT K omega l jk.1 jk.2).symm

private theorem eventGridState_isFluidState
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (l : Nat) :
    IsFluidState (fun i =>
      (N.eventGridState initial T U K omega l i : Real) / (K : Nat)) := by
  constructor
  · intro i
    positivity
  · rw [<- Finset.sum_div]
    rw [show
      Finset.univ.sum
          (fun i => ((N.eventGridState initial T U K omega l i : Nat) : Real)) =
        ((K : Nat) : Real) by
      exact_mod_cast (N.eventGridState initial T U K omega l).total_jobs]
    exact div_self (by positivity)

private theorem eventGridAllocation_incompatible
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    N.eventGridAllocation initial T U K omega l i j k = 0 := by
  unfold eventGridAllocation
  exact ff_runAllocationCount_incompatible N _ _ _ _ _ _ hij

private theorem eventGridAllocation_le_input
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    N.eventGridAllocation initial T U K omega l i j k <=
      N.eventGridInput T K omega l j k := by
  unfold eventGridAllocation eventGridInput
  exact ff_runAllocationCount_le_count N _ _ _ _ _ _

private theorem eventGrid_balance
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (l : Nat) (i : Buffer) :
    (N.eventGridState initial T U K omega l i : Real) / (K : Nat) =
      (initial K i : Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          (N.eventGridAllocation initial T U K omega l q j i : Real) /
            (K : Nat)) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          (N.eventGridAllocation initial T U K omega l i j k : Real) /
            (K : Nat)) := by
  have h := ff_runTokens_runAllocationCount_balance N (U K)
    (initial K) (N.eventGridPrefix T K omega l) i
  unfold eventGridState eventGridAllocation
  have hK : ((K : Nat) : Real) ≠ 0 := by positivity
  push_cast at h
  simp_rw [← Finset.sum_div]
  field_simp [hK]
  linarith

private theorem eventPolygonalState_in_simplex
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    IsFluidState (N.eventPolygonalState initial T U K omega t) := by
  exact fi_polygonal_state_simplex K _ hT ht
    (fun l _ => eventGridState_isFluidState N initial T U K omega l)

private theorem eventPolygonalAllocation_incompatible
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (t : Real)
    (i : Buffer) (j : Server) (k : Buffer)
    (hij : Not (N.compatible i j)) :
    N.eventPolygonalAllocation initial T U K omega t i j k = 0 := by
  unfold eventPolygonalAllocation
  apply fi_polygonal_allocation_incompatible
    (e := fun l i j k =>
      (N.eventGridAllocation initial T U K omega l i j k : Real) / (K : Nat))
  intro l hl
  rw [eventGridAllocation_incompatible N initial T U K omega l i j k hij]
  simp

private theorem eventPolygonalState_initial
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (i : Buffer) :
    N.eventPolygonalState initial T U K omega 0 i =
      (initial K i : Real) / (K : Nat) := by
  rw [eventPolygonalState, fi_polygonal_initial K _ T hT]
  simp [eventGridState, eventGridPrefix, eventGridCount_zero,
    eventTokenPrefix, runTokens]

private theorem eventPolygonalAllocation_initial
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (i : Buffer) (j : Server) (k : Buffer) :
    N.eventPolygonalAllocation initial T U K omega 0 i j k = 0 := by
  rw [eventPolygonalAllocation, fi_polygonal_initial K _ T hT]
  simp [eventGridAllocation, eventGridPrefix, eventGridCount_zero,
    eventTokenPrefix, runAllocationCount]

private theorem eventPolygonal_balance
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) (i : Buffer) :
    N.eventPolygonalState initial T U K omega t i =
      (initial K i : Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          N.eventPolygonalAllocation initial T U K omega t q j i) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          N.eventPolygonalAllocation initial T U K omega t i j k) := by
  unfold eventPolygonalState eventPolygonalAllocation
  change
    fi_polygonalStatePath K
        (fun l i =>
          (N.eventGridState initial T U K omega l i : Real) / (K : Nat))
        T t i =
      (initial K i : Real) / (K : Nat) +
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun q : Buffer =>
          fi_polygonalAllocationPath K
            (fun l i j k =>
              (N.eventGridAllocation initial T U K omega l i j k : Real) /
                (K : Nat))
            T t q j i) -
      (Finset.univ.sum fun j : Server =>
        Finset.univ.sum fun k : Buffer =>
          fi_polygonalAllocationPath K
            (fun l i j k =>
              (N.eventGridAllocation initial T U K omega l i j k : Real) /
                (K : Nat))
            T t i j k)
  exact fi_polygonal_paths_balance
    (K := K)
    (x := fun l i =>
      (N.eventGridState initial T U K omega l i : Real) / (K : Nat))
    (e := fun l i j k =>
      (N.eventGridAllocation initial T U K omega l i j k : Real) / (K : Nat))
    (x0 := fun i => (initial K i : Real) / (K : Nat))
    hT ht (fun l _ i => eventGrid_balance N initial T U K omega l i) i

private def eventIntervalBatch
    (K : PNat) (omega : N.TokenPath) (s t : Real) :
    List (TokenType (Buffer := Buffer) (Server := Server)) :=
  (N.eventTokenPrefix (N.eventEpochCount K t) omega).drop
    (N.eventEpochCount K s)

private theorem eventTokenPrefix_interval
    (K : PNat) (omega : N.TokenPath) {s t : Real} (hst : s <= t) :
    N.eventTokenPrefix (N.eventEpochCount K t) omega =
      N.eventTokenPrefix (N.eventEpochCount K s) omega ++
        N.eventIntervalBatch K omega s t := by
  unfold eventIntervalBatch
  exact (eventTokenPrefix_append_drop N
    (eventEpochCount_mono N K hst) omega).symm

private theorem eventIntervalBatch_count
    (K : PNat) (omega : N.TokenPath) {s t : Real} (hst : s <= t)
    (j : Server) (k : Buffer) :
    (N.eventIntervalBatch K omega s t).count (j, k) =
      (N.eventTokenPrefix (N.eventEpochCount K t) omega).count (j, k) -
        (N.eventTokenPrefix (N.eventEpochCount K s) omega).count (j, k) := by
  rw [eventTokenPrefix_interval N K omega hst, List.count_append,
    Nat.add_sub_cancel_left]

private theorem eventIntervalBatch_length
    (K : PNat) (omega : N.TokenPath) {s t : Real} (hst : s <= t) :
    (N.eventIntervalBatch K omega s t).length =
      N.eventEpochCount K t - N.eventEpochCount K s := by
  unfold eventIntervalBatch
  rw [List.length_drop, eventTokenPrefix_length N]

private theorem scaledTokenInput_mono
    (K : PNat) (omega : N.TokenPath) {s t : Real} (hst : s <= t)
    (j : Server) (k : Buffer) :
    N.scaledTokenInput K omega s j k <=
      N.scaledTokenInput K omega t j k := by
  rw [scaledTokenInput_eq_prefix_count N,
    scaledTokenInput_eq_prefix_count N]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast
    (show
      (N.eventTokenPrefix (N.eventEpochCount K s) omega).count (j, k) <=
        (N.eventTokenPrefix (N.eventEpochCount K t) omega).count (j, k) by
      rw [eventTokenPrefix_interval N K omega hst, List.count_append]
      omega)

private theorem eventIntervalBatch_scaled_length
    (K : PNat) (omega : N.TokenPath) {s t : Real} (hst : s <= t) :
    ((N.eventIntervalBatch K omega s t).length : Real) / (K : Nat) =
      Finset.univ.sum (fun jk : Server × Buffer =>
        N.scaledTokenInput K omega t jk.1 jk.2 -
          N.scaledTokenInput K omega s jk.1 jk.2) := by
  rw [show
    (N.eventIntervalBatch K omega s t).length =
      Finset.univ.sum (fun jk : Server × Buffer =>
        (N.eventIntervalBatch K omega s t).count jk) by
    exact (allTokenCounts_sum (Buffer := Buffer) (Server := Server)
      (N.eventIntervalBatch K omega s t)).symm]
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro jk hjk
  rw [scaledTokenInput_eq_prefix_count N,
    scaledTokenInput_eq_prefix_count N,
    eventIntervalBatch_count N K omega hst]
  have hle :
      (N.eventTokenPrefix (N.eventEpochCount K s) omega).count jk <=
        (N.eventTokenPrefix (N.eventEpochCount K t) omega).count jk := by
    rw [eventTokenPrefix_interval N K omega hst, List.count_append]
    omega
  push_cast
  rw [Nat.cast_sub hle]
  ring

private theorem scaledQueueState_ordered_dist_le
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) {s t : Real} (hst : s <= t)
    (i : Buffer) :
    dist (N.scaledQueueStateFrom initial U K omega s i)
        (N.scaledQueueStateFrom initial U K omega t i) <=
      2 * Finset.univ.sum (fun jk : Server × Buffer =>
        (N.scaledTokenInput K omega t jk.1 jk.2 -
          N.scaledTokenInput K omega s jk.1 jk.2)) := by
  have hrun :=
    ff_runTokens_batch_l1_le_two_mul_length N (U K)
      (initial K)
      (N.eventTokenPrefix (N.eventEpochCount K s) omega)
      (N.eventIntervalBatch K omega s t)
  rw [<- eventTokenPrefix_interval N K omega hst] at hrun
  have hcoord :
      abs (((N.runTokens (U K) (initial K)
          (N.eventTokenPrefix (N.eventEpochCount K t) omega) i : Nat) :
            Real) -
        ((N.runTokens (U K) (initial K)
          (N.eventTokenPrefix (N.eventEpochCount K s) omega) i : Nat) :
            Real)) <=
        2 * (N.eventIntervalBatch K omega s t).length := by
    exact (Finset.single_le_sum
      (fun q _ => abs_nonneg
        (((N.runTokens (U K) (initial K)
            (N.eventTokenPrefix (N.eventEpochCount K t) omega) q : Nat) :
              Real) -
          ((N.runTokens (U K) (initial K)
            (N.eventTokenPrefix (N.eventEpochCount K s) omega) q : Nat) :
              Real)))
      (Finset.mem_univ i)).trans hrun
  unfold scaledQueueStateFrom
  rw [Real.dist_eq]
  have hK : (0 : Real) < (K : Nat) := by positivity
  rw [<- sub_div, abs_div, abs_of_pos hK]
  calc
    abs
          (((N.runTokens (U K) (initial K)
              (N.eventTokenPrefix (N.eventEpochCount K s) omega) i :
                Nat) : Real) -
            ((N.runTokens (U K) (initial K)
              (N.eventTokenPrefix (N.eventEpochCount K t) omega) i :
                Nat) : Real)) /
        (K : Nat) <=
        (2 * (N.eventIntervalBatch K omega s t).length : Real) /
          (K : Nat) := by
      apply div_le_div_of_nonneg_right _ hK.le
      simpa [abs_sub_comm] using hcoord
    _ = 2 * Finset.univ.sum (fun jk : Server × Buffer =>
          (N.scaledTokenInput K omega t jk.1 jk.2 -
            N.scaledTokenInput K omega s jk.1 jk.2)) := by
      rw [show
        (2 * (N.eventIntervalBatch K omega s t).length : Real) /
            (K : Nat) =
          2 * (((N.eventIntervalBatch K omega s t).length : Real) /
            (K : Nat)) by ring]
      rw [eventIntervalBatch_scaled_length N K omega hst]

private theorem scaledQueueState_dist_le
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (s t : Real) (i : Buffer) :
    dist (N.scaledQueueStateFrom initial U K omega s i)
        (N.scaledQueueStateFrom initial U K omega t i) <=
      2 * Finset.univ.sum (fun jk : Server × Buffer =>
        dist (N.scaledTokenInput K omega s jk.1 jk.2)
          (N.scaledTokenInput K omega t jk.1 jk.2)) := by
  rcases le_total s t with hst | hts
  · have h := scaledQueueState_ordered_dist_le N initial U K omega hst i
    convert h using 1
    apply congrArg
    apply Finset.sum_congr rfl
    intro jk hjk
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (scaledTokenInput_mono N K omega hst jk.1 jk.2))]
  · rw [dist_comm]
    have h := scaledQueueState_ordered_dist_le N initial U K omega hts i
    convert h using 1
    apply congrArg
    apply Finset.sum_congr rfl
    intro jk hjk
    rw [Real.dist_eq, abs_of_nonneg
      (sub_nonneg.mpr (scaledTokenInput_mono N K omega hts jk.1 jk.2))]

private theorem scaledAllocation_ordered_increment
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) {s t : Real} (hst : s <= t)
    (i : Buffer) (j : Server) (k : Buffer) :
    0 <= N.scaledAllocationFrom initial U K omega t i j k -
        N.scaledAllocationFrom initial U K omega s i j k /\
      N.scaledAllocationFrom initial U K omega t i j k -
          N.scaledAllocationFrom initial U K omega s i j k <=
        N.scaledTokenInput K omega t j k -
          N.scaledTokenInput K omega s j k := by
  have happend :=
    ff_runAllocationCount_append N (U K) (initial K)
      (N.eventTokenPrefix (N.eventEpochCount K s) omega)
      (N.eventIntervalBatch K omega s t) i j k
  rw [<- eventTokenPrefix_interval N K omega hst] at happend
  have hle :=
    ff_runAllocationCount_le_count N (U K)
      (N.runTokens (U K) (initial K)
        (N.eventTokenPrefix (N.eventEpochCount K s) omega))
      (N.eventIntervalBatch K omega s t) i j k
  unfold scaledAllocationFrom
  have hK : (0 : Real) < (K : Nat) := by positivity
  constructor
  · apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ hK.le
    exact_mod_cast (show
      N.runAllocationCount (U K) (initial K)
          (N.eventTokenPrefix (N.eventEpochCount K s) omega) i j k <=
        N.runAllocationCount (U K) (initial K)
          (N.eventTokenPrefix (N.eventEpochCount K t) omega) i j k by
      omega)
  · rw [scaledTokenInput_eq_prefix_count N,
      scaledTokenInput_eq_prefix_count N]
    have halloc_le :
        N.runAllocationCount (U K) (initial K)
            (N.eventTokenPrefix (N.eventEpochCount K s) omega) i j k <=
          N.runAllocationCount (U K) (initial K)
            (N.eventTokenPrefix (N.eventEpochCount K t) omega) i j k := by
      omega
    have hcount_le :
        (N.eventTokenPrefix (N.eventEpochCount K s) omega).count (j, k) <=
          (N.eventTokenPrefix (N.eventEpochCount K t) omega).count (j, k) := by
      rw [eventTokenPrefix_interval N K omega hst, List.count_append]
      omega
    have hnat :
        N.runAllocationCount (U K) (initial K)
              (N.eventTokenPrefix (N.eventEpochCount K t) omega) i j k -
            N.runAllocationCount (U K) (initial K)
              (N.eventTokenPrefix (N.eventEpochCount K s) omega) i j k <=
          (N.eventTokenPrefix (N.eventEpochCount K t) omega).count (j, k) -
            (N.eventTokenPrefix (N.eventEpochCount K s) omega).count
              (j, k) := by
      rw [eventIntervalBatch_count N K omega hst] at hle
      omega
    rw [<- sub_div, <- sub_div]
    apply div_le_div_of_nonneg_right _ hK.le
    rw [← Nat.cast_sub halloc_le, ← Nat.cast_sub hcount_le]
    exact_mod_cast hnat

private theorem scaledAllocation_dist_le
    (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (s t : Real)
    (i : Buffer) (j : Server) (k : Buffer) :
    dist (N.scaledAllocationFrom initial U K omega s i j k)
        (N.scaledAllocationFrom initial U K omega t i j k) <=
      dist (N.scaledTokenInput K omega s j k)
        (N.scaledTokenInput K omega t j k) := by
  rcases le_total s t with hst | hts
  · have h := scaledAllocation_ordered_increment N initial U K omega hst i j k
    rw [Real.dist_eq, Real.dist_eq]
    rw [abs_sub_comm, abs_of_nonneg h.1]
    rw [abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (scaledTokenInput_mono N K omega hst j k))]
    exact h.2
  · rw [dist_comm, dist_comm
      (N.scaledTokenInput K omega s j k)]
    have h := scaledAllocation_ordered_increment N initial U K omega hts i j k
    rw [Real.dist_eq, Real.dist_eq]
    rw [abs_sub_comm, abs_of_nonneg h.1]
    rw [abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (scaledTokenInput_mono N K omega hts j k))]
    exact h.2

private theorem stateLimit_continuousOn
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall i, ContinuousOn (fun t => X t i) (Icc (0 : Real) T) := by
  have hinput := hconverges.1
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.scaledTokenInput (K r) omega t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  change UniformlyOnIcc T
      (fun r t i => N.scaledQueueStateFrom initial U (K r) omega t i)
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
      dist (X s i) (N.scaledQueueStateFrom initial U (K r) omega s i) <
        epsilon / 8 := by
    rw [Real.dist_eq, abs_sub_comm]
    exact hrState r hrS s hs i
  have htState :
      dist (N.scaledQueueStateFrom initial U (K r) omega t i) (X t i) <
        epsilon / 8 := by
    rw [Real.dist_eq]
    exact hrState r hrS t ht i
  have hAmetric : dist (Avec s) (Avec t) < eta :=
    hdeltaWorks s hs t ht hst
  have hterm (jk : Server × Buffer) :
      dist (N.scaledTokenInput (K r) omega s jk.1 jk.2)
          (N.scaledTokenInput (K r) omega t jk.1 jk.2) <
        3 * eta := by
    have hsInput := hrInput r hrI s hs jk
    have htInput := hrInput r hrI t ht jk
    have hcoord :
        dist (Avec s jk) (Avec t jk) <= dist (Avec s) (Avec t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl : dist (Avec s) (Avec t) <= dist (Avec s) (Avec t)) jk
    rw [Real.dist_eq]
    calc
      abs (N.scaledTokenInput (K r) omega s jk.1 jk.2 -
          N.scaledTokenInput (K r) omega t jk.1 jk.2) <=
          abs (N.scaledTokenInput (K r) omega s jk.1 jk.2 -
            A s jk.1 jk.2) +
          abs (A s jk.1 jk.2 - A t jk.1 jk.2) +
          abs (A t jk.1 jk.2 -
            N.scaledTokenInput (K r) omega t jk.1 jk.2) := by
        calc
          _ <= abs (N.scaledTokenInput (K r) omega s jk.1 jk.2 -
                A s jk.1 jk.2) +
              abs (A s jk.1 jk.2 -
                N.scaledTokenInput (K r) omega t jk.1 jk.2) :=
            abs_sub_le _ _ _
          _ <= _ := by
            have htri :=
              abs_sub_le (A s jk.1 jk.2) (A t jk.1 jk.2)
                (N.scaledTokenInput (K r) omega t jk.1 jk.2)
            linarith
      _ < eta + eta + eta := by
        have hcoord' :
            abs (A s jk.1 jk.2 - A t jk.1 jk.2) < eta := by
          simpa [Avec, Real.dist_eq] using hcoord.trans_lt hAmetric
        have htInput' :
            abs (A t jk.1 jk.2 -
              N.scaledTokenInput (K r) omega t jk.1 jk.2) < eta := by
          simpa [abs_sub_comm] using htInput
        gcongr
      _ = 3 * eta := by ring
  have hraw :=
    scaledQueueState_dist_le N initial U (K r) omega s t i
  have hsum :
      Finset.univ.sum (fun jk : Server × Buffer =>
        dist (N.scaledTokenInput (K r) omega s jk.1 jk.2)
          (N.scaledTokenInput (K r) omega t jk.1 jk.2)) <
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
        dist (X s i) (N.scaledQueueStateFrom initial U (K r) omega s i) +
        dist (N.scaledQueueStateFrom initial U (K r) omega s i)
          (N.scaledQueueStateFrom initial U (K r) omega t i) +
        dist (N.scaledQueueStateFrom initial U (K r) omega t i) (X t i) := by
      calc
        _ <= dist (X s i) (N.scaledQueueStateFrom initial U (K r) omega s i) +
            dist (N.scaledQueueStateFrom initial U (K r) omega s i) (X t i) :=
          dist_triangle _ _ _
        _ <= _ := by
          have htri :=
            dist_triangle
              (N.scaledQueueStateFrom initial U (K r) omega s i)
              (N.scaledQueueStateFrom initial U (K r) omega t i) (X t i)
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

private theorem eventGridTime_eq_ffGridTime
    (T : Real) (K : PNat) {l : Nat} (hl : l <= (K : Nat)) :
    eventGridTime T K l = ff_gridTime T K l := by
  simp [eventGridTime, ff_gridTime, min_eq_left hl]

private theorem polygonalInterpolate_error_of_nodes
    {T : Real} (hT : 0 < T) (K : PNat)
    (values : Nat -> Real) (g : Real -> Real)
    (delta eta : Real)
    (hnode : forall l, l <= (K : Nat) ->
      abs (values l - g (eventGridTime T K l)) <= delta)
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
          abs (eventGridTime T K l - t) <= T / (K : Nat) := by
        rw [eventGridTime_eq_ffGridTime T K hlK]
        exact hdistFF
      have hosc' := hosc (eventGridTime T K l)
        (eventGridTime_mem_Icc hT K hlK) t ht hdist
      calc
        abs (values l - g t) <=
            abs (values l - g (eventGridTime T K l)) +
              abs (g (eventGridTime T K l) - g t) := abs_sub_le _ _ _
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
          abs (values r l - g (eventGridTime T (K r) l)) < epsilon) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall t, t ∈ Icc (0 : Real) T ->
          abs (fi_polygonalInterpolate (K r) (values r) t T - g t) <
            epsilon := by
  have huc : UniformContinuousOn g (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  have hKreal :
      Tendsto (fun r => (((K r : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (pnat_val_tendsto_atTop hK)
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
    polygonalInterpolate_error_of_nodes hT (K r) (values r) g
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

private theorem eventPolygonalInput_converges
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall jk : Server × Buffer, forall t, t ∈ Icc (0 : Real) T ->
          dist (N.eventPolygonalInput T (K r) omega t jk.1 jk.2)
            (A t jk.1 jk.2) < epsilon := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.scaledTokenInput (K r) omega t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  intro epsilon hepsilon
  have hcoord (jk : Server × Buffer) :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall t, t ∈ Icc (0 : Real) T ->
            abs (N.eventPolygonalInput T (K r) omega t jk.1 jk.2 -
              A t jk.1 jk.2) < epsilon := by
    apply polygonal_converges_of_nodes hT K hK
      (fun r l =>
        (N.eventGridInput T (K r) omega l jk.1 jk.2 : Real) /
          (K r : Nat))
      (fun t => A t jk.1 jk.2)
    · simpa [uIcc_of_le hT.le] using (hA jk.1 jk.2).continuousOn
    · intro eta heta
      obtain ⟨r0, hr0⟩ := hinput eta heta
      refine ⟨r0, fun r hr l hl => ?_⟩
      have hnode := hr0 r hr (eventGridTime T (K r) l)
        (eventGridTime_mem_Icc hT (K r) hl) jk
      change
        abs (N.scaledTokenInput (K r) omega
          (eventGridTime T (K r) l) jk.1 jk.2 -
            A (eventGridTime T (K r) l) jk.1 jk.2) < eta at hnode
      rw [scaledTokenInput_eq_prefix_count N] at hnode
      simpa only [eventGridInput, eventGridPrefix, eventGridCount] using hnode
  obtain ⟨r0, hr0⟩ :=
    exists_common_nat_bound (P := fun jk : Server × Buffer => fun r =>
        forall t, t ∈ Icc (0 : Real) T ->
          abs (N.eventPolygonalInput T (K r) omega t jk.1 jk.2 -
            A t jk.1 jk.2) < epsilon)
      (fun jk => hcoord jk epsilon hepsilon)
  refine ⟨r0, fun r hr jk t ht => ?_⟩
  rw [Real.dist_eq]
  exact hr0 r hr jk t ht

private theorem eventPolygonalState_converges
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall i : Buffer, forall t, t ∈ Icc (0 : Real) T ->
          dist (N.eventPolygonalState initial T U (K r) omega t i)
            (X t i) < epsilon := by
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t i => N.scaledQueueStateFrom initial U (K r) omega t i)
      X at hstate
  have hXcont :=
    stateLimit_continuousOn N initial hT U K omega A X hA hconverges
  intro epsilon hepsilon
  have hcoord (i : Buffer) :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall t, t ∈ Icc (0 : Real) T ->
            abs (N.eventPolygonalState initial T U (K r) omega t i -
              X t i) < epsilon := by
    apply polygonal_converges_of_nodes hT K hK
      (fun r l =>
        (N.eventGridState initial T U (K r) omega l i : Real) / (K r : Nat))
      (fun t => X t i) (hXcont i)
    intro eta heta
    obtain ⟨r0, hr0⟩ := hstate eta heta
    refine ⟨r0, fun r hr l hl => ?_⟩
    exact hr0 r hr (eventGridTime T (K r) l)
      (eventGridTime_mem_Icc hT (K r) hl) i
  obtain ⟨r0, hr0⟩ :=
    exists_common_nat_bound (P := fun i : Buffer => fun r =>
        forall t, t ∈ Icc (0 : Real) T ->
          abs (N.eventPolygonalState initial T U (K r) omega t i -
            X t i) < epsilon)
      (fun i => hcoord i epsilon hepsilon)
  refine ⟨r0, fun r hr i t ht => ?_⟩
  rw [Real.dist_eq]
  exact hr0 r hr i t ht

private theorem eventGridAllocation_step_le
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (l : Nat)
    (i : Buffer) (j : Server) (k : Buffer) :
    abs
        ((N.eventGridAllocation initial T U K omega (l + 1) i j k : Real) /
            (K : Nat) -
          (N.eventGridAllocation initial T U K omega l i j k : Real) /
            (K : Nat)) <=
      Finset.univ.sum (fun jk : Server × Buffer =>
        (N.eventGridInput T K omega (l + 1) jk.1 jk.2 : Real) /
            (K : Nat) -
          (N.eventGridInput T K omega l jk.1 jk.2 : Real) /
            (K : Nat)) := by
  have happend :=
    eventGridAllocation_succ N initial hT U K omega l i j k
  have htail :=
    ff_runAllocationCount_le_count N (U K)
      (N.eventGridState initial T U K omega l)
      (N.eventGridBatch T K omega l) i j k
  have hmono :
      N.eventGridAllocation initial T U K omega l i j k <=
        N.eventGridAllocation initial T U K omega (l + 1) i j k := by
    omega
  have hdiff :
      N.eventGridAllocation initial T U K omega (l + 1) i j k -
          N.eventGridAllocation initial T U K omega l i j k <=
        (N.eventGridBatch T K omega l).length := by
    have htailLength := htail.trans List.count_le_length
    omega
  have hsum :=
    eventGridBatch_length_eq_input_sum N hT K omega l
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
      (eventGridInput_mono N hT K omega (Nat.le_succ l) jk.1 jk.2)]
  rw [← Nat.cast_sum]
  exact_mod_cast hdiff.trans_eq hsum

private theorem eventPolygonalAllocation_increment_domination
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (i : Buffer) (j : Server) (k : Buffer)
    {s t : Real} (hs : s ∈ Icc (0 : Real) T)
    (ht : t ∈ Icc (0 : Real) T) :
    dist (N.eventPolygonalAllocation initial T U K omega s i j k)
        (N.eventPolygonalAllocation initial T U K omega t i j k) <=
      Finset.univ.sum (fun jk : Server × Buffer =>
        dist (N.eventPolygonalInput T K omega s jk.1 jk.2)
          (N.eventPolygonalInput T K omega t jk.1 jk.2)) := by
  let values : Nat -> Real := fun l =>
    (N.eventGridAllocation initial T U K omega l i j k : Real) / (K : Nat)
  let control : Server × Buffer -> Nat -> Real := fun jk l =>
    (N.eventGridInput T K omega l jk.1 jk.2 : Real) / (K : Nat)
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
    exact_mod_cast eventGridInput_mono N hT K omega
      (Nat.le_succ l) jk.1 jk.2
  have hstep : forall l, l < (K : Nat) ->
      abs (values (l + 1) - values l) <=
        Finset.univ.sum (fun jk =>
          control jk (l + 1) - control jk l) := by
    intro l hl
    exact eventGridAllocation_step_le N initial hT U K omega l i j k
  exact fi_polygonal_increment_domination K values control hT hs ht
    hcontrol hstep

private theorem eventGridAllocation_scaled_le_T
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) {l : Nat}
    (hl : l <= (K : Nat))
    (i : Buffer) (j : Server) (k : Buffer) :
    (N.eventGridAllocation initial T U K omega l i j k : Real) / (K : Nat) <= T := by
  have halloc :
      N.eventGridAllocation initial T U K omega l i j k <=
        N.eventGridCount T K l := by
    calc
      _ <= N.eventGridInput T K omega l j k :=
        eventGridAllocation_le_input N initial T U K omega l i j k
      _ <= (N.eventGridPrefix T K omega l).length :=
        List.count_le_length
      _ = N.eventGridCount T K l := by
        simp [eventGridPrefix, eventTokenPrefix_length N]
  have hcount :
      ((N.eventGridCount T K l : Nat) : Real) <=
        (K : Nat) * eventGridTime T K l := by
    have hfloor :=
      Nat.floor_le
        (mul_nonneg (eventGridTime_mem_Icc hT K hl).1
          (Nat.cast_nonneg (K : Nat)))
    unfold eventGridCount eventEpochCount
    rw [max_eq_left (eventGridTime_mem_Icc hT K hl).1]
    nlinarith
  have htime := (eventGridTime_mem_Icc hT K hl).2
  have hKreal : (0 : Real) < (K : Nat) := by positivity
  apply (div_le_iff₀ hKreal).2
  have hallocReal :
      (N.eventGridAllocation initial T U K omega l i j k : Real) <=
        (N.eventGridCount T K l : Real) := by
    exact_mod_cast halloc
  have hcountT :
      (N.eventGridCount T K l : Real) <= T * (K : Nat) := by
    exact le_trans hcount (by nlinarith)
  exact le_trans hallocReal hcountT

private theorem eventPolygonalAllocation_abs_le_T
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (i : Buffer) (j : Server) (k : Buffer)
    {t : Real} (ht : t ∈ Icc (0 : Real) T) :
    abs (N.eventPolygonalAllocation initial T U K omega t i j k) <= T := by
  let r : Real := ((K : Nat) : Real) * t / T
  have hr0 : 0 <= r := by
    dsimp [r]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) ht.1) hT.le
  have hrK : r <= (K : Nat) := by
    dsimp [r]
    apply (div_le_iff₀ hT).2
    nlinarith [ht.2]
  have hsum :
      Finset.sum (Finset.range ((K : Nat) + 1)) (fi_hatWeight r) = 1 :=
    fi_sum_hatWeight_eq_one K hr0 hrK
  have hnonneg :
      0 <= N.eventPolygonalAllocation initial T U K omega t i j k := by
    unfold eventPolygonalAllocation fi_polygonalInterpolate
    apply Finset.sum_nonneg
    intro l hl
    exact mul_nonneg (fi_hatWeight_nonnegative _ _)
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  rw [abs_of_nonneg hnonneg]
  unfold eventPolygonalAllocation fi_polygonalInterpolate
  change
    Finset.sum (Finset.range ((K : Nat) + 1)) (fun l =>
      fi_hatWeight r l *
        (((N.eventGridAllocation initial T U K omega l i j k : Nat) : Real) /
          (K : Nat))) <= T
  calc
    _ <= Finset.sum (Finset.range ((K : Nat) + 1))
        (fun l => fi_hatWeight r l * T) := by
      apply Finset.sum_le_sum
      intro l hl
      apply mul_le_mul_of_nonneg_left
      · exact eventGridAllocation_scaled_le_T N initial hT U K omega
          (by
            have hl' := Finset.mem_range.mp hl
            omega : l <= (K : Nat)) i j k
      · exact fi_hatWeight_nonnegative r l
    _ = T := by
      rw [<- Finset.sum_mul, hsum, one_mul]

private theorem exists_eventPolygonalAllocation_limit
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X) :
    exists q : Nat -> Nat, StrictMono q /\
      exists E : FluidAllocationPath Buffer Server,
        (forall i j k, ContinuousOn (fun t => E t i j k)
          (Icc (0 : Real) T)) /\
        (forall epsilon, 0 < epsilon ->
          exists r0, forall r, r0 <= r ->
            forall i j k t, t ∈ Icc (0 : Real) T ->
              dist
                (N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
                (E t i j k) < epsilon) := by
  let f : Nat -> (Buffer × Server × Buffer) -> Real -> Real :=
    fun r ijk t =>
      N.eventPolygonalAllocation initial T U (K r) omega t
        ijk.1 ijk.2.1 ijk.2.2
  let g : Nat -> (Server × Buffer) -> Real -> Real :=
    fun r jk t => N.eventPolygonalInput T (K r) omega t jk.1 jk.2
  let control : (Server × Buffer) -> Real -> Real :=
    fun jk t => A t jk.1 jk.2
  have hf :
      forall r ijk, ContinuousOn (f r ijk) (Icc (0 : Real) T) := by
    intro r ijk
    exact (continuous_eventPolygonalAllocation N initial T U (K r) omega
      ijk.1 ijk.2.1 ijk.2.2).continuousOn
  have hbound :
      forall r ijk t, t ∈ Icc (0 : Real) T ->
        abs (f r ijk t) <= T := by
    intro r ijk t ht
    exact eventPolygonalAllocation_abs_le_T N initial hT U (K r) omega
      ijk.1 ijk.2.1 ijk.2.2 ht
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
      eventPolygonalInput_converges N initial hT U K hK omega A X hA
        hconverges epsilon hepsilon
  have hdom :
      forall r ijk s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T ->
          dist (f r ijk s) (f r ijk t) <=
            Finset.univ.sum (fun jk =>
              dist (g r jk s) (g r jk t)) := by
    intro r ijk s hs t ht
    exact eventPolygonalAllocation_increment_domination N initial hT U (K r)
      omega ijk.1 ijk.2.1 ijk.2.2 hs ht
  obtain ⟨q, hq, limit, hlimitCont, hlimitConv⟩ :=
    FluidControlledCompactness.exists_uniformly_convergent_subsequence_finite
      (f := f) (g := g) (control := control)
      (a := (0 : Real)) (b := T) (M := T)
      hf hbound hcontrol hgconv hdom
  let E : FluidAllocationPath Buffer Server :=
    fun t i j k => limit (i, j, k) t
  refine ⟨q, hq, E, ?_, ?_⟩
  · intro i j k
    exact hlimitCont (i, j, k)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hlimitConv epsilon hepsilon
    refine ⟨r0, fun r hr i j k t ht => ?_⟩
    exact hr0 r hr (i, j, k) t ht

private theorem eventPolygonalAllocation_approximates_scaled
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall i j k t, t ∈ Icc (0 : Real) T ->
          dist
            (N.eventPolygonalAllocation initial T U (K r) omega t i j k)
            (N.scaledAllocationFrom initial U (K r) omega t i j k) < epsilon := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.scaledTokenInput (K r) omega t jk.1 jk.2)
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
    tendsto_natCast_atTop_atTop.comp (pnat_val_tendsto_atTop hK)
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
            (N.scaledAllocationFrom initial U (K r) omega s i j k -
              N.scaledAllocationFrom initial U (K r) omega u i j k) <=
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
        dist (N.scaledTokenInput (K r) omega s j k)
          (N.scaledTokenInput (K r) omega u j k) <
            3 * (epsilon / 4) := by
      calc
        _ <= dist (N.scaledTokenInput (K r) omega s j k) (A s j k) +
              dist (A s j k) (A u j k) +
              dist (A u j k)
                (N.scaledTokenInput (K r) omega u j k) := by
          calc
            _ <= dist (N.scaledTokenInput (K r) omega s j k) (A s j k) +
                dist (A s j k)
                  (N.scaledTokenInput (K r) omega u j k) :=
              dist_triangle _ _ _
            _ <= _ := by
              have htri := dist_triangle (A s j k) (A u j k)
                (N.scaledTokenInput (K r) omega u j k)
              linarith
        _ < epsilon / 4 + epsilon / 4 + epsilon / 4 := by
          have huInput' :
              dist (A u j k)
                (N.scaledTokenInput (K r) omega u j k) < epsilon / 4 := by
            simpa [Real.dist_eq, abs_sub_comm] using huInput
          exact add_lt_add (add_lt_add hsInput
            (hcoord.trans_lt hAu)) huInput'
        _ = _ := by ring
    have halloc :=
      scaledAllocation_dist_le N initial U (K r) omega s u i j k
    rw [Real.dist_eq] at halloc
    exact halloc.trans (le_of_lt htoken)
  have hnode :
      forall l, l <= (K r : Nat) ->
        abs
          (((N.eventGridAllocation initial T U (K r) omega l i j k : Real) /
              (K r : Nat)) -
            N.scaledAllocationFrom initial U (K r) omega
              (eventGridTime T (K r) l) i j k) <= 0 := by
    intro l hl
    have heq :
        N.scaledAllocationFrom initial U (K r) omega
            (eventGridTime T (K r) l) i j k =
          (N.eventGridAllocation initial T U (K r) omega l i j k : Real) /
            (K r : Nat) := by
      rfl
    rw [heq, sub_self, abs_zero]
  have herr :=
    polygonalInterpolate_error_of_nodes hT (K r)
      (fun l =>
        (N.eventGridAllocation initial T U (K r) omega l i j k : Real) /
          (K r : Nat))
      (fun s => N.scaledAllocationFrom initial U (K r) omega s i j k)
      0 (3 * (epsilon / 4)) hnode hosc t ht
  rw [Real.dist_eq]
  exact herr.trans_lt (by nlinarith)

private theorem eventInput_isFluidInput
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X) :
    IsFluidInput T A := by
  have hinput := hconverges.1
  change UniformlyOnIcc T
      (fun r t (jk : Server × Buffer) =>
        N.scaledTokenInput (K r) omega t jk.1 jk.2)
      (fun t jk => A t jk.1 jk.2) at hinput
  have hpoint (t : Real) (ht : t ∈ Icc (0 : Real) T)
      (j : Server) (k : Buffer) :
      Tendsto (fun r => N.scaledTokenInput (K r) omega t j k)
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
        scaledTokenInput_mono N (K r) omega hst j k)
  · intro j k
    have hzero :
        (fun r => N.scaledTokenInput (K r) omega 0 j k) =
          fun _ => 0 := by
      funext r
      simp [scaledTokenInput, eventEpochCount]
    apply tendsto_nhds_unique (hpoint 0 ⟨le_rfl, hT.le⟩ j k)
    rw [hzero]
    exact tendsto_const_nhds

private theorem eventAllocation_raw_converges
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    (N.eventEpochExecutionFrom initial).AllocationConvergesOn T U K q omega E := by
  have happ :=
    eventPolygonalAllocation_approximates_scaled
      N initial hT U K hK omega A X hA hconverges
  change UniformlyOnIcc T
      (fun r t (ijk : Buffer × Server × Buffer) =>
        N.scaledAllocationFrom initial U (K (q r)) omega t
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
          (N.scaledAllocationFrom initial U (K (q r)) omega t
            ijk.1 ijk.2.1 ijk.2.2)
          (N.eventPolygonalAllocation initial T U (K (q r)) omega t
            ijk.1 ijk.2.1 ijk.2.2) < epsilon / 2 := by
    simpa [dist_comm] using ha
  change
    dist
      (N.scaledAllocationFrom initial U (K (q r)) omega t
        ijk.1 ijk.2.1 ijk.2.2)
      (E t ijk.1 ijk.2.1 ijk.2.2) < epsilon
  calc
    _ <= _ := dist_triangle _ _ _
    _ < epsilon / 2 + epsilon / 2 := add_lt_add ha' hp
    _ = epsilon := by ring

private noncomputable def eventGridPreActionStates
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (j : Server) (k : Buffer) (l : Fin (K : Nat)) :
    List (JobState Buffer (K : Nat)) :=
  N.fluidEmpiricalPreActionStates (U K)
    (N.eventGridState initial T U K omega l.val)
    (N.eventGridBatch T K omega l.val) j k

private noncomputable def eventPolygonalAction
    (T : Real) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (j : Server) (k : Buffer) (t : Real) : ActionVector Buffer :=
  scaledBatchedPolicyActionInterpolate N K U K
    (N.eventGridPreActionStates initial T U K omega j k) j k T t

private theorem edgeProgress_eq_ff_clamp (r : Real) (l : Nat) :
    edgeProgress r l = ff_clamp01 (r - l) := by
  unfold edgeProgress ff_clamp01
  rcases le_total (r - l) 0 with h | h
  · simp [max_eq_left h, min_eq_right (h.trans zero_le_one)]
  · by_cases h1 : r - l <= 1
    · simp [max_eq_right h, min_eq_right h1]
    · have h1' : 1 <= r - l := le_of_not_ge h1
      simp [max_eq_right h, min_eq_left h1']

private theorem ff_rampInterpolate_div
    (K : PNat) (values : Nat -> Real) (c t T : Real) :
    ff_rampInterpolate K (fun l => values l / c) t T =
      ff_rampInterpolate K values t T / c := by
  unfold ff_rampInterpolate
  rw [show
    Finset.sum (Finset.range (K : Nat)) (fun l =>
      (values (l + 1) / c - values l / c) *
        ff_clamp01 (((K : Nat) : Real) * t / T - l)) =
      (Finset.sum (Finset.range (K : Nat)) (fun l =>
        (values (l + 1) - values l) *
          ff_clamp01 (((K : Nat) : Real) * t / T - l))) / c by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l hl
    ring]
  ring

private theorem eventGridPreActionStates_length
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (j : Server) (k : Buffer) (l : Fin (K : Nat)) :
    (N.eventGridPreActionStates initial T U K omega j k l).length =
      N.eventGridInput T K omega (l.val + 1) j k -
        N.eventGridInput T K omega l.val j k := by
  unfold eventGridPreActionStates
  rw [N.fluidEmpiricalPreActionStates_length]
  exact eventGridBatch_count N hT K omega l.val j k

private theorem eventGridPreAction_sum_some
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (l : Fin (K : Nat)) (i : Buffer) (j : Server) (k : Buffer) :
    ((N.eventGridPreActionStates initial T U K omega j k l).map
      (fun y => N.actionDirac (U K y j k))).sum (some i) =
      (N.eventGridAllocation initial T U K omega (l.val + 1) i j k : Real) -
        (N.eventGridAllocation initial T U K omega l.val i j k : Real) := by
  let z := N.eventGridState initial T U K omega l.val
  let batch := N.eventGridBatch T K omega l.val
  have hemp := congrFun
    (N.fluidEmpiricalActionCount_eq_preActionState_sum
      (U K) z batch j k) (some i)
  rw [N.fluidEmpiricalActionCount_some_eq_runAllocationCount] at hemp
  change
    ((N.fluidEmpiricalPreActionStates (U K) z batch j k).map
      (fun y => N.actionDirac (U K y j k))).sum (some i) = _
  rw [<- hemp]
  have hsucc :=
    eventGridAllocation_succ N initial hT U K omega l.val i j k
  dsimp [z, batch]
  rw [hsucc, Nat.cast_add]
  ring

private theorem eventPolygonalInput_eq_batched
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    N.eventPolygonalInput T K omega t j k =
      scaledBatchedInputInterpolate K
        (N.eventGridPreActionStates initial T U K omega j k) T t := by
  let states := N.eventGridPreActionStates initial T U K omega j k
  let values : Nat -> Real :=
    fun l => (N.eventGridInput T K omega l j k : Real)
  let r : Real := ((K : Nat) : Real) * t / T
  have hbatch :
      batchedInputInterpolate states r =
        ff_rampInterpolate K values t T := by
    rw [batchedInputInterpolate_eq_cumulativeRamp states values r]
    · unfold ff_rampInterpolate
      dsimp [r]
      apply congrArg (fun x => values 0 + x)
      apply Finset.sum_congr rfl
      intro l hl
      rw [edgeProgress_eq_ff_clamp]
    · simp [values, eventGridInput, eventGridPrefix,
        eventGridCount_zero, eventTokenPrefix]
    · intro l
      rw [eventGridPreActionStates_length N initial hT U K omega j k l]
      dsimp [values]
      rw [Nat.cast_sub
        (eventGridInput_mono N hT K omega
          (Nat.le_succ l.val) j k)]
  unfold eventPolygonalInput scaledBatchedInputInterpolate
  rw [fi_polygonalInterpolate_eq_ramp K _ hT ht]
  change ff_rampInterpolate K (fun l =>
      (N.eventGridInput T K omega l j k : Real) / (K : Nat)) t T =
    batchedInputInterpolate states r / (K : Nat)
  rw [hbatch]
  exact ff_rampInterpolate_div K values (K : Nat) t T

private theorem eventPolygonalAction_some
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (i : Buffer) (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    N.eventPolygonalAction initial T U K omega j k t (some i) =
      N.eventPolygonalAllocation initial T U K omega t i j k := by
  let states := N.eventGridPreActionStates initial T U K omega j k
  let values : Nat -> Real :=
    fun l => (N.eventGridAllocation initial T U K omega l i j k : Real)
  let r : Real := ((K : Nat) : Real) * t / T
  have hbatch :
      batchedPolicyActionInterpolate N U K states j k r (some i) =
        ff_rampInterpolate K values t T := by
    rw [batchedPolicyActionInterpolate_eq_batch_sum]
    unfold ff_rampInterpolate
    rw [show values 0 = 0 by
      simp [values, eventGridAllocation, eventGridPrefix,
        eventGridCount_zero, eventTokenPrefix, runAllocationCount]]
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
    rw [eventGridPreAction_sum_some N initial hT U K omega l i j k]
    rw [edgeProgress_eq_ff_clamp]
  unfold eventPolygonalAction scaledBatchedPolicyActionInterpolate
  change
    batchedPolicyActionInterpolate N U K states j k r (some i) /
        (K : Nat) =
      fi_polygonalInterpolate K
        (fun l => (N.eventGridAllocation initial T U K omega l i j k : Real) /
          (K : Nat)) t T
  rw [hbatch, fi_polygonalInterpolate_eq_ramp K _ hT ht]
  exact (ff_rampInterpolate_div K values (K : Nat) t T).symm

private theorem eventPolygonalAction_sum
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    Finset.univ.sum (N.eventPolygonalAction initial T U K omega j k t) =
      N.eventPolygonalInput T K omega t j k := by
  rw [eventPolygonalInput_eq_batched N initial hT U K omega j k ht]
  unfold eventPolygonalAction scaledBatchedPolicyActionInterpolate
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
      ((N.eventGridPreActionStates initial T U K omega j k q.1).get q.2)
      j k)).2]
  rw [mul_one]

private theorem eventPolygonalAction_none
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath)
    (j : Server) (k : Buffer) {t : Real}
    (ht : t ∈ Icc (0 : Real) T) :
    N.eventPolygonalAction initial T U K omega j k t none =
      N.eventPolygonalInput T K omega t j k -
        Finset.univ.sum (fun i : Buffer =>
          N.eventPolygonalAllocation initial T U K omega t i j k) := by
  have hsum := eventPolygonalAction_sum N initial hT U K omega j k ht
  rw [show
    Finset.univ.sum (N.eventPolygonalAction initial T U K omega j k t) =
      N.eventPolygonalAction initial T U K omega j k t none +
        Finset.univ.sum (fun i : Buffer =>
          N.eventPolygonalAction initial T U K omega j k t (some i)) by
    rw [Fintype.sum_option]] at hsum
  simp_rw [eventPolygonalAction_some N initial hT U K omega _ _ _ ht] at hsum
  linarith

private theorem fluidEmpiricalPreActionStates_mem_dist_le {Knat : Nat}
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

private theorem eventGridCount_real_bounds
    {T : Real} (hT : 0 < T) (K : PNat) (l : Nat) :
    T * l - 1 <
        (N.eventGridCount T K l : Real) /\
      (N.eventGridCount T K l : Real) <= T * l := by
  have harg :
      max (eventGridTime T K l) 0 * (K : Nat) = T * l := by
    rw [max_eq_left]
    · unfold eventGridTime
      have hKne : ((K : Nat) : Real) ≠ 0 := by positivity
      field_simp
    · exact div_nonneg
        (mul_nonneg hT.le (Nat.cast_nonneg l)) (by positivity)
  constructor
  · have hfloor :=
      Nat.lt_floor_add_one (T * (l : Real))
    unfold eventGridCount eventEpochCount
    rw [harg]
    linarith
  · unfold eventGridCount eventEpochCount
    rw [harg]
    exact Nat.floor_le (mul_nonneg hT.le (Nat.cast_nonneg l))

private theorem eventGridBatch_scaled_length_le
    {T : Real} (hT : 0 < T) (K : PNat)
    (omega : N.TokenPath) (l : Nat) :
    ((N.eventGridBatch T K omega l).length : Real) / (K : Nat) <=
      (T + 1) / (K : Nat) := by
  rw [eventGridBatch_length N hT K omega l]
  have hmono :=
    eventGridCount_mono N hT K (Nat.le_succ l)
  rw [Nat.cast_sub hmono]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hl := eventGridCount_real_bounds N hT K l
  have hr := eventGridCount_real_bounds N hT K (l + 1)
  push_cast at hr
  linarith

private theorem edgeProgress_le_one (r : Real) (l : Nat) :
    edgeProgress r l <= 1 := by
  unfold edgeProgress
  exact max_le (by norm_num) (min_le_left _ _)

private theorem edgeProgress_pos_imp (r : Real) (l : Nat)
    (h : 0 < edgeProgress r l) :
    (l : Real) < r := by
  unfold edgeProgress at h
  have hm : 0 < min 1 (r - (l : Real)) := by
    by_contra hn
    have hmle : min 1 (r - (l : Real)) <= 0 := le_of_not_gt hn
    rw [max_eq_left hmle] at h
    exact (lt_irrefl 0 h)
  exact sub_pos.mp ((lt_min_iff.mp hm).2)

private theorem edgeProgress_lt_one_imp (r : Real) (l : Nat)
    (h : edgeProgress r l < 1) :
    r < (l : Real) + 1 := by
  by_contra hn
  have hr : 1 <= r - (l : Real) := by linarith
  unfold edgeProgress at h
  rw [min_eq_left hr, max_eq_right zero_le_one] at h
  exact (lt_irrefl 1 h)

private theorem used_edge_gridTime_close
    {T : Real} (hT : 0 < T) (K : PNat)
    {t h : Real} (hh : 0 < h) (l : Nat)
    (hused :
      0 <
        edgeProgress (((K : Nat) : Real) * (t + h) / T) l -
          edgeProgress (((K : Nat) : Real) * t / T) l) :
    abs (eventGridTime T K l - t) <
      h + T / (K : Nat) := by
  let r0 : Real := ((K : Nat) : Real) * t / T
  let r1 : Real := ((K : Nat) : Real) * (t + h) / T
  have hp : edgeProgress r0 l < edgeProgress r1 l := sub_pos.mp hused
  have hr1pos : 0 < edgeProgress r1 l :=
    lt_of_le_of_lt (edgeProgress_nonneg r0 l) hp
  have hr0lt : edgeProgress r0 l < 1 :=
    hp.trans_le (edgeProgress_le_one r1 l)
  have hlr1 := edgeProgress_pos_imp r1 l hr1pos
  have hr0l := edgeProgress_lt_one_imp r0 l hr0lt
  have hK : (0 : Real) < (K : Nat) := by positivity
  have hcancel :
      T / (K : Nat) * (K : Nat) = T :=
    div_mul_cancel₀ T (ne_of_gt hK)
  have hlower : t - T / (K : Nat) < eventGridTime T K l := by
    dsimp [r0] at hr0l
    unfold eventGridTime
    apply (lt_div_iff₀ hK).2
    apply (div_lt_iff₀ hT).1 at hr0l
    nlinarith [hcancel]
  have hupper : eventGridTime T K l < t + h := by
    dsimp [r1] at hlr1
    unfold eventGridTime
    apply (div_lt_iff₀ hK).2
    apply (lt_div_iff₀ hT).1 at hlr1
    nlinarith
  rw [abs_lt]
  constructor <;> nlinarith [div_pos hT hK]

private theorem eventPreActionStates_near
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X)
    {t epsilon : Real} (ht : t ∈ Ioo (0 : Real) T)
    (hepsilon : 0 < epsilon) :
    exists delta, 0 < delta /\
      exists r0, forall r, r0 <= r ->
        forall h, 0 < h -> h < delta ->
          forall j k (l : Fin (K r : Nat))
            (y : JobState Buffer (K r : Nat)),
            y ∈ N.eventGridPreActionStates initial T U (K r) omega j k l ->
            0 <
              edgeProgress
                  (((K r : Nat) : Real) * (t + h) / T) l.val -
                edgeProgress
                  (((K r : Nat) : Real) * t / T) l.val ->
            IsNearNormalizedState y (X t) epsilon := by
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t i => N.scaledQueueStateFrom initial U (K r) omega t i)
      X at hstate
  let Xvec : Real -> (Buffer -> Real) := fun s i => X s i
  have hXcont : ContinuousOn Xvec (Icc (0 : Real) T) := by
    rw [continuousOn_pi]
    exact stateLimit_continuousOn N initial hT U K omega A X hA hconverges
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
    tendsto_natCast_atTop_atTop.comp (pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun r => T / (((K r : Nat) : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  have hbatchBound :
      Tendsto (fun r => 2 * ((T + 1) / (((K r : Nat) : Real))))
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_const_nhds.div_atTop hKreal) :
          Tendsto (fun r =>
            (2 : Real) * ((T + 1) / (((K r : Nat) : Real))))
            atTop (nhds (2 * 0)))
  obtain ⟨rMesh, hrMesh⟩ :=
    Metric.tendsto_atTop.mp hmesh (deltaX / 2) (by positivity)
  obtain ⟨rBatch, hrBatch⟩ :=
    Metric.tendsto_atTop.mp hbatchBound (epsilon / 3) (by positivity)
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
      2 * ((T + 1) / (((K r : Nat) : Real))) < epsilon / 3 := by
    have hb := hrBatch r hrB
    rw [Real.dist_eq, sub_zero] at hb
    have hnonneg :
        0 <= 2 * ((T + 1) / (((K r : Nat) : Real))) := by
      positivity
    simpa [abs_of_nonneg hnonneg] using hb
  have hlK : l.val <= (K r : Nat) := Nat.le_of_lt l.isLt
  have hgridMem :
      eventGridTime T (K r) l.val ∈ Icc (0 : Real) T :=
    eventGridTime_mem_Icc hT (K r) hlK
  have hgridClose :
      dist (eventGridTime T (K r) l.val) t < deltaX := by
    rw [Real.dist_eq]
    have hc :=
      used_edge_gridTime_close hT (K r) hh l.val hused
    exact hc.trans_le (by
      have hdX : delta <= deltaX / 2 := min_le_left _ _
      linarith)
  have hXclose :
      dist (Xvec (eventGridTime T (K r) l.val)) (Xvec t) <
        epsilon / 3 :=
    hdeltaXWorks _ hgridMem _ ⟨ht.1.le, ht.2.le⟩ hgridClose
  have hfiniteState (i : Buffer) :
      abs
        (((N.eventGridState initial T U (K r) omega l.val i : Nat) : Real) /
            (K r : Nat) -
          X (eventGridTime T (K r) l.val) i) < epsilon / 3 := by
    exact hrState r hrS _ hgridMem i
  intro i
  have hyraw :=
    fluidEmpiricalPreActionStates_mem_dist_le N (U (K r))
      (N.eventGridState initial T U (K r) omega l.val)
      (N.eventGridBatch T (K r) omega l.val) j k hy i
  have hygrid :
      abs
        (((y i : Nat) : Real) / (K r : Nat) -
          ((N.eventGridState initial T U (K r) omega l.val i : Nat) : Real) /
            (K r : Nat)) < epsilon / 3 := by
    have hKpos : (0 : Real) < (K r : Nat) := by positivity
    rw [<- sub_div, abs_div, abs_of_pos hKpos]
    calc
      _ <= (2 * (N.eventGridBatch T (K r) omega l.val).length : Real) /
          (K r : Nat) := div_le_div_of_nonneg_right hyraw hKpos.le
      _ = 2 *
          (((N.eventGridBatch T (K r) omega l.val).length : Real) /
            (K r : Nat)) := by ring
      _ <= 2 * ((T + 1) / (K r : Nat)) := by
        exact mul_le_mul_of_nonneg_left
          (eventGridBatch_scaled_length_le N hT (K r) omega l.val)
          (by norm_num)
      _ < epsilon / 3 := hbatchSmall
  have hXcoord :
      abs
        (X (eventGridTime T (K r) l.val) i - X t i) <
          epsilon / 3 := by
    have hc :
        dist
            (Xvec (eventGridTime T (K r) l.val) i)
            (Xvec t i) <=
          dist
            (Xvec (eventGridTime T (K r) l.val))
            (Xvec t) :=
      (dist_pi_le_iff dist_nonneg).mp
        (le_rfl :
          dist (Xvec (eventGridTime T (K r) l.val)) (Xvec t) <= _) i
    simpa [Xvec, Real.dist_eq] using hc.trans_lt hXclose
  calc
    abs (((y i : Nat) : Real) / (K r : Nat) - X t i) <=
        abs
          (((y i : Nat) : Real) / (K r : Nat) -
            ((N.eventGridState initial T U (K r) omega l.val i : Nat) : Real) /
              (K r : Nat)) +
        abs
          (((N.eventGridState initial T U (K r) omega l.val i : Nat) : Real) /
              (K r : Nat) -
            X (eventGridTime T (K r) l.val) i) +
        abs (X (eventGridTime T (K r) l.val) i - X t i) := by
      calc
        _ <= abs
            (((y i : Nat) : Real) / (K r : Nat) -
              ((N.eventGridState initial T U (K r) omega l.val i : Nat) : Real) /
                (K r : Nat)) +
            abs
              (((N.eventGridState initial T U (K r) omega l.val i : Nat) : Real) /
                (K r : Nat) - X t i) := abs_sub_le _ _ _
        _ <= _ := by
          have htri := abs_sub_le
            (((N.eventGridState initial T U (K r) omega l.val i : Nat) : Real) /
              (K r : Nat))
            (X (eventGridTime T (K r) l.val) i) (X t i)
          linarith
    _ < epsilon / 3 + epsilon / 3 + epsilon / 3 :=
      add_lt_add (add_lt_add hygrid (hfiniteState i)) hXcoord
    _ = epsilon := by ring

private noncomputable def eventLimitAction
    (A : MatrixPath Server Buffer) (E : FluidAllocationPath Buffer Server)
    (j : Server) (k : Buffer) (t : Real) : ActionVector Buffer
  | none => A t j k - Finset.univ.sum (fun i : Buffer => E t i j k)
  | some i => E t i j k

private theorem eventPolygonalAction_tendsto
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon)
    {t : Real} (ht : t ∈ Icc (0 : Real) T)
    (j : Server) (k : Buffer) (a : Option Buffer) :
    Tendsto
      (fun r => N.eventPolygonalAction initial T U (K (q r)) omega j k t a)
      atTop (nhds (eventLimitAction A E j k t a)) := by
  have hinputConv :=
    eventPolygonalInput_converges N initial hT U K hK omega A X hA hconverges
  have hApoint :
      Tendsto
        (fun r => N.eventPolygonalInput T (K (q r)) omega t j k)
        atTop (nhds (A t j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hinputConv epsilon hepsilon
    refine ⟨r0, fun r hr => ?_⟩
    exact hr0 (q r) (hr.trans (hq.id_le r)) (j, k) t ht
  have hEpoint (i : Buffer) :
      Tendsto
        (fun r =>
          N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
        atTop (nhds (E t i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i j k t ht⟩
  cases a with
  | none =>
      rw [show
        (fun r =>
          N.eventPolygonalAction initial T U (K (q r)) omega j k t none) =
        fun r =>
          N.eventPolygonalInput T (K (q r)) omega t j k -
            Finset.univ.sum (fun i : Buffer =>
              N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k) by
        funext r
        exact eventPolygonalAction_none N initial hT U (K (q r)) omega j k ht]
      exact hApoint.sub (tendsto_finsetSum _ (fun i _ => hEpoint i))
  | some i =>
      rw [show
        (fun r =>
          N.eventPolygonalAction initial T U (K (q r)) omega j k t (some i)) =
        fun r =>
          N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k by
        funext r
        exact eventPolygonalAction_some N initial hT U (K (q r)) omega i j k ht]
      exact hEpoint i

private theorem eventLimit_finiteDifference_mem_epsilon
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon)
    {t epsilon h : Real} (ht : t ∈ Ioo (0 : Real) T)
    (hepsilon : 0 < epsilon) (hh : 0 < h)
    (hth : t + h ∈ Icc (0 : Real) T)
    (hden : 0 < A (t + h) j k - A t j k)
    (hnearWindow :
      exists r0, forall r, r0 <= r ->
        forall l
          (y : JobState Buffer (K (q r) : Nat)),
          y ∈ N.eventGridPreActionStates initial
            T U (K (q r)) omega j k l ->
          0 <
            edgeProgress
                (((K (q r) : Nat) : Real) * (t + h) / T) l.val -
              edgeProgress
                (((K (q r) : Nat) : Real) * t / T) l.val ->
          IsNearNormalizedState y (X t) epsilon) :
    N.finiteDifferenceRatio
        (fun s => A s j k)
        (fun s => eventLimitAction A E j k s)
        t h ∈
      N.fluidPolicyEpsilonCorrespondence U j k (X t) epsilon := by
  have hinputConv :=
    eventPolygonalInput_converges N initial hT U K hK omega A X hA hconverges
  have hApoint (s : Real) (hs : s ∈ Icc (0 : Real) T) :
      Tendsto
        (fun r => N.eventPolygonalInput T (K (q r)) omega s j k)
        atTop (nhds (A s j k)) := by
    rw [Metric.tendsto_atTop]
    intro eta heta
    obtain ⟨r0, hr0⟩ := hinputConv eta heta
    exact ⟨r0, fun r hr =>
      hr0 (q r) (hr.trans (hq.id_le r)) (j, k) s hs⟩
  have hdenConv :
      Tendsto
        (fun r =>
          N.eventPolygonalInput T (K (q r)) omega (t + h) j k -
            N.eventPolygonalInput T (K (q r)) omega t j k)
        atTop (nhds (A (t + h) j k - A t j k)) :=
    (hApoint (t + h) hth).sub
      (hApoint t ⟨ht.1.le, ht.2.le⟩)
  have hdenEventually :
      Filter.Eventually
        (fun r =>
          0 <
            N.eventPolygonalInput T (K (q r)) omega (t + h) j k -
              N.eventPolygonalInput T (K (q r)) omega t j k)
        atTop := by
    exact (tendsto_order.mp hdenConv).1 0 hden
  have hKreal :
      Tendsto (fun r => (((K (q r) : Nat) : Real))) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      ((pnat_val_strictMono hK).comp hq).tendsto_atTop
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
            y ∈ N.eventGridPreActionStates initial
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
          N.finiteDifferenceRatio
              (fun s =>
                N.eventPolygonalInput T (K (q r)) omega s j k)
              (fun s =>
                N.eventPolygonalAction initial T U (K (q r)) omega j k s)
              t h ∈
            N.fluidPolicyEpsilonCorrespondence U j k (X t) epsilon)
        atTop := by
    filter_upwards [hdenEventually, hKEventually, hnearEventually] with
      r hpos hsize hnear
    unfold finiteDifferenceRatio
    change
      (fun a =>
        (N.eventPolygonalAction initial T U (K (q r)) omega j k (t + h) a -
            N.eventPolygonalAction initial T U (K (q r)) omega j k t a) /
          (N.eventPolygonalInput T (K (q r)) omega (t + h) j k -
            N.eventPolygonalInput T (K (q r)) omega t j k)) ∈
        N.fluidPolicyEpsilonCorrespondence U j k (X t) epsilon
    rw [eventPolygonalInput_eq_batched
      N initial hT U (K (q r)) omega j k ⟨ht.1.le, ht.2.le⟩]
    rw [eventPolygonalInput_eq_batched
      N initial hT U (K (q r)) omega j k hth]
    have hpos' :
        0 <
          scaledBatchedInputInterpolate (K (q r))
              (N.eventGridPreActionStates initial T U (K (q r)) omega j k)
              T (t + h) -
            scaledBatchedInputInterpolate (K (q r))
              (N.eventGridPreActionStates initial T U (K (q r)) omega j k)
              T t := by
      simpa only [
        eventPolygonalInput_eq_batched
          N initial hT U (K (q r)) omega j k hth,
        eventPolygonalInput_eq_batched
          N initial hT U (K (q r)) omega j k
            ⟨ht.1.le, ht.2.le⟩] using hpos
    exact N.finiteDifferenceRatio_scaledBatched_mem_epsilon
      (K (q r)) U (K (q r))
      (N.eventGridPreActionStates initial T U (K (q r)) omega j k)
      j k (X t) epsilon T t h hT hh hpos' hsize hnear
  apply closed_mem_of_finiteDifferenceRatio_limit
    (N.fluidPolicyEpsilonCorrespondence_isClosed U j k (X t) epsilon)
    (fun r s => N.eventPolygonalInput T (K (q r)) omega s j k)
    (fun s => A s j k)
    (fun r s => N.eventPolygonalAction initial T U (K (q r)) omega j k s)
    (fun s => eventLimitAction A E j k s)
    t (t + h)
  · exact hApoint t ⟨ht.1.le, ht.2.le⟩
  · exact hApoint (t + h) hth
  · intro a
    exact eventPolygonalAction_tendsto N initial hT U K hK omega A X hA
      hconverges q hq E hpoly ⟨ht.1.le, ht.2.le⟩ j k a
  · intro a
    exact eventPolygonalAction_tendsto N initial hT U K hK omega A X hA
      hconverges q hq E hpoly hth j k a
  · exact ne_of_gt hden
  · filter_upwards [hmem] with n hn
    change
      (fun a =>
        (N.eventPolygonalAction initial T U (K (q n)) omega j k (t + h) a -
            N.eventPolygonalAction initial T U (K (q n)) omega j k t a) /
          (N.eventPolygonalInput T (K (q n)) omega (t + h) j k -
            N.eventPolygonalInput T (K (q n)) omega t j k)) ∈
        N.fluidPolicyEpsilonCorrespondence U j k (X t) epsilon at hn
    exact hn

private theorem eventLimit_allocation_initial
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : N.TokenPath)
    (q : Nat -> Nat) (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall i j k, E 0 i j k = 0 := by
  intro i j k
  have hlim :
      Tendsto
        (fun r =>
          N.eventPolygonalAllocation initial T U (K (q r)) omega 0 i j k)
        atTop (nhds (E 0 i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i j k 0 ⟨le_rfl, hT.le⟩⟩
  have heq :
      (fun r =>
        N.eventPolygonalAllocation initial T U (K (q r)) omega 0 i j k) =
        fun _ => 0 := by
    funext r
    exact eventPolygonalAllocation_initial N initial hT U (K (q r)) omega i j k
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem eventLimit_allocation_incompatible
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : N.TokenPath)
    (q : Nat -> Nat) (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall t, t ∈ Icc (0 : Real) T ->
      forall i j k, Not (N.compatible i j) -> E t i j k = 0 := by
  intro t ht i j k hij
  have hlim :
      Tendsto
        (fun r =>
          N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
        atTop (nhds (E t i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr i j k t ht⟩
  have heq :
      (fun r =>
        N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k) =
        fun _ => 0 := by
    funext r
    exact eventPolygonalAllocation_incompatible
      N initial T U (K (q r)) omega t i j k hij
  rw [heq] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

private theorem eventLimit_state_in_simplex
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall t, t ∈ Icc (0 : Real) T -> IsFluidState (X t) := by
  have hstate :=
    eventPolygonalState_converges N initial hT U K hK omega A X hA hconverges
  intro t ht
  have hpoint (i : Buffer) :
      Tendsto (fun r => N.eventPolygonalState initial T U (K r) omega t i)
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
          (eventPolygonalState_in_simplex N initial hT U (K r) omega ht).1 i
        linarith)
    linarith
  · apply tendsto_nhds_unique
      (tendsto_finsetSum _ (fun i _ => hpoint i))
    have heq :
        (fun r =>
          Finset.univ.sum (N.eventPolygonalState initial T U (K r) omega t)) =
          fun _ => 1 := by
      funext r
      exact (eventPolygonalState_in_simplex N initial hT U (K r) omega ht).2
    rw [heq]
    exact tendsto_const_nhds

private theorem eventLimit_balance
    {T : Real} (hT : 0 < T) (x0 : Simplex Buffer)
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hX0 : forall i, X 0 i = x0 i)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall t, t ∈ Icc (0 : Real) T ->
      forall i,
        X t i = x0 i +
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun l : Buffer => E t l j i) -
          (Finset.univ.sum fun j : Server =>
            Finset.univ.sum fun k : Buffer => E t i j k) := by
  have hstate :=
    eventPolygonalState_converges N initial hT U K hK omega A X hA hconverges
  intro t ht i
  have hXpoint :
      Tendsto
        (fun r => N.eventPolygonalState initial T U (K (q r)) omega t i)
        atTop (nhds (X t i)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hstate epsilon hepsilon
    exact ⟨r0, fun r hr =>
      hr0 (q r) (hr.trans (hq.id_le r)) i t ht⟩
  have hEpoint (l : Buffer) (j : Server) (k : Buffer) :
      Tendsto
        (fun r =>
          N.eventPolygonalAllocation initial T U (K (q r)) omega t l j k)
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
        (fun r t i => N.scaledQueueStateFrom initial U (K r) omega t i)
        X at hzeroState
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hzeroState epsilon hepsilon
    refine ⟨r0, fun r hr => ?_⟩
    have hz := hr0 (q r) (hr.trans (hq.id_le r))
      0 ⟨le_rfl, hT.le⟩ i
    simpa [Real.dist_eq, scaledQueueStateFrom, eventEpochCount, eventTokenPrefix,
      runTokens, hX0 i] using hz
  have hrhs :
      Tendsto
        (fun r =>
          ((initial (K (q r)) i : Nat) : Real) /
              (K (q r) : Nat) +
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun l : Buffer =>
                N.eventPolygonalAllocation initial
                  T U (K (q r)) omega t l j i) -
            (Finset.univ.sum fun j : Server =>
              Finset.univ.sum fun k : Buffer =>
                N.eventPolygonalAllocation initial
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
  exact (eventPolygonal_balance N initial hT U (K (q r)) omega ht i).symm

private theorem eventLimit_allocation_ac
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon) :
    forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T := by
  intro i j k
  apply FluidCompactness.absolutelyContinuousOnInterval_of_uniform_limits_finset
    (f := fun r t =>
      N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
    (limit := fun t => E t i j k)
    (g := fun r (jk : Server × Buffer) t =>
      N.eventPolygonalInput T (K (q r)) omega t jk.1 jk.2)
    (control := fun (jk : Server × Buffer) t => A t jk.1 jk.2)
    (s := Finset.univ)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hpoly epsilon hepsilon
    refine ⟨r0, fun r hr t ht => ?_⟩
    exact hr0 r hr i j k t (by simpa [uIcc_of_le hT.le] using ht)
  · intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ :=
      eventPolygonalInput_converges N initial hT U K hK omega A X hA
        hconverges epsilon hepsilon
    refine ⟨r0, fun r hr jk hjk t ht => ?_⟩
    exact hr0 (q r) (hr.trans (hq.id_le r)) jk t
      (by simpa [uIcc_of_le hT.le] using ht)
  · intro jk hjk
    exact hA jk.1 jk.2
  · intro r s hs t ht
    exact eventPolygonalAllocation_increment_domination
      N initial hT U (K (q r)) omega i j k
      (by simpa [uIcc_of_le hT.le] using hs)
      (by simpa [uIcc_of_le hT.le] using ht)

private theorem eventLimit_allocation_increment
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hinput :
      UniformlyOnIcc T
        (fun r t (jk : Server × Buffer) =>
          N.scaledTokenInput (K r) omega t jk.1 jk.2)
        (fun t jk => A t jk.1 jk.2))
    (hraw :
      (N.eventEpochExecutionFrom initial).AllocationConvergesOn T U K q omega E) :
    forall i j k s, s ∈ Icc (0 : Real) T ->
      forall t, t ∈ Icc (0 : Real) T -> s <= t ->
        0 <= E t i j k - E s i j k /\
        E t i j k - E s i j k <= A t j k - A s j k := by
  intro i j k s hs t ht hst
  have hEpoint (u : Real) (hu : u ∈ Icc (0 : Real) T) :
      Tendsto (fun r => N.scaledAllocationFrom initial U (K (q r)) omega u i j k)
        atTop (nhds (E u i j k)) := by
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hraw epsilon hepsilon
    exact ⟨r0, fun r hr => hr0 r hr u hu (i, j, k)⟩
  have hApoint (u : Real) (hu : u ∈ Icc (0 : Real) T) :
      Tendsto (fun r => N.scaledTokenInput (K (q r)) omega u j k)
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
        (scaledAllocation_ordered_increment
          N initial U (K (q r)) omega hst i j k).1)
  · exact le_of_tendsto_of_tendsto
      ((hEpoint t ht).sub (hEpoint s hs))
      ((hApoint t ht).sub (hApoint s hs))
      (Eventually.of_forall fun r =>
        (scaledAllocation_ordered_increment
          N initial U (K (q r)) omega hst i j k).2)

private theorem eventLimit_state_ac
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X) :
    forall i, AbsolutelyContinuousOnInterval (fun t => X t i) 0 T := by
  intro i
  have hstate := hconverges.2
  change UniformlyOnIcc T
      (fun r t i => N.scaledQueueStateFrom initial U (K r) omega t i)
      X at hstate
  apply FluidCompactness.absolutelyContinuousOnInterval_of_uniform_limits_finset
    (f := fun r t => N.scaledQueueStateFrom initial U (K r) omega t i)
    (limit := fun t => X t i)
    (g := fun r (jk : Server × Buffer) t =>
      2 * N.scaledTokenInput (K r) omega t jk.1 jk.2)
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
      abs (N.scaledTokenInput (K r) omega t b.1 b.2 -
        A t b.1 b.2) < epsilon / 2 at h
    rw [Real.dist_eq, <- mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : Real) < 2)]
    nlinarith
  · intro b hb
    have hac := (hA b.1 b.2).const_mul 2
    unfold AbsolutelyContinuousOnInterval at hac ⊢
    simpa only using hac
  · intro r s hs t ht
    have hdom := scaledQueueState_dist_le N initial U (K r) omega s t i
    calc
      _ <= 2 * Finset.univ.sum (fun jk : Server × Buffer =>
          dist (N.scaledTokenInput (K r) omega s jk.1 jk.2)
            (N.scaledTokenInput (K r) omega t jk.1 jk.2)) := hdom
      _ = Finset.univ.sum (fun jk : Server × Buffer =>
          dist (2 * N.scaledTokenInput (K r) omega s jk.1 jk.2)
            (2 * N.scaledTokenInput (K r) omega t jk.1 jk.2)) := by
        simp_rw [Real.dist_eq, <- mul_sub, abs_mul,
          abs_of_pos (by norm_num : (0 : Real) < 2)]
        rw [Finset.mul_sum]

private theorem eventLimit_balance_restricted
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

private theorem absolutelyContinuousOnInterval_finset_sum
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

private theorem eventLimitAction_ac
    {T : Real} (A : MatrixPath Server Buffer)
    (E : FluidAllocationPath Buffer Server)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hE : forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T) :
    forall j k a,
      AbsolutelyContinuousOnInterval
        (fun t => eventLimitAction A E j k t a) 0 T := by
  intro j k a
  cases a with
  | some i =>
      exact hE i j k
  | none =>
      have hsum :
          AbsolutelyContinuousOnInterval
            (fun t => Finset.univ.sum fun i : Buffer => E t i j k)
            0 T := by
        apply absolutelyContinuousOnInterval_finset_sum
        intro i hi
        exact hE i j k
      have hsub := (hA j k).sub hsum
      unfold AbsolutelyContinuousOnInterval at hsub ⊢
      simpa only [eventLimitAction, Pi.sub_apply] using hsub

private theorem hasDerivAt_eq_zero_of_increment_domination_Icc
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

private theorem eventLimit_zero_derivative_ae
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
  apply hasDerivAt_eq_zero_of_increment_domination_Icc
    (fun s => A s j k) (fun s => E s i j k) ht
  · simpa [hzero] using (hAt j k (Set.Ioo_subset_Icc_self ht)).hasDerivAt
  · exact (hEt i j k (Set.Ioo_subset_Icc_self ht)).hasDerivAt
  · intro s hs u hu hsu
    exact hdom i j k s hs u hu hsu

private theorem eventLimit_positive_policy_ae
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K) (omega : N.TokenPath)
    (A : MatrixPath Server Buffer) (X : FluidStatePath Buffer)
    (hA : IsAbsolutelyContinuousMatrixPath T A)
    (hconverges :
      (N.eventEpochExecutionFrom initial).PairConvergesOn T U K omega A X)
    (q : Nat -> Nat) (hq : StrictMono q)
    (E : FluidAllocationPath Buffer Server)
    (hpoly :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall i j k t, t ∈ Icc (0 : Real) T ->
            dist
              (N.eventPolygonalAllocation initial T U (K (q r)) omega t i j k)
              (E t i j k) < epsilon)
    (hEac : forall i j k,
      AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T) :
    forall j k,
      Filter.Eventually
        (fun t => 0 < deriv (fun s => A s j k) t ->
          Membership.mem
            (N.fluidPolicyCorrespondence U j k (X t))
            (fun a =>
              deriv (fun s => eventLimitAction A E j k s a) t /
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
    eventLimitAction_ac A E hA hEac
  have hActionDiff (a : Option Buffer) :
      Filter.Eventually
        (fun t =>
          DifferentiableAt Real
            (fun s => eventLimitAction A E j k s a) t)
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
                N.finiteDifferenceRatio
                    (fun s => A s j k)
                    (fun s => eventLimitAction A E j k s) t h ∈
                  N.fluidPolicyEpsilonCorrespondence
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
      eventPreActionStates_near N initial hT U K hK omega A X hA hconverges
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
    apply eventLimit_finiteDifference_mem_epsilon
      N initial hT U K hK omega A X hA hconverges q hq E hpoly ht
        epsilon.2 hhpos hth hden
    refine ⟨rNear, fun r hr l y hy hused => ?_⟩
    exact hrNear (q r) (hr.trans (hq.id_le r)) h hhpos hhNear
      j k l y hy hused
  exact N.ae_derivativeRatio_mem_fluidPolicyCorrespondence
    (TimeMeasure := mu) U j k X
    (fun s => A s j k)
    (fun s => eventLimitAction A E j k s)
    hAdiff hActionDiff hfinite

theorem eventEpochExecutionFrom_stochasticFluidExtension :
    N.StochasticFluidExtensionReadback
      (N.eventEpochExecutionFrom initial) := by
  intro T hT x0 U K hK omega A X hX0 hA hconverges
  obtain ⟨q, hq, E, hEcont, hpoly⟩ :=
    exists_eventPolygonalAllocation_limit
      N initial hT U K hK omega A X hA hconverges
  have hinput : IsFluidInput T A :=
    eventInput_isFluidInput N initial hT U K omega A X hA hconverges
  have hraw :
      (N.eventEpochExecutionFrom initial).AllocationConvergesOn T U K q omega E :=
    eventAllocation_raw_converges
      N initial hT U K hK omega A X hA hconverges q hq E hpoly
  have hE0 : forall i j k, E 0 i j k = 0 :=
    eventLimit_allocation_initial N initial hT U K omega q E hpoly
  have hEincompat :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i j k, Not (N.compatible i j) -> E t i j k = 0 :=
    eventLimit_allocation_incompatible N initial hT U K omega q E hpoly
  have hstate :
      forall t, t ∈ Icc (0 : Real) T -> IsFluidState (X t) :=
    eventLimit_state_in_simplex
      N initial hT U K hK omega A X hA hconverges
  have hbalance :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i,
          X t i = x0 i
            + (Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun l : Buffer => E t l j i)
            - (Finset.univ.sum fun j : Server =>
                Finset.univ.sum fun k : Buffer => E t i j k) :=
    eventLimit_balance
      N initial hT x0 U K hK omega A X hX0 hA hconverges q hq E hpoly
  have hEac :
      forall i j k,
        AbsolutelyContinuousOnInterval (fun t => E t i j k) 0 T :=
    eventLimit_allocation_ac
      N initial hT U K hK omega A X hA hconverges q hq E hpoly
  have hXac :
      forall i, AbsolutelyContinuousOnInterval (fun t => X t i) 0 T :=
    eventLimit_state_ac N initial hT U K omega A X hA hconverges
  have hinc :
      forall i j k s, s ∈ Icc (0 : Real) T ->
        forall t, t ∈ Icc (0 : Real) T -> s <= t ->
          0 <= E t i j k - E s i j k /\
          E t i j k - E s i j k <= A t j k - A s j k :=
    eventLimit_allocation_increment
      N initial hT U K omega A q hq E hconverges.1 hraw
  have hbalanceRestricted :
      forall t, t ∈ Icc (0 : Real) T ->
        forall i,
          X t i = x0 i
            + (Finset.univ.sum fun j : Server =>
                Finset.sum (N.buffersOf j) fun l => E t l j i)
            - (Finset.sum (N.serversOf i) fun j =>
                Finset.univ.sum fun k : Buffer => E t i j k) :=
    eventLimit_balance_restricted N x0 X E hbalance hEincompat
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
      N.verifiedPatchedFluidPolicy U j k Xclip
        (fun s => A s j k)
        (fun s => eventLimitAction A E j k s) t
  have hpositive (j : Server) (k : Buffer) :
      Filter.Eventually
        (fun t => 0 < deriv (fun s => A s j k) t ->
          Membership.mem
            (N.fluidPolicyCorrespondence U j k (Xclip t))
            (fun a =>
              deriv (fun s => eventLimitAction A E j k s a) t /
                deriv (fun s => A s j k) t))
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    have hp :=
      eventLimit_positive_policy_ae
        N initial hT U K hK omega A X hA hconverges q hq E hpoly hEac j k
    filter_upwards [ae_restrict_mem measurableSet_Icc, hp] with t ht hpt
    simpa only [hXclip_eq t ht] using hpt
  have hzeroE :=
    eventLimit_zero_derivative_ae hT A E hA hEac hinc
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
            deriv (fun s => eventLimitAction A E j k s a) t = 0)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    filter_upwards [hzeroE,
      ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => hAdiff j k)),
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
        ae_all_iff.mpr (fun k => hEdiff i j k)))] with
        t hzeroEt hAdifft hEdifft
    intro j k hAzero a
    cases a with
    | some i =>
        simpa only [eventLimitAction] using hzeroEt j k hAzero i
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
          deriv (fun s => eventLimitAction A E j k s a) t =
            deriv (fun s => A s j k) t * p t j k a)
        (ae (volume.restrict (Icc (0 : Real) T))) := by
    exact N.verifiedPatchedFluidPolicy_allocation_rule_ae
      (TimeMeasure := volume.restrict (Icc (0 : Real) T))
      U j k Xclip
      (fun s => A s j k)
      (fun s => eventLimitAction A E j k s)
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
    exact N.verifiedPatchedFluidPolicy_coordinate_measurable
      U j k Xclip
      (fun s => A s j k)
      (fun s => eventLimitAction A E j k s)
      hXclipMeas a
  · intro t ht j k
    apply N.verifiedPatchedFluidPolicy_isActionDistribution
    rw [hXclip_eq t ht]
    exact hstate t ht
  · intro t ht j k i hi
    apply N.verifiedPatchedFluidPolicy_incompatible_zero
    · rw [hXclip_eq t ht]
      exact hstate t ht
    · exact hi
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro j k
    rw [show X t = Xclip t by exact (hXclip_eq t ht).symm]
    exact N.verifiedPatchedFluidPolicy_mem U j k Xclip
      (fun s => A s j k)
      (fun s => eventLimitAction A E j k s) t
      (by
        rw [hXclip_eq t ht]
        exact hstate t ht)
  · filter_upwards [
      ae_all_iff.mpr (fun j =>
        ae_all_iff.mpr (fun k => hAllocationRule j k))] with t ht
    intro i j k hij
    simpa only [eventLimitAction] using ht j k (some i)
  · exact hraw

private theorem eventUniformOnIcc_of_monotone_tendsto
    {T : Real} (hT : 0 < T)
    {f : Nat -> Real -> Real} {g : Real -> Real}
    (hf : forall r, Monotone (f r))
    (hg : ContinuousOn g (Icc (0 : Real) T))
    (hpoint : forall t, t ∈ Icc (0 : Real) T ->
      Tendsto (fun r => f r t) atTop (nhds (g t))) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall t, t ∈ Icc (0 : Real) T ->
          dist (f r t) (g t) < epsilon := by
  intro epsilon hepsilon
  have huc : UniformContinuousOn g (Icc (0 : Real) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  obtain ⟨rho, hrho, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp huc (epsilon / 3) (by positivity)
  obtain ⟨centers, hcenters, hcentersFinite, hcover⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : Real) T)).finite_cover_balls
      (show 0 < rho / 4 by positivity)
  let lo : Real -> Real := fun x => max 0 (x - rho / 2)
  let hi : Real -> Real := fun x => min T (x + rho / 2)
  have hlo_mem (x : Real) (hx : x ∈ Icc (0 : Real) T) :
      lo x ∈ Icc (0 : Real) T := by
    dsimp [lo]
    constructor
    · exact le_max_left _ _
    · exact max_le hT.le (by
        calc
          x - rho / 2 <= x :=
            sub_le_self x (div_nonneg hrho.le (by norm_num))
          _ <= T := hx.2)
  have hhi_mem (x : Real) (hx : x ∈ Icc (0 : Real) T) :
      hi x ∈ Icc (0 : Real) T := by
    dsimp [hi]
    constructor
    · exact le_min hT.le
        (add_nonneg hx.1 (div_nonneg hrho.le (by norm_num)))
    · exact min_le_left _ _
  letI : Finite {x : Real // x ∈ centers} := hcentersFinite
  letI : Fintype {x : Real // x ∈ centers} := Fintype.ofFinite _
  have hanchor (cb : {x : Real // x ∈ centers} × Bool) :
      exists r0, forall r, r0 <= r ->
        dist
          (f r (if cb.2 then hi cb.1 else lo cb.1))
          (g (if cb.2 then hi cb.1 else lo cb.1)) < epsilon / 3 := by
    have hc : (cb.1 : Real) ∈ Icc (0 : Real) T :=
      hcenters cb.1.property
    have hm :
        (if cb.2 then hi cb.1 else lo cb.1) ∈ Icc (0 : Real) T := by
      by_cases hb : cb.2
      · simp only [hb, ↓reduceIte]
        exact hhi_mem cb.1 hc
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact hlo_mem cb.1 hc
    have hp := hpoint _ hm
    rw [Metric.tendsto_atTop] at hp
    exact hp (epsilon / 3) (by positivity)
  obtain ⟨r0, hr0⟩ :=
    exists_common_nat_bound
      (I := {x : Real // x ∈ centers} × Bool)
      (P := fun cb r =>
        dist
          (f r (if cb.2 then hi cb.1 else lo cb.1))
          (g (if cb.2 then hi cb.1 else lo cb.1)) < epsilon / 3)
      hanchor
  refine ⟨r0, fun r hr t ht => ?_⟩
  have htcover := hcover ht
  rcases Set.mem_iUnion.mp htcover with ⟨c, hc⟩
  rcases Set.mem_iUnion.mp hc with ⟨hcCenters, htc⟩
  let cs : {x : Real // x ∈ centers} := ⟨c, hcCenters⟩
  have hcIcc : c ∈ Icc (0 : Real) T := hcenters hcCenters
  have htc' : abs (t - c) < rho / 4 := by
    simpa [Real.dist_eq] using htc
  have hlo_le_c : lo c <= c := by
    apply max_le hcIcc.1
    linarith
  have hc_le_hi : c <= hi c := by
    apply le_min hcIcc.2
    linarith
  have hlo_le_t : lo c <= t := by
    apply max_le ht.1
    rw [abs_lt] at htc'
    linarith
  have ht_le_hi : t <= hi c := by
    apply le_min ht.2
    rw [abs_lt] at htc'
    linarith
  have hlo_dist : dist (lo c) t < rho := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlo_le_t)]
    rw [abs_lt] at htc'
    dsimp [lo]
    have hlo_lower : c - rho / 2 <= max 0 (c - rho / 2) :=
      le_max_right _ _
    linarith
  have hhi_dist : dist (hi c) t < rho := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht_le_hi)]
    rw [abs_lt] at htc'
    dsimp [hi]
    have hhi_upper : min T (c + rho / 2) <= c + rho / 2 :=
      min_le_right _ _
    linarith
  have hglo :=
    hmod (lo c) (hlo_mem c hcIcc) t ht hlo_dist
  have hghi :=
    hmod (hi c) (hhi_mem c hcIcc) t ht hhi_dist
  have hflo := hr0 r hr (cs, false)
  have hfhi := hr0 r hr (cs, true)
  simp only [Bool.false_eq_true, ↓reduceIte] at hflo
  simp only [Bool.true_eq, ↓reduceIte] at hfhi
  rw [Real.dist_eq] at hflo hfhi hglo hghi ⊢
  rw [abs_lt] at hflo hfhi hglo hghi ⊢
  constructor
  · have hmono := hf r hlo_le_t
    linarith
  · have hmono := hf r ht_le_hi
    linarith

private theorem scaledTokenInput_uniform_converges_nominal
    {T : Real} (hT : 0 < T)
    (K : Nat -> PNat) (hK : StrictMono K)
    (omega : N.TokenPath)
    (homega :
      forall jk : TokenType (Buffer := Buffer) (Server := Server),
        Tendsto (fun n => N.empiricalFrequency jk n omega)
          atTop (nhds (N.phi jk.1 jk.2))) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall jk : Server × Buffer, forall t, t ∈ Icc (0 : Real) T ->
          dist
            (N.scaledTokenInput (K r) omega t jk.1 jk.2)
            (N.phi jk.1 jk.2 * t) < epsilon := by
  have hcoord (jk : Server × Buffer) :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall t, t ∈ Icc (0 : Real) T ->
            dist
              (N.scaledTokenInput (K r) omega t jk.1 jk.2)
              (N.phi jk.1 jk.2 * t) < epsilon := by
    apply eventUniformOnIcc_of_monotone_tendsto hT
    · intro r s t hst
      exact scaledTokenInput_mono N (K r) omega hst jk.1 jk.2
    · fun_prop
    · intro t ht
      exact N.scaledTokenInput_tendsto
        omega homega K hK t ht.1 jk.1 jk.2
  intro epsilon hepsilon
  obtain ⟨r0, hr0⟩ :=
    exists_common_nat_bound
      (I := Server × Buffer)
      (P := fun jk r =>
        forall t, t ∈ Icc (0 : Real) T ->
          dist
            (N.scaledTokenInput (K r) omega t jk.1 jk.2)
            (N.phi jk.1 jk.2 * t) < epsilon)
      (fun jk => hcoord jk epsilon hepsilon)
  exact ⟨r0, fun r hr jk => hr0 r hr jk⟩

private theorem eventPolygonalInput_uniform_converges_nominal
    {T : Real} (hT : 0 < T)
    (K : Nat -> PNat) (hK : StrictMono K)
    (omega : N.TokenPath)
    (homega :
      forall jk : TokenType (Buffer := Buffer) (Server := Server),
        Tendsto (fun n => N.empiricalFrequency jk n omega)
          atTop (nhds (N.phi jk.1 jk.2))) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall jk : Server × Buffer, forall t, t ∈ Icc (0 : Real) T ->
          dist
            (N.eventPolygonalInput T (K r) omega t jk.1 jk.2)
            (N.phi jk.1 jk.2 * t) < epsilon := by
  have hraw :=
    scaledTokenInput_uniform_converges_nominal
      N hT K hK omega homega
  have hcoord (jk : Server × Buffer) :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall t, t ∈ Icc (0 : Real) T ->
            abs
              (N.eventPolygonalInput T (K r) omega t jk.1 jk.2 -
                N.phi jk.1 jk.2 * t) < epsilon := by
    apply polygonal_converges_of_nodes hT K hK
      (fun r l =>
        (N.eventGridInput T (K r) omega l jk.1 jk.2 : Real) /
          (K r : Nat))
      (fun t => N.phi jk.1 jk.2 * t)
    · fun_prop
    · intro epsilon hepsilon
      obtain ⟨r0, hr0⟩ := hraw epsilon hepsilon
      refine ⟨r0, fun r hr l hl => ?_⟩
      have hnode := hr0 r hr jk
        (eventGridTime T (K r) l)
        (eventGridTime_mem_Icc hT (K r) hl)
      rw [Real.dist_eq] at hnode
      rw [scaledTokenInput_eq_prefix_count N] at hnode
      simpa only [eventGridInput, eventGridPrefix, eventGridCount] using hnode
  intro epsilon hepsilon
  obtain ⟨r0, hr0⟩ :=
    exists_common_nat_bound
      (I := Server × Buffer)
      (P := fun jk r =>
        forall t, t ∈ Icc (0 : Real) T ->
          abs
            (N.eventPolygonalInput T (K r) omega t jk.1 jk.2 -
              N.phi jk.1 jk.2 * t) < epsilon)
      (fun jk => hcoord jk epsilon hepsilon)
  refine ⟨r0, fun r hr jk t ht => ?_⟩
  rw [Real.dist_eq]
  exact hr0 r hr jk t ht

private theorem eventGridState_step_le_two_input_sum
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (l : Nat) (i : Buffer) :
    abs
        ((N.eventGridState initial T U K omega (l + 1) i : Real) /
            (K : Nat) -
          (N.eventGridState initial T U K omega l i : Real) /
            (K : Nat)) <=
      2 * Finset.univ.sum (fun jk : Server × Buffer =>
        (N.eventGridInput T K omega (l + 1) jk.1 jk.2 : Real) /
            (K : Nat) -
          (N.eventGridInput T K omega l jk.1 jk.2 : Real) /
            (K : Nat)) := by
  have hrun :=
    ff_runTokens_batch_l1_le_two_mul_length N (U K)
      (N.eventGridState initial T U K omega l)
      []
      (N.eventGridBatch T K omega l)
  simp only [List.nil_append, runTokens] at hrun
  rw [<- eventGridState_succ N initial hT U K omega l] at hrun
  have hcoord :=
    (Finset.single_le_sum
      (fun q _ => abs_nonneg
        (((N.eventGridState initial T U K omega (l + 1) q : Nat) : Real) -
          ((N.eventGridState initial T U K omega l q : Nat) : Real)))
      (Finset.mem_univ i)).trans hrun
  have hKreal : (0 : Real) < (K : Nat) := by positivity
  rw [<- sub_div, abs_div, abs_of_pos hKreal]
  calc
    abs
        (((N.eventGridState initial T U K omega (l + 1) i : Nat) : Real) -
          ((N.eventGridState initial T U K omega l i : Nat) : Real)) /
          (K : Nat) <=
        (2 * (N.eventGridBatch T K omega l).length : Real) /
          (K : Nat) := by
      exact div_le_div_of_nonneg_right hcoord hKreal.le
    _ = 2 * (((N.eventGridBatch T K omega l).length : Real) /
          (K : Nat)) := by ring
    _ = _ := by
      rw [eventGridBatch_length_eq_input_sum N hT K omega l]
      rw [Nat.cast_sum, Finset.sum_div]
      apply congrArg (fun x : Real => 2 * x)
      apply Finset.sum_congr rfl
      intro jk hjk
      rw [Nat.cast_sub
        (eventGridInput_mono N hT K omega
          (Nat.le_succ l) jk.1 jk.2)]
      ring

private theorem eventPolygonalState_increment_domination
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : PNat) (omega : N.TokenPath) (i : Buffer) {s t : Real}
    (hs : s ∈ Icc (0 : Real) T) (ht : t ∈ Icc (0 : Real) T) :
    dist
        (N.eventPolygonalState initial T U K omega s i)
        (N.eventPolygonalState initial T U K omega t i) <=
      Finset.univ.sum (fun z : (Server × Buffer) × Fin 2 =>
        dist
          (N.eventPolygonalInput T K omega s z.1.1 z.1.2)
          (N.eventPolygonalInput T K omega t z.1.1 z.1.2)) := by
  let values : Nat -> Real := fun l =>
    (N.eventGridState initial T U K omega l i : Real) / (K : Nat)
  let control : (Server × Buffer) × Fin 2 -> Nat -> Real :=
    fun z l =>
      (N.eventGridInput T K omega l z.1.1 z.1.2 : Real) / (K : Nat)
  change
    dist (fi_polygonalInterpolate K values s T)
        (fi_polygonalInterpolate K values t T) <=
      Finset.univ.sum (fun z : (Server × Buffer) × Fin 2 =>
        dist (fi_polygonalInterpolate K (control z) s T)
          (fi_polygonalInterpolate K (control z) t T))
  apply fi_polygonal_increment_domination K values control hT hs ht
  · intro z l hl
    dsimp [control]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast eventGridInput_mono N hT K omega
      (Nat.le_succ l) z.1.1 z.1.2
  · intro l hl
    have hstep :=
      eventGridState_step_le_two_input_sum
        N initial hT U K omega l i
    calc
      abs (values (l + 1) - values l) <=
          2 * Finset.univ.sum (fun jk : Server × Buffer =>
            (N.eventGridInput T K omega (l + 1) jk.1 jk.2 : Real) /
                (K : Nat) -
              (N.eventGridInput T K omega l jk.1 jk.2 : Real) /
                (K : Nat)) := by
        simpa [values] using hstep
      _ = Finset.univ.sum (fun z : (Server × Buffer) × Fin 2 =>
          control z (l + 1) - control z l) := by
        rw [Fintype.sum_prod_type
          (fun z : (Server × Buffer) × Fin 2 =>
            control z (l + 1) - control z l)]
        simp only [Fin.sum_univ_two]
        change
          2 * Finset.univ.sum (fun jk : Server × Buffer =>
              (N.eventGridInput T K omega (l + 1) jk.1 jk.2 : Real) /
                  (K : Nat) -
                (N.eventGridInput T K omega l jk.1 jk.2 : Real) /
                  (K : Nat)) =
            Finset.univ.sum (fun jk : Server × Buffer =>
              ((N.eventGridInput T K omega (l + 1) jk.1 jk.2 : Real) /
                  (K : Nat) -
                (N.eventGridInput T K omega l jk.1 jk.2 : Real) /
                  (K : Nat)) +
              ((N.eventGridInput T K omega (l + 1) jk.1 jk.2 : Real) /
                  (K : Nat) -
                (N.eventGridInput T K omega l jk.1 jk.2 : Real) /
                  (K : Nat)))
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro jk hjk
        ring

private theorem exists_eventPolygonalState_limit
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K)
    (omega : N.TokenPath)
    (homega :
      forall jk : TokenType (Buffer := Buffer) (Server := Server),
        Tendsto (fun n => N.empiricalFrequency jk n omega)
          atTop (nhds (N.phi jk.1 jk.2))) :
    exists q : Nat -> Nat, StrictMono q /\
      exists X : FluidStatePath Buffer,
        (forall i, ContinuousOn (fun t => X t i) (Icc (0 : Real) T)) /\
        (forall epsilon, 0 < epsilon ->
          exists r0, forall r, r0 <= r ->
            forall i t, t ∈ Icc (0 : Real) T ->
              dist
                (N.eventPolygonalState initial T U (K (q r)) omega t i)
                (X t i) < epsilon) := by
  let f : Nat -> Buffer -> Real -> Real := fun r i t =>
    N.eventPolygonalState initial T U (K r) omega t i
  let g : Nat -> ((Server × Buffer) × Fin 2) -> Real -> Real :=
    fun r z t =>
      N.eventPolygonalInput T (K r) omega t z.1.1 z.1.2
  let control : ((Server × Buffer) × Fin 2) -> Real -> Real :=
    fun z t => N.phi z.1.1 z.1.2 * t
  have hgconv :
      forall epsilon, 0 < epsilon ->
        exists r0, forall r, r0 <= r ->
          forall z t, t ∈ Icc (0 : Real) T ->
            dist (g r z t) (control z t) < epsilon := by
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ :=
      eventPolygonalInput_uniform_converges_nominal
        N hT K hK omega homega epsilon hepsilon
    exact ⟨r0, fun r hr z => hr0 r hr z.1⟩
  obtain ⟨q, hq, limit, hlimitCont, hlimitConv⟩ :=
    FluidControlledCompactness.exists_uniformly_convergent_subsequence_finite
      (f := f) (g := g) (control := control)
      (a := (0 : Real)) (b := T) (M := 1)
      (by
        intro r i
        exact (continuous_eventPolygonalState
          N initial T U (K r) omega i).continuousOn)
      (by
        intro r i t ht
        have hs :=
          eventPolygonalState_in_simplex
            N initial hT U (K r) omega ht
        rw [abs_of_nonneg (hs.1 i)]
        calc
          f r i t <= Finset.univ.sum (f r · t) :=
            Finset.single_le_sum
              (fun q _ => hs.1 q) (Finset.mem_univ i)
          _ = 1 := hs.2)
      (by intro z; fun_prop)
      hgconv
      (by
        intro r i s hs t ht
        exact eventPolygonalState_increment_domination
          N initial hT U (K r) omega i hs ht)
  let X : FluidStatePath Buffer := fun t i => limit i t
  exact ⟨q, hq, X, hlimitCont, hlimitConv⟩

private theorem eventPolygonalState_approximates_scaled_uniformly
    {T : Real} (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K)
    (omega : N.TokenPath)
    (homega :
      forall jk : TokenType (Buffer := Buffer) (Server := Server),
        Tendsto (fun n => N.empiricalFrequency jk n omega)
          atTop (nhds (N.phi jk.1 jk.2))) :
    forall epsilon, 0 < epsilon ->
      exists r0, forall r, r0 <= r ->
        forall i t, t ∈ Icc (0 : Real) T ->
          dist
            (N.eventPolygonalState initial T U (K r) omega t i)
            (N.scaledQueueStateFrom initial U (K r) omega t i) <
            epsilon := by
  have hraw :=
    scaledTokenInput_uniform_converges_nominal
      N hT K hK omega homega
  have hKreal :
      Tendsto (fun r => (((K r : Nat) : Real))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (pnat_val_tendsto_atTop hK)
  have hmesh :
      Tendsto (fun r => T / (((K r : Nat) : Real))) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hKreal
  intro epsilon hepsilon
  let C : Real := (Fintype.card (Server × Buffer) : Real) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  let eta : Real := epsilon / (16 * C)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  obtain ⟨rInput, hrInput⟩ := hraw eta heta
  obtain ⟨rMesh, hrMesh⟩ :=
    (Metric.tendsto_atTop.mp hmesh) eta heta
  refine ⟨max rInput rMesh, fun r hr i t ht => ?_⟩
  have hrI : rInput <= r := (le_max_left _ _).trans hr
  have hrM : rMesh <= r := (le_max_right _ _).trans hr
  have hmeshSmall :
      T / (((K r : Nat) : Real)) < eta := by
    have hm := hrMesh r hrM
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (div_nonneg hT.le (by positivity))] at hm
    exact hm
  have hosc :
      forall s, s ∈ Icc (0 : Real) T ->
        forall u, u ∈ Icc (0 : Real) T ->
          abs (s - u) <= T / (K r : Nat) ->
          abs
            (N.scaledQueueStateFrom initial U (K r) omega s i -
              N.scaledQueueStateFrom initial U (K r) omega u i) <=
            epsilon / 2 := by
    intro s hs u hu hsu
    have hstate :=
      scaledQueueState_dist_le
        N initial U (K r) omega s u i
    rw [Real.dist_eq] at hstate
    exact (calc
      abs
          (N.scaledQueueStateFrom initial U (K r) omega s i -
            N.scaledQueueStateFrom initial U (K r) omega u i) <=
          2 * Finset.univ.sum (fun jk : Server × Buffer =>
            dist
              (N.scaledTokenInput (K r) omega s jk.1 jk.2)
              (N.scaledTokenInput (K r) omega u jk.1 jk.2)) := hstate
      _ < 2 * Finset.univ.sum (fun _ : Server × Buffer => 3 * eta) := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        apply Finset.sum_lt_sum_of_nonempty
          (Finset.univ_nonempty : (Finset.univ :
            Finset (Server × Buffer)).Nonempty)
        intro jk hjk
        have hsI := hrInput r hrI jk s hs
        have huI := hrInput r hrI jk u hu
        calc
          dist
              (N.scaledTokenInput (K r) omega s jk.1 jk.2)
              (N.scaledTokenInput (K r) omega u jk.1 jk.2) <=
              dist
                (N.scaledTokenInput (K r) omega s jk.1 jk.2)
                (N.phi jk.1 jk.2 * s) +
              dist (N.phi jk.1 jk.2 * s)
                (N.phi jk.1 jk.2 * u) +
              dist (N.phi jk.1 jk.2 * u)
                (N.scaledTokenInput (K r) omega u jk.1 jk.2) := by
            calc
              _ <=
                  dist
                    (N.scaledTokenInput (K r) omega s jk.1 jk.2)
                    (N.phi jk.1 jk.2 * s) +
                  dist (N.phi jk.1 jk.2 * s)
                    (N.scaledTokenInput (K r) omega u jk.1 jk.2) :=
                dist_triangle _ _ _
              _ <= _ := by
                have htri :=
                  dist_triangle
                    (N.phi jk.1 jk.2 * s)
                    (N.phi jk.1 jk.2 * u)
                    (N.scaledTokenInput (K r) omega u jk.1 jk.2)
                linarith
          _ < eta + eta + eta := by
            have hmiddle :
                dist (N.phi jk.1 jk.2 * s)
                    (N.phi jk.1 jk.2 * u) < eta := by
              rw [Real.dist_eq, <- mul_sub, abs_mul,
                abs_of_nonneg (N.phi_nonneg jk.1 jk.2)]
              calc
                N.phi jk.1 jk.2 * abs (s - u) <=
                    1 * abs (s - u) := by
                  gcongr
                  calc
                    N.phi jk.1 jk.2 <=
                        Finset.univ.sum (fun k' : Buffer =>
                          N.phi jk.1 k') :=
                      Finset.single_le_sum
                        (fun k' _ => N.phi_nonneg jk.1 k')
                        (Finset.mem_univ jk.2)
                    _ <= Finset.univ.sum (fun j' : Server =>
                          Finset.univ.sum (fun k' : Buffer =>
                            N.phi j' k')) :=
                      Finset.single_le_sum
                        (fun j' _ => Finset.sum_nonneg
                          (fun k' _ => N.phi_nonneg j' k'))
                        (Finset.mem_univ jk.1)
                    _ = 1 := N.total_rate
                _ <= T / (K r : Nat) := by simpa using hsu
                _ < eta := hmeshSmall
            rw [dist_comm] at huI
            linarith
          _ = 3 * eta := by ring
      _ <= epsilon / 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [eta, C]
        have hc : (0 : Real) <= Fintype.card (Server × Buffer) := by
          positivity
        let c : Real := Fintype.card (Server × Buffer)
        have hc1 : 0 < c + 1 := by
          dsimp [c]
          linarith
        have hratio : c / (c + 1) <= 1 :=
          (div_le_one hc1).2 (by linarith)
        have heq :
            2 * (c * (3 * (epsilon / (16 * (c + 1))))) =
              (3 / 8 : Real) * (c / (c + 1)) * epsilon := by
          field_simp
          ring
        change 2 * (c * (3 * (epsilon / (16 * (c + 1))))) <=
          epsilon / 2
        rw [heq]
        have hmul :
            (c / (c + 1)) * epsilon <= 1 * epsilon :=
          mul_le_mul_of_nonneg_right hratio hepsilon.le
        nlinarith).le
  have hnode :
      forall l, l <= (K r : Nat) ->
        abs
          (((N.eventGridState initial T U (K r) omega l i : Real) /
              (K r : Nat)) -
            N.scaledQueueStateFrom initial U (K r) omega
              (eventGridTime T (K r) l) i) <= 0 := by
    intro l hl
    have heq :
        N.scaledQueueStateFrom initial U (K r) omega
            (eventGridTime T (K r) l) i =
          (N.eventGridState initial T U (K r) omega l i : Real) /
            (K r : Nat) := by
      rfl
    rw [heq, sub_self, abs_zero]
  have herr :=
    polygonalInterpolate_error_of_nodes hT (K r)
      (fun l =>
        (N.eventGridState initial T U (K r) omega l i : Real) /
          (K r : Nat))
      (fun s =>
        N.scaledQueueStateFrom initial U (K r) omega s i)
      0 (epsilon / 2) hnode hosc t ht
  rw [Real.dist_eq]
  exact herr.trans_lt (by linarith)

/-- Sample-wise compactness of the arbitrary-initial event-epoch execution
on the simultaneous marked-token strong-law event. The conclusion includes
the limiting normalized initial state used by the fluid solution. -/
theorem eventEpochExecutionFrom_pairCompactness
    (T : Real) (hT : 0 < T) (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : StrictMono K)
    (omega : N.TokenPath)
    (homega :
      forall jk : TokenType (Buffer := Buffer) (Server := Server),
        Tendsto (fun n => N.empiricalFrequency jk n omega)
          atTop (nhds (N.phi jk.1 jk.2))) :
    exists q : Nat -> Nat, StrictMono q /\
      exists (X : FluidStatePath Buffer) (x0 : Simplex Buffer),
        (N.eventEpochExecutionFrom initial).PairConvergesOn
          T U (K ∘ q) omega (fun t j k => N.phi j k * t) X /\
        Tendsto
          (fun r i =>
            ((initial (K (q r)) i : Nat) : Real) / (K (q r) : Nat))
          atTop (nhds (fun i => x0 i)) /\
        (forall i, X 0 i = x0 i) := by
  obtain ⟨q, hq, X, hXcont, hpoly⟩ :=
    exists_eventPolygonalState_limit
      N initial hT U K hK omega homega
  let A : MatrixPath Server Buffer := fun t j k => N.phi j k * t
  have hinput :
      UniformlyOnIcc T
        (fun r t (jk : Server × Buffer) =>
          N.scaledTokenInput (K (q r)) omega t jk.1 jk.2)
        (fun t jk => A t jk.1 jk.2) := by
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ :=
      scaledTokenInput_uniform_converges_nominal
        N hT K hK omega homega epsilon hepsilon
    refine ⟨r0, fun r hr t ht jk => ?_⟩
    have h := hr0 (q r) (hr.trans (hq.id_le r)) jk t ht
    simpa [A, Real.dist_eq] using h
  have happrox :=
    eventPolygonalState_approximates_scaled_uniformly
      N initial hT U K hK omega homega
  have hstate :
      UniformlyOnIcc T
        (fun r t i =>
          N.scaledQueueStateFrom initial U (K (q r)) omega t i)
        X := by
    intro epsilon hepsilon
    obtain ⟨rPoly, hrPoly⟩ := hpoly (epsilon / 2) (by positivity)
    obtain ⟨rApprox, hrApprox⟩ := happrox (epsilon / 2) (by positivity)
    refine ⟨max rPoly rApprox, fun r hr t ht i => ?_⟩
    have hp := hrPoly r ((le_max_left _ _).trans hr) i t ht
    have ha := hrApprox (q r)
      ((le_max_right _ _).trans hr |>.trans (hq.id_le r)) i t ht
    rw [Real.dist_eq] at hp ha
    calc
      abs
          (N.scaledQueueStateFrom initial U (K (q r)) omega t i -
            X t i) <=
          abs
              (N.scaledQueueStateFrom initial U (K (q r)) omega t i -
                N.eventPolygonalState initial T U (K (q r)) omega t i) +
            abs
              (N.eventPolygonalState initial T U (K (q r)) omega t i -
                X t i) :=
        abs_sub_le _ _ _
      _ < epsilon / 2 + epsilon / 2 := by
        exact add_lt_add (by simpa [abs_sub_comm] using ha) hp
      _ = epsilon := by ring
  have hpair :
      (N.eventEpochExecutionFrom initial).PairConvergesOn
        T U (K ∘ q) omega A X := by
    exact ⟨hinput, hstate⟩
  have hA : IsAbsolutelyContinuousMatrixPath T A := by
    intro j k
    have hlip :
        LipschitzWith (Real.toNNReal (abs (N.phi j k)))
          (fun t : Real => N.phi j k * t) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change
        dist (N.phi j k * x) (N.phi j k * y) <=
          (Real.toNNReal (abs (N.phi j k)) : Real) * dist x y
      rw [Real.coe_toNNReal _ (abs_nonneg _), Real.dist_eq,
        Real.dist_eq, <- mul_sub, abs_mul]
    exact hlip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hsimplex :
      IsFluidState (X 0) :=
    eventLimit_state_in_simplex
      N initial hT U (K ∘ q) (hK.comp hq) omega A X hA hpair
      0 ⟨le_rfl, hT.le⟩
  let x0 : Simplex Buffer := {
    val := X 0
    nonneg := hsimplex.1
    sum_eq_one := hsimplex.2
  }
  have hinitial :
      Tendsto
        (fun r i =>
          ((initial (K (q r)) i : Nat) : Real) / (K (q r) : Nat))
        atTop (nhds (fun i => x0 i)) := by
    rw [tendsto_pi_nhds]
    intro i
    rw [Metric.tendsto_atTop]
    intro epsilon hepsilon
    obtain ⟨r0, hr0⟩ := hstate epsilon hepsilon
    refine ⟨r0, fun r hr => ?_⟩
    have hz := hr0 r hr 0 ⟨le_rfl, hT.le⟩ i
    simpa [Real.dist_eq, scaledQueueStateFrom, eventEpochCount,
      eventTokenPrefix, runTokens, x0] using hz
  exact ⟨q, hq, X, x0, hpair, hinitial, fun i => rfl⟩

private noncomputable def fluidReturnInitialFamily
    (K : Nat -> PNat)
    (z : forall n, JobState Buffer (K n : Nat))
    (L : PNat) : JobState Buffer (L : Nat) := by
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

private theorem fluidReturnInitialFamily_apply
    (K : Nat -> PNat) (hK : StrictMono K)
    (z : forall n, JobState Buffer (K n : Nat)) (n : Nat) :
    fluidReturnInitialFamily N K z (K n) = z n := by
  classical
  apply JobState.ext
  funext i
  change
    Function.extend K (fun m => (z m).jobs)
      (fun M => (N.eventInitialState M).jobs) (K n) i =
        (z n).jobs i
  rw [hK.injective.extend_apply]

/-- Negative drift forces every sufficiently large finite queue, from every
initial state, into any prescribed normalized neighborhood of `alpha` at one
common event-epoch fluid time, on every simultaneous IID strong-law path. -/
theorem negativeDrift_eventually_uniform_eventToken_return
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative :
      PaperStatements.Network.NegativeDriftCondition
        (N := N) alpha U)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists T : Real, 0 < T /\
      forall omega : N.TokenPath,
        (forall jk : TokenType (Buffer := Buffer) (Server := Server),
          Tendsto (fun n => N.empiricalFrequency jk n omega)
            atTop (nhds (N.phi jk.1 jk.2))) ->
        Filter.Eventually
          (fun K : PNat =>
            forall x : JobState Buffer (K : Nat),
              IsNearNormalizedState
                (N.runTokens (U K) x
                  (N.eventTokenPrefix
                    (Nat.floor (T * ((K : Nat) : Real))) omega))
                alpha epsilon)
          atTop := by
  obtain ⟨eta, heta, hattraction⟩ :=
    PaperStatements.Network.FluidModelSolution.eq_alpha_of_nominal_negativeDrift
      alpha halpha hnegative
  let T : Real := 1 / eta
  have hT : 0 < T := by
    dsimp [T]
    positivity
  refine ⟨T, hT, ?_⟩
  intro omega homega
  by_contra hnot
  have hfrequent :
      Filter.Frequently
        (fun K : PNat =>
          Not (forall x : JobState Buffer (K : Nat),
            IsNearNormalizedState
              (N.runTokens (U K) x
                (N.eventTokenPrefix
                  (Nat.floor (T * ((K : Nat) : Real))) omega))
              alpha epsilon))
        atTop :=
    Filter.not_eventually.mp hnot
  obtain ⟨K0, hK0top, hbad0⟩ :=
    Filter.exists_seq_forall_of_frequently hfrequent
  obtain ⟨q, hq, hK⟩ :=
    Filter.strictMono_subseq_of_tendsto_atTop hK0top
  let K : Nat -> PNat := K0 ∘ q
  have hKstrict : StrictMono K := hK
  have hexists (n : Nat) :
      exists x : JobState Buffer (K n : Nat),
        Not (IsNearNormalizedState
          (N.runTokens (U (K n)) x
            (N.eventTokenPrefix
              (Nat.floor (T * ((K n : Nat) : Real))) omega))
          alpha epsilon) := by
    exact Classical.not_forall.mp (hbad0 (q n))
  choose z hz using hexists
  let initial : forall L : PNat, JobState Buffer (L : Nat) :=
    fluidReturnInitialFamily N K z
  obtain ⟨r, hr, X, x0, hpair, hinitial, hX0⟩ :=
    N.eventEpochExecutionFrom_pairCompactness
      initial T hT U K hKstrict omega homega
  have hA :
      IsAbsolutelyContinuousMatrixPath T
        (fun t j k => N.phi j k * t) := by
    intro j k
    have hlip :
        LipschitzWith (Real.toNNReal (abs (N.phi j k)))
          (fun t : Real => N.phi j k * t) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      change
        dist (N.phi j k * x) (N.phi j k * y) <=
          (Real.toNNReal (abs (N.phi j k)) : Real) * dist x y
      rw [Real.coe_toNNReal _ (abs_nonneg _), Real.dist_eq,
        Real.dist_eq, <- mul_sub, abs_mul]
    exact hlip.lipschitzOnWith.absolutelyContinuousOnInterval
  obtain ⟨p, hp, s, hsX, hallocation⟩ :=
    N.eventEpochExecutionFrom_stochasticFluidExtension initial
      T hT x0 U (K ∘ r) (hKstrict.comp hr) omega
      (fun t j k => N.phi j k * t) X hX0 hA hpair
  have hsFluid : s.IsFluidLimit := by
    intro t ht j k
    rfl
  have hXT : X T = fun i => alpha i := by
    rw [<- hsX]
    exact hattraction T x0 (fun t j k => N.phi j k * t) s hsFluid
      T ⟨hT.le, le_rfl⟩ (by simp [T])
  obtain ⟨n0, hn0⟩ := hpair.2 epsilon hepsilon
  have hnear :
      IsNearNormalizedState
        (N.runTokens (U (K (r n0))) (z (r n0))
          (N.eventTokenPrefix
            (Nat.floor
              (T * ((K (r n0) : Nat) : Real))) omega))
        alpha epsilon := by
    intro i
    have hi := hn0 n0 le_rfl T ⟨hT.le, le_rfl⟩ i
    change
      abs
        ((N.eventEpochExecutionFrom initial).state
            U ((K ∘ r) n0) omega T i -
          X T i) < epsilon at hi
    rw [N.eventEpochExecutionFrom_state_at
      initial U ((K ∘ r) n0) omega T hT.le i] at hi
    simp only [Function.comp_apply] at hi
    rw [show initial (K (r n0)) = z (r n0) by
      exact fluidReturnInitialFamily_apply
        N K hKstrict z (r n0)] at hi
    rw [show X T i = alpha i from congrFun hXT i] at hi
    simpa [Function.comp_apply] using hi
  exact hz (r n0) hnear

/-- Real mass assigned by a finite PMF to a finite set. -/
noncomputable def finiteSetMass {A : Type*} [Fintype A]
    (pi : PMF A) (s : Finset A) : Real :=
  Finset.sum s fun x => (pi x).toReal

/-- Finite queue states in the coordinatewise normalized
`epsilon`-neighborhood of `alpha`. -/
noncomputable def nearAlphaStates
    (alpha : Simplex Buffer) (epsilon : Real) (K : Nat) :
    Finset (JobState Buffer K) := by
  classical
  exact Finset.univ.filter fun x =>
    IsNearNormalizedState x alpha epsilon

@[simp]
theorem mem_nearAlphaStates_iff
    (alpha : Simplex Buffer) (epsilon : Real) {K : Nat}
    (x : JobState Buffer K) :
    x ∈ nearAlphaStates alpha epsilon K <->
      IsNearNormalizedState x alpha epsilon := by
  classical
  simp [nearAlphaStates]

private theorem fluidReturn_nStepLaw_pure_succ_first
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (n : Nat) :
    N.nStepLaw U (PMF.pure x) (n + 1) =
      (N.transitionPMF U x).bind
        (fun y => N.nStepLaw U (PMF.pure y) n) := by
  induction n generalizing x with
  | zero =>
      simpa using (PMF.bind_pure (N.transitionPMF U x)).symm
  | succ n ih =>
      rw [N.nStepLaw_succ, ih, PMF.bind_bind]
      apply congrArg
      funext y
      exact N.nStepLaw_succ U (PMF.pure y) n

private theorem fluidReturn_tokenVectorLaw_succ_eq_bind (n : Nat) :
    N.tokenVectorLaw (n + 1) =
      N.tokenLaw.bind (fun jk =>
        (N.tokenVectorLaw n).map (Fin.cons jk)) := by
  classical
  apply PMF.ext
  intro tokens
  apply (ENNReal.toReal_eq_toReal_iff'
    ((N.tokenVectorLaw (n + 1)).apply_ne_top tokens)
    ((N.tokenLaw.bind (fun jk =>
      (N.tokenVectorLaw n).map (Fin.cons jk))).apply_ne_top tokens)).mp
  rw [N.tokenVectorLaw_apply_toReal]
  rw [PMF.bind_apply, tsum_fintype]
  rw [ENNReal.toReal_sum (fun jk _ =>
    ENNReal.mul_ne_top (N.tokenLaw.apply_ne_top jk)
      (((N.tokenVectorLaw n).map (Fin.cons jk)).apply_ne_top tokens))]
  simp_rw [ENNReal.toReal_mul]
  simp_rw [PMF.map_apply, tsum_fintype]
  rw [Fin.prod_univ_succ]
  rw [Finset.sum_eq_single (tokens 0)]
  next =>
    rw [Finset.sum_eq_single (fun i => tokens i.succ)]
    next =>
      have hself :
          tokens = Fin.cons (tokens 0) (fun i => tokens i.succ) :=
        (Fin.cons_self_tail tokens).symm
      rw [if_pos hself, N.tokenVectorLaw_apply_toReal]
    next =>
      intro tail htail hne
      have hnot :
          Not (tokens = Fin.cons (tokens 0) tail) := by
        intro h
        apply hne
        funext i
        exact (congrFun h i.succ).symm
      simp [hnot]
    next =>
      simp
  next =>
    intro jk hjk hne
    have hcons (tail : Fin n ->
        TokenType (Buffer := Buffer) (Server := Server)) :
        Not (tokens = Fin.cons jk tail) := by
      intro h
      apply hne
      exact (congrFun h 0).symm
    simp [hcons]
  next =>
    simp

/-- Exact finite-chain law of running an IID token vector for `n` epochs. -/
theorem nStepLaw_pure_eq_tokenVectorLaw_map_runTokens
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (n : Nat) :
    N.nStepLaw U (PMF.pure x) n =
      (N.tokenVectorLaw n).map
        (fun tokens => N.runTokens U x (List.ofFn tokens)) := by
  induction n generalizing x with
  | zero =>
      rw [N.nStepLaw_zero]
      have hrun :
          (fun tokens : Fin 0 ->
              TokenType (Buffer := Buffer) (Server := Server) =>
            N.runTokens U x (List.ofFn tokens)) =
            Function.const
              (Fin 0 ->
                TokenType (Buffer := Buffer) (Server := Server)) x := by
        funext tokens
        simp [runTokens]
      rw [hrun, PMF.map_const]
  | succ n ih =>
      rw [fluidReturn_nStepLaw_pure_succ_first N U x n]
      rw [fluidReturn_tokenVectorLaw_succ_eq_bind N n, PMF.map_bind]
      rw [transitionPMF, PMF.bind_map]
      apply congrArg
      funext jk
      calc
        (Function.comp (fun y => N.nStepLaw U (PMF.pure y) n)
            (N.queueStep U x)) jk =
            N.nStepLaw U (PMF.pure (N.queueStep U x jk)) n := rfl
        _ = (N.tokenVectorLaw n).map
            (fun tokens =>
              N.runTokens U (N.queueStep U x jk)
                (List.ofFn tokens)) :=
          ih (N.queueStep U x jk)
        _ = (N.tokenVectorLaw n).map
            (Function.comp
              (fun tokens => N.runTokens U x (List.ofFn tokens))
              (Fin.cons jk)) := by
          apply congrArg (fun f :
            (Fin n ->
              TokenType (Buffer := Buffer) (Server := Server)) ->
                JobState Buffer K =>
              (N.tokenVectorLaw n).map f)
          funext tokens
          simp [Function.comp_def, List.ofFn_succ, runTokens]
        _ = ((N.tokenVectorLaw n).map (Fin.cons jk)).map
            (fun tokens => N.runTokens U x (List.ofFn tokens)) := by
          exact (PMF.map_comp
            (p := N.tokenVectorLaw n) (f := Fin.cons jk)
            (g := fun tokens : Fin (n + 1) ->
              TokenType (Buffer := Buffer) (Server := Server) =>
                N.runTokens U x (List.ofFn tokens))).symm

/-- The concrete token-path endpoint event has exactly the corresponding
finite-chain `nStepLaw` mass. -/
theorem eventTokenEndpoint_nearAlpha_measureReal_eq_finiteSetMass
    (alpha : Simplex Buffer) (epsilon : Real)
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (x : JobState Buffer K) (n : Nat) :
    N.tokenPathMeasure.real
        {omega |
          IsNearNormalizedState
            (N.runTokens U x (N.eventTokenPrefix n omega))
            alpha epsilon} =
      finiteSetMass (N.nStepLaw U (PMF.pure x) n)
        (nearAlphaStates alpha epsilon K) := by
  letI : MeasurableSpace (JobState Buffer K) := ⊤
  let f :
      (Fin n -> TokenType (Buffer := Buffer) (Server := Server)) ->
        JobState Buffer K :=
    fun tokens => N.runTokens U x (List.ofFn tokens)
  let s : Finset (JobState Buffer K) :=
    nearAlphaStates alpha epsilon K
  have hlaw :=
    (N.tokenVector_hasLaw n).measureReal_eq
      (p := fun tokens => f tokens ∈ s)
      MeasurableSet.of_discrete
  calc
    N.tokenPathMeasure.real
        {omega |
          IsNearNormalizedState
            (N.runTokens U x (N.eventTokenPrefix n omega))
            alpha epsilon} =
        N.tokenPathMeasure.real
          {omega | f (N.tokenVector n omega) ∈ s} := by
      apply congrArg
      ext omega
      simp only [Set.mem_setOf_eq]
      change
        IsNearNormalizedState
            (N.runTokens U x (List.ofFn (N.tokenVector n omega)))
            alpha epsilon <->
          f (N.tokenVector n omega) ∈ s
      rw [mem_nearAlphaStates_iff]
    _ = (N.tokenVectorLaw n).toMeasure.real
        {tokens | f tokens ∈ s} := hlaw
    _ = ((N.tokenVectorLaw n).map f).toMeasure.real (s : Set _) := by
      simp only [Measure.real_def]
      rw [PMF.toMeasure_map_apply]
      · rfl
      · exact Measurable.of_discrete
      · exact MeasurableSet.of_discrete
    _ = finiteSetMass (N.nStepLaw U (PMF.pure x) n) s := by
      rw [N.nStepLaw_pure_eq_tokenVectorLaw_map_runTokens U x n]
      change
        (((N.tokenVectorLaw n).map f).toMeasure (s : Set _)).toReal =
          Finset.sum s (fun y => (((N.tokenVectorLaw n).map f) y).toReal)
      rw [PMF.toMeasure_apply_finset]
      exact ENNReal.toReal_sum
        (fun y hy => ((N.tokenVectorLaw n).map f).apply_ne_top y)

private noncomputable def eventReturnGood
    (alpha : Simplex Buffer) (epsilon : Real)
    (U : N.DeterministicPolicySequence) (T : Real) (K : PNat) :
    Set N.TokenPath :=
  {omega |
    forall x : JobState Buffer (K : Nat),
      IsNearNormalizedState
        (N.runTokens (U K) x
          (N.eventTokenPrefix
            (Nat.floor (T * ((K : Nat) : Real))) omega))
        alpha epsilon}

private noncomputable def eventReturnTail
    (alpha : Simplex Buffer) (epsilon : Real)
    (U : N.DeterministicPolicySequence) (T : Real) (K0 : PNat) :
    Set N.TokenPath :=
  {omega |
    forall K : PNat, K0 <= K ->
      omega ∈ eventReturnGood N alpha epsilon U T K}

private theorem eventReturnTail_mono
    (alpha : Simplex Buffer) (epsilon : Real)
    (U : N.DeterministicPolicySequence) (T : Real) :
    Monotone (eventReturnTail N alpha epsilon U T) := by
  intro K0 K1 hK omega homega L hL
  exact homega L (hK.trans hL)

/-- The pathwise uniform return and the common IID strong-law event imply a
uniform finite-chain return probability of at least one half. -/
theorem negativeDrift_uniformHalfNStepReturn
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnegative :
      PaperStatements.Network.NegativeDriftCondition
        (N := N) alpha U)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    exists T : Real, 0 < T /\
      Filter.Eventually
        (fun K : PNat =>
          forall x : JobState Buffer (K : Nat),
            (1 / 2 : Real) <=
              finiteSetMass
                (N.nStepLaw (U K) (PMF.pure x)
                  (Nat.floor (T * ((K : Nat) : Real))))
                (nearAlphaStates alpha epsilon (K : Nat)))
        atTop := by
  obtain ⟨T, hT, hpath⟩ :=
    N.negativeDrift_eventually_uniform_eventToken_return
      alpha halpha U hnegative epsilon hepsilon
  refine ⟨T, hT, ?_⟩
  let Good : PNat -> Set N.TokenPath :=
    eventReturnGood N alpha epsilon U T
  let Tail : PNat -> Set N.TokenPath :=
    eventReturnTail N alpha epsilon U T
  have hTailMono : Monotone Tail := by
    exact eventReturnTail_mono N alpha epsilon U T
  have hAEUnion :
      Filter.Eventually
        (fun omega => omega ∈ ⋃ K : PNat, Tail K)
        (ae N.tokenPathMeasure) := by
    filter_upwards [N.all_empiricalFrequencies_tendsto_phi_ae] with
      omega homega
    obtain ⟨K0, hK0⟩ :=
      Filter.eventually_atTop.mp (hpath omega homega)
    apply Set.mem_iUnion.2
    refine ⟨K0, ?_⟩
    change
      forall K : PNat, K0 <= K ->
        omega ∈ eventReturnGood N alpha epsilon U T K
    intro K hK
    exact hK0 K hK
  have hUnionCompl :
      N.tokenPathMeasure (⋃ K : PNat, Tail K)ᶜ = 0 := by
    simpa only [Set.compl_def, Set.mem_setOf_eq] using
      (ae_iff.mp hAEUnion)
  have hUnion :
      N.tokenPathMeasure (⋃ K : PNat, Tail K) = 1 := by
    calc
      N.tokenPathMeasure (⋃ K : PNat, Tail K) =
          N.tokenPathMeasure Set.univ :=
        measure_of_measure_compl_eq_zero hUnionCompl
      _ = 1 := measure_univ
  have hMeasureTendsto :
      Tendsto (fun K : PNat => N.tokenPathMeasure (Tail K))
        atTop (nhds 1) := by
    have h :=
      MeasureTheory.tendsto_measure_iUnion_atTop
        (μ := N.tokenPathMeasure) hTailMono
    change
      Tendsto (fun K : PNat => N.tokenPathMeasure (Tail K))
        atTop
        (nhds (N.tokenPathMeasure (⋃ K : PNat, Tail K))) at h
    simpa only [hUnion] using h
  have hMeasureRealTendsto :
      Tendsto (fun K : PNat => N.tokenPathMeasure.real (Tail K))
        atTop (nhds 1) := by
    have h :=
      (ENNReal.tendsto_toReal (a := (1 : ENNReal)) (by norm_num)).comp
        hMeasureTendsto
    change
      Tendsto
        (fun K : PNat => (N.tokenPathMeasure (Tail K)).toReal)
        atTop (nhds ((1 : ENNReal).toReal)) at h
    simpa only [Measure.real_def, ENNReal.toReal_one] using h
  have hHalf :
      Filter.Eventually
        (fun K : PNat =>
          (1 / 2 : Real) <= N.tokenPathMeasure.real (Tail K))
        atTop := by
    rw [Metric.tendsto_atTop] at hMeasureRealTendsto
    obtain ⟨K0, hK0⟩ :=
      hMeasureRealTendsto (1 / 2) (by norm_num)
    refine Filter.eventually_atTop.2 ⟨K0, fun K hK => ?_⟩
    have hd := hK0 K hK
    rw [Real.dist_eq] at hd
    have hlower := (abs_lt.mp hd).1
    linarith
  filter_upwards [hHalf] with K hTailHalf
  intro x
  let endpointEvent : Set N.TokenPath :=
    {omega |
      IsNearNormalizedState
        (N.runTokens (U K) x
          (N.eventTokenPrefix
            (Nat.floor (T * ((K : Nat) : Real))) omega))
        alpha epsilon}
  have hsubset : Tail K ⊆ endpointEvent := by
    intro omega homega
    change
      forall L : PNat, K <= L ->
        omega ∈ eventReturnGood N alpha epsilon U T L at homega
    exact homega K le_rfl x
  have hrealMono :
      N.tokenPathMeasure.real (Tail K) <=
        N.tokenPathMeasure.real endpointEvent := by
    unfold Measure.real
    exact ENNReal.toReal_mono
      (measure_ne_top N.tokenPathMeasure endpointEvent)
      (measure_mono hsubset)
  calc
    (1 / 2 : Real) <= N.tokenPathMeasure.real (Tail K) := hTailHalf
    _ <= N.tokenPathMeasure.real endpointEvent := hrealMono
    _ = finiteSetMass
          (N.nStepLaw (U K) (PMF.pure x)
            (Nat.floor (T * ((K : Nat) : Real))))
          (nearAlphaStates alpha epsilon (K : Nat)) := by
      exact N.eventTokenEndpoint_nearAlpha_measureReal_eq_finiteSetMass
        alpha epsilon (U K) x
          (Nat.floor (T * ((K : Nat) : Real)))

private theorem nStepLaw_eq_bind_pure_start
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (n : Nat) :
    N.nStepLaw U pi n =
      pi.bind (fun x => N.nStepLaw U (PMF.pure x) n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [N.nStepLaw_succ, ih, PMF.bind_bind]
      congr 1

theorem invariant_finiteSetMass_ge_of_uniform_nStep_return
    {K : Nat} (U : N.DeterministicStationaryPolicy K)
    (pi : PMF (JobState Buffer K)) (hinvariant : N.IsInvariantPMF U pi)
    (n : Nat) (s : Finset (JobState Buffer K)) (p : Real)
    (hreturn : forall x,
      p <= finiteSetMass (N.nStepLaw U (PMF.pure x) n) s) :
    p <= finiteSetMass pi s := by
  have hstationary : N.nStepLaw U pi n = pi :=
    N.nStepLaw_eq_of_isInvariant U pi hinvariant n
  rw [<- hstationary, nStepLaw_eq_bind_pure_start]
  unfold finiteSetMass
  simp_rw [PMF.bind_apply, tsum_fintype]
  simp_rw [ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top (pi.apply_ne_top x)
      ((N.nStepLaw U (PMF.pure x) n).apply_ne_top _))]
  simp_rw [ENNReal.toReal_mul]
  calc
    p = Finset.sum Finset.univ (fun x => (pi x).toReal * p) := by
      rw [<- Finset.sum_mul, PMF.sum_toReal, one_mul]
    _ <= Finset.sum Finset.univ (fun x =>
        (pi x).toReal *
          Finset.sum s (fun y =>
            (N.nStepLaw U (PMF.pure x) n y).toReal)) := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hreturn x) ENNReal.toReal_nonneg
    _ = Finset.sum Finset.univ (fun x =>
        Finset.sum s (fun y =>
          (pi x).toReal *
            (N.nStepLaw U (PMF.pure x) n y).toReal)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ = Finset.sum s (fun y =>
        Finset.sum Finset.univ (fun x =>
          (pi x).toReal *
            (N.nStepLaw U (PMF.pure x) n y).toReal)) := by
      exact Finset.sum_comm
        (s := Finset.univ) (t := s)
        (f := fun x y =>
          (pi x).toReal *
            (N.nStepLaw U (PMF.pure x) n y).toReal)

theorem minimumInvariantPMF_nearAlpha_mass_ge_of_uniform_return
    (alpha : Simplex Buffer) (epsilon p : Real) (K : PNat)
    (U : N.DeterministicPolicySequence) (n : Nat)
    (hreturn : forall x : JobState Buffer (K : Nat),
      p <= finiteSetMass
        (N.nStepLaw (U K) (PMF.pure x) n)
        (nearAlphaStates alpha epsilon (K : Nat))) :
    p <= finiteSetMass (N.minimumInvariantPMF (U K))
      (nearAlphaStates alpha epsilon (K : Nat)) := by
  exact invariant_finiteSetMass_ge_of_uniform_nStep_return
    N (U K) (N.minimumInvariantPMF (U K))
      (N.minimumInvariantPMF_isInvariant (U K)) n
      (nearAlphaStates alpha epsilon (K : Nat)) p hreturn

theorem exists_atom_ge_average_of_mass_ge
    {A : Type*} [Fintype A] [Nonempty A]
    (pi : PMF A) (s : Finset A)
    (p : Real) (hp : 0 < p)
    (hmass : p <= finiteSetMass pi s) :
    exists x, x ∈ s /\
      p / (Fintype.card A : Real) <= (pi x).toReal := by
  classical
  by_contra h
  push Not at h
  have hcard : 0 < (Fintype.card A : Real) := by
    exact_mod_cast Fintype.card_pos
  have hterm (x : A) (hx : x ∈ s) :
      (pi x).toReal < p / (Fintype.card A : Real) :=
    h x hx
  have hsnonempty : s.Nonempty := by
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty.mp hs] at hmass
    simp [finiteSetMass] at hmass
    linarith
  have hsum :
      finiteSetMass pi s <
        Finset.sum s (fun _ : A =>
          p / (Fintype.card A : Real)) := by
    unfold finiteSetMass
    apply Finset.sum_lt_sum
    · intro x hx
      exact (hterm x hx).le
    · obtain ⟨x, hx⟩ := hsnonempty
      exact ⟨x, hx, hterm x hx⟩
  have hcardS :
      (s.card : Real) <= (Fintype.card A : Real) := by
    exact_mod_cast Finset.card_le_univ s
  have hupper :
      Finset.sum s (fun _ : A =>
          p / (Fintype.card A : Real)) <= p := by
    rw [Finset.sum_const, nsmul_eq_mul]
    calc
      (s.card : Real) * (p / (Fintype.card A : Real)) <=
          (Fintype.card A : Real) *
            (p / (Fintype.card A : Real)) := by
        exact mul_le_mul_of_nonneg_right hcardS
          (div_nonneg hp.le hcard.le)
      _ = p := by field_simp
  linarith

theorem exists_nearAlpha_atom_of_uniform_return
    (alpha : Simplex Buffer) (epsilon : Real) (K : PNat)
    (U : N.DeterministicPolicySequence) (n : Nat)
    (hreturn : forall x : JobState Buffer (K : Nat),
      (1 / 2 : Real) <= finiteSetMass
        (N.nStepLaw (U K) (PMF.pure x) n)
        (nearAlphaStates alpha epsilon (K : Nat))) :
    exists y : JobState Buffer (K : Nat),
      IsNearNormalizedState y alpha epsilon /\
      1 / (2 *
          (((K : Nat) + 1 : Nat) ^ Fintype.card Buffer : Real)) <=
        (N.minimumInvariantPMF (U K) y).toReal := by
  have hmass :
      (1 / 2 : Real) <=
        finiteSetMass (N.minimumInvariantPMF (U K))
          (nearAlphaStates alpha epsilon (K : Nat)) :=
    minimumInvariantPMF_nearAlpha_mass_ge_of_uniform_return
      N alpha epsilon (1 / 2) K U n hreturn
  obtain ⟨y, hy, hymass⟩ :=
    exists_atom_ge_average_of_mass_ge
      (N.minimumInvariantPMF (U K))
      (nearAlphaStates alpha epsilon (K : Nat))
      (1 / 2) (by norm_num) hmass
  refine ⟨y, (mem_nearAlphaStates_iff alpha epsilon y).1 hy, ?_⟩
  have hcard_pos :
      0 < (Fintype.card (JobState Buffer (K : Nat)) : Real) := by
    exact_mod_cast Fintype.card_pos
  have hcard_le :
      (Fintype.card (JobState Buffer (K : Nat)) : Real) <=
        ((((K : Nat) + 1 : Nat) ^ Fintype.card Buffer : Nat) : Real) := by
    exact_mod_cast
      JobState.card_le_coordinate_box (Buffer := Buffer) (K : Nat)
  have havg :
      (1 / 2 : Real) /
          (Fintype.card (JobState Buffer (K : Nat)) : Real) <=
        (N.minimumInvariantPMF (U K) y).toReal :=
    hymass
  calc
    1 / (2 *
        (((K : Nat) + 1 : Nat) ^ Fintype.card Buffer : Real)) <=
        (1 / 2 : Real) /
          (Fintype.card (JobState Buffer (K : Nat)) : Real) := by
      have heq :
          1 / (2 *
              (((K : Nat) + 1 : Nat) ^ Fintype.card Buffer : Real)) =
            (1 / 2 : Real) *
              (1 /
                ((((K : Nat) + 1 : Nat) ^ Fintype.card Buffer :
                    Nat) : Real)) := by
        field_simp
        simp only [Nat.cast_pow]
      rw [heq, div_eq_mul_inv]
      simpa [one_div, div_eq_mul_inv, Nat.cast_pow] using
        (mul_le_mul_of_nonneg_left
          (one_div_le_one_div_of_le hcard_pos hcard_le)
          (by norm_num : (0 : Real) <= 1 / 2))
    _ <= (N.minimumInvariantPMF (U K) y).toReal := havg

/-- Uniform finite-horizon return under the actual finite queue chain. -/
def UniformHalfReturn
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence) : Prop :=
  forall epsilon : Real, 0 < epsilon ->
    exists T : Real, 0 < T /\
      Filter.Eventually
        (fun K : PNat =>
          forall x : JobState Buffer (K : Nat),
            (1 / 2 : Real) <= finiteSetMass
              (N.nStepLaw (U K) (PMF.pure x)
                (Nat.floor (T * ((K : Nat) : Real))))
              (nearAlphaStates alpha epsilon (K : Nat)))
        atTop

def NegativeDriftUniformHalfReturnStatement : Prop :=
  forall (alpha : Simplex Buffer), alpha.IsInterior ->
  forall U : N.DeterministicPolicySequence,
    PaperStatements.Network.NegativeDriftCondition
      (N := N) alpha U ->
    UniformHalfReturn N alpha U

theorem negativeDriftUniformHalfReturnStatement :
    NegativeDriftUniformHalfReturnStatement N := by
  intro alpha halpha U hnegative epsilon hepsilon
  exact N.negativeDrift_uniformHalfNStepReturn
    alpha halpha U hnegative epsilon hepsilon

theorem UniformHalfReturn.eventually_nearAlpha_polynomial_atom
    (alpha : Simplex Buffer) (U : N.DeterministicPolicySequence)
    (hreturn : UniformHalfReturn N alpha U)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun K : PNat =>
        exists y : JobState Buffer (K : Nat),
          IsNearNormalizedState y alpha epsilon /\
          1 / (2 *
              (((K : Nat) + 1 : Nat) ^ Fintype.card Buffer : Real)) <=
            (N.minimumInvariantPMF (U K) y).toReal)
      atTop := by
  obtain ⟨T, hT, hreturnT⟩ := hreturn epsilon hepsilon
  filter_upwards [hreturnT] with K hK
  exact exists_nearAlpha_atom_of_uniform_return
    N alpha epsilon K U
      (Nat.floor (T * ((K : Nat) : Real))) hK

theorem nearAlphaAtom_rounded_forcing_polynomial_lower_bound
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop)
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (T : NNReal) (hT : 0 < T)
    (hc :
      1 + epsilon / Lyapunov.minCoordinate (fun i => alpha i) <
        (T : Real) *
          PaperStatements.Network.vAlpha (N := N) alpha f)
    (hnearAtom :
      Filter.Eventually
        (fun r =>
          exists x : JobState Buffer (K r : Nat),
            IsNearNormalizedState x alpha epsilon /\
            1 / (2 *
                (((K r : Nat) + 1 : Nat) ^
                  Fintype.card Buffer : Real)) <=
              (N.minimumInvariantPMF (U (K r)) x).toReal)
        atTop) :
    Filter.Eventually
      (fun r =>
        1 / (((K r : Nat) : Real) ^
            (Fintype.card Buffer + 4)) *
          (poissonCountLaw N (K r) T).real
            {ConverseAsymptotics.roundedPoissonCount T f (K r)} <=
          N.minimumInvariantLossFamily U (K r))
      atTop := by
  have hforce :=
    N.roundedCount_vAlpha_force_eventually
      alpha halpha f hf T hT
      (1 + epsilon / Lyapunov.minCoordinate (fun i => alpha i))
      hc K hK
  have hprefactor :=
    N.roundedCount_prefactor_le_power_eventually f hf T K hK
  have hKnat :
      Tendsto (fun r => (K r : Nat)) atTop atTop :=
    tendsto_PNat_val_atTop_atTop.comp hK
  have hlarge :
      Filter.Eventually (fun r => 2 <= (K r : Nat)) atTop :=
    (eventually_ge_atTop 2).filter_mono hKnat
  filter_upwards [hnearAtom, hforce, hprefactor, hlarge] with
    r hnear_r hforce_r hprefactor_r hlarge_r
  obtain ⟨x, hxnear, hxmass⟩ := hnear_r
  let n : Server -> Buffer -> Nat :=
    ConverseAsymptotics.roundedPoissonCount T f (K r)
  let mass : Real :=
    (N.minimumInvariantPMF (U (K r)) x).toReal
  let atom : Real := (poissonCountLaw N (K r) T).real {n}
  let box : Real :=
    ((((K r : Nat) + 1 : Nat) ^ Fintype.card Buffer : Nat) : Real)
  let total : Real := (N.totalFiniteCount n : Real)
  let loss : Real := N.minimumInvariantLossFamily U (K r)
  let power : Real :=
    ((K r : Nat) : Real) ^ (Fintype.card Buffer + 3)
  let largerPower : Real :=
    ((K r : Nat) : Real) ^ (Fintype.card Buffer + 4)
  have hstation :
      mass * atom <= total * loss := by
    have hbridge :
        atom <= N.exactCountVectorMass n := by
      dsimp [atom, n]
      exact N.poissonCountLaw_real_singleton_le_exactCountVectorMass
        (K r) T
          (ConverseAsymptotics.roundedPoissonCount T f (K r))
    have hforced :
        mass * N.exactCountVectorMass n <= total * loss := by
      dsimp [mass, total, loss, n]
      apply N.forcedCountMass_near_alpha_le_minimumInvariantLoss
        alpha halpha (K r).pos (U (K r)) x
          (ConverseAsymptotics.roundedPoissonCount T f (K r))
          epsilon hepsilon
      · intro i
        exact (hxnear i).le
      · exact hforce_r
    exact
      (mul_le_mul_of_nonneg_left hbridge ENNReal.toReal_nonneg).trans
        hforced
  have hmass : 1 / (2 * box) <= mass := by
    dsimp [box, mass]
    simpa only [Nat.cast_pow] using hxmass
  have hbox : 0 < box := by
    dsimp [box]
    positivity
  have hden : 0 < 2 * box := mul_pos (by norm_num) hbox
  have hone_mass : 1 <= (2 * box) * mass := by
    have h := (div_le_iff₀ hden).1 hmass
    simpa [mul_comm] using h
  have hatom : 0 <= atom := by
    dsimp [atom]
    exact MeasureTheory.measureReal_nonneg
  have hloss : 0 <= loss := by
    dsimp [loss]
    exact N.minimumInvariantLossFamily_nonnegative U (K r)
  have hpower : 0 < power := by
    dsimp [power]
    positivity
  have hlargerPower : 0 < largerPower := by
    dsimp [largerPower]
    positivity
  have htwoPower :
      2 * power <= largerPower := by
    have hlargeReal : (2 : Real) <= (K r : Nat) := by
      exact_mod_cast hlarge_r
    have hpoweq :
        largerPower = power * ((K r : Nat) : Real) := by
      dsimp [largerPower, power]
      rw [show Fintype.card Buffer + 4 =
          (Fintype.card Buffer + 3) + 1 by omega, pow_succ]
    rw [hpoweq]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left (a := power)
        hlargeReal hpower.le)
  have hatom_le : atom <= largerPower * loss := by
    calc
      atom = 1 * atom := by ring
      _ <= ((2 * box) * mass) * atom :=
        mul_le_mul_of_nonneg_right hone_mass hatom
      _ = (2 * box) * (mass * atom) := by ring
      _ <= (2 * box) * (total * loss) :=
        mul_le_mul_of_nonneg_left hstation (by positivity)
      _ = (2 * (box * total)) * loss := by ring
      _ <= (2 * power) * loss := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hprefactor_r (by norm_num))
          hloss
      _ <= largerPower * loss :=
        mul_le_mul_of_nonneg_right htwoPower hloss
  change 1 / largerPower * atom <= loss
  have heq : 1 / largerPower * atom = atom / largerPower := by
    simp only [one_div, div_eq_mul_inv]
    ring
  rw [heq]
  apply (div_le_iff₀ hlargerPower).2
  simpa [mul_comm] using hatom_le

theorem negativeLiminfLogRate_le_nearAlpha_forcing_cost
    (U : N.DeterministicPolicySequence)
    (K : Nat -> PNat) (hK : Tendsto K atTop atTop)
    (hrealize :
      Tendsto
        (fun r =>
          ConverseAsymptotics.scaledLogLoss
            (N.minimumInvariantLossFamily U) (K r))
        atTop
        (nhds
          (liminf
            (ConverseAsymptotics.scaledLogLoss
              (N.minimumInvariantLossFamily U)) atTop)))
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (epsilon : Real) (hepsilon : 0 <= epsilon)
    (f : Server -> Buffer -> Real)
    (hf : forall j k, 0 <= f j k)
    (hsupport : forall j k, N.phi j k = 0 -> f j k = 0)
    (T : NNReal) (hT : 0 < T)
    (hc :
      1 + epsilon / Lyapunov.minCoordinate (fun i => alpha i) <
        (T : Real) *
          PaperStatements.Network.vAlpha (N := N) alpha f)
    (hnearAtom :
      Filter.Eventually
        (fun r =>
          exists x : JobState Buffer (K r : Nat),
            IsNearNormalizedState x alpha epsilon /\
            1 / (2 *
                (((K r : Nat) + 1 : Nat) ^
                  Fintype.card Buffer : Real)) <=
              (N.minimumInvariantPMF (U (K r)) x).toReal)
        atTop) :
    PaperStatements.negativeLiminfLogRate
        (N.minimumInvariantLossFamily U) <=
      ((((T : Real) *
        Finset.univ.sum (fun j =>
          Finset.univ.sum (fun k =>
            poissonCostReal (N.phi j k) (f j k)))) : Real) : EReal) := by
  let degree : Nat := Fintype.card Buffer + 4
  let atom : Nat -> Real := fun r =>
    (poissonCountLaw N (K r) T).real
      {ConverseAsymptotics.roundedPoissonCount T f (K r)}
  let prefactor : Nat -> Real := fun r =>
    ((K r : Nat) : Real) ^ degree
  let lower : Nat -> Real := fun r => 1 / prefactor r * atom r
  let cost : Real :=
    (T : Real) *
      Finset.univ.sum (fun j =>
        Finset.univ.sum (fun k =>
          poissonCostReal (N.phi j k) (f j k)))
  have hbound :
      Filter.Eventually
        (fun r => lower r <= N.minimumInvariantLossFamily U (K r))
        atTop := by
    simpa only [lower, prefactor, atom, degree] using
      N.nearAlphaAtom_rounded_forcing_polynomial_lower_bound
        U K hK alpha halpha epsilon hepsilon f hf T hT hc hnearAtom
  have hatom : forall r, 0 < atom r := by
    intro r
    exact N.poissonCountLaw_rounded_singleton_pos
      f hsupport T hT (K r)
  have hprefactor : forall r, 0 < prefactor r := by
    intro r
    dsimp [prefactor]
    positivity
  have hlower :
      Filter.Eventually (fun r => 0 < lower r) atTop :=
    Filter.Eventually.of_forall fun r =>
      mul_pos (div_pos zero_lt_one (hprefactor r)) (hatom r)
  have hzero :
      forall j k, N.phi j k = 0 ->
        forall q,
          ConverseAsymptotics.roundedPoissonCount T f q j k = 0 := by
    intro j k hphi q
    exact ConverseAsymptotics.roundedPoissonCount_zero
      T f j k (hsupport j k hphi)
  have hn :
      forall j k,
        Tendsto
          (fun q : Nat =>
            (ConverseAsymptotics.roundedPoissonCount T f q j k : Real) / q)
          atTop (nhds ((T : Real) * f j k)) :=
    ConverseAsymptotics.roundedPoissonCount_ratio_tendsto T f hf
  have hatom_cost :
      Tendsto
        (fun r => -Real.log (atom r) / ((K r : Nat) : Real))
        atTop (nhds cost) := by
    have hfull :=
      ConverseAsymptotics.poissonCountLaw_log_asymptotic_pnat
        N T hT f (ConverseAsymptotics.roundedPoissonCount T f)
        hzero hn
    exact hfull.comp hK
  have hprefactor_rate :
      Tendsto
        (fun r => Real.log (prefactor r) / ((K r : Nat) : Real))
        atTop (nhds 0) := by
    exact (ConverseAsymptotics.tendsto_log_pnat_pow_div degree).comp hK
  have hlower_cost :
      Tendsto
        (fun r => -Real.log (lower r) / ((K r : Nat) : Real))
        atTop (nhds cost) := by
    have hsum := hprefactor_rate.add hatom_cost
    simpa only [zero_add] using hsum.congr' (by
      filter_upwards [] with r
      dsimp [lower]
      rw [one_div, Real.log_mul
        (inv_ne_zero (hprefactor r).ne') (hatom r).ne',
        Real.log_inv]
      ring)
  exact
    ConverseAsymptotics.negativeLiminfLogRate_le_of_realizing_lower_bound
      (N.minimumInvariantLossFamily U) lower K cost
      hrealize hlower hbound hlower_cost

theorem negativeLiminfLogRate_le_gammaCB_of_nearAlpha_atoms
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hnearAtoms :
      forall epsilon : Real, 0 < epsilon ->
        Filter.Eventually
          (fun K : PNat =>
            exists x : JobState Buffer (K : Nat),
              IsNearNormalizedState x alpha epsilon /\
              1 / (2 *
                  (((K : Nat) + 1 : Nat) ^
                    Fintype.card Buffer : Real)) <=
                (N.minimumInvariantPMF (U K) x).toReal)
          atTop) :
    PaperStatements.negativeLiminfLogRate
        (N.minimumInvariantLossFamily U) <=
      PaperStatements.Network.gammaCB (N := N) alpha := by
  obtain ⟨K, hrealize, hK⟩ :=
    exists_seq_tendsto_liminf
      (f := (atTop : Filter PNat))
      (u := ConverseAsymptotics.scaledLogLoss
        (N.minimumInvariantLossFamily U))
  unfold PaperStatements.Network.gammaCB
  apply le_sInf
  intro q hq
  obtain ⟨f, hf, hv, rfl⟩ := hq
  by_cases htop : N.localRate f = (Top.top : ENNReal)
  · rw [htop, EReal.coe_ennreal_top]
    rw [EReal.top_div_of_pos_ne_top
      (EReal.coe_pos.2 hv) (EReal.coe_ne_top _)]
    exact le_top
  have hsupport :
      forall j k, N.phi j k = 0 -> f j k = 0 :=
    N.localRate_ne_top_implies_zero_of_phi_eq_zero f htop
  let I : Real :=
    Finset.univ.sum (fun j =>
      Finset.univ.sum (fun k =>
        poissonCostReal (N.phi j k) (f j k)))
  have hI : 0 <= I := by
    dsimp [I]
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro k hk
    rcases (N.phi_nonneg j k).eq_or_lt with hphi_zero | hphi_pos
    · rw [<- hphi_zero, hsupport j k hphi_zero.symm]
      simp [poissonCostReal]
    · exact poissonCostReal_nonneg hphi_pos (hf j k)
  let m : Real := Lyapunov.minCoordinate (fun i => alpha i)
  have hm : 0 < m := Lyapunov.minCoordinate_pos halpha
  have hreal :
      PaperStatements.negativeLiminfLogRate
          (N.minimumInvariantLossFamily U) <=
        ((I / PaperStatements.Network.vAlpha (N := N) alpha f :
            Real) : EReal) := by
    apply ereal_le_coe_of_forall_pos_le_add
    intro delta hdelta
    let v : Real := PaperStatements.Network.vAlpha (N := N) alpha f
    have hv' : 0 < v := hv
    have hIone : 0 < I + 1 := by linarith
    let epsilon : Real :=
      delta * m * v / (2 * (I + 1))
    have hepsilon : 0 < epsilon := by
      dsimp [epsilon]
      positivity
    let c : Real := 1 + epsilon / m
    let t : Real := c / v + delta / (2 * (I + 1))
    have ht : 0 < t := by
      dsimp [t, c]
      positivity
    let T : NNReal := ⟨t, ht.le⟩
    have hT : 0 < T := by
      exact_mod_cast ht
    have hforce : c < (T : Real) * v := by
      change c < t * v
      dsimp [t]
      have hextra :
          0 < delta / (2 * (I + 1)) * v := by positivity
      calc
        c < c + delta / (2 * (I + 1)) * v :=
          lt_add_of_pos_right c hextra
        _ = (c / v + delta / (2 * (I + 1))) * v := by
          field_simp
    have hnearK :
        Filter.Eventually
          (fun r =>
            exists x : JobState Buffer (K r : Nat),
              IsNearNormalizedState x alpha epsilon /\
              1 / (2 *
                  (((K r : Nat) + 1 : Nat) ^
                    Fintype.card Buffer : Real)) <=
                (N.minimumInvariantPMF (U (K r)) x).toReal)
          atTop :=
      (hnearAtoms epsilon hepsilon).filter_mono hK
    have hbound :=
      N.negativeLiminfLogRate_le_nearAlpha_forcing_cost
        U K hK hrealize alpha halpha epsilon hepsilon.le
        f hf hsupport T hT
        (by
          change c < (T : Real) * v
          exact hforce)
        hnearK
    have hcost :
        (T : Real) * I <= I / v + delta := by
      change t * I <= I / v + delta
      dsimp [t, c, epsilon]
      have hfrac : delta * I / (I + 1) <= delta := by
        apply (div_le_iff₀ hIone).2
        nlinarith
      field_simp [ne_of_gt hm, ne_of_gt hv', ne_of_gt hIone] at *
      nlinarith
    exact hbound.trans (EReal.coe_le_coe_iff.mpr hcost)
  have hlocal :=
    ConverseAsymptotics.localRate_eq_ofReal_sum_poissonCostReal
      N f hf hsupport
  rw [hlocal, EReal.coe_ennreal_ofReal, max_eq_left hI,
    <- EReal.coe_div]
  exact hreal

theorem UniformHalfReturn.negativeLiminfLogRate_le_gammaCB
    (alpha : Simplex Buffer) (halpha : alpha.IsInterior)
    (U : N.DeterministicPolicySequence)
    (hreturn : UniformHalfReturn N alpha U) :
    PaperStatements.negativeLiminfLogRate
        (N.minimumInvariantLossFamily U) <=
      PaperStatements.Network.gammaCB (N := N) alpha := by
  apply N.negativeLiminfLogRate_le_gammaCB_of_nearAlpha_atoms
    alpha halpha U
  intro epsilon hepsilon
  exact hreturn.eventually_nearAlpha_polynomial_atom
    N alpha U epsilon hepsilon

theorem fluidRestingPointStatement_of_negativeDriftUniformHalfReturn
    (hreturn : NegativeDriftUniformHalfReturnStatement N) :
    PaperStatements.FluidRestingPointStatement N := by
  intro alpha halpha U hnegative
  exact
    (hreturn alpha halpha U hnegative).negativeLiminfLogRate_le_gammaCB
      N alpha halpha U

/-- The unconditional concrete fluid-resting converse. Its loss family is
the actual minimum invariant loss of the finite randomized queue chain. -/
theorem fluidRestingPointStatement :
    PaperStatements.FluidRestingPointStatement N :=
  fluidRestingPointStatement_of_negativeDriftUniformHalfReturn
    N (negativeDriftUniformHalfReturnStatement N)

end

end Network

end StateDepMOR
