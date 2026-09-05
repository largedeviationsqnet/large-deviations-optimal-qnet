import StateDepMOR.Network

/-!
# Lyapunov function

The paper defines `L_α` on the probability simplex, but later evaluates it at
vectors that need not lie in the simplex.  `LAlphaAmbient` is the explicit
ambient extension to all real vectors; `LAlpha` is its simplex-domain wrapper.
-/

open scoped BigOperators

namespace StateDepMOR

universe u

namespace Lyapunov

variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The minimum coordinate of a vector on a nonempty finite index type. -/
noncomputable def minCoordinate (x : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty x

/-- The maximum coordinatewise distance, i.e. the finite-dimensional
`ℓ∞` distance used in `lem:tech_lems`. -/
noncomputable def maxCoordinateDistance (x y : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |x i - y i|

/-- Ambient extension of the paper's Lyapunov function:
`L_α(x) = 1 - min_i (x_i / α_i)`. -/
noncomputable def LAlphaAmbient (α x : ι → ℝ) : ℝ :=
  1 - minCoordinate fun i => x i / α i

/-- The paper-facing simplex-domain wrapper for `LAlphaAmbient`. -/
noncomputable def LAlpha (α x : Simplex ι) : ℝ :=
  LAlphaAmbient (fun i => α i) fun i => x i

/-- Ambient membership in the probability simplex.  This lets the source
hypotheses be stated without forcing off-simplex expressions into a subtype. -/
def IsSimplexVector (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

/-- Readback of the ambient definition. -/
theorem LAlphaAmbient_readback (α x : ι → ℝ) :
    LAlphaAmbient α x = 1 - Finset.univ.inf' Finset.univ_nonempty
      (fun i => x i / α i) := by
  rfl

/-- Simplex-domain readback of the paper's definition of `L_α`. -/
theorem LAlpha_readback (α x : Simplex ι) :
    LAlpha α x = 1 - Finset.univ.inf' Finset.univ_nonempty
      (fun i => x i / α i) := by
  rfl

private theorem minCoordinate_congr {f g : ι → ℝ}
    (h : ∀ i, f i = g i) :
    minCoordinate f = minCoordinate g := by
  unfold minCoordinate
  apply Finset.inf'_congr Finset.univ_nonempty rfl
  intro i _
  exact h i

private theorem minCoordinate_add_const (a : ℝ) (f : ι → ℝ) :
    minCoordinate (fun i => a + f i) = a + minCoordinate f := by
  unfold minCoordinate
  apply le_antisymm
  · obtain ⟨i, _, hi⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty f
    calc
      minCoordinate (fun j => a + f j) ≤ a + f i := by
        exact Finset.inf'_le _ (Finset.mem_univ i)
      _ = a + Finset.univ.inf' Finset.univ_nonempty f := by rw [← hi]
  · apply Finset.le_inf' Finset.univ_nonempty
    intro i _
    have hi := Finset.inf'_le f (Finset.mem_univ i)
    linarith

private theorem minCoordinate_mul_of_nonneg (c : ℝ) (hc : 0 ≤ c)
    (f : ι → ℝ) :
    minCoordinate (fun i => c * f i) = c * minCoordinate f := by
  unfold minCoordinate
  apply le_antisymm
  · obtain ⟨i, _, hi⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty f
    calc
      minCoordinate (fun j => c * f j) ≤ c * f i := by
        exact Finset.inf'_le _ (Finset.mem_univ i)
      _ = c * Finset.univ.inf' Finset.univ_nonempty f := by rw [← hi]
  · apply Finset.le_inf' Finset.univ_nonempty
    intro i _
    exact mul_le_mul_of_nonneg_left
      (Finset.inf'_le f (Finset.mem_univ i)) hc

private theorem minCoordinate_add_ge (f g : ι → ℝ) :
    minCoordinate f + minCoordinate g ≤ minCoordinate (fun i => f i + g i) := by
  unfold minCoordinate
  apply Finset.le_inf' Finset.univ_nonempty
  intro i _
  exact add_le_add
    (Finset.inf'_le f (Finset.mem_univ i))
    (Finset.inf'_le g (Finset.mem_univ i))

/-- Stronger ambient helper: centering `LAlphaAmbient` at `α` needs only
nonzero coordinates of `α`; no zero-sum or simplex-membership hypothesis is
needed. -/
theorem LAlphaAmbient_centered (α z : ι → ℝ)
    (hα : ∀ i, α i ≠ 0) :
    LAlphaAmbient α (α + z) = -minCoordinate (fun i => z i / α i) := by
  rw [LAlphaAmbient]
  have hmin :
      minCoordinate (fun i => (α + z) i / α i) =
        1 + minCoordinate (fun i => z i / α i) := by
    calc
      minCoordinate (fun i => (α + z) i / α i) =
          minCoordinate (fun i => 1 + z i / α i) := by
            apply minCoordinate_congr
            intro i
            simp only [Pi.add_apply]
            field_simp [hα i]
      _ = 1 + minCoordinate (fun i => z i / α i) :=
        minCoordinate_add_const 1 _
  rw [hmin]
  ring

/-- Stronger ambient version of the scale-invariance part of
`lem:key_property_lyap`. -/
theorem LAlphaAmbient_centered_scale (α z : ι → ℝ) (c : ℝ)
    (hα : ∀ i, α i ≠ 0) (hc : 0 ≤ c) :
    LAlphaAmbient α (α + c • z) = c * LAlphaAmbient α (α + z) := by
  rw [LAlphaAmbient_centered α (c • z) hα,
    LAlphaAmbient_centered α z hα]
  have hmin :
      minCoordinate (fun i => (c • z) i / α i) =
        c * minCoordinate (fun i => z i / α i) := by
    calc
      minCoordinate (fun i => (c • z) i / α i) =
          minCoordinate (fun i => c * (z i / α i)) := by
            apply minCoordinate_congr
            intro i
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
      _ = c * minCoordinate (fun i => z i / α i) :=
        minCoordinate_mul_of_nonneg c hc _
  rw [hmin]
  ring

/-- Stronger ambient version of the subadditivity part of
`lem:key_property_lyap`. -/
theorem LAlphaAmbient_centered_subadditive (α z w : ι → ℝ)
    (hα : ∀ i, α i ≠ 0) :
    LAlphaAmbient α (α + z + w) ≤
      LAlphaAmbient α (α + z) + LAlphaAmbient α (α + w) := by
  rw [show α + z + w = α + (z + w) by abel]
  rw [LAlphaAmbient_centered α (z + w) hα,
    LAlphaAmbient_centered α z hα,
    LAlphaAmbient_centered α w hα]
  have hratio :
      minCoordinate (fun i => z i / α i) +
          minCoordinate (fun i => w i / α i) ≤
        minCoordinate (fun i => (z + w) i / α i) := by
    calc
      minCoordinate (fun i => z i / α i) +
          minCoordinate (fun i => w i / α i) ≤
          minCoordinate (fun i => z i / α i + w i / α i) :=
        minCoordinate_add_ge _ _
      _ = minCoordinate (fun i => (z + w) i / α i) := by
        apply minCoordinate_congr
        intro i
        simp only [Pi.add_apply]
        ring
  linarith

/-- Source `lem:key_property_lyap`, part 1 (centered positive scale
invariance), retaining all hypotheses printed in the paper. -/
theorem LAlpha_centered_scale_invariance
    (α : Simplex ι) (hα : α.IsInterior) (c : ℝ) (hc : 0 < c)
    (Δx : ι → ℝ)
    (_hsum : ∑ i, Δx i = 0)
    (_hmem_one : IsSimplexVector ((fun i => α i) + Δx))
    (_hmem_scaled : IsSimplexVector ((fun i => α i) + c • Δx)) :
    LAlphaAmbient (fun i => α i) ((fun i => α i) + c • Δx) =
      c * LAlphaAmbient (fun i => α i) ((fun i => α i) + Δx) := by
  exact LAlphaAmbient_centered_scale _ _ c
    (fun i => ne_of_gt (hα i)) hc.le

/-- Source `lem:key_property_lyap`, part 2 (centered subadditivity), retaining
all hypotheses printed in the paper. -/
theorem LAlpha_centered_subadditivity
    (α : Simplex ι) (hα : α.IsInterior) (Δx Δx' : ι → ℝ)
    (_hsum : ∑ i, Δx i = 0)
    (_hsum' : ∑ i, Δx' i = 0)
    (_hmem_sum : IsSimplexVector ((fun i => α i) + Δx + Δx'))
    (_hmem : IsSimplexVector ((fun i => α i) + Δx))
    (_hmem' : IsSimplexVector ((fun i => α i) + Δx')) :
    LAlphaAmbient (fun i => α i) ((fun i => α i) + Δx + Δx') ≤
      LAlphaAmbient (fun i => α i) ((fun i => α i) + Δx) +
        LAlphaAmbient (fun i => α i) ((fun i => α i) + Δx') := by
  exact LAlphaAmbient_centered_subadditive _ _ _
    (fun i => ne_of_gt (hα i))

theorem minCoordinate_pos {α : ι → ℝ} (hα : ∀ i, 0 < α i) :
    0 < minCoordinate α := by
  unfold minCoordinate
  rw [Finset.lt_inf'_iff Finset.univ_nonempty]
  intro i _
  exact hα i

theorem coordinate_le_maxCoordinateDistance (x y : ι → ℝ) (i : ι) :
    |x i - y i| ≤ maxCoordinateDistance x y := by
  exact Finset.le_sup' (fun j => |x j - y j|) (Finset.mem_univ i)

private theorem abs_minCoordinate_sub_minCoordinate_le
    (f g : ι → ℝ) (C : ℝ) (hC : ∀ i, |f i - g i| ≤ C) :
    |minCoordinate f - minCoordinate g| ≤ C := by
  rw [abs_sub_le_iff]
  constructor
  · obtain ⟨i, _, hi⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty g
    change minCoordinate g = g i at hi
    apply (sub_le_iff_le_add).2
    calc
      minCoordinate f ≤ f i := Finset.inf'_le f (Finset.mem_univ i)
      _ ≤ g i + C := by
        have hfg : f i - g i ≤ C :=
          (le_abs_self (f i - g i)).trans (hC i)
        linarith
      _ = minCoordinate g + C := by rw [← hi]
      _ = C + minCoordinate g := add_comm _ _
  · obtain ⟨i, _, hi⟩ :=
      Finset.exists_mem_eq_inf' Finset.univ_nonempty f
    change minCoordinate f = f i at hi
    apply (sub_le_iff_le_add).2
    calc
      minCoordinate g ≤ g i := Finset.inf'_le g (Finset.mem_univ i)
      _ ≤ f i + C := by
        have hgf : g i - f i ≤ C := by
          calc
            g i - f i = -(f i - g i) := by ring
            _ ≤ |f i - g i| := neg_le_abs _
            _ ≤ C := hC i
        linarith
      _ = minCoordinate f + C := by rw [← hi]
      _ = C + minCoordinate f := add_comm _ _

/-- Source `lem:tech_lems`, part 1: nonnegativity on the simplex. -/
theorem LAlpha_nonnegative
    (α x : Simplex ι) (hα : α.IsInterior) :
    0 ≤ LAlpha α x := by
  have hexists : ∃ i, x i ≤ α i := by
    by_contra h
    push Not at h
    have hsum :
        (∑ i, α i) < ∑ i, x i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun i _ => h i)
    rw [α.sum_eq_one, x.sum_eq_one] at hsum
    exact lt_irrefl 1 hsum
  obtain ⟨i, hi⟩ := hexists
  rw [LAlpha, LAlphaAmbient]
  have hmin :
      minCoordinate (fun j => x j / α j) ≤ 1 :=
    (Finset.inf'_le (fun j => x j / α j) (Finset.mem_univ i)).trans
      ((div_le_one (hα i)).2 hi)
  linarith

/-- Source `lem:tech_lems`, part 1: `L_α` vanishes exactly at the interior
reference state. -/
theorem LAlpha_eq_zero_iff
    (α x : Simplex ι) (hα : α.IsInterior) :
    LAlpha α x = 0 ↔ x = α := by
  constructor
  · intro hzero
    have hmin :
        minCoordinate (fun i => x i / α i) = 1 := by
      rw [LAlpha, LAlphaAmbient] at hzero
      linarith
    have hle : ∀ i, α i ≤ x i := by
      intro i
      have hone : 1 ≤ x i / α i := by
        rw [← hmin]
        exact Finset.inf'_le _ (Finset.mem_univ i)
      exact (one_le_div₀ (hα i)).1 hone
    apply Simplex.eq_of_apply_eq
    have hsum : (∑ i, α i) = ∑ i, x i := by
      rw [α.sum_eq_one, x.sum_eq_one]
    have hall :
        ∀ i ∈ Finset.univ, α i = x i :=
      (Finset.sum_eq_sum_iff_of_le
        (fun i (_ : i ∈ Finset.univ) => hle i)).1 hsum
    intro i
    exact (hall i (Finset.mem_univ i)).symm
  · intro h
    subst x
    rw [LAlpha, LAlphaAmbient]
    have hratios :
        minCoordinate (fun i => α i / α i) = 1 := by
      calc
        minCoordinate (fun i => α i / α i) =
            minCoordinate (fun _i : ι => 1) := by
          apply minCoordinate_congr
          intro i
          exact div_self (ne_of_gt (hα i))
        _ = 1 := by
          unfold minCoordinate
          exact Finset.inf'_const Finset.univ_nonempty 1
    rw [hratios]
    ring

/-- Source `lem:tech_lems`, part 2: the stated global `ℓ∞` Lipschitz
estimate, written with the equivalent maximum coordinate distance. -/
theorem LAlpha_lipschitz
    (α x y : Simplex ι) (hα : α.IsInterior) :
    |LAlpha α x - LAlpha α y| ≤
      (1 / minCoordinate (fun i => α i)) *
        maxCoordinateDistance (fun i => x i) (fun i => y i) := by
  let m := minCoordinate (fun i => α i)
  let D := maxCoordinateDistance (fun i => x i) (fun i => y i)
  have hm : 0 < m := minCoordinate_pos hα
  have hm_le : ∀ i, m ≤ α i := by
    intro i
    exact Finset.inf'_le (fun j => α j) (Finset.mem_univ i)
  have hD : 0 ≤ D := by
    let i : ι := Classical.choice inferInstance
    exact (abs_nonneg (x i - y i)).trans
      (coordinate_le_maxCoordinateDistance
        (fun j => x j) (fun j => y j) i)
  have hcoord : ∀ i, |x i / α i - y i / α i| ≤ (1 / m) * D := by
    intro i
    calc
      |x i / α i - y i / α i| = |x i - y i| / α i := by
        rw [← sub_div, abs_div, abs_of_pos (hα i)]
      _ ≤ D / α i := div_le_div_of_nonneg_right
        (coordinate_le_maxCoordinateDistance
          (fun j => x j) (fun j => y j) i) (hα i).le
      _ ≤ D / m := div_le_div_of_nonneg_left hD hm (hm_le i)
      _ = (1 / m) * D := by ring
  dsimp [m, D] at hcoord ⊢
  rw [LAlpha, LAlpha, LAlphaAmbient, LAlphaAmbient]
  calc
    |(1 - minCoordinate (fun i => x i / α i)) -
        (1 - minCoordinate (fun i => y i / α i))| =
        |minCoordinate (fun i => x i / α i) -
          minCoordinate (fun i => y i / α i)| := by
      rw [show
        (1 - minCoordinate (fun i => x i / α i)) -
            (1 - minCoordinate (fun i => y i / α i)) =
          minCoordinate (fun i => y i / α i) -
            minCoordinate (fun i => x i / α i) by ring]
      exact abs_sub_comm _ _
    _ ≤ (1 / minCoordinate (fun i => α i)) *
        maxCoordinateDistance (fun i => x i) (fun i => y i) :=
      abs_minCoordinate_sub_minCoordinate_le
      (fun i => x i / α i) (fun i => y i / α i)
        ((1 / minCoordinate (fun i => α i)) *
          maxCoordinateDistance (fun i => x i) (fun i => y i)) hcoord

end Lyapunov

end StateDepMOR
