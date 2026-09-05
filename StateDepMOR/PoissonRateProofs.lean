import StateDepMOR.LargeDeviations
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Elementary properties of the Poisson rate

Checked facts about the scalar relative-entropy integrand used by the path
rate and the finite-dimensional variational arguments.
-/

open scoped BigOperators ENNReal

namespace StateDepMOR

/-- The finite real-valued Poisson cost when the nominal rate is positive. -/
noncomputable def poissonCostReal (nominal candidate : ℝ) : ℝ :=
  candidate * Real.log (candidate / nominal) - candidate + nominal

theorem poissonCostReal_nonneg
    {nominal candidate : ℝ} (hn : 0 < nominal) (hc : 0 ≤ candidate) :
    0 ≤ poissonCostReal nominal candidate := by
  rcases hc.eq_or_lt with rfl | hc
  · simp [poissonCostReal, hn.le]
  · let r := candidate / nominal
    have hr : 0 ≤ r := (div_pos hc hn).le
    have hbasic : r - 1 ≤ r * Real.log r :=
      Real.self_sub_one_le_mul_log hr
    have hnom_nonneg : 0 ≤ nominal := hn.le
    have hscaled := mul_le_mul_of_nonneg_left hbasic hnom_nonneg
    have hr_eq : nominal * r = candidate := by
      dsimp [r]
      field_simp
    rw [mul_sub, hr_eq, mul_one] at hscaled
    have hlog :
        nominal * (r * Real.log r) =
          candidate * Real.log (candidate / nominal) := by
      rw [← mul_assoc, hr_eq]
    rw [hlog] at hscaled
    dsimp [poissonCostReal]
    linarith

theorem poissonCostReal_eq_zero_iff
    {nominal candidate : ℝ} (hn : 0 < nominal) (hc : 0 ≤ candidate) :
    poissonCostReal nominal candidate = 0 ↔ candidate = nominal := by
  constructor
  · intro hzero
    rcases hc.eq_or_lt with rfl | hc
    · simp [poissonCostReal, hn.ne'] at hzero
    · by_contra hne
      let r := candidate / nominal
      have hr : 0 ≤ r := (div_pos hc hn).le
      have hr_ne : r ≠ 1 := by
        intro hr_one
        apply hne
        dsimp [r] at hr_one
        exact (div_eq_one_iff_eq hn.ne').mp hr_one
      have hbasic : r - 1 < r * Real.log r :=
        Real.self_sub_one_lt_mul_log hr hr_ne
      have hscaled := mul_lt_mul_of_pos_left hbasic hn
      have hr_eq : nominal * r = candidate := by
        dsimp [r]
        field_simp
      rw [mul_sub, hr_eq, mul_one] at hscaled
      have hlog :
          nominal * (r * Real.log r) =
            candidate * Real.log (candidate / nominal) := by
        rw [← mul_assoc, hr_eq]
      rw [hlog] at hscaled
      have : 0 < poissonCostReal nominal candidate := by
        dsimp [poissonCostReal]
        linarith
      exact this.ne' hzero
  · rintro rfl
    simp [poissonCostReal, hn.ne']

theorem poissonCost_nonneg (nominal candidate : ℝ) :
    0 ≤ poissonCost nominal candidate := by
  exact bot_le

theorem poissonCost_eq_zero_iff
    {nominal candidate : ℝ} (hn : 0 ≤ nominal) :
    poissonCost nominal candidate = 0 ↔ candidate = nominal := by
  rcases hn.eq_or_lt with rfl | hn
  · by_cases hcneg : candidate < 0
    · simp [poissonCost, hcneg, ne_of_lt hcneg]
    · by_cases hczero : candidate = 0
      · simp [poissonCost, hczero]
      · simp [poissonCost, hcneg, hczero]
  · by_cases hcneg : candidate < 0
    · simp [poissonCost, hcneg, ne_of_lt (hcneg.trans hn)]
    · have hc : 0 ≤ candidate := le_of_not_gt hcneg
      rw [poissonCost_of_nominal_pos hn hc]
      rw [ENNReal.ofReal_eq_zero]
      constructor
      · intro h
        change poissonCostReal nominal candidate ≤ 0 at h
        exact (poissonCostReal_eq_zero_iff hn hc).mp
          (le_antisymm h (poissonCostReal_nonneg hn hc))
      · rintro rfl
        simp [hn.ne']

/-- At zero nominal rate, finite cost is possible only at candidate rate
zero. -/
theorem poissonCost_zero_ne_top_iff (candidate : Real) :
    poissonCost 0 candidate ≠ (⊤ : ENNReal) <-> candidate = 0 := by
  by_cases hneg : candidate < 0
  · simp [poissonCost, hneg, ne_of_lt hneg]
  · simp [poissonCost, hneg]

namespace Network

universe u v

variable {Buffer : Type u} {Server : Type v}
variable [Fintype Buffer] [Fintype Server]

theorem localRate_nonneg (N : Network Buffer Server)
    (f : Server → Buffer → ℝ) :
    0 ≤ N.localRate f :=
  bot_le

theorem localRate_phi (N : Network Buffer Server) :
    N.localRate N.phi = 0 := by
  classical
  simp only [localRate, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies]
  intro j k
  exact (poissonCost_eq_zero_iff (N.phi_nonneg j k)).2 rfl

/-- The nominal linear input path has zero sample-path action. -/
theorem poissonPathRate_nominalPath
    (N : Network Buffer Server) (T : Real) :
    poissonPathRate N T (fun t j k => N.phi j k * t) = 0 := by
  have hpath :
      (fun t j k => N.phi j k * t) = linearMatrixPath N.phi := by
    funext t j k
    simp [linearMatrixPath, mul_comm]
  rw [hpath, poissonPathRate_linearMatrixPath, N.localRate_phi, zero_mul]

theorem localRate_eq_zero_iff (N : Network Buffer Server)
    (f : Server → Buffer → ℝ) :
    N.localRate f = 0 ↔ f = N.phi := by
  classical
  constructor
  · intro h
    rw [localRate] at h
    funext j k
    have hj :
        ∑ k, poissonCost (N.phi j k) (f j k) = 0 := by
      exact (Finset.sum_eq_zero_iff.mp h) j (Finset.mem_univ j)
    have hjk : poissonCost (N.phi j k) (f j k) = 0 := by
      exact (Finset.sum_eq_zero_iff.mp hj) k (Finset.mem_univ k)
    exact (poissonCost_eq_zero_iff (N.phi_nonneg j k)).1 hjk
  · rintro rfl
    exact N.localRate_phi

/-- Finite local action respects every zero in the support of the nominal
service-token matrix. -/
theorem localRate_ne_top_implies_zero_of_phi_eq_zero
    (N : Network Buffer Server) (f : Server -> Buffer -> Real)
    (hfinite : N.localRate f ≠ (⊤ : ENNReal))
    (j : Server) (k : Buffer) (hphi : N.phi j k = 0) :
    f j k = 0 := by
  rw [Network.localRate, ENNReal.sum_ne_top] at hfinite
  have hj := hfinite j (Finset.mem_univ j)
  rw [ENNReal.sum_ne_top] at hj
  have hjk := hj k (Finset.mem_univ k)
  rw [hphi] at hjk
  exact (poissonCost_zero_ne_top_iff (f j k)).mp hjk

end Network

end StateDepMOR
