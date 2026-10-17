module

public import TimeTraps.Graph.ProfileMinimum
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
The manuscript's asymmetric example, with source profile Ω(q) = 1 + q and
mass one. The stated integral and cost polynomials and the actual unique
minimizer are proved exactly. The minimum is the exact radical obtained by
substituting that minimizer into the displayed cost polynomial. No decimal
approximation is used in a proof.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Interval

def profileExampleWeight : CellWeight where
  value := fun q => 1 + q
  continuous := (continuous_const.add continuous_id).continuousOn
  positive := fun q hq => by linarith [hq.1]

theorem profileExample_primitive (z : ℝ) :
    profileExampleWeight.primitive z = z + z ^ 2 / 2 := by
  change (∫ q in (0 : ℝ)..z, 1 + q) = z + z ^ 2 / 2
  have h1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 z :=
    continuous_const.intervalIntegrable 0 z
  have hi : IntervalIntegrable (fun q : ℝ => q) volume 0 z :=
    continuous_id.intervalIntegrable 0 z
  rw [intervalIntegral.integral_add h1 hi, intervalIntegral.integral_const,
    integral_id]
  norm_num

theorem profileExample_moment (z : ℝ) :
    profileExampleWeight.moment z = z ^ 2 / 2 + z ^ 3 / 3 := by
  change (∫ q in (0 : ℝ)..z, (1 + q) * q) = z ^ 2 / 2 + z ^ 3 / 3
  have hi : IntervalIntegrable (fun q : ℝ => q) volume 0 z :=
    continuous_id.intervalIntegrable 0 z
  have hsq : IntervalIntegrable (fun q : ℝ => q ^ 2) volume 0 z :=
    (continuous_id.pow 2).intervalIntegrable 0 z
  calc
    _ = ∫ q in (0 : ℝ)..z, q + q ^ 2 := by
      apply intervalIntegral.integral_congr
      intro q _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add hi hsq, integral_id, integral_pow]
      norm_num

theorem profileExample_left_triangle {α : ℝ} (hα : α ∈ Icc 0 1) :
    profileExampleWeight.rightRise α 0 = α ^ 2 / 2 + α ^ 3 / 6 := by
  rw [profileExampleWeight.rightRise_formula hα ⟨le_rfl, zero_le_one⟩]
  simp only [profileExample_primitive, profileExample_moment]
  ring

theorem profileExample_right_triangle {α : ℝ} (hα : α ∈ Icc 0 1) :
    profileExampleWeight.leftRise α 1 =
      5 / 6 - 3 * α / 2 + α ^ 2 / 2 + α ^ 3 / 6 := by
  rw [profileExampleWeight.leftRise_formula hα ⟨zero_le_one, le_rfl⟩]
  simp only [profileExample_primitive, profileExample_moment]
  ring

theorem profileExample_cost {α : ℝ} (hα : α ∈ Icc 0 1) :
    profileCost profileExampleWeight 1 α =
      5 / 6 - 7 * α / 3 + 2 * α ^ 2 + α ^ 3 / 6 := by
  rw [profileCost, profileExample_left_triangle hα, profileExample_right_triangle hα]
  ring

theorem profileExample_slope (α : ℝ) :
    profileSlope profileExampleWeight α = -7 / 3 + 4 * α + α ^ 2 / 2 := by
  rw [profileSlope]
  simp only [profileExample_primitive, profileExample_moment]
  ring

theorem profileExample_cost_hasDerivAt {α : ℝ} (hα : α ∈ Ioo 0 1) :
    HasDerivAt (profileCost profileExampleWeight 1) (-7 / 3 + 4 * α + α ^ 2 / 2) α := by
  simpa only [profileExample_slope, one_mul] using
    profileCost_hasDerivAt profileExampleWeight 1 hα

noncomputable def profileExampleRoot : ℝ := (-12 + Real.sqrt 186) / 3

theorem profileExampleRoot_mem : profileExampleRoot ∈ Ioo (0 : ℝ) 1 := by
  have hs := Real.sqrt_nonneg (186 : ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 186)
  have hlo : (12 : ℝ) < Real.sqrt 186 := by nlinarith
  have hhi : Real.sqrt 186 < (15 : ℝ) := by nlinarith
  unfold profileExampleRoot
  constructor <;> linarith

theorem profileExampleRoot_equation :
    3 * profileExampleRoot ^ 2 + 24 * profileExampleRoot - 14 = 0 := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 186)
  unfold profileExampleRoot
  nlinarith

theorem profileExample_minimizer :
    profileMinimizer profileExampleWeight = (-12 + Real.sqrt 186) / 3 := by
  change profileMinimizer profileExampleWeight = profileExampleRoot
  apply (profileSlope_strictMono profileExampleWeight).injOn
    (Ioo_subset_Icc_self (profileMinimizer_mem profileExampleWeight))
    (Ioo_subset_Icc_self profileExampleRoot_mem)
  rw [profileMinimizer_slope, profileExample_slope]
  nlinarith [profileExampleRoot_equation]

theorem profileExample_minimizer_gt_half :
    (1 : ℝ) / 2 < profileMinimizer profileExampleWeight := by
  rw [profileExample_minimizer]
  have hs := Real.sqrt_nonneg (186 : ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 186)
  have hbound : (27 : ℝ) / 2 < Real.sqrt 186 := by nlinarith
  linarith

theorem profileExample_minimum :
    profileMinimum profileExampleWeight 1 = 63 / 2 - 62 * Real.sqrt 186 / 27 := by
  rw [profileMinimum, profileExample_cost
    (Ioo_subset_Icc_self (profileMinimizer_mem profileExampleWeight)), profileExample_minimizer]
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 186)
  have hcub : Real.sqrt 186 ^ 3 = 186 * Real.sqrt 186 := by
    calc
      _ = Real.sqrt 186 ^ 2 * Real.sqrt 186 := by ring
      _ = _ := by rw [hsq]
  nlinarith

end TimeTraps.Graph
