module

public import TimeTraps.Interval.CellRises
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-!
The actual local profile functional from the variable-medium graph bound.
The profile is positive and continuous only on the closed unit interval.
Its cost and slope have continuous endpoint extensions; all ordinary
derivative assertions are restricted to the open unit interval.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval

noncomputable def profileCost (W : CellWeight) (m α : ℝ) : ℝ :=
  m * (α * W.rightRise α 0 + (1 - α) * W.leftRise α 1)

noncomputable def profileSlope (W : CellWeight) (α : ℝ) : ℝ :=
  W.primitive α + (2 * α - 1) * W.primitive 1 - W.moment 1

theorem profile_moment_bounds (W : CellWeight) :
    0 < W.moment 1 ∧ W.moment 1 < W.primitive 1 := by
  have hleft := W.leftRise_pos (α := 0) (c := 1) le_rfl le_rfl zero_lt_one
  have hright := W.rightRise_pos (c := 0) (β := 1) le_rfl le_rfl zero_lt_one
  rw [W.leftRise_formula ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩] at hleft
  rw [W.rightRise_formula ⟨zero_le_one, le_rfl⟩ ⟨le_rfl, zero_le_one⟩] at hright
  have hp : W.primitive 0 = 0 := by simp [CellWeight.primitive]
  have hm : W.moment 0 = 0 := by simp [CellWeight.moment]
  rw [hp, hm] at hleft hright
  constructor <;> linarith

theorem profileCost_formula (W : CellWeight) (m : ℝ) {α : ℝ} (hα : α ∈ Icc 0 1) :
    profileCost W m α = m * (α * W.primitive α - W.moment α +
      (1 - α) * W.moment 1 + (α ^ 2 - α) * W.primitive 1) := by
  rw [profileCost, W.rightRise_formula hα ⟨le_rfl, zero_le_one⟩,
    W.leftRise_formula hα ⟨zero_le_one, le_rfl⟩]
  have hp : W.primitive 0 = 0 := by simp [CellWeight.primitive]
  have hm : W.moment 0 = 0 := by simp [CellWeight.moment]
  rw [hp, hm]
  ring

theorem profileCost_continuous (W : CellWeight) (m : ℝ) :
    ContinuousOn (profileCost W m) (Icc 0 1) := by
  have h : ContinuousOn (fun α : ℝ => m * (α * W.primitive α - W.moment α +
      (1 - α) * W.moment 1 + (α ^ 2 - α) * W.primitive 1)) (Icc 0 1) :=
    continuousOn_const.mul ((((continuousOn_id.mul W.primitive_continuous).sub
      W.moment_continuous).add ((continuousOn_const.sub continuousOn_id).mul
        continuousOn_const)).add (((continuousOn_id.pow 2).sub continuousOn_id).mul
          continuousOn_const))
  exact h.congr (fun α hα => profileCost_formula W m hα)

theorem profileSlope_continuous (W : CellWeight) :
    ContinuousOn (profileSlope W) (Icc 0 1) :=
  (W.primitive_continuous.add (((continuousOn_const.mul continuousOn_id).sub
    continuousOn_const).mul continuousOn_const)).sub continuousOn_const

theorem profileCost_hasDerivAt (W : CellWeight) (m : ℝ) {α : ℝ} (hα : α ∈ Ioo 0 1) :
    HasDerivAt (profileCost W m) (m * profileSlope W α) α := by
  have hp : HasDerivAt W.primitive (W.value α) α :=
    integral_primitive_hasDerivAt W.continuous hα
  have hm : HasDerivAt W.moment (W.value α * α) α :=
    integral_primitive_hasDerivAt (W.continuous.mul continuousOn_id) hα
  have hd := (((((hasDerivAt_id' α).mul hp).sub hm).add
    (((hasDerivAt_id' α).const_sub 1).mul_const (W.moment 1))).add
      ((((hasDerivAt_id' α).pow 2).sub (hasDerivAt_id' α)).mul_const
        (W.primitive 1))).const_mul m
  have he : (fun x : ℝ => m * (x * W.primitive x - W.moment x +
      (1 - x) * W.moment 1 + (x ^ 2 - x) * W.primitive 1)) =ᶠ[nhds α]
      profileCost W m := by
    filter_upwards [isOpen_Ioo.mem_nhds hα] with x hx
    exact (profileCost_formula W m (Ioo_subset_Icc_self hx)).symm
  change HasDerivAt (profileCost W m)
    (m * (W.primitive α + (2 * α - 1) * W.primitive 1 - W.moment 1)) α
  convert hd.congr_of_eventuallyEq he.symm using 1 <;> first | rfl | ring

theorem profileSlope_hasDerivAt (W : CellWeight) {α : ℝ} (hα : α ∈ Ioo 0 1) :
    HasDerivAt (profileSlope W) (W.value α + 2 * W.primitive 1) α := by
  have hp : HasDerivAt W.primitive (W.value α) α :=
    integral_primitive_hasDerivAt W.continuous hα
  have hd := (hp.add ((((hasDerivAt_id' α).const_mul 2).sub_const 1).mul_const
    (W.primitive 1))).sub_const (W.moment 1)
  change HasDerivAt (fun x => W.primitive x + (2 * x - 1) * W.primitive 1 - W.moment 1)
    (W.value α + 2 * W.primitive 1) α
  convert hd using 1 <;> first | rfl | ring

theorem profileSlope_derivative_pos (W : CellWeight) {α : ℝ} (hα : α ∈ Ioo 0 1) :
    0 < W.value α + 2 * W.primitive 1 := by
  have hm := profile_moment_bounds W
  have hv := W.positive α (Ioo_subset_Icc_self hα)
  linarith

theorem profileSlope_strictMono (W : CellWeight) :
    StrictMonoOn (profileSlope W) (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) (profileSlope_continuous W)
  intro α hα
  rw [interior_Icc] at hα
  rw [(profileSlope_hasDerivAt W hα).deriv]
  exact profileSlope_derivative_pos W hα

theorem profileSlope_zero (W : CellWeight) :
    profileSlope W 0 = -W.moment 1 - W.primitive 1 := by
  have hp : W.primitive 0 = 0 := by simp [CellWeight.primitive]
  rw [profileSlope, hp]
  ring

theorem profileSlope_one (W : CellWeight) :
    profileSlope W 1 = 2 * W.primitive 1 - W.moment 1 := by
  unfold profileSlope
  ring

theorem profileSlope_endpoint_signs (W : CellWeight) :
    profileSlope W 0 < 0 ∧ 0 < profileSlope W 1 := by
  rw [profileSlope_zero, profileSlope_one]
  have hm := profile_moment_bounds W
  constructor <;> linarith

theorem profileCost_zero (W : CellWeight) (m : ℝ) :
    profileCost W m 0 = m * W.moment 1 := by
  rw [profileCost_formula W m ⟨le_rfl, zero_le_one⟩]
  have hm : W.moment 0 = 0 := by simp [CellWeight.moment]
  rw [hm]
  ring

theorem profileCost_one (W : CellWeight) (m : ℝ) :
    profileCost W m 1 = m * (W.primitive 1 - W.moment 1) := by
  rw [profileCost_formula W m ⟨zero_le_one, le_rfl⟩]
  ring

end TimeTraps.Graph
