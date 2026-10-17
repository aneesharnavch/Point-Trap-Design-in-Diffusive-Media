module

public import TimeTraps.Graph.ProfileMoment
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-!
Strict convexity and the unique actual minimizer of the local profile cost.
The minimizer is first constructed from the continuous slope crossing;
interior derivative signs then prove minimization of the original cost on
the entire closed interval. No differentiability of the profile is assumed.
-/

namespace TimeTraps.Graph

open Set Filter TimeTraps.Interval
open scoped Topology

theorem profileCost_deriv_hasDerivAt (W : CellWeight) (m : ℝ) {α : ℝ}
    (hα : α ∈ Ioo 0 1) :
    HasDerivAt (deriv (profileCost W m)) (m * (W.value α + 2 * W.primitive 1)) α := by
  have he : deriv (profileCost W m) =ᶠ[𝓝 α] (fun x => m * profileSlope W x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hα] with x hx
    exact (profileCost_hasDerivAt W m hx).deriv
  exact ((profileSlope_hasDerivAt W hα).const_mul m).congr_of_eventuallyEq he

theorem profileCost_second_derivative_pos (W : CellWeight) {m α : ℝ}
    (hm : 0 < m) (hα : α ∈ Ioo 0 1) : 0 < deriv (deriv (profileCost W m)) α := by
  rw [(profileCost_deriv_hasDerivAt W m hα).deriv]
  exact mul_pos hm (profileSlope_derivative_pos W hα)

theorem profileCost_strictConvexOn (W : CellWeight) {m : ℝ} (hm : 0 < m) :
    StrictConvexOn ℝ (Icc 0 1) (profileCost W m) := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1) (profileCost_continuous W m)
  intro x hx y hy hxy
  rw [interior_Icc] at hx hy
  rw [(profileCost_hasDerivAt W m hx).deriv, (profileCost_hasDerivAt W m hy).deriv]
  exact mul_lt_mul_of_pos_left
    (profileSlope_strictMono W (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy) hm

theorem profileSlope_zero_existsUnique (W : CellWeight) :
    ∃! α : ℝ, α ∈ Ioo 0 1 ∧ profileSlope W α = 0 := by
  have hs := profileSlope_endpoint_signs W
  obtain ⟨α, hα, he⟩ := intermediate_value_Icc zero_le_one (profileSlope_continuous W)
    ⟨hs.1.le, hs.2.le⟩
  change profileSlope W α = 0 at he
  have hzero : α ≠ 0 := by
    intro hz
    rw [hz] at he
    linarith [hs.1]
  have hone : α ≠ 1 := by
    intro ho
    rw [ho] at he
    linarith [hs.2]
  have hi : α ∈ Ioo 0 1 :=
    ⟨lt_of_le_of_ne hα.1 hzero.symm, lt_of_le_of_ne hα.2 hone⟩
  refine ⟨α, ⟨hi, he⟩, ?_⟩
  intro x hx
  exact (profileSlope_strictMono W).injOn (Ioo_subset_Icc_self hx.1) hα (hx.2.trans he.symm)

noncomputable def profileMinimizer (W : CellWeight) : ℝ :=
  Classical.choose (profileSlope_zero_existsUnique W)

theorem profileMinimizer_mem (W : CellWeight) : profileMinimizer W ∈ Ioo 0 1 :=
  (Classical.choose_spec (profileSlope_zero_existsUnique W)).1.1

theorem profileMinimizer_slope (W : CellWeight) : profileSlope W (profileMinimizer W) = 0 :=
  (Classical.choose_spec (profileSlope_zero_existsUnique W)).1.2

theorem profileMinimizer_equation (W : CellWeight) :
    W.primitive (profileMinimizer W) + (2 * profileMinimizer W - 1) * W.primitive 1 =
      W.moment 1 := by
  have h := profileMinimizer_slope W
  unfold profileSlope at h
  linarith

noncomputable def profileMinimum (W : CellWeight) (m : ℝ) : ℝ :=
  profileCost W m (profileMinimizer W)

theorem profileCost_strictAntiOn_left (W : CellWeight) {m : ℝ} (hm : 0 < m) :
    StrictAntiOn (profileCost W m) (Icc 0 (profileMinimizer W)) := by
  have hstar := profileMinimizer_mem W
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 (profileMinimizer W))
    ((profileCost_continuous W m).mono (Icc_subset_Icc le_rfl hstar.2.le))
  intro α hα
  rw [interior_Icc] at hα
  have hi : α ∈ Ioo 0 1 := ⟨hα.1, hα.2.trans hstar.2⟩
  rw [(profileCost_hasDerivAt W m hi).deriv]
  have hs := profileSlope_strictMono W (Ioo_subset_Icc_self hi)
    (Ioo_subset_Icc_self hstar) hα.2
  rw [profileMinimizer_slope] at hs
  exact mul_neg_of_pos_of_neg hm hs

theorem profileCost_strictMonoOn_right (W : CellWeight) {m : ℝ} (hm : 0 < m) :
    StrictMonoOn (profileCost W m) (Icc (profileMinimizer W) 1) := by
  have hstar := profileMinimizer_mem W
  apply strictMonoOn_of_deriv_pos (convex_Icc (profileMinimizer W) 1)
    ((profileCost_continuous W m).mono (Icc_subset_Icc hstar.1.le le_rfl))
  intro α hα
  rw [interior_Icc] at hα
  have hi : α ∈ Ioo 0 1 := ⟨hstar.1.trans hα.1, hα.2⟩
  rw [(profileCost_hasDerivAt W m hi).deriv]
  have hs := profileSlope_strictMono W (Ioo_subset_Icc_self hstar)
    (Ioo_subset_Icc_self hi) hα.1
  rw [profileMinimizer_slope] at hs
  exact mul_pos hm hs

theorem profileMinimum_lt_cost_of_ne (W : CellWeight) {m α : ℝ} (hm : 0 < m)
    (hα : α ∈ Icc 0 1) (hne : α ≠ profileMinimizer W) :
    profileMinimum W m < profileCost W m α := by
  have hstar := profileMinimizer_mem W
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact profileCost_strictAntiOn_left W hm ⟨hα.1, hlt.le⟩
      ⟨hstar.1.le, le_rfl⟩ hlt
  · exact profileCost_strictMonoOn_right W hm ⟨le_rfl, hstar.2.le⟩
      ⟨hgt.le, hα.2⟩ hgt

theorem profileCost_minimum (W : CellWeight) {m : ℝ} (hm : 0 < m) :
    IsLeast (profileCost W m '' Icc 0 1) (profileMinimum W m) := by
  refine ⟨⟨profileMinimizer W, Ioo_subset_Icc_self (profileMinimizer_mem W), rfl⟩, ?_⟩
  rintro y ⟨α, hα, rfl⟩
  by_cases he : α = profileMinimizer W
  · rw [he]
    exact le_rfl
  · exact (profileMinimum_lt_cost_of_ne W hm hα he).le

theorem profileCost_eq_minimum_iff (W : CellWeight) {m α : ℝ} (hm : 0 < m)
    (hα : α ∈ Icc 0 1) :
    profileCost W m α = profileMinimum W m ↔ α = profileMinimizer W := by
  constructor
  · intro he
    by_contra hne
    exact (profileMinimum_lt_cost_of_ne W hm hα hne).ne' he
  · rintro rfl
    rfl

theorem profileCost_minimizer_existsUnique (W : CellWeight) {m : ℝ} (hm : 0 < m) :
    ∃! α : ℝ, α ∈ Icc 0 1 ∧ ∀ x ∈ Icc 0 1, profileCost W m α ≤ profileCost W m x := by
  have hstar := Ioo_subset_Icc_self (profileMinimizer_mem W)
  refine ⟨profileMinimizer W, ⟨hstar, ?_⟩, ?_⟩
  · intro x hx
    exact (profileCost_minimum W hm).2 ⟨x, hx, rfl⟩
  · intro α hα
    apply (profileCost_eq_minimum_iff W hm hα.1).mp
    exact le_antisymm (hα.2 (profileMinimizer W) hstar)
      ((profileCost_minimum W hm).2 ⟨α, hα.1, rfl⟩)

theorem profileMinimum_pos (W : CellWeight) {m : ℝ} (hm : 0 < m) :
    0 < profileMinimum W m := by
  have hstar := profileMinimizer_mem W
  unfold profileMinimum profileCost
  apply mul_pos hm
  exact add_pos
    (mul_pos hstar.1 (W.rightRise_pos le_rfl hstar.2.le hstar.1))
    (mul_pos (sub_pos.mpr hstar.2) (W.leftRise_pos hstar.1.le le_rfl hstar.2))

end TimeTraps.Graph
