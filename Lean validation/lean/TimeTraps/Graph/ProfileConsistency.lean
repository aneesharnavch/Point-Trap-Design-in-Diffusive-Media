module

public import TimeTraps.Graph.ProfileMinimum
public import TimeTraps.Graph.SourceCoordinates
public import TimeTraps.Interval.ConstantCell

@[expose] public section

/-!
The actual profile minimizer and minimum recover the constant-medium graph
constants. Constancy is assumed only on the unit source interval. The
metric-graph specialization uses the existing physical source-weight
identity, so its mass and resistance are the original edge quantities.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Interval

theorem profile_primitive_constant (W : CellWeight) {C α : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hα : α ∈ Icc 0 1) :
    W.primitive α = C * α := by
  unfold CellWeight.primitive
  calc
    _ = ∫ _z in (0 : ℝ)..α, C := by
      apply intervalIntegral.integral_congr_Ioo_of_le hα.1
      intro z hz
      exact hC z ⟨hz.1.le, hz.2.le.trans hα.2⟩
    _ = _ := by simp [mul_comm]

theorem profile_moment_constant (W : CellWeight) {C α : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hα : α ∈ Icc 0 1) :
    W.moment α = C * α ^ 2 / 2 := by
  have h := W.leftRise_constant hC (α := 0) (c := α) le_rfl hα.2 hα.1
  simpa only [CellWeight.leftRise, CellWeight.moment, sub_zero] using h

theorem profileSlope_constant (W : CellWeight) {C α : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hα : α ∈ Icc 0 1) :
    profileSlope W α = C * (3 * α - 3 / 2) := by
  rw [profileSlope, profile_primitive_constant W hC hα,
    profile_primitive_constant W hC ⟨zero_le_one, le_rfl⟩,
    profile_moment_constant W hC ⟨zero_le_one, le_rfl⟩]
  ring

theorem profileCost_constant (W : CellWeight) (m : ℝ) {C α : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) (hα : α ∈ Icc 0 1) :
    profileCost W m α = m * C / 2 * (α ^ 3 + (1 - α) ^ 3) := by
  rw [profileCost, W.rightRise_constant hC le_rfl hα.2 hα.1,
    W.leftRise_constant hC hα.1 le_rfl hα.2]
  ring

theorem profileMinimizer_constant (W : CellWeight) {C : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) : profileMinimizer W = 1 / 2 := by
  apply (profileSlope_strictMono W).injOn
    (Ioo_subset_Icc_self (profileMinimizer_mem W)) (by constructor <;> norm_num)
  rw [profileMinimizer_slope, profileSlope_constant W hC (by constructor <;> norm_num)]
  ring

theorem profileMinimum_constant (W : CellWeight) (m : ℝ) {C : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) :
    profileMinimum W m = m * C / 8 := by
  rw [profileMinimum, profileMinimizer_constant W hC,
    profileCost_constant W m hC (by constructor <;> norm_num)]
  ring

theorem profileCost_constant_endpoints (W : CellWeight) (m : ℝ) {C : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C) :
    profileCost W m 0 = m * C / 2 ∧ profileCost W m 1 = m * C / 2 := by
  rw [profileCost_constant W m hC ⟨le_rfl, zero_le_one⟩,
    profileCost_constant W m hC ⟨zero_le_one, le_rfl⟩]
  constructor <;> ring

variable {V E : Type*}

noncomputable def MetricGraph.profileWeight (G : MetricGraph V E) (e : E) : CellWeight where
  value := G.sourceWeight e
  continuous := (G.sourceWeight_continuous e).continuousOn
  positive := fun z _ => G.sourceWeight_pos e z

theorem MetricGraph.profileWeight_value (G : MetricGraph V E) (e : E) (z : ℝ) :
    (G.profileWeight e).value z = G.sourceWeight e z := rfl

theorem EdgeConstants.profileMinimizer_eq_half {G : MetricGraph V E}
    (c : EdgeConstants G) (e : E) : profileMinimizer (G.profileWeight e) = 1 / 2 :=
  profileMinimizer_constant (G.profileWeight e) (fun z _ => c.sourceWeight_eq e z)

theorem EdgeConstants.profileMinimum_eq {G : MetricGraph V E}
    (c : EdgeConstants G) (e : E) :
    profileMinimum (G.profileWeight e) (G.edgeMass e) =
      G.edgeMass e ^ 2 * G.resistance e / 8 := by
  rw [profileMinimum_constant (G.profileWeight e) (G.edgeMass e)
    (fun z _ => c.sourceWeight_eq e z)]
  ring

theorem EdgeConstants.profileCost_endpoints {G : MetricGraph V E}
    (c : EdgeConstants G) (e : E) :
    profileCost (G.profileWeight e) (G.edgeMass e) 0 = G.edgeMass e ^ 2 * G.resistance e / 2 ∧
    profileCost (G.profileWeight e) (G.edgeMass e) 1 = G.edgeMass e ^ 2 * G.resistance e / 2 := by
  have h := profileCost_constant_endpoints (G.profileWeight e) (G.edgeMass e)
    (fun z _ => c.sourceWeight_eq e z)
  constructor
  · rw [h.1]
    ring
  · rw [h.2]
    ring

end TimeTraps.Graph
