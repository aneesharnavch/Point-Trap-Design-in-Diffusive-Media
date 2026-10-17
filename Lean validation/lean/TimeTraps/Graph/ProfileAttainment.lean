module

public import TimeTraps.Graph.ProfileBarrier

@[expose] public section

/-!
Constructive local sharpness for the variable-profile cost. The canonical
deficit is defined by the actual primitive and first moment. It solves the
source-coordinate equation, is nonnegative on the physical unit interval,
vanishes only at the unique minimizing flux level, and attains the sharp
integral cost. Only continuity and positivity of the weight are used.
-/

namespace TimeTraps.Graph

open Set TimeTraps.Analysis TimeTraps.Interval

noncomputable def profileAttainingDeficit (W : CellWeight) (z : ℝ) : ℝ :=
  W.moment z - W.moment (profileMinimizer W) -
    profileMinimizer W * (W.primitive z - W.primitive (profileMinimizer W))

theorem profileAttainingDeficit_continuous (W : CellWeight) :
    ContinuousOn (profileAttainingDeficit W) (Icc 0 1) :=
  (W.moment_continuous.sub continuousOn_const).sub
    (continuousOn_const.mul (W.primitive_continuous.sub continuousOn_const))

theorem profileAttainingDeficit_hasDerivAt (W : CellWeight) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (profileAttainingDeficit W) (W.value z * (z - profileMinimizer W)) z := by
  have hm : HasDerivAt W.moment (W.value z * z) z :=
    integral_primitive_hasDerivAt (W.continuous.mul continuousOn_id) hz
  have hp : HasDerivAt W.primitive (W.value z) z :=
    integral_primitive_hasDerivAt W.continuous hz
  have hd := (hm.sub_const (W.moment (profileMinimizer W))).sub
    ((hp.sub_const (W.primitive (profileMinimizer W))).const_mul (profileMinimizer W))
  change HasDerivAt (fun x => W.moment x - W.moment (profileMinimizer W) -
    profileMinimizer W * (W.primitive x - W.primitive (profileMinimizer W)))
      (W.value z * (z - profileMinimizer W)) z
  convert hd using 1 <;> first | rfl | ring

theorem profileAttainingDeficit_equation (W : CellWeight) :
    ProfileEquation W (profileMinimizer W) (profileAttainingDeficit W) :=
  ⟨profileAttainingDeficit_continuous W,
    fun _ hz => profileAttainingDeficit_hasDerivAt W hz⟩

theorem profileAttainingDeficit_at_minimizer (W : CellWeight) :
    profileAttainingDeficit W (profileMinimizer W) = 0 := by
  unfold profileAttainingDeficit
  ring

theorem profileAttainingDeficit_eq_leftRise (W : CellWeight) {z : ℝ} (hz : z ∈ Icc 0 1) :
    profileAttainingDeficit W z = W.leftRise (profileMinimizer W) z := by
  rw [W.leftRise_formula (Ioo_subset_Icc_self (profileMinimizer_mem W)) hz]
  rfl

theorem profileAttainingDeficit_eq_rightRise (W : CellWeight) {z : ℝ} (hz : z ∈ Icc 0 1) :
    profileAttainingDeficit W z = W.rightRise (profileMinimizer W) z := by
  rw [W.rightRise_formula (Ioo_subset_Icc_self (profileMinimizer_mem W)) hz]
  unfold profileAttainingDeficit
  ring

theorem profileAttainingDeficit_pos_of_ne (W : CellWeight) {z : ℝ} (hz : z ∈ Icc 0 1)
    (hne : z ≠ profileMinimizer W) : 0 < profileAttainingDeficit W z := by
  have hstar := profileMinimizer_mem W
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [profileAttainingDeficit_eq_rightRise W hz]
    exact W.rightRise_pos hz.1 hstar.2.le hlt
  · rw [profileAttainingDeficit_eq_leftRise W hz]
    exact W.leftRise_pos hstar.1.le hz.2 hgt

theorem profileAttainingDeficit_nonneg (W : CellWeight) (z : ℝ) (hz : z ∈ Icc 0 1) :
    0 ≤ profileAttainingDeficit W z := by
  by_cases he : z = profileMinimizer W
  · rw [he, profileAttainingDeficit_at_minimizer]
  · exact (profileAttainingDeficit_pos_of_ne W hz he).le

theorem profileAttainingDeficit_zero_iff (W : CellWeight) {z : ℝ} (hz : z ∈ Icc 0 1) :
    profileAttainingDeficit W z = 0 ↔ z = profileMinimizer W := by
  constructor
  · intro he
    by_contra hne
    exact (profileAttainingDeficit_pos_of_ne W hz hne).ne' he
  · rintro rfl
    exact profileAttainingDeficit_at_minimizer W

theorem profileAttainingDeficit_cost (W : CellWeight) {m : ℝ} (hm : 0 < m) :
    profileIntegralCost W m (profileMinimizer W) (profileAttainingDeficit W) =
      profileMinimum W m :=
  ((profileAttainingDeficit_equation W).cost_eq_minimum_iff hm
    (profileAttainingDeficit_nonneg W)).mpr ⟨rfl, profileAttainingDeficit_at_minimizer W⟩

theorem profileMinimum_attained (W : CellWeight) {m : ℝ} (hm : 0 < m) :
    ∃ y : ℝ → ℝ, ProfileEquation W (profileMinimizer W) y ∧
      (∀ z ∈ Icc (0 : ℝ) 1, 0 ≤ y z) ∧
      profileIntegralCost W m (profileMinimizer W) y = profileMinimum W m :=
  ⟨profileAttainingDeficit W, profileAttainingDeficit_equation W,
    profileAttainingDeficit_nonneg W, profileAttainingDeficit_cost W hm⟩

end TimeTraps.Graph
