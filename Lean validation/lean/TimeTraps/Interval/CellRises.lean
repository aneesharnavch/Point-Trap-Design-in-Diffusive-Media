module

public import TimeTraps.Analysis.SourceTransport

@[expose] public section

/-!
The two physical height-rise integrals in a source-coordinate cell. The
weight is only assumed positive and continuous on the unit interval. All
cell endpoints and trial sites are real; zero-length cells are permitted
where no strict inequality is asserted.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis

structure CellWeight where
  value : ℝ → ℝ
  continuous : ContinuousOn value (Icc 0 1)
  positive : ∀ x ∈ Icc 0 1, 0 < value x

noncomputable def CellWeight.ofSource (P : SourceInterval) (a : ℝ → ℝ)
    (ha : ContinuousOn a (Icc P.left P.right))
    (hapos : ∀ x ∈ Icc P.left P.right, 0 < a x) : CellWeight where
  value := P.weight a
  continuous := (P.weight_continuous ha hapos).continuousOn
  positive := fun x _ => P.weight_pos hapos x

def CellWeight.sourceInterval (W : CellWeight) : SourceInterval where
  left := 0
  right := 1
  increasing := zero_lt_one
  density := W.value
  continuous := W.continuous
  positive := W.positive

noncomputable def CellWeight.primitive (W : CellWeight) (x : ℝ) : ℝ :=
  ∫ s in 0..x, W.value s

noncomputable def CellWeight.moment (W : CellWeight) (x : ℝ) : ℝ :=
  ∫ s in 0..x, W.value s * s

noncomputable def CellWeight.leftRise (W : CellWeight) (α c : ℝ) : ℝ :=
  ∫ s in α..c, W.value s * (s - α)

noncomputable def CellWeight.rightRise (W : CellWeight) (β c : ℝ) : ℝ :=
  ∫ s in c..β, W.value s * (β - s)

theorem CellWeight.integrable (W : CellWeight) {x y : ℝ} (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    IntervalIntegrable W.value volume x y :=
  (W.continuous.mono (uIcc_subset_Icc hx hy)).intervalIntegrable

theorem CellWeight.moment_integrable (W : CellWeight) {x y : ℝ}
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    IntervalIntegrable (fun s => W.value s * s) volume x y :=
  ((W.continuous.mul continuousOn_id).mono (uIcc_subset_Icc hx hy)).intervalIntegrable

theorem CellWeight.integral_eq_primitive (W : CellWeight) {x y : ℝ}
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    (∫ s in x..y, W.value s) = W.primitive y - W.primitive x :=
  (intervalIntegral.integral_interval_sub_left
    (W.integrable ⟨le_rfl, zero_le_one⟩ hy) (W.integrable ⟨le_rfl, zero_le_one⟩ hx)).symm

theorem CellWeight.integral_eq_moment (W : CellWeight) {x y : ℝ}
    (hx : x ∈ Icc 0 1) (hy : y ∈ Icc 0 1) :
    (∫ s in x..y, W.value s * s) = W.moment y - W.moment x :=
  (intervalIntegral.integral_interval_sub_left
    (W.moment_integrable ⟨le_rfl, zero_le_one⟩ hy)
    (W.moment_integrable ⟨le_rfl, zero_le_one⟩ hx)).symm

theorem CellWeight.primitive_continuous (W : CellWeight) : ContinuousOn W.primitive (Icc 0 1) :=
  integral_primitive_continuousOn zero_le_one W.continuous

theorem CellWeight.moment_continuous (W : CellWeight) : ContinuousOn W.moment (Icc 0 1) :=
  integral_primitive_continuousOn zero_le_one (W.continuous.mul continuousOn_id)

theorem CellWeight.leftRise_formula (W : CellWeight) {α c : ℝ}
    (hα : α ∈ Icc 0 1) (hc : c ∈ Icc 0 1) :
    W.leftRise α c = W.moment c - W.moment α - α * (W.primitive c - W.primitive α) := by
  have hi := W.integrable hα hc
  have hm := W.moment_integrable hα hc
  calc
    _ = ∫ s in α..c, (W.value s * s - α * W.value s) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub hm (hi.const_mul α), intervalIntegral.integral_const_mul,
        W.integral_eq_primitive hα hc, W.integral_eq_moment hα hc]

theorem CellWeight.rightRise_formula (W : CellWeight) {β c : ℝ}
    (hβ : β ∈ Icc 0 1) (hc : c ∈ Icc 0 1) :
    W.rightRise β c = β * (W.primitive β - W.primitive c) - (W.moment β - W.moment c) := by
  have hi := W.integrable hc hβ
  have hm := W.moment_integrable hc hβ
  calc
    _ = ∫ s in c..β, (β * W.value s - W.value s * s) := by
      apply intervalIntegral.integral_congr
      intro s _
      dsimp only
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (hi.const_mul β) hm, intervalIntegral.integral_const_mul,
        W.integral_eq_primitive hc hβ, W.integral_eq_moment hc hβ]

theorem CellWeight.leftRise_self (W : CellWeight) (α : ℝ) : W.leftRise α α = 0 := by
  simp [CellWeight.leftRise]

theorem CellWeight.rightRise_self (W : CellWeight) (β : ℝ) : W.rightRise β β = 0 := by
  simp [CellWeight.rightRise]

theorem CellWeight.leftRise_continuous (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) : ContinuousOn (W.leftRise α) (Icc α β) :=
  integral_primitive_continuousOn hab
    ((W.continuous.mul (continuousOn_id.sub continuousOn_const)).mono (Icc_subset_Icc hα hβ))

theorem CellWeight.rightRise_continuous (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) : ContinuousOn (W.rightRise β) (Icc α β) := by
  have hc : ContinuousOn (fun s => W.value s * (β - s)) (Icc α β) :=
    (W.continuous.mul (continuousOn_const.sub continuousOn_id)).mono (Icc_subset_Icc hα hβ)
  have hi : IntegrableOn (fun s => W.value s * (β - s)) (uIcc α β) volume := by
    rw [uIcc_of_le hab]
    exact hc.integrableOn_Icc
  change ContinuousOn (fun c => ∫ s in c..β, W.value s * (β - s)) (Icc α β)
  simpa only [uIcc_of_le hab] using
    intervalIntegral.continuousOn_primitive_interval_left hi

theorem CellWeight.leftRise_derivative (W : CellWeight) {α β c : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hc : c ∈ Ioo α β) :
    HasDerivAt (W.leftRise α) (W.value c * (c - α)) c :=
  integral_primitive_hasDerivAt
    ((W.continuous.mul (continuousOn_id.sub continuousOn_const)).mono (Icc_subset_Icc hα hβ)) hc

theorem CellWeight.rightRise_derivative (W : CellWeight) {α β c : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hc : c ∈ Ioo α β) :
    HasDerivAt (W.rightRise β) (-(W.value c * (β - c))) c := by
  have hw : ContinuousOn (fun s => W.value s * (β - s)) (Icc α β) :=
    (W.continuous.mul (continuousOn_const.sub continuousOn_id)).mono (Icc_subset_Icc hα hβ)
  have hi : IntervalIntegrable (fun s => W.value s * (β - s)) volume c β :=
    (hw.mono (Icc_subset_Icc hc.1.le le_rfl)).intervalIntegrable_of_Icc hc.2.le
  have ho := hw.mono Ioo_subset_Icc_self
  exact intervalIntegral.integral_hasDerivAt_left hi
    (ho.stronglyMeasurableAtFilter isOpen_Ioo c hc) (ho.continuousAt (isOpen_Ioo.mem_nhds hc))

theorem CellWeight.leftRise_strictMono (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) : StrictMonoOn (W.leftRise α) (Icc α β) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc α β) (W.leftRise_continuous hα hβ hab)
  intro c hc
  rw [interior_Icc] at hc
  rw [(W.leftRise_derivative hα hβ hc).deriv]
  exact mul_pos (W.positive c ⟨hα.trans hc.1.le, hc.2.le.trans hβ⟩) (sub_pos.mpr hc.1)

theorem CellWeight.rightRise_strictAnti (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) : StrictAntiOn (W.rightRise β) (Icc α β) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc α β) (W.rightRise_continuous hα hβ hab)
  intro c hc
  rw [interior_Icc] at hc
  rw [(W.rightRise_derivative hα hβ hc).deriv]
  exact neg_neg_of_pos (mul_pos (W.positive c ⟨hα.trans hc.1.le, hc.2.le.trans hβ⟩) (sub_pos.mpr hc.2))

theorem CellWeight.leftRise_pos (W : CellWeight) {α c : ℝ}
    (hα : 0 ≤ α) (hc : c ≤ 1) (hac : α < c) : 0 < W.leftRise α c := by
  simpa only [W.leftRise_self] using
    W.leftRise_strictMono hα hc hac.le ⟨le_rfl, hac.le⟩ ⟨hac.le, le_rfl⟩ hac

theorem CellWeight.rightRise_pos (W : CellWeight) {c β : ℝ}
    (hc : 0 ≤ c) (hβ : β ≤ 1) (hcb : c < β) : 0 < W.rightRise β c := by
  simpa only [W.rightRise_self] using
    W.rightRise_strictAnti hc hβ hcb.le ⟨le_rfl, hcb.le⟩ ⟨hcb.le, le_rfl⟩ hcb

theorem CellWeight.rise_difference_strictMono (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    StrictMonoOn (fun c => W.leftRise α c - W.rightRise β c) (Icc α β) := by
  intro x hx y hy hxy
  have hl := W.leftRise_strictMono hα hβ hab hx hy hxy
  have hr := W.rightRise_strictAnti hα hβ hab hx hy hxy
  linarith

end TimeTraps.Interval
