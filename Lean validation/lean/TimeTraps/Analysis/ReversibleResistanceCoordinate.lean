module

public import TimeTraps.Interval.StrictPartition

@[expose] public section

/-! The actual resistance coordinate for continuous positive conductance.
The physical interval and speed density remain those of `IntervalMedium`.
No derivative of the conductance or normalization of the speed mass is used. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis

noncomputable def IntervalMedium.resistanceSource (A : IntervalMedium) : SourceInterval where
  left := A.source.left
  right := A.source.right
  increasing := A.source.increasing
  density := fun x => 1 / A.conductance x
  continuous := continuousOn_const.div A.conductance_continuous
    (fun x hx => ne_of_gt (A.conductance_pos x hx))
  positive := fun x hx => one_div_pos.mpr (A.conductance_pos x hx)

noncomputable def IntervalMedium.resistanceLength (A : IntervalMedium) : ℝ :=
  A.resistanceSource.mass

noncomputable def IntervalMedium.resistance (A : IntervalMedium) (x : ℝ) : ℝ :=
  ∫ y in A.source.left..x, 1 / A.conductance y

theorem IntervalMedium.resistanceLength_pos (A : IntervalMedium) : 0 < A.resistanceLength :=
  A.resistanceSource.mass_pos

theorem IntervalMedium.resistance_eq (A : IntervalMedium) (x : ℝ) :
    A.resistance x = A.resistanceLength * A.resistanceSource.coordinate x := by
  exact A.resistanceSource.sourcePrimitive_eq x

theorem IntervalMedium.resistance_left (A : IntervalMedium) :
    A.resistance A.source.left = 0 := by
  simp only [IntervalMedium.resistance, intervalIntegral.integral_same]

theorem IntervalMedium.resistance_right (A : IntervalMedium) :
    A.resistance A.source.right = A.resistanceLength := rfl

theorem IntervalMedium.resistance_continuous (A : IntervalMedium) :
    ContinuousOn A.resistance (Icc A.source.left A.source.right) :=
  integral_primitive_continuousOn A.source.increasing.le A.resistanceSource.continuous

theorem IntervalMedium.resistance_strictMono (A : IntervalMedium) :
    StrictMonoOn A.resistance (Icc A.source.left A.source.right) := by
  intro x hx y hy hxy
  rw [A.resistance_eq, A.resistance_eq]
  exact mul_lt_mul_of_pos_left (A.resistanceSource.coordinate_strictMono hx hy hxy)
    A.resistanceLength_pos

theorem IntervalMedium.resistance_image (A : IntervalMedium) :
    A.resistance '' Icc A.source.left A.source.right = Icc 0 A.resistanceLength := by
  simpa only [A.resistance_left, A.resistance_right] using
    A.resistance_continuous.image_Icc_of_monotoneOn A.source.increasing.le
      A.resistance_strictMono.monotoneOn

theorem IntervalMedium.resistance_mem (A : IntervalMedium) {x : ℝ}
    (hx : x ∈ Icc A.source.left A.source.right) :
    A.resistance x ∈ Icc 0 A.resistanceLength := by
  rw [← A.resistance_image]
  exact mem_image_of_mem _ hx

noncomputable def IntervalMedium.resistanceOrderIso (A : IntervalMedium) :
    Icc A.source.left A.source.right ≃o Icc 0 A.resistanceLength :=
  (A.resistance_strictMono.orderIso A.resistance (Icc A.source.left A.source.right)).trans
    (OrderIso.setCongr _ _ A.resistance_image)

theorem IntervalMedium.resistanceOrderIso_apply (A : IntervalMedium)
    (x : Icc A.source.left A.source.right) :
    (A.resistanceOrderIso x : ℝ) = A.resistance x := rfl

theorem IntervalMedium.resistance_hasDerivAt (A : IntervalMedium) {x : ℝ}
    (hx : x ∈ Ioo A.source.left A.source.right) :
    HasDerivAt A.resistance (1 / A.conductance x) x :=
  integral_primitive_hasDerivAt A.resistanceSource.continuous hx

end TimeTraps.Interval
