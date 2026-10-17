module

public import TimeTraps.Analysis.ReversibleResistanceCoordinateOccupation

@[expose] public section

/-! Integrability under resistance and speed-density transport. -/

namespace TimeTraps.Interval

open Set MeasureTheory

theorem IntervalMedium.resistance_density_integrable_iff (A : IntervalMedium)
    (g w : ℝ → ℝ) :
    IntervalIntegrable (fun z => g z * A.source.density z * w (A.resistance z))
        volume A.source.left A.source.right ↔
      IntervalIntegrable (fun y => g (A.resistanceInverse y) * A.resistanceSpeed y * w y)
        volume 0 A.resistanceLength := by
  rw [← A.resistanceInverse_integrable_iff]
  apply intervalIntegrable_congr_uIoo
  intro y hy
  have hy' : y ∈ Icc (0 : ℝ) A.resistanceLength :=
    ⟨(le_min (le_refl 0) A.resistanceLength_pos.le).trans hy.1.le,
      hy.2.le.trans (max_le A.resistanceLength_pos.le le_rfl)⟩
  change g (A.resistanceInverse y) * A.source.density (A.resistanceInverse y) *
      w (A.resistance (A.resistanceInverse y)) * A.conductance (A.resistanceInverse y) =
    g (A.resistanceInverse y) * A.resistanceSpeed y * w y
  rw [A.resistance_inverse hy']
  dsimp only [IntervalMedium.resistanceSpeed]
  ring

end TimeTraps.Interval
