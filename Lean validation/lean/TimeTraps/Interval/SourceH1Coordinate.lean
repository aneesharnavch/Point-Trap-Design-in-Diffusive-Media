module

public import TimeTraps.Interval.SourceH1Calculus
public import TimeTraps.Analysis.IntervalEnergyLocal

@[expose] public section

/-! Equivalence of the full H1 spaces in physical and normalized source
coordinates, including the almost-everywhere chain rules in both directions.
Only positivity and continuity of the physical source density are needed. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis

theorem source_h1_coordinate (P : SourceInterval) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 1) :
    IntervalEnergy (fun x => v (P.coordinate x)) P.left P.right ∧
      ∀ᵐ x, x ∈ Ioo P.left P.right →
        deriv (fun y => v (P.coordinate y)) x = deriv v (P.coordinate x) * (P.density x / P.mass) := by
  have hv' : IntervalEnergy v (P.coordinate P.left) (P.coordinate P.right) := by
    simpa only [P.coordinate_left, P.coordinate_right] using hv
  exact source_h1_comp P.increasing.le P.coordinate_continuous P.coordinate_strictMono.monotoneOn
    (fun _ hx => P.coordinate_derivative hx) (P.continuous.div_const P.mass)
    (fun x hx => (div_pos (P.positive x (Ioo_subset_Icc_self hx)) P.mass_pos).le) hv'

theorem source_h1_inverse (P : SourceInterval) {u : ℝ → ℝ}
    (hu : IntervalEnergy u P.left P.right) :
    IntervalEnergy (P.transformed u) 0 1 ∧
      ∀ᵐ z, z ∈ Ioo (0 : ℝ) 1 →
        deriv (P.transformed u) z = deriv u (P.inverse z) * (P.mass / P.density (P.inverse z)) := by
  have hu' : IntervalEnergy u (P.inverse 0) (P.inverse 1) := by
    simpa only [P.inverse_zero, P.inverse_one] using hu
  have hj : ContinuousOn (fun z => P.mass / P.density (P.inverse z)) (Icc (0 : ℝ) 1) :=
    (continuous_const.div (P.transformed_continuous P.continuous)
      (fun z => ne_of_gt (P.positive _ (P.inverse_mem z)))).continuousOn
  exact source_h1_comp zero_le_one P.inverse_continuous.continuousOn P.inverse_strictMono.monotoneOn
    (fun _ hz => P.inverse_derivative hz) hj
    (fun z _ => (div_pos P.mass_pos (P.positive _ (P.inverse_mem z))).le) hu'

theorem source_h1_iff (P : SourceInterval) (u : ℝ → ℝ) :
    IntervalEnergy u P.left P.right ↔ IntervalEnergy (P.transformed u) 0 1 := by
  constructor
  · intro hu
    exact (source_h1_inverse P hu).1
  · intro hu
    apply (source_h1_coordinate P hu).1.congr
    intro x hx
    exact P.transformed_coordinate u (by simpa only [uIcc_of_le P.increasing.le] using hx)

theorem source_h1_pullback_iff (P : SourceInterval) (v : ℝ → ℝ) :
    IntervalEnergy v 0 1 ↔ IntervalEnergy (fun x => v (P.coordinate x)) P.left P.right := by
  constructor
  · intro hv
    exact (source_h1_coordinate P hv).1
  · intro hv
    apply (source_h1_inverse P hv).1.congr
    intro z hz
    change v (P.coordinate (P.inverse z)) = v z
    rw [P.coordinate_inverse (by simpa only [uIcc_of_le zero_le_one] using hz)]

end TimeTraps.Interval
