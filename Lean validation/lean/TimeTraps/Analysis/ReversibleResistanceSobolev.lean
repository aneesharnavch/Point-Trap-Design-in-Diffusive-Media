module

public import TimeTraps.Analysis.ReversibleResistanceCoordinateOccupation
public import TimeTraps.Interval.SourceH1Calculus
public import TimeTraps.Analysis.IntervalEnergyLocal

@[expose] public section

/-! The full physical H¹ space and the full resistance-coordinate H¹
space correspond under the actual resistance map. Almost-everywhere
chain rules are derived from integral representations; neither the state
nor the test function is assumed to have a continuous derivative. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis

noncomputable def IntervalMedium.resistanceProfile (A : IntervalMedium) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun y => u (A.resistanceInverse y)

theorem IntervalMedium.resistance_h1_pullback (A : IntervalMedium) {v : ℝ → ℝ}
    (hv : IntervalEnergy v 0 A.resistanceLength) :
    IntervalEnergy (fun x => v (A.resistance x)) A.source.left A.source.right ∧
      ∀ᵐ x, x ∈ Ioo A.source.left A.source.right →
        deriv (fun y => v (A.resistance y)) x = deriv v (A.resistance x) * (1 / A.conductance x) := by
  have hv' : IntervalEnergy v (A.resistance A.source.left) (A.resistance A.source.right) := by
    simpa only [A.resistance_left, A.resistance_right] using hv
  exact source_h1_comp A.source.increasing.le A.resistance_continuous
    A.resistance_strictMono.monotoneOn (fun _ hx => A.resistance_hasDerivAt hx)
    A.resistanceSource.continuous
    (fun x hx => (one_div_pos.mpr (A.conductance_pos x (Ioo_subset_Icc_self hx))).le) hv'

theorem IntervalMedium.resistance_h1_profile (A : IntervalMedium) {u : ℝ → ℝ}
    (hu : IntervalEnergy u A.source.left A.source.right) :
    IntervalEnergy (A.resistanceProfile u) 0 A.resistanceLength ∧
      ∀ᵐ y, y ∈ Ioo (0 : ℝ) A.resistanceLength →
        deriv (A.resistanceProfile u) y =
          deriv u (A.resistanceInverse y) * A.conductance (A.resistanceInverse y) := by
  have hu' : IntervalEnergy u (A.resistanceInverse 0) (A.resistanceInverse A.resistanceLength) := by
    simpa only [A.resistanceInverse_zero, A.resistanceInverse_length] using hu
  have hc : ContinuousOn (fun y => A.conductance (A.resistanceInverse y))
      (Icc (0 : ℝ) A.resistanceLength) :=
    (A.conductance_continuous.comp_continuous A.resistanceInverse_continuous
      A.resistanceInverse_mem).continuousOn
  exact source_h1_comp A.resistanceLength_pos.le A.resistanceInverse_continuous.continuousOn
    A.resistanceInverse_strictMono.monotoneOn (fun _ hy => A.resistanceInverse_hasDerivAt hy)
    hc (fun y _ => (A.conductance_pos _ (A.resistanceInverse_mem y)).le) hu'

theorem IntervalMedium.resistance_h1_iff (A : IntervalMedium) (u : ℝ → ℝ) :
    IntervalEnergy u A.source.left A.source.right ↔
      IntervalEnergy (A.resistanceProfile u) 0 A.resistanceLength := by
  constructor
  · exact fun hu => (A.resistance_h1_profile hu).1
  · intro hu
    apply (A.resistance_h1_pullback hu).1.congr
    intro x hx
    change u (A.resistanceInverse (A.resistance x)) = u x
    rw [A.resistanceInverse_resistance (by simpa only [uIcc_of_le A.source.increasing.le] using hx)]

theorem IntervalMedium.resistance_profile_pullback (A : IntervalMedium) (v : ℝ → ℝ) :
    EqOn (A.resistanceProfile (fun x => v (A.resistance x))) v (Icc 0 A.resistanceLength) := by
  intro y hy
  change v (A.resistance (A.resistanceInverse y)) = v y
  rw [A.resistance_inverse hy]

end TimeTraps.Interval
