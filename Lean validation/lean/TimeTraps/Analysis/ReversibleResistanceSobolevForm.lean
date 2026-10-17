module

public import TimeTraps.Analysis.ReversibleResistanceSobolev

@[expose] public section

/-! The original full-H¹ energy form becomes unit-conductance energy
in resistance coordinates. Its forcing is the actual clock speed a*rho,
with unchanged finite contact strengths. -/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis

theorem IntervalMedium.resistance_h1_bilinear (A : IntervalMedium) {u v : ℝ → ℝ}
    (hu : IntervalEnergy u A.source.left A.source.right)
    (hv : IntervalEnergy v A.source.left A.source.right) :
    (∫ x in A.source.left..A.source.right, A.conductance x * deriv u x * deriv v x) =
      ∫ y in (0 : ℝ)..A.resistanceLength,
        deriv (A.resistanceProfile u) y * deriv (A.resistanceProfile v) y := by
  rw [← A.resistanceInverse_integral (fun x => A.conductance x * deriv u x * deriv v x)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(A.resistance_h1_profile hu).2, (A.resistance_h1_profile hv).2,
    volume.ae_ne A.resistanceLength] with y hyu hyv hyne hy
  have hyi : y ∈ Ioo (0 : ℝ) A.resistanceLength := by
    have hy' : y ∈ Ioc (0 : ℝ) A.resistanceLength := by
      simpa only [uIoc_of_le A.resistanceLength_pos.le] using hy
    exact ⟨hy'.1, lt_of_le_of_ne hy'.2 hyne⟩
  rw [hyu hyi, hyv hyi]
  ring

theorem IntervalMedium.resistance_forcing_integral (A : IntervalMedium) (v : ℝ → ℝ) :
    (∫ x in A.source.left..A.source.right, A.source.density x * v x) =
      ∫ y in (0 : ℝ)..A.resistanceLength, A.resistanceSpeed y * A.resistanceProfile v y := by
  rw [← A.resistanceInverse_integral (fun x => A.source.density x * v x)]
  apply intervalIntegral.integral_congr
  intro y _hy
  dsimp only [IntervalMedium.resistanceSpeed, IntervalMedium.resistanceProfile]
  ring

end TimeTraps.Interval
