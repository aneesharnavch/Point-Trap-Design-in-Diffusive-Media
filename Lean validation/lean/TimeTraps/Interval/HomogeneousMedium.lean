module

public import TimeTraps.Interval.StrictPartition

@[expose] public section

/-! Physical normalization for unit source and constant positive diffusivity
on [0,L]. The source coordinate and inverse are proved from their integral
definitions, and the transformed weight is exactly L²/D. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis

def homogeneous (L D : ℝ) (hL : 0 < L) (hD : 0 < D) : IntervalMedium where
  source := {
    left := 0
    right := L
    increasing := hL
    density := fun _ => 1
    continuous := continuousOn_const
    positive := fun _ _ => zero_lt_one }
  conductance := fun _ => D
  conductance_continuous := continuousOn_const
  conductance_pos := fun _ _ => hD

theorem homogeneous_mass {L D : ℝ} (hL : 0 < L) (hD : 0 < D) :
    (homogeneous L D hL hD).source.mass = L := by
  change (∫ _ in (0 : ℝ)..L, (1 : ℝ)) = L
  simp

theorem homogeneous_coordinate {L D : ℝ} (hL : 0 < L) (hD : 0 < D) (x : ℝ) :
    (homogeneous L D hL hD).source.coordinate x = x / L := by
  unfold SourceInterval.coordinate
  rw [homogeneous_mass]
  change (∫ _ in (0 : ℝ)..x, (1 : ℝ)) / L = x / L
  simp

theorem homogeneous_inverse {L D z : ℝ} (hL : 0 < L) (hD : 0 < D) (hz : z ∈ Icc (0 : ℝ) 1) :
    (homogeneous L D hL hD).source.inverse z = L * z := by
  have hx : L * z ∈ Icc (0 : ℝ) L := ⟨mul_nonneg hL.le hz.1, by nlinarith [hz.2]⟩
  have hc : (homogeneous L D hL hD).source.coordinate (L * z) = z := by
    rw [homogeneous_coordinate]
    exact mul_div_cancel_left₀ z (ne_of_gt hL)
  have hi := (homogeneous L D hL hD).source.inverse_coordinate hx
  rw [hc] at hi
  exact hi

theorem homogeneous_weight {L D : ℝ} (hL : 0 < L) (hD : 0 < D) (z : ℝ) :
    (homogeneous L D hL hD).cellWeight.value z = L ^ 2 / D := by
  change (homogeneous L D hL hD).source.mass ^ 2 / (D * 1) = _
  rw [homogeneous_mass, mul_one]

end TimeTraps.Interval
