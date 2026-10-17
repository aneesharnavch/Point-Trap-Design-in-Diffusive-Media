module

public import TimeTraps.Analysis.GraphConservativeCoordinatePowers
public import TimeTraps.Analysis.GraphConservativeMoment

@[expose] public section

/-! Explicit uniform constants for the genuine coordinate generators.
The fourth generator is bounded by a constant times the squared
increment, using the continuous flux energy density of the original
conductance. -/

namespace TimeTraps.Graph

open Set TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def MetricGraph.coordinateSecondMomentConstant (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) : ℝ :=
  4 * ‖G.coordinateTest φ‖ * ‖G.coordinateGenerator φ‖ + 2 * ‖G.coordinateEnergyDensity φ‖

noncomputable def MetricGraph.coordinateFourthGeneratorConstant (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) : ℝ :=
  8 * ‖G.coordinateTest φ‖ * ‖G.coordinateGenerator φ‖ + 12 * ‖G.coordinateEnergyDensity φ‖

theorem MetricGraph.coordinateMomentConstants_nonneg (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) :
    0 ≤ G.coordinateSecondMomentConstant φ ∧ 0 ≤ G.coordinateFourthGeneratorConstant φ := by
  constructor
  · unfold coordinateSecondMomentConstant
    positivity
  · unfold coordinateFourthGeneratorConstant
    positivity

theorem MetricGraph.coordinate_increment_generator_bound (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (x z : GraphRealization G) :
    (G.coordinateTest φ z - G.coordinateTest φ x) * G.coordinateGenerator φ z ≤
      2 * ‖G.coordinateTest φ‖ * ‖G.coordinateGenerator φ‖ := by
  have hd : |G.coordinateTest φ z - G.coordinateTest φ x| ≤ 2 * ‖G.coordinateTest φ‖ := by
    have hs := (norm_sub_le (G.coordinateTest φ z) (G.coordinateTest φ x)).trans
      (add_le_add ((G.coordinateTest φ).norm_coe_le_norm z) ((G.coordinateTest φ).norm_coe_le_norm x))
    simpa only [Real.norm_eq_abs, two_mul] using hs
  calc
    _ ≤ |(G.coordinateTest φ z - G.coordinateTest φ x) * G.coordinateGenerator φ z| := le_abs_self _
    _ = |G.coordinateTest φ z - G.coordinateTest φ x| * |G.coordinateGenerator φ z| := abs_mul _ _
    _ ≤ _ := mul_le_mul hd ((G.coordinateGenerator φ).norm_coe_le_norm z)
      (abs_nonneg _) (by positivity)

theorem MetricGraph.coordinateSquareGenerator_bound (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (x z : GraphRealization G) :
    G.coordinateSquareGenerator φ (G.coordinateTest φ x) z ≤ G.coordinateSecondMomentConstant φ := by
  have hp := G.coordinate_increment_generator_bound φ x z
  have he : G.coordinateEnergyDensity φ z ≤ ‖G.coordinateEnergyDensity φ‖ :=
    (le_abs_self _).trans ((G.coordinateEnergyDensity φ).norm_coe_le_norm z)
  change 2 * ((G.coordinateTest φ z - G.coordinateTest φ x) * G.coordinateGenerator φ z) +
    2 * G.coordinateEnergyDensity φ z ≤
      4 * ‖G.coordinateTest φ‖ * ‖G.coordinateGenerator φ‖ + 2 * ‖G.coordinateEnergyDensity φ‖
  nlinarith

theorem MetricGraph.coordinateFourthGenerator_bound (G : MetricGraph V E)
    (φ : GraphRealizationCoordinates V E →L[ℝ] ℝ) (x z : GraphRealization G) :
    G.coordinateFourthGenerator φ (G.coordinateTest φ x) z ≤
      G.coordinateFourthGeneratorConstant φ * (G.coordinateTest φ z - G.coordinateTest φ x) ^ 2 := by
  have hp := G.coordinate_increment_generator_bound φ x z
  have he : G.coordinateEnergyDensity φ z ≤ ‖G.coordinateEnergyDensity φ‖ :=
    (le_abs_self _).trans ((G.coordinateEnergyDensity φ).norm_coe_le_norm z)
  have hb : 4 * ((G.coordinateTest φ z - G.coordinateTest φ x) * G.coordinateGenerator φ z) +
      12 * G.coordinateEnergyDensity φ z ≤ G.coordinateFourthGeneratorConstant φ := by
    unfold coordinateFourthGeneratorConstant
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg (G.coordinateTest φ z - G.coordinateTest φ x))
  calc
    _ = (4 * ((G.coordinateTest φ z - G.coordinateTest φ x) * G.coordinateGenerator φ z) +
        12 * G.coordinateEnergyDensity φ z) * (G.coordinateTest φ z - G.coordinateTest φ x) ^ 2 := by
      change 4 * ((G.coordinateTest φ z - G.coordinateTest φ x) ^ 3 * G.coordinateGenerator φ z) +
        12 * ((G.coordinateTest φ z - G.coordinateTest φ x) ^ 2 * G.coordinateEnergyDensity φ z) = _
      ring
    _ ≤ _ := hm

end TimeTraps.Graph
