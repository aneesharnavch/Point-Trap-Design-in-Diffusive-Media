module

public import TimeTraps.Analysis.GraphHeatPointPotentialBumpApproximation
public import TimeTraps.Analysis.GraphHeatPointPotentialSemigroup

@[expose] public section

/-! The continuous point approximants have the exact actual semigroup
potentials, with bounds and convergence uniform over a full compact time
horizon and all starting points and target points. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

theorem GraphShiftedContactOperatorProblem.occupationPotential_pointBump
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (r : ℝ)
    (x : GraphRealization P.geometry) {t : ℝ} (ht : 0 ≤ t) :
    P.occupationPotential (P.geometry.pointBump a r) t x = P.bumpPointPotential a r x t :=
  P.occupationPotential_pointPotential (P.geometry.pointBump a r) x ht

theorem GraphShiftedContactOperatorProblem.occupationPotential_pointBump_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ), 0 ≤ t →
      ∀ (a x : GraphRealization P.geometry) (r : ℝ),
        0 ≤ P.occupationPotential (P.geometry.pointBump a r) t x ∧
        P.occupationPotential (P.geometry.pointBump a r) t x ≤ C * (t + 2 * Real.sqrt t) := by
  obtain ⟨C, hC, hb⟩ := P.realizedHeatPointPotential_global_bound
  refine ⟨C, hC, ?_⟩
  intro t ht a x r
  rw [P.occupationPotential_pointBump a r x ht]
  constructor
  · exact integral_nonneg (fun y => mul_nonneg (hb t ht x y).2.1 (P.geometry.pointBump_nonneg a y r))
  · calc
      _ ≤ ∫ y, (C * (t + 2 * Real.sqrt t)) * P.geometry.pointBump a r y ∂P.geometry.lengthMeasure :=
        integral_mono (P.bumpPointPotential_integrable a r x t)
          ((P.geometry.pointBump_integrable a r).const_mul _)
          (fun y => mul_le_mul_of_nonneg_right (hb t ht x y).2.2 (P.geometry.pointBump_nonneg a y r))
      _ = _ := by rw [integral_const_mul, P.geometry.pointBump_integral_one, mul_one]

theorem GraphShiftedContactOperatorProblem.occupationPotential_pointBump_compact_uniform
    (P : GraphShiftedContactOperatorProblem V E) (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℝ), 0 < r → r < δ →
      ∀ (t : ℝ), t ∈ Icc 0 T → ∀ (x a : GraphRealization P.geometry),
        |P.occupationPotential (P.geometry.pointBump a r) t x -
          P.realizedHeatPointPotential x a t| < ε := by
  obtain ⟨δ, hδ, hb⟩ := P.bumpPointPotential_compact_uniform T hε
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrδ t ht x a
  rw [P.occupationPotential_pointBump a r x ht.1]
  exact hb r hr hrδ t ht x a

end TimeTraps.Analysis
