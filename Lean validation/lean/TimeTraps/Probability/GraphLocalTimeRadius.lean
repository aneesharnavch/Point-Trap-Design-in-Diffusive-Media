module

public import TimeTraps.Analysis.GraphHeatPointPotentialBumpOccupation
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! One deterministic sequence of positive radii gives geometrically
accurate point-potential approximation on growing horizons. The sequence
is chosen uniformly in both the starting and target graph points. -/

namespace TimeTraps.Analysis

open Set Filter TimeTraps.Graph
open scoped Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def graphLocalTimeError (n : ℕ) : ℝ := (1 / 16 : ℝ) ^ n

theorem graphLocalTimeError_pos (n : ℕ) : 0 < graphLocalTimeError n := by
  unfold graphLocalTimeError
  positivity

theorem graphLocalTimeError_le_one (n : ℕ) : graphLocalTimeError n ≤ 1 := by
  exact pow_le_one₀ (by norm_num : 0 ≤ (1 / 16 : ℝ)) (by norm_num)

theorem graphLocalTimeError_succ_le (n : ℕ) : graphLocalTimeError (n + 1) ≤ graphLocalTimeError n := by
  have h := graphLocalTimeError_pos n
  unfold graphLocalTimeError at *
  rw [pow_succ]
  nlinarith

theorem GraphShiftedContactOperatorProblem.localTimeRadius_exists
    (P : GraphShiftedContactOperatorProblem V E) (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / ((n : ℝ) + 1) ∧
      ∀ t ∈ Icc (0 : ℝ) ((n : ℝ) + 1), ∀ x a : GraphRealization P.geometry,
        |P.occupationPotential (P.geometry.pointBump a r) t x -
          P.realizedHeatPointPotential x a t| ≤ graphLocalTimeError n := by
  obtain ⟨δ, hδ, hd⟩ := P.occupationPotential_pointBump_compact_uniform ((n : ℝ) + 1)
    (graphLocalTimeError_pos n)
  let r := min (δ / 2) (1 / ((n : ℝ) + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  intro t ht x a
  exact (hd r hr ((min_le_left _ _).trans_lt (by linarith)) t ht x a).le

noncomputable def GraphShiftedContactOperatorProblem.localTimeRadius
    (P : GraphShiftedContactOperatorProblem V E) (n : ℕ) : ℝ :=
  (P.localTimeRadius_exists n).choose

theorem GraphShiftedContactOperatorProblem.localTimeRadius_pos
    (P : GraphShiftedContactOperatorProblem V E) (n : ℕ) : 0 < P.localTimeRadius n :=
  (P.localTimeRadius_exists n).choose_spec.1

theorem GraphShiftedContactOperatorProblem.localTimeRadius_tendsto
    (P : GraphShiftedContactOperatorProblem V E) : Tendsto P.localTimeRadius atTop (𝓝 0) :=
  squeeze_zero (fun n => (P.localTimeRadius_pos n).le)
    (fun n => (P.localTimeRadius_exists n).choose_spec.2.1) tendsto_one_div_add_atTop_nhds_zero_nat

theorem GraphShiftedContactOperatorProblem.localTimeRadius_potential_error
    (P : GraphShiftedContactOperatorProblem V E) (n : ℕ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ((n : ℝ) + 1)) (x a : GraphRealization P.geometry) :
    |P.occupationPotential (P.geometry.pointBump a (P.localTimeRadius n)) t x -
      P.realizedHeatPointPotential x a t| ≤ graphLocalTimeError n :=
  (P.localTimeRadius_exists n).choose_spec.2.2 t ht x a

end TimeTraps.Analysis
