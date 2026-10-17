module

public import TimeTraps.Probability.GraphOccupationPotentialCauchy
public import TimeTraps.Analysis.GraphHeatPointPotentialBumpOccupation
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Shrinking ordinary-length-normalized graph neighborhoods produce a
true mean-square limit under the original conservative path probability.
No local-time existence or occupation convergence is assumed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Probability TimeTraps.Graph
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointOccupationL2_cauchy
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) :
    CauchySeq (fun n => P.occupationL2 hκ x (P.geometry.pointBump a (r n)) T) := by
  obtain ⟨C, hC, hb⟩ := P.occupationPotential_pointBump_bound
  apply P.occupationL2_cauchy_of_potential_approx hκ x
    (fun n => P.geometry.pointBump a (r n)) T (fun t y => P.realizedHeatPointPotential y a t)
    (fun n y => P.geometry.pointBump_nonneg a y (r n))
    (B := C * ((T : ℝ) + 2 * Real.sqrt T)) (by positivity)
    (fun n => (hb T T.coe_nonneg a x (r n)).2)
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := P.occupationPotential_pointBump_compact_uniform T hε
  filter_upwards [hr0.eventually (gt_mem_nhds hδ)] with n hn
  intro t ht y
  exact (hd (r n) (hr n) hn t ht y a).le

theorem GraphShiftedContactOperatorProblem.pointOccupationL2_exists_limit
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) :
    ∃ L : Lp ℝ 2 (P.continuousPathLaw hκ x),
      Tendsto (fun n => P.occupationL2 hκ x (P.geometry.pointBump a (r n)) T) atTop (𝓝 L) :=
  cauchySeq_tendsto_of_complete (P.pointOccupationL2_cauchy hκ x a T hr hr0)

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeL2
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) : Lp ℝ 2 (P.continuousPathLaw hκ x) :=
  (P.pointOccupationL2_exists_limit hκ x a T (r := fun n => 1 / ((n : ℝ) + 1))
    (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat).choose

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_tendsto
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (T : ℝ≥0) :
    Tendsto (fun n : ℕ => P.occupationL2 hκ x
      (P.geometry.pointBump a (1 / ((n : ℝ) + 1))) T) atTop (𝓝 (P.pointLocalTimeL2 hκ x a T)) :=
  (P.pointOccupationL2_exists_limit hκ x a T (r := fun n => 1 / ((n : ℝ) + 1))
    (fun n => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat).choose_spec

end TimeTraps.Analysis
