module

public import TimeTraps.Analysis.GraphRobinResolventPointwise
public import TimeTraps.Graph.WeakIdentities

@[expose] public section

/-! Positivity and boundedness of the realized original Robin weak state,
including all graph vertices, follow from the proved source weak theory. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem graphRobinWeak_realized_pos {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation G κ U u) (hκ : ∀ v, 0 ≤ κ v) (ha : ∃ v, 0 < κ v)
    (x : GraphRealization G) :
    0 < graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu.energy) x := by
  obtain ⟨e, y, rfl⟩ := G.edgePoint_surjective x
  rw [graphRealizedSobolev_ofEnergy]
  exact (hu.positive hκ ha).2 e y.val y.property

theorem graphRobinWeak_realized_nonneg {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation G κ U u) (hκ : ∀ v, 0 ≤ κ v) (ha : ∃ v, 0 < κ v)
    (x : GraphRealization G) :
    0 ≤ graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu.energy) x :=
  (graphRobinWeak_realized_pos hu hκ ha x).le

theorem graphRobinWeak_realized_bounded {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation G κ U u) :
    ∃ C : ℝ, ∀ x, ‖graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu.energy) x‖ ≤ C :=
  ⟨‖graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu.energy)‖,
    fun x => ContinuousMap.norm_coe_le_norm _ x⟩

end TimeTraps.Analysis
