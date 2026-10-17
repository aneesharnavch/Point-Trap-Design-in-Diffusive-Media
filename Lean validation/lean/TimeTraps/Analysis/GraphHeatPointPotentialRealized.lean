module

public import TimeTraps.Analysis.GraphHeatPointPotential
public import TimeTraps.Analysis.GraphShiftedContactRealizedHeatKernel

@[expose] public section

/-! Point-potential estimates on the actual compact graph state space.
The bounds include vertices and remain independent of the chosen incident
edge; the kernel is the density of the constructed graph transition law. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def GraphShiftedContactOperatorProblem.realizedHeatPointKernelTime
    (P : GraphShiftedContactOperatorProblem V E)
    (x y : GraphRealization P.geometry) (t : ℝ) : ℝ :=
  if ht : 0 < t then P.realizedHeatKernel t.toNNReal (Real.toNNReal_pos.mpr ht) x y else 0

theorem GraphShiftedContactOperatorProblem.realizedHeatPointKernelTime_edge
    (P : GraphShiftedContactOperatorProblem V E)
    (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (y : Icc (0 : ℝ) (P.geometry.length d)) (t : ℝ) :
    P.realizedHeatPointKernelTime (P.geometry.edgePoint e x) (P.geometry.edgePoint d y) t =
      P.heatPointKernelTime e d x y t := by
  unfold realizedHeatPointKernelTime heatPointKernelTime
  split_ifs with ht
  · exact P.realizedHeatKernel_edge _ _ e d x y
  · rfl

theorem GraphShiftedContactOperatorProblem.realizedHeatPointKernelTime_continuousOn
    (P : GraphShiftedContactOperatorProblem V E) (x y : GraphRealization P.geometry) :
    ContinuousOn (P.realizedHeatPointKernelTime x y) (Ioi 0) := by
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  obtain ⟨d, v, rfl⟩ := P.geometry.edgePoint_surjective y
  rw [funext (P.realizedHeatPointKernelTime_edge e d u v)]
  exact P.heatPointKernelTime_continuousOn e d u v

theorem GraphShiftedContactOperatorProblem.realizedHeatKernel_short_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (ht : 0 < t), t ≤ 1 →
      ∀ (x y : GraphRealization P.geometry),
        0 ≤ P.realizedHeatKernel t ht x y ∧
          P.realizedHeatKernel t ht x y ≤ C * (1 + 1 / Real.sqrt (t : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := P.heatKernel_short_bound
  refine ⟨C, hC, ?_⟩
  intro t ht ht1 x y
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  obtain ⟨d, v, rfl⟩ := P.geometry.edgePoint_surjective y
  rw [P.realizedHeatKernel_edge]
  exact hb t ht ht1 e d u v

noncomputable def GraphShiftedContactOperatorProblem.realizedHeatPointPotential
    (P : GraphShiftedContactOperatorProblem V E)
    (x y : GraphRealization P.geometry) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, P.realizedHeatPointKernelTime x y t

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_edge
    (P : GraphShiftedContactOperatorProblem V E)
    (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
    (y : Icc (0 : ℝ) (P.geometry.length d)) (T : ℝ) :
    P.realizedHeatPointPotential (P.geometry.edgePoint e x) (P.geometry.edgePoint d y) T =
      P.heatPointPotential e d x y T := by
  unfold realizedHeatPointPotential heatPointPotential
  simp_rw [P.realizedHeatPointKernelTime_edge]

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_short_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ), 0 ≤ T → T ≤ 1 →
      ∀ (x y : GraphRealization P.geometry),
        IntervalIntegrable (P.realizedHeatPointKernelTime x y) volume 0 T ∧
        0 ≤ P.realizedHeatPointPotential x y T ∧
        P.realizedHeatPointPotential x y T ≤ C * (T + 2 * Real.sqrt T) := by
  obtain ⟨C, hC, hb⟩ := P.heatPointPotential_short_bound
  refine ⟨C, hC, ?_⟩
  intro T hT hT1 x y
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  obtain ⟨d, v, rfl⟩ := P.geometry.edgePoint_surjective y
  rw [funext (P.realizedHeatPointKernelTime_edge e d u v)]
  simpa only [P.realizedHeatPointPotential_edge] using
    hb T hT hT1 e d u v

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_uniform_small
    (P : GraphShiftedContactOperatorProblem V E) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (T : ℝ), 0 ≤ T → T ≤ δ →
      ∀ (x y : GraphRealization P.geometry),
        IntervalIntegrable (P.realizedHeatPointKernelTime x y) volume 0 T ∧
        0 ≤ P.realizedHeatPointPotential x y T ∧ P.realizedHeatPointPotential x y T < ε := by
  obtain ⟨δ, hδ, hb⟩ := P.heatPointPotential_uniform_small hε
  refine ⟨δ, hδ, ?_⟩
  intro T hT hTδ x y
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  obtain ⟨d, v, rfl⟩ := P.geometry.edgePoint_surjective y
  rw [funext (P.realizedHeatPointKernelTime_edge e d u v)]
  simpa only [P.realizedHeatPointPotential_edge] using
    hb T hT hTδ e d u v

end TimeTraps.Analysis
