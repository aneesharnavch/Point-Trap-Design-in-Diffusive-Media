module

public import TimeTraps.Analysis.GraphContactRealizedHeatIntegral
public import TimeTraps.Analysis.GraphContactHeatKernelComposition

@[expose] public section

/-! Positive-time density composition on the original compact graph,
against ordinary physical edge length. Variable conductance, passive
vertices and the one-positive-contact hypothesis remain unchanged. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph InnerProductSpace
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem GraphContactOperatorProblem.realizedHeatKernel_product_integrable
    (P : GraphContactOperatorProblem V E) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (x y : GraphRealization P.geometry) :
    Integrable (fun z => P.realizedHeatKernel s hs x z * P.realizedHeatKernel t ht y z)
      P.geometry.lengthMeasure :=
  ((P.realizedHeatKernel_right_continuous s hs x).mul
    (P.realizedHeatKernel_right_continuous t ht y)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem GraphContactOperatorProblem.realizedHeatKernel_composition
    (P : GraphContactOperatorProblem V E) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (x y : GraphRealization P.geometry) :
    P.realizedHeatKernel (s + t) (add_pos hs ht) x y =
      ∫ z, P.realizedHeatKernel s hs x z * P.realizedHeatKernel t ht y z
        ∂P.geometry.lengthMeasure := by
  have he := P.geometry.lengthMeasure_integral (fun z =>
    P.realizedHeatKernel s hs x z * P.realizedHeatKernel t ht y z)
    ((P.realizedHeatKernel_right_continuous s hs x).mul
      (P.realizedHeatKernel_right_continuous t ht y))
  rw [he]
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  obtain ⟨d, v, rfl⟩ := P.geometry.edgePoint_surjective y
  rw [P.realizedHeatKernel_edge, P.heatKernel_composition s t hs ht e d u v]
  apply Finset.sum_congr rfl
  intro b _
  apply integral_congr_ae
  filter_upwards [P.realizedHeatKernel_edge_ae s hs e b u,
    P.realizedHeatKernel_edge_ae t ht d b v] with z hz hw
  rw [hz, hw]

theorem GraphContactOperatorProblem.realizedHeatKernel_composition_lintegral
    (P : GraphContactOperatorProblem V E) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (x y : GraphRealization P.geometry) :
    ENNReal.ofReal (P.realizedHeatKernel (s + t) (add_pos hs ht) x y) =
      ∫⁻ z, ENNReal.ofReal (P.realizedHeatKernel s hs x z) *
        ENNReal.ofReal (P.realizedHeatKernel t ht z y) ∂P.geometry.lengthMeasure := by
  rw [P.realizedHeatKernel_composition s t hs ht x y,
    ofReal_integral_eq_lintegral_ofReal (P.realizedHeatKernel_product_integrable s t hs ht x y)
      (Filter.Eventually.of_forall (fun z => mul_nonneg (P.realizedHeatKernel_nonneg s hs x z)
        (P.realizedHeatKernel_nonneg t ht y z)))]
  apply lintegral_congr
  intro z
  rw [ENNReal.ofReal_mul (P.realizedHeatKernel_nonneg s hs x z),
    P.realizedHeatKernel_symmetric t ht y z]

end TimeTraps.Analysis
