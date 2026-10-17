module

public import TimeTraps.Spectral.NetworkOperatorHeatPositive
public import TimeTraps.Spectral.NetworkHeatBoundOne
public import TimeTraps.Analysis.CompactHeatInverseComposition

@[expose] public section

/-! Actual positive-time network heat evolution as a bounded map into
the original vertex-continuous H1 space. Every closed-edge point and every
vertex can therefore be evaluated continuously from arbitrary L2 data. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph IntervalSobolevSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

noncomputable def SpectralNetwork.heatSobolevL (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) : GraphL2Product P.geometry →L[ℝ] GraphSobolevSpace P.geometry :=
  P.operatorSolution.comp (P.operatorCompactPositiveInverse.heatInverseL t ht)

theorem SpectralNetwork.heatSobolevL_state (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (f : GraphL2Product P.geometry) :
    graphSobolevSpaceStateL P.geometry (P.heatSobolevL t ht f) = P.heatSemigroup t f :=
  P.operatorCompactPositiveInverse.heatInverseL_right_inverse t ht f

theorem SpectralNetwork.heatSobolevL_state_ae (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (f : GraphL2Product P.geometry) (e : E) :
    (P.heatSemigroup t f) e =ᵐ[volume.restrict (Ioo 0 (P.length e))]
      P.operatorRep (P.heatSobolevL t ht f) e := by
  rw [← P.heatSobolevL_state t ht f]
  exact graphSobolevRepresentative_state_ae P.geometry (P.heatSobolevL t ht f).val e

theorem SpectralNetwork.heatSobolevL_add (P : SpectralNetwork V E)
    (s : ℝ≥0) (hs : 0 < s) (t : ℝ≥0) (f : GraphL2Product P.geometry) :
    P.heatSobolevL (s + t) (lt_add_of_lt_of_nonneg hs (show 0 ≤ t from zero_le)) f =
      P.heatSobolevL s hs (P.heatSemigroup t f) := by
  apply graphSobolevSpaceStateL_injective P.geometry
  rw [P.heatSobolevL_state, P.heatSobolevL_state, P.heatSemigroup_add]
  rfl

noncomputable def SpectralNetwork.heatPointEvaluation (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e)) :
    GraphL2Product P.geometry →L[ℝ] ℝ :=
  ((evalL (P.length_pos e) x x.property).comp (P.operatorEdgeL e)).comp (P.heatSobolevL t ht)

theorem SpectralNetwork.heatPointEvaluation_apply (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e))
    (f : GraphL2Product P.geometry) :
    P.heatPointEvaluation t ht e x f = P.operatorRep (P.heatSobolevL t ht f) e x := rfl

noncomputable def SpectralNetwork.heatNodeEvaluation (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (v : V) : GraphL2Product P.geometry →L[ℝ] ℝ :=
  (graphSobolevNodeValueL P.geometry v).comp (P.heatSobolevL t ht)

theorem SpectralNetwork.heatPointEvaluation_tail (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) :
    P.heatPointEvaluation t ht e ⟨0, le_rfl, (P.length_pos e).le⟩ =
      P.heatNodeEvaluation t ht (P.tail e) := by
  ext f
  exact (graphSobolevNodeValue_tail P.geometry (P.heatSobolevL t ht f) e).symm

theorem SpectralNetwork.heatPointEvaluation_head (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) :
    P.heatPointEvaluation t ht e ⟨P.length e, (P.length_pos e).le, le_rfl⟩ =
      P.heatNodeEvaluation t ht (P.head e) := by
  ext f
  exact (graphSobolevNodeValue_head P.geometry (P.heatSobolevL t ht f) e).symm

end TimeTraps.Spectral
