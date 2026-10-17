module

public import TimeTraps.Analysis.GraphSobolevProduct
public import TimeTraps.Analysis.IntervalSobolevDense

@[expose] public section

/-! Density of the actual finite edge H1 state range in the edge L2
Hilbert product. Continuous linear equivalences transfer the ordinary
product-topology density theorem to the square-sum Hilbert topology. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Graph IntervalSobolevSpace

variable {V E : Type*}

theorem graphSobolevStateL_denseRange (G : MetricGraph V E) :
    DenseRange (graphSobolevStateL G) := by
  let A := PiLp.continuousLinearEquiv 2 ℝ
    (fun e : E => IntervalSobolevSpace 0 (G.length e))
  let B := PiLp.continuousLinearEquiv 2 ℝ
    (fun e : E => IntervalSobolevL2 0 (G.length e))
  let F := ContinuousLinearMap.piMap
    (fun e : E => IntervalSobolevSpace.stateL 0 (G.length e))
  have hF : DenseRange F := DenseRange.piMap (fun e => stateL_denseRange (G.length_pos e))
  have hFA : DenseRange (F ∘ A) := hF.comp A.surjective.denseRange F.continuous
  exact B.symm.surjective.denseRange.comp hFA B.symm.continuous

end TimeTraps.Analysis
