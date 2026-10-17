module

public import TimeTraps.Spectral.NetworkHeatSobolev

@[expose] public section

namespace TimeTraps.Spectral

open TimeTraps.Analysis IntervalSobolevSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem SpectralNetwork.heatSobolevL_norm_le (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) :
    ‖P.heatSobolevL t ht‖ ≤ ‖P.operatorSolution‖ / (t : ℝ) := by
  let : NormedSpace ℝ (GraphSobolevSpace P.geometry) :=
    Submodule.normedSpace (graphSobolevSubspace P.geometry)
  exact P.operatorCompactPositiveInverse.heatInverseL_comp_norm_le P.operatorSolution t ht

end TimeTraps.Spectral
