module

public import TimeTraps.Analysis.IntervalSobolevCompactEmbedding

@[expose] public section

/-! Spatial continuity of point evaluation in the operator norm of the
actual H1 dual. The half-Hölder bound is uniform over the H1 unit ball. -/

namespace TimeTraps.Analysis.IntervalSobolevSpace

open Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable local instance intervalEvaluationNormedSpace (l r : ℝ) :
    NormedSpace ℝ (IntervalSobolevSpace l r) := Submodule.normedSpace (intervalSobolevGraph l r)

theorem evalL_dist_le {l r : ℝ} (hlr : l < r) (x y : Icc l r) :
    dist (evalL hlr x x.property) (evalL hlr y y.property) ≤ Real.sqrt (dist x y) := by
  rw [dist_eq_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  change ‖u.representative hlr x - u.representative hlr y‖ ≤ _
  exact toContinuousL_dist_le hlr u x y

theorem evalL_continuous {l r : ℝ} (hlr : l < r) :
    Continuous (fun x : Icc l r => evalL hlr x x.property) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  change Tendsto (fun x : Icc l r => evalL hlr x x.property) (𝓝 y)
    (𝓝 (evalL hlr y y.property))
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun x => dist_nonneg) (fun x => evalL_dist_le hlr x y)
  have hc : Continuous (fun x : Icc l r => Real.sqrt (dist x y)) :=
    Real.continuous_sqrt.comp (continuous_id.dist continuous_const)
  simpa only [ContinuousAt, dist_self, Real.sqrt_zero] using hc.continuousAt (x := y)

end TimeTraps.Analysis.IntervalSobolevSpace
