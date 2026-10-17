module

public import TimeTraps.Analysis.GraphConservativeCoordinateEmbedding
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! Explicit first and second derivatives of the finite graph coordinate
curve. These polynomial identities are used before inserting the actual
resistance coordinate and the original conductance. -/

namespace TimeTraps.Graph

open Set

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def MetricGraph.edgeCoordinateSlope (G : MetricGraph V E) (e : E) (s : ℝ) :
    GraphRealizationCoordinates V E := by
  classical
  exact (Pi.single (G.head e) 1 - Pi.single (G.tail e) 1,
    (1 - 2 * s) • Pi.single e 1, (2 * s - 3 * s ^ 2) • Pi.single e 1)

noncomputable def MetricGraph.edgeCoordinateCurvature (_G : MetricGraph V E) (e : E) (s : ℝ) :
    GraphRealizationCoordinates V E := by
  classical
  exact (0, (-2 : ℝ) • Pi.single e 1, (2 - 6 * s) • Pi.single e 1)

theorem MetricGraph.edgeCoordinates_hasDerivAt (G : MetricGraph V E) (e : E) (s : ℝ) :
    HasDerivAt (G.edgeCoordinates e) (G.edgeCoordinateSlope e s) s := by
  classical
  convert! ((((hasDerivAt_const s 1).sub (hasDerivAt_id s)).smul_const (Pi.single (G.tail e) 1 : V → ℝ)).add
    ((hasDerivAt_id s).smul_const (Pi.single (G.head e) 1 : V → ℝ))).prodMk
      ((((hasDerivAt_id s).mul ((hasDerivAt_const s 1).sub (hasDerivAt_id s))).smul_const
        (Pi.single e 1 : E → ℝ)).prodMk
          (((hasDerivAt_id s).mul ((hasDerivAt_id s).mul ((hasDerivAt_const s 1).sub
            (hasDerivAt_id s)))).smul_const (Pi.single e 1 : E → ℝ))) using 1
  ext <;> dsimp [edgeCoordinateSlope] <;> ring

theorem MetricGraph.edgeCoordinateSlope_hasDerivAt (G : MetricGraph V E) (e : E) (s : ℝ) :
    HasDerivAt (G.edgeCoordinateSlope e) (G.edgeCoordinateCurvature e s) s := by
  classical
  convert! (hasDerivAt_const s (Pi.single (G.head e) 1 - Pi.single (G.tail e) 1 : V → ℝ)).prodMk
    ((((hasDerivAt_const s 1).sub ((hasDerivAt_id s).const_mul 2)).smul_const (Pi.single e 1 : E → ℝ)).prodMk
      ((((hasDerivAt_id s).const_mul 2).sub (((hasDerivAt_id s).pow 2).const_mul 3)).smul_const
        (Pi.single e 1 : E → ℝ))) using 1
  ext <;> dsimp [edgeCoordinateCurvature] <;> ring

end TimeTraps.Graph
