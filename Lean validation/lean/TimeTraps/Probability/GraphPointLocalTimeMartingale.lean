module

public import TimeTraps.Probability.GraphPointLocalTimeMartingaleL2
public import TimeTraps.Probability.GraphPointLocalTimeMartingaleLimit

@[expose] public section

/-! The actual graph point-local-time terminal martingale is derived by
L2 closedness of conditional expectation from the genuine occupation
martingales. Its filtration is the full raw graph path history. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalProcess_condExp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H t : ℝ≥0) :
    (P.continuousPathLaw hκ x)[P.pointLocalTime a H | graphContinuousNaturalFiltration P.geometry t]
      =ᵐ[P.continuousPathLaw hκ x] P.pointLocalTimeTerminalProcess a H t := by
  let inst := P.continuousPathLaw_probability hκ x
  have hC : (P.continuousPathLaw hκ x)[P.pointLocalTimeL2 hκ x a H |
        graphContinuousNaturalFiltration P.geometry t] =ᵐ[P.continuousPathLaw hκ x]
      P.pointLocalTimeTerminalL2 hκ x a H t := by
    apply pointMartingale_condExp_closed_L2 ((graphContinuousNaturalFiltration P.geometry).le t)
      (P.pointLocalTimeL2_tendsto hκ x a H) (P.pointLocalTimeTerminalApproxL2_tendsto hκ x a H t)
    intro n
    exact (condExp_congr_ae (P.occupationL2_coe hκ x
      (P.geometry.pointBump a (1 / ((n : ℝ) + 1))) H)).trans
      ((P.occupationTerminalProcess_condExp hκ x (P.geometry.pointBump a (1 / ((n : ℝ) + 1))) H t).trans
        (P.pointLocalTimeTerminalApproxL2_coe hκ x a H t n).symm)
  exact (condExp_congr_ae (P.pointLocalTime_eq_L2_ae hκ x a H)).trans
    (hC.trans (P.pointLocalTimeTerminalL2_coe hκ x a H t))

theorem GraphShiftedContactOperatorProblem.pointLocalTimeTerminalProcess_martingale
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (H : ℝ≥0) :
    Martingale (P.pointLocalTimeTerminalProcess a H) (graphContinuousNaturalFiltration P.geometry)
      (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact (martingale_condExp (P.pointLocalTime a H) (graphContinuousNaturalFiltration P.geometry)
    (P.continuousPathLaw hκ x)).congr (P.pointLocalTimeTerminalProcess_stronglyAdapted a H)
      (P.pointLocalTimeTerminalProcess_condExp hκ x a H)

end TimeTraps.Analysis
