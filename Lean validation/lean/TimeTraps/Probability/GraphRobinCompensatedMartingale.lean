module

public import TimeTraps.Probability.GraphRobinCompensatedIdentity
public import TimeTraps.Probability.GraphResolventCompensatedMartingaleData
public import TimeTraps.Probability.GraphPointLocalTimeResolventOne
public import TimeTraps.Probability.GraphBorelResolventOne

@[expose] public section

/-! The original full graph Robin weak equation implies the actual
compensated martingale. Both resolvent martingales come from the genuine
conservative path law; no martingale or Dynkin premise is assumed here. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.robinWeak_compensated_martingale
    (P : GraphShiftedContactOperatorProblem V E) (hP : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation P.geometry κ U u) (b : ℝ) (hb : 0 < b) :
    Martingale
      (P.atomicCompensatedProcess b hb (fun v => P.geometry.vertexPoint v) κ
        (graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy)))
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw hP x) := by
  let Q := graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy)
  let f := fun y => Q y + P.geometry.physicalSpeed b y
  have hf : Measurable f := graphRobinResolventForcing_measurable P.geometry hu.energy b
  obtain ⟨C, hC⟩ := graphRobinResolventForcing_bounded P.geometry hu.energy b hb
  have hC0 : 0 ≤ C := (norm_nonneg (f x)).trans (hC x)
  let F : ℝ≥0 → GraphContinuousPath P.geometry → ℝ := fun t p =>
    P.borelResolventOne f (p t) -
      (∫ s in (0 : ℝ)..t.val, P.borelResolventOne f (p s.toNNReal)) +
      (∫ s in (0 : ℝ)..t.val, f (p s.toNNReal))
  let M : V → ℝ≥0 → GraphContinuousPath P.geometry → ℝ := fun v t p =>
    P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint v) 1 (p t) -
      (∫ s in (0 : ℝ)..t.val,
        P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint v) 1 (p s.toNNReal)) +
      P.pointLocalTime (P.geometry.vertexPoint v) t p
  have hF : Martingale F (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw hP x) :=
    P.borelResolvent_martingaleOne hP x f hf hC0 hC
  have hM (v : V) : Martingale (M v) (graphContinuousNaturalFiltration P.geometry)
      (P.continuousPathLaw hP x) :=
    P.pointLocalTimeResolvent_martingaleOne hP x (P.geometry.vertexPoint v)
  have he : P.atomicCompensatedProcess b hb (fun v => P.geometry.vertexPoint v) κ Q =
      (fun t p => F t p - ∑ v, (κ v * U v) * M v t p) := by
    funext t p
    exact P.robinWeak_compensated_identity hP hu b hb t p
  rw [he]
  exact graphResolventMartingale_sub_sum _ _ F M (fun v => κ v * U v) hF hM

end TimeTraps.Analysis
