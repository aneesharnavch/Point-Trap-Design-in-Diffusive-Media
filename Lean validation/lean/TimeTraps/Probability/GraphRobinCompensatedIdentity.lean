module

public import TimeTraps.Analysis.GraphRobinResolvent
public import TimeTraps.Probability.GraphAtomicCompensatedData
public import TimeTraps.Probability.GraphResolventCompensatedAlgebra

@[expose] public section

/-! The original graph compensated process is exactly the resolvent
forcing process minus the finite original vertex point-source processes.
This is a pathwise identity, before any martingale conclusion is used. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.robinWeak_compensated_identity
    (P : GraphShiftedContactOperatorProblem V E) (hP : ∀ v, P.strength v = 0)
    {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : WeakGraphEquation P.geometry κ U u)
    (b : ℝ) (hb : 0 < b) (T : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    let Q := graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy)
    let f := fun y => Q y + P.geometry.physicalSpeed b y
    P.atomicCompensatedProcess b hb (fun v => P.geometry.vertexPoint v) κ Q T p =
      (P.borelResolventOne f (p T) -
        (∫ s in (0 : ℝ)..T.val, P.borelResolventOne f (p s.toNNReal)) +
        (∫ s in (0 : ℝ)..T.val, f (p s.toNNReal))) -
      ∑ v, (κ v * U v) *
        (P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint v) 1 (p T) -
          (∫ s in (0 : ℝ)..T.val,
            P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint v) 1 (p s.toNNReal)) +
          P.pointLocalTime (P.geometry.vertexPoint v) T p) := by
  dsimp only
  let Q := graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy)
  let f := fun y => Q y + P.geometry.physicalSpeed b y
  have hq : Continuous (fun t => Q (p t)) := Q.continuous.comp p.continuous
  have hv (v : V) : Continuous
      (fun t => P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint v) 1 (p t)) := by
    have hc := (graphRealizedSobolev P.geometry
      (P.pointResolventSolution (P.geometry.vertexPoint v))).continuous.comp p.continuous
    change Continuous (fun t => (graphRealizedSobolev P.geometry
      (P.pointResolventSolution (P.geometry.vertexPoint v))) (p t)) at hc
    simpa only [P.pointLocalTimeDiscountedPotential_one_eq] using hc
  have hs : IntervalIntegrable (fun s : ℝ => P.geometry.physicalSpeed b (p s.toNNReal)) volume 0 T.val :=
    (P.geometry.physicalClockSpeed b hb p).rate_intervalIntegrable 0 T.val
  have hd (t : ℝ≥0) : Q (p t) = P.borelResolventOne f (p t) -
      ∑ v, (κ v * U v) * P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint v) 1 (p t) :=
    P.robinWeak_resolvent_borel hP hu b hb (p t)
  have he := graphResolventCompensated_algebra
    (fun t => Q (p t)) (fun t => P.borelResolventOne f (p t))
    (fun v t => P.pointLocalTimeDiscountedPotential (P.geometry.vertexPoint v) 1 (p t))
    (fun v t => P.pointLocalTime (P.geometry.vertexPoint v) t p) (fun v => κ v * U v)
    (fun t => P.geometry.physicalSpeed b (p t)) T hq hv hs hd
  symm
  apply he.trans
  change Q (p T) + (∫ s in (0 : ℝ)..T.val, P.geometry.physicalSpeed b (p s.toNNReal)) -
      ∑ v, κ v * U v * P.pointLocalTime (P.geometry.vertexPoint v) T p =
    Q (p T) + (P.geometry.physicalClock b hb T p : ℝ) -
      ∑ v, κ v * Q (P.geometry.vertexPoint v) * P.pointLocalTime (P.geometry.vertexPoint v) T p
  rw [P.geometry.physicalClock_coe]
  have hQ (v : V) : Q (P.geometry.vertexPoint v) = U v := by
    change graphRealizedSobolev P.geometry (graphSobolevSpaceOfEnergy P.geometry hu.energy)
      (P.geometry.vertexPoint v) = U v
    rw [graphRealizedSobolev_vertex, graphSobolevSpaceOfEnergy_node]
  simp only [hQ]

end TimeTraps.Analysis
