module

public import TimeTraps.Probability.GraphPointLocalTimeDiscountProduct
public import TimeTraps.Probability.GraphPointLocalTimeDiscountNorm
public import TimeTraps.Probability.GraphPointLocalTimeDiscountMeasurable

@[expose] public section

/-! Infinite-horizon exponential integrability under the actual graph
path law, for both local time and its raw-adapted terminal martingales. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscount_product_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) :
    Integrable (fun q : ℝ × GraphContinuousPath P.geometry =>
      Real.exp (-(α * q.1)) * P.pointLocalTime a q.1.toNNReal q.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (P.continuousPathLaw hκ x)) := by
  let inst := P.continuousPathLaw_probability hκ x
  obtain ⟨C, _, hb⟩ := P.realizedHeatPointPotential_global_bound
  have hm : StronglyMeasurable (fun q : ℝ × GraphContinuousPath P.geometry =>
      P.pointLocalTime a q.1.toNNReal q.2) :=
    ((P.pointLocalTime_jointlyMeasurable a).comp
      (measurable_fst.real_toNNReal.prodMk measurable_snd)).stronglyMeasurable
  apply graphPointDiscount_product_integrable (P.continuousPathLaw hκ x) (C := C) hα _ hm
  · intro H
    exact (P.pointLocalTime_memLp hκ x a H.toNNReal).integrable (by norm_num)
  · intro H hH
    rw [P.pointLocalTime_integral_norm hκ x a H.toNNReal, Real.coe_toNNReal H hH.le]
    exact (hb H hH.le x a).2.2

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountTerminal_product_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) (t : ℝ≥0) :
    Integrable (fun q : ℝ × GraphContinuousPath P.geometry =>
      Real.exp (-(α * q.1)) * P.pointLocalTimeTerminalProcess a q.1.toNNReal t q.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (P.continuousPathLaw hκ x)) := by
  let inst := P.continuousPathLaw_probability hκ x
  obtain ⟨C, _, hb⟩ := P.realizedHeatPointPotential_global_bound
  have hm : StronglyMeasurable (fun q : ℝ × GraphContinuousPath P.geometry =>
      P.pointLocalTimeTerminalProcess a q.1.toNNReal t q.2) :=
    (P.pointLocalTimeTerminalProcess_horizon_stronglyMeasurable a t).mono
      (sup_le_sup le_rfl (MeasurableSpace.comap_mono ((graphContinuousNaturalFiltration P.geometry).le t)))
  apply graphPointDiscount_product_integrable (P.continuousPathLaw hκ x) (C := C) hα _ hm
  · intro H
    exact (P.pointLocalTimeTerminalProcess_memLp hκ x a H.toNNReal t).integrable (by norm_num)
  · intro H hH
    apply (P.pointLocalTimeTerminalProcess_integral_norm_le hκ x a H.toNNReal t).trans
    simpa only [Real.coe_toNNReal H hH.le] using (hb H hH.le x a).2.2

end TimeTraps.Analysis
