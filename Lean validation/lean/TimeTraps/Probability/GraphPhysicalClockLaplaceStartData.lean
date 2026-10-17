module

public import TimeTraps.Probability.GraphPhysicalClockLaplaceMeasurable
public import TimeTraps.Probability.GraphPhysicalSpeedMeasure
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-! The reference clock Laplace integrand as a function of the initial
point and reference time. Joint measurability comes from the actual
path kernel and the bounded Borel physical speed, with no Feller claim
for that discontinuous speed representative. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.physicalClockLaplaceIntegrand
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (α : ℝ) (g : GraphRealization P.geometry → ℝ)
    (r : ℝ) (x : GraphRealization P.geometry) : ℝ :=
  ∫ p, Real.exp (-α * (P.geometry.physicalClock b hb r.toNNReal p : ℝ)) *
    g (p r.toNNReal) * P.geometry.physicalSpeed b (p r.toNNReal)
      ∂P.continuousPathLaw h0 x

theorem GraphShiftedContactOperatorProblem.physicalClockLaplaceIntegrand_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (α : ℝ) {g : GraphRealization P.geometry → ℝ} (hg : Measurable g) :
    Measurable (fun q : ℝ × GraphRealization P.geometry =>
      P.physicalClockLaplaceIntegrand h0 b hb α g q.1 q.2) := by
  let K : Kernel (ℝ × GraphRealization P.geometry) (GraphContinuousPath P.geometry) :=
    (P.continuousPathKernel h0).comap
      (Prod.snd : ℝ × GraphRealization P.geometry → GraphRealization P.geometry) measurable_snd
  have hπ : Measurable (fun q : (ℝ × GraphRealization P.geometry) × GraphContinuousPath P.geometry =>
      (q.1.1, q.2)) := (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hm := ((P.geometry.physicalClockLaplace_jointlyMeasurable b hb hg α).comp hπ).stronglyMeasurable
  have hi := hm.integral_kernel_prod_right' (κ := K)
  exact hi.measurable

theorem GraphShiftedContactOperatorProblem.physicalClockLaplaceIntegrand_measurable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (α : ℝ) {g : GraphRealization P.geometry → ℝ}
    (hg : Measurable g) (r : ℝ) :
    Measurable (P.physicalClockLaplaceIntegrand h0 b hb α g r) :=
  (P.physicalClockLaplaceIntegrand_jointlyMeasurable h0 b hb α hg).comp
    (measurable_const.prodMk measurable_id)

end TimeTraps.Analysis
