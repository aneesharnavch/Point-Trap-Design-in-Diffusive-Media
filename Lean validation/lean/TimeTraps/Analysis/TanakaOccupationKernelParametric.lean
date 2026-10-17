module

public import TimeTraps.Analysis.TanakaOccupationKernelAverage
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Actual kernel averages are measurable in the evaluation point.
For a bounded continuous function their averages are continuous, with
domination by the integrable kernel on the whole real line. -/

namespace TimeTraps.Analysis

open MeasureTheory Filter
open scoped Topology

theorem tanakaOccupationKernel_average_measurable {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (fun x => ∫ y, tanakaOccupationKernel ε y * g (x - y)) := by
  have hm : Measurable (fun p : ℝ × ℝ => tanakaOccupationKernel ε p.2 * g (p.1 - p.2)) :=
    ((tanakaOccupationKernel_continuous hε).measurable.comp measurable_snd).mul
      (hg.comp (measurable_fst.sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem tanakaOccupationKernel_average_continuous {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hb : ∀ x, |g x| ≤ M) :
    Continuous (fun x => ∫ y, tanakaOccupationKernel ε y * g (x - y)) := by
  apply continuous_iff_seqContinuous.mpr
  intro u x hu
  exact tendsto_integral_of_dominated_convergence
    (F := fun n y => tanakaOccupationKernel ε y * g (u n - y))
    (f := fun y => tanakaOccupationKernel ε y * g (x - y))
    (fun y => tanakaOccupationKernel ε y * M)
    (fun n => ((tanakaOccupationKernel_continuous hε).measurable.mul
      (hg.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable)
    ((tanakaOccupationKernel_integrable hε).mul_const M)
    (fun n => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tanakaOccupationKernel_nonneg hε y)]
      exact mul_le_mul_of_nonneg_left (hb (u n - y)) (tanakaOccupationKernel_nonneg hε y))
    (Eventually.of_forall fun y =>
      (hg.continuousAt.tendsto.comp (hu.sub_const y)).const_mul (tanakaOccupationKernel ε y))

end TimeTraps.Analysis
