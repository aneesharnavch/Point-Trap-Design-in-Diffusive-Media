module

public import TimeTraps.Analysis.TanakaOccupationKernelScaling
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Kernel averages of bounded measurable functions are genuine integrals.
At every continuity point they recover the original function as the
smoothing scale vanishes, by exact scaling and dominated convergence. -/

namespace TimeTraps.Analysis

open MeasureTheory Filter
open scoped Topology

theorem tanakaOccupationKernel_average_integrable {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ x, |g x| ≤ M) (x : ℝ) :
    Integrable (fun y => tanakaOccupationKernel ε y * g (x - y)) := by
  apply (tanakaOccupationKernel_integrable hε).mul_bdd
    (hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall fun y => by
    change ‖g (x - y)‖ ≤ M
    simpa only [Real.norm_eq_abs] using hb (x - y)

theorem tanakaOccupationKernel_average_bound {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ x, |g x| ≤ M) (x : ℝ) :
    |∫ y, tanakaOccupationKernel ε y * g (x - y)| ≤ M := by
  have hi := tanakaOccupationKernel_average_integrable hε hg hb x
  calc
    _ ≤ ∫ y, |tanakaOccupationKernel ε y * g (x - y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, tanakaOccupationKernel ε y * M := by
      apply integral_mono hi.norm ((tanakaOccupationKernel_integrable hε).mul_const M)
      intro y
      change |tanakaOccupationKernel ε y * g (x - y)| ≤ tanakaOccupationKernel ε y * M
      rw [abs_mul, abs_of_nonneg (tanakaOccupationKernel_nonneg hε y)]
      exact mul_le_mul_of_nonneg_left (hb (x - y)) (tanakaOccupationKernel_nonneg hε y)
    _ = M := by rw [integral_mul_const, tanakaOccupationKernel_integral hε, one_mul]

theorem tanakaOccupationKernel_average_tendsto {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n)
    (hlim : Tendsto ε atTop (𝓝 0)) {g : ℝ → ℝ} (hg : Measurable g)
    {M : ℝ} (hb : ∀ x, |g x| ≤ M) {x : ℝ} (hgc : ContinuousAt g x) :
    Tendsto (fun n => ∫ y, tanakaOccupationKernel (ε n) y * g (x - y)) atTop (𝓝 (g x)) := by
  have h₁ : (0 : ℝ) < 1 := by norm_num
  have hi := (tanakaOccupationKernel_integrable h₁).mul_const M
  have hd := tendsto_integral_of_dominated_convergence
    (F := fun n y => tanakaOccupationKernel 1 y * g (x - ε n * y))
    (f := fun y => tanakaOccupationKernel 1 y * g x)
    (fun y => tanakaOccupationKernel 1 y * M)
    (fun n => ((tanakaOccupationKernel_continuous h₁).measurable.mul
      (hg.comp (measurable_const.sub (measurable_const.mul measurable_id)))).aestronglyMeasurable)
    hi
    (fun n => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tanakaOccupationKernel_nonneg h₁ y)]
      exact mul_le_mul_of_nonneg_left (hb (x - ε n * y)) (tanakaOccupationKernel_nonneg h₁ y))
    (Eventually.of_forall fun y => by
      have hx : Tendsto (fun n => x - ε n * y) atTop (𝓝 x) := by
        simpa only [zero_mul, sub_zero] using
          (tendsto_const_nhds (x := x)).sub (hlim.mul_const y)
      exact (hgc.tendsto.comp hx).const_mul (tanakaOccupationKernel 1 y))
  have ht : Tendsto (fun n => ∫ y, tanakaOccupationKernel 1 y * g (x - ε n * y)) atTop (𝓝 (g x)) := by
    simpa only [integral_mul_const, tanakaOccupationKernel_integral h₁, one_mul] using hd
  exact ht.congr' (Eventually.of_forall fun n => (tanakaOccupationKernel_average_scale (hε n) g x).symm)

end TimeTraps.Analysis
