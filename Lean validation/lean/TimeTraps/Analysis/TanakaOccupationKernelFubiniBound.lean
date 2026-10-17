module

public import TimeTraps.Analysis.TanakaOccupationKernelParametric
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! The smooth Tanaka kernel is bounded by 1/(2 epsilon). Thus every
scalar L1 level weight gives an absolutely integrable joint kernel along
any measurable path on a finite measure space. No boundedness or pointwise
measurability assumption is added to the L1 weight. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter

theorem tanakaOccupationKernel_uniform_bound {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    tanakaOccupationKernel ε x ≤ 1 / (2 * ε) := by
  rw [tanakaOccupationKernel_eq_half_second hε]
  have hb := tanakaSmoothAbs_second_bound hε x
  rw [abs_of_nonneg (tanakaSmoothAbs_second_nonneg hε x)] at hb
  calc
    _ ≤ (1 / 2 : ℝ) * (1 / ε) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

theorem tanakaOccupationKernel_path_integrable {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε)
    {b : S → ℝ} (hb : Measurable b) {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable (fun p : ℝ × S => g p.1 * tanakaOccupationKernel ε (b p.2 - p.1))
      (volume.prod μ) := by
  apply (hg.comp_fst μ).mul_bdd
    ((tanakaOccupationKernel_continuous hε).measurable.comp
      ((hb.comp measurable_snd).sub measurable_fst)).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖tanakaOccupationKernel ε (b p.2 - p.1)‖ ≤ 1 / (2 * ε)
    rw [Real.norm_eq_abs, abs_of_nonneg (tanakaOccupationKernel_nonneg hε _)]
    exact tanakaOccupationKernel_uniform_bound hε _

theorem tanakaOccupationKernel_average_L1_integrable {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ} (hg : Integrable g) (x : ℝ) :
    Integrable (fun y => tanakaOccupationKernel ε y * g (x - y)) := by
  have hi := (hg.comp_sub_left x).mul_bdd
    (tanakaOccupationKernel_continuous hε).aestronglyMeasurable
    (Eventually.of_forall fun y => show ‖tanakaOccupationKernel ε y‖ ≤ 1 / (2 * ε) by
      rw [Real.norm_eq_abs, abs_of_nonneg (tanakaOccupationKernel_nonneg hε y)]
      exact tanakaOccupationKernel_uniform_bound hε y)
  simpa only [mul_comm] using hi

theorem tanakaOccupationKernel_average_L1_bound {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℝ} (hg : Integrable g) (x : ℝ) :
    |∫ y, tanakaOccupationKernel ε y * g (x - y)| ≤
      (1 / (2 * ε)) * ∫ a, |g a| := by
  calc
    _ ≤ ∫ y, |tanakaOccupationKernel ε y * g (x - y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, (1 / (2 * ε)) * |g (x - y)| := by
      apply integral_mono (tanakaOccupationKernel_average_L1_integrable hε hg x).norm
        ((hg.comp_sub_left x).norm.const_mul _)
      intro y
      change |tanakaOccupationKernel ε y * g (x - y)| ≤ _
      rw [abs_mul, abs_of_nonneg (tanakaOccupationKernel_nonneg hε y)]
      exact mul_le_mul_of_nonneg_right (tanakaOccupationKernel_uniform_bound hε y) (abs_nonneg _)
    _ = _ := by rw [integral_const_mul, integral_sub_left_eq_self (fun a => |g a|) volume x]

end TimeTraps.Analysis
