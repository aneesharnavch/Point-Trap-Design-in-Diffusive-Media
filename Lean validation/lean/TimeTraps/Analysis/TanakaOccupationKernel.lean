module

public import TimeTraps.Analysis.TanakaSmoothAbsoluteLimit
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! The explicit occupation kernel furnished by smooth Tanaka corrections.
Its factor one half comes from the proved standard-Brownian Itô formula. -/

namespace TimeTraps.Analysis

open MeasureTheory

noncomputable def tanakaOccupationKernel (ε x : ℝ) : ℝ :=
  ε ^ 2 / (2 * tanakaSmoothAbs ε x ^ 3)

theorem tanakaOccupationKernel_nonneg {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 ≤ tanakaOccupationKernel ε x := by
  unfold tanakaOccupationKernel
  exact div_nonneg (sq_nonneg ε) (mul_nonneg (by norm_num) (pow_nonneg (tanakaSmoothAbs_pos hε x).le 3))

theorem tanakaOccupationKernel_even (ε x : ℝ) :
    tanakaOccupationKernel ε (-x) = tanakaOccupationKernel ε x := by
  simp only [tanakaOccupationKernel, tanakaSmoothAbs, neg_sq]

theorem tanakaOccupationKernel_eq_half_second {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    tanakaOccupationKernel ε x = (1 / 2 : ℝ) * deriv (deriv (tanakaSmoothAbs ε)) x := by
  rw [tanakaSmoothAbs_second_deriv hε]
  unfold tanakaOccupationKernel
  ring

theorem tanakaOccupationKernel_continuous {ε : ℝ} (hε : 0 < ε) :
    Continuous (tanakaOccupationKernel ε) := by
  apply Continuous.div continuous_const
    (continuous_const.mul ((tanakaSmoothAbs_contDiff hε).continuous.pow 3))
  intro x
  exact mul_ne_zero (by norm_num) (pow_ne_zero 3 (tanakaSmoothAbs_pos hε x).ne')

theorem tanakaOccupationKernel_primitive {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (fun y => deriv (tanakaSmoothAbs ε) y / 2) (tanakaOccupationKernel ε x) x := by
  convert! (tanakaSmoothAbs_second_hasDerivAt hε x).div_const 2 using 1
  unfold tanakaOccupationKernel
  ring

theorem tanakaOccupationKernel_bound {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    tanakaOccupationKernel ε x ≤ ((ε ^ 2 + 1) / (2 * ε)) * (1 + x ^ 2)⁻¹ := by
  have hs := tanakaSmoothAbs_pos hε x
  have he := epsilon_le_tanakaSmoothAbs hε.le x
  have hq : 0 < x ^ 2 + ε ^ 2 := by positivity
  have hx : 0 < 1 + x ^ 2 := by positivity
  have hr : ε ^ 2 / (x ^ 2 + ε ^ 2) ≤ (ε ^ 2 + 1) / (1 + x ^ 2) := by
    apply (div_le_div_iff₀ hq hx).2
    nlinarith [sq_nonneg x, sq_nonneg (ε ^ 2)]
  have hf : 1 / (2 * tanakaSmoothAbs ε x) ≤ 1 / (2 * ε) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  calc
    _ = (1 / (2 * tanakaSmoothAbs ε x)) * (ε ^ 2 / (x ^ 2 + ε ^ 2)) := by
      rw [← tanakaSmoothAbs_sq ε x]
      unfold tanakaOccupationKernel
      ring
    _ ≤ (1 / (2 * ε)) * ((ε ^ 2 + 1) / (1 + x ^ 2)) :=
      mul_le_mul hf hr (by positivity) (by positivity)
    _ = _ := by ring

theorem tanakaOccupationKernel_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (tanakaOccupationKernel ε) := by
  apply (integrable_inv_one_add_sq.const_mul ((ε ^ 2 + 1) / (2 * ε))).mono'
    (tanakaOccupationKernel_continuous hε).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (tanakaOccupationKernel_nonneg hε x)]
    exact tanakaOccupationKernel_bound hε x

end TimeTraps.Analysis
