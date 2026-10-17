module

public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Data.Real.Sign
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! A smooth base plus finitely many signed absolute-value kinks. The
slope uses the midpoint sign convention at the sites; away from all sites
it is the actual derivative. Repeated sites and signed coefficients are
allowed. -/

namespace TimeTraps.Analysis

variable {ι : Type*}

noncomputable def finiteKinkPotential (F : ℝ → ℝ) (s : Finset ι) (a c : ι → ℝ) (x : ℝ) : ℝ :=
  F x + ∑ i ∈ s, c i * |x - a i|

noncomputable def finiteKinkSlope (F : ℝ → ℝ) (s : Finset ι) (a c : ι → ℝ) (x : ℝ) : ℝ :=
  deriv F x + ∑ i ∈ s, c i * Real.sign (x - a i)

theorem finiteKinkPotential_continuous {F : ℝ → ℝ} (hF : Continuous F)
    (s : Finset ι) (a c : ι → ℝ) : Continuous (finiteKinkPotential F s a c) := by
  apply hF.add
  exact continuous_finsetSum s (fun i _ => ((continuous_id.sub continuous_const).abs).const_mul (c i))

theorem abs_sub_hasDerivAt_real_sign {x a : ℝ} (hx : x ≠ a) :
    HasDerivAt (fun y : ℝ => |y - a|) (Real.sign (x - a)) x := by
  rcases (sub_ne_zero.mpr hx).lt_or_gt with hn | hp
  · rw [Real.sign_of_neg hn]
    simpa only [mul_one, Function.comp_def, id_eq] using (hasDerivAt_abs_neg hn).comp x ((hasDerivAt_id x).sub_const a)
  · rw [Real.sign_of_pos hp]
    simpa only [mul_one, Function.comp_def, id_eq] using (hasDerivAt_abs_pos hp).comp x ((hasDerivAt_id x).sub_const a)

theorem finiteKinkPotential_hasDerivAt {F : ℝ → ℝ} {x : ℝ}
    (hF : DifferentiableAt ℝ F x) (s : Finset ι) (a c : ι → ℝ)
    (hx : ∀ i ∈ s, x ≠ a i) :
    HasDerivAt (finiteKinkPotential F s a c) (finiteKinkSlope F s a c x) x := by
  exact hF.hasDerivAt.add (HasDerivAt.fun_sum (fun i hi =>
    (abs_sub_hasDerivAt_real_sign (hx i hi)).const_mul (c i)))

end TimeTraps.Analysis
