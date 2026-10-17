module

public import TimeTraps.Analysis.GaussianLatticeSecondDerivative
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! Variance differentiation of the actual Gaussian density at positive
variance. The derivative is one half of its second spatial derivative.
The ordinary real variance parameter is mapped through `toNNReal`, and
the equality with the explicit formula is derived locally. -/

namespace TimeTraps.Analysis

open ProbabilityTheory Set Filter
open scoped NNReal Topology

theorem gaussianPDFReal_variance_hasDerivAt (x z : ℝ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w : ℝ => gaussianPDFReal x w.toNNReal z)
      ((1 / 2 : ℝ) * gaussianPDFSecondDerivative x v.toNNReal z) v := by
  have harg : 0 < 2 * Real.pi * v := mul_pos (mul_pos (by norm_num) Real.pi_pos) hv
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * v) := Real.sqrt_pos.mpr harg
  have hs := ((((hasDerivAt_id v).const_mul (2 * Real.pi)).sqrt (ne_of_gt harg)).inv
    (ne_of_gt hsqrt))
  have he := (((hasDerivAt_const v (-(z - x) ^ 2)).div
    ((hasDerivAt_id v).const_mul 2) (ne_of_gt (mul_pos (by norm_num) hv))).exp)
  have hprod := hs.mul he
  have hlocal : (fun w : ℝ => gaussianPDFReal x w.toNNReal z) =ᶠ[𝓝 v]
      (fun w : ℝ => (Real.sqrt (2 * Real.pi * w))⁻¹ * Real.exp (-(z - x) ^ 2 / (2 * w))) := by
    filter_upwards [Ioi_mem_nhds hv] with w hw
    unfold gaussianPDFReal
    rw [Real.coe_toNNReal _ hw.le]
  apply (hprod.congr_of_eventuallyEq hlocal).congr_deriv
  unfold gaussianPDFSecondDerivative gaussianPDFReal
  rw [Real.coe_toNNReal _ hv.le]
  dsimp
  have hsquare := Real.sq_sqrt harg.le
  field_simp [ne_of_gt hv, ne_of_gt hsqrt]
  nlinarith [hsquare]

end TimeTraps.Analysis
