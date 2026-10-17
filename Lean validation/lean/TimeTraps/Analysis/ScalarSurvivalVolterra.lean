module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section

/-! The scalar Volterra equation obtained from a killed eigenfunction
has its exact exponential solution. Differentiability of the expected
value is derived from its continuous integral equation. -/

namespace TimeTraps.Analysis

open MeasureTheory Set
open scoped NNReal

theorem scalarSurvivalVolterra {q : ℝ≥0 → ℝ} (hq : Continuous q) (b ev : ℝ)
    (he : ∀ T : ℝ≥0, q T = b - ev * ∫ r in (0 : ℝ)..T.val, q r.toNNReal)
    (T : ℝ≥0) : q T = Real.exp (-ev * T.val) * b := by
  let f : ℝ → ℝ := fun r => q r.toNNReal
  have hf : Continuous f := hq.comp continuous_real_toNNReal
  let p : ℝ → ℝ := fun t => b - ev * ∫ r in (0 : ℝ)..t, f r
  have hp (t : ℝ) : HasDerivAt p (-ev * f t) t := by
    simpa only [neg_mul] using
      ((hf.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul ev).const_sub b
  let g : ℝ → ℝ := fun t => Real.exp (ev * t) * p t
  have hg : Continuous g := by
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_iff_continuousAt.mpr (fun t => (hp t).continuousAt))
  have hd (t : ℝ) (ht : t ∈ Ioo 0 T.val) : HasDerivAt g 0 t := by
    have hpt : p t = f t := by
      have ht' : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.1.le
      have hc := congrArg (fun z : ℝ => b - ev * ∫ r in (0 : ℝ)..z, f r) ht'
      exact hc.symm.trans (he t.toNNReal).symm
    have h := (((hasDerivAt_id t).const_mul ev).exp).mul (hp t)
    convert! h using 1
    simp only [id_eq, mul_one, hpt]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le T.coe_nonneg
    hg.continuousOn hd (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 T.val)
  have hz : g 0 = b := by simp [g, p]
  have hT : p T.val = q T := by
    exact (he T).symm
  have hprod : Real.exp (ev * T.val) * q T = b := by
    have hie : 0 = g T.val - g 0 := by
      convert! hi using 1
      exact (intervalIntegral.integral_zero).symm
    have hgT : g T.val = Real.exp (ev * T.val) * q T :=
      congrArg (fun z : ℝ => Real.exp (ev * T.val) * z) hT
    exact hgT.symm.trans ((sub_eq_zero.mp hie.symm).trans hz)
  have hinv : Real.exp (-ev * T.val) * Real.exp (ev * T.val) = 1 := by
    calc
      _ = Real.exp (-ev * T.val + ev * T.val) := (Real.exp_add _ _).symm
      _ = Real.exp 0 := congrArg Real.exp (by ring)
      _ = 1 := Real.exp_zero
  calc
    q T = (Real.exp (-ev * T.val) * Real.exp (ev * T.val)) * q T := by rw [hinv, one_mul]
    _ = Real.exp (-ev * T.val) * b := by rw [mul_assoc, hprod]

end TimeTraps.Analysis
