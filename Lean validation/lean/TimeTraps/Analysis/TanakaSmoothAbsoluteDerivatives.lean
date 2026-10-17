module

public import TimeTraps.Analysis.TanakaSmoothAbsolute
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-! Exact second and third derivatives of the smooth absolute value. -/

namespace TimeTraps.Analysis

theorem tanakaSmoothAbs_second_hasDerivAt {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (deriv (tanakaSmoothAbs ε))
      (ε ^ 2 / tanakaSmoothAbs ε x ^ 3) x := by
  have hs := ne_of_gt (tanakaSmoothAbs_pos hε x)
  have hd := (hasDerivAt_id x).div (tanakaSmoothAbs_hasDerivAt hε x) hs
  have hf : deriv (tanakaSmoothAbs ε) = fun y => y / tanakaSmoothAbs ε y := by
    funext y
    exact tanakaSmoothAbs_deriv hε y
  rw [hf]
  convert! hd using 1
  change ε ^ 2 / tanakaSmoothAbs ε x ^ 3 =
    (1 * tanakaSmoothAbs ε x - x * (x / tanakaSmoothAbs ε x)) / tanakaSmoothAbs ε x ^ 2
  field_simp
  nlinarith [tanakaSmoothAbs_sq ε x]

theorem tanakaSmoothAbs_second_deriv {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    deriv (deriv (tanakaSmoothAbs ε)) x = ε ^ 2 / tanakaSmoothAbs ε x ^ 3 :=
  (tanakaSmoothAbs_second_hasDerivAt hε x).deriv

theorem tanakaSmoothAbs_third_hasDerivAt {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (deriv (deriv (tanakaSmoothAbs ε)))
      (-3 * ε ^ 2 * x / tanakaSmoothAbs ε x ^ 5) x := by
  have hs := ne_of_gt (tanakaSmoothAbs_pos hε x)
  have hd := (hasDerivAt_const x (ε ^ 2)).div
    ((tanakaSmoothAbs_hasDerivAt hε x).pow 3) (pow_ne_zero 3 hs)
  have hf : deriv (deriv (tanakaSmoothAbs ε)) = fun y => ε ^ 2 / tanakaSmoothAbs ε y ^ 3 := by
    funext y
    exact tanakaSmoothAbs_second_deriv hε y
  rw [hf]
  convert! hd using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem tanakaSmoothAbs_third_deriv {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    iteratedDeriv 3 (tanakaSmoothAbs ε) x = -3 * ε ^ 2 * x / tanakaSmoothAbs ε x ^ 5 := by
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
    (tanakaSmoothAbs_third_hasDerivAt hε x).deriv

end TimeTraps.Analysis
