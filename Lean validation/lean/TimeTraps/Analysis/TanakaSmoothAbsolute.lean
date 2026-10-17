module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Tactic

@[expose] public section

/-! A smooth convex approximation to absolute value. These deterministic
estimates will be applied to the proved Brownian Itô formula. -/

namespace TimeTraps.Analysis

noncomputable def tanakaSmoothAbs (ε x : ℝ) : ℝ := Real.sqrt (x ^ 2 + ε ^ 2)

theorem tanakaSmoothAbs_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    0 < tanakaSmoothAbs ε x := by
  apply Real.sqrt_pos.2
  positivity

theorem tanakaSmoothAbs_sq (ε x : ℝ) :
    tanakaSmoothAbs ε x ^ 2 = x ^ 2 + ε ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem abs_le_tanakaSmoothAbs (ε x : ℝ) :
    |x| ≤ tanakaSmoothAbs ε x :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])

theorem epsilon_le_tanakaSmoothAbs {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    ε ≤ tanakaSmoothAbs ε x := by
  simpa only [abs_of_nonneg hε, tanakaSmoothAbs] using
    (Real.abs_le_sqrt (x := ε) (y := x ^ 2 + ε ^ 2) (by nlinarith [sq_nonneg x]))

theorem tanakaSmoothAbs_le {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    tanakaSmoothAbs ε x ≤ |x| + ε := by
  apply (Real.sqrt_le_left (by positivity)).2
  nlinarith [sq_abs x, mul_nonneg (abs_nonneg x) hε]

theorem tanakaSmoothAbs_error {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) :
    |tanakaSmoothAbs ε x - (|x|)| ≤ ε := by
  rw [abs_of_nonneg (sub_nonneg.mpr (abs_le_tanakaSmoothAbs ε x))]
  linarith [tanakaSmoothAbs_le hε x]

theorem tanakaSmoothAbs_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 3 (tanakaSmoothAbs ε) := by
  apply ContDiff.sqrt (by fun_prop)
  intro x
  have : 0 < x ^ 2 + ε ^ 2 := by positivity
  exact ne_of_gt this

theorem tanakaSmoothAbs_hasDerivAt {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (tanakaSmoothAbs ε) (x / tanakaSmoothAbs ε x) x := by
  have hn : x ^ 2 + ε ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hp : HasDerivAt (fun y : ℝ => y ^ 2 + ε ^ 2) (2 * x) x := by
    have hq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      convert! (hasDerivAt_id x).pow 2 using 1
      simp
    simpa only [add_zero] using hq.fun_add (hasDerivAt_const x (ε ^ 2))
  have hd := hp.sqrt hn
  change HasDerivAt (fun y => Real.sqrt (y ^ 2 + ε ^ 2)) (x / Real.sqrt (x ^ 2 + ε ^ 2)) x
  convert hd using 1
  ring

theorem tanakaSmoothAbs_deriv {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    deriv (tanakaSmoothAbs ε) x = x / tanakaSmoothAbs ε x :=
  (tanakaSmoothAbs_hasDerivAt hε x).deriv

end TimeTraps.Analysis
