module

public import TimeTraps.Analysis.TanakaSmoothAbsoluteBounds
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

/-! The same smooth approximation centered at an arbitrary real level. -/

namespace TimeTraps.Analysis

noncomputable def tanakaSmoothShift (ε a x : ℝ) : ℝ := tanakaSmoothAbs ε (x - a)

theorem tanakaSmoothShift_contDiff {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    ContDiff ℝ 3 (tanakaSmoothShift ε a) :=
  (tanakaSmoothAbs_contDiff hε).comp (by fun_prop)

theorem tanakaSmoothShift_deriv (ε a : ℝ) :
    deriv (tanakaSmoothShift ε a) = fun x => deriv (tanakaSmoothAbs ε) (x - a) :=
  funext fun x => deriv_comp_sub_const (tanakaSmoothAbs ε) a x

theorem tanakaSmoothShift_second_deriv (ε a x : ℝ) :
    deriv (deriv (tanakaSmoothShift ε a)) x = deriv (deriv (tanakaSmoothAbs ε)) (x - a) := by
  rw [tanakaSmoothShift_deriv]
  exact deriv_comp_sub_const _ a x

theorem iteratedDeriv_translate (F : ℝ → ℝ) (n : ℕ) (a x : ℝ) :
    iteratedDeriv n (fun y => F (y - a)) x = iteratedDeriv n F (x - a) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ, funext ih]
    exact deriv_comp_sub_const _ a x

theorem tanakaSmoothShift_first_bound {ε : ℝ} (hε : 0 < ε) (a x : ℝ) :
    |deriv (tanakaSmoothShift ε a) x| ≤ 1 := by
  rw [tanakaSmoothShift_deriv]
  exact tanakaSmoothAbs_first_bound hε (x - a)

theorem tanakaSmoothShift_second_nonneg {ε : ℝ} (hε : 0 < ε) (a x : ℝ) :
    0 ≤ deriv (deriv (tanakaSmoothShift ε a)) x := by
  rw [tanakaSmoothShift_second_deriv]
  exact tanakaSmoothAbs_second_nonneg hε (x - a)

theorem tanakaSmoothShift_second_bound {ε : ℝ} (hε : 0 < ε) (a x : ℝ) :
    |deriv (deriv (tanakaSmoothShift ε a)) x| ≤ 1 / ε := by
  rw [tanakaSmoothShift_second_deriv]
  exact tanakaSmoothAbs_second_bound hε (x - a)

theorem tanakaSmoothShift_third_bound {ε : ℝ} (hε : 0 < ε) (a x : ℝ) :
    |iteratedDeriv 3 (tanakaSmoothShift ε a) x| ≤ 3 / ε ^ 2 := by
  change |iteratedDeriv 3 (fun y => tanakaSmoothAbs ε (y - a)) x| ≤ _
  rw [iteratedDeriv_translate]
  exact tanakaSmoothAbs_third_bound hε (x - a)

theorem tanakaSmoothShift_error {ε : ℝ} (hε : 0 ≤ ε) (a x : ℝ) :
    |tanakaSmoothShift ε a x - (|x - a|)| ≤ ε :=
  tanakaSmoothAbs_error hε (x - a)

end TimeTraps.Analysis
