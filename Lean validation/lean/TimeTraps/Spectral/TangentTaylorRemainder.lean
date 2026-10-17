module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

@[expose] public section

/-! Analytic Taylor remainders for the tangent equation used in spectral design. -/

namespace TimeTraps.Spectral

open Set Filter Topology Asymptotics

theorem sine_taylor_seven (z : ℝ) :
    taylorWithinEval Real.sin 7 univ 0 z = z - z ^ 3 / 6 + z ^ 5 / 120 - z ^ 7 / 5040 := by
  norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ,
    iteratedDeriv_succ', Real.deriv_sin, Real.deriv_cos', iteratedDeriv_neg,
    iteratedDeriv_zero, smul_eq_mul]
  ring

theorem cosine_taylor_six (z : ℝ) :
    taylorWithinEval Real.cos 6 univ 0 z = 1 - z ^ 2 / 2 + z ^ 4 / 24 - z ^ 6 / 720 := by
  norm_num [taylorWithinEval_succ, iteratedDerivWithin_univ,
    iteratedDeriv_succ', Real.deriv_sin, Real.deriv_cos', iteratedDeriv_neg,
    iteratedDeriv_zero, smul_eq_mul]
  ring

theorem sine_taylor_remainder :
    (fun z : ℝ => Real.sin z - (z - z ^ 3 / 6 + z ^ 5 / 120)) =O[𝓝 0] (fun z => z ^ 7) := by
  have h := (taylor_isLittleO_univ (x₀ := 0) (n := 7) Real.contDiff_sin).isBigO
  simp only [sine_taylor_seven, sub_zero] at h
  have hp := (isBigO_refl (fun z : ℝ => z ^ 7) (𝓝 0)).const_mul_left (-1 / 5040 : ℝ)
  exact (h.add hp).congr_left (fun z => by ring)

theorem cosine_taylor_remainder :
    (fun z : ℝ => Real.cos z - (1 - z ^ 2 / 2 + z ^ 4 / 24)) =O[𝓝 0] (fun z => z ^ 6) := by
  have h := (taylor_isLittleO_univ (x₀ := 0) (n := 6) Real.contDiff_cos).isBigO
  simp only [cosine_taylor_six, sub_zero] at h
  have hp := (isBigO_refl (fun z : ℝ => z ^ 6) (𝓝 0)).const_mul_left (-1 / 720 : ℝ)
  exact (h.add hp).congr_left (fun z => by ring)

end TimeTraps.Spectral
