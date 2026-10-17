module

public import TimeTraps.Probability.ReflectedC2ItoDrift

@[expose] public section

/-! The two actual quadratic tests isolating the upper and lower reflected
regulators. Their ordinary curvature integrals are computed exactly. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def reflectedUpperBoundaryTest (L z : ℝ) : ℝ := z ^ 2 / (2 * L)

def reflectedLowerBoundaryTest (L z : ℝ) : ℝ := z - reflectedUpperBoundaryTest L z

theorem reflectedUpperBoundaryTest_contDiff (L : ℝ) :
    ContDiff ℝ 2 (reflectedUpperBoundaryTest L) := by
  unfold reflectedUpperBoundaryTest
  fun_prop

theorem reflectedUpperBoundaryTest_deriv (L : ℝ) (hL : 0 < L) :
    deriv (reflectedUpperBoundaryTest L) = fun z => z / L := by
  funext z
  have hd : HasDerivAt (reflectedUpperBoundaryTest L) ((2 * z) / (2 * L)) z := by
    convert! ((hasDerivAt_id z).pow 2).div_const (2 * L) using 1
    simp
  rw [hd.deriv]
  field_simp [ne_of_gt hL]

theorem reflectedUpperBoundaryTest_curvature (L : ℝ) (hL : 0 < L) :
    deriv (deriv (reflectedUpperBoundaryTest L)) = fun _ => 1 / L := by
  rw [reflectedUpperBoundaryTest_deriv L hL]
  funext z
  exact ((hasDerivAt_id z).div_const L).deriv

theorem reflectedLowerBoundaryTest_contDiff (L : ℝ) :
    ContDiff ℝ 2 (reflectedLowerBoundaryTest L) := by
  unfold reflectedLowerBoundaryTest
  exact contDiff_id.sub (reflectedUpperBoundaryTest_contDiff L)

theorem reflectedLowerBoundaryTest_deriv (L : ℝ) (hL : 0 < L) :
    deriv (reflectedLowerBoundaryTest L) = fun z => 1 - z / L := by
  funext z
  have hu : HasDerivAt (reflectedUpperBoundaryTest L) (z / L) z := by
    simpa only [reflectedUpperBoundaryTest_deriv L hL] using
      (((reflectedUpperBoundaryTest_contDiff L).differentiable (by norm_num)) z).hasDerivAt
  exact ((hasDerivAt_id z).sub hu).deriv

theorem reflectedLowerBoundaryTest_curvature (L : ℝ) (hL : 0 < L) :
    deriv (deriv (reflectedLowerBoundaryTest L)) = fun _ => -(1 / L) := by
  rw [reflectedLowerBoundaryTest_deriv L hL]
  funext z
  simpa only [zero_sub] using
    ((hasDerivAt_const z (1 : ℝ)).fun_sub ((hasDerivAt_id' z).div_const L)).deriv

theorem reflectedUpperBoundaryTest_drift {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) (ω : Ω) :
    reflectedC2ItoDrift (reflectedUpperBoundaryTest L) B L D x T ω = T.val / L := by
  simp only [reflectedC2ItoDrift, reflectedUpperBoundaryTest_curvature L hL,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

theorem reflectedLowerBoundaryTest_drift {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (T : ℝ≥0) (ω : Ω) :
    reflectedC2ItoDrift (reflectedLowerBoundaryTest L) B L D x T ω = -(T.val / L) := by
  simp only [reflectedC2ItoDrift, reflectedLowerBoundaryTest_curvature L hL,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

end TimeTraps.Probability

end
