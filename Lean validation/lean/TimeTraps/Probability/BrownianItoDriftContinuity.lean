module

public import TimeTraps.Probability.BrownianItoDriftProcess
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Ordinary drift integrals along a continuous path are continuous in
the horizon and have exact interval increments. These deterministic facts
do not impose a bound on the continuous integrand or the path. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {g : ℝ → ℝ}

theorem brownianItoDrift_continuous (hg : Continuous g) {ω : Ω}
    (hω : Continuous (fun t => B t ω)) :
    Continuous (fun t => brownianItoDrift B g t ω) := by
  have hc : Continuous (fun s : ℝ => g (B s.toNNReal ω)) :=
    hg.comp (hω.comp continuous_real_toNNReal)
  have hi : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, g (B s.toNNReal ω)) :=
    continuous_iff_continuousAt.mpr (fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt)
  exact hi.comp (by fun_prop : Continuous (fun t : ℝ≥0 => t.val))

theorem brownianItoDrift_increment (hg : Continuous g) {ω : Ω}
    (hω : Continuous (fun t => B t ω)) (S T : ℝ≥0) :
    brownianItoDrift B g T ω - brownianItoDrift B g S ω =
      ∫ s in S.val..T.val, g (B s.toNNReal ω) := by
  have hc : Continuous (fun s : ℝ => g (B s.toNNReal ω)) :=
    hg.comp (hω.comp continuous_real_toNNReal)
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 S.val) (hc.intervalIntegrable S.val T.val)
  unfold brownianItoDrift
  linarith

end TimeTraps.Probability
