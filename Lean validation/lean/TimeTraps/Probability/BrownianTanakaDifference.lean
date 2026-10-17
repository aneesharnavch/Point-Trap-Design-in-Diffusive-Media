module

public import TimeTraps.Probability.BrownianSignIntegrandStochastic

@[expose] public section

/-! The actual shifted absolute-value Brownian difference, keeping B₀
explicit, and its independently justified square-integrable representative. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianTanakaDifference (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  |B T ω - a| - |B 0 ω - a|

theorem brownianTanakaDifference_measurable (hBm : ∀ t, Measurable (B t)) (a : ℝ) (T : ℝ≥0) :
    Measurable (brownianTanakaDifference B a T) :=
  ((hBm T).sub_const a).abs.sub (((hBm 0).sub_const a).abs)

theorem brownianTanakaDifference_memLp (hB : IsPreBrownianReal B P) (a : ℝ) (T : ℝ≥0) :
    MemLp (brownianTanakaDifference B a T) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hT := ((hB.hasLaw_eval T).hasGaussianLaw.memLp_two.sub (memLp_const a)).norm
  have h₀ := ((hB.hasLaw_eval 0).hasGaussianLaw.memLp_two.sub (memLp_const a)).norm
  have h := hT.sub h₀
  change MemLp (fun ω => ‖B T ω - a‖ - ‖B 0 ω - a‖) 2 P at h
  change MemLp (fun ω => |B T ω - a| - |B 0 ω - a|) 2 P
  simpa only [Real.norm_eq_abs] using h

noncomputable def brownianTanakaDifferenceL2 (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0)
    (hA : MemLp (brownianTanakaDifference B a T) 2 P) : Lp ℝ 2 P :=
  hA.toLp (brownianTanakaDifference B a T)

theorem brownianTanakaDifferenceL2_coe (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0)
    (hA : MemLp (brownianTanakaDifference B a T) 2 P) :
    brownianTanakaDifferenceL2 B a T hA =ᵐ[P] brownianTanakaDifference B a T := hA.coeFn_toLp

theorem brownianTanakaDifference_zero (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (ω : Ω) :
    brownianTanakaDifference B a 0 ω = 0 := by simp [brownianTanakaDifference]

noncomputable def brownianTanakaApproxDifference (B : ℝ≥0 → Ω → ℝ) (F : ℝ → ℝ)
    (T : ℝ≥0) (ω : Ω) : ℝ := F (B T ω) - F (B 0 ω)

theorem brownianTanakaApproxDifference_measurable (hBm : ∀ t, Measurable (B t))
    {F : ℝ → ℝ} (hF : Measurable F) (T : ℝ≥0) :
    Measurable (brownianTanakaApproxDifference B F T) := (hF.comp (hBm T)).sub (hF.comp (hBm 0))

theorem brownianTanakaApproxDifference_zero (B : ℝ≥0 → Ω → ℝ) (F : ℝ → ℝ) (ω : Ω) :
    brownianTanakaApproxDifference B F 0 ω = 0 := by simp [brownianTanakaApproxDifference]

end TimeTraps.Probability
