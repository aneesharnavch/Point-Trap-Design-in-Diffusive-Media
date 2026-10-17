module

public import TimeTraps.Probability.BrownianPredictableSignLaw

@[expose] public section

/-! The conditional characteristic law can be tested against every
integrable complex multiplier measurable in the original Brownian past.
Bounded past multipliers are a special case. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianRealChar_mul_integrable {Z : Ω → ℂ} (hZ : Integrable Z P)
    {Y : Ω → ℝ} (hY : Measurable Y) (u : ℝ) :
    Integrable (fun ω => Z ω * brownianRealChar u (Y ω)) P := by
  apply hZ.norm.mono' (hZ.aestronglyMeasurable.mul
    ((brownianRealChar_measurable u).comp hY).aestronglyMeasurable)
  filter_upwards [] with ω
  change ‖Z ω * brownianRealChar u (Y ω)‖ ≤ ‖Z ω‖
  rw [norm_mul, brownianRealChar_norm, mul_one]

theorem brownian_predictable_sign_past_step (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℂ} {ξ : Ω → ℝ}
    (hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z) (hZi : Integrable Z P)
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hunit : ∀ᵐ ω ∂P, |ξ ω| = 1) (u c : ℝ) :
    (∫ ω, Z ω * brownianRealChar u (c * (ξ ω * (B t ω - B s ω))) ∂P) =
      (∫ ω, Z ω ∂P) * Complex.exp (-((t.val - s.val : ℝ) : ℂ) * ((u * c : ℝ) : ℂ) ^ 2 / 2) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let g : Ω → ℂ := fun ω => brownianRealChar (u * c) (ξ ω * (B t ω - B s ω))
  have hξm : Measurable ξ := (hξ.mono ((brownianNaturalFiltration B hBm).le s)).measurable
  have hYm : Measurable (fun ω => ξ ω * (B t ω - B s ω)) := hξm.mul ((hBm t).sub (hBm s))
  have hg : Integrable g P := brownianRealChar_integrable hYm (u * c)
  have hZg : Integrable (fun ω => Z ω * g ω) P := brownianRealChar_mul_integrable hZi hYm (u * c)
  have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hZ hZg hg
  have hc := brownian_predictable_sign_char_condExp hB hBm hst hξ hunit (u * c)
  have he : P[fun ω => Z ω * g ω | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => Z ω * Complex.exp (-((t.val - s.val : ℝ) : ℂ) * ((u * c : ℝ) : ℂ) ^ 2 / 2) := by
    filter_upwards [hp, hc] with ω hpω hcω
    change P[fun ω => Z ω * g ω | brownianNaturalFiltration B hBm s] ω =
      Z ω * P[g | brownianNaturalFiltration B hBm s] ω at hpω
    rw [hpω, hcω]
  calc
    _ = ∫ ω, Z ω * g ω ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => congrArg (fun z : ℂ => Z ω * z)
        (brownianRealChar_mul_arg u c _))
    _ = ∫ ω, P[fun ω => Z ω * g ω | brownianNaturalFiltration B hBm s] ω ∂P :=
      (integral_condExp ((brownianNaturalFiltration B hBm).le s)).symm
    _ = ∫ ω, Z ω * Complex.exp (-((t.val - s.val : ℝ) : ℂ) * ((u * c : ℝ) : ℂ) ^ 2 / 2) ∂P :=
      integral_congr_ae he
    _ = _ := integral_mul_const _ _

end TimeTraps.Probability
