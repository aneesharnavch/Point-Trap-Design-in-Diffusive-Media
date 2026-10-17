module

public import TimeTraps.Probability.BrownianPredictableSignCharacteristic
public import TimeTraps.Probability.BrownianStepIntegralBasic

@[expose] public section

/-! A characteristic-function recursion for adding one predictable
unit-sign increment to an arbitrary past-measurable real random variable.
The deterministic coefficient is unrestricted. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_predictable_sign_char_step (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {Y ξ : Ω → ℝ}
    (hY : StronglyMeasurable[brownianNaturalFiltration B hBm s] Y)
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hunit : ∀ᵐ ω ∂P, |ξ ω| = 1) (u c : ℝ) :
    (∫ ω, brownianRealChar u (Y ω + c * (ξ ω * (B t ω - B s ω))) ∂P) =
      (∫ ω, brownianRealChar u (Y ω) ∂P) *
        Complex.exp (-((t.val - s.val : ℝ) : ℂ) * ((u * c : ℝ) : ℂ) ^ 2 / 2) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let f : Ω → ℂ := fun ω => brownianRealChar u (Y ω)
  let g : Ω → ℂ := fun ω => brownianRealChar (u * c) (ξ ω * (B t ω - B s ω))
  have hYm : Measurable Y := (hY.mono ((brownianNaturalFiltration B hBm).le s)).measurable
  have hξm : Measurable ξ := (hξ.mono ((brownianNaturalFiltration B hBm).le s)).measurable
  have hsm : Measurable (fun ω => Y ω + c * (ξ ω * (B t ω - B s ω))) :=
    hYm.add ((hξm.mul ((hBm t).sub (hBm s))).const_mul c)
  have hf : StronglyMeasurable[brownianNaturalFiltration B hBm s] f :=
    ((brownianRealChar_measurable u).comp hY.measurable).stronglyMeasurable
  have hg : Integrable g P := brownianRealChar_integrable (hξm.mul ((hBm t).sub (hBm s))) (u * c)
  have he : (fun ω => brownianRealChar u (Y ω + c * (ξ ω * (B t ω - B s ω)))) =
      fun ω => f ω * g ω := by
    funext ω
    rw [brownianRealChar_add, brownianRealChar_mul_arg]
  have hfg : Integrable (fun ω => f ω * g ω) P := by
    rw [← he]
    exact brownianRealChar_integrable hsm u
  have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hf hfg hg
  have hc := brownian_predictable_sign_char_condExp hB hBm hst hξ hunit (u * c)
  have hcond : P[fun ω => f ω * g ω | brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => f ω * Complex.exp (-((t.val - s.val : ℝ) : ℂ) * ((u * c : ℝ) : ℂ) ^ 2 / 2) := by
    filter_upwards [hp, hc] with ω hpω hcω
    change P[fun ω => f ω * g ω | brownianNaturalFiltration B hBm s] ω =
      f ω * P[g | brownianNaturalFiltration B hBm s] ω at hpω
    rw [hpω, hcω]
  calc
    _ = ∫ ω, f ω * g ω ∂P := by rw [he]
    _ = ∫ ω, P[fun ω => f ω * g ω | brownianNaturalFiltration B hBm s] ω ∂P :=
      (integral_condExp ((brownianNaturalFiltration B hBm).le s)).symm
    _ = ∫ ω, f ω * Complex.exp (-((t.val - s.val : ℝ) : ℂ) * ((u * c : ℝ) : ℂ) ^ 2 / 2) ∂P :=
      integral_congr_ae hcond
    _ = _ := integral_mul_const _ _

end TimeTraps.Probability
