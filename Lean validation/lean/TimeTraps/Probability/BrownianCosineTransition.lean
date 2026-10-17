module

public import TimeTraps.Probability.BrownianPredictableSignPastStep

@[expose] public section

/-! Conditional Fourier evolution of an affine Brownian trajectory.
The conditioning is on the original Brownian past. Only the verified
Gaussian increment law and its independence from that past are used. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_affine_char_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) (x σ u : ℝ) :
    P[fun ω => brownianRealChar u (x + σ * B t ω) |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => (Real.exp (-(t.val - s.val) * (u * σ) ^ 2 / 2) : ℂ) *
        brownianRealChar u (x + σ * B s ω) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let Z : Ω → ℂ := fun ω => brownianRealChar u (x + σ * B s ω)
  let g : Ω → ℂ := fun ω => brownianRealChar (u * σ) (B t ω - B s ω)
  have hZ : StronglyMeasurable[brownianNaturalFiltration B hBm s] Z :=
    ((brownianRealChar_measurable u).comp (measurable_const.add (measurable_const.mul
      (brownianNaturalFiltration_stronglyAdapted B hBm s).measurable))).stronglyMeasurable
  have hZi : Integrable Z P := brownianRealChar_integrable
    (measurable_const.add (measurable_const.mul (hBm s))) u
  have hg : Integrable g P := brownianRealChar_integrable ((hBm t).sub (hBm s)) (u * σ)
  have hZg : Integrable (fun ω => Z ω * g ω) P :=
    brownianRealChar_mul_integrable hZi ((hBm t).sub (hBm s)) (u * σ)
  have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hZ hZg hg
  have hc := brownian_predictable_sign_char_condExp hB hBm hst
    (ξ := fun _ => 1) stronglyMeasurable_const (Eventually.of_forall (fun _ => abs_one)) (u * σ)
  simp only [one_mul] at hc
  have he : Complex.exp (-((t.val - s.val : ℝ) : ℂ) * ((u * σ : ℝ) : ℂ) ^ 2 / 2) =
      (Real.exp (-(t.val - s.val) * (u * σ) ^ 2 / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  rw [he] at hc
  have hf : (fun ω => brownianRealChar u (x + σ * B t ω)) =
      (fun ω => Z ω * g ω) := by
    funext ω
    change brownianRealChar u (x + σ * B t ω) =
      brownianRealChar u (x + σ * B s ω) * brownianRealChar (u * σ) (B t ω - B s ω)
    rw [← brownianRealChar_mul_arg, ← brownianRealChar_add]
    congr 1
    ring
  rw [hf]
  filter_upwards [hp, hc] with ω hpω hcω
  change P[fun ω => Z ω * g ω | brownianNaturalFiltration B hBm s] ω =
    Z ω * P[g | brownianNaturalFiltration B hBm s] ω at hpω
  rw [hpω, hcω, mul_comm]

theorem brownian_affine_cos_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) (x σ u : ℝ) :
    P[fun ω => Real.cos (u * (x + σ * B t ω)) |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => Real.exp (-(t.val - s.val) * (u * σ) ^ 2 / 2) *
        Real.cos (u * (x + σ * B s ω)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hi : Integrable (fun ω => brownianRealChar u (x + σ * B t ω)) P :=
    brownianRealChar_integrable (measurable_const.add (measurable_const.mul (hBm t))) u
  have hr := Complex.reCLM.comp_condExp_comm hi (m := brownianNaturalFiltration B hBm s)
  have hc := brownian_affine_char_condExp hB hBm hst x σ u
  filter_upwards [hr, hc] with ω hrω hcω
  have hf : (Complex.reCLM ∘ (fun ω => brownianRealChar u (x + σ * B t ω))) =
      (fun ω => Real.cos (u * (x + σ * B t ω))) := by
    funext ω
    exact Complex.exp_ofReal_mul_I_re _
  rw [hf] at hrω
  rw [← hrω]
  change (P[fun ω => brownianRealChar u (x + σ * B t ω) |
    brownianNaturalFiltration B hBm s] ω).re = _
  rw [hcω]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [show (brownianRealChar u (x + σ * B s ω)).re =
    Real.cos (u * (x + σ * B s ω)) from Complex.exp_ofReal_mul_I_re _]

theorem brownian_affine_cos_integral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (t : ℝ≥0) (x σ u : ℝ) :
    (∫ ω, Real.cos (u * (x + σ * B t ω)) ∂P) =
      Real.exp (-t.val * (u * σ) ^ 2 / 2) * Real.cos (u * x) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hc := brownian_affine_cos_condExp hB hBm (show (0 : ℝ≥0) ≤ t from zero_le) x σ u
  have he : P[fun ω => Real.cos (u * (x + σ * B t ω)) |
      brownianNaturalFiltration B hBm 0] =ᵐ[P]
      fun _ => Real.exp (-t.val * (u * σ) ^ 2 / 2) * Real.cos (u * x) := by
    filter_upwards [hc, hB.eval_zero_ae_eq_zero] with ω hcω hzero
    simpa [hzero] using hcω
  calc
    _ = ∫ ω, P[fun ω => Real.cos (u * (x + σ * B t ω)) |
      brownianNaturalFiltration B hBm 0] ω ∂P :=
      (integral_condExp ((brownianNaturalFiltration B hBm).le 0)).symm
    _ = _ := by rw [integral_congr_ae he]; simp

end TimeTraps.Probability
