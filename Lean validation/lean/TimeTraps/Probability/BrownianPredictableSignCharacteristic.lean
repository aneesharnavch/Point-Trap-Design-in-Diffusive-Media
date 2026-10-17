module

public import TimeTraps.Probability.BrownianPredictableSignConditional

@[expose] public section

/-! Exact conditional characteristic functions of predictable unit-sign
Brownian increments, including zero-length increments. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def brownianRealChar (u z : ℝ) : ℂ := Complex.exp ((u * z : ℝ) * Complex.I)

theorem brownianRealChar_norm (u z : ℝ) : ‖brownianRealChar u z‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I (u * z)

theorem brownianRealChar_measurable (u : ℝ) : Measurable (brownianRealChar u) := by
  unfold brownianRealChar
  fun_prop

theorem brownianRealChar_add (u y z : ℝ) :
    brownianRealChar u (y + z) = brownianRealChar u y * brownianRealChar u z := by
  unfold brownianRealChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem brownianRealChar_mul_arg (u c z : ℝ) :
    brownianRealChar u (c * z) = brownianRealChar (u * c) z := by
  unfold brownianRealChar
  rw [mul_assoc]

theorem brownianRealChar_integrable [IsFiniteMeasure P] {Y : Ω → ℝ}
    (hY : Measurable Y) (u : ℝ) : Integrable (fun ω => brownianRealChar u (Y ω)) P := by
  apply (integrable_const (1 : ℝ)).mono' ((brownianRealChar_measurable u).comp hY).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => (brownianRealChar_norm u (Y ω)).le)

theorem brownianRealChar_gaussianIntegral (v : ℝ≥0) (u : ℝ) :
    (∫ z, brownianRealChar u z ∂gaussianReal 0 v) =
      Complex.exp (-(v : ℂ) * (u : ℂ) ^ 2 / 2) := by
  have he : (∫ z, brownianRealChar u z ∂gaussianReal 0 v) = charFun (gaussianReal 0 v) u := by
    rw [charFun_apply_real]
    simp only [brownianRealChar, Complex.ofReal_mul]
  rw [he, charFun_gaussianReal]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub, neg_mul, neg_div]

theorem brownian_predictable_sign_char_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hunit : ∀ᵐ ω ∂P, |ξ ω| = 1) (u : ℝ) :
    P[fun ω => brownianRealChar u (ξ ω * (B t ω - B s ω)) |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun _ => Complex.exp (-((t.val - s.val : ℝ) : ℂ) * (u : ℂ) ^ 2 / 2) := by
  have hc := brownian_predictable_sign_test_condExp hB hBm hst hξ hunit
    (brownianRealChar u) (brownianRealChar_measurable u) (fun z => (brownianRealChar_norm u z).le)
  rw [brownianRealChar_gaussianIntegral] at hc
  have hd : (nndist t.val s.val : ℝ) = t.val - s.val := by
    change dist t.val s.val = _
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show s.val ≤ t.val from hst))]
  have hdC : (nndist t.val s.val : ℂ) = ((t.val - s.val : ℝ) : ℂ) :=
    congrArg Complex.ofReal hd
  rw [hdC] at hc
  exact hc

end TimeTraps.Probability

end
