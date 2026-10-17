module

public import TimeTraps.Probability.BrownianTanakaDifference

@[expose] public section

/-! Uniform approximation of shifted absolute value controls the actual
Brownian differences by twice the uniform error. No derivative hypothesis
is needed for square integrability or the L² error estimate. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {F : ℝ → ℝ} {a ε : ℝ}

theorem brownianTanakaApproxDifference_error_le (B : ℝ≥0 → Ω → ℝ)
    (hF : ∀ x, |F x - abs (x - a)| ≤ ε) (T : ℝ≥0) (ω : Ω) :
    |brownianTanakaApproxDifference B F T ω - brownianTanakaDifference B a T ω| ≤ 2 * ε := by
  calc
    _ = |(F (B T ω) - |B T ω - a|) - (F (B 0 ω) - |B 0 ω - a|)| := by
      congr 1
      unfold brownianTanakaApproxDifference brownianTanakaDifference
      ring
    _ ≤ |F (B T ω) - abs (B T ω - a)| + |F (B 0 ω) - abs (B 0 ω - a)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (F (B T ω) - abs (B T ω - a)) 0 (F (B 0 ω) - abs (B 0 ω - a))
    _ ≤ ε + ε := add_le_add (hF _) (hF _)
    _ = _ := by ring

theorem brownianTanakaApproxDifference_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : Measurable F)
    (hApprox : ∀ x, |F x - abs (x - a)| ≤ ε) (T : ℝ≥0) :
    MemLp (brownianTanakaApproxDifference B F T) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hA := brownianTanakaDifference_memLp hB a T
  have hE : MemLp (fun ω => brownianTanakaApproxDifference B F T ω - brownianTanakaDifference B a T ω) 2 P := by
    apply MemLp.of_bound (((brownianTanakaApproxDifference_measurable hBm hF T).sub
      (brownianTanakaDifference_measurable hBm a T)).aestronglyMeasurable) (2 * ε)
    exact Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using brownianTanakaApproxDifference_error_le B hApprox T ω)
  convert hE.add hA using 1
  funext ω
  exact (sub_add_cancel _ _).symm

noncomputable def brownianTanakaApproxDifferenceL2 (B : ℝ≥0 → Ω → ℝ) (F : ℝ → ℝ) (T : ℝ≥0)
    (hF₂ : MemLp (brownianTanakaApproxDifference B F T) 2 P) : Lp ℝ 2 P :=
  hF₂.toLp (brownianTanakaApproxDifference B F T)

theorem brownianTanakaApproxDifferenceL2_coe (B : ℝ≥0 → Ω → ℝ) (F : ℝ → ℝ) (T : ℝ≥0)
    (hF₂ : MemLp (brownianTanakaApproxDifference B F T) 2 P) :
    brownianTanakaApproxDifferenceL2 B F T hF₂ =ᵐ[P] brownianTanakaApproxDifference B F T := hF₂.coeFn_toLp

theorem brownianTanakaApproxDifferenceL2_error_le (hB : IsPreBrownianReal B P)
    (hε : 0 ≤ ε) (hApprox : ∀ x, |F x - abs (x - a)| ≤ ε) (T : ℝ≥0)
    (hF₂ : MemLp (brownianTanakaApproxDifference B F T) 2 P)
    (hA : MemLp (brownianTanakaDifference B a T) 2 P) :
    ‖brownianTanakaApproxDifferenceL2 B F T hF₂ - brownianTanakaDifferenceL2 B a T hA‖ ≤ 2 * ε := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hbound : ∀ᵐ ω ∂P,
      ‖(brownianTanakaApproxDifferenceL2 B F T hF₂ - brownianTanakaDifferenceL2 B a T hA) ω‖ ≤ 2 * ε := by
    filter_upwards [Lp.coeFn_sub (brownianTanakaApproxDifferenceL2 B F T hF₂) (brownianTanakaDifferenceL2 B a T hA),
      brownianTanakaApproxDifferenceL2_coe B F T hF₂, brownianTanakaDifferenceL2_coe B a T hA] with ω hd hf ha
    rw [hd, Pi.sub_apply, hf, ha, Real.norm_eq_abs]
    exact brownianTanakaApproxDifference_error_le B hApprox T ω
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by positivity : 0 ≤ 2 * ε) hbound

end TimeTraps.Probability
