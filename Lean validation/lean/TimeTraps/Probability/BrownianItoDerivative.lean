module

public import TimeTraps.Analysis.ItoTaylorRemainder
public import TimeTraps.Probability.BrownianIntegralLipschitz
public import TimeTraps.Probability.BrownianItoDriftApproximation

@[expose] public section

/-! Global derivative bounds for the restricted C³ Brownian Itô theorem.
These produce actual Lipschitz stochastic and ordinary integrands. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {F : ℝ → ℝ}

theorem brownianIto_firstDerivative_lipschitz (hF : ContDiff ℝ 3 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val) :
    LipschitzWith M₂ (deriv F) := by
  have hd : ContDiff ℝ 2 (deriv F) := hF.deriv'
  apply lipschitzWith_of_nnnorm_deriv_le (hd.differentiable (by norm_num))
  intro x
  change ‖deriv (deriv F) x‖ ≤ M₂.val
  simpa only [Real.norm_eq_abs] using h₂ x

theorem brownianIto_secondDerivative_lipschitz (hF : ContDiff ℝ 3 F)
    {M₃ : ℝ≥0} (h₃ : ∀ x, |iteratedDeriv 3 F x| ≤ M₃.val) :
    LipschitzWith M₃ (deriv (deriv F)) := by
  have hd : ContDiff ℝ 2 (deriv F) := hF.deriv'
  apply lipschitzWith_of_nnnorm_deriv_le hd.differentiable_deriv_two
  intro x
  change ‖deriv (deriv (deriv F)) x‖ ≤ M₃.val
  simpa only [Real.norm_eq_abs, iteratedDeriv_succ, iteratedDeriv_zero] using h₃ x

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianItoIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    brownianIntegralSpace B hBm P :=
  brownianLipschitzIntegrand hB hBm (brownianIto_firstDerivative_lipschitz hF h₂) hjoint T

theorem brownianItoIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hF : ContDiff ℝ 3 F)
    {M₂ : ℝ≥0} (h₂ : ∀ x, |deriv (deriv F) x| ≤ M₂.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    (brownianItoIntegrand hB hBm hF h₂ hjoint T : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      (fun p => (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * deriv F (B p.1.toNNReal p.2)) :=
  brownianLipschitzIntegrand_coe hB hBm (brownianIto_firstDerivative_lipschitz hF h₂) hjoint T

theorem brownianIto_drift_memLp (hB : IsPreBrownianReal B P) (hF : ContDiff ℝ 3 F)
    {M₃ : ℝ≥0} (h₃ : ∀ x, |iteratedDeriv 3 F x| ≤ M₃.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    MemLp (brownianItoDrift B (deriv (deriv F)) T) 2 P :=
  brownianItoDrift_memLp hB (brownianIto_secondDerivative_lipschitz hF h₃) hjoint T

theorem brownianIto_drift_intervalIntegrable_ae (hB : IsPreBrownianReal B P) (hF : ContDiff ℝ 3 F)
    {M₃ : ℝ≥0} (h₃ : ∀ x, |iteratedDeriv 3 F x| ≤ M₃.val)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, IntervalIntegrable (fun s => deriv (deriv F) (B s.toNNReal ω)) volume 0 T.val :=
  brownianItoDrift_intervalIntegrable_ae hB (brownianIto_secondDerivative_lipschitz hF h₃) hjoint T

end TimeTraps.Probability
