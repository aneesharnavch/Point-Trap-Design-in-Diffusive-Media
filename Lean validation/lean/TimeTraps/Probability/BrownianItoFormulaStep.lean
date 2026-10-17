module

public import TimeTraps.Probability.BrownianItoDerivative

@[expose] public section

/-! The actual stochastic left sums appearing in Taylor's identity
are the integrals of the checked elementary approximations. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {K : ℝ≥0}

theorem brownianIto_stochastic_step_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g) (T : ℝ≥0) (n : ℕ) :
    brownianIntegral hB (brownianLipschitzStepIntegrand hB hBm hg T n) =ᵐ[P]
      (fun ω => ∑ i : Fin (2 ^ n), g (B (brownianDyadicGrid T n i.castSucc) ω) *
        (B (brownianDyadicGrid T n i.succ) ω - B (brownianDyadicGrid T n i.castSucc) ω)) :=
  brownianIntegral_elementarySum_ae hB (brownianLipschitzElementary hB hBm hg T n)

theorem brownianIto_stochastic_step_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Tendsto (fun n => brownianIntegral hB (brownianLipschitzStepIntegrand hB hBm hg T n)) atTop
      (𝓝 (brownianIntegral hB (brownianLipschitzIntegrand hB hBm hg hjoint T))) :=
  (brownianIntegral hB).continuous.continuousAt.tendsto.comp
    (brownianLipschitzIntegrand_step_tendsto hB hBm hg hjoint T)

theorem brownianIto_stochastic_step_error_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (n : ℕ) :
    ‖brownianIntegral hB (brownianLipschitzStepIntegrand hB hBm hg T n) -
      brownianIntegral hB (brownianLipschitzIntegrand hB hBm hg hjoint T)‖ ^ 2 ≤
      K.val ^ 2 * T.val ^ 2 / (2 : ℝ) ^ n := by
  rw [← map_sub, brownianIntegral_norm]
  exact brownianLipschitzStep_process_error_le hB hBm hg hjoint T n

end TimeTraps.Probability
