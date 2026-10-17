module

public import TimeTraps.Probability.BrownianSignIntegrand

@[expose] public section

/-! Actual stochastic integrals of the constructed sign integrand.
Lipschitz approximation converges in L² and preserves the exact isometry.
This construction does not assert Tanaka's identity or local-time existence. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianSignIntegral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) : Lp ℝ 2 P :=
  brownianIntegral hB (brownianSignIntegrand hB hBm hjoint a T)

theorem brownianSignIntegral_isometry (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    (∫ ω, brownianSignIntegral hB hBm hjoint a T ω ^ 2 ∂P) =
      ∫ p, brownianSignProcess B a T p ^ 2 ∂(volume : Measure ℝ).prod P := by
  calc
    _ = ∫ p, (brownianSignIntegrand hB hBm hjoint a T : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2
        ∂(volume : Measure ℝ).prod P := brownianIntegral_isometry hB _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [brownianSignIntegrand_coe hB hBm hjoint a T] with p hp
      exact congrArg (fun r : ℝ => r ^ 2) hp

theorem brownianSignIntegral_approximation_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => brownianIntegral hB
      (brownianLipschitzIntegrand hB hBm (brownianSignApprox_lipschitz a n) hjoint T)) atTop
      (𝓝 (brownianSignIntegral hB hBm hjoint a T)) :=
  (brownianIntegral hB).continuous.continuousAt.tendsto.comp
    (brownianSignIntegrand_approximation_tendsto hB hBm hjoint a T)

theorem brownianSignIntegral_approximation_isometry (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    ‖brownianIntegral hB (brownianLipschitzIntegrand hB hBm (brownianSignApprox_lipschitz a n) hjoint T) -
      brownianSignIntegral hB hBm hjoint a T‖ ^ 2 =
    ‖brownianLipschitzProcessL2 hB (brownianSignApprox_lipschitz a n) hjoint T -
      brownianSignProcessL2 B a T (brownianSignProcess_memLp hB hjoint a T)‖ ^ 2 := by
  rw [brownianSignIntegral, ← map_sub, brownianIntegral_norm]
  rfl

theorem brownianSignIntegral_zero (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) :
    brownianSignIntegral hB hBm hjoint a 0 = 0 := by
  rw [brownianSignIntegral, brownianSignIntegrand_zero, map_zero]

noncomputable def brownianDyadicSignIntegral (a : ℝ) (T : ℝ≥0) : Lp ℝ 2 brownianDyadicMeasure :=
  brownianStochasticIntegral (brownianDyadicSignIntegrand a T)

theorem brownianDyadicSignIntegral_isometry (a : ℝ) (T : ℝ≥0) :
    (∫ ω, brownianDyadicSignIntegral a T ω ^ 2 ∂brownianDyadicMeasure) =
      ∫ p, brownianSignProcess brownianDyadicPath a T p ^ 2
        ∂(volume : Measure ℝ).prod brownianDyadicMeasure :=
  brownianSignIntegral_isometry brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a T

theorem brownianDyadicSignIntegral_approximation_tendsto (a : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => brownianStochasticIntegral (brownianDyadicLipschitzIntegrand
      (brownianSignApprox_lipschitz a n) T)) atTop (𝓝 (brownianDyadicSignIntegral a T)) :=
  brownianSignIntegral_approximation_tendsto brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a T

end TimeTraps.Probability
