module

public import TimeTraps.Probability.BrownianLocalTimeSmoothLevel
public import TimeTraps.Probability.BrownianLocalTimeLevelIntegral

@[expose] public section

/-! Scalar L¹ weights may be integrated against smooth Tanaka
compensations in actual L², and the resulting Bochner integrals converge
to the already constructed weighted compensation integral. Domination
uses the uniform 2 sqrt T bound, not an occupation identity. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaSmoothCompensation_weight_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (n : ℕ)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    Integrable (fun a => g a • brownianTanakaSmoothCompensation hB hBm hjoint a T n) volume :=
  hg.smul_bdd (2 * Real.sqrt T.val)
    (brownianTanakaSmoothCompensation_level_continuous hB hBm hjoint T n).aestronglyMeasurable
    (Eventually.of_forall (fun a => brownianTanakaSmoothCompensation_norm_le hB hBm hjoint a T n))

def brownianTanakaSmoothLevelIntegral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (g : ℝ → ℝ) (n : ℕ) : Lp ℝ 2 P :=
  ∫ a, g a • brownianTanakaSmoothCompensation hB hBm hjoint a T n

theorem brownianTanakaSmoothLevelIntegral_norm_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (n : ℕ)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    ‖brownianTanakaSmoothLevelIntegral hB hBm hjoint T g n‖ ≤ 2 * Real.sqrt T.val * ∫ a, |g a| := by
  have hi : Integrable (fun a => |g a| * (2 * Real.sqrt T.val)) volume := by
    simpa only [Real.norm_eq_abs] using hg.norm.mul_const (2 * Real.sqrt T.val)
  calc
    _ ≤ ∫ a, |g a| * (2 * Real.sqrt T.val) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [] with a
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (brownianTanakaSmoothCompensation_norm_le hB hBm hjoint a T n)
        (abs_nonneg _)
    _ = (∫ a, |g a|) * (2 * Real.sqrt T.val) := integral_mul_const _ _
    _ = _ := mul_comm _ _

theorem brownianTanakaSmoothLevelIntegral_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    Tendsto (brownianTanakaSmoothLevelIntegral hB hBm hjoint T g) atTop
      (𝓝 (brownianTanakaLevelIntegral hB hBm hjoint T g)) := by
  have hi : Integrable (fun a => |g a| * (2 * Real.sqrt T.val)) volume := by
    simpa only [Real.norm_eq_abs] using hg.norm.mul_const (2 * Real.sqrt T.val)
  exact tendsto_integral_of_dominated_convergence
    (F := fun n a => g a • brownianTanakaSmoothCompensation hB hBm hjoint a T n)
    (f := fun a => g a • brownianTanakaCompensation hB hBm hjoint a T)
    (fun a => |g a| * (2 * Real.sqrt T.val))
    (fun n => hg.aestronglyMeasurable.smul
      (brownianTanakaSmoothCompensation_level_continuous hB hBm hjoint T n).aestronglyMeasurable) hi
    (fun n => Eventually.of_forall (fun a => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (brownianTanakaSmoothCompensation_norm_le hB hBm hjoint a T n)
        (abs_nonneg _)))
    (Eventually.of_forall (fun a => (brownianTanakaSmoothCompensation_tendsto hB hBm hjoint a T).const_smul (g a)))

theorem brownianDyadicTanakaSmoothLevelIntegral_tendsto (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    Tendsto (brownianTanakaSmoothLevelIntegral brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
      brownianDyadicPath_jointly_measurable T g) atTop (𝓝 (brownianDyadicTanakaLevelIntegral T g)) :=
  brownianTanakaSmoothLevelIntegral_tendsto brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T hg

end TimeTraps.Probability

end
