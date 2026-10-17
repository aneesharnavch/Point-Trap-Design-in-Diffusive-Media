module

public import TimeTraps.Probability.BrownianLocalTimeNorm
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section

/-! Bochner integration in the spatial level of the actual L² Tanaka
compensation. Every scalar L¹ weight is admissible; bounded measurable
compactly supported weights and continuous compactly supported weights
are justified instances. No occupation identity is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaCompensation_weight_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    Integrable (fun a => g a • brownianTanakaCompensation hB hBm hjoint a T) volume :=
  hg.smul_bdd (2 * Real.sqrt T.val)
    (brownianTanakaCompensation_level_continuous hB hBm hjoint T).aestronglyMeasurable
    (Eventually.of_forall (fun a => brownianTanakaCompensation_norm_le hB hBm hjoint a T))

theorem brownianTanakaCompensation_weight_bounded_compact (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Measurable g) (hcomp : HasCompactSupport g)
    (M : ℝ) (hM : ∀ a, |g a| ≤ M) :
    Integrable (fun a => g a • brownianTanakaCompensation hB hBm hjoint a T) volume := by
  have hg1 : MemLp g 1 volume := hcomp.memLp_of_bound hg.aestronglyMeasurable M
    (Eventually.of_forall (fun a => by simpa only [Real.norm_eq_abs] using hM a))
  exact brownianTanakaCompensation_weight_integrable hB hBm hjoint T (memLp_one_iff_integrable.mp hg1)

theorem brownianTanakaCompensation_weight_continuous_compact (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Continuous g) (hcomp : HasCompactSupport g) :
    Integrable (fun a => g a • brownianTanakaCompensation hB hBm hjoint a T) volume :=
  brownianTanakaCompensation_weight_integrable hB hBm hjoint T (hg.integrable_of_hasCompactSupport hcomp)

def brownianTanakaLevelIntegral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (g : ℝ → ℝ) : Lp ℝ 2 P :=
  ∫ a, g a • brownianTanakaCompensation hB hBm hjoint a T

theorem brownianTanakaLevelIntegral_norm_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    ‖brownianTanakaLevelIntegral hB hBm hjoint T g‖ ≤ 2 * Real.sqrt T.val * ∫ a, |g a| := by
  have hi : Integrable (fun a => |g a| * (2 * Real.sqrt T.val)) volume := by
    simpa only [Real.norm_eq_abs] using hg.norm.mul_const (2 * Real.sqrt T.val)
  calc
    _ ≤ ∫ a, |g a| * (2 * Real.sqrt T.val) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [] with a
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (brownianTanakaCompensation_norm_le hB hBm hjoint a T) (abs_nonneg _)
    _ = (∫ a, |g a|) * (2 * Real.sqrt T.val) := integral_mul_const _ _
    _ = _ := mul_comm _ _

theorem brownianTanakaLevelIntegral_add (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g k : ℝ → ℝ} (hg : Integrable g volume) (hk : Integrable k volume) :
    brownianTanakaLevelIntegral hB hBm hjoint T (g + k) =
      brownianTanakaLevelIntegral hB hBm hjoint T g + brownianTanakaLevelIntegral hB hBm hjoint T k := by
  simp only [brownianTanakaLevelIntegral, Pi.add_apply, add_smul]
  exact integral_add (brownianTanakaCompensation_weight_integrable hB hBm hjoint T hg)
    (brownianTanakaCompensation_weight_integrable hB hBm hjoint T hk)

theorem brownianTanakaLevelIntegral_smul (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (c : ℝ) (g : ℝ → ℝ) :
    brownianTanakaLevelIntegral hB hBm hjoint T (c • g) =
      c • brownianTanakaLevelIntegral hB hBm hjoint T g := by
  calc
    _ = ∫ a, c • (g a • brownianTanakaCompensation hB hBm hjoint a T) := by
      apply integral_congr_ae
      filter_upwards [] with a
      exact (smul_smul c (g a) (brownianTanakaCompensation hB hBm hjoint a T)).symm
    _ = _ := integral_smul c _

def brownianDyadicTanakaLevelIntegral (T : ℝ≥0) (g : ℝ → ℝ) : Lp ℝ 2 brownianDyadicMeasure :=
  brownianTanakaLevelIntegral brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T g

theorem brownianDyadicTanakaLevelIntegral_norm_le (T : ℝ≥0) {g : ℝ → ℝ} (hg : Integrable g volume) :
    ‖brownianDyadicTanakaLevelIntegral T g‖ ≤ 2 * Real.sqrt T.val * ∫ a, |g a| :=
  brownianTanakaLevelIntegral_norm_le brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T hg

end TimeTraps.Probability

end
