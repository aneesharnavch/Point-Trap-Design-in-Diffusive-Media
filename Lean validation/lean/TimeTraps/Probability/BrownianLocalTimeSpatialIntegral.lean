module

public import TimeTraps.Analysis.L2IntegralSectionsFinite
public import TimeTraps.Probability.BrownianLocalTimeLevelVersion
public import TimeTraps.Probability.BrownianLocalTimeLevelIntegral

@[expose] public section

/-! Scalar L¹ weights give absolutely integrable ordinary spatial
sections of the jointly measurable local-time version. Their actual
integrals represent the previously constructed L²-valued Bochner
integral. The justification uses finite-measure L² bounds, not a
uniform pointwise bound in the sample. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianLocalTimeLevelVersion_weight_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (g : ℝ → ℝ) (a : ℝ) :
    (g a • brownianTanakaCompensation hB hBm hjoint a T : Lp ℝ 2 P) =ᵐ[P]
      (fun ω => g a * brownianLocalTimeLevelVersion hB hBm hjoint T a ω) := by
  filter_upwards [Lp.coeFn_smul (g a) (brownianTanakaCompensation hB hBm hjoint a T),
    brownianLocalTimeLevelVersion_ae hB hBm hjoint T a] with ω hs he
  rw [hs, Pi.smul_apply, smul_eq_mul, he]

theorem brownianLocalTimeLevelVersion_weight_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    Integrable (fun p : ℝ × Ω => g p.1 * brownianLocalTimeLevelVersion hB hBm hjoint T p.1 p.2)
      (volume.prod P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact real_L2_sections_integrable (brownianTanakaCompensation_weight_integrable hB hBm hjoint T hg)
    (hg.aestronglyMeasurable.comp_fst.mul
      (brownianLocalTimeLevelVersion_jointlyMeasurable hB hBm hjoint T).aestronglyMeasurable)
    (brownianLocalTimeLevelVersion_weight_coe hB hBm hjoint T g)

theorem brownianLocalTimeLevelVersion_spatial_integrable_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    ∀ᵐ ω ∂P, Integrable (fun a => g a * brownianLocalTimeLevelVersion hB hBm hjoint T a ω) volume := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (brownianLocalTimeLevelVersion_weight_integrable hB hBm hjoint T hg).prod_left_ae

theorem brownianLocalTimeLevelVersion_integral_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    brownianTanakaLevelIntegral hB hBm hjoint T g =ᵐ[P]
      (fun ω => ∫ a, g a * brownianLocalTimeLevelVersion hB hBm hjoint T a ω) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact real_L2_integral_sections_ae (brownianTanakaCompensation_weight_integrable hB hBm hjoint T hg)
    (hg.aestronglyMeasurable.comp_fst.mul
      (brownianLocalTimeLevelVersion_jointlyMeasurable hB hBm hjoint T).aestronglyMeasurable)
    (brownianLocalTimeLevelVersion_weight_coe hB hBm hjoint T g)

theorem brownianLocalTimeLevelVersion_integral_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    MemLp (fun ω => ∫ a, g a * brownianLocalTimeLevelVersion hB hBm hjoint T a ω) 2 P :=
  (Lp.memLp (brownianTanakaLevelIntegral hB hBm hjoint T g)).ae_eq
    (brownianLocalTimeLevelVersion_integral_ae hB hBm hjoint T hg)

end TimeTraps.Probability
