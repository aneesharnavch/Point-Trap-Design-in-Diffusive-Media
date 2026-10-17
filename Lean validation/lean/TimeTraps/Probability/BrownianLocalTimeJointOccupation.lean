module

public import TimeTraps.Analysis.L2IntegralSectionsFinite
public import TimeTraps.Probability.BrownianLocalTimeJointVersion
public import TimeTraps.Probability.BrownianOccupationL1Extension
public import TimeTraps.Probability.BrownianLocalTimeLevelIntegral

@[expose] public section

/-! Scalar L¹ weights give absolutely integrable ordinary spatial
sections of the jointly measurable level/time/outcome version. Their actual
integrals represent the previously constructed L²-valued Bochner
integral. The justification uses finite-measure L² bounds, not a
uniform pointwise bound in the sample. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianLocalTimeJointVersion_weight_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (g : ℝ → ℝ) (a : ℝ) :
    (g a • brownianTanakaCompensation hB hBm hjoint a T : Lp ℝ 2 P) =ᵐ[P]
      (fun ω => g a * brownianLocalTimeJointVersion hB hBm hjoint a T ω) := by
  filter_upwards [Lp.coeFn_smul (g a) (brownianTanakaCompensation hB hBm hjoint a T),
    brownianLocalTimeJointVersion_ae hB hBm hjoint a T] with ω hs he
  rw [hs, Pi.smul_apply, smul_eq_mul, he]

theorem brownianLocalTimeJointVersion_weight_integrable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    Integrable (fun p : ℝ × Ω => g p.1 * brownianLocalTimeJointVersion hB hBm hjoint p.1 T p.2)
      (volume.prod P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact real_L2_sections_integrable (brownianTanakaCompensation_weight_integrable hB hBm hjoint T hg)
    (hg.aestronglyMeasurable.comp_fst.mul
      (brownianLocalTimeJointVersion_timeSlice_measurable hB hBm hjoint T).aestronglyMeasurable)
    (brownianLocalTimeJointVersion_weight_coe hB hBm hjoint T g)

theorem brownianLocalTimeJointVersion_spatial_integrable_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    ∀ᵐ ω ∂P, Integrable (fun a => g a * brownianLocalTimeJointVersion hB hBm hjoint a T ω) volume := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (brownianLocalTimeJointVersion_weight_integrable hB hBm hjoint T hg).prod_left_ae

theorem brownianLocalTimeJointVersion_integral_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    brownianTanakaLevelIntegral hB hBm hjoint T g =ᵐ[P]
      (fun ω => ∫ a, g a * brownianLocalTimeJointVersion hB hBm hjoint a T ω) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact real_L2_integral_sections_ae (brownianTanakaCompensation_weight_integrable hB hBm hjoint T hg)
    (hg.aestronglyMeasurable.comp_fst.mul
      (brownianLocalTimeJointVersion_timeSlice_measurable hB hBm hjoint T).aestronglyMeasurable)
    (brownianLocalTimeJointVersion_weight_coe hB hBm hjoint T g)

theorem brownianLocalTimeJointVersion_integral_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    MemLp (fun ω => ∫ a, g a * brownianLocalTimeJointVersion hB hBm hjoint a T ω) 2 P :=
  (Lp.memLp (brownianTanakaLevelIntegral hB hBm hjoint T g)).ae_eq
    (brownianLocalTimeJointVersion_integral_ae hB hBm hjoint T hg)

theorem brownianLocalTimeJointVersion_occupation_L1_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    (fun ω => ∫ a, g a * brownianLocalTimeJointVersion hB hBm hjoint a T ω) =ᵐ[P]
      (fun ω => ∫ s in (0 : ℝ)..T.val, g (B s.toNNReal ω)) :=
  (brownianLocalTimeJointVersion_integral_ae hB hBm hjoint T hg).symm.trans
    (brownianTanakaLevelIntegral_occupation_L1_ae hB hBm hjoint T hg)

theorem brownianDyadicLocalTimeJointVersion_occupation_L1_ae (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    (fun ω => ∫ a, g a * brownianDyadicLocalTimeJointVersion a T ω) =ᵐ[brownianDyadicMeasure]
      (fun ω => ∫ s in (0 : ℝ)..T.val, g (brownianDyadicPath s.toNNReal ω)) :=
  brownianLocalTimeJointVersion_occupation_L1_ae brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable T hg

end TimeTraps.Probability
