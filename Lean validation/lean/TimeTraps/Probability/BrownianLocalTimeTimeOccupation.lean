module

public import TimeTraps.Probability.BrownianLocalTimeTimeRegularity
public import TimeTraps.Probability.BrownianLocalTimeOccupationL1

@[expose] public section

/-! The jointly measurable field with continuous increasing time paths
has the actual ordinary occupation identity for every scalar L1 weight.
Spatial section integrability and L2 identification are proved, rather
than inferred from pointwise evaluation of a Bochner integral. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal

theorem brownianLocalTimeTimeField_weight_coe (T : ℝ≥0) (g : ℝ → ℝ) (a : ℝ) :
    (g a • brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable a T :
        Lp ℝ 2 brownianDyadicMeasure) =ᵐ[brownianDyadicMeasure]
      (fun ω => g a * brownianLocalTimeTimeField a T ω) := by
  filter_upwards [Lp.coeFn_smul (g a) (brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable a T),
    brownianLocalTimeTimeField_compensation_ae a T] with ω hs he
  rw [hs, Pi.smul_apply, smul_eq_mul, he]

theorem brownianLocalTimeTimeField_weight_integrable (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    Integrable (fun p : ℝ × (ℕ → ℝ) => g p.1 * brownianLocalTimeTimeField p.1 T p.2)
      (volume.prod brownianDyadicMeasure) :=
  real_L2_sections_integrable
    (brownianTanakaCompensation_weight_integrable brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable T hg)
    (hg.aestronglyMeasurable.comp_fst.mul
      (brownianLocalTimeTimeField_timeSlice_measurable T).aestronglyMeasurable)
    (brownianLocalTimeTimeField_weight_coe T g)

theorem brownianLocalTimeTimeField_spatial_integrable_ae (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    ∀ᵐ ω ∂brownianDyadicMeasure, Integrable (fun a => g a * brownianLocalTimeTimeField a T ω) volume :=
  (brownianLocalTimeTimeField_weight_integrable T hg).prod_left_ae

theorem brownianLocalTimeTimeField_integral_ae (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    brownianDyadicTanakaLevelIntegral T g =ᵐ[brownianDyadicMeasure]
      (fun ω => ∫ a, g a * brownianLocalTimeTimeField a T ω) := by
  have he := real_L2_integral_sections_ae
    (F := fun a => g a • brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable a T)
    (f := fun p : ℝ × (ℕ → ℝ) => g p.1 * brownianLocalTimeTimeField p.1 T p.2)
    (brownianTanakaCompensation_weight_integrable brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable T hg)
    (hg.aestronglyMeasurable.comp_fst.mul
      (brownianLocalTimeTimeField_timeSlice_measurable T).aestronglyMeasurable)
    (brownianLocalTimeTimeField_weight_coe T g)
  change brownianDyadicTanakaLevelIntegral T g =ᵐ[brownianDyadicMeasure]
    (fun ω => ∫ a, g a * brownianLocalTimeTimeField a T ω) at he
  exact he

theorem brownianLocalTimeTimeField_integral_memLp (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    MemLp (fun ω => ∫ a, g a * brownianLocalTimeTimeField a T ω) 2 brownianDyadicMeasure :=
  (Lp.memLp (brownianDyadicTanakaLevelIntegral T g)).ae_eq
    (brownianLocalTimeTimeField_integral_ae T hg)

theorem brownianLocalTimeTimeField_occupation_L1_ae (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g volume) :
    (fun ω => ∫ a, g a * brownianLocalTimeTimeField a T ω) =ᵐ[brownianDyadicMeasure]
      (fun ω => ∫ s in (0 : ℝ)..T.val, g (brownianDyadicPath s.toNNReal ω)) :=
  (brownianLocalTimeTimeField_integral_ae T hg).symm.trans
    (brownianTanakaLevelIntegral_occupation_L1_ae brownianDyadicPath_isPreBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable T hg)

end TimeTraps.Probability
