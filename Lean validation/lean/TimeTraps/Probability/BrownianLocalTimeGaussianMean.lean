module

public import TimeTraps.Probability.BrownianLocalTimeGaussianKernel
public import TimeTraps.Probability.BrownianOccupationL1Integrability
public import TimeTraps.Probability.BrownianLocalTimeTimeRegularity

@[expose] public section

/-! The mean of the actual Tanaka compensation equals the time integral
of the Gaussian density at the fixed level. The proof takes the mean of
the proved smooth corrections and passes through their actual L² limit.
No occupation-mean or Revuz identity is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaSmoothCompensation_gaussian_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, brownianTanakaSmoothCompensation hB hBm hjoint a T n ω ∂P) =
      ∫ s in (0 : ℝ)..T.val,
        ∫ y, tanakaOccupationKernel (tanakaSmoothingScale n) y * gaussianPDFReal 0 s.toNNReal (a - y) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hk : Integrable (fun z => tanakaOccupationKernel (tanakaSmoothingScale n) (z - a)) :=
    (tanakaOccupationKernel_integrable (tanakaSmoothingScale_pos n)).comp_sub_right a
  have hi := brownian_time_L1_integrable hB hjoint T hk
  calc
    _ = ∫ ω, (∫ s in Ioc (0 : ℝ) T.val,
        tanakaOccupationKernel (tanakaSmoothingScale n) (B s.toNNReal ω - a)) ∂P := by
      apply integral_congr_ae
      filter_upwards [brownianTanakaSmoothCompensation_kernel_coe hB hBm hjoint a T n] with ω hω
      rw [hω]
      exact intervalIntegral.integral_of_le T.coe_nonneg
    _ = ∫ s in Ioc (0 : ℝ) T.val, ∫ ω,
        tanakaOccupationKernel (tanakaSmoothingScale n) (B s.toNNReal ω - a) ∂P :=
      (integral_integral_swap hi).symm
    _ = ∫ s in Ioc (0 : ℝ) T.val,
        ∫ y, tanakaOccupationKernel (tanakaSmoothingScale n) y * gaussianPDFReal 0 s.toNNReal (a - y) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hm : AEStronglyMeasurable
          (fun z => tanakaOccupationKernel (tanakaSmoothingScale n) (z - a))
          (gaussianReal 0 s.toNNReal) :=
        (((tanakaOccupationKernel_continuous (tanakaSmoothingScale_pos n)).measurable).comp
          (measurable_id.sub_const a)).aestronglyMeasurable
      exact ((hB.hasLaw_eval s.toNNReal).integral_comp hm).trans
        (gaussian_tanaka_kernel_integral (tanakaSmoothingScale_pos n) 0 a (Real.toNNReal_pos.mpr hs.1))
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem brownianTanakaCompensation_gaussian_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    (∫ ω, brownianTanakaCompensation hB hBm hjoint a T ω ∂P) =
      ∫ s in (0 : ℝ)..T.val, gaussianPDFReal 0 s.toNNReal a := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let oneL2 : Lp ℝ 2 P := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P univ) (1 : ℝ)
  have he (U : Lp ℝ 2 P) : inner ℝ oneL2 U = ∫ ω, U ω ∂P := by
    simpa only [Measure.restrict_univ] using
      L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top P univ) U
  have hmean : Tendsto (fun n => ∫ ω, brownianTanakaSmoothCompensation hB hBm hjoint a T n ω ∂P)
      atTop (𝓝 (∫ ω, brownianTanakaCompensation hB hBm hjoint a T ω ∂P)) := by
    have hh : Tendsto (fun n => inner ℝ oneL2 (brownianTanakaSmoothCompensation hB hBm hjoint a T n))
        atTop (𝓝 (inner ℝ oneL2 (brownianTanakaCompensation hB hBm hjoint a T))) :=
      (innerSL ℝ oneL2).continuous.continuousAt.tendsto.comp
        (brownianTanakaSmoothCompensation_tendsto hB hBm hjoint a T)
    simpa only [he] using hh
  have hkernel := gaussian_tanaka_kernel_time_tendsto tanakaSmoothingScale_pos
    tanakaSmoothingScale_tendsto 0 a T
  have hmean' : Tendsto (fun n => ∫ ω, brownianTanakaSmoothCompensation hB hBm hjoint a T n ω ∂P)
      atTop (𝓝 (∫ s in (0 : ℝ)..T.val, gaussianPDFReal 0 s.toNNReal a)) := by
    simpa only [brownianTanakaSmoothCompensation_gaussian_mean hB hBm hjoint a T] using hkernel
  exact tendsto_nhds_unique hmean hmean'

theorem brownianLocalTimeTimeField_gaussian_mean (a : ℝ) (T : ℝ≥0) :
    (∫ ω, brownianLocalTimeTimeField a T ω ∂brownianDyadicMeasure) =
      ∫ s in (0 : ℝ)..T.val, gaussianPDFReal 0 s.toNNReal a := by
  rw [integral_congr_ae (brownianLocalTimeTimeField_compensation_ae a T)]
  exact brownianTanakaCompensation_gaussian_mean brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable a T

end TimeTraps.Probability
