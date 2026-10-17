module

public import TimeTraps.Probability.BrownianIntegralClosure
public import Mathlib.Probability.Moments.Covariance

@[expose] public section

/-! Mean and covariance of the stochastic integral on its actual domain:
the L2 closed span of elementary adapted processes. Mean zero extends by
continuity of the L2 pairing with the constant function one. Covariance
is the product-measure pairing of the two integrands. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

theorem BrownianIntegralElementary.integralL2_mean (hB : IsPreBrownianReal B P)
    (a : BrownianIntegralElementary B hBm P) : (∫ ω, a.integralL2 hB ω ∂P) = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [integral_congr_ae (a.integralL2_coe hB)]
  exact brownian_weighted_increment_mean hB hBm a.ordered a.adapted
    (a.squareIntegrable.integrable (by norm_num))

/-- Every completed integrand has a mean-zero stochastic integral. -/
theorem brownianIntegral_mean (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) : (∫ ω, brownianIntegral hB f ω ∂P) = 0 := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let oneL2 : Lp ℝ 2 P := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top P univ) (1 : ℝ)
  let J : brownianIntegralSpace B hBm P →L[ℝ] ℝ :=
    (innerSL ℝ oneL2).comp (brownianIntegral hB).toContinuousLinearMap
  have hJ (g : brownianIntegralSpace B hBm P) : J g = ∫ ω, brownianIntegral hB g ω ∂P := by
    change inner ℝ oneL2 (brownianIntegral hB g) = _
    simpa only [setIntegral_univ] using
      L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top P univ) (brownianIntegral hB g)
  let inclusion : brownianIntegralStepSpace B hBm P →ₗᵢ[ℝ] brownianIntegralSpace B hBm P :=
    TimeTraps.Analysis.gramClosureInclusion
    (fun a : BrownianIntegralElementary B hBm P => a.processL2)
  have hs : ∀ v : brownianIntegralStepSpace B hBm P, J (inclusion v) = 0 := by
    have H : ∀ z hz, J (inclusion ⟨z, hz⟩) = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨a, rfl⟩ := hz
        change J (brownianIntegralGenerator a) = 0
        rw [hJ, brownianIntegral_generator, a.integralL2_mean hB]
      | zero =>
        change J (inclusion 0) = 0
        simp
      | add v w hv hw ihv ihw =>
        change J (inclusion (⟨v, hv⟩ + ⟨w, hw⟩)) = 0
        rw [map_add, map_add, ihv, ihw, add_zero]
      | smul a v hv ih =>
        change J (inclusion (a • ⟨v, hv⟩)) = 0
        rw [map_smul, map_smul, ih, smul_zero]
    intro v
    exact H v v.property
  rw [← hJ]
  exact (TimeTraps.Analysis.gramClosureInclusion_dense
    (fun a : BrownianIntegralElementary B hBm P => a.processL2)).induction_on f
      (isClosed_eq J.continuous continuous_const) hs

/-- Bilinear form of the stochastic integral isometry. -/
theorem brownianIntegral_pairing (hB : IsPreBrownianReal B P)
    (f g : brownianIntegralSpace B hBm P) :
    (∫ ω, brownianIntegral hB f ω * brownianIntegral hB g ω ∂P) =
      ∫ p, (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p *
        (g : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ∂volume.prod P := by
  calc
    _ = inner ℝ (brownianIntegral hB f) (brownianIntegral hB g) := by
      rw [L2.inner_def]
      simp only [Real.inner_apply]
    _ = inner ℝ (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))
        (g : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :=
      (brownianIntegral hB).inner_map_map f g
    _ = _ := by rw [L2.inner_def]; simp only [Real.inner_apply]

theorem brownianIntegral_covariance (hB : IsPreBrownianReal B P)
    (f g : brownianIntegralSpace B hBm P) :
    cov[brownianIntegral hB f, brownianIntegral hB g; P] =
      ∫ p, (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p *
        (g : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ∂volume.prod P := by
  simp only [covariance, brownianIntegral_mean, sub_zero]
  exact brownianIntegral_pairing hB f g

theorem brownianStochasticIntegral_mean (f : BrownianIntegrand) :
    (∫ ω, brownianStochasticIntegral f ω ∂brownianDyadicMeasure) = 0 :=
  brownianIntegral_mean brownianDyadicPath_isPreBrownianReal f

theorem brownianStochasticIntegral_covariance (f g : BrownianIntegrand) :
    cov[brownianStochasticIntegral f, brownianStochasticIntegral g; brownianDyadicMeasure] =
      ∫ p, (f : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) p *
        (g : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) p
          ∂volume.prod brownianDyadicMeasure :=
  brownianIntegral_covariance brownianDyadicPath_isPreBrownianReal f g

end TimeTraps.Probability
