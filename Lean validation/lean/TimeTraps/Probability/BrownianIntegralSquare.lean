module

public import TimeTraps.Probability.BrownianIntegralSquareApproximation
public import TimeTraps.Probability.BrownianIntegralSquareLimit

@[expose] public section

/-! The quadratic Ito identity for the actual Brownian integrand. The
domain element is the product-L2 class of 1_(0,T](s) B_s, whose membership
in the closed elementary span is proved by left-grid approximation. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSquareProcessL2_mem (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    brownianSquareProcessL2 hB hjoint T ∈ brownianIntegralSpace B hBm P := by
  have hc : IsClosed (brownianIntegralSpace B hBm P : Set (Lp ℝ 2 ((volume : Measure ℝ).prod P))) :=
    (brownianIntegralStepSpace B hBm P).isClosed_topologicalClosure
  exact hc.mem_of_tendsto (brownianSquareStep_process_tendsto hB hBm hjoint T)
    (Filter.Eventually.of_forall (fun n => (brownianSquareStepIntegrand hB hBm T n).property))

noncomputable def brownianSquareIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    brownianIntegralSpace B hBm P :=
  ⟨brownianSquareProcessL2 hB hjoint T, brownianSquareProcessL2_mem hB hBm hjoint T⟩

theorem brownianSquareIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    (brownianSquareIntegrand hB hBm hjoint T : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      brownianSquareProcess B T :=
  brownianSquareProcessL2_coe hB hjoint T

/-- The quadratic Ito identity as equality in the actual output L2 space. -/
theorem brownianIntegral_square (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    brownianIntegral hB (brownianSquareIntegrand hB hBm hjoint T) = brownianSquareTarget hB T := by
  have hi : Tendsto (fun n => brownianSquareStepIntegrand hB hBm T n) atTop
      (𝓝 (brownianSquareIntegrand hB hBm hjoint T)) := by
    apply tendsto_subtype_rng.mpr
    exact brownianSquareStep_process_tendsto hB hBm hjoint T
  exact tendsto_nhds_unique ((brownianIntegral hB).continuous.continuousAt.tendsto.comp hi)
    (brownianSquareStep_integral_tendsto hB hBm T)

noncomputable def brownianIdentityIntegrand (T : ℝ≥0) : BrownianIntegrand :=
  brownianSquareIntegrand brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T

/-- For the constructed Brownian process, the coefficient is B_s on (0,T]. -/
theorem brownianIdentityIntegrand_coe (T : ℝ≥0) :
    (brownianIdentityIntegrand T : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure))
      =ᵐ[volume.prod brownianDyadicMeasure] brownianSquareProcess brownianDyadicPath T :=
  brownianSquareIntegrand_coe brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T

theorem brownianStochasticIntegral_square (T : ℝ≥0) :
    brownianStochasticIntegral (brownianIdentityIntegrand T) =
      brownianSquareTarget brownianDyadicPath_isPreBrownianReal T :=
  brownianIntegral_square brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable T

theorem brownianStochasticIntegral_square_ae (T : ℝ≥0) :
    brownianStochasticIntegral (brownianIdentityIntegrand T) =ᵐ[brownianDyadicMeasure]
      fun ω => (brownianDyadicPath T ω ^ 2 - T.val) / 2 := by
  rw [brownianStochasticIntegral_square]
  exact brownianSquareTarget_coe brownianDyadicPath_isPreBrownianReal T

end TimeTraps.Probability
