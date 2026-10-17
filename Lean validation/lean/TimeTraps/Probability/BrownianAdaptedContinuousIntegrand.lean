module

public import TimeTraps.Probability.BrownianAdaptedContinuousApproximation
public import TimeTraps.Probability.BrownianAdaptedContinuousStep

@[expose] public section

/-! Every uniformly bounded, raw Brownian-adapted process with ambient
joint measurability and almost-sure continuous paths belongs, after finite
time cutoff, to the actual closed integrand space. Membership is derived
from the concrete dyadic elementary sums, not from a predictable-density
assumption. Its stochastic integral is the canonical completed integral. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B H : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {M : ℝ≥0}

def brownianAdaptedContinuousProcessL2 (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) : Lp ℝ 2 ((volume : Measure ℝ).prod P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (brownianAdaptedContinuous_cutoff_memLp hjoint hb T).toLp (brownianSquareProcess H T)

theorem brownianAdaptedContinuousProcessL2_coe (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) :
    brownianAdaptedContinuousProcessL2 hB hjoint hb T =ᵐ[volume.prod P] brownianSquareProcess H T := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact (brownianAdaptedContinuous_cutoff_memLp hjoint hb T).coeFn_toLp

theorem brownianAdaptedContinuous_mem_integralSpace (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0) :
    brownianAdaptedContinuousProcessL2 hB hjoint hb T ∈ brownianIntegralSpace B hBm P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hconv := brownianAdaptedContinuous_L2_tendsto hjoint hb hcont T
    (fun n => (brownianAdaptedContinuousStepIntegrand hB hBm hH hb T n :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)))
    (brownianAdaptedContinuousProcessL2 hB hjoint hb T)
    (brownianAdaptedContinuousStepIntegrand_coe hB hBm hH hb T)
    (brownianAdaptedContinuousProcessL2_coe hB hjoint hb T)
  have hc : IsClosed (brownianIntegralSpace B hBm P : Set (Lp ℝ 2 ((volume : Measure ℝ).prod P))) :=
    (brownianIntegralStepSpace B hBm P).isClosed_topologicalClosure
  exact hc.mem_of_tendsto hconv (Filter.Eventually.of_forall (fun n =>
    (brownianAdaptedContinuousStepIntegrand hB hBm hH hb T n).property))

def brownianAdaptedContinuousIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0) : brownianIntegralSpace B hBm P :=
  ⟨brownianAdaptedContinuousProcessL2 hB hjoint hb T,
    brownianAdaptedContinuous_mem_integralSpace hB hBm hH hjoint hb hcont T⟩

theorem brownianAdaptedContinuousIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0) :
    (brownianAdaptedContinuousIntegrand hB hBm hH hjoint hb hcont T :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] brownianSquareProcess H T :=
  brownianAdaptedContinuousProcessL2_coe hB hjoint hb T

theorem brownianAdaptedContinuousStepIntegrand_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0) :
    Tendsto (fun n => brownianAdaptedContinuousStepIntegrand hB hBm hH hb T n) atTop
      (𝓝 (brownianAdaptedContinuousIntegrand hB hBm hH hjoint hb hcont T)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply tendsto_subtype_rng.mpr
  exact brownianAdaptedContinuous_L2_tendsto hjoint hb hcont T _ _
    (brownianAdaptedContinuousStepIntegrand_coe hB hBm hH hb T)
    (brownianAdaptedContinuousIntegrand_coe hB hBm hH hjoint hb hcont T)

def brownianAdaptedContinuousIntegral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0) : Lp ℝ 2 P :=
  brownianIntegral hB (brownianAdaptedContinuousIntegrand hB hBm hH hjoint hb hcont T)

theorem brownianAdaptedContinuousStepIntegral_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hb : ∀ t ω, |H t ω| ≤ M.val)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) (T : ℝ≥0) :
    Tendsto (fun n => brownianIntegral hB (brownianAdaptedContinuousStepIntegrand hB hBm hH hb T n))
      atTop (𝓝 (brownianAdaptedContinuousIntegral hB hBm hH hjoint hb hcont T)) :=
  (brownianIntegral hB).continuous.continuousAt.tendsto.comp
    (brownianAdaptedContinuousStepIntegrand_tendsto hB hBm hH hjoint hb hcont T)

end TimeTraps.Probability

end
