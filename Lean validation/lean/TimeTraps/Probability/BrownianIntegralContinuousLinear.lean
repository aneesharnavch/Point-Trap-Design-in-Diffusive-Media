module

public import TimeTraps.Probability.BrownianIntegralContinuousGlobal

@[expose] public section

/-! Finite linear combinations of actual continuous stochastic integrals
agree simultaneously at all times, on one event. Fixed-time L2 linearity
is extended by a countable dense set and everywhere path continuity. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped NNReal ENNReal

variable {ι : Type*}

theorem brownianIntegralGlobalPath_affine_sum_fixed_ae (f₀ : BrownianIntegrand)
    (s : Finset ι) (c : ι → ℝ) (f : ι → BrownianIntegrand) (t : ℝ≥0) :
    brownianIntegralGlobalPath (f₀ + ∑ i ∈ s, c i • f i) t =ᵐ[brownianDyadicMeasure]
      fun ω => brownianIntegralGlobalPath f₀ t ω + ∑ i ∈ s, c i * brownianIntegralGlobalPath (f i) t ω := by
  let I := brownianIntegralUpTo (hBm := brownianDyadicPath_measurable) brownianDyadicPath_isPreBrownianReal t
  have hsum : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i ∈ s,
      (c i • I (f i) : Lp ℝ 2 brownianDyadicMeasure) ω =
        c i * brownianIntegralGlobalPath (f i) t ω := by
    apply (eventually_all_finset s).mpr
    intro i _
    filter_upwards [Lp.coeFn_smul (c i) (I (f i)), brownianIntegralGlobalPath_integral_ae (f i) t]
      with ω hc hi
    rw [hc, Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun z => c i * z) hi.symm
  filter_upwards [brownianIntegralGlobalPath_integral_ae (f₀ + ∑ i ∈ s, c i • f i) t,
    brownianIntegralGlobalPath_integral_ae f₀ t,
    Lp.coeFn_add (I f₀) (∑ i ∈ s, c i • I (f i)),
    Lp.coeFn_fun_finsetSum s (fun i => c i • I (f i)), hsum] with ω he h₀ ha hs hc
  rw [he]
  change I (f₀ + ∑ i ∈ s, c i • f i) ω = _
  rw [map_add, map_sum]
  simp only [map_smul]
  rw [ha, Pi.add_apply, hs, ← h₀]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => hc i hi)

theorem brownianIntegralGlobalPath_affine_sum_ae (f₀ : BrownianIntegrand)
    (s : Finset ι) (c : ι → ℝ) (f : ι → BrownianIntegrand) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      brownianIntegralGlobalPath (f₀ + ∑ i ∈ s, c i • f i) t ω =
        brownianIntegralGlobalPath f₀ t ω + ∑ i ∈ s, c i * brownianIntegralGlobalPath (f i) t ω := by
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      brownianIntegralGlobalPath (f₀ + ∑ i ∈ s, c i • f i) (denseSeq ℝ≥0 n) ω =
        brownianIntegralGlobalPath f₀ (denseSeq ℝ≥0 n) ω +
          ∑ i ∈ s, c i * brownianIntegralGlobalPath (f i) (denseSeq ℝ≥0 n) ω :=
    ae_all_iff.mpr (fun n => brownianIntegralGlobalPath_affine_sum_fixed_ae f₀ s c f (denseSeq ℝ≥0 n))
  filter_upwards [hall] with ω hω
  have hr : Continuous (fun t : ℝ≥0 => brownianIntegralGlobalPath f₀ t ω +
      ∑ i ∈ s, c i * brownianIntegralGlobalPath (f i) t ω) := by
    apply (brownianIntegralGlobalPath_continuous f₀ ω).add
    exact continuous_finsetSum s (fun i _ => (brownianIntegralGlobalPath_continuous (f i) ω).const_mul (c i))
  have he := (denseRange_denseSeq ℝ≥0).equalizer
    (brownianIntegralGlobalPath_continuous _ ω) hr (funext hω)
  exact congrFun he

end TimeTraps.Probability
