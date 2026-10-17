module

public import TimeTraps.Probability.BrownianIntegralElementary
public import TimeTraps.Analysis.HilbertGramExtensionClosure

@[expose] public section

/-! The stochastic integral is a bounded linear isometry on the actual
L² closure of elementary adapted processes. The domain is explicitly this
closed span; no density claim in a larger predictable process space is made. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def brownianIntegralStepSpace (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) (P : Measure Ω) :
    Submodule ℝ (Lp ℝ 2 ((volume : Measure ℝ).prod P)) :=
  Submodule.span ℝ (Set.range (fun a : BrownianIntegralElementary B hBm P => a.processL2))

def brownianIntegralSpace (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) (P : Measure Ω) :
    Submodule ℝ (Lp ℝ 2 ((volume : Measure ℝ).prod P)) :=
  (brownianIntegralStepSpace B hBm P).topologicalClosure

variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

def brownianIntegralGenerator (a : BrownianIntegralElementary B hBm P) :
    brownianIntegralSpace B hBm P :=
  TimeTraps.Analysis.gramClosureGenerator
    (fun a : BrownianIntegralElementary B hBm P => a.processL2) a

def brownianIntegral (hB : IsPreBrownianReal B P) :
    brownianIntegralSpace B hBm P →ₗᵢ[ℝ] Lp ℝ 2 P :=
  TimeTraps.Analysis.gramClosureIsometry
    (fun a : BrownianIntegralElementary B hBm P => a.processL2)
    (fun a : BrownianIntegralElementary B hBm P => a.integralL2 hB)
    (BrownianIntegralElementary.gram_eq hB)

theorem brownianIntegral_generator (hB : IsPreBrownianReal B P)
    (a : BrownianIntegralElementary B hBm P) :
    brownianIntegral hB (brownianIntegralGenerator a) = a.integralL2 hB :=
  TimeTraps.Analysis.gramClosureIsometry_generator _ _ _ a

theorem brownianIntegral_norm (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) :
    ‖brownianIntegral hB f‖ = ‖(f : Lp ℝ 2 ((volume : Measure ℝ).prod P))‖ :=
  (brownianIntegral hB).norm_map f

theorem brownianIntegral_isometry (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) :
    (∫ ω, (brownianIntegral hB f) ω ^ 2 ∂P) =
      ∫ p, (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2 ∂volume.prod P := by
  calc
    _ = inner ℝ (brownianIntegral hB f) (brownianIntegral hB f) := by
      rw [L2.inner_def]
      simp only [Real.inner_apply, pow_two]
    _ = inner ℝ (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))
        (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :=
      (brownianIntegral hB).inner_map_map f f
    _ = _ := by rw [L2.inner_def]; simp only [Real.inner_apply, pow_two]

theorem brownianIntegral_unique (hB : IsPreBrownianReal B P)
    (J : brownianIntegralSpace B hBm P →L[ℝ] Lp ℝ 2 P)
    (hJ : ∀ a, J (brownianIntegralGenerator a) = a.integralL2 hB) :
    J = (brownianIntegral hB).toContinuousLinearMap :=
  TimeTraps.Analysis.gramClosureIsometry_unique _ _ _ J hJ

abbrev BrownianIntegrand :=
  brownianIntegralSpace brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure

def brownianStochasticIntegral : BrownianIntegrand →ₗᵢ[ℝ] Lp ℝ 2 brownianDyadicMeasure :=
  brownianIntegral brownianDyadicPath_isPreBrownianReal

theorem brownianStochasticIntegral_isometry (f : BrownianIntegrand) :
    (∫ ω, brownianStochasticIntegral f ω ^ 2 ∂brownianDyadicMeasure) =
      ∫ p, (f : Lp ℝ 2 ((volume : Measure ℝ).prod brownianDyadicMeasure)) p ^ 2
        ∂volume.prod brownianDyadicMeasure :=
  brownianIntegral_isometry brownianDyadicPath_isPreBrownianReal f

end TimeTraps.Probability

end
