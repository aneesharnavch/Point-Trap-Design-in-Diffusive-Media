module

public import TimeTraps.Probability.ExponentialKillingSurvival
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Conditional expectation given the full path coordinate. The exponential
survival weight is obtained from product integration, independently of any
diffusion or regularity of a time-indexed clock. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem exponentialKilling_survival_indicator_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ℝ) (hA : Measurable A) :
    Integrable ((exponentialSurvivalEvent A).indicator (fun _ => (1 : ℝ)))
      (exponentialKillingMeasure μ) := by
  let _ := exponentialKilling_probability μ
  exact (integrable_const 1).indicator (exponentialSurvivalEvent_measurable A hA)

theorem exponentialKilling_survival_condExp (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ℝ) (hA : Measurable A) (hAnonneg : ∀ ω, 0 ≤ A ω) :
    (exponentialKillingMeasure μ)[(exponentialSurvivalEvent A).indicator (fun _ => (1 : ℝ)) |
      (inferInstance : MeasurableSpace Ω).comap (Prod.fst : Ω × ℝ → Ω)]
      =ᵐ[exponentialKillingMeasure μ] (fun p => Real.exp (-A p.1)) := by
  let _ := unitExponential_probability
  let _ := exponentialKilling_probability μ
  let f := (exponentialSurvivalEvent A).indicator (fun _ => (1 : ℝ))
  let g := fun p : Ω × ℝ => Real.exp (-A p.1)
  have hf : Integrable f (exponentialKillingMeasure μ) :=
    exponentialKilling_survival_indicator_integrable μ A hA
  have hg : Integrable g (exponentialKillingMeasure μ) := by
    apply (integrable_const (1 : ℝ)).mono' ((hA.comp measurable_fst).neg.exp.aestronglyMeasurable)
    exact Eventually.of_forall (fun p => by
      change ‖Real.exp (-A p.1)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hAnonneg p.1)))
  have hgm : StronglyMeasurable[(inferInstance : MeasurableSpace Ω).comap
      (Prod.fst : Ω × ℝ → Ω)] g :=
    (hA.neg.exp.comp (comap_measurable Prod.fst)).stronglyMeasurable
  apply (ae_eq_condExp_of_forall_setIntegral_eq measurable_fst.comap_le hf
    (fun _ _ _ => hg.integrableOn) ?_ hgm.aestronglyMeasurable).symm
  intro s hs _
  obtain ⟨B, hB, rfl⟩ := hs
  have hset : (Prod.fst : Ω × ℝ → Ω) ⁻¹' B = B ×ˢ (univ : Set ℝ) := by ext p; simp
  rw [hset]
  change (∫ p in B ×ˢ univ, g p ∂μ.prod (expMeasure 1)) =
    ∫ p in B ×ˢ univ, f p ∂μ.prod (expMeasure 1)
  rw [setIntegral_prod g hg.integrableOn, setIntegral_prod f hf.integrableOn]
  apply setIntegral_congr_fun hB
  intro ω _
  simp only [Measure.restrict_univ]
  have he : (fun e => f (ω, e)) = (Ioi (A ω)).indicator (fun _ => (1 : ℝ)) := by
    funext e
    rfl
  rw [he, integral_indicator measurableSet_Ioi, setIntegral_const, smul_eq_mul, mul_one,
    measureReal_def, unitExponential_tail _ (hAnonneg ω),
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  change (∫ _e, Real.exp (-A ω) ∂expMeasure 1) = Real.exp (-A ω)
  simp

end TimeTraps.Probability
