module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

@[expose] public section

/-! Adding one absorbing cemetery state to a subprobability kernel.
The lost mass is retained explicitly; no stochastic process is assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

noncomputable def cemeteryMeasure (μ : Measure α) : Measure (α ⊕ Unit) :=
  μ.map Sum.inl + (1 - μ univ) • Measure.dirac (Sum.inr ())

theorem cemeteryMeasure_apply (μ : Measure α) {A : Set (α ⊕ Unit)} (hA : MeasurableSet A) :
    cemeteryMeasure μ A = μ (Sum.inl ⁻¹' A) +
      (1 - μ univ) * A.indicator (fun _ => 1) (Sum.inr ()) := by
  rw [cemeteryMeasure, Measure.add_apply, Measure.map_apply measurable_inl hA,
    Measure.smul_apply, Measure.dirac_apply' _ hA]
  rfl

theorem cemeteryMeasure_mass (μ : Measure α) (hμ : μ univ ≤ 1) :
    cemeteryMeasure μ univ = 1 := by
  rw [cemeteryMeasure_apply μ MeasurableSet.univ]
  simp only [preimage_univ, indicator_univ, mul_one]
  exact add_tsub_cancel_of_le hμ

noncomputable def cemeteryKernel (κ : Kernel α α) : Kernel (α ⊕ Unit) (α ⊕ Unit) where
  toFun := Sum.elim (fun x => cemeteryMeasure (κ x)) (fun _ => Measure.dirac (Sum.inr ()))
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    apply measurable_fun_sum
    · change Measurable (fun x => cemeteryMeasure (κ x) A)
      simp_rw [cemeteryMeasure_apply _ hA]
      exact (κ.measurable_coe (measurable_inl hA)).add
        ((measurable_const.sub (κ.measurable_coe MeasurableSet.univ)).mul measurable_const)
    · exact measurable_const

theorem cemeteryKernel_live (κ : Kernel α α) (x : α) :
    cemeteryKernel κ (Sum.inl x) = cemeteryMeasure (κ x) := rfl

theorem cemeteryKernel_dead (κ : Kernel α α) :
    cemeteryKernel κ (Sum.inr ()) = Measure.dirac (Sum.inr ()) := rfl

theorem cemeteryKernel_isMarkov (κ : Kernel α α) (hκ : ∀ x, κ x univ ≤ 1) :
    IsMarkovKernel (cemeteryKernel κ) := by
  constructor
  intro x
  constructor
  cases x with
  | inl x => exact cemeteryMeasure_mass (κ x) (hκ x)
  | inr u =>
    cases u
    simp only [cemeteryKernel_dead, Measure.dirac_apply_of_mem (mem_univ _)]

theorem cemeteryMeasure_lintegral (μ : Measure α) {f : α ⊕ Unit → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂cemeteryMeasure μ) =
      (∫⁻ x, f (Sum.inl x) ∂μ) + (1 - μ univ) * f (Sum.inr ()) := by
  rw [cemeteryMeasure, lintegral_add_measure, lintegral_map hf measurable_inl,
    lintegral_smul_measure, lintegral_dirac' _ hf]
  rfl

end TimeTraps.Probability
