module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Conditional integration with an explicitly factorized conditional
mean. Actual product integrability justifies the interchange over every
event in the conditioning sigma algebra. -/

namespace TimeTraps.Probability

open MeasureTheory Filter
open scoped ENNReal

variable {α Ω : Type*} [MeasurableSpace α] {m mΩ : MeasurableSpace Ω}
variable {ν : Measure α} {P : Measure Ω} [SFinite ν] [IsFiniteMeasure P]

theorem condExp_integral_factor (hm : m ≤ mΩ) {F : α × Ω → ℝ}
    (hF : Integrable F (ν.prod P)) {k : α → ℝ}
    {Y : Ω → ℝ} (hY : Integrable Y P) (hYm : StronglyMeasurable[m] Y)
    (hcond : ∀ᵐ a ∂ν, P[fun ω => F (a, ω) | m] =ᵐ[P] (fun ω => k a * Y ω)) :
    P[fun ω => ∫ a, F (a, ω) ∂ν | m] =ᵐ[P]
      (fun ω => (∫ a, k a ∂ν) * Y ω) := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hF.integral_prod_right
    (fun _ _ _ => (hY.const_mul _).integrableOn) ?_
    (hYm.const_mul _).aestronglyMeasurable).symm
  intro A hA _
  have hFA : Integrable F (ν.prod (P.restrict A)) :=
    hF.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    (∫ ω in A, (∫ a, k a ∂ν) * Y ω ∂P) =
        (∫ a, k a ∂ν) * (∫ ω in A, Y ω ∂P) := integral_const_mul _ _
    _ = ∫ a, k a * (∫ ω in A, Y ω ∂P) ∂ν := (integral_mul_const _ _).symm
    _ = ∫ a, ∫ ω in A, F (a, ω) ∂P ∂ν := by
      apply integral_congr_ae
      filter_upwards [hcond, hF.prod_right_ae] with a ha hi
      rw [← integral_const_mul]
      calc
        _ = ∫ ω in A, P[fun ω => F (a, ω) | m] ω ∂P :=
          integral_congr_ae (ae_restrict_of_ae ha.symm)
        _ = _ := setIntegral_condExp hm hi hA
    _ = ∫ ω in A, ∫ a, F (a, ω) ∂ν ∂P := integral_integral_swap hFA

end TimeTraps.Probability
