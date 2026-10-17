module

public import TimeTraps.Probability.ConditionalIntegralFactor

@[expose] public section

/-! Conditional Fubini for actual integrable sections, with an explicit
jointly measurable version of their conditional means in the raw
conditioning sigma algebra. -/

namespace TimeTraps.Probability

open MeasureTheory Filter
open scoped ENNReal

variable {α Ω : Type*} [mα : MeasurableSpace α] {m mΩ : MeasurableSpace Ω}
variable {ν : Measure α} {P : Measure Ω} [SFinite ν] [IsFiniteMeasure P]

theorem condExp_integral_sections (hm : m ≤ mΩ) {F G : α × Ω → ℝ}
    (hF : Integrable F (ν.prod P)) (hG : Integrable G (ν.prod P))
    (hGm : @StronglyMeasurable (α × Ω) ℝ _ (mα.prod m) G)
    (hcond : ∀ᵐ a ∂ν, P[fun ω => F (a, ω) | m] =ᵐ[P] (fun ω => G (a, ω))) :
    P[fun ω => ∫ a, F (a, ω) ∂ν | m] =ᵐ[P] (fun ω => ∫ a, G (a, ω) ∂ν) := by
  have hgm : StronglyMeasurable[m] (fun ω => ∫ a, G (a, ω) ∂ν) := by
    let : MeasurableSpace Ω := m
    exact hGm.integral_prod_left' (μ := ν)
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hF.integral_prod_right
    (fun _ _ _ => hG.integral_prod_right.integrableOn) ?_
    ⟨_, hgm, EventuallyEq.rfl⟩).symm
  intro A hA _
  have hFA : Integrable F (ν.prod (P.restrict A)) :=
    hF.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hGA : Integrable G (ν.prod (P.restrict A)) :=
    hG.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    (∫ ω in A, ∫ a, G (a, ω) ∂ν ∂P) = ∫ a, ∫ ω in A, G (a, ω) ∂P ∂ν :=
      (integral_integral_swap (f := fun a ω => G (a, ω)) hGA).symm
    _ = ∫ a, ∫ ω in A, F (a, ω) ∂P ∂ν := by
      apply integral_congr_ae
      filter_upwards [hcond, hF.prod_right_ae] with a ha hi
      calc
        _ = ∫ ω in A, P[fun ω => F (a, ω) | m] ω ∂P :=
          integral_congr_ae (ae_restrict_of_ae ha.symm)
        _ = _ := setIntegral_condExp hm hi hA
    _ = ∫ ω in A, ∫ a, F (a, ω) ∂ν ∂P := integral_integral_swap hFA

end TimeTraps.Probability
