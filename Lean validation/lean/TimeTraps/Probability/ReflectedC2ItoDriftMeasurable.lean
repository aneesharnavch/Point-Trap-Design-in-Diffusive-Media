module

public import TimeTraps.Probability.BrownianItoDriftProcess

@[expose] public section

/-! Joint measurability of a literal ordinary time integral, with a variable
nonnegative upper endpoint. This is independent of Brownian motion. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set
open scoped NNReal ENNReal

theorem timeIntegral_jointlyMeasurable {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {H : ℝ × Ω → ℝ} (hH : Measurable H) :
    Measurable (fun p : ℝ≥0 × Ω => ∫ r in (0 : ℝ)..p.1.val, H (r, p.2)) := by
  let g : ℝ × (ℝ≥0 × Ω) → ℝ := fun p => H (p.1, p.2.2)
  have hg : Measurable g := hH.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  let A : Set (ℝ × (ℝ≥0 × Ω)) := {p | 0 < p.1 ∧ p.1 ≤ p.2.1.val}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst (by fun_prop))
  have hi : Measurable (fun p : ℝ≥0 × Ω => ∫ r : ℝ, A.indicator g (r, p)) :=
    ((hg.indicator hA).stronglyMeasurable.integral_prod_left' (μ := (volume : Measure ℝ))).measurable
  have he : (fun p : ℝ≥0 × Ω => ∫ r : ℝ, A.indicator g (r, p)) =
      (fun p : ℝ≥0 × Ω => ∫ r in (0 : ℝ)..p.1.val, H (r, p.2)) := by
    funext p
    calc
      _ = ∫ r in Ioc (0 : ℝ) p.1.val, H (r, p.2) := by
        change (∫ r : ℝ, (Ioc (0 : ℝ) p.1.val).indicator (fun r => H (r, p.2)) r) = _
        exact integral_indicator measurableSet_Ioc
      _ = _ := (intervalIntegral.integral_of_le p.1.coe_nonneg).symm
  exact he ▸ hi

end TimeTraps.Probability

end
