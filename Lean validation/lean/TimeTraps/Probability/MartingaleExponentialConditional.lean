module

public import TimeTraps.Probability.MartingaleExponentialData

@[expose] public section

/-! Conditional Fubini for the exponential time integral of a genuine
martingale. All product integrability is derived from its terminal L1 norm. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem martingale_exponential_integral_condExp (hM : Martingale M ℱ μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    μ[fun ω => ∫ r in (s : ℝ)..(t : ℝ), Real.exp r * M r.toNNReal ω | ℱ s] =ᵐ[μ]
      (fun ω => (Real.exp (t : ℝ) - Real.exp (s : ℝ)) * M s ω) := by
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  let F : ℝ × Ω → ℝ := fun q => Real.exp q.1 * M q.1.toNNReal q.2
  let G : ℝ × Ω → ℝ := fun q => Real.exp q.1 * M s q.2
  have hFi : Integrable F (ν.prod μ) := martingale_exponential_product_integrable hM hc s t
  have hei : Integrable Real.exp ν := Real.continuous_exp.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hGi : Integrable G (ν.prod μ) := hei.mul_prod (hM.integrable s)
  have hGm : @StronglyMeasurable (ℝ × Ω) ℝ _ ((borel ℝ).prod (ℱ s)) G := by
    let : MeasurableSpace Ω := ℱ s
    exact (Real.continuous_exp.stronglyMeasurable.comp_measurable measurable_fst).mul
      ((hM.stronglyAdapted s).comp_measurable measurable_snd)
  have hs : ∀ᵐ r ∂ν, μ[fun ω => F (r, ω) | ℱ s] =ᵐ[μ] (fun ω => G (r, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hsr : s ≤ r.toNNReal := by
      change (s : ℝ) ≤ (r.toNNReal : ℝ)
      rw [Real.coe_toNNReal r (s.coe_nonneg.trans hr.1.le)]
      exact hr.1.le
    have hm := condExp_smul (μ := μ) (Real.exp r) (M r.toNNReal) (ℱ s)
    have hh := (hM.condExp_ae_eq hsr).mono (fun ω hω => congrArg (fun z => Real.exp r * z) hω)
    filter_upwards [hm, hh] with ω hm hh
    simp only [Pi.smul_apply, smul_eq_mul] at hm
    exact hm.trans hh
  have hh := condExp_integral_sections (ℱ.le s) hFi hGi hGm hs
  have he : (fun ω => ∫ r, G (r, ω) ∂ν) =
      (fun ω => (Real.exp (t : ℝ) - Real.exp (s : ℝ)) * M s ω) := by
    funext ω
    change (∫ r in Ioc (s : ℝ) (t : ℝ), Real.exp r * M s ω) = _
    rw [← intervalIntegral.integral_of_le (show (s : ℝ) ≤ (t : ℝ) from hst),
      intervalIntegral.integral_mul_const, integral_exp]
  rw [he] at hh
  simpa only [intervalIntegral.integral_of_le (show (s : ℝ) ≤ (t : ℝ) from hst)] using hh

end TimeTraps.Probability
