module

public import TimeTraps.Probability.MartingaleExponentialConditional

@[expose] public section

/-! Removing deterministic exponential discount from a continuous
martingale by genuine conditional Fubini. The candidate process retains
its original raw adaptation; no completed-filtration modification is used. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M N : ℝ≥0 → Ω → ℝ}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem martingale_exponential_unweight (hM : Martingale M ℱ μ)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) (hN : StronglyAdapted ℱ N)
    (he : ∀ t, N t =ᵐ[μ] (fun ω => Real.exp (t : ℝ) * M t ω -
      ∫ r in (0 : ℝ)..(t : ℝ), Real.exp r * M r.toNNReal ω)) :
    Martingale N ℱ μ := by
  have hpi (s t : ℝ≥0) := martingale_exponential_product_integrable hM hc s t
  have hNi (t : ℝ≥0) : Integrable (N t) μ := by
    have hi := (hpi 0 t).integral_prod_right
    simp only [NNReal.coe_zero] at hi
    have hh := ((hM.integrable t).const_mul (Real.exp (t : ℝ))).sub hi
    exact hh.congr ((he t).symm.mono (fun ω hω => by
      simpa only [Pi.sub_apply, intervalIntegral.integral_of_le t.coe_nonneg] using hω))
  refine ⟨hN, fun s t hst => ?_⟩
  let I : Ω → ℝ := fun ω => ∫ r in (s : ℝ)..(t : ℝ), Real.exp r * M r.toNNReal ω
  have hIi : Integrable I μ := by
    simpa only [I, intervalIntegral.integral_of_le (show (s : ℝ) ≤ (t : ℝ) from hst)]
      using (hpi s t).integral_prod_right
  have hrel : N t =ᵐ[μ] N s +
      ((Real.exp (t : ℝ)) • M t - (Real.exp (s : ℝ)) • M s) - I := by
    filter_upwards [he s, he t, (hpi 0 s).prod_left_ae, (hpi s t).prod_left_ae] with ω hs ht h0s hstint
    have h0s' : IntervalIntegrable (fun r => Real.exp r * M r.toNNReal ω) volume 0 (s : ℝ) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le s.coe_nonneg]
      change Integrable (fun r => Real.exp r * M r.toNNReal ω) (volume.restrict (Ioc 0 (s : ℝ)))
      simpa only [NNReal.coe_zero] using h0s
    have hst' : IntervalIntegrable (fun r => Real.exp r * M r.toNNReal ω) volume (s : ℝ) (t : ℝ) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (s : ℝ) ≤ (t : ℝ) from hst)]
      exact hstint
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0s' hst'
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [I]
    rw [hs, ht, ← hadd]
    ring
  have hJ := condExp_sub ((hM.integrable t).smul (Real.exp (t : ℝ)))
    ((hM.integrable s).smul (Real.exp (s : ℝ))) (ℱ s)
  have hsum := condExp_add (hNi s)
    (((hM.integrable t).smul (Real.exp (t : ℝ))).sub ((hM.integrable s).smul (Real.exp (s : ℝ)))) (ℱ s)
  have hsub := condExp_sub ((hNi s).add
    (((hM.integrable t).smul (Real.exp (t : ℝ))).sub ((hM.integrable s).smul (Real.exp (s : ℝ))))) hIi (ℱ s)
  have hNs : μ[N s | ℱ s] = N s := condExp_of_stronglyMeasurable (ℱ.le s) (hN s) (hNi s)
  have hMt := condExp_smul (μ := μ) (Real.exp (t : ℝ)) (M t) (ℱ s)
  have hMs := condExp_smul (μ := μ) (Real.exp (s : ℝ)) (M s) (ℱ s)
  have hcI := martingale_exponential_integral_condExp hM hc hst
  filter_upwards [condExp_congr_ae (m := ℱ s) hrel, hsub, hsum, hJ, hMt, hMs,
    hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s), hcI] with ω hr hsub hsum hj hmt hms htm hsm hi
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hsub hsum hj hmt hms
  rw [hr, hsub, hsum, hj, hmt, hms, htm, hsm, hNs]
  change N s ω + (Real.exp (t : ℝ) * M s ω - Real.exp (s : ℝ) * M s ω) - μ[I | ℱ s] ω = N s ω
  rw [hi]
  ring

end TimeTraps.Probability
