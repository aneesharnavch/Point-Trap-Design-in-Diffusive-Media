module

public import TimeTraps.Probability.ReflectedDiscountedData

@[expose] public section

/-! Conditional discounted continuation for the original raw Brownian
past. Infinite conditional Fubini is applied only after integrability of
both actual and conditional sections has been proved. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedDiscountedFuture_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (s : ℝ≥0) :
    P[reflectedDiscountedFuture B L hL D α x f s | brownianNaturalFiltration B hBm s] =ᵐ[P]
      (fun ω => reflectedContinuousInput L hL D x (reflectedFellerLaplace L hL D α f) (B s ω)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let ν : Measure ℝ := volume.restrict (Ioi s.val)
  let F : ℝ × Ω → ℝ := fun p => Real.exp (-α * (p.1 - s.val)) *
    reflectedContinuousInput L hL D x f (B p.1.toNNReal p.2)
  let G : ℝ × Ω → ℝ := fun p => Real.exp (-α * (p.1 - s.val)) *
    reflectedContinuousInput L hL D x (reflectedFellerTimeOperator L hL D (p.1 - s.val) f) (B s p.2)
  have hF : Integrable F (ν.prod P) :=
    reflectedDiscounted_future_joint_integrable B hjoint L hL D x hα f s
  have hGc := reflectedContinuousInput_time_continuous L hL D x f
  have hGm : @StronglyMeasurable (ℝ × Ω) ℝ _
      (MeasurableSpace.prod inferInstance (brownianNaturalFiltration B hBm s)) G := by
    have hs := (brownianNaturalFiltration_stronglyAdapted B hBm s).measurable
    let : MeasurableSpace Ω := brownianNaturalFiltration B hBm s
    exact ((by fun_prop : Measurable (fun p : ℝ × Ω => Real.exp (-α * (p.1 - s.val)))).mul
      (hGc.measurable.comp ((measurable_fst.sub_const s.val).prodMk (hs.comp measurable_snd)))).stronglyMeasurable
  have hprod : MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ)
      (brownianNaturalFiltration B hBm s) ≤ MeasurableSpace.prod inferInstance mΩ :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono ((brownianNaturalFiltration B hBm).le s))
  have hG : Integrable G (ν.prod P) := by
    apply (((reflectedDiscounted_exponential_integrable hα s.val).mul_const ‖f‖).comp_fst P).mono'
      (hGm.measurable.mono hprod le_rfl).aestronglyMeasurable
    filter_upwards [] with p
    change ‖Real.exp (-α * (p.1 - s.val)) * _‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (reflectedContinuousInput_time_bound L hL D x f (p.1 - s.val) (B s p.2)) (Real.exp_pos _).le
  have hcond : ∀ᵐ r ∂ν, P[fun ω => F (r, ω) | brownianNaturalFiltration B hBm s] =ᵐ[P]
      (fun ω => G (r, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have he : r.toNNReal.val = r := Real.coe_toNNReal r (s.coe_nonneg.trans hr.le)
    have hsr : s ≤ r.toNNReal := show s.val ≤ r.toNNReal.val from hr.le.trans_eq he.symm
    have hc := reflectedContinuousInput_condExp hB hBm L hL D hD x f hsr
    have hs := condExp_smul (μ := P) (Real.exp (-α * (r - s.val)))
      (fun ω => reflectedContinuousInput L hL D x f (B r.toNNReal ω))
      (brownianNaturalFiltration B hBm s)
    change P[Real.exp (-α * (r - s.val)) • (fun ω => reflectedContinuousInput L hL D x f (B r.toNNReal ω)) |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
      (Real.exp (-α * (r - s.val)) • fun ω => reflectedContinuousInput L hL D x
        (reflectedFellerTimeOperator L hL D (r - s.val) f) (B s ω))
    simpa only [he] using hs.trans (hc.const_smul (Real.exp (-α * (r - s.val))))
  have hc := condExp_integral_sections ((brownianNaturalFiltration B hBm).le s) hF hG hGm hcond
  have hi (ω : Ω) : (∫ r, G (r, ω) ∂ν) =
      reflectedContinuousInput L hL D x (reflectedFellerLaplace L hL D α f) (B s ω) := by
    change (∫ r in Ioi s.val, Real.exp (-α * (r - s.val)) * reflectedContinuousInput L hL D x
      (reflectedFellerTimeOperator L hL D (r - s.val) f) (B s ω)) = _
    exact (reflectedDiscounted_shift_integral s.val (fun r => Real.exp (-α * r) *
      reflectedContinuousInput L hL D x (reflectedFellerTimeOperator L hL D r f) (B s ω))).trans
      (reflectedFellerLaplace_apply L hL D hα f
        (reflectedIntervalFold L hL (x + Real.sqrt (2 * D) * B s ω))).symm
  filter_upwards [hc] with ω hω
  exact hω.trans (hi ω)

theorem reflectedDiscountedFuture_condExp_path (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (s : ℝ≥0) :
    P[fun ω => ∫ r in Ioi s.val, Real.exp (-α * (r - s.val)) *
      f ⟨foldedTrajectory L D x B r.toNNReal ω, foldedTrajectory_mem L hL D x B r.toNNReal ω⟩ |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
      (fun ω => reflectedFellerLaplace L hL D α f
        ⟨foldedTrajectory L D x B s ω, foldedTrajectory_mem L hL D x B s ω⟩) := by
  exact reflectedDiscountedFuture_condExp hB hBm hjoint L hL D hD x hα f s

end TimeTraps.Probability
