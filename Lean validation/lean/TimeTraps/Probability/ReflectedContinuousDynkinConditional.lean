module

public import TimeTraps.Probability.ReflectedContinuousDynkinData
public import TimeTraps.Probability.ConditionalIntegral
public import TimeTraps.Probability.BrownianOccupationTimeBound

@[expose] public section

/-! Conditional Fubini for the genuine time integral of every continuous
observable on the reflecting interval. The conditional integrand is
jointly measurable in elapsed time and the original Brownian past. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

set_option maxHeartbeats 400000 in
theorem reflectedContinuous_drift_increment_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => brownianItoDrift B (reflectedContinuousInput L hL D x f) t ω -
      brownianItoDrift B (reflectedContinuousInput L hL D x f) s ω |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
      (fun ω => ∫ r in s.val..t.val, reflectedContinuousInput L hL D x
        (reflectedFellerTimeOperator L hL D (r - s.val) f) (B s ω)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let g := reflectedContinuousInput L hL D x f
  let ν : Measure ℝ := volume.restrict (Ioc s.val t.val)
  let F : ℝ × Ω → ℝ := fun p => g (B p.1.toNNReal p.2)
  let G : ℝ × Ω → ℝ := fun p => reflectedContinuousInput L hL D x
    (reflectedFellerTimeOperator L hL D (p.1 - s.val) f) (B s p.2)
  have hg := reflectedContinuousInput_continuous L hL D x f
  have hb := reflectedContinuousInput_bound L hL D x f
  have hFm : Measurable F := hg.measurable.comp
    (hjoint.comp ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd))
  have hF : Integrable F (ν.prod P) := by
    apply (integrable_const ‖f‖).mono' hFm.aestronglyMeasurable
    exact Eventually.of_forall (fun p => hb _)
  have hGc := reflectedContinuousInput_time_continuous L hL D x f
  have hGm : @StronglyMeasurable (ℝ × Ω) ℝ _
      (MeasurableSpace.prod inferInstance (brownianNaturalFiltration B hBm s)) G := by
    have hs := (brownianNaturalFiltration_stronglyAdapted B hBm s).measurable
    let : MeasurableSpace Ω := brownianNaturalFiltration B hBm s
    exact (hGc.measurable.comp ((measurable_fst.sub_const s.val).prodMk
      (hs.comp measurable_snd))).stronglyMeasurable
  have hprod : MeasurableSpace.prod (inferInstance : MeasurableSpace ℝ)
      (brownianNaturalFiltration B hBm s) ≤ MeasurableSpace.prod inferInstance mΩ :=
    sup_le_sup le_rfl (MeasurableSpace.comap_mono ((brownianNaturalFiltration B hBm).le s))
  have hGambient : Measurable G := hGm.measurable.mono hprod le_rfl
  have hG : Integrable G (ν.prod P) := by
    apply (integrable_const ‖f‖).mono' hGambient.aestronglyMeasurable
    filter_upwards [] with p
    change |reflectedContinuousInput L hL D x
      (reflectedFellerTimeOperator L hL D (p.1 - s.val) f) (B s p.2)| ≤ ‖f‖
    exact reflectedContinuousInput_time_bound L hL D x f (p.1 - s.val) (B s p.2)
  have hcond : ∀ᵐ r ∂ν, P[fun ω => F (r, ω) | brownianNaturalFiltration B hBm s] =ᵐ[P]
      (fun ω => G (r, ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have he : r.toNNReal.val = r := Real.coe_toNNReal r (s.coe_nonneg.trans hr.1.le)
    have hsr : s ≤ r.toNNReal := show s.val ≤ r.toNNReal.val from hr.1.le.trans_eq he.symm
    simpa only [he] using reflectedContinuousInput_condExp hB hBm L hL D hD x f hsr
  have hc := condExp_integral_sections (α := ℝ) (Ω := Ω) (mα := inferInstance)
    (mΩ := mΩ) (m := brownianNaturalFiltration B hBm s) (ν := ν) (P := P) (F := F) (G := G)
    ((brownianNaturalFiltration B hBm).le s) hF hG hGm hcond
  have hid (ω : Ω) : (∫ r, F (r, ω) ∂ν) = brownianItoDrift B g t ω - brownianItoDrift B g s ω := by
    have hs := brownianItoDrift_bounded_intervalIntegrable hg.measurable hjoint hb s ω
    have ht := brownianItoDrift_bounded_intervalIntegrable hg.measurable hjoint hb t ω
    have ha := intervalIntegral.integral_add_adjacent_intervals hs (hs.symm.trans ht)
    have hv : (∫ r, F (r, ω) ∂ν) = ∫ r in s.val..t.val, g (B r.toNNReal ω) :=
      (intervalIntegral.integral_of_le (show s.val ≤ t.val from hst)).symm
    rw [hv]
    change (∫ r in s.val..t.val, g (B r.toNNReal ω)) =
      (∫ r in (0 : ℝ)..t.val, g (B r.toNNReal ω)) - ∫ r in (0 : ℝ)..s.val, g (B r.toNNReal ω)
    linarith
  have hik (ω : Ω) : (∫ r, G (r, ω) ∂ν) = ∫ r in s.val..t.val,
      reflectedContinuousInput L hL D x (reflectedFellerTimeOperator L hL D (r - s.val) f) (B s ω) :=
    (intervalIntegral.integral_of_le (show s.val ≤ t.val from hst)).symm
  simpa only [hid, hik] using hc

end TimeTraps.Probability
