module

public import TimeTraps.Probability.ReflectedCosineDynkinData
public import TimeTraps.Probability.ConditionalIntegralFactor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Conditional integration of the actual Neumann cosine trajectory.
The exponential compensator identity is division-free, so the constant
mode and equal times are included. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem exponential_decay_integral_identity (a s t : ℝ) :
    Real.exp (-a * (t - s)) + a * (∫ r in s..t, Real.exp (-a * (r - s))) = 1 := by
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => Real.exp (-a * (r - s)))
      (-a * Real.exp (-a * (r - s))) r := by
    have h := ((((hasDerivAt_id r).sub_const s).const_mul (-a)).exp)
    simp only [id_eq, mul_one] at h
    exact h.congr_deriv (mul_comm _ _)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r)
    (show IntervalIntegrable (fun r : ℝ => -a * Real.exp (-a * (r - s))) volume s t from
      (by fun_prop : Continuous (fun r : ℝ => -a * Real.exp (-a * (r - s)))).intervalIntegrable s t)
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [sub_self, mul_zero, Real.exp_zero] at hi
  linarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedCosine_drift_increment_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (n : ℕ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => brownianItoDrift B (reflectedCosineInput L D x n) t ω -
      brownianItoDrift B (reflectedCosineInput L D x n) s ω | brownianNaturalFiltration B hBm s] =ᵐ[P]
      (fun ω => (∫ r in s.val..t.val,
        Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (r - s.val))) *
          reflectedCosineInput L D x n (B s ω)) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let g := reflectedCosineInput L D x n
  let ν : Measure ℝ := volume.restrict (Ioc s.val t.val)
  let F : ℝ × Ω → ℝ := fun p => g (B p.1.toNNReal p.2)
  have hg := reflectedCosineInput_lipschitz L D x n
  have hFm : Measurable F := hg.continuous.measurable.comp
    (hjoint.comp ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd))
  have hF : Integrable F (ν.prod P) := by
    apply (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
    filter_upwards [] with p
    simpa only [Real.norm_eq_abs] using reflectedCosineInput_bound L D x n (B p.1.toNNReal p.2)
  have hYm : StronglyMeasurable[brownianNaturalFiltration B hBm s] (fun ω => g (B s ω)) :=
    hg.continuous.comp_stronglyMeasurable (brownianNaturalFiltration_stronglyAdapted B hBm s)
  have hYi : Integrable (fun ω => g (B s ω)) P :=
    (brownianLipschitz_eval_memLp hB hg s).integrable (by norm_num)
  have hcond : ∀ᵐ r ∂ν, P[fun ω => F (r, ω) | brownianNaturalFiltration B hBm s] =ᵐ[P]
      (fun ω => Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (r - s.val)) * g (B s ω)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have hr0 : 0 ≤ r := s.coe_nonneg.trans hr.1.le
    have he : r.toNNReal.val = r := Real.coe_toNNReal r hr0
    have hsr : s ≤ r.toNNReal := show s.val ≤ r.toNNReal.val from hr.1.le.trans_eq he.symm
    simpa only [he] using reflectedCosineInput_condExp hB hBm L hL D hD x n hsr
  have hc := condExp_integral_factor ((brownianNaturalFiltration B hBm).le s) hF hYi hYm hcond
  have hid (ω : Ω) : (∫ r, F (r, ω) ∂ν) = brownianItoDrift B g t ω - brownianItoDrift B g s ω := by
    have hs := brownianItoDrift_bounded_intervalIntegrable hg.continuous.measurable hjoint
      (reflectedCosineInput_bound L D x n) s ω
    have ht := brownianItoDrift_bounded_intervalIntegrable hg.continuous.measurable hjoint
      (reflectedCosineInput_bound L D x n) t ω
    have ha := intervalIntegral.integral_add_adjacent_intervals hs (hs.symm.trans ht)
    have hv : (∫ r, F (r, ω) ∂ν) = ∫ r in s.val..t.val, g (B r.toNNReal ω) :=
      (intervalIntegral.integral_of_le (show s.val ≤ t.val from hst)).symm
    rw [hv]
    change (∫ r in s.val..t.val, g (B r.toNNReal ω)) =
      (∫ r in (0 : ℝ)..t.val, g (B r.toNNReal ω)) - ∫ r in (0 : ℝ)..s.val, g (B r.toNNReal ω)
    linarith
  have hk : (∫ r, Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (r - s.val)) ∂ν) =
      ∫ r in s.val..t.val, Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (r - s.val)) :=
    (intervalIntegral.integral_of_le (show s.val ≤ t.val from hst)).symm
  simpa only [hid, hk] using hc

end TimeTraps.Probability
