module

public import TimeTraps.Probability.ReflectedBrownianTransition
public import TimeTraps.Probability.ReflectedFellerIntegral

@[expose] public section

/-! Continuous observables on the closed reflecting interval, evaluated
along the actual affine Brownian input. The conditional evolution is the
actual reflected Feller operator, including a zero elapsed time. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

def reflectedContinuousInput (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (z : ℝ) : ℝ :=
  reflectedFellerExtension L hL f (x + Real.sqrt (2 * D) * z)

theorem reflectedContinuousInput_continuous (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) : Continuous (reflectedContinuousInput L hL D x f) :=
  (reflectedFellerExtension L hL f).continuous.comp (by fun_prop)

theorem reflectedContinuousInput_bound (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (z : ℝ) : |reflectedContinuousInput L hL D x f z| ≤ ‖f‖ :=
  reflectedFellerExtension_bound L hL f _

theorem reflectedContinuousInput_folded {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0) (ω : Ω) :
    reflectedFellerExtension L hL f (foldedTrajectory L D x B t ω) =
      reflectedContinuousInput L hL D x f (B t ω) :=
  reflectedFellerExtension_on_interval L hL f
    (reflectedIntervalFold L hL (x + Real.sqrt (2 * D) * B t ω))

theorem reflectedContinuousInput_time_continuous (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    Continuous (fun p : ℝ × ℝ => reflectedContinuousInput L hL D x
      (reflectedFellerTimeOperator L hL D p.1 f) p.2) := by
  change Continuous (fun p : ℝ × ℝ => (reflectedFellerTimeOperator L hL D p.1 f)
    (reflectedIntervalFold L hL (x + Real.sqrt (2 * D) * p.2)))
  exact continuous_eval.comp (((reflectedFellerTimeOperator_continuous L hL D f).comp
    continuous_fst).prodMk ((reflectedIntervalFold L hL).continuous.comp (by fun_prop)))

theorem reflectedContinuousInput_time_bound (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (r z : ℝ) :
    |reflectedContinuousInput L hL D x (reflectedFellerTimeOperator L hL D r f) z| ≤ ‖f‖ :=
  (reflectedContinuousInput_bound L hL D x _ z).trans
    (reflectedFellerOperator_contraction L hL _ f)

theorem reflectedContinuousInput_condExp {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => reflectedContinuousInput L hL D x f (B t ω) |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
      (fun ω => reflectedContinuousInput L hL D x
        (reflectedFellerTimeOperator L hL D (t.val - s.val) f) (B s ω)) := by
  have h := foldedTrajectory_condExp hB hBm L hL D hD x hst
    (reflectedFellerExtension L hL f).continuous.measurable
    (reflectedFellerExtension_bound L hL f)
  have hv : Real.toNNReal (2 * D) * (t - s) = Real.toNNReal (2 * D * (t.val - s.val)) := by
    apply NNReal.eq
    rw [NNReal.coe_mul, NNReal.coe_sub hst, Real.coe_toNNReal _ (by positivity),
      Real.coe_toNNReal _ (mul_nonneg (by positivity) (sub_nonneg.mpr hst))]
    rfl
  have he (ω : Ω) : (∫ y, reflectedFellerExtension L hL f y ∂reflectedGaussianLaw L
      (foldedTrajectory L D x B s ω) (Real.toNNReal (2 * D) * (t - s))) =
      reflectedContinuousInput L hL D x (reflectedFellerTimeOperator L hL D (t.val - s.val) f)
        (B s ω) := by
    rw [hv]
    exact (reflectedFellerOperator_kernel L hL _ f
      (reflectedIntervalFold L hL (x + Real.sqrt (2 * D) * B s ω))).symm
  simpa only [reflectedContinuousInput_folded, he] using h

end TimeTraps.Probability

end
