module

public import TimeTraps.Probability.ReflectedFellerLaplace
public import TimeTraps.Probability.ReflectedBrownianMarginal
public import TimeTraps.Probability.BrownianJointMeasurability
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Genuine discounted payoffs of the constructed folded Brownian path.
The bounded continuous observable and exponential discount establish
integrability on every sample path and on the full time/sample product. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set

def reflectedDiscountedPayoff (L : ℝ) (hL : 0 < L) (D α : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (x t : ℝ) (ω : ℕ → ℝ) : ℝ :=
  Real.exp (-α * t) * reflectedFellerExtension L hL f
    (foldedTrajectory L D x brownianDyadicPath t.toNNReal ω)

theorem reflectedDiscountedPayoff_measurable (L : ℝ) (hL : 0 < L) (D α : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) :
    Measurable (Function.uncurry (reflectedDiscountedPayoff L hL D α f x)) := by
  have hb := (foldedTrajectory_joint_measurable L D x brownianDyadicPath
    brownianDyadicPath_jointly_measurable).comp
      ((by fun_prop : Measurable (fun p : ℝ × (ℕ → ℝ) => p.1.toNNReal)).prodMk measurable_snd)
  exact (by fun_prop : Measurable (fun p : ℝ × (ℕ → ℝ) => Real.exp (-α * p.1))).mul
    ((reflectedFellerExtension L hL f).continuous.measurable.comp hb)

theorem reflectedDiscountedPayoff_bound (L : ℝ) (hL : 0 < L) (D α : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (x t : ℝ) (ω : ℕ → ℝ) :
    ‖reflectedDiscountedPayoff L hL D α f x t ω‖ ≤ Real.exp (-α * t) * ‖f‖ := by
  rw [reflectedDiscountedPayoff, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (reflectedFellerExtension_bound L hL f _) (Real.exp_pos _).le

theorem reflectedDiscountedPayoff_path_integrable (L : ℝ) (hL : 0 < L) (D : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) (ω : ℕ → ℝ) :
    IntegrableOn (fun t => reflectedDiscountedPayoff L hL D α f x t ω) (Ioi 0) := by
  apply ((exp_neg_integrableOn_Ioi 0 hα).mul_const ‖f‖).mono'
    ((reflectedDiscountedPayoff_measurable L hL D α f x).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => reflectedDiscountedPayoff_bound L hL D α f x t ω)

theorem reflectedDiscountedPayoff_joint_integrable (L : ℝ) (hL : 0 < L) (D : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) :
    Integrable (Function.uncurry (reflectedDiscountedPayoff L hL D α f x))
      ((volume.restrict (Ioi 0)).prod brownianDyadicMeasure) := by
  apply (((exp_neg_integrableOn_Ioi 0 hα).mul_const ‖f‖).comp_fst brownianDyadicMeasure).mono'
    (reflectedDiscountedPayoff_measurable L hL D α f x).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => reflectedDiscountedPayoff_bound L hL D α f x p.1 p.2)

theorem reflectedDiscountedPayoff_integral_integrable (L : ℝ) (hL : 0 < L) (D : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (x : ℝ) :
    Integrable (fun ω => ∫ t in Ioi (0 : ℝ), reflectedDiscountedPayoff L hL D α f x t ω)
      brownianDyadicMeasure :=
  (reflectedDiscountedPayoff_joint_integrable L hL D hα f x).integral_prod_right

end TimeTraps.Probability

end
