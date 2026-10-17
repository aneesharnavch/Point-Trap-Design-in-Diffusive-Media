module

public import TimeTraps.Probability.ReflectedFellerIntegral
public import TimeTraps.Probability.ReflectedNeumannLaplace

@[expose] public section

/-! The actual continuous-function Laplace integral of the reflected
transition family. Exponential decay controls the infinite horizon, and
evaluation at every interval point commutes with this Bochner integral. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set

def reflectedFellerLaplace (L : ℝ) (hL : 0 < L) (D α : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) : C(Icc (0 : ℝ) L, ℝ) :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) • reflectedFellerTimeOperator L hL D t f

theorem reflectedFellerLaplace_integrable (L : ℝ) (hL : 0 < L) (D : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) :
    IntegrableOn (fun t : ℝ => Real.exp (-α * t) • reflectedFellerTimeOperator L hL D t f)
      (Ioi 0) := by
  have hc : Continuous (fun t : ℝ =>
      Real.exp (-α * t) • reflectedFellerTimeOperator L hL D t f) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (reflectedFellerTimeOperator_continuous L hL D f)
  apply ((exp_neg_integrableOn_Ioi 0 hα).mul_const ‖f‖).mono' hc.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (reflectedFellerOperator_contraction L hL (2 * D * t).toNNReal f) (Real.exp_pos _).le

theorem reflectedFellerLaplace_norm_le (L : ℝ) (hL : 0 < L) (D : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) :
    ‖reflectedFellerLaplace L hL D α f‖ ≤ ‖f‖ / α := by
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ),
        ‖Real.exp (-α * t) • reflectedFellerTimeOperator L hL D t f‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * ‖f‖ := by
      apply integral_mono_ae (reflectedFellerLaplace_integrable L hL D hα f).norm
        ((exp_neg_integrableOn_Ioi 0 hα).mul_const ‖f‖)
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left
        (reflectedFellerOperator_contraction L hL (2 * D * t).toNNReal f) (Real.exp_pos _).le
    _ = _ := by
      rw [integral_mul_const, reflectedLaplace_exponential_integral hα, div_eq_mul_inv, mul_comm]

theorem reflectedFellerLaplace_apply (L : ℝ) (hL : 0 < L) (D : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) (x : Icc (0 : ℝ) L) :
    reflectedFellerLaplace L hL D α f x =
      ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * reflectedFellerTimeOperator L hL D t f x :=
  ContinuousMap.integral_apply (reflectedFellerLaplace_integrable L hL D hα f) x

theorem reflectedFellerLaplace_toL2 (L : ℝ) (hL : 0 < L) (D : ℝ)
    {α : ℝ} (hα : 0 < α) (f : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerToL2 L hL (reflectedFellerLaplace L hL D α f) =
      reflectedNeumannLaplace L hL D α (reflectedFellerToL2 L hL f) := by
  rw [reflectedFellerLaplace,
    ← (reflectedFellerToL2 L hL).integral_comp_comm
      (reflectedFellerLaplace_integrable L hL D hα f)]
  unfold reflectedNeumannLaplace
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [map_smul]
  congr 1
  exact (reflectedGaussianL2Operator_feller L hL (2 * D * t).toNNReal f).symm

end TimeTraps.Probability

end
