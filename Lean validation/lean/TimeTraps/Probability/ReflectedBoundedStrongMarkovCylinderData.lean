module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkov
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-! Finite future observations and their actual iterated Feller kernels.
Durations may be zero. Bounds and integrability are proved for every
finite stopping time, before deriving the cylinder conditional law. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

abbrev ReflectedMarkovWord (L : ℝ) := List (ℝ≥0 × C(Icc (0 : ℝ) L, ℝ))

def reflectedMarkovCylinder (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    ReflectedMarkovWord L → ℝ≥0 → BrownianCompletedSample → ℝ
  | [], _, _ => 1
  | (h, f) :: w, t, ω => reflectedMarkovObservation L hL D x f (t + h) ω *
      reflectedMarkovCylinder L hL D x w (t + h) ω

def reflectedMarkovCylinderKernel (L : ℝ) (hL : 0 < L) (D : ℝ) :
    ReflectedMarkovWord L → C(Icc (0 : ℝ) L, ℝ)
  | [] => 1
  | (h, f) :: w => reflectedFellerTimeOperator L hL D h.val
      (f * reflectedMarkovCylinderKernel L hL D w)

def reflectedMarkovCylinderBound {L : ℝ} : ReflectedMarkovWord L → ℝ
  | [] => 1
  | (_, f) :: w => ‖f‖ * reflectedMarkovCylinderBound w

theorem reflectedMarkovCylinderBound_nonneg {L : ℝ} (w : ReflectedMarkovWord L) :
    0 ≤ reflectedMarkovCylinderBound w := by
  induction w with
  | nil => exact zero_le_one
  | cons a w ih => exact mul_nonneg (norm_nonneg a.2) ih

theorem reflectedMarkovCylinder_bound (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (w : ReflectedMarkovWord L) (t : ℝ≥0) (ω : BrownianCompletedSample) :
    ‖reflectedMarkovCylinder L hL D x w t ω‖ ≤ reflectedMarkovCylinderBound w := by
  induction w generalizing t with
  | nil => exact le_of_eq norm_one
  | cons a w ih =>
      rcases a with ⟨h, f⟩
      change ‖reflectedMarkovObservation L hL D x f (t + h) ω *
        reflectedMarkovCylinder L hL D x w (t + h) ω‖ ≤ ‖f‖ * reflectedMarkovCylinderBound w
      rw [norm_mul]
      exact mul_le_mul (reflectedMarkovObservation_bound L hL D x f _ ω) (ih _)
        (norm_nonneg _) (norm_nonneg _)

theorem reflectedMarkovCylinderKernel_bound (L : ℝ) (hL : 0 < L) (D : ℝ)
    (w : ReflectedMarkovWord L) :
    ‖reflectedMarkovCylinderKernel L hL D w‖ ≤ reflectedMarkovCylinderBound w := by
  induction w with
  | nil =>
      let : Nonempty (Icc (0 : ℝ) L) := ⟨⟨0, le_rfl, hL.le⟩⟩
      exact le_of_eq norm_one
  | cons a w ih =>
      rcases a with ⟨h, f⟩
      exact (reflectedFellerOperator_contraction L hL _ _).trans
        ((norm_mul_le f _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg f)))

theorem reflectedMarkovCylinder_stopped_stronglyMeasurable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (w : ReflectedMarkovWord L)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    StronglyMeasurable (fun ω => reflectedMarkovCylinder L hL D x w (τ ω) ω) := by
  induction w generalizing τ with
  | nil => exact stronglyMeasurable_const
  | cons a w ih =>
      rcases a with ⟨h, f⟩
      have hσ := reflectedMarkovStoppingTime_add hτ h
      exact ((reflectedMarkovObservation_stopped_stronglyMeasurable L hL D x f hσ).mono
        hσ.measurableSpace_le).mul (ih hσ)

theorem reflectedMarkovCylinder_stopped_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (w : ReflectedMarkovWord L)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => reflectedMarkovCylinder L hL D x w (τ ω) ω) brownianCompletedMeasure := by
  apply (integrable_const (reflectedMarkovCylinderBound w)).mono'
    (reflectedMarkovCylinder_stopped_stronglyMeasurable L hL D x w hτ).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => reflectedMarkovCylinder_bound L hL D x w _ ω)

theorem reflectedMarkovObservation_mul (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f g : C(Icc (0 : ℝ) L, ℝ)) (t : ℝ≥0) (ω : BrownianCompletedSample) :
    reflectedMarkovObservation L hL D x (f * g) t ω =
      reflectedMarkovObservation L hL D x f t ω * reflectedMarkovObservation L hL D x g t ω := rfl

theorem reflectedMarkovObservation_one (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (t : ℝ≥0) (ω : BrownianCompletedSample) :
    reflectedMarkovObservation L hL D x 1 t ω = 1 := rfl

end TimeTraps.Probability

end
