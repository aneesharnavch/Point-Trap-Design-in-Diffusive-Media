module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovCylinderData

@[expose] public section

/-! Finite-dimensional strong Markov identities derived by tower and
pull-out from the actual one-time transition law. The final cylinder
uses the literal folded trajectory, with no future-path law premise. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

theorem reflectedMarkovCylinder_condExp (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (w : ReflectedMarkovWord L) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    brownianCompletedMeasure[(fun ω => reflectedMarkovCylinder L hL D x w (τ ω) ω) |
      hτ.measurableSpace] =ᵐ[brownianCompletedMeasure]
        (fun ω => reflectedMarkovObservation L hL D x (reflectedMarkovCylinderKernel L hL D w) (τ ω) ω) := by
  induction w generalizing τ with
  | nil =>
      simp only [reflectedMarkovCylinder, reflectedMarkovCylinderKernel,
        reflectedMarkovObservation_one, condExp_const hτ.measurableSpace_le]
      exact EventuallyEq.rfl
  | cons a w ih =>
      rcases a with ⟨h, f⟩
      have hσ := reflectedMarkovStoppingTime_add hτ h
      have hle : hτ.measurableSpace ≤ hσ.measurableSpace := by
        apply hτ.measurableSpace_mono hσ
        intro ω
        change (τ ω : WithTop ℝ≥0) ≤ ((τ ω + h : ℝ≥0) : WithTop ℝ≥0)
        exact WithTop.coe_le_coe.mpr (le_add_of_nonneg_right bot_le)
      have hfg : Integrable
          ((fun ω => reflectedMarkovObservation L hL D x f (τ ω + h) ω) *
            (fun ω => reflectedMarkovCylinder L hL D x w (τ ω + h) ω)) brownianCompletedMeasure :=
        reflectedMarkovCylinder_stopped_integrable L hL D x ((h, f) :: w) hτ
      have hce : brownianCompletedMeasure[
          (fun ω => reflectedMarkovCylinder L hL D x ((h, f) :: w) (τ ω) ω) |
          hσ.measurableSpace] =ᵐ[brownianCompletedMeasure]
          (fun ω => reflectedMarkovObservation L hL D x
            (f * reflectedMarkovCylinderKernel L hL D w) (τ ω + h) ω) := by
        exact (condExp_mul_of_stronglyMeasurable_left
          (reflectedMarkovObservation_stopped_stronglyMeasurable L hL D x f hσ) hfg
          (reflectedMarkovCylinder_stopped_integrable L hL D x w hσ)).trans
          (((EventuallyEq.rfl).mul (ih hσ)).trans (Eventually.of_forall (fun ω =>
            (reflectedMarkovObservation_mul L hL D x f (reflectedMarkovCylinderKernel L hL D w)
              (τ ω + h) ω).symm)))
      calc
        _ =ᵐ[brownianCompletedMeasure] brownianCompletedMeasure[
            brownianCompletedMeasure[
              (fun ω => reflectedMarkovCylinder L hL D x ((h, f) :: w) (τ ω) ω) |
              hσ.measurableSpace] | hτ.measurableSpace] :=
          (condExp_condExp_of_le hle hσ.measurableSpace_le).symm
        _ =ᵐ[brownianCompletedMeasure] brownianCompletedMeasure[
            (fun ω => reflectedMarkovObservation L hL D x
              (f * reflectedMarkovCylinderKernel L hL D w) (τ ω + h) ω) | hτ.measurableSpace] :=
          condExp_congr_ae hce
        _ =ᵐ[brownianCompletedMeasure] _ :=
          reflectedMarkovObservation_stopping_condExp L hL D hD x
            (f * reflectedMarkovCylinderKernel L hL D w) h hτ

def foldedTrajectoryFutureCylinder (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    ReflectedMarkovWord L → ℝ≥0 → BrownianCompletedSample → ℝ
  | [], _, _ => 1
  | (h, f) :: w, t, ω => reflectedFellerExtension L hL f
      (foldedTrajectory L D x brownianDyadicPath (t + h) ω) *
        foldedTrajectoryFutureCylinder L hL D x w (t + h) ω

theorem foldedTrajectoryFutureCylinder_ae (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ (w : ReflectedMarkovWord L) (t : ℝ≥0),
      foldedTrajectoryFutureCylinder L hL D x w t ω = reflectedMarkovCylinder L hL D x w t ω := by
  filter_upwards [foldedTrajectory_completed_observation_ae L hL D x] with ω hω
  intro w
  induction w with
  | nil => exact fun _ => rfl
  | cons a w ih =>
      rcases a with ⟨h, f⟩
      intro t
      exact congrArg₂ (fun a b : ℝ => a * b) (hω f (t + h)) (ih (t + h))

theorem foldedTrajectoryFutureCylinder_stopped_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (w : ReflectedMarkovWord L)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    Integrable (fun ω => foldedTrajectoryFutureCylinder L hL D x w (τ ω) ω)
      brownianCompletedMeasure :=
  (reflectedMarkovCylinder_stopped_integrable L hL D x w hτ).congr
    ((foldedTrajectoryFutureCylinder_ae L hL D x).mono (fun ω hω => (hω w (τ ω)).symm))

theorem foldedTrajectoryFutureCylinder_strongMarkov
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (w : ReflectedMarkovWord L)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    brownianCompletedMeasure[(fun ω => foldedTrajectoryFutureCylinder L hL D x w (τ ω) ω) |
      hτ.measurableSpace] =ᵐ[brownianCompletedMeasure]
        (fun ω => reflectedFellerExtension L hL (reflectedMarkovCylinderKernel L hL D w)
          (foldedTrajectory L D x brownianDyadicPath (τ ω) ω)) :=
  (condExp_congr_ae ((foldedTrajectoryFutureCylinder_ae L hL D x).mono
    (fun ω hω => hω w (τ ω)))).trans
      ((reflectedMarkovCylinder_condExp L hL D hD x w hτ).trans
        ((foldedTrajectory_completed_observation_ae L hL D x).mono
          (fun ω hω => (hω (reflectedMarkovCylinderKernel L hL D w) (τ ω)).symm)))

end TimeTraps.Probability

end
