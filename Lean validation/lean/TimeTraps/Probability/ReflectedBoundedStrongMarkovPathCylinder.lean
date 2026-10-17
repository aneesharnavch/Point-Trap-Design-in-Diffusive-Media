module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovPathMeasure
public import TimeTraps.Probability.ReflectedBoundedStrongMarkovAbsolute

@[expose] public section

/-! The continuous future-path products have the already proved stopping
law. Fresh paths use a separate Brownian coordinate; full product
integrability is derived before interchanging the two integrals. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction

def reflectedMarkovPathWord {L : ℝ} {H : ℝ≥0}
    (w : List (Icc (0 : ℝ≥0) H × C(Icc (0 : ℝ) L, ℝ))) : ReflectedMarkovWord L :=
  w.map (fun a => (a.1.val, a.2))

theorem reflectedMarkovPathProduct_future (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    (w : List (Icc (0 : ℝ≥0) H × C(Icc (0 : ℝ) L, ℝ)))
    (τ : BrownianCompletedSample → ℝ≥0) (ω : BrownianCompletedSample) :
    reflectedMarkovPathProduct L H w (reflectedMarkovFuturePath L hL D x H τ ω) =
      reflectedMarkovAbsoluteCylinder L hL D x (reflectedMarkovPathWord w) (τ ω) ω := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [reflectedMarkovPathProduct, List.map_cons, List.prod_cons,
        BoundedContinuousFunction.mul_apply, reflectedMarkovPathWord,
        reflectedMarkovAbsoluteCylinder] at ih ⊢
      rw [ih]
      rfl

theorem reflectedMarkovPathProduct_continuation (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    (w : List (Icc (0 : ℝ≥0) H × C(Icc (0 : ℝ) L, ℝ)))
    (τ : BrownianCompletedSample → ℝ≥0) (q : BrownianCompletedSample × BrownianCompletedSample) :
    reflectedMarkovPathProduct L H w (reflectedMarkovContinuationPath L hL D x H τ q) =
      reflectedMarkovAbsoluteCylinder L hL D
        (reflectedMarkovState L hL D x (τ q.1) q.1).val (reflectedMarkovPathWord w) 0 q.2 :=
  reflectedMarkovPathProduct_future L hL D _ H w (fun _ => 0) q.2

theorem reflectedMarkovContinuationPath_test_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (ν : Measure BrownianCompletedSample) [IsFiniteMeasure ν]
    (g : ReflectedMarkovPath L H →ᵇ ℝ) :
    Integrable (fun q => g (reflectedMarkovContinuationPath L hL D x H τ q))
      (ν.prod brownianCompletedMeasure) := by
  apply (integrable_const ‖g‖).mono'
    (g.continuous.measurable.comp
      (reflectedMarkovContinuationPath_measurable L hL D x H hτ)).aestronglyMeasurable
  exact Eventually.of_forall (fun q => g.norm_coe_le_norm _)

theorem reflectedMarkovPathProduct_setIntegral (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (H : ℝ≥0)
    (w : List (Icc (0 : ℝ≥0) H × C(Icc (0 : ℝ) L, ℝ)))
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set BrownianCompletedSample} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, reflectedMarkovPathProduct L H w
      (reflectedMarkovFuturePath L hL D x H τ ω) ∂brownianCompletedMeasure) =
      ∫ q, reflectedMarkovPathProduct L H w
        (reflectedMarkovContinuationPath L hL D x H τ q)
        ∂((brownianCompletedMeasure.restrict A).prod brownianCompletedMeasure) := by
  rw [integral_prod _ (reflectedMarkovContinuationPath_test_integrable L hL D x H hτ
    (brownianCompletedMeasure.restrict A) (reflectedMarkovPathProduct L H w))]
  have he := reflectedMarkovAbsoluteCylinder_condExp L hL D hD x (reflectedMarkovPathWord w) hτ
  calc
    _ = ∫ ω in A, reflectedMarkovObservation L hL D x
        (reflectedMarkovAbsoluteKernel L hL D (reflectedMarkovPathWord w)) (τ ω) ω
          ∂brownianCompletedMeasure := by
      simp only [reflectedMarkovPathProduct_future]
      exact (setIntegral_condExp hτ.measurableSpace_le
        (reflectedMarkovAbsoluteCylinder_integrable L hL D x (reflectedMarkovPathWord w) hτ) hA).symm.trans
          (integral_congr_ae (he.filter_mono ae_restrict_le))
    _ = _ := by
      apply integral_congr_ae
      refine Eventually.of_forall (fun ω => ?_)
      simp only [reflectedMarkovPathProduct_continuation]
      exact (reflectedMarkovAbsoluteCylinder_expectation L hL D hD
        (reflectedMarkovState L hL D x (τ ω) ω) (reflectedMarkovPathWord w)).symm

end TimeTraps.Probability

end
