module

public import TimeTraps.Probability.ReversibleResistanceSpeedSymmetry
public import Mathlib.Topology.ContinuousMap.Interval

@[expose] public section

/-! Speed invariance and reversibility for arbitrary functions continuous
on the original physical interval. Constant extension outside the interval
is used only internally; the conclusions retain the original functions. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Interval
open scoped NNReal Topology BoundedContinuousFunction

def reversibleResistanceContinuousExtension (A : IntervalMedium) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc A.source.left A.source.right)) : ℝ →ᵇ ℝ :=
  (BoundedContinuousFunction.mkOfCompact
    (⟨fun x => g x.val, hg.comp_continuous continuous_subtype_val (fun x => x.property)⟩ :
      C(Icc A.source.left A.source.right, ℝ))).compContinuous
        ⟨projIcc A.source.left A.source.right A.source.increasing.le, continuous_projIcc⟩

theorem reversibleResistanceContinuousExtension_eq (A : IntervalMedium) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc A.source.left A.source.right)) :
    EqOn (reversibleResistanceContinuousExtension A g hg) g (Icc A.source.left A.source.right) := by
  intro x hx
  change g (projIcc A.source.left A.source.right A.source.increasing.le x).val = g x
  rw [projIcc_of_mem A.source.increasing.le hx]

theorem reversibleResistanceTransition_congr_interval (A : IntervalMedium)
    {f g : ℝ → ℝ} (hfg : EqOn f g (Icc A.source.left A.source.right)) (t : ℝ≥0) (x : ℝ) :
    reversibleResistanceTransition A t f x = reversibleResistanceTransition A t g x :=
  integral_congr_ae (Eventually.of_forall (fun ω => hfg (reversibleResistancePath_mem A x t ω)))

theorem reversibleResistanceTransition_speed_symmetric_continuous (A : IntervalMedium)
    {f g : ℝ → ℝ} (hf : ContinuousOn f (Icc A.source.left A.source.right))
    (hg : ContinuousOn g (Icc A.source.left A.source.right)) (t : ℝ≥0) :
    (∫ x in A.source.left..A.source.right,
      A.source.density x * f x * reversibleResistanceTransition A t g x) =
      ∫ x in A.source.left..A.source.right,
        A.source.density x * g x * reversibleResistanceTransition A t f x := by
  let F := reversibleResistanceContinuousExtension A f hf
  let G := reversibleResistanceContinuousExtension A g hg
  have hF := reversibleResistanceContinuousExtension_eq A f hf
  have hG := reversibleResistanceContinuousExtension_eq A g hg
  have he (u v : ℝ → ℝ) (U V : ℝ →ᵇ ℝ)
      (hu : EqOn U u (Icc A.source.left A.source.right))
      (hv : EqOn V v (Icc A.source.left A.source.right)) :
      (∫ x in A.source.left..A.source.right, A.source.density x * U x * reversibleResistanceTransition A t V x) =
        ∫ x in A.source.left..A.source.right, A.source.density x * u x * reversibleResistanceTransition A t v x := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [hu (uIcc_of_le A.source.increasing.le ▸ hx), reversibleResistanceTransition_congr_interval A hv]
  exact (he f g F G hF hG).symm.trans
    ((reversibleResistanceTransition_speed_symmetric A F G t).trans (he g f G F hG hF))

theorem reversibleResistanceTransition_speed_invariant_continuous (A : IntervalMedium)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (t : ℝ≥0) :
    (∫ x in A.source.left..A.source.right,
      A.source.density x * reversibleResistanceTransition A t g x) =
      ∫ x in A.source.left..A.source.right, A.source.density x * g x := by
  have hs := reversibleResistanceTransition_speed_symmetric_continuous A
    (f := fun _ => (1 : ℝ)) continuousOn_const hg t
  change (∫ x in A.source.left..A.source.right,
    A.source.density x * 1 * reversibleResistanceTransition A t g x) =
    ∫ x in A.source.left..A.source.right,
      A.source.density x * g x * reversibleResistanceTransition A t (fun _ => 1) x at hs
  simpa only [mul_one, reversibleResistanceTransition_one] using hs

end TimeTraps.Probability

end
