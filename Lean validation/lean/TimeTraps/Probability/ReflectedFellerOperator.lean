module

public import TimeTraps.Probability.ReflectedFellerData

@[expose] public section

/-! The actual reflected-Gaussian operator on continuous functions. It is
constructed by a Bochner integral of continuous-function-valued samples,
then identified with integration against the previously defined law. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def reflectedFellerValue (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : C(Icc (0 : ℝ) L, ℝ)) : C(Icc (0 : ℝ) L, ℝ) :=
  ∫ z, reflectedFellerSample L hL v z f ∂gaussianReal 0 1

theorem reflectedFellerValue_apply (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : C(Icc (0 : ℝ) L, ℝ)) (x : Icc (0 : ℝ) L) :
    reflectedFellerValue L hL v f x =
      ∫ z, reflectedFellerExtension L hL f (x.val + Real.sqrt v * z) ∂gaussianReal 0 1 :=
  ContinuousMap.integral_apply (reflectedFellerSample_integrable L hL v f) x

theorem reflectedFellerValue_norm (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : C(Icc (0 : ℝ) L, ℝ)) : ‖reflectedFellerValue L hL v f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ∫ z, ‖reflectedFellerSample L hL v z f‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : ℝ, ‖f‖ ∂gaussianReal 0 1 := integral_mono
      (reflectedFellerSample_integrable L hL v f).norm (integrable_const _) (fun z =>
        reflectedFellerSample_norm L hL v z f)
    _ = _ := by simp

def reflectedFellerLinear (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    C(Icc (0 : ℝ) L, ℝ) →ₗ[ℝ] C(Icc (0 : ℝ) L, ℝ) where
  toFun := reflectedFellerValue L hL v
  map_add' f g := by
    unfold reflectedFellerValue
    rw [show (fun z => reflectedFellerSample L hL v z (f + g)) =
      (fun z => reflectedFellerSample L hL v z f + reflectedFellerSample L hL v z g) by
        funext z; ext x; rfl]
    exact integral_add (reflectedFellerSample_integrable L hL v f)
      (reflectedFellerSample_integrable L hL v g)
  map_smul' c f := by
    unfold reflectedFellerValue
    rw [show (fun z => reflectedFellerSample L hL v z (c • f)) =
      (fun z => c • reflectedFellerSample L hL v z f) by funext z; ext x; rfl]
    exact integral_smul c _

def reflectedFellerOperator (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    C(Icc (0 : ℝ) L, ℝ) →L[ℝ] C(Icc (0 : ℝ) L, ℝ) :=
  (reflectedFellerLinear L hL v).mkContinuous 1 (fun f => by
    change ‖reflectedFellerValue L hL v f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using reflectedFellerValue_norm L hL v f)

theorem reflectedFellerOperator_apply (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedFellerOperator L hL v f = reflectedFellerValue L hL v f := rfl

theorem reflectedFellerOperator_kernel (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : C(Icc (0 : ℝ) L, ℝ)) (x : Icc (0 : ℝ) L) :
    reflectedFellerOperator L hL v f x =
      ∫ y, reflectedFellerExtension L hL f y ∂reflectedGaussianLaw L x.val v := by
  rw [reflectedFellerOperator_apply, reflectedFellerValue_apply, reflectedGaussianLaw_standard]
  have hm : Measurable (fun z : ℝ => reflectedFold L (x.val + Real.sqrt v * z)) :=
    (reflectedFold_measurable L).comp (measurable_const.add (measurable_const.mul measurable_id))
  rw [integral_map hm.aemeasurable
    (reflectedFellerExtension L hL f).continuous.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  exact (reflectedFellerExtension_on_interval L hL f
    (reflectedIntervalFold L hL (x.val + Real.sqrt v * z))).symm

theorem reflectedFellerOperator_contraction (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : C(Icc (0 : ℝ) L, ℝ)) : ‖reflectedFellerOperator L hL v f‖ ≤ ‖f‖ :=
  reflectedFellerValue_norm L hL v f

theorem reflectedFellerOperator_nonneg (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    {f : C(Icc (0 : ℝ) L, ℝ)} (hf : ∀ x, 0 ≤ f x) (x : Icc (0 : ℝ) L) :
    0 ≤ reflectedFellerOperator L hL v f x := by
  rw [reflectedFellerOperator_apply, reflectedFellerValue_apply]
  exact integral_nonneg (fun z => hf (reflectedIntervalFold L hL (x.val + Real.sqrt v * z)))

theorem reflectedFellerOperator_one (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    reflectedFellerOperator L hL v 1 = 1 := by
  ext x
  rw [reflectedFellerOperator_apply, reflectedFellerValue_apply]
  change (∫ _ : ℝ, (1 : ℝ) ∂gaussianReal 0 1) = 1
  simp

theorem reflectedFellerOperator_zero (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) : reflectedFellerOperator L hL 0 f = f := by
  rw [reflectedFellerOperator_apply, reflectedFellerValue]
  simp only [reflectedFellerSample_zero, integral_const, measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]

end TimeTraps.Probability

end
