module

public import TimeTraps.Probability.ReflectedFoldLaw
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! A fixed-standard-Gaussian realization of the reflected transition.
The samples take values in the actual continuous-function space on the
closed interval, endowed with its uniform norm. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def reflectedIntervalFold (L : ℝ) (hL : 0 < L) : C(ℝ, Icc (0 : ℝ) L) where
  toFun z := ⟨reflectedFold L z, reflectedFold_mem L hL z⟩
  continuous_toFun := (reflectedFold_continuous L).subtype_mk _

def reflectedFellerExtension (L : ℝ) (hL : 0 < L) (f : C(Icc (0 : ℝ) L, ℝ)) : C(ℝ, ℝ) :=
  f.comp (reflectedIntervalFold L hL)

theorem reflectedFellerExtension_on_interval (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) (x : Icc (0 : ℝ) L) :
    reflectedFellerExtension L hL f x.val = f x := by
  apply congrArg f
  apply Subtype.ext
  exact reflectedFold_eq_self L hL x.val x.property

theorem reflectedFellerExtension_bound (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) (z : ℝ) : ‖reflectedFellerExtension L hL f z‖ ≤ ‖f‖ :=
  f.norm_coe_le_norm _

theorem reflectedGaussianLaw_standard (L x : ℝ) (v : ℝ≥0) :
    reflectedGaussianLaw L x v =
      (gaussianReal 0 1).map (fun z => reflectedFold L (x + Real.sqrt v * z)) := by
  have hm : (gaussianReal 0 1).map (fun z => Real.sqrt v * z) = gaussianReal 0 v := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
    simp only [mul_zero, mul_one] at h
    have hv : NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg (Real.sqrt v)) = v := by
      apply Subtype.ext
      exact Real.sq_sqrt v.property
    rwa [hv] at h
  rw [reflectedGaussianLaw_centered, ← hm, Measure.map_map]
  · rfl
  · exact (reflectedFold_measurable L).comp (measurable_const.add measurable_id)
  · fun_prop

def reflectedFellerSample (L : ℝ) (hL : 0 < L) (v : ℝ≥0) (z : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) : C(Icc (0 : ℝ) L, ℝ) where
  toFun x := reflectedFellerExtension L hL f (x.val + Real.sqrt v * z)
  continuous_toFun := (reflectedFellerExtension L hL f).continuous.comp
    (continuous_subtype_val.add continuous_const)

theorem reflectedFellerSample_continuous (L : ℝ) (hL : 0 < L)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    Continuous (fun p : ℝ≥0 × ℝ => reflectedFellerSample L hL p.1 p.2 f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (ℝ≥0 × ℝ) × Icc (0 : ℝ) L =>
    reflectedFellerExtension L hL f (p.2.val + Real.sqrt p.1.1 * p.1.2))
  apply (reflectedFellerExtension L hL f).continuous.comp
  fun_prop

theorem reflectedFellerSample_norm (L : ℝ) (hL : 0 < L) (v : ℝ≥0) (z : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) : ‖reflectedFellerSample L hL v z f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact reflectedFellerExtension_bound L hL f _

theorem reflectedFellerSample_integrable (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    Integrable (fun z => reflectedFellerSample L hL v z f) (gaussianReal 0 1) := by
  apply (integrable_const ‖f‖).mono'
    ((reflectedFellerSample_continuous L hL f).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => reflectedFellerSample_norm L hL v z f)

theorem reflectedFellerSample_zero (L : ℝ) (hL : 0 < L) (z : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) : reflectedFellerSample L hL 0 z f = f := by
  ext x
  change reflectedFellerExtension L hL f (x.val + Real.sqrt (0 : ℝ≥0) * z) = f x
  simpa only [NNReal.coe_zero, Real.sqrt_zero, zero_mul, add_zero] using
    reflectedFellerExtension_on_interval L hL f x

end TimeTraps.Probability

end
