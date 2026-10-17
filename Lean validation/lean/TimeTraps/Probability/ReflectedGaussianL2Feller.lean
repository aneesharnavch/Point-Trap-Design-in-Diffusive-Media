module

public import TimeTraps.Probability.ReflectedGaussianL2Average
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

@[expose] public section

/-! The actual continuous functions on the reflecting interval embed
densely in its normalized-uniform L2 space. The joint-law L2 operator
intertwines this map with the independently constructed Feller operator.
Density uses Mathlib's bounded-continuous-function approximation theorem
and the proved support of the uniform law. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal ProbabilityTheory

def reflectedFellerToL2 (L : ℝ) (hL : 0 < L) :
    C(Icc (0 : ℝ) L, ℝ) →L[ℝ] ReflectedUniformL2 L hL :=
  (BoundedContinuousFunction.toLp 2 (reflectedUniformLaw L hL) ℝ).comp
    ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ (reflectedIntervalFold L hL)).comp
      (ContinuousMap.linearIsometryBoundedOfCompact (Icc (0 : ℝ) L) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

theorem reflectedFellerToL2_coe (L : ℝ) (hL : 0 < L) (f : C(Icc (0 : ℝ) L, ℝ)) :
    (reflectedFellerToL2 L hL f : ℝ → ℝ) =ᵐ[reflectedUniformLaw L hL]
      reflectedFellerExtension L hL f :=
  BoundedContinuousFunction.coeFn_toLp 2 (reflectedUniformLaw L hL) ℝ
    (((ContinuousMap.linearIsometryBoundedOfCompact (Icc (0 : ℝ) L) ℝ ℝ) f).compContinuous
      (reflectedIntervalFold L hL))

theorem reflectedGaussianL2Operator_feller (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : C(Icc (0 : ℝ) L, ℝ)) :
    reflectedGaussianL2Operator L hL v (reflectedFellerToL2 L hL f) =
      reflectedFellerToL2 L hL (reflectedFellerOperator L hL v f) := by
  have hf2 : MemLp (reflectedFellerExtension L hL f) 2 (reflectedUniformLaw L hL) :=
    MemLp.of_bound (reflectedFellerExtension L hL f).continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall (reflectedFellerExtension_bound L hL f))
  have he : reflectedFellerToL2 L hL f = hf2.toLp (reflectedFellerExtension L hL f) := by
    apply Lp.ext
    exact (reflectedFellerToL2_coe L hL f).trans hf2.coeFn_toLp.symm
  rw [he]
  apply Lp.ext
  filter_upwards [reflectedGaussianL2Operator_bounded_coe L hL v
    (reflectedFellerExtension L hL f).continuous.measurable
    (reflectedFellerExtension_bound L hL f) hf2,
    reflectedFellerToL2_coe L hL (reflectedFellerOperator L hL v f)] with x hx hy
  rw [hx, hy]
  exact (reflectedFellerOperator_extension_kernel L hL v f x).symm

theorem reflectedFellerToL2_denseRange (L : ℝ) (hL : 0 < L) :
    DenseRange (reflectedFellerToL2 L hL) := by
  have hd := BoundedContinuousFunction.toLp_denseRange (p := (2 : ℝ≥0∞))
    ℝ (reflectedUniformLaw L hL) ℝ (by norm_num)
  apply hd.mono
  rintro _ ⟨g, rfl⟩
  let f : C(Icc (0 : ℝ) L, ℝ) := g.toContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩
  refine ⟨f, ?_⟩
  apply Lp.ext
  filter_upwards [reflectedFellerToL2_coe L hL f,
    BoundedContinuousFunction.coeFn_toLp 2 (reflectedUniformLaw L hL) ℝ g,
    reflectedUniformLaw_ae_mem L hL] with x hx hy hxi
  rw [hx, hy]
  change g (reflectedFold L x) = g x
  rw [reflectedFold_eq_self L hL x hxi]

end TimeTraps.Probability

end
