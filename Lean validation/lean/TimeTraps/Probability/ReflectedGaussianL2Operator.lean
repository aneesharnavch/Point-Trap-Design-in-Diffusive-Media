module

public import TimeTraps.Probability.ReflectedGaussianL2Data

@[expose] public section

/-! The reflected-Gaussian evolution on the actual uniform L2 space.
It is the adjoint of first-coordinate pullback followed by second-
coordinate pullback on the stationary joint law. Its full L2 pairing is
the actual joint integral; contraction and symmetry follow from the
proved marginals and reversibility. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal ProbabilityTheory

def reflectedGaussianL2Operator (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    ReflectedUniformL2 L hL →L[ℝ] ReflectedUniformL2 L hL :=
  (reflectedGaussianL2Fst L hL v).toContinuousLinearMap.adjoint.comp
    (reflectedGaussianL2Snd L hL v).toContinuousLinearMap

theorem reflectedGaussianL2Operator_norm_le_one (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    ‖reflectedGaussianL2Operator L hL v‖ ≤ 1 := by
  have ha : ‖(reflectedGaussianL2Fst L hL v).toContinuousLinearMap.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (reflectedGaussianL2Fst L hL v).norm_toContinuousLinearMap_le
  have hb := (reflectedGaussianL2Snd L hL v).norm_toContinuousLinearMap_le
  calc
    _ ≤ ‖(reflectedGaussianL2Fst L hL v).toContinuousLinearMap.adjoint‖ *
        ‖(reflectedGaussianL2Snd L hL v).toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem reflectedGaussianL2Operator_contraction (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f : ReflectedUniformL2 L hL) : ‖reflectedGaussianL2Operator L hL v f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖reflectedGaussianL2Operator L hL v‖ * ‖f‖ :=
      (reflectedGaussianL2Operator L hL v).le_opNorm f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (reflectedGaussianL2Operator_norm_le_one L hL v) (norm_nonneg _)
    _ = _ := one_mul _

theorem reflectedGaussianL2Operator_pairing (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f g : ReflectedUniformL2 L hL) :
    inner ℝ f (reflectedGaussianL2Operator L hL v g) =
      ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂reflectedGaussianJoint L hL v := by
  change inner ℝ f ((reflectedGaussianL2Fst L hL v).toContinuousLinearMap.adjoint
    (reflectedGaussianL2Snd L hL v g)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (reflectedGaussianL2Fst L hL v f) (reflectedGaussianL2Snd L hL v g) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reflectedGaussianL2Fst_coe L hL v f,
    reflectedGaussianL2Snd_coe L hL v g] with p hp hq
  simp only [hp, hq, Real.inner_apply]

theorem reflectedGaussianJoint_integral_mul_swap (L : ℝ) (hL : 0 < L) (v : ℝ≥0)
    (f g : ReflectedUniformL2 L hL) :
    (∫ p : ℝ × ℝ, f p.1 * g p.2 ∂reflectedGaussianJoint L hL v) =
      ∫ p : ℝ × ℝ, g p.1 * f p.2 ∂reflectedGaussianJoint L hL v := by
  have hswap : (reflectedGaussianJoint L hL v).map Prod.swap = reflectedGaussianJoint L hL v :=
    reflectedGaussianTransition_joint_swap L hL v
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 * g p.2)
      ((reflectedGaussianJoint L hL v).map Prod.swap) := by
    rw [hswap]
    exact (reflectedGaussianJoint_integrable_mul L hL v f g).aestronglyMeasurable
  calc
    _ = ∫ p : ℝ × ℝ, f p.1 * g p.2 ∂(reflectedGaussianJoint L hL v).map Prod.swap := by
      rw [hswap]
    _ = ∫ p : ℝ × ℝ, f p.2 * g p.1 ∂reflectedGaussianJoint L hL v :=
      integral_map measurable_swap.aemeasurable hm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact mul_comm _ _

theorem reflectedGaussianL2Operator_symmetric (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    (reflectedGaussianL2Operator L hL v).IsSymmetric := by
  intro f g
  change inner ℝ (reflectedGaussianL2Operator L hL v f) g =
    inner ℝ f (reflectedGaussianL2Operator L hL v g)
  rw [real_inner_comm g (reflectedGaussianL2Operator L hL v f),
    reflectedGaussianL2Operator_pairing, reflectedGaussianL2Operator_pairing]
  exact reflectedGaussianJoint_integral_mul_swap L hL v g f

theorem reflectedGaussianL2Operator_selfAdjoint (L : ℝ) (hL : 0 < L) (v : ℝ≥0) :
    IsSelfAdjoint (reflectedGaussianL2Operator L hL v) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    (reflectedGaussianL2Operator_symmetric L hL v)

end TimeTraps.Probability

end
