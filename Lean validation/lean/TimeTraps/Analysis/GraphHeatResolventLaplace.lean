module

public import TimeTraps.Analysis.GraphShiftedContactHeatContraction
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! The discount-one Bochner integral of the actual original graph heat
is the already constructed mass-shifted weak inverse, for every edge L2
source. The source need not match at vertices. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem GraphShiftedContactOperatorProblem.heatLaplaceOne_integrable
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphL2Product P.geometry) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) • P.heatSemigroup t.toNNReal f) (Ioi 0) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-t) • P.heatSemigroup t.toNNReal f) :=
    (Real.continuous_exp.comp continuous_neg).smul
      ((P.heatSemigroup_strong_continuous f).comp continuous_real_toNNReal)
  have he : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0
  apply (he.mul_const ‖f‖).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (P.heatSemigroup_norm_le _ f) (Real.exp_pos _).le)

theorem GraphShiftedContactOperatorProblem.heatLaplaceOne_eigenbasis
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphL2Product P.geometry)
    (i : CompactSpectralIndex P.operatorInverse) :
    inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i)
      (∫ t in Ioi (0 : ℝ), Real.exp (-t) • P.heatSemigroup t.toNNReal f) =
      i.1 * inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i) f := by
  have hcomm : inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i)
      (∫ t in Ioi (0 : ℝ), Real.exp (-t) • P.heatSemigroup t.toNNReal f) =
      ∫ t in Ioi (0 : ℝ), inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i)
        (Real.exp (-t) • P.heatSemigroup t.toNNReal f) := by
    simpa only [innerSL_apply_apply] using
      ((innerSL ℝ (P.operatorCompactPositiveInverse.eigenbasis i)).integral_comp_comm
        (P.heatLaplaceOne_integrable f)).symm
  rw [hcomm]
  have he : (fun t : ℝ => inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i)
      (Real.exp (-t) • P.heatSemigroup t.toNNReal f)) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => Real.exp (-i.1⁻¹ * t) * inner ℝ (P.operatorCompactPositiveInverse.eigenbasis i) f) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [inner_smul_right, P.heatSemigroup_inner,
      GraphShiftedContactOperatorProblem.heatCoefficient,
      GraphShiftedContactOperatorProblem.heatRate, Real.coe_toNNReal t ht.le]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [integral_congr_ae he, integral_mul_const]
  have hi := P.operatorCompactPositiveInverse.eigenbasis_positive i
  have hv : (∫ t in Ioi (0 : ℝ), Real.exp (-i.1⁻¹ * t)) = i.1 := by
    simpa only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div, inv_inv] using
      integral_exp_mul_Ioi (a := -i.1⁻¹) (neg_neg_iff_pos.mpr (inv_pos.mpr hi)) 0
  rw [hv]

theorem GraphShiftedContactOperatorProblem.heatLaplaceOne_eq_inverse
    (P : GraphShiftedContactOperatorProblem V E) (f : GraphL2Product P.geometry) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-t) • P.heatSemigroup t.toNNReal f) = P.operatorInverse f := by
  apply P.operatorCompactPositiveInverse.eigenbasis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply, P.heatLaplaceOne_eigenbasis,
    P.operatorCompactPositiveInverse.inner_eigenbasis_apply]

end TimeTraps.Analysis
