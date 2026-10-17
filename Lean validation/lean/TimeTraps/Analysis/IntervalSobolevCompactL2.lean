module

public import TimeTraps.Analysis.IntervalSobolevCompactArzela
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.Order.ProjIcc

@[expose] public section

/-! The actual state map into L2 factors through the compact continuous
representative map. The continuous-to-L2 inclusion has the exact length
bound sqrt(r-l) times the uniform norm. -/

namespace TimeTraps.Analysis.IntervalSobolevSpace

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace

noncomputable section

def continuousL2 {l r : ℝ} (hlr : l < r) : C(Icc l r, ℝ) →L[ℝ] IntervalSobolevL2 l r :=
  (BoundedContinuousFunction.toLp 2 (volume.restrict (Ioo l r)) ℝ).comp
    ((BoundedContinuousFunction.compContinuousCLM ℝ ℝ
      ⟨projIcc l r hlr.le, continuous_projIcc⟩).comp
      (ContinuousMap.linearIsometryBoundedOfCompact (Icc l r) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

theorem continuousL2_ae {l r : ℝ} (hlr : l < r) (f : C(Icc l r, ℝ)) :
    continuousL2 hlr f =ᵐ[volume.restrict (Ioo l r)] fun x => f (projIcc l r hlr.le x) :=
  BoundedContinuousFunction.coeFn_toLp 2 (volume.restrict (Ioo l r)) ℝ _

theorem continuousL2_norm_le {l r : ℝ} (hlr : l < r) (f : C(Icc l r, ℝ)) :
    ‖continuousL2 hlr f‖ ≤ Real.sqrt (r - l) * ‖f‖ := by
  have he : ‖continuousL2 hlr f‖ ^ 2 = ∫ x in Ioo l r, (continuousL2 hlr f) x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [Real.inner_apply, pow_two]
  have hb : (∫ x in Ioo l r, (continuousL2 hlr f) x ^ 2) ≤ ∫ _x in Ioo l r, ‖f‖ ^ 2 := by
    apply integral_mono_ae (Lp.memLp _).integrable_sq (integrable_const _)
    filter_upwards [continuousL2_ae hlr f] with x hx
    rw [hx]
    simpa only [Real.norm_eq_abs, sq_abs] using
      sq_le_sq₀ (norm_nonneg (f (projIcc l r hlr.le x))) (norm_nonneg f) |>.mpr
        (f.norm_coe_le_norm _)
  have hc : (∫ _x in Ioo l r, ‖f‖ ^ 2) = (r - l) * ‖f‖ ^ 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlr.le,
      intervalIntegral.integral_const]
    rfl
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hlr.le), he]
  exact hb.trans_eq hc

theorem continuousL2_factor_stateL {l r : ℝ} (hlr : l < r) :
    (continuousL2 hlr).comp (toContinuousL hlr) = stateL l r := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [continuousL2_ae hlr (toContinuousL hlr u),
    (u.representative_spec hlr).2.1, ae_restrict_mem measurableSet_Ioo] with x hx hy hm
  change (continuousL2 hlr (toContinuousL hlr u)) x = u.state x
  rw [hx, hy, projIcc_of_mem hlr.le (Ioo_subset_Icc_self hm)]
  rfl

theorem stateL_isCompact {l r : ℝ} (hlr : l < r) : IsCompactOperator (stateL l r) := by
  rw [← continuousL2_factor_stateL hlr]
  exact (toContinuousL_isCompact hlr).clm_comp (continuousL2 hlr)

end

end TimeTraps.Analysis.IntervalSobolevSpace
