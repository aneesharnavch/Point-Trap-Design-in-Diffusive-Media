module

public import TimeTraps.Analysis.IntervalSobolevSpaceEvaluation
public import Mathlib.Topology.ContinuousMap.Compact

@[expose] public section

/-! The actual continuous representative map from the Hilbert Sobolev
space to continuous functions on the compact interval. This is an
injective continuous linear map with an explicit uniform bound and a
half-Hölder modulus. -/

namespace TimeTraps.Analysis.IntervalSobolevSpace

open Set MeasureTheory Filter
open scoped Topology

noncomputable section

def toContinuous {l r : ℝ} (u : IntervalSobolevSpace l r) (hlr : l < r) : C(Icc l r, ℝ) where
  toFun x := u.representative hlr x
  continuous_toFun := by
    have hc : ContinuousOn (u.representative hlr) (Icc l r) := by
      simpa only [uIcc_of_le hlr.le] using (u.representative_spec hlr).1.continuousOn
    exact (continuousOn_iff_continuous_domRestrict (f := u.representative hlr)).mp hc

def toContinuousLinear {l r : ℝ} (hlr : l < r) :
    IntervalSobolevSpace l r →ₗ[ℝ] C(Icc l r, ℝ) where
  toFun u := u.toContinuous hlr
  map_add' u v := by
    ext x
    exact representative_add u v hlr x.property
  map_smul' c u := by
    ext x
    change (c • u).representative hlr x = c * u.representative hlr x
    exact representative_smul u hlr c x.property

def toContinuousL {l r : ℝ} (hlr : l < r) :
    IntervalSobolevSpace l r →L[ℝ] C(Icc l r, ℝ) :=
  (toContinuousLinear hlr).mkContinuous (Real.sqrt (2 / (r - l) + 2 * (r - l))) (by
    intro u
    apply (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr
    intro x
    change ‖u.representative hlr x‖ ≤ _
    simpa only [Real.norm_eq_abs] using representative_abs_le u hlr x.property)

theorem toContinuousL_apply {l r : ℝ} (hlr : l < r) (u : IntervalSobolevSpace l r)
    (x : Icc l r) : toContinuousL hlr u x = u.representative hlr x := rfl

theorem toContinuousL_norm_le {l r : ℝ} (hlr : l < r) :
    ‖toContinuousL hlr‖ ≤ Real.sqrt (2 / (r - l) + 2 * (r - l)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr
  intro x
  simpa only [toContinuousL_apply, Real.norm_eq_abs] using representative_abs_le u hlr x.property

theorem toContinuousL_injective {l r : ℝ} (hlr : l < r) :
    Function.Injective (toContinuousL hlr) := by
  intro u v huv
  apply ext_state
  apply Lp.ext
  filter_upwards [(u.representative_spec hlr).2.1, (v.representative_spec hlr).2.1,
    ae_restrict_mem measurableSet_Ioo] with x hx hy hm
  rw [hx, hy]
  exact DFunLike.congr_fun huv ⟨x, Ioo_subset_Icc_self hm⟩

theorem toContinuousL_dist_le {l r : ℝ} (hlr : l < r) (u : IntervalSobolevSpace l r)
    (x y : Icc l r) :
    dist (toContinuousL hlr u x) (toContinuousL hlr u y) ≤ Real.sqrt (dist x y) * ‖u‖ := by
  have hs := (u.representative_spec hlr).1.abs_sub_le_sqrt x.property y.property
  have hI : 0 ≤ ∫ t in l..r, u.representative hlr t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hlr.le (fun t => sq_nonneg _)
  have hJ : (∫ t in l..r, deriv (u.representative hlr) t ^ 2) ≤ ‖u‖ ^ 2 := by
    rw [u.norm_sq_eq_h1SizeSq hlr]
    exact le_add_of_nonneg_left hI
  have hroot : Real.sqrt (∫ t in l..r, deriv (u.representative hlr) t ^ 2) ≤ ‖u‖ := by
    calc
      _ ≤ Real.sqrt (‖u‖ ^ 2) := Real.sqrt_le_sqrt hJ
      _ = ‖u‖ := Real.sqrt_sq (norm_nonneg _)
  simpa only [toContinuousL_apply, Subtype.dist_eq, Real.dist_eq] using
    hs.trans (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _))

end

end TimeTraps.Analysis.IntervalSobolevSpace
