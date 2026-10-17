module

public import TimeTraps.Analysis.IntervalPointFormHilbert

@[expose] public section

/-! Every continuous real coefficient on a compact physical interval acts
boundedly on its actual length-L2 space. No derivative of the coefficient
is required. This supplies conductance, potential and speed multipliers
for the regular variable-coefficient Sturm problem. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {l r : ℝ}

noncomputable def intervalContinuousCoefficient (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r)) :
    C(Icc l r, ℝ) :=
  ⟨fun x => c x, continuousOn_iff_continuous_domRestrict.mp hc⟩

theorem intervalContinuousCoefficient_bound (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r))
    {x : ℝ} (hx : x ∈ Icc l r) :
    ‖c x‖ ≤ ‖intervalContinuousCoefficient c hc‖ :=
  (intervalContinuousCoefficient c hc).norm_coe_le_norm ⟨x, hx⟩

theorem intervalContinuousMultiply_memLp (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r))
    (f : IntervalSobolevL2 l r) :
    MemLp (fun x => c x * f x) 2 (volume.restrict (Ioo l r)) := by
  apply (Lp.memLp f).of_le_mul (c := ‖intervalContinuousCoefficient c hc‖)
    ((hc.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo |>.mul
      (Lp.aestronglyMeasurable f))
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
  simp only [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (intervalContinuousCoefficient_bound c hc (Ioo_subset_Icc_self hx))
    (norm_nonneg _)

noncomputable def intervalContinuousMultiply (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r))
    (f : IntervalSobolevL2 l r) : IntervalSobolevL2 l r :=
  (intervalContinuousMultiply_memLp c hc f).toLp (fun x => c x * f x)

theorem intervalContinuousMultiply_coe (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r))
    (f : IntervalSobolevL2 l r) :
    intervalContinuousMultiply c hc f =ᵐ[volume.restrict (Ioo l r)]
      (fun x => c x * f x) :=
  (intervalContinuousMultiply_memLp c hc f).coeFn_toLp

noncomputable def intervalContinuousMultiplyLinear (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r)) :
    IntervalSobolevL2 l r →ₗ[ℝ] IntervalSobolevL2 l r where
  toFun := intervalContinuousMultiply c hc
  map_add' f g := by
    apply Lp.ext
    filter_upwards [intervalContinuousMultiply_coe c hc (f + g), Lp.coeFn_add f g,
      intervalContinuousMultiply_coe c hc f, intervalContinuousMultiply_coe c hc g,
      Lp.coeFn_add (intervalContinuousMultiply c hc f) (intervalContinuousMultiply c hc g)]
      with x hsum hfg hf hg hout
    simp only [hsum, hfg, hout, Pi.add_apply, hf, hg]
    ring
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [intervalContinuousMultiply_coe c hc (z • f), Lp.coeFn_smul z f,
      intervalContinuousMultiply_coe c hc f, Lp.coeFn_smul z (intervalContinuousMultiply c hc f)]
      with x hprod hcf hf hout
    simp only [hprod, hcf, hout, hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem intervalContinuousMultiply_norm_le (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r))
    (f : IntervalSobolevL2 l r) :
    ‖intervalContinuousMultiply c hc f‖ ≤ ‖intervalContinuousCoefficient c hc‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [intervalContinuousMultiply_coe c hc f,
    ae_restrict_mem (μ := volume) measurableSet_Ioo] with x he hx
  rw [he, norm_mul]
  exact mul_le_mul_of_nonneg_right (intervalContinuousCoefficient_bound c hc (Ioo_subset_Icc_self hx))
    (norm_nonneg _)

noncomputable def intervalContinuousMultiplyL (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r)) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevL2 l r :=
  (intervalContinuousMultiplyLinear c hc).mkContinuous ‖intervalContinuousCoefficient c hc‖
    (intervalContinuousMultiply_norm_le c hc)

theorem intervalContinuousMultiplyL_coe (c : ℝ → ℝ) (hc : ContinuousOn c (Icc l r))
    (f : IntervalSobolevL2 l r) :
    intervalContinuousMultiplyL c hc f =ᵐ[volume.restrict (Ioo l r)]
      (fun x => c x * f x) := intervalContinuousMultiply_coe c hc f

end TimeTraps.Analysis
