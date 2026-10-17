module

public import TimeTraps.Spectral.NetworkHeatEdgeKernel
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! Integration and total-mass normalization of the finite family of
measurable edge heat kernels, with the original operator recovered exactly. -/

namespace TimeTraps.Spectral

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.heatEdgeKernel_integral (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) (x : Icc (0 : ℝ) (P.length e)) (f : ℝ → ℝ) :
    (∫ y, f y ∂P.heatEdgeKernel t ht e d x) =
      ∫ y in Ioo 0 (P.length d), P.heatKernel t ht e x d y * f y := by
  have hm : Measurable (fun y => ENNReal.ofReal (P.heatKernelClamped t ht e d x y)) :=
    ((P.heatKernelClamped_continuous t ht e d).comp
      (continuous_const.prodMk continuous_id)).measurable.ennreal_ofReal
  rw [P.heatEdgeKernel_apply, integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [P.heatKernelClamped_ae t ht e d x] with y hy
  rw [ENNReal.toReal_ofReal (P.heatKernelClamped_nonneg t ht e d x y), hy]
  rfl

theorem SpectralNetwork.heatEdgeKernel_sum_integral (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e))
    (f : GraphL2Product P.geometry) :
    (∑ d, ∫ y, (f d) y ∂P.heatEdgeKernel t ht e d x) = P.heatPointEvaluation t ht e x f := by
  simp_rw [P.heatEdgeKernel_integral]
  exact (P.heatKernel_integral_apply t ht e x f).symm

theorem SpectralNetwork.heatEdgeKernel_sum_mass (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e)) :
    (∑ d, P.heatEdgeKernel t ht e d x univ) =
      ENNReal.ofReal (P.heatPointEvaluation t ht e x
        (graphSobolevSpaceStateL P.geometry P.operatorOne)) := by
  simp_rw [P.heatEdgeKernel_mass]
  rw [← ENNReal.ofReal_sum_of_nonneg, P.heatKernel_mass]
  intro d _
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact P.heatKernel_nonneg t ht e d x ⟨y, Ioo_subset_Icc_self hy⟩

theorem SpectralNetwork.heatEdgeKernel_sum_mass_le_one (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e)) :
    (∑ d, P.heatEdgeKernel t ht e d x univ) ≤ 1 := by
  rw [P.heatEdgeKernel_sum_mass, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  rw [← P.heatKernel_mass]
  exact (P.heatKernel_mass_bounds t ht e x).2

end TimeTraps.Spectral
