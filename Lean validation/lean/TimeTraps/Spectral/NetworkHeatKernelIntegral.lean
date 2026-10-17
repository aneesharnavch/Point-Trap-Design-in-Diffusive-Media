module

public import TimeTraps.Spectral.NetworkHeatKernel

@[expose] public section

/-! The physical network heat kernel represents the original L2 heat
operator against every L2 datum. Its total mass is between zero and one,
as a consequence of the original vertex reaction form. -/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem SpectralNetwork.heatKernel_memLp (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e)) (d : E) :
    MemLp (P.heatKernel t ht e x d) 2 (volume.restrict (Ioo 0 (P.length d))) :=
  (memLp_congr_ae (P.heatKernel_representative t ht e x d)).mp (Lp.memLp _)

theorem SpectralNetwork.heatKernel_mul_integrable (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e))
    (f : GraphL2Product P.geometry) (d : E) :
    Integrable (fun y => P.heatKernel t ht e x d y * (f d) y)
      (volume.restrict (Ioo 0 (P.length d))) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (f d) (P.heatKernelVector t ht e x d)).congr
  filter_upwards [P.heatKernel_representative t ht e x d] with y hy
  simp only [Real.inner_apply, hy, mul_comm]

theorem SpectralNetwork.heatKernel_integral_apply (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e))
    (f : GraphL2Product P.geometry) :
    P.heatPointEvaluation t ht e x f =
      ∑ d, ∫ y in Ioo 0 (P.length d), P.heatKernel t ht e x d y * (f d) y := by
  rw [← P.heatKernelVector_inner, graphL2Product_inner]
  apply Finset.sum_congr rfl
  intro d _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [P.heatKernel_representative t ht e x d] with y hy
  simp only [Real.inner_apply, hy]

theorem SpectralNetwork.heatKernel_integrable (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e)) (d : E) :
    Integrable (P.heatKernel t ht e x d) (volume.restrict (Ioo 0 (P.length d))) := by
  apply (P.heatKernel_mul_integrable t ht e x
    (graphSobolevSpaceStateL P.geometry P.operatorOne) d).congr
  filter_upwards [P.operatorOne_state_ae d] with y hy
  rw [hy, mul_one]

theorem SpectralNetwork.heatKernel_mass (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e)) :
    ∑ d, ∫ y in Ioo 0 (P.length d), P.heatKernel t ht e x d y =
      P.heatPointEvaluation t ht e x (graphSobolevSpaceStateL P.geometry P.operatorOne) := by
  rw [P.heatKernel_integral_apply]
  apply Finset.sum_congr rfl
  intro d _
  apply integral_congr_ae
  filter_upwards [P.operatorOne_state_ae d] with y hy
  rw [hy, mul_one]

theorem SpectralNetwork.heatKernel_mass_bounds (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e)) :
    0 ≤ ∑ d, ∫ y in Ioo 0 (P.length d), P.heatKernel t ht e x d y ∧
      (∑ d, ∫ y in Ioo 0 (P.length d), P.heatKernel t ht e x d y) ≤ 1 := by
  rw [P.heatKernel_mass]
  constructor
  · apply P.heatPointEvaluation_nonneg
    intro d
    filter_upwards [P.operatorOne_state_ae d] with y hy
    rw [hy]
    exact zero_le_one
  · apply P.heatPointEvaluation_le_one
    intro d
    filter_upwards [P.operatorOne_state_ae d] with y hy
    exact hy.le

end TimeTraps.Spectral
