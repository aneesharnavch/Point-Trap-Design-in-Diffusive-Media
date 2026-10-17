module

public import TimeTraps.Spectral.NetworkHeatKernelContinuity
public import TimeTraps.Spectral.NetworkHeatKernelIntegral
public import Mathlib.Probability.Kernel.WithDensity

@[expose] public section

/-! Genuine measurable edge transition kernels of the original network
heat operator. The integration measure is edge length on the open edge;
clamping only supplies a continuous extension outside that support. -/

namespace TimeTraps.Spectral

open Set MeasureTheory ProbabilityTheory TimeTraps.Analysis
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000

noncomputable def SpectralNetwork.heatKernelClamped (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) (x : Icc (0 : ℝ) (P.length e)) (y : ℝ) : ℝ :=
  P.heatKernel t ht e x d (projIcc 0 (P.length d) (P.length_pos d).le y)

theorem SpectralNetwork.heatKernelClamped_continuous (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) :
    Continuous (Function.uncurry (P.heatKernelClamped t ht e d)) := by
  have hp : Continuous (fun z : Icc (0 : ℝ) (P.length e) × ℝ =>
      projIcc 0 (P.length d) (P.length_pos d).le z.2) :=
    continuous_projIcc.comp continuous_snd
  have hc := (P.heatKernel_continuous t ht e d).comp (continuous_fst.prodMk hp)
  exact hc

theorem SpectralNetwork.heatKernelClamped_nonneg (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) (x : Icc (0 : ℝ) (P.length e)) (y : ℝ) :
    0 ≤ P.heatKernelClamped t ht e d x y := P.heatKernel_nonneg t ht e d x _

theorem SpectralNetwork.heatKernelClamped_ae (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) (x : Icc (0 : ℝ) (P.length e)) :
    P.heatKernelClamped t ht e d x =ᵐ[volume.restrict (Ioo 0 (P.length d))]
      P.heatKernel t ht e x d := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  simp only [heatKernelClamped, projIcc_of_mem (P.length_pos d).le (Ioo_subset_Icc_self hy)]

noncomputable def SpectralNetwork.heatEdgeKernel (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) : Kernel (Icc (0 : ℝ) (P.length e)) ℝ :=
  (Kernel.const _ (volume.restrict (Ioo 0 (P.length d)))).withDensity
    (fun x y => ENNReal.ofReal (P.heatKernelClamped t ht e d x y))

theorem SpectralNetwork.heatEdgeKernel_apply (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) (x : Icc (0 : ℝ) (P.length e)) :
    P.heatEdgeKernel t ht e d x = (volume.restrict (Ioo 0 (P.length d))).withDensity
      (fun y => ENNReal.ofReal (P.heatKernelClamped t ht e d x y)) :=
  Kernel.withDensity_apply _ (P.heatKernelClamped_continuous t ht e d).measurable.ennreal_ofReal x

theorem SpectralNetwork.heatEdgeKernel_mass (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) (x : Icc (0 : ℝ) (P.length e)) :
    P.heatEdgeKernel t ht e d x univ =
      ENNReal.ofReal (∫ y in Ioo 0 (P.length d), P.heatKernel t ht e x d y) := by
  rw [P.heatEdgeKernel_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    _ = ∫⁻ y in Ioo 0 (P.length d), ENNReal.ofReal (P.heatKernel t ht e x d y) := by
      apply lintegral_congr_ae
      exact (P.heatKernelClamped_ae t ht e d x).mono (fun _ h => congrArg ENNReal.ofReal h)
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (P.heatKernel_integrable t ht e x d) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      exact P.heatKernel_nonneg t ht e d x ⟨y, Ioo_subset_Icc_self hy⟩)).symm

theorem SpectralNetwork.heatEdgeKernel_mass_le_one (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) (x : Icc (0 : ℝ) (P.length e)) :
    P.heatEdgeKernel t ht e d x univ ≤ 1 := by
  rw [P.heatEdgeKernel_mass, ← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  apply le_trans (Finset.single_le_sum (f := fun b =>
    ∫ y in Ioo 0 (P.length b), P.heatKernel t ht e x b y) ?_ (Finset.mem_univ d))
      (P.heatKernel_mass_bounds t ht e x).2
  intro b _
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact P.heatKernel_nonneg t ht e b x ⟨y, Ioo_subset_Icc_self hy⟩

instance SpectralNetwork.heatEdgeKernel_finite (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) : IsFiniteKernel (P.heatEdgeKernel t ht e d) where
  exists_univ_le := ⟨1, ENNReal.one_lt_top, P.heatEdgeKernel_mass_le_one t ht e d⟩

end TimeTraps.Spectral
