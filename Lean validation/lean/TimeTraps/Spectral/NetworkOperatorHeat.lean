module

public import TimeTraps.Spectral.NetworkOperatorGround
public import TimeTraps.Analysis.CompactSpectralSemigroupGeneratorCharacterization

@[expose] public section

/-! The actual contraction heat family on the original finite edge L2
Hilbert product, built from the complete network eigenbasis. These are
analytic operators; no stochastic or Markov interpretation is used. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def SpectralNetwork.heatSemigroup (P : SpectralNetwork V E) (t : ℝ≥0) :
    GraphL2Product P.geometry →L[ℝ] GraphL2Product P.geometry :=
  P.operatorCompactPositiveInverse.heatSemigroup t

noncomputable def SpectralNetwork.heatCurve (P : SpectralNetwork V E)
    (x : GraphL2Product P.geometry) (t : ℝ) : GraphL2Product P.geometry :=
  P.operatorCompactPositiveInverse.heatCurve x t

theorem SpectralNetwork.heatSemigroup_zero (P : SpectralNetwork V E) :
    P.heatSemigroup 0 = ContinuousLinearMap.id ℝ (GraphL2Product P.geometry) :=
  P.operatorCompactPositiveInverse.heatSemigroup_zero

theorem SpectralNetwork.heatSemigroup_add (P : SpectralNetwork V E) (s t : ℝ≥0) :
    P.heatSemigroup (s + t) = (P.heatSemigroup s).comp (P.heatSemigroup t) :=
  P.operatorCompactPositiveInverse.heatSemigroup_add s t

theorem SpectralNetwork.heatSemigroup_norm_le (P : SpectralNetwork V E)
    (t : ℝ≥0) (x : GraphL2Product P.geometry) : ‖P.heatSemigroup t x‖ ≤ ‖x‖ :=
  P.operatorCompactPositiveInverse.heatSemigroup_norm_le t x

theorem SpectralNetwork.heatSemigroup_opNorm_le (P : SpectralNetwork V E)
    (t : ℝ≥0) : ‖P.heatSemigroup t‖ ≤ 1 :=
  P.operatorCompactPositiveInverse.heatSemigroup_opNorm_le t

theorem SpectralNetwork.heatSemigroup_inner (P : SpectralNetwork V E)
    (t : ℝ≥0) (x : GraphL2Product P.geometry) (i : CompactSpectralIndex P.operatorInverse) :
    inner ℝ (P.eigenbasis i) (P.heatSemigroup t x) =
      Real.exp (-(t : ℝ) / i.1) * inner ℝ (P.eigenbasis i) x :=
  P.operatorCompactPositiveInverse.heatSemigroup_inner t x i

theorem SpectralNetwork.heatSemigroup_expansion (P : SpectralNetwork V E)
    (t : ℝ≥0) (x : GraphL2Product P.geometry) :
    HasSum (fun i : CompactSpectralIndex P.operatorInverse =>
      (Real.exp (-(t : ℝ) / i.1) * inner ℝ (P.eigenbasis i) x) • P.eigenbasis i)
        (P.heatSemigroup t x) :=
  P.operatorCompactPositiveInverse.hasSum_heatSemigroup t x

theorem SpectralNetwork.heat_initial (P : SpectralNetwork V E) (x : GraphL2Product P.geometry) :
    P.heatCurve x 0 = x := P.operatorCompactPositiveInverse.heatCurve_zero x

theorem SpectralNetwork.heat_strong_continuous (P : SpectralNetwork V E)
    (x : GraphL2Product P.geometry) : Continuous (fun t : ℝ≥0 => P.heatCurve x t) := by
  simpa only [SpectralNetwork.heatCurve, CompactPositiveInverse.heatCurve, Real.toNNReal_coe] using
    P.operatorCompactPositiveInverse.heatSemigroup_strong_continuous x

end TimeTraps.Spectral
