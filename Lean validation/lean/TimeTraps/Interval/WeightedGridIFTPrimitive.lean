module

public import TimeTraps.Interval.WeightedGridHessianPositive
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Smooth primitives for the fixed perturbation profile h. The source
hypothesis is C¹ on the closed unit interval. The resulting primitives are
C² on its interior, where every midpoint of a strict grid lies. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped ContDiff

noncomputable def gridIFTPrimitive (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..x, h z

noncomputable def gridIFTMoment (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..x, h z * z

theorem gridIFTPrimitive_derivative (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt (gridIFTPrimitive h) (h x) x :=
  integral_primitive_hasDerivAt hh hx

theorem gridIFTMoment_derivative (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (0 : ℝ) 1))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt (gridIFTMoment h) (h x * x) x :=
  integral_primitive_hasDerivAt (hh.mul continuousOn_id) hx

theorem gridIFTPrimitive_contDiff (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (gridIFTPrimitive h) (Ioo (0 : ℝ) 1) := by
  rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun x hx => (gridIFTPrimitive_derivative h hh.continuousOn hx).differentiableAt.differentiableWithinAt,
    ?_, ?_⟩
  · intro he
    norm_num at he
  · apply (hh.mono Ioo_subset_Icc_self).congr
    intro x hx
    exact (gridIFTPrimitive_derivative h hh.continuousOn hx).deriv

theorem gridIFTMoment_contDiff (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) :
    ContDiffOn ℝ 2 (gridIFTMoment h) (Ioo (0 : ℝ) 1) :=
  gridIFTPrimitive_contDiff (fun x => h x * x) (hh.mul contDiffOn_id)

theorem gridIFT_residual_integral (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (0 : ℝ) 1))
    (q : ℝ) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    (∫ z in a..b, h z * (q - z)) =
      q * (gridIFTPrimitive h b - gridIFTPrimitive h a) - (gridIFTMoment h b - gridIFTMoment h a) := by
  have hi (l r : ℝ) (hl : l ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable h volume l r := (hh.mono (uIcc_subset_Icc hl hr)).intervalIntegrable
  have hm (l r : ℝ) (hl : l ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable (fun z => h z * z) volume l r :=
    ((hh.mul continuousOn_id).mono (uIcc_subset_Icc hl hr)).intervalIntegrable
  have hp : (∫ z in a..b, h z) = gridIFTPrimitive h b - gridIFTPrimitive h a :=
    (intervalIntegral.integral_interval_sub_left
      (hi 0 b ⟨le_rfl, zero_le_one⟩ hb) (hi 0 a ⟨le_rfl, zero_le_one⟩ ha)).symm
  have hM : (∫ z in a..b, h z * z) = gridIFTMoment h b - gridIFTMoment h a :=
    (intervalIntegral.integral_interval_sub_left
      (hm 0 b ⟨le_rfl, zero_le_one⟩ hb) (hm 0 a ⟨le_rfl, zero_le_one⟩ ha)).symm
  calc
    _ = ∫ z in a..b, (q * h z - h z * z) := by
      apply intervalIntegral.integral_congr
      intro z _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub ((hi a b ha hb).const_mul q) (hm a b ha hb),
        intervalIntegral.integral_const_mul, hp, hM]

end TimeTraps.Interval
