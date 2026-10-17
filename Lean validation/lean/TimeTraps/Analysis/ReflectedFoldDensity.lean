module

public import TimeTraps.Analysis.ReflectedFoldDensityBranches
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-! Pushing a nonnegative Lebesgue density through the triangular fold
adds its two lattice preimages at each interior point. The ENNReal series
and Tonelli permit arbitrary measurable densities, including infinite mass.
The boundary fibres are null, so the density is restricted to the interior. -/

noncomputable section

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Probability
open scoped ENNReal Function

def reflectedFoldDensity (L : ℝ) (f : ℝ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∑' k : ℤ, (f (y + k * (2 * L)) + f (k * (2 * L) - y))

theorem reflectedFoldDensity_measurable (L : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (reflectedFoldDensity L f) :=
  Measurable.tsum (fun k : ℤ =>
    (hf.comp (measurable_id.add (measurable_const (a := (k : ℝ) * (2 * L))))).add
      (hf.comp ((measurable_const (a := (k : ℝ) * (2 * L))).sub measurable_id)))

theorem reflectedFoldDensity_interior_apply (L : ℝ) (hL : 0 < L)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {s : Set ℝ} (hs : MeasurableSet s)
    (hsi : s ⊆ Ioo 0 L) :
    (volume.withDensity f).map (reflectedFold L) s = ∫⁻ y in s, reflectedFoldDensity L f y := by
  have hr (k : ℤ) : MeasurableSet ((fun y : ℝ => y + k * (2 * L)) '' s) :=
    (MeasurableEquiv.addRight (k * (2 * L))).measurableSet_image.mpr hs
  have hl (k : ℤ) : MeasurableSet ((fun y : ℝ => k * (2 * L) - y) '' s) :=
    (MeasurableEquiv.subLeft (k * (2 * L))).measurableSet_image.mpr hs
  have hp : (reflectedFold L) ⁻¹' s =
      (⋃ k : ℤ, (fun y : ℝ => y + k * (2 * L)) '' s) ∪
      (⋃ k : ℤ, (fun y : ℝ => k * (2 * L) - y) '' s) := by
    simpa only [sub_eq_neg_add] using reflectedFold_preimage_branches L hL (hsi.trans Ioo_subset_Icc_self)
  rw [Measure.map_apply (reflectedFold_measurable L) hs,
    withDensity_apply _ ((reflectedFold_measurable L) hs), hp,
    lintegral_union (MeasurableSet.iUnion hl) (reflectedFold_rising_falling_disjoint L hL hsi),
    lintegral_iUnion hr (reflectedFold_rising_pairwiseDisjoint L hL hsi),
    lintegral_iUnion hl (reflectedFold_falling_pairwiseDisjoint L hL hsi)]
  simp only [reflectedFold_rising_lintegral, reflectedFold_falling_lintegral]
  rw [← ENNReal.tsum_add]
  unfold reflectedFoldDensity
  have hfun (k : ℤ) : Measurable (fun y : ℝ => f (y + k * (2 * L)) + f (k * (2 * L) - y)) := by
    fun_prop
  rw [lintegral_tsum (fun k => (hfun k).aemeasurable)]
  apply tsum_congr
  intro k
  exact (lintegral_add_left (hf.comp (measurable_id.add measurable_const)) _).symm

theorem reflectedFoldDensity_map (L : ℝ) (hL : 0 < L)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (volume.withDensity f).map (reflectedFold L) =
      (volume.restrict (Ioo 0 L)).withDensity (reflectedFoldDensity L f) := by
  have ha : ∀ᵐ y ∂(volume.withDensity f).map (reflectedFold L), y ∈ Ioo 0 L := by
    apply (ae_map_iff (reflectedFold_measurable L).aemeasurable measurableSet_Ioo).mpr
    exact (withDensity_absolutelyContinuous volume f).ae_le (reflectedFold_interior_ae L hL)
  have he := Measure.restrict_eq_self_of_ae_mem ha
  apply Measure.ext
  intro s hs
  calc
    _ = (volume.withDensity f).map (reflectedFold L) (s ∩ Ioo 0 L) := by
      rw [← he, Measure.restrict_apply hs, Measure.restrict_apply (hs.inter measurableSet_Ioo)]
      simp only [inter_assoc, inter_self]
    _ = ∫⁻ y in s ∩ Ioo 0 L, reflectedFoldDensity L f y :=
      reflectedFoldDensity_interior_apply L hL hf (hs.inter measurableSet_Ioo) inter_subset_right
    _ = _ := by
      rw [withDensity_apply _ hs, Measure.restrict_restrict hs]

theorem reflectedFoldDensity_singleton (L : ℝ) (hL : 0 < L) (f : ℝ → ℝ≥0∞) (y : ℝ) :
    (volume.withDensity f).map (reflectedFold L) {y} = 0 := by
  rw [Measure.map_apply (reflectedFold_measurable L) (measurableSet_singleton y)]
  exact withDensity_absolutelyContinuous volume f (reflectedFold_preimage_singleton_null L hL y)

end TimeTraps.Analysis

end
