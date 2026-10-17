module

public import TimeTraps.Analysis.OccupationDensityGridLimit
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! Actual occupation measures extend from monotone grid times to every
nonnegative time. Increasing half-open time intervals exhaust the limiting
interval up to its null endpoint. The spatial density limit uses monotone
convergence, with no sample-path or spatial continuity hypothesis. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

theorem occupationTime_Ioc_union_ae {q : ℕ → ℝ≥0} {T : ℝ≥0}
    (hle : ∀ n, q n ≤ T) (hlim : Tendsto q atTop (𝓝 T)) :
    (⋃ n, Ioc (0 : ℝ) (q n).val) =ᵐ[volume] Ioc (0 : ℝ) T.val := by
  have hne : ∀ᵐ s : ℝ ∂volume, s ≠ T.val := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with s hs
  apply propext
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_iUnion.mp h
    exact ⟨hn.1, hn.2.trans (hle n)⟩
  · intro h
    have hst : s < T.val := lt_of_le_of_ne h.2 hs
    have ht := ((continuous_subtype_val.tendsto T).comp hlim).eventually (lt_mem_nhds hst)
    obtain ⟨n, hn⟩ := ht.exists
    exact mem_iUnion.mpr ⟨n, h.1, hn.le⟩

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

noncomputable def occupationTimeMeasure (b : ℝ → α) (T : ℝ≥0) : Measure α :=
  (volume.restrict (Ioc (0 : ℝ) T.val)).map b

theorem occupationTimeMeasure_apply {b : ℝ → α} (hb : Measurable b)
    (T : ℝ≥0) {s : Set α} (hs : MeasurableSet s) :
    occupationTimeMeasure b T s = volume.restrict (Ioc (0 : ℝ) T.val) (b ⁻¹' s) :=
  Measure.map_apply hb hs

theorem occupationTimeMeasure_univ {b : ℝ → α} (hb : Measurable b) (T : ℝ≥0) :
    occupationTimeMeasure b T univ = ENNReal.ofReal T.val := by
  rw [occupationTimeMeasure_apply hb T MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero]

theorem occupationTimeMeasure_eq_iSup {b : ℝ → α} (hb : Measurable b)
    {q : ℕ → ℝ≥0} {T : ℝ≥0} (hm : Monotone q) (hle : ∀ n, q n ≤ T)
    (hlim : Tendsto q atTop (𝓝 T)) {s : Set α} (hs : MeasurableSet s) :
    occupationTimeMeasure b T s = ⨆ n, occupationTimeMeasure b (q n) s := by
  have hsets : Monotone (fun n => Ioc (0 : ℝ) (q n).val) :=
    fun i j hij => Ioc_subset_Ioc le_rfl (hm hij)
  have he := Measure.restrict_congr_set (occupationTime_Ioc_union_ae hle hlim)
  calc
    _ = volume.restrict (Ioc (0 : ℝ) T.val) (b ⁻¹' s) := occupationTimeMeasure_apply hb T hs
    _ = volume.restrict (⋃ n, Ioc (0 : ℝ) (q n).val) (b ⁻¹' s) := by rw [he]
    _ = ⨆ n, volume.restrict (Ioc (0 : ℝ) (q n).val) (b ⁻¹' s) :=
      Measure.restrict_iUnion_apply_eq_iSup hsets.directed_le (hb hs)
    _ = _ := iSup_congr fun n => (occupationTimeMeasure_apply hb (q n) hs).symm

theorem occupationDensity_grid_eq_occupation (q : ℕ → ℝ≥0) (f : ℕ → α → ℝ)
    {b : ℝ → α} (hb : Measurable b) (hf : ∀ i, Measurable (f i))
    (horder : ∀ᵐ a ∂μ, ∀ i j, q i ≤ q j → f i a ≤ f j a)
    (T : ℝ≥0) (k : ℕ → ℕ)
    (hm : Monotone (fun n => q (k n))) (hle : ∀ n, q (k n) ≤ T)
    (hlim : Tendsto (fun n => q (k n)) atTop (𝓝 T))
    (hupper : ∃ j, ∀ n, q (k n) ≤ q j)
    (heq : ∀ i, μ.withDensity (fun a => ENNReal.ofReal (f i a)) = occupationTimeMeasure b (q i)) :
    μ.withDensity (fun a => ENNReal.ofReal (occupationDensityLimit (fun n => f (k n)) a)) =
      occupationTimeMeasure b T := by
  obtain ⟨j, hj⟩ := hupper
  have hmono : ∀ᵐ a ∂μ, Monotone (fun n => f (k n) a) :=
    horder.mono (fun a ha i l hil => ha (k i) (k l) (hm hil))
  have hbound : ∀ᵐ a ∂μ, ∃ C : ℝ, ∀ n, f (k n) a ≤ C :=
    horder.mono (fun a ha => ⟨f j a, fun n => ha (k n) j (hj n)⟩)
  apply Measure.ext
  intro s hs
  rw [occupationDensityLimit_withDensity_apply (fun n => hf (k n)) hmono hbound hs]
  simp only [heq]
  exact (occupationTimeMeasure_eq_iSup hb hm hle hlim hs).symm

end TimeTraps.Analysis
