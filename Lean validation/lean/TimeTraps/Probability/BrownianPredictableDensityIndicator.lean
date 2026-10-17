module

public import TimeTraps.Probability.BrownianPredictableDensityGenerators
public import TimeTraps.Probability.BrownianPredictableDensityRectangles
public import TimeTraps.Probability.BrownianAdaptedContinuousProcess

@[expose] public section

/-! Finite-horizon indicators of predictable sets, interpreted in the
original real-time product L2 space. The time-zero generator contributes
zero, and each tail generator becomes the corresponding finite rectangle. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

noncomputable def brownianPredictableCutoffIndicator (T : ℝ≥0) (E : Set (ℝ≥0 × Ω)) : ℝ × Ω → ℝ :=
  brownianSquareProcess (fun t ω => E.indicator (fun _ => (1 : ℝ)) (t, ω)) T

theorem brownianPredictableCutoffIndicator_measurable (F : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0) {E : Set (ℝ≥0 × Ω)} (hE : MeasurableSet[F.predictable] E) :
    Measurable (brownianPredictableCutoffIndicator T E) :=
  brownianSquareProcess_measurable
    (measurable_const.indicator (brownianPredictable_le_product F E hE)) T

theorem brownianPredictableCutoffIndicator_memLp (F : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0) {E : Set (ℝ≥0 × Ω)} (hE : MeasurableSet[F.predictable] E) :
    MemLp (brownianPredictableCutoffIndicator T E) 2 (volume.prod P) := by
  apply brownianAdaptedContinuous_cutoff_memLp (M := (1 : ℝ≥0))
    (measurable_const.indicator (brownianPredictable_le_product F E hE))
  intro t ω
  by_cases h : (t, ω) ∈ E
  · rw [indicator_of_mem h, abs_one]
    exact le_rfl
  · rw [indicator_of_notMem h, abs_zero]
    exact zero_le_one

theorem brownianPredictableCutoffIndicator_empty (T : ℝ≥0) :
    brownianPredictableCutoffIndicator T (∅ : Set (ℝ≥0 × Ω)) = 0 := by
  funext p
  simp only [brownianPredictableCutoffIndicator, brownianSquareProcess, indicator_empty,
    Pi.zero_apply, mul_zero]

theorem brownianPredictableCutoffIndicator_univ (T : ℝ≥0) :
    brownianPredictableCutoffIndicator T (univ : Set (ℝ≥0 × Ω)) =
      brownianElementaryProcess 0 T (fun _ => (1 : ℝ)) := by
  funext p
  simp only [brownianPredictableCutoffIndicator, brownianSquareProcess, indicator_univ,
    brownianElementaryProcess, brownianIntervalIndicator]
  rfl

theorem brownianPredictableCutoffIndicator_compl (T : ℝ≥0) (E : Set (ℝ≥0 × Ω)) :
    brownianPredictableCutoffIndicator T Eᶜ =
      brownianPredictableCutoffIndicator T univ - brownianPredictableCutoffIndicator T E := by
  funext p
  by_cases h : (p.1.toNNReal, p.2) ∈ E
  · simp only [brownianPredictableCutoffIndicator, brownianSquareProcess, indicator_of_mem h,
      indicator_of_notMem (show (p.1.toNNReal, p.2) ∉ Eᶜ from fun hn => hn h), indicator_univ, Pi.sub_apply,
      mul_zero, mul_one, sub_self]
  · simp only [brownianPredictableCutoffIndicator, brownianSquareProcess, indicator_of_notMem h,
      indicator_of_mem (show (p.1.toNNReal, p.2) ∈ Eᶜ from h), indicator_univ, Pi.sub_apply,
      mul_zero, mul_one, sub_zero]

theorem brownianPredictableCutoffIndicator_tail (s T : ℝ≥0) (A : Set Ω) :
    brownianPredictableCutoffIndicator T (Ioi s ×ˢ A) =
      (Ioc s.val T.val ×ˢ A).indicator (fun _ : ℝ × Ω => (1 : ℝ)) := by
  funext p
  change (Ioc (0 : ℝ) T.val).indicator (fun _ => (1 : ℝ)) p.1 *
    (Ioi s ×ˢ A).indicator (fun _ => (1 : ℝ)) (p.1.toNNReal, p.2) = _
  by_cases hp : p ∈ Ioc s.val T.val ×ˢ A
  · have hcut : p.1 ∈ Ioc (0 : ℝ) T.val := ⟨s.coe_nonneg.trans_lt hp.1.1, hp.1.2⟩
    have ht : (p.1.toNNReal, p.2) ∈ Ioi s ×ˢ A :=
      ⟨Real.lt_toNNReal_iff_coe_lt.mpr hp.1.1, hp.2⟩
    rw [indicator_of_mem hcut, indicator_of_mem ht, indicator_of_mem hp, one_mul]
  · by_cases hcut : p.1 ∈ Ioc (0 : ℝ) T.val
    · have ht : (p.1.toNNReal, p.2) ∉ Ioi s ×ˢ A := by
        intro ht
        exact hp ⟨⟨Real.lt_toNNReal_iff_coe_lt.mp ht.1, hcut.2⟩, ht.2⟩
      rw [indicator_of_notMem ht, indicator_of_notMem hp, mul_zero]
    · rw [indicator_of_notMem hcut, indicator_of_notMem hp, zero_mul]

theorem brownianPredictableCutoffIndicator_zero_time (T : ℝ≥0) (A : Set Ω) :
    brownianPredictableCutoffIndicator T ({0} ×ˢ A) = 0 := by
  funext p
  change (Ioc (0 : ℝ) T.val).indicator (fun _ => (1 : ℝ)) p.1 *
    ({0} ×ˢ A).indicator (fun _ => (1 : ℝ)) (p.1.toNNReal, p.2) = 0
  by_cases hcut : p.1 ∈ Ioc (0 : ℝ) T.val
  · have ht : (p.1.toNNReal, p.2) ∉ ({0} ×ˢ A) := by
      intro ht
      exact (Real.toNNReal_pos.mpr hcut.1).ne' (mem_singleton_iff.mp ht.1)
    rw [indicator_of_notMem ht, mul_zero]
  · rw [indicator_of_notMem hcut, zero_mul]

end TimeTraps.Probability
