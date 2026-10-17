module

public import TimeTraps.Probability.ReversibleResistancePhysicalBandData

@[expose] public section

/-! Full level/time/sample measurability of the folded density, followed
by joint physical-space/sample measurability at the actual inverse clock. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem foldedOccupationDensity_full_jointlyMeasurable (L D x : ℝ) :
    Measurable (fun p : (ℝ × ℝ≥0) × (ℕ → ℝ) => foldedOccupationDensity L D x p.1.2 p.2 p.1.1) := by
  let G : (ℝ × ℝ≥0) × (ℕ → ℝ) → ℝ≥0∞ := fun p =>
    reflectedFoldDensity L (fun y => ENNReal.ofReal
      (affineBrownianOccupationDensity x (Real.sqrt (2 * D)) y p.1.2 p.2)) p.1.1
  have hG : Measurable G := by
    unfold G reflectedFoldDensity
    apply Measurable.tsum
    intro k
    let q₁ : (ℝ × ℝ≥0) × (ℕ → ℝ) → (ℝ × ℝ≥0) × (ℕ → ℝ) :=
      fun p => ((p.1.1 + (k : ℝ) * (2 * L), p.1.2), p.2)
    let q₂ : (ℝ × ℝ≥0) × (ℕ → ℝ) → (ℝ × ℝ≥0) × (ℕ → ℝ) :=
      fun p => (((k : ℝ) * (2 * L) - p.1.1, p.1.2), p.2)
    have hq₁ : Measurable q₁ := by fun_prop
    have hq₂ : Measurable q₂ := by fun_prop
    have hl := (affineBrownianOccupationDensity_jointlyMeasurable x (Real.sqrt (2 * D))).comp hq₁
    have hr := (affineBrownianOccupationDensity_jointlyMeasurable x (Real.sqrt (2 * D))).comp hq₂
    exact hl.ennreal_ofReal.add hr.ennreal_ofReal
  let U : Set ((ℝ × ℝ≥0) × (ℕ → ℝ)) := {p | p.1.1 ∈ Ioo 0 L}
  have hU : MeasurableSet U := measurableSet_Ioo.preimage (measurable_fst.comp measurable_fst)
  change Measurable (fun p => (U.indicator G p).toReal)
  exact (hG.indicator hU).ennreal_toReal

theorem reversibleResistanceOccupationDensity_spatial_jointlyMeasurable (A : IntervalMedium) (x : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => reversibleResistanceOccupationDensity A x T p.2 p.1) := by
  let q : ℝ × (ℕ → ℝ) → (ℝ × ℝ≥0) × (ℕ → ℝ) :=
    fun p => ((resistancePhysicalCoordinate A p.1, reversibleResistanceInversePath A x T p.2), p.2)
  have hq : Measurable q :=
    (((resistancePhysicalCoordinate_continuous A).measurable.comp measurable_fst).prodMk
      ((reversibleResistanceInversePath_measurable A x T).comp measurable_snd)).prodMk measurable_snd
  have hw := (foldedOccupationDensity_full_jointlyMeasurable A.resistanceLength 1 (A.resistance x)).comp hq
  dsimp only [Function.comp_def, q] at hw
  let W : ℝ × (ℕ → ℝ) → ℝ := fun p => resistancePhysicalDensity A p.1 *
    foldedOccupationDensity A.resistanceLength 1 (A.resistance x)
      (reversibleResistanceInversePath A x T p.2) p.2 (resistancePhysicalCoordinate A p.1)
  have hW : Measurable W := ((resistancePhysicalDensity_continuous A).measurable.comp measurable_fst).mul hw
  let U : Set (ℝ × (ℕ → ℝ)) := {p | p.1 ∈ Ioo A.source.left A.source.right}
  have hU : MeasurableSet U := measurableSet_Ioo.preimage measurable_fst
  have he : (fun p : ℝ × (ℕ → ℝ) => reversibleResistanceOccupationDensity A x T p.2 p.1) = U.indicator W := by
    funext p
    by_cases hp : p.1 ∈ Ioo A.source.left A.source.right
    · have hpU : p ∈ U := hp
      simp only [reversibleResistanceOccupationDensity, indicator_of_mem hp, indicator_of_mem hpU,
        W, resistancePhysicalDensity_eq A (Ioo_subset_Icc_self hp), resistancePhysicalCoordinate_eq A (Ioo_subset_Icc_self hp)]
    · have hpU : p ∉ U := hp
      simp only [reversibleResistanceOccupationDensity, indicator_of_notMem hp, indicator_of_notMem hpU]
  rw [he]
  exact hW.indicator hU

end TimeTraps.Probability
