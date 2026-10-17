module

public import TimeTraps.Probability.GraphLocalTimeCanonicalAlmostSure

@[expose] public section

/-! The canonical limit is a Borel continuous path, jointly measurable
in time and sample. Its compact restrictions are strongly measurable.
Zero initial value, nonnegativity and monotonicity pass from literal
approximants and also hold on the declared zero exceptional paths. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal Topology

variable {Ω : Type*}

theorem graphLocalTimeCompactIncrement_norm_measurable [MeasurableSpace Ω]
    (A : ℕ → Ω → C(ℝ≥0, ℝ)) (hA : ∀ n, Measurable (A n)) (T : ℝ≥0) (n : ℕ) :
    Measurable (fun ω => ‖graphLocalTimeCompactRestriction T (A (n + 1) ω) -
      graphLocalTimeCompactRestriction T (A n ω)‖) := by
  have h₁ := (graphLocalTimeCompactRestriction_continuous T).measurable.comp (hA (n + 1))
  have h₀ := (graphLocalTimeCompactRestriction_continuous T).measurable.comp (hA n)
  exact (h₁.sub h₀).norm

theorem graphLocalTimeCompactIncrement_event_measurableSet [MeasurableSpace Ω]
    (A : ℕ → Ω → C(ℝ≥0, ℝ)) (hA : ∀ n, Measurable (A n)) (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    MeasurableSet {ω | ε < ‖graphLocalTimeCompactRestriction T (A (n + 1) ω) -
      graphLocalTimeCompactRestriction T (A n ω)‖} :=
  measurableSet_lt measurable_const (graphLocalTimeCompactIncrement_norm_measurable A hA T n)

theorem graphLocalTimeCanonicalPath_jointlyMeasurable [MeasurableSpace Ω]
    (A : ℕ → Ω → C(ℝ≥0, ℝ)) (hA : ∀ n, Measurable (A n)) :
    Measurable (fun p : ℝ≥0 × Ω => graphLocalTimeCanonicalPath A p.2 p.1) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => (graphLocalTimeCanonicalPath A ω).continuous)
    (fun t => (continuous_eval_const t).measurable.comp (graphLocalTimeCanonicalPath_measurable A hA))

theorem graphLocalTimeCanonicalPath_compact_stronglyMeasurable [MeasurableSpace Ω]
    (A : ℕ → Ω → C(ℝ≥0, ℝ)) (hA : ∀ n, Measurable (A n)) (T : ℝ≥0) :
    StronglyMeasurable (fun ω => graphLocalTimeCompactRestriction T (graphLocalTimeCanonicalPath A ω)) :=
  ((graphLocalTimeCompactRestriction_continuous T).measurable.comp
    (graphLocalTimeCanonicalPath_measurable A hA)).stronglyMeasurable

theorem graphLocalTimeCanonicalPath_compact_norm_measurable [MeasurableSpace Ω]
    (A : ℕ → Ω → C(ℝ≥0, ℝ)) (hA : ∀ n, Measurable (A n)) (T : ℝ≥0) :
    Measurable (fun ω => ‖graphLocalTimeCompactRestriction T (graphLocalTimeCanonicalPath A ω)‖) :=
  (graphLocalTimeCanonicalPath_compact_stronglyMeasurable A hA T).norm.measurable

theorem graphLocalTimeCanonicalPath_zero (A : ℕ → Ω → C(ℝ≥0, ℝ)) (ω : Ω)
    (hA : ∀ n, A n ω 0 = 0) : graphLocalTimeCanonicalPath A ω 0 = 0 := by
  by_cases hω : GraphLocalTimeCanonicalHasLimit A ω
  · have h := hω.eval_tendsto 0
    simp only [hA] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · rw [graphLocalTimeCanonicalPath_zero_off A hω]
    rfl

theorem graphLocalTimeCanonicalPath_monotone (A : ℕ → Ω → C(ℝ≥0, ℝ)) (ω : Ω)
    (hA : ∀ n, Monotone (A n ω)) : Monotone (graphLocalTimeCanonicalPath A ω) := by
  by_cases hω : GraphLocalTimeCanonicalHasLimit A ω
  · intro s t hst
    exact le_of_tendsto_of_tendsto (hω.eval_tendsto s) (hω.eval_tendsto t)
      (Eventually.of_forall (fun n => hA n hst))
  · rw [graphLocalTimeCanonicalPath_zero_off A hω]
    exact monotone_const

theorem graphLocalTimeCanonicalPath_nonneg (A : ℕ → Ω → C(ℝ≥0, ℝ)) (ω : Ω)
    (hA : ∀ n t, 0 ≤ A n ω t) (t : ℝ≥0) : 0 ≤ graphLocalTimeCanonicalPath A ω t := by
  by_cases hω : GraphLocalTimeCanonicalHasLimit A ω
  · exact ge_of_tendsto (hω.eval_tendsto t) (Eventually.of_forall (fun n => hA n t))
  · rw [graphLocalTimeCanonicalPath_zero_off A hω]
    exact le_rfl

end TimeTraps.Probability
