module

public import TimeTraps.Probability.ContinuousPathLocalTimeCompact

@[expose] public section

/-! Measure-independent canonical limits of globally continuous path
approximants. The convergence event and the zero-off-event convention
are fixed before a starting law is chosen. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal Topology

def graphLocalTimeCompactRestriction (T : ℝ≥0) (p : C(ℝ≥0, ℝ)) : C(Icc (0 : ℝ≥0) T, ℝ) :=
  p.comp ⟨Subtype.val, continuous_subtype_val⟩

theorem graphLocalTimeCompactRestriction_apply (T : ℝ≥0) (p : C(ℝ≥0, ℝ)) (t : Icc (0 : ℝ≥0) T) :
    graphLocalTimeCompactRestriction T p t = p t.val := rfl

theorem graphLocalTimeCompactRestriction_continuous (T : ℝ≥0) :
    Continuous (graphLocalTimeCompactRestriction T) :=
  (ContinuousMap.uniformContinuous_comp_left ⟨Subtype.val, continuous_subtype_val⟩).continuous

variable {Ω : Type*}

theorem graphLocalTimeApproximant_measurable_of_eval [MeasurableSpace Ω] (F : Ω → C(ℝ≥0, ℝ))
    (hF : ∀ t, Measurable (fun ω => F ω t)) : Measurable F := by
  apply reversibleNeumannFullPathSample_measurableEmbedding.measurable_comp_iff.mp
  exact measurable_pi_lambda _ (fun n => hF (TopologicalSpace.denseSeq ℝ≥0 n))

def GraphLocalTimeCanonicalHasLimit (A : ℕ → Ω → C(ℝ≥0, ℝ)) (ω : Ω) : Prop :=
  ∃ l : C(ℝ≥0, ℝ), Tendsto (fun n => A n ω) atTop (𝓝 l)

def graphLocalTimeCanonicalPath (A : ℕ → Ω → C(ℝ≥0, ℝ)) (ω : Ω) : C(ℝ≥0, ℝ) := by
  classical
  exact if GraphLocalTimeCanonicalHasLimit A ω then limUnder atTop (fun n => A n ω) else 0

theorem graphLocalTimeCanonicalHasLimit_measurableSet [MeasurableSpace Ω] (A : ℕ → Ω → C(ℝ≥0, ℝ))
    (hA : ∀ n, Measurable (A n)) : MeasurableSet {ω | GraphLocalTimeCanonicalHasLimit A ω} :=
  StronglyMeasurable.measurableSet_exists_tendsto (fun n => (hA n).stronglyMeasurable)

theorem graphLocalTimeCanonicalPath_measurable [MeasurableSpace Ω] (A : ℕ → Ω → C(ℝ≥0, ℝ))
    (hA : ∀ n, Measurable (A n)) : Measurable (graphLocalTimeCanonicalPath A) := by
  exact Measurable.ite (graphLocalTimeCanonicalHasLimit_measurableSet A hA)
    (StronglyMeasurable.limUnder (l := atTop) (fun n => (hA n).stronglyMeasurable)).measurable measurable_const

theorem graphLocalTimeCanonicalPath_zero_off (A : ℕ → Ω → C(ℝ≥0, ℝ)) {ω : Ω}
    (hω : ¬ GraphLocalTimeCanonicalHasLimit A ω) : graphLocalTimeCanonicalPath A ω = 0 :=
  if_neg hω

theorem graphLocalTimeCanonicalPath_eq_of_tendsto (A : ℕ → Ω → C(ℝ≥0, ℝ)) {ω : Ω}
    {l : C(ℝ≥0, ℝ)} (hl : Tendsto (fun n => A n ω) atTop (𝓝 l)) :
    graphLocalTimeCanonicalPath A ω = l := by
  rw [graphLocalTimeCanonicalPath, if_pos ⟨l, hl⟩, hl.limUnder_eq]

theorem GraphLocalTimeCanonicalHasLimit.tendsto {A : ℕ → Ω → C(ℝ≥0, ℝ)} {ω : Ω}
    (hω : GraphLocalTimeCanonicalHasLimit A ω) :
    Tendsto (fun n => A n ω) atTop (𝓝 (graphLocalTimeCanonicalPath A ω)) := by
  obtain ⟨l, hl⟩ := hω
  rw [graphLocalTimeCanonicalPath_eq_of_tendsto A hl]
  exact hl

theorem GraphLocalTimeCanonicalHasLimit.eval_tendsto {A : ℕ → Ω → C(ℝ≥0, ℝ)} {ω : Ω}
    (hω : GraphLocalTimeCanonicalHasLimit A ω) (t : ℝ≥0) :
    Tendsto (fun n => A n ω t) atTop (𝓝 (graphLocalTimeCanonicalPath A ω t)) :=
  (continuous_eval_const t).continuousAt.tendsto.comp hω.tendsto

end TimeTraps.Probability

end
