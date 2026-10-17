module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemFullPath
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-! Literal point-hitting events on continuous paths. Compact-horizon
hitting is closed; arbitrary finite-time hitting is a countable union of
these measurable events. No process law or local-time premise is used. -/

namespace TimeTraps.Probability

open Set MeasureTheory TopologicalSpace
open scoped NNReal Topology

def continuousPathHitsBy (a : ℝ) (T : ℝ≥0) : Set ReversibleNeumannFullPath :=
  {p | ∃ t ∈ Icc (0 : ℝ≥0) T, p t = a}

def continuousPathHits (a : ℝ) : Set ReversibleNeumannFullPath :=
  {p | ∃ t : ℝ≥0, p t = a}

theorem continuousPathHitsBy_closed (a : ℝ) (T : ℝ≥0) :
    IsClosed (continuousPathHitsBy a T) := by
  let S : Set (ReversibleNeumannFullPath × Icc (0 : ℝ≥0) T) :=
    {z | z.1 z.2.val = a}
  have hc : Continuous (fun z : ReversibleNeumannFullPath × Icc (0 : ℝ≥0) T =>
      z.1 z.2.val) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hs : IsClosed S := isClosed_eq hc continuous_const
  have he : Prod.fst '' S = continuousPathHitsBy a T := by
    ext p
    simp only [mem_image, S, mem_ofPred_eq, continuousPathHitsBy]
    constructor
    · rintro ⟨⟨q,t⟩, ht, rfl⟩
      exact ⟨t.val, t.property, ht⟩
    · rintro ⟨t, ht, he⟩
      exact ⟨(p, ⟨t, ht⟩), he, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace S hs

theorem continuousPathHitsBy_measurable (a : ℝ) (T : ℝ≥0) :
    MeasurableSet (continuousPathHitsBy a T) :=
  (continuousPathHitsBy_closed a T).measurableSet

theorem continuousPathHits_eq_union (a : ℝ) :
    continuousPathHits a = ⋃ N : ℕ, continuousPathHitsBy a (N : ℝ≥0) := by
  ext p
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨N, hN⟩ := exists_nat_ge t
    exact mem_iUnion.mpr ⟨N, t, ⟨bot_le, hN⟩, ht⟩
  · intro hp
    obtain ⟨N, t, _ht, he⟩ := mem_iUnion.mp hp
    exact ⟨t, he⟩

theorem continuousPathHits_measurable (a : ℝ) :
    MeasurableSet (continuousPathHits a) := by
  rw [continuousPathHits_eq_union]
  exact MeasurableSet.iUnion (fun N => continuousPathHitsBy_measurable a N)

theorem continuousPathHits_positive_compact {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ReversibleNeumannFullPath) (a : ℝ)
    (h : 0 < μ (X ⁻¹' continuousPathHits a)) :
    ∃ N : ℕ, 0 < μ (X ⁻¹' continuousPathHitsBy a (N : ℝ≥0)) := by
  rw [continuousPathHits_eq_union, preimage_iUnion] at h
  exact exists_measure_pos_of_not_measure_iUnion_null h.ne'

end TimeTraps.Probability
