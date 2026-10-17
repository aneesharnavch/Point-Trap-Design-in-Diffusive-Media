module

public import TimeTraps.Probability.ContinuousPathPointHitting

@[expose] public section

/-! Strictly positive-time hitting is Borel, with compact windows bounded
away from zero. This excludes the trivial time-zero hit of a starting site. -/

namespace TimeTraps.Probability

open Set MeasureTheory TopologicalSpace
open scoped NNReal Topology

def continuousPathHitsBetween (a : ℝ) (S T : ℝ≥0) : Set ReversibleNeumannFullPath :=
  {p | ∃ t ∈ Icc S T, p t = a}

def continuousPathHitsPositive (a : ℝ) : Set ReversibleNeumannFullPath :=
  {p | ∃ t : ℝ≥0, 0 < t ∧ p t = a}

theorem continuousPathHitsBetween_closed (a : ℝ) (S T : ℝ≥0) :
    IsClosed (continuousPathHitsBetween a S T) := by
  let K : Set (ReversibleNeumannFullPath × Icc S T) := {z | z.1 z.2.val = a}
  have hc : Continuous (fun z : ReversibleNeumannFullPath × Icc S T => z.1 z.2.val) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hk : IsClosed K := isClosed_eq hc continuous_const
  have he : Prod.fst '' K = continuousPathHitsBetween a S T := by
    ext p
    constructor
    · rintro ⟨⟨q,t⟩, ht, rfl⟩
      exact ⟨t.val, t.property, ht⟩
    · rintro ⟨t, ht, he⟩
      exact ⟨(p, ⟨t, ht⟩), he, rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace K hk

theorem continuousPathHitsPositive_eq_union (a : ℝ) :
    continuousPathHitsPositive a = ⋃ n : ℕ, ⋃ m : ℕ,
      continuousPathHitsBetween a (1 / (n + 1 : ℝ≥0)) (m : ℝ≥0) := by
  ext p
  constructor
  · rintro ⟨t, ht, he⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ht
    obtain ⟨m, hm⟩ := exists_nat_ge t
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨m, t, ⟨hn.le, hm⟩, he⟩⟩
  · intro hp
    obtain ⟨n, hp⟩ := mem_iUnion.mp hp
    obtain ⟨m, t, ht, he⟩ := mem_iUnion.mp hp
    refine ⟨t, lt_of_lt_of_le ?_ ht.1, he⟩
    positivity

theorem continuousPathHitsPositive_measurable (a : ℝ) :
    MeasurableSet (continuousPathHitsPositive a) := by
  rw [continuousPathHitsPositive_eq_union]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    (continuousPathHitsBetween_closed a _ _).measurableSet

theorem continuousPathHitsPositive_compact {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ReversibleNeumannFullPath) (a : ℝ)
    (h : 0 < μ (X ⁻¹' continuousPathHitsPositive a)) :
    ∃ n m : ℕ, 0 < μ (X ⁻¹' continuousPathHitsBetween a (1 / (n + 1 : ℝ≥0)) m) := by
  rw [continuousPathHitsPositive_eq_union, preimage_iUnion] at h
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null h.ne'
  rw [preimage_iUnion] at hn
  obtain ⟨m, hm⟩ := exists_measure_pos_of_not_measure_iUnion_null hn.ne'
  exact ⟨n,m,hm⟩

end TimeTraps.Probability
