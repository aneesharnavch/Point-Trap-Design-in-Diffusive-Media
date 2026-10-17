module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovTimeChange

@[expose] public section

/-! Stopping a clock at a countably valued time uses only the stopped
sigma-fields of its deterministic clock times. Restricting to a stopping
event is included, so the later limiting proof also controls the entire
stopped sigma-field rather than just the sampled time. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter Classical
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem sampledClock_countable_restricted_isStoppingTime
    {F G : Filtration ℝ≥0 mΩ} {T : ℝ≥0 → Ω → ℝ≥0}
    (hT : ∀ t, IsStoppingTime F (fun ω => (T t ω : WithTop ℝ≥0)))
    (hG : ∀ t, G t = (hT t).measurableSpace)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime G (fun ω => (σ ω : WithTop ℝ≥0)))
    (hc : (range σ).Countable) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    IsStoppingTime F (fun ω => if ω ∈ A then (T (σ ω) ω : WithTop ℝ≥0) else ⊤) := by
  let : Countable (range σ) := hc.to_subtype
  intro r
  let C : range σ → Set Ω := fun q => A ∩ {ω | (σ ω : WithTop ℝ≥0) = q.val}
  have hC (q : range σ) : MeasurableSet[G q.val] (C q) :=
    (hσ.measurableSet_inter_eq_iff A q.val).mp (hA.inter (hσ.measurableSet_eq' q.val))
  have hCf (q : range σ) :
      MeasurableSet[F r] (C q ∩ {ω | (T q.val ω : WithTop ℝ≥0) ≤ r}) := by
    have h := hC q
    rw [hG] at h
    exact h.2 r
  have he : {ω | (if ω ∈ A then (T (σ ω) ω : WithTop ℝ≥0) else ⊤) ≤ r} =
      ⋃ q : range σ, C q ∩ {ω | (T q.val ω : WithTop ℝ≥0) ≤ r} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      have hω : ω ∈ A := by
        by_contra hn
        simp only [if_neg hn, WithTop.not_top_le_coe] at h
      rw [if_pos hω] at h
      exact ⟨⟨σ ω, ⟨ω, rfl⟩⟩, ⟨hω, rfl⟩, h⟩
    · rintro ⟨q, hq, hr⟩
      have heq : σ ω = q.val := WithTop.coe_injective hq.2
      rw [if_pos hq.1, heq]
      exact hr
  rw [he]
  exact MeasurableSet.iUnion hCf

theorem sampledClock_upperGrid_countable (σ : Ω → ℝ≥0) (n : ℕ) :
    (range (fun ω => boundedStoppingUpperGrid n (σ ω))).Countable := by
  apply (countable_range (fun k : ℕ => (k : ℝ≥0) / ((n : ℝ≥0) + 1))).mono
  rintro _ ⟨ω, rfl⟩
  exact ⟨⌈σ ω * ((n : ℝ≥0) + 1)⌉₊, rfl⟩

theorem sampledClock_upperGrid_iInf {T : ℝ≥0 → Ω → ℝ≥0}
    (hmono : ∀ ω, Monotone (fun t => T t ω))
    (hcont : ∀ ω, Continuous (fun t => T t ω)) (σ : Ω → ℝ≥0) (ω : Ω) :
    (⨅ n : ℕ, (T (boundedStoppingUpperGrid n (σ ω)) ω : WithTop ℝ≥0)) = T (σ ω) ω := by
  apply iInf_eq_of_forall_le_of_tendsto (F := atTop)
  · intro n
    exact WithTop.coe_le_coe.mpr (hmono ω (boundedStoppingUpperGrid_bounds n (σ ω)).1)
  · exact WithTop.continuous_coe.continuousAt.tendsto.comp
      ((hcont ω).continuousAt.tendsto.comp (boundedStoppingUpperGrid_tendsto (σ ω)))

end TimeTraps.Probability

end
