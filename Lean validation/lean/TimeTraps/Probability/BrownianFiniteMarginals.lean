module

public import TimeTraps.Probability.BrownianSequenceReindex

@[expose] public section

/-! Identification of a finite set of prescribed time coordinates inside
an actual countable sequence realization. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem brownianSequence_finset_hasLaw (τ : ℕ → ℝ≥0) (I : Finset ℝ≥0)
    (e : I → ℕ) (he : ∀ i : I, τ (e i) = i) :
    HasLaw (fun ω : ℕ → ℝ => fun i : I => ω (e i))
      (BrownianReal.projectiveFamily I) (brownianSequenceMeasure τ) := by
  classical
  let J : Finset ℕ := Finset.univ.image e
  have heJ (i : I) : e i ∈ J := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hJ : J.image τ = I := by
    ext t
    constructor
    · intro ht
      obtain ⟨j, hj, hjt⟩ := Finset.mem_image.mp ht
      obtain ⟨i, _, hij⟩ := Finset.mem_image.mp hj
      subst j
      rw [← hjt, he i]
      exact i.prop
    · intro ht
      exact Finset.mem_image.mpr ⟨e ⟨t, ht⟩, heJ ⟨t, ht⟩, he ⟨t, ht⟩⟩
  let r : (J → ℝ) → (I → ℝ) := fun x i => x ⟨e i, heJ i⟩
  have hr : Measurable r := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have h : HasLaw r (BrownianReal.projectiveFamily I) (brownianSequenceFamily τ J) := by
    refine ⟨hr.aemeasurable, ?_⟩
    rw [brownianSequenceFamily, Measure.map_map hr (brownianTimeProjection_measurable τ J)]
    have h₁ (i : I) : τ (e i) ∈ J.image τ := Finset.mem_image.mpr ⟨e i, heJ i, rfl⟩
    have h₂ (i : I) : τ (e i) ∈ I := by rw [he i]; exact i.prop
    calc
      _ = (BrownianReal.projectiveFamily I).map
          (fun x : I → ℝ => fun i : I => x ⟨τ (e i), h₂ i⟩) :=
        brownianProjectiveFamily_map_eval_congr hJ (fun i : I => τ (e i)) h₁ h₂
      _ = BrownianReal.projectiveFamily I := by
        have hf : (fun x : I → ℝ => fun i : I => x ⟨τ (e i), h₂ i⟩) = id := by
          funext x i
          congr 1
          exact Subtype.ext (he i)
        rw [hf, Measure.map_id]
  exact h.comp (brownianSequence_hasLaw τ J)

end TimeTraps.Probability
