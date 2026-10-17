module

public import Mathlib.Probability.Process.Predictable
public import Mathlib.MeasureTheory.PiSystem

@[expose] public section

/-! The actual predictable generators form a pi-system and are
measurable for the ambient time/product space. This permits a pi-lambda
argument without changing Mathlib's predictable sigma-algebra. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def brownianPredictableGenerators (F : Filtration ℝ≥0 mΩ) : Set (Set (ℝ≥0 × Ω)) :=
  {s | ∃ A, MeasurableSet[F 0] A ∧ s = {0} ×ˢ A} ∪
    {s | ∃ t A, MeasurableSet[F t] A ∧ s = Ioi t ×ˢ A}

theorem brownianPredictableGenerators_generate (F : Filtration ℝ≥0 mΩ) :
    MeasurableSpace.generateFrom (brownianPredictableGenerators F) = F.predictable := rfl

theorem brownianPredictableGenerators_isPiSystem (F : Filtration ℝ≥0 mΩ) :
    IsPiSystem (brownianPredictableGenerators F) := by
  intro s hs t ht hne
  rcases hs with ⟨A, hA, rfl⟩ | ⟨r, A, hA, rfl⟩
  · rcases ht with ⟨B, hB, rfl⟩ | ⟨q, B, hB, rfl⟩
    · exact Or.inl ⟨A ∩ B, hA.inter hB, by rw [prod_inter_prod, inter_self]⟩
    · obtain ⟨⟨u, ω⟩, hu, hv⟩ := hne
      have hu0 : u = 0 := mem_singleton_iff.mp hu.1
      have hqu : q < u := hv.1
      rw [hu0] at hqu
      exact False.elim ((not_lt_of_ge (show (0 : ℝ≥0) ≤ q from zero_le)) hqu)
  · rcases ht with ⟨B, hB, rfl⟩ | ⟨q, B, hB, rfl⟩
    · obtain ⟨⟨u, ω⟩, hu, hv⟩ := hne
      have hu0 : u = 0 := mem_singleton_iff.mp hv.1
      have hru : r < u := hu.1
      rw [hu0] at hru
      exact False.elim ((not_lt_of_ge (show (0 : ℝ≥0) ≤ r from zero_le)) hru)
    · refine Or.inr ⟨max r q, A ∩ B,
        (F.mono (le_max_left r q) _ hA).inter (F.mono (le_max_right r q) _ hB), ?_⟩
      ext p
      simp only [mem_inter_iff, mem_prod, mem_Ioi, max_lt_iff]
      tauto

theorem brownianPredictable_le_product (F : Filtration ℝ≥0 mΩ) :
    F.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
  rw [← brownianPredictableGenerators_generate]
  apply MeasurableSpace.generateFrom_le
  intro s hs
  rcases hs with ⟨A, hA, rfl⟩ | ⟨t, A, hA, rfl⟩
  · exact (measurableSet_singleton (0 : ℝ≥0)).prod (F.le 0 _ hA)
  · exact measurableSet_Ioi.prod (F.le t _ hA)

end TimeTraps.Probability
