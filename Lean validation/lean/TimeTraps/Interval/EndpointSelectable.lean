module

public import TimeTraps.Interval.EndpointComparisonPhysical

@[expose] public section

/-! Choosing between endpoint architectures means optimizing over a tagged
union of the original physical design spaces. Its minimum is derived from
that independent union, rather than used to define its objective. -/

namespace TimeTraps.Interval

open Set

abbrev EndpointAlternative (A₁ A₂ : EndpointArchitecture) (B : IntervalMedium) (K : ℝ) :=
  EndpointPhysicalDesign A₁ B K ⊕ EndpointPhysicalDesign A₂ B K

variable {A₁ A₂ : EndpointArchitecture} {B : IntervalMedium} {K : ℝ}

noncomputable def EndpointAlternative.cost (E : EndpointAlternative A₁ A₂ B K) : ℝ :=
  E.elim EndpointPhysicalDesign.cost EndpointPhysicalDesign.cost

def EndpointAlternative.Optimal (E : EndpointAlternative A₁ A₂ B K) : Prop :=
  ∀ F : EndpointAlternative A₁ A₂ B K, E.cost ≤ F.cost

theorem endpoint_alternative_minimum (A₁ A₂ : EndpointArchitecture) (B : IntervalMedium)
    (hK : 0 < K) :
    IsLeast (range (fun E : EndpointAlternative A₁ A₂ B K => E.cost))
      (min (A₁.physicalValue B K) (A₂.physicalValue B K)) := by
  obtain ⟨E, hE, he⟩ := A₁.physicalValue_attained B hK
  obtain ⟨F, hF, hf⟩ := A₂.physicalValue_attained B hK
  constructor
  · by_cases h : A₁.physicalValue B K ≤ A₂.physicalValue B K
    · exact ⟨Sum.inl E, he.trans (min_eq_left h).symm⟩
    · exact ⟨Sum.inr F, hf.trans (min_eq_right (le_of_not_ge h)).symm⟩
  · rintro M ⟨G, rfl⟩
    cases G with
    | inl G => exact ((min_le_left _ _).trans_eq he.symm).trans (hE G)
    | inr G => exact ((min_le_right _ _).trans_eq hf.symm).trans (hF G)

theorem EndpointAlternative.optimal_iff_isLeast (E : EndpointAlternative A₁ A₂ B K) :
    E.Optimal ↔ IsLeast (range (fun F : EndpointAlternative A₁ A₂ B K => F.cost)) E.cost := by
  constructor
  · intro hE
    refine ⟨⟨E, rfl⟩, ?_⟩
    rintro M ⟨F, rfl⟩
    exact hE F
  · intro hE F
    exact hE.2 ⟨F, rfl⟩

theorem EndpointAlternative.optimal_iff_cost_eq (E : EndpointAlternative A₁ A₂ B K)
    (hK : 0 < K) :
    E.Optimal ↔ E.cost = min (A₁.physicalValue B K) (A₂.physicalValue B K) := by
  constructor
  · intro hE
    exact (E.optimal_iff_isLeast.mp hE).unique (endpoint_alternative_minimum A₁ A₂ B hK)
  · intro he F
    rw [he]
    exact (endpoint_alternative_minimum A₁ A₂ B hK).2 ⟨F, rfl⟩

theorem endpoint_alternative_left_optimal_iff (E : EndpointPhysicalDesign A₁ B K) :
    EndpointAlternative.Optimal (Sum.inl E : EndpointAlternative A₁ A₂ B K) ↔
      E.Optimal ∧ E.cost ≤ A₂.physicalValue B K := by
  obtain ⟨F, hF, hf⟩ := A₂.physicalValue_attained B E.reactions.budget_pos
  constructor
  · intro h
    exact ⟨fun G => h (Sum.inl G), (h (Sum.inr F)).trans_eq hf⟩
  · rintro ⟨hE, he⟩ G
    cases G with
    | inl G => exact hE G
    | inr G => exact (he.trans_eq hf.symm).trans (hF G)

theorem endpoint_alternative_right_optimal_iff (F : EndpointPhysicalDesign A₂ B K) :
    EndpointAlternative.Optimal (Sum.inr F : EndpointAlternative A₁ A₂ B K) ↔
      F.Optimal ∧ F.cost ≤ A₁.physicalValue B K := by
  obtain ⟨E, hE, he⟩ := A₁.physicalValue_attained B F.reactions.budget_pos
  constructor
  · intro h
    exact ⟨fun G => h (Sum.inr G), (h (Sum.inl E)).trans_eq he⟩
  · rintro ⟨hF, hf⟩ G
    cases G with
    | inl G => exact (hf.trans_eq he.symm).trans (hE G)
    | inr G => exact hF G

def EndpointArchitecture.singleLeft (m : ℕ) : EndpointArchitecture :=
  ⟨m, true, false, by simp⟩

def EndpointArchitecture.singleRight (m : ℕ) : EndpointArchitecture :=
  ⟨m, false, true, by simp⟩

/-- Exactly one reactive endpoint may be selected, with m interior traps. -/
theorem selectable_endpoint_minimum (m : ℕ) (B : IntervalMedium) (hK : 0 < K) :
    IsLeast (range (fun E : EndpointAlternative (EndpointArchitecture.singleLeft m)
      (EndpointArchitecture.singleRight m) B K => E.cost))
      (min ((EndpointArchitecture.singleLeft m).physicalValue B K)
        ((EndpointArchitecture.singleRight m).physicalValue B K)) :=
  endpoint_alternative_minimum _ _ B hK

end TimeTraps.Interval
