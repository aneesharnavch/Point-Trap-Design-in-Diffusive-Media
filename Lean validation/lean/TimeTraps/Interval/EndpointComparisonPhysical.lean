module

public import TimeTraps.Interval.EndpointComparison
public import TimeTraps.Interval.EndpointOptimality

@[expose] public section

/-! Medium comparison for the independent physical endpoint-design problem.
The architecture is fixed and the physical budgets may differ, provided
their ratios to total source mass agree. -/

namespace TimeTraps.Interval

open Set

variable {A : EndpointArchitecture} {B C : IntervalMedium} {K K₁ K₂ ε : ℝ}

theorem EndpointPhysicalDesign.optimal_le_partition (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) (Q : StrictPartition A.count) :
    E.cost ≤ A.root Q.closed B.cellWeight (div_pos E.reactions.budget_pos B.source.mass_pos) := by
  have h := hE (B.endpointPartitionDesign A Q E.reactions.budget_pos)
  rwa [B.endpointPartitionDesign_cost] at h

theorem EndpointPhysicalDesign.optimal_cost_mono_weight (E : EndpointPhysicalDesign A B K₁)
    (F : EndpointPhysicalDesign A C K₂) (hE : E.Optimal) (hF : F.Optimal)
    (hbudget : K₁ / B.source.mass = K₂ / C.source.mass)
    (hBC : ∀ z ∈ Icc (0 : ℝ) 1, B.cellWeight.value z ≤ C.cellWeight.value z) :
    E.cost ≤ F.cost := by
  have h := A.root_mono_weight F.partition.closed B.cellWeight C.cellWeight hBC
    (div_pos F.reactions.budget_pos C.source.mass_pos)
  have he := E.optimal_le_partition hE F.partition
  simp only [hbudget] at he
  exact (he.trans h).trans_eq (F.optimal_cost_eq_root hF).symm

theorem EndpointPhysicalDesign.optimal_cost_lt_weight (E : EndpointPhysicalDesign A B K₁)
    (F : EndpointPhysicalDesign A C K₂) (hE : E.Optimal) (hF : F.Optimal)
    (hbudget : K₁ / B.source.mass = K₂ / C.source.mass)
    (hBC : ∀ z ∈ Icc (0 : ℝ) 1, B.cellWeight.value z < C.cellWeight.value z) :
    E.cost < F.cost := by
  have h := A.root_lt_weight F.partition.closed B.cellWeight C.cellWeight hBC
    (div_pos F.reactions.budget_pos C.source.mass_pos)
  have he := E.optimal_le_partition hE F.partition
  simp only [hbudget] at he
  exact (he.trans_lt h).trans_eq (F.optimal_cost_eq_root hF).symm

theorem EndpointPhysicalDesign.optimal_cost_abs_sub_le (E : EndpointPhysicalDesign A B K₁)
    (F : EndpointPhysicalDesign A C K₂) (hE : E.Optimal) (hF : F.Optimal)
    (hbudget : K₁ / B.source.mass = K₂ / C.source.mass)
    (hBC : ∀ z ∈ Icc (0 : ℝ) 1, |B.cellWeight.value z - C.cellWeight.value z| ≤ ε) :
    |E.cost - F.cost| ≤ ε / 2 := by
  have h₁ := A.root_abs_sub_le F.partition.closed B.cellWeight C.cellWeight hBC
    (div_pos F.reactions.budget_pos C.source.mass_pos)
  have h₂ := A.root_abs_sub_le E.partition.closed B.cellWeight C.cellWeight hBC
    (div_pos F.reactions.budget_pos C.source.mass_pos)
  have he := E.optimal_le_partition hE F.partition
  have hf := F.optimal_le_partition hF E.partition
  have heq := E.optimal_cost_eq_root hE
  have hfq := F.optimal_cost_eq_root hF
  simp only [hbudget] at he heq
  exact abs_le.mpr ⟨by linarith [(abs_le.mp h₂).1], by linarith [(abs_le.mp h₁).2]⟩

theorem EndpointPhysicalDesign.optimal_cost_abs_sub_le_Linfty (E : EndpointPhysicalDesign A B K₁)
    (F : EndpointPhysicalDesign A C K₂) (hE : E.Optimal) (hF : F.Optimal)
    (hbudget : K₁ / B.source.mass = K₂ / C.source.mass)
    (hBC : B.cellWeight.uniformDistance C.cellWeight ≤ ε) :
    |E.cost - F.cost| ≤ ε / 2 :=
  E.optimal_cost_abs_sub_le F hE hF hbudget
    ((B.cellWeight.uniformDistance_le_iff C.cellWeight).mp hBC)

noncomputable def EndpointArchitecture.physicalValue (A : EndpointArchitecture)
    (B : IntervalMedium) (K : ℝ) : ℝ :=
  sInf (range (fun E : EndpointPhysicalDesign A B K => E.cost))

theorem EndpointPhysicalDesign.physicalValue_eq_cost (E : EndpointPhysicalDesign A B K)
    (hE : E.Optimal) : A.physicalValue B K = E.cost :=
  (E.optimal_iff_isLeast.mp hE).csInf_eq

theorem EndpointArchitecture.physicalValue_attained (A : EndpointArchitecture)
    (B : IntervalMedium) (hK : 0 < K) :
    ∃ E : EndpointPhysicalDesign A B K, E.Optimal ∧ E.cost = A.physicalValue B K := by
  obtain ⟨E, hE⟩ := endpoint_physical_minimum_exists A B hK
  exact ⟨E, hE, (E.physicalValue_eq_cost hE).symm⟩

theorem EndpointArchitecture.physicalValue_mono_weight (A : EndpointArchitecture)
    (B C : IntervalMedium) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / B.source.mass = K₂ / C.source.mass)
    (hBC : ∀ z ∈ Icc (0 : ℝ) 1, B.cellWeight.value z ≤ C.cellWeight.value z) :
    A.physicalValue B K₁ ≤ A.physicalValue C K₂ := by
  obtain ⟨E, hE, he⟩ := A.physicalValue_attained B hK₁
  obtain ⟨F, hF, hf⟩ := A.physicalValue_attained C hK₂
  rw [← he, ← hf]
  exact E.optimal_cost_mono_weight F hE hF hbudget hBC

theorem EndpointArchitecture.physicalValue_lt_weight (A : EndpointArchitecture)
    (B C : IntervalMedium) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / B.source.mass = K₂ / C.source.mass)
    (hBC : ∀ z ∈ Icc (0 : ℝ) 1, B.cellWeight.value z < C.cellWeight.value z) :
    A.physicalValue B K₁ < A.physicalValue C K₂ := by
  obtain ⟨E, hE, he⟩ := A.physicalValue_attained B hK₁
  obtain ⟨F, hF, hf⟩ := A.physicalValue_attained C hK₂
  rw [← he, ← hf]
  exact E.optimal_cost_lt_weight F hE hF hbudget hBC

theorem EndpointArchitecture.physicalValue_abs_sub_le_Linfty (A : EndpointArchitecture)
    (B C : IntervalMedium) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / B.source.mass = K₂ / C.source.mass)
    (hBC : B.cellWeight.uniformDistance C.cellWeight ≤ ε) :
    |A.physicalValue B K₁ - A.physicalValue C K₂| ≤ ε / 2 := by
  obtain ⟨E, hE, he⟩ := A.physicalValue_attained B hK₁
  obtain ⟨F, hF, hf⟩ := A.physicalValue_attained C hK₂
  rw [← he, ← hf]
  exact E.optimal_cost_abs_sub_le_Linfty F hE hF hbudget hBC

end TimeTraps.Interval
