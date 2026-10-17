module

public import TimeTraps.Interval.WeightedGridPerturbation
public import TimeTraps.Interval.WeightedGridConstant

@[expose] public section

/-! Compactness gap and concentration of every global minimizing grid.
The neighborhood is relative to the actual compact closed-grid space.
No local branch, critical equation, or uniqueness of perturbed grids is
assumed in the concentration theorem. -/

namespace TimeTraps.Interval

open Set

variable {n : ℕ}

theorem weighted_grid_compact_gap (W : CellWeight) (Q₀ : ClosedPartition n)
    (hstrict : ∀ Q : ClosedPartition n, Q ≠ Q₀ → Q₀.gridCost W < Q.gridCost W)
    (U : Set (ClosedPartition n)) (hU : IsOpen U) (h₀ : Q₀ ∈ U) (hne : Uᶜ.Nonempty) :
    ∃ γ : ℝ, 0 < γ ∧
      IsLeast ((fun Q : ClosedPartition n => Q.gridCost W - Q₀.gridCost W) '' Uᶜ) γ := by
  obtain ⟨Q, hQ, hmin⟩ := hU.isClosed_compl.isCompact.exists_isMinOn hne
    ((ClosedPartition.gridCost_continuous W).sub continuous_const).continuousOn
  have hne₀ : Q ≠ Q₀ := by
    intro he
    exact hQ (he ▸ h₀)
  refine ⟨Q.gridCost W - Q₀.gridCost W, sub_pos.mpr (hstrict Q hne₀),
    ⟨⟨Q, hQ, rfl⟩, ?_⟩⟩
  rintro M ⟨R, hR, rfl⟩
  exact hmin hR

theorem weighted_grid_minimizers_near_unique (V : CellWeight) (Q₀ : ClosedPartition n)
    (hstrict : ∀ Q : ClosedPartition n, Q ≠ Q₀ → Q₀.gridCost V < Q.gridCost V)
    (U : Set (ClosedPartition n)) (hU : IsOpen U) (h₀ : Q₀ ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ W : CellWeight,
      (∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ δ) →
      ∀ Q : ClosedPartition n, (∀ P : ClosedPartition n, Q.gridCost W ≤ P.gridCost W) → Q ∈ U := by
  by_cases hne : Uᶜ.Nonempty
  · obtain ⟨γ, hγ, hgap⟩ := weighted_grid_compact_gap V Q₀ hstrict U hU h₀ hne
    refine ⟨γ / 3, div_pos hγ (by norm_num), ?_⟩
    intro W hW Q hQ
    by_contra hn
    have haway := hgap.2 ⟨Q, hn, rfl⟩
    have hbQ := abs_le.mp (Q.gridCost_weight_perturbation W V hW)
    have hb₀ := abs_le.mp (Q₀.gridCost_weight_perturbation W V hW)
    have hcomp := hQ Q₀
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro _ _ Q _
    by_contra hn
    exact hne ⟨Q, hn⟩

theorem weighted_grid_constant_strict (V : CellWeight) (hn : 0 < n) {Ω : ℝ}
    (hΩ : 0 < Ω) (hV : ∀ x ∈ Icc (0 : ℝ) 1, V.value x = Ω)
    (Q : ClosedPartition n) (hne : Q ≠ (StrictPartition.uniform n hn).closed) :
    (StrictPartition.uniform n hn).closed.gridCost V < Q.gridCost V := by
  rw [StrictPartition.uniform_gridCost_constant V hn hΩ hV]
  have hle := Q.constant_grid_lower V hΩ.le hV
  by_contra hnot
  have he : Q.gridCost V = Ω / (12 * (n : ℝ) ^ 2) := le_antisymm (le_of_not_gt hnot) hle
  have hw := (Q.constant_grid_eq_iff_width V hΩ hV).mp he
  exact hne (Q.eq_uniform_of_width hn hw)

theorem weighted_grid_minimizers_near_uniform (V : CellWeight) (hn : 0 < n) {Ω : ℝ}
    (hΩ : 0 < Ω) (hV : ∀ x ∈ Icc (0 : ℝ) 1, V.value x = Ω)
    (U : Set (ClosedPartition n)) (hU : IsOpen U) (h₀ : (StrictPartition.uniform n hn).closed ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ W : CellWeight,
      (∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ δ) →
      ∀ Q : ClosedPartition n, (∀ P : ClosedPartition n, Q.gridCost W ≤ P.gridCost W) → Q ∈ U :=
  weighted_grid_minimizers_near_unique V (StrictPartition.uniform n hn).closed
    (weighted_grid_constant_strict V hn hΩ hV) U hU h₀

end TimeTraps.Interval
