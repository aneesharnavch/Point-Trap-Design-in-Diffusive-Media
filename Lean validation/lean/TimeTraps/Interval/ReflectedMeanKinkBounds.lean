module

public import TimeTraps.Interval.ReflectedMeanKinkBridge
public import TimeTraps.Interval.PhysicalNorm

@[expose] public section

/-! Positivity and a finite uniform bound for the actual homogeneous
weak mean state. The anchor is derived from its positive design strengths;
the bound comes from the continuous finite-kink representative. -/

noncomputable section

namespace TimeTraps.Interval

open Set TimeTraps.Analysis

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

theorem IntervalDesign.homogeneous_state_pos
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    ∀ x ∈ Icc (0 : ℝ) L, 0 < E.state x := by
  have hp := E.equation.positive (fun i => (E.strength_pos i).le)
    ⟨⟨0, E.partition.size_pos⟩, E.strength_pos ⟨0, E.partition.size_pos⟩⟩
  rw [E.homogeneous_source] at hp
  exact hp

theorem IntervalDesign.homogeneous_state_bounded
    (E : IntervalDesign (homogeneous L D hL hD) n K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (0 : ℝ) L, |E.state x| ≤ C := by
  have hc : Continuous E.meanKinkPotential :=
    finiteKinkPotential_continuous E.meanKinkBase_contDiff.continuous
      Finset.univ E.geometry.site E.meanKinkCoefficient
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn E.meanKinkPotential (Icc (0 : ℝ) L))
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro x hx
  rw [← E.meanKinkPotential_eq hx]
  exact (hR x hx).trans (le_max_left _ _)

end TimeTraps.Interval

end
