module

public import TimeTraps.Analysis.GraphConservativeCoordinateProjection

@[expose] public section

/-! The fourth power of the actual graph-coordinate norm is bounded by
the sum of its literal scalar fourth powers. No new equivalent norm or
choice of coordinate representative is introduced. -/

namespace TimeTraps.Analysis

theorem finite_pi_norm_fourth_le_sum {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ‖f‖ ^ 4 ≤ ∑ i, f i ^ 4 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      have hf : f = 0 := Subsingleton.elim _ _
      simp only [hf, norm_zero, zero_pow (by norm_num : (4 : ℕ) ≠ 0), Pi.zero_apply,
        Finset.sum_const_zero, le_refl]
  | inr h =>
      obtain ⟨i, hi⟩ := (IsGreatest.pi_norm f).1
      rw [← hi]
      change ‖f i‖ ^ 4 ≤ _
      rw [Real.norm_eq_abs, (by decide : Even (4 : ℕ)).pow_abs]
      exact Finset.single_le_sum (fun j _ => (show (0 : ℝ) ≤ f j ^ 4 by positivity))
        (Finset.mem_univ i)

end TimeTraps.Analysis

namespace TimeTraps.Graph

open TimeTraps.Analysis

variable {V E : Type*} [Fintype V] [Fintype E]

theorem graphCoordinateProjection_fourth_le_sum (z : GraphRealizationCoordinates V E) :
    ‖z‖ ^ 4 ≤ ∑ i : GraphCoordinateIndex V E, graphCoordinateProjection i z ^ 4 := by
  rw [← graphCoordinateProjection_norm z]
  exact finite_pi_norm_fourth_le_sum _

theorem graphCoordinateProjection_sub_fourth_le_sum (z w : GraphRealizationCoordinates V E) :
    ‖z - w‖ ^ 4 ≤ ∑ i : GraphCoordinateIndex V E,
      (graphCoordinateProjection i z - graphCoordinateProjection i w) ^ 4 := by
  simpa only [map_sub] using graphCoordinateProjection_fourth_le_sum (z - w)

end TimeTraps.Graph
