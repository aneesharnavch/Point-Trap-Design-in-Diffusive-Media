module

public import TimeTraps.Analysis.GraphContactCoercivityWeight

@[expose] public section

/-! The original weighted gradient and one actual vertex value control
every full graph H1 state. Positive conductance is used only through its
proved finite-graph lower bound. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem graphSingleTrace_weighted_h1_control (G : MetricGraph V E) (v₀ : V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : V → ℝ) (u : E → ℝ → ℝ), GraphEnergy G U u →
      (∑ e, intervalH1SizeSq (u e) 0 (G.length e)) ≤
        C * (U v₀ ^ 2 + graphConductanceSquare G u) := by
  obtain ⟨C, hC, hb⟩ := graphSingleTrace_h1_control G v₀
  obtain ⟨m, hm, hbound⟩ := graphConductance_lower_bound G
  have hi : 0 < m⁻¹ := inv_pos.mpr hm
  refine ⟨C * (1 + m⁻¹), mul_pos hC (by linarith), ?_⟩
  intro U u hu
  have hd := graphDerivativeSquare_le_conductance hm hbound hu
  have hW := graphConductanceSquare_nonneg G u
  have hx : U v₀ ^ 2 + graphDerivativeSquare G u ≤
      (1 + m⁻¹) * (U v₀ ^ 2 + graphConductanceSquare G u) := by
    have hh := mul_nonneg hi.le (sq_nonneg (U v₀))
    nlinarith
  exact (hb U u hu).trans ((mul_le_mul_of_nonneg_left hx hC.le).trans_eq (by ring))

theorem graphSingleTrace_weighted_norm_control (G : MetricGraph V E) (v₀ : V) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : GraphSobolevSpace G,
      ‖u‖ ^ 2 ≤ C * ((graphSobolevNodeValue G u v₀) ^ 2 +
        graphConductanceSquare G (graphSobolevRepresentative G u.val)) := by
  obtain ⟨C, hC, hb⟩ := graphSingleTrace_weighted_h1_control G v₀
  refine ⟨C, hC, ?_⟩
  intro u
  change ‖u.val‖ ^ 2 ≤ _
  rw [graphSobolevProduct_norm_sq_integral]
  exact hb _ _ (graphSobolevSpace_energy G u)

end TimeTraps.Analysis
