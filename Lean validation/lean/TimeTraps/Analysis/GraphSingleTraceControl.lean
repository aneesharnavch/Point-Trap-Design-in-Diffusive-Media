module

public import TimeTraps.Analysis.GraphSingleTraceData

@[expose] public section

/-! One actual vertex trace and the summed derivative energy control the
full H1 norm on a connected finite metric graph. This is derived from
interval Poincare and incidence connectivity, without a spectral premise. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

theorem graphSingleTrace_h1_control (G : MetricGraph V E) (v₀ : V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (U : V → ℝ) (u : E → ℝ → ℝ), GraphEnergy G U u →
      (∑ e, intervalH1SizeSq (u e) 0 (G.length e)) ≤
        C * (U v₀ ^ 2 + graphDerivativeSquare G u) := by
  classical
  obtain ⟨M, hM, hb⟩ := graphSingleTrace_uniform_difference_control G v₀
  let c : E → ℝ := fun e => 4 * G.length e + 4 * G.length e * M + 2 * G.length e ^ 2 + 1
  have hc : ∀ e, 0 ≤ c e := by
    intro e
    dsimp only [c]
    have hL := (G.length_pos e).le
    positivity
  refine ⟨1 + ∑ e, c e, by linarith [Finset.sum_nonneg (s := Finset.univ) (fun e _ => hc e)], ?_⟩
  intro U u hu
  have hD := graphDerivativeSquare_nonneg G u
  have hN : ∀ v, U v ^ 2 ≤ 2 * U v₀ ^ 2 + 2 * M * graphDerivativeSquare G u := by
    intro v
    have h := hb U u hu v
    nlinarith [sq_nonneg (U v - 2 * U v₀)]
  have hedge : ∀ e, intervalH1SizeSq (u e) 0 (G.length e) ≤
      c e * (U v₀ ^ 2 + graphDerivativeSquare G u) := by
    intro e
    have hL := (G.length_pos e).le
    have hh := (hu.edge_energy e).h1_control
      (show (0 : ℝ) ∈ Icc 0 (G.length e) from ⟨le_rfl, (G.length_pos e).le⟩)
    simp only [sub_zero, hu.tail_value] at hh
    have hn := mul_le_mul_of_nonneg_left (hN (G.tail e))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (G.length_pos e).le)
    have hd := mul_le_mul_of_nonneg_left (graphDerivativeSquare_edge_le G u e)
      (by positivity : 0 ≤ 2 * G.length e ^ 2 + 1)
    have hbound : intervalH1SizeSq (u e) 0 (G.length e) ≤
        4 * G.length e * U v₀ ^ 2 +
          (4 * G.length e * M + 2 * G.length e ^ 2 + 1) * graphDerivativeSquare G u := by
      nlinarith
    apply hbound.trans
    dsimp only [c]
    have h₁ : 0 ≤ (4 * G.length e * M + 2 * G.length e ^ 2 + 1) * U v₀ ^ 2 := by positivity
    have h₂ : 0 ≤ 4 * G.length e * graphDerivativeSquare G u := by positivity
    nlinarith
  calc
    _ ≤ ∑ e, c e * (U v₀ ^ 2 + graphDerivativeSquare G u) := Finset.sum_le_sum (fun e _ => hedge e)
    _ = (∑ e, c e) * (U v₀ ^ 2 + graphDerivativeSquare G u) := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (sq_nonneg _) hD)

theorem graphSingleTrace_norm_control [Nonempty E] (G : MetricGraph V E) (v₀ : V) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : GraphSobolevSpace G,
      ‖u‖ ^ 2 ≤ C * ((graphSobolevNodeValue G u v₀) ^ 2 +
        graphDerivativeSquare G (graphSobolevRepresentative G u.val)) := by
  obtain ⟨C, hC, hb⟩ := graphSingleTrace_h1_control G v₀
  refine ⟨C, hC, ?_⟩
  intro u
  change ‖u.val‖ ^ 2 ≤ _
  rw [graphSobolevProduct_norm_sq_integral]
  exact hb _ _ (graphSobolevSpace_energy G u)

end TimeTraps.Analysis
