module

public import TimeTraps.Analysis.GraphSingleTraceWeighted

@[expose] public section

/-! Coercivity of the original full graph contact form. All vertex
reactions may be zero except one positive reaction; passive leaves and
passive internal vertices are retained in the connected graph. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def graphContactForm (G : MetricGraph V E) (κ U W : V → ℝ)
    (u w : E → ℝ → ℝ) : ℝ :=
  (∑ e, ∫ x in (0 : ℝ)..G.length e, G.conductance e x * deriv (u e) x * deriv (w e) x) +
    ∑ v, κ v * U v * W v

theorem graphContactForm_self (G : MetricGraph V E) (κ U : V → ℝ) (u : E → ℝ → ℝ) :
    graphContactForm G κ U U u u = graphConductanceSquare G u + ∑ v, κ v * U v ^ 2 := by
  simp only [graphContactForm, graphConductanceSquare, pow_two, mul_assoc]

theorem graphContactForm_nonneg (G : MetricGraph V E) (κ U : V → ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (u : E → ℝ → ℝ) : 0 ≤ graphContactForm G κ U U u u := by
  rw [graphContactForm_self]
  exact add_nonneg (graphConductanceSquare_nonneg G u)
    (Finset.sum_nonneg (fun v _ => mul_nonneg (hκ v) (sq_nonneg _)))

theorem graphContactForm_single_le (G : MetricGraph V E) (κ U : V → ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (u : E → ℝ → ℝ) (v₀ : V) :
    graphConductanceSquare G u + κ v₀ * U v₀ ^ 2 ≤ graphContactForm G κ U U u u := by
  classical
  rw [graphContactForm_self]
  exact add_le_add le_rfl (Finset.single_le_sum (fun v _ => mul_nonneg (hκ v) (sq_nonneg (U v)))
    (Finset.mem_univ v₀))

theorem graphContactForm_h1_coercive [Nonempty E] (G : MetricGraph V E) (κ : V → ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    ∃ c : ℝ, 0 < c ∧ ∀ (U : V → ℝ) (u : E → ℝ → ℝ), GraphEnergy G U u →
      c * (∑ e, intervalH1SizeSq (u e) 0 (G.length e)) ≤ graphContactForm G κ U U u u := by
  obtain ⟨v₀, hv₀⟩ := hanchor
  obtain ⟨C, hC, hb⟩ := graphSingleTrace_weighted_h1_control G v₀
  let A : ℝ := C * (1 + (κ v₀)⁻¹)
  have hi : 0 < (κ v₀)⁻¹ := inv_pos.mpr hv₀
  have hA : 0 < A := mul_pos hC (by linarith)
  refine ⟨A⁻¹, inv_pos.mpr hA, ?_⟩
  intro U u hu
  have hW := graphConductanceSquare_nonneg G u
  have hsingle := graphContactForm_single_le G κ U hκ u v₀
  have htrace : U v₀ ^ 2 ≤ (κ v₀)⁻¹ * graphContactForm G κ U U u u := by
    have hle : κ v₀ * U v₀ ^ 2 ≤ graphContactForm G κ U U u u := by linarith
    have h := mul_le_mul_of_nonneg_left hle hi.le
    rwa [← mul_assoc, inv_mul_cancel₀ hv₀.ne', one_mul] at h
  have hgradient : graphConductanceSquare G u ≤ graphContactForm G κ U U u u := by
    have hpos := mul_nonneg hv₀.le (sq_nonneg (U v₀))
    linarith
  have hsum : U v₀ ^ 2 + graphConductanceSquare G u ≤
      (1 + (κ v₀)⁻¹) * graphContactForm G κ U U u u := by nlinarith
  have hbound : (∑ e, intervalH1SizeSq (u e) 0 (G.length e)) ≤
      A * graphContactForm G κ U U u u :=
    (hb U u hu).trans ((mul_le_mul_of_nonneg_left hsum hC.le).trans_eq (by dsimp only [A]; ring))
  have h := mul_le_mul_of_nonneg_left hbound (inv_pos.mpr hA).le
  rwa [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul] at h

theorem graphContactForm_norm_coercive [Nonempty E] (G : MetricGraph V E) (κ : V → ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : GraphSobolevSpace G,
      c * ‖u‖ ^ 2 ≤ graphContactForm G κ
        (graphSobolevNodeValue G u) (graphSobolevNodeValue G u)
        (graphSobolevRepresentative G u.val) (graphSobolevRepresentative G u.val) := by
  obtain ⟨c, hc, hb⟩ := graphContactForm_h1_coercive G κ hκ hanchor
  refine ⟨c, hc, ?_⟩
  intro u
  change c * ‖u.val‖ ^ 2 ≤ _
  rw [graphSobolevProduct_norm_sq_integral]
  exact hb _ _ (graphSobolevSpace_energy G u)

end TimeTraps.Analysis
