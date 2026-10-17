module

public import TimeTraps.Analysis.GraphContactCoercivity

@[expose] public section

/-! Adding ordinary L2 mass makes the original graph contact form coercive
without a positive reaction. In particular every reaction may be zero.
The estimate follows from the actual compact conductance minimum and the
mass already present in the full graph H1 norm. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def graphShiftedContactForm (G : MetricGraph V E) (κ U W : V → ℝ)
    (u w : E → ℝ → ℝ) : ℝ :=
  (∑ e, ∫ x in (0 : ℝ)..G.length e, u e x * w e x) + graphContactForm G κ U W u w

theorem graphShiftedContactForm_self (G : MetricGraph V E) (κ U : V → ℝ)
    (u : E → ℝ → ℝ) :
    graphShiftedContactForm G κ U U u u =
      (∑ e, ∫ x in (0 : ℝ)..G.length e, u e x ^ 2) +
        graphConductanceSquare G u + ∑ v, κ v * U v ^ 2 := by
  simp only [graphShiftedContactForm, graphContactForm_self, pow_two, add_assoc]

theorem graphShiftedContactForm_h1_coercive [Nonempty E]
    (G : MetricGraph V E) (κ : V → ℝ) (hκ : ∀ v, 0 ≤ κ v) :
    ∃ c : ℝ, 0 < c ∧ ∀ (U : V → ℝ) (u : E → ℝ → ℝ), GraphEnergy G U u →
      c * (∑ e, intervalH1SizeSq (u e) 0 (G.length e)) ≤
        graphShiftedContactForm G κ U U u u := by
  obtain ⟨m, hm, hb⟩ := graphConductance_lower_bound G
  refine ⟨min 1 m, lt_min (by norm_num) hm, ?_⟩
  intro U u hu
  let M : ℝ := ∑ e, ∫ x in (0 : ℝ)..G.length e, u e x ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg (fun e _ =>
    intervalIntegral.integral_nonneg_of_forall (G.length_pos e).le (fun _ => sq_nonneg _))
  have hD := graphDerivativeSquare_nonneg G u
  have hW : m * graphDerivativeSquare G u ≤ graphConductanceSquare G u := by
    have h := mul_le_mul_of_nonneg_left (graphDerivativeSquare_le_conductance hm hb hu) hm.le
    rwa [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul] at h
  have hmass : min 1 m * M ≤ M := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) m) hM
  have hgrad : min 1 m * graphDerivativeSquare G u ≤ graphConductanceSquare G u :=
    (mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) m) hD).trans hW
  have hnodes : 0 ≤ ∑ v, κ v * U v ^ 2 :=
    Finset.sum_nonneg (fun v _ => mul_nonneg (hκ v) (sq_nonneg _))
  have hnorm : (∑ e, intervalH1SizeSq (u e) 0 (G.length e)) =
      M + graphDerivativeSquare G u := by
    simp only [intervalH1SizeSq, Finset.sum_add_distrib, M, graphDerivativeSquare]
  rw [hnorm, graphShiftedContactForm_self, mul_add]
  change min 1 m * M + min 1 m * graphDerivativeSquare G u ≤
    M + graphConductanceSquare G u + ∑ v, κ v * U v ^ 2
  linarith

theorem graphShiftedContactForm_norm_coercive [Nonempty E]
    (G : MetricGraph V E) (κ : V → ℝ) (hκ : ∀ v, 0 ≤ κ v) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : GraphSobolevSpace G,
      c * ‖u‖ ^ 2 ≤ graphShiftedContactForm G κ
        (graphSobolevNodeValue G u) (graphSobolevNodeValue G u)
        (graphSobolevRepresentative G u.val) (graphSobolevRepresentative G u.val) := by
  obtain ⟨c, hc, hb⟩ := graphShiftedContactForm_h1_coercive G κ hκ
  refine ⟨c, hc, ?_⟩
  intro u
  change c * ‖u.val‖ ^ 2 ≤ _
  rw [graphSobolevProduct_norm_sq_integral]
  exact hb _ _ (graphSobolevSpace_energy G u)

end TimeTraps.Analysis
