module

public import TimeTraps.Graph.WeakState
public import TimeTraps.Graph.MetricCost

@[expose] public section

/-!
The positivity, source conservation, energy and normalized deficit identities
for the actual H1 weak solution. The cost is defined using its derivative,
independently of any flux reconstruction.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {V E : Type*}

noncomputable def MetricGraph.weakEdgeCost (G : MetricGraph V E) (u : E → ℝ → ℝ)
    (M : ℝ) (e : E) : ℝ :=
  ∫ x in 0..G.length e, (G.source e x * (M - u e x) + G.conductance e x * deriv (u e) x ^ 2)

theorem WeakGraphEquation.energy_identity [Fintype V] [Fintype E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ} (h : WeakGraphEquation G κ U u) :
    (∑ e, ∫ x in 0..G.length e, G.conductance e x * deriv (u e) x ^ 2) +
      (∑ v, κ v * U v ^ 2) = ∑ e, ∫ x in 0..G.length e, G.source e x * u e x := by
  simpa only [pow_two, mul_assoc] using h.weak_form U u h.energy

theorem WeakGraphEquation.positive [Fintype V] [Fintype E] [Nonempty E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (h : WeakGraphEquation G κ U u) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    (∀ v, 0 < U v) ∧ ∀ e x, x ∈ Icc 0 (G.length e) → 0 < u e x := by
  obtain ⟨j, hj⟩ := h.to_strong hκ hanchor
  exact hj.positive hκ

theorem WeakGraphEquation.conservation [Fintype V] [Fintype E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (h : WeakGraphEquation G κ U u) :
    ∑ v, κ v * U v = G.totalMass := by
  have hid := h.weak_form (fun _ => 1) (fun _ _ => 1) (GraphEnergy.const G 1)
  simpa [MetricGraph.totalMass, sourcePrimitive] using hid

/-- The derivative-defined physical cost agrees with the flux-defined cost. -/
theorem GraphEquation.weakEdgeCost_eq [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) (M : ℝ) (e : E) :
    G.weakEdgeCost u M e = G.edgeCost u j M e := by
  apply intervalIntegral.integral_congr_Ioo_of_le (G.length_pos e).le
  intro x hx
  dsimp only
  rw [((h.edge_equation e).state_derivative x hx).deriv]
  field_simp [ne_of_gt (G.conductance_pos e x ⟨hx.1.le, hx.2.le⟩)]

/-- Exact cost-energy identity for every real height, as in the manuscript. -/
theorem WeakGraphEquation.cost_energy_identity [Fintype V] [Fintype E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (h : WeakGraphEquation G κ U u) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) (M : ℝ) :
    G.totalMass * M = (∑ v, κ v * U v ^ 2) + ∑ e, G.weakEdgeCost u M e := by
  obtain ⟨j, hj⟩ := h.to_strong hκ hanchor
  simp_rw [hj.weakEdgeCost_eq M]
  exact hj.cost_energy_identity M

/-- The normalized deficit is now an identity for the independently defined
weak state. Sharp edge excesses and their equality classification remain separate. -/
theorem WeakGraphEquation.deficit_normalized [Fintype V] [Fintype E] [Nonempty E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (h : WeakGraphEquation G κ U u) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (t : E → ℝ) (ht : ∀ e, 0 < t e) (M : ℝ) :
    M - G.totalMass / (∑ v, κ v) - G.totalMass / (8 * ∑ e, 1 / t e) =
      G.totalMass / (∑ v, κ v) * ((1 / 2 : ℝ) * ∑ v, ∑ w,
        (κ v * U v / G.totalMass) * (κ w * U w / G.totalMass) *
          (U v - U w) ^ 2 / (U v * U w)) +
      (∑ e, (G.weakEdgeCost u M e - t e * G.edgeMass e ^ 2 / 8)) / G.totalMass +
      (∑ e, 1 / t e) / (8 * G.totalMass) *
        (∑ e, 1 / (t e * ∑ d, 1 / t d) *
          (t e * G.edgeMass e - G.totalMass / (∑ d, 1 / t d)) ^ 2) := by
  obtain ⟨j, hj⟩ := h.to_strong hκ hanchor
  simp_rw [hj.weakEdgeCost_eq M]
  exact hj.deficit_normalized hκ hanchor t ht M

end TimeTraps.Graph
