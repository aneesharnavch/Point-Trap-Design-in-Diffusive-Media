module

public import TimeTraps.Analysis.EdgeWeak
public import TimeTraps.Graph.MetricIdentities

@[expose] public section

/-!
The metric-graph energy space and weak equation. Test functions are arbitrary
absolutely continuous edge functions with L2 derivatives and matching vertex
traces; no edge differential equation is assumed of a weak state.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {V E : Type*}

structure GraphEnergy (G : MetricGraph V E) (U : V → ℝ) (u : E → ℝ → ℝ) : Prop where
  edge_energy : ∀ e, IntervalEnergy (u e) 0 (G.length e)
  tail_value : ∀ e, u e 0 = U (G.tail e)
  head_value : ∀ e, u e (G.length e) = U (G.head e)

structure WeakGraphEquation [Fintype V] [Fintype E]
    (G : MetricGraph V E) (κ U : V → ℝ) (u : E → ℝ → ℝ) : Prop where
  energy : GraphEnergy G U u
  weak_form : ∀ (Ψ : V → ℝ) (ψ : E → ℝ → ℝ), GraphEnergy G Ψ ψ →
    (∑ e, ∫ x in 0..G.length e, G.conductance e x * deriv (u e) x * deriv (ψ e) x) +
      (∑ v, κ v * U v * Ψ v) = ∑ e, ∫ x in 0..G.length e, G.source e x * ψ e x

theorem GraphEnergy.const (G : MetricGraph V E) (c : ℝ) :
    GraphEnergy G (fun _ => c) (fun _ _ => c) :=
  ⟨fun e => IntervalEnergy.const c 0 (G.length e), fun _ => rfl, fun _ => rfl⟩

theorem GraphEnergy.source_integrable {G : MetricGraph V E} {U : V → ℝ}
    {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) (e : E) :
    IntervalIntegrable (fun x => G.source e x * u e x) volume 0 (G.length e) := by
  have huc : ContinuousOn (u e) (Icc 0 (G.length e)) := by
    simpa only [uIcc_of_le (G.length_pos e).le] using (hu.edge_energy e).continuousOn
  exact ((G.source_continuous e).mul huc).intervalIntegrable_of_Icc (G.length_pos e).le

theorem GraphEnergy.sub {G : MetricGraph V E} {U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : GraphEnergy G U u) (hw : GraphEnergy G W w) :
    GraphEnergy G (fun v => U v - W v) (fun e x => u e x - w e x) := by
  refine ⟨fun e => (hu.edge_energy e).sub (hw.edge_energy e), ?_, ?_⟩
  · intro e
    rw [hu.tail_value, hw.tail_value]
  · intro e
    rw [hu.head_value, hw.head_value]

theorem GraphEquation.energy_membership [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) : GraphEnergy G U u := by
  refine ⟨?_, h.tail_value, h.head_value⟩
  intro e
  exact (h.edge_equation e).state_energy (G.length_pos e).le (G.conductance_continuous e)
    (fun x hx => ne_of_gt (G.conductance_pos e x hx))

/-- Every strong solution satisfies the weak equation for the full energy
space, not just for smooth tests. -/
theorem GraphEquation.to_weak [Fintype V] [Fintype E] {G : MetricGraph V E}
    {κ U : V → ℝ} {u j : E → ℝ → ℝ} (h : GraphEquation G κ U u j) :
    WeakGraphEquation G κ U u := by
  refine ⟨h.energy_membership, ?_⟩
  intro Ψ ψ hψ
  have hedge : ∀ e, (∫ x in 0..G.length e,
      G.conductance e x * deriv (u e) x * deriv (ψ e) x) =
      (∫ x in 0..G.length e, G.source e x * ψ e x) +
        (j e (G.length e) * Ψ (G.head e) - j e 0 * Ψ (G.tail e)) := by
    intro e
    have he := (h.edge_equation e).green_identity_energy (G.length_pos e).le
      (G.source_continuous e) (fun x hx => ne_of_gt (G.conductance_pos e x hx)) (hψ.edge_energy e)
    rw [hψ.tail_value e, hψ.head_value e] at he
    linarith
  have hboundary : (∑ e, (j e (G.length e) * Ψ (G.head e) - j e 0 * Ψ (G.tail e))) =
      -(∑ v, κ v * U v * Ψ v) := by
    rw [incidence_boundary_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    rw [← h.vertex_balance v]
    ring
  simp_rw [hedge]
  rw [Finset.sum_add_distrib, hboundary]
  ring

theorem weak_graph_state_exists [Fintype V] [Fintype E] (G : MetricGraph V E) (κ : V → ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    ∃ U u, WeakGraphEquation G κ U u := by
  obtain ⟨U, u, j, h⟩ := graph_state_exists G κ hκ hanchor
  exact ⟨U, u, h.to_weak⟩

/-- Testing the difference of two weak solutions gives zero total energy. -/
theorem WeakGraphEquation.difference_energy_zero [Fintype V] [Fintype E]
    {G : MetricGraph V E} {κ U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : WeakGraphEquation G κ U u) (hw : WeakGraphEquation G κ W w) :
    (∑ e, ∫ x in 0..G.length e,
      G.conductance e x * deriv (fun y => u e y - w e y) x ^ 2) +
      (∑ v, κ v * (U v - W v) ^ 2) = 0 := by
  let δ : E → ℝ → ℝ := fun e x => u e x - w e x
  let Δ : V → ℝ := fun v => U v - W v
  have hδ : GraphEnergy G Δ δ := hu.energy.sub hw.energy
  have h₁ := hu.weak_form Δ δ hδ
  have h₂ := hw.weak_form Δ δ hδ
  have he : (∑ e, ∫ x in 0..G.length e, G.conductance e x * deriv (δ e) x ^ 2) =
      (∑ e, ∫ x in 0..G.length e, G.conductance e x * deriv (u e) x * deriv (δ e) x) -
      (∑ e, ∫ x in 0..G.length e, G.conductance e x * deriv (w e) x * deriv (δ e) x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    have hpair := (hu.energy.edge_energy e).bilinear_sub_left (hw.energy.edge_energy e)
      (hδ.edge_energy e) (by simpa only [uIcc_of_le (G.length_pos e).le]
        using G.conductance_continuous e)
    simpa only [δ, pow_two, mul_assoc] using hpair
  have hv : (∑ v, κ v * Δ v ^ 2) =
      (∑ v, κ v * U v * Δ v) - (∑ v, κ v * W v * Δ v) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _
    dsimp only [Δ]
    ring
  change (∑ e, ∫ x in 0..G.length e, G.conductance e x * deriv (δ e) x ^ 2) +
    (∑ v, κ v * Δ v ^ 2) = 0
  rw [he, hv]
  linarith

/-- The graph energy has trivial kernel when the connected graph has a
reactive vertex. Constancy is derived from absolute continuity and zero energy. -/
theorem GraphEnergy.zero_of_energy_zero [Fintype V] [Fintype E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v)
    (hzero : (∑ e, ∫ x in 0..G.length e, G.conductance e x * deriv (u e) x ^ 2) +
      (∑ v, κ v * U v ^ 2) = 0) :
    (∀ v, U v = 0) ∧ ∀ e x, x ∈ Icc 0 (G.length e) → u e x = 0 := by
  have he_nonneg : ∀ e, 0 ≤ ∫ x in 0..G.length e, G.conductance e x * deriv (u e) x ^ 2 := by
    intro e
    exact intervalIntegral.integral_nonneg (G.length_pos e).le
      (fun x hx => mul_nonneg (G.conductance_pos e x hx).le (sq_nonneg _))
  have hr_nonneg : ∀ v, 0 ≤ κ v * U v ^ 2 := fun v => mul_nonneg (hκ v) (sq_nonneg _)
  have hEs := Finset.sum_nonneg (fun e (_ : e ∈ Finset.univ) => he_nonneg e)
  have hRs := Finset.sum_nonneg (fun v (_ : v ∈ Finset.univ) => hr_nonneg v)
  have hEzero : (∑ e, ∫ x in 0..G.length e, G.conductance e x * deriv (u e) x ^ 2) = 0 := by
    linarith
  have hRzero : (∑ v, κ v * U v ^ 2) = 0 := by linarith
  have he_zero : ∀ e, (∫ x in 0..G.length e, G.conductance e x * deriv (u e) x ^ 2) = 0 :=
    fun e => (Finset.sum_eq_zero_iff_of_nonneg (fun d _ => he_nonneg d)).mp hEzero e (Finset.mem_univ e)
  have hconst : ∀ e x, x ∈ Icc 0 (G.length e) → u e x = u e 0 := by
    intro e
    exact (hu.edge_energy e).constant_of_energy_zero (G.length_pos e).le
      (G.conductance_continuous e) (G.conductance_pos e) (he_zero e)
  have hedge : ∀ e, U (G.tail e) = U (G.head e) := by
    intro e
    rw [← hu.tail_value e, ← hu.head_value e]
    exact (hconst e (G.length e) ⟨(G.length_pos e).le, le_rfl⟩).symm
  have hUconst : ∀ v w, U v = U w := by
    intro v w
    induction G.connected v w with
    | rel v w hvw =>
        obtain ⟨e, rfl, rfl⟩ := hvw
        exact hedge e
    | refl v => rfl
    | symm v w _ ih => exact ih.symm
    | trans v w z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  obtain ⟨v₀, hv₀⟩ := hanchor
  have hr₀ := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hr_nonneg v)).mp hRzero v₀
    (Finset.mem_univ v₀)
  have hvzero : U v₀ = 0 := sq_eq_zero_iff.mp
    ((mul_eq_zero.mp hr₀).resolve_left (ne_of_gt hv₀))
  have hUzero : ∀ v, U v = 0 := fun v => (hUconst v v₀).trans hvzero
  refine ⟨hUzero, ?_⟩
  intro e x hx
  exact (hconst e x hx).trans ((hu.tail_value e).trans (hUzero _))

theorem weak_graph_state_unique [Fintype V] [Fintype E]
    {G : MetricGraph V E} {κ U W : V → ℝ} {u w : E → ℝ → ℝ}
    (hu : WeakGraphEquation G κ U u) (hw : WeakGraphEquation G κ W w)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    U = W ∧ ∀ e, EqOn (u e) (w e) (Icc 0 (G.length e)) := by
  obtain ⟨hv, he⟩ := (hu.energy.sub hw.energy).zero_of_energy_zero hκ hanchor
    (hu.difference_energy_zero hw)
  constructor
  · funext v
    exact sub_eq_zero.mp (hv v)
  · intro e x hx
    exact sub_eq_zero.mp (he e x hx)

/-- Weak regularity follows by comparison with the constructed strong state;
the weak solution was not assumed to possess a continuous flux. -/
theorem WeakGraphEquation.to_strong [Fintype V] [Fintype E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation G κ U u) (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    ∃ j, GraphEquation G κ U u j := by
  obtain ⟨W, w, j, hw⟩ := graph_state_exists G κ hκ hanchor
  obtain ⟨hUW, heq⟩ := weak_graph_state_unique hu hw.to_weak hκ hanchor
  refine ⟨j, ⟨fun e => (hw.edge_equation e).congr_state (heq e),
    hu.energy.tail_value, hu.energy.head_value, ?_⟩⟩
  intro v
  rw [hUW]
  exact hw.vertex_balance v

/-- Full equivalence with the independently defined H1 weak equation. -/
theorem weak_graph_iff_strong [Fintype V] [Fintype E]
    {G : MetricGraph V E} {κ U : V → ℝ} {u : E → ℝ → ℝ}
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) :
    WeakGraphEquation G κ U u ↔ ∃ j, GraphEquation G κ U u j := by
  constructor
  · intro h
    exact h.to_strong hκ hanchor
  · rintro ⟨j, h⟩
    exact h.to_weak

end TimeTraps.Graph
