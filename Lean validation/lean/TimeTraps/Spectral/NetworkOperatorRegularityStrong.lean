module

public import TimeTraps.Spectral.NetworkOperatorRegularityGreen

@[expose] public section

/-! The exact AC/L2 strong network equation. Kirchhoff/contact laws are
derived from arbitrary nodal affine tests in the forward direction;
in the converse they cancel the signed edge boundary terms for every
GraphEnergy test. No continuous forcing or edge C2 premise is imposed. -/

namespace TimeTraps.Spectral

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Graph
open scoped Topology

variable {V E : Type*} [Fintype V] [Fintype E]

structure NetworkL2StrongEquation (P : SpectralNetwork V E) (f : GraphL2Product P.geometry)
    (U : V → ℝ) (u j : E → ℝ → ℝ) : Prop where
  edge_regularity : ∀ e, IntervalSlopeRegularity (u e) (j e)
    (fun x => -(f e) x / P.diffusivity) 0 (P.length e)
  tail_value : ∀ e, u e 0 = U (P.tail e)
  head_value : ∀ e, u e (P.length e) = U (P.head e)
  vertex_balance : ∀ v, P.diffusivity * P.operatorSlopeFlux j v = P.strength v * U v

variable {P : SpectralNetwork V E} {f : GraphL2Product P.geometry}
variable {U : V → ℝ} {u j : E → ℝ → ℝ}

omit [Fintype V] in
theorem NetworkL2StrongEquation.energy (h : NetworkL2StrongEquation P f U u j) :
    GraphEnergy P.geometry U u :=
  ⟨fun e => (h.edge_regularity e).state_energy, h.tail_value, h.head_value⟩

omit [Fintype V] in
theorem NetworkL2StrongEquation.second_derivative_ae (h : NetworkL2StrongEquation P f U u j)
    (e : E) : deriv (deriv (u e)) =ᵐ[volume.restrict (Ioo 0 (P.length e))]
      fun x => -(f e) x / P.diffusivity :=
  (h.edge_regularity e).second_derivative_ae

omit [Fintype V] in
theorem NetworkL2StrongEquation.slope_traces (h : NetworkL2StrongEquation P f U u j) (e : E) :
    Tendsto (deriv (u e)) (𝓝[>] 0) (𝓝 (j e 0)) ∧
      Tendsto (deriv (u e)) (𝓝[<] (P.length e)) (𝓝 (j e (P.length e))) :=
  ⟨(h.edge_regularity e).left_trace (P.length_pos e),
    (h.edge_regularity e).right_trace (P.length_pos e)⟩

theorem NetworkL2WeakEquation.vertex_balance (h : NetworkL2WeakEquation P f U u)
    (hj : ∀ e, IntervalSlopeRegularity (u e) (j e)
      (fun x => -(f e) x / P.diffusivity) 0 (P.length e)) (v : V) :
    P.diffusivity * P.operatorSlopeFlux j v = P.strength v * U v := by
  classical
  let W : V → ℝ := fun w => if w = v then 1 else 0
  have he := h.weak_form W (P.operatorNodeTest W) (P.operatorNodeTest_energy W)
  have hg := P.operator_slopes_green f hj (P.operatorNodeTest_energy W)
  have hb : (∑ w, P.diffusivity * P.operatorSlopeFlux j w * W w) =
      ∑ w, P.strength w * U w * W w := by linarith
  simpa only [W, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] using hb

theorem NetworkL2WeakEquation.exists_strong (h : NetworkL2WeakEquation P f U u) :
    ∃ j : E → ℝ → ℝ, NetworkL2StrongEquation P f U u j := by
  choose j hj using h.edge_regularity
  exact ⟨j, hj, h.energy.tail_value, h.energy.head_value, h.vertex_balance hj⟩

theorem NetworkL2StrongEquation.to_weak (h : NetworkL2StrongEquation P f U u j) :
    NetworkL2WeakEquation P f U u := by
  refine ⟨h.energy, ?_⟩
  intro W w hw
  have hg := P.operator_slopes_green f h.edge_regularity hw
  simp_rw [h.vertex_balance] at hg
  linarith

theorem networkL2_weak_iff_strong :
    NetworkL2WeakEquation P f U u ↔ ∃ j, NetworkL2StrongEquation P f U u j := by
  constructor
  · exact NetworkL2WeakEquation.exists_strong
  · rintro ⟨j, hj⟩
    exact hj.to_weak

end TimeTraps.Spectral
