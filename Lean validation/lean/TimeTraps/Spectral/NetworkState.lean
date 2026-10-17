module

public import TimeTraps.Spectral.NetworkTerminalTest
public import TimeTraps.Spectral.CircleGeometry
public import TimeTraps.Spectral.SineInterpolation

@[expose] public section

/-! Positive physical network eigenstates obtained from the exact nodal kernel.
The energy space, gap differential equations and vertex reaction law are all checked. -/

namespace TimeTraps.Spectral

open Set TimeTraps.Analysis TimeTraps.Graph

variable {V E : Type*} [Fintype E]

structure PositiveNetworkEigenstate (P : SpectralNetwork V E) (ev : ℝ) where
  nodal : V → ℝ
  state : E → ℝ → ℝ
  slope : E → ℝ → ℝ
  energy : GraphEnergy P.geometry nodal state
  nodal_positive : ∀ v, 0 < nodal v
  positive : ∀ e x, x ∈ Icc 0 (P.length e) → 0 < state e x
  slope_continuous : ∀ e, ContinuousOn (slope e) (Icc 0 (P.length e))
  state_derivative : ∀ e x, x ∈ Ioo 0 (P.length e) → HasDerivAt (state e) (slope e x) x
  slope_derivative : ∀ e x, x ∈ Ioo 0 (P.length e) →
    HasDerivAt (slope e) (-(ev / P.diffusivity) * state e x) x
  vertex_balance : ∀ v, P.strength v * nodal v = vertexFlux P.tail P.head
    (fun e => P.diffusivity * slope e 0) (fun e => P.diffusivity * slope e (P.length e)) v

noncomputable def SpectralNetwork.sineState (P : SpectralNetwork V E)
    (k : ℝ) (U : V → ℝ) (e : E) : ℝ → ℝ :=
  sineInterpolation k (P.length e) (U (P.tail e)) (U (P.head e))

noncomputable def SpectralNetwork.sineStateSlope (P : SpectralNetwork V E)
    (k : ℝ) (U : V → ℝ) (e : E) : ℝ → ℝ :=
  sineInterpolationSlope k (P.length e) (U (P.tail e)) (U (P.head e))

omit [Fintype E] in
theorem SpectralNetwork.sineState_energy (P : SpectralNetwork V E) {k : ℝ}
    (hk : 0 < k) (hp : P.BelowFirstPole k) (U : V → ℝ) :
    GraphEnergy P.geometry U (P.sineState k U) := by
  refine ⟨fun e => sineInterpolation_energy (P.length_pos e).le k _ _, ?_, ?_⟩
  · intro e
    exact sineInterpolation_left
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (mul_pos hk (P.length_pos e)) (hp.2 e))) _ _
  · intro e
    exact sineInterpolation_right
      (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (mul_pos hk (P.length_pos e)) (hp.2 e))) _ _

omit [Fintype E] in
theorem SpectralNetwork.sineState_left_flux (P : SpectralNetwork V E) {k : ℝ}
    (hk : 0 < k) (U : V → ℝ) (e : E) :
    P.diffusivity * P.sineStateSlope k U e 0 = P.leftEndpointFlux k U e := by
  unfold sineStateSlope leftEndpointFlux
  rw [sineInterpolationSlope_left, P.edgeWeight_eq hk]
  ring

omit [Fintype E] in
theorem SpectralNetwork.sineState_right_flux (P : SpectralNetwork V E) {k : ℝ}
    (hk : 0 < k) (U : V → ℝ) (e : E) :
    P.diffusivity * P.sineStateSlope k U e (P.length e) = P.rightEndpointFlux k U e := by
  unfold sineStateSlope rightEndpointFlux
  rw [sineInterpolationSlope_right, P.edgeWeight_eq hk]
  ring

noncomputable def SpectralNetwork.positiveSineEigenstate (P : SpectralNetwork V E) {k : ℝ}
    (hk : 0 < k) (hp : P.BelowFirstPole k) (U : V → ℝ) (hU : ∀ v, 0 < U v)
    (hop : ∀ v, P.nodalOperator k U v = 0) :
    PositiveNetworkEigenstate P (P.diffusivity * k ^ 2) where
  nodal := U
  state := P.sineState k U
  slope := P.sineStateSlope k U
  energy := P.sineState_energy hk hp U
  nodal_positive := hU
  positive := fun e _ hx => sineInterpolation_pos hk (P.length_pos e) (hp.2 e)
    (hU (P.tail e)) (hU (P.head e)) hx
  slope_continuous := fun e => (sineInterpolationSlope_continuous k (P.length e) _ _).continuousOn
  state_derivative := fun e x _ => sineInterpolation_hasDerivAt k (P.length e) _ _ x
  slope_derivative := by
    intro e x _
    rw [mul_div_cancel_left₀ _ (ne_of_gt P.diffusivity_pos)]
    exact sineInterpolationSlope_hasDerivAt k (P.length e) _ _ x
  vertex_balance := by
    intro v
    have h := sub_eq_zero.mp (hop v)
    have hl : (fun e => P.diffusivity * P.sineStateSlope k U e 0) = P.leftEndpointFlux k U :=
      funext (P.sineState_left_flux hk U)
    have hr : (fun e => P.diffusivity * P.sineStateSlope k U e (P.length e)) = P.rightEndpointFlux k U :=
      funext (P.sineState_right_flux hk U)
    rw [hl, hr]
    exact h

theorem SpectralNetwork.positive_eigenstate_exists [Fintype V] [Nonempty V] [Nonempty E]
    (P : SpectralNetwork V E) : ∃ ev : ℝ, 0 < ev ∧ Nonempty (PositiveNetworkEigenstate P ev) := by
  obtain ⟨k, hk, hp, _, U, hU, hop⟩ := P.positive_nodal_state_exists
  exact ⟨P.diffusivity * k ^ 2, mul_pos P.diffusivity_pos (sq_pos_of_pos hk),
    ⟨P.positiveSineEigenstate hk hp U hU hop⟩⟩

omit [Fintype E] in
theorem CircleProblem.positive_eigenstate_exists {n : ℕ} (C : CircleProblem n) :
    ∃ ev : ℝ, 0 < ev ∧ Nonempty (PositiveNetworkEigenstate C.network ev) := by
  let : Nonempty (Fin n) := ⟨⟨0, C.count_pos⟩⟩
  exact C.network.positive_eigenstate_exists

end TimeTraps.Spectral
