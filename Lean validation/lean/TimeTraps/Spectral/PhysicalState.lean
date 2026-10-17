module

public import TimeTraps.Spectral.PhysicalProblem
public import TimeTraps.Spectral.GroundStateExistence

@[expose] public section

/-!
The exact shooting solutions are assembled on the actual physical interval.
Their original global H1 membership, positivity, gap differential equation,
reflection and point-interaction laws are proved from the construction.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval TimeTraps.Graph
open scoped BigOperators Topology

variable {n : ℕ}

noncomputable def SpectralProblem.nodeValues (P : SpectralProblem n) (k : ℝ) : Fin (n + 2) → ℝ :=
  Fin.snoc (fun e => P.shooting.value k e 0)
    (P.shooting.value k (Fin.last n) (P.shooting.gap (Fin.last n)))

theorem SpectralProblem.shooting_energy (P : SpectralProblem n) (k : ℝ) :
    GraphEnergy P.geometry.graph (P.nodeValues k) (P.shooting.value k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    change IntervalEnergy (P.shooting.value k e) 0 (P.shooting.gap e)
    have hi : Continuous (fun x : ℝ => (k, x)) := continuous_const.prodMk continuous_id
    have hv := (P.shooting.value_continuous e).comp hi
    have hd := (P.shooting.slope_continuous e).comp hi
    exact intervalEnergy_of_continuous_derivative (P.shooting.gap_pos e).le hv.continuousOn hd.continuousOn
      (fun x _ => P.shooting.value_hasDerivAt k e x)
  · intro e
    change P.shooting.value k e 0 = P.nodeValues k e.castSucc
    rw [nodeValues, Fin.snoc_castSucc]
  · intro e
    change P.shooting.value k e (P.shooting.gap e) = P.nodeValues k e.succ
    refine Fin.lastCases ?_ (fun i => ?_) e
    · change P.shooting.value k (Fin.last n) (P.shooting.gap (Fin.last n)) = P.nodeValues k (Fin.last (n + 1))
      rw [nodeValues, Fin.snoc_last]
    · rw [nodeValues, Fin.succ_castSucc, Fin.snoc_castSucc]
      exact (P.shooting.value_matching k i).symm

noncomputable def SpectralProblem.shootingState (P : SpectralProblem n) (k : ℝ) : ℝ → ℝ :=
  P.geometry.assembledState (P.nodeValues k) (P.shooting.value k)

theorem SpectralProblem.shootingState_continuous (P : SpectralProblem n) (k : ℝ) :
    Continuous (P.shootingState k) := P.geometry.assembledState_continuous (P.shooting_energy k)

theorem SpectralProblem.shootingState_gap (P : SpectralProblem n) (k : ℝ) (e : Fin (n + 1))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (P.shooting.gap e)) :
    P.shootingState k (P.geometry.node e.castSucc + x) = P.shooting.value k e x :=
  P.geometry.assembledState_gap (P.shooting_energy k) e hx

theorem SpectralProblem.shootingState_energy (P : SpectralProblem n) (k : ℝ) :
    IntervalEnergy (P.shootingState k) 0 P.length := by
  apply P.geometry.assembledState_energy_of_piecewise (P.shooting_energy k)
    (g := P.shooting.slope k)
  · intro e
    have hi : Continuous (fun x : ℝ => (k, x)) := continuous_const.prodMk continuous_id
    have h := (P.shooting.slope_continuous e).comp hi
    exact h.continuousOn
  · intro e x _
    exact P.shooting.value_hasDerivAt k e x

theorem SpectralProblem.shootingState_left (P : SpectralProblem n) (k : ℝ) : P.shootingState k 0 = 1 := by
  have h := P.shootingState_gap k 0 ⟨le_rfl, (P.shooting.gap_pos 0).le⟩
  rw [add_zero] at h
  change P.shootingState k (P.geometry.node 0) = P.shooting.value k 0 0 at h
  rw [P.geometry.node_first, P.geometry_left, P.shooting.left_value] at h
  exact h

theorem SpectralProblem.shootingState_trap (P : SpectralProblem n) (k : ℝ) (i : Fin n) :
    P.shootingState k (P.site i) = P.shooting.value k i.castSucc (P.shooting.gap i.castSucc) := by
  have h := P.shootingState_gap k i.castSucc ⟨(P.shooting.gap_pos i.castSucc).le, le_rfl⟩
  rw [P.shooting_gap, add_sub_cancel] at h
  change P.shootingState k (P.geometry.site i) = _ at h
  rwa [P.geometry_site] at h

theorem SpectralProblem.shootingState_positive (P : SpectralProblem n) {k : ℝ}
    (hk : ∀ e, ∀ x ∈ Icc (0 : ℝ) (P.shooting.gap e), 0 < P.shooting.value k e x)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) P.length) : 0 < P.shootingState k x := by
  obtain ⟨e, he⟩ := P.geometry.gap_cover hx
  have ht : x - P.geometry.node e.castSucc ∈ Icc (0 : ℝ) (P.shooting.gap e) :=
    ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  have h := P.shootingState_gap k e ht
  rw [add_sub_cancel] at h
  rw [h]
  exact hk e _ ht

theorem SpectralProblem.shootingState_gap_hasDerivAt (P : SpectralProblem n) (k : ℝ)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (P.shooting.gap e)) :
    HasDerivAt (fun t => P.shootingState k (P.geometry.node e.castSucc + t))
      (P.shooting.slope k e x) x := by
  have he : (fun t => P.shootingState k (P.geometry.node e.castSucc + t)) =ᶠ[nhds x]
      P.shooting.value k e := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact P.shootingState_gap k e (Ioo_subset_Icc_self ht)
  exact (P.shooting.value_hasDerivAt k e x).congr_of_eventuallyEq he

theorem SpectralProblem.shooting_slope_equation (P : SpectralProblem n) (k : ℝ)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (P.shooting.gap e)) :
    HasDerivAt (P.shooting.slope k e)
      (-(P.diffusivity * k ^ 2 / P.diffusivity) * P.shootingState k (P.geometry.node e.castSucc + x)) x := by
  rw [mul_div_cancel_left₀ _ (ne_of_gt P.diffusivity_pos), P.shootingState_gap k e hx]
  exact P.shooting.slope_hasDerivAt k e x

theorem SpectralProblem.shooting_reaction_jump (P : SpectralProblem n) (k : ℝ) (i : Fin n) :
    P.diffusivity * (P.shooting.slope k i.succ 0 - P.shooting.slope k i.castSucc (P.shooting.gap i.castSucc)) =
      P.strength i * P.shootingState k (P.site i) := by
  rw [P.shooting.slope_jump, add_sub_cancel_left, P.shooting_reaction, P.shootingState_trap]
  field_simp [ne_of_gt P.diffusivity_pos]

/-- A positive physical eigenstate is specified by its own H1 representative
and gap slopes. No shooting formula, scalar optimum, or Rayleigh conclusion
is part of this definition. -/
structure PositiveEigenstate (P : SpectralProblem n) (eigenvalue : ℝ) where
  state : ℝ → ℝ
  slope : Fin (n + 1) → ℝ → ℝ
  energy : IntervalEnergy state 0 P.length
  positive : ∀ x ∈ Icc (0 : ℝ) P.length, 0 < state x
  slope_continuous : ∀ e, ContinuousOn (slope e) (Icc (0 : ℝ) (P.shooting.gap e))
  state_derivative : ∀ e, ∀ x ∈ Ioo (0 : ℝ) (P.shooting.gap e),
    HasDerivAt (fun t => state (P.geometry.node e.castSucc + t)) (slope e x) x
  slope_derivative : ∀ e, ∀ x ∈ Ioo (0 : ℝ) (P.shooting.gap e),
    HasDerivAt (slope e) (-(eigenvalue / P.diffusivity) * state (P.geometry.node e.castSucc + x)) x
  left_reflecting : slope 0 0 = 0
  right_reflecting : slope (Fin.last n) (P.shooting.gap (Fin.last n)) = 0
  reaction_jump : ∀ i, P.diffusivity * (slope i.succ 0 - slope i.castSucc (P.shooting.gap i.castSucc)) =
    P.strength i * state (P.site i)

theorem SpectralProblem.positive_eigenstate_exists (P : SpectralProblem n) :
    ∃ eigenvalue : ℝ, 0 < eigenvalue ∧ ∃ E : PositiveEigenstate P eigenvalue, E.state 0 = 1 := by
  obtain ⟨k, hk, hR, hp⟩ := P.shooting.positive_neumann_parameter P.count_pos
  have heigenvalue : 0 < P.diffusivity * k ^ 2 := mul_pos P.diffusivity_pos (sq_pos_of_pos hk.1)
  refine ⟨P.diffusivity * k ^ 2, heigenvalue, {
    state := P.shootingState k
    slope := P.shooting.slope k
    energy := P.shootingState_energy k
    positive := fun x hx => P.shootingState_positive hp hx
    slope_continuous := ?_
    state_derivative := fun e x hx => P.shootingState_gap_hasDerivAt k e hx
    slope_derivative := fun e x hx => P.shooting_slope_equation k e (Ioo_subset_Icc_self hx)
    left_reflecting := P.shooting.left_slope k
    right_reflecting := hR
    reaction_jump := P.shooting_reaction_jump k }, P.shootingState_left k⟩
  intro e
  have hi : Continuous (fun x : ℝ => (k, x)) := continuous_const.prodMk continuous_id
  have h := (P.shooting.slope_continuous e).comp hi
  exact h.continuousOn

end TimeTraps.Spectral
