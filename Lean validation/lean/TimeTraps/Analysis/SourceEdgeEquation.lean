module

public import TimeTraps.Analysis.SourceTransport

@[expose] public section

/-!
Source-coordinate identities derived from the independently defined physical
edge equation. The flux level is arbitrary: it may lie outside the unit
interval. Neither the transformed profile nor its integral cost is assumed.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory

noncomputable def SourceInterval.fluxLevel (P : SourceInterval) (j : ℝ → ℝ) : ℝ :=
  j P.left / P.mass

theorem SourceInterval.physical_flux (P : SourceInterval) {a u j : ℝ → ℝ}
    (h : EdgeEquation a P.density P.left P.right u j) {x : ℝ}
    (hx : x ∈ Icc P.left P.right) :
    j x = P.mass * (P.fluxLevel j - P.coordinate x) := by
  rw [h.flux_formula P.continuous hx, P.sourcePrimitive_eq]
  unfold SourceInterval.fluxLevel
  field_simp [ne_of_gt P.mass_pos]

theorem SourceInterval.transformed_flux (P : SourceInterval) {a u j : ℝ → ℝ}
    (h : EdgeEquation a P.density P.left P.right u j) {z : ℝ} (hz : z ∈ Icc 0 1) :
    P.transformed j z = P.mass * (P.fluxLevel j - z) := by
  change j (P.inverse z) = _
  rw [P.physical_flux h (P.inverse_mem z), P.coordinate_inverse hz]

theorem SourceInterval.normalized_flux_derivative (P : SourceInterval) {a u j : ℝ → ℝ}
    (h : EdgeEquation a P.density P.left P.right u j) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (fun w => P.transformed j w / P.mass) (-1) z := by
  have hd := (P.transformed_derivative hz (h.flux_derivative _ (P.inverse_interior hz))).div_const
    P.mass
  have he : (-P.density (P.inverse z) * (P.mass / P.density (P.inverse z))) / P.mass = -1 := by
    field_simp [ne_of_gt P.mass_pos, ne_of_gt (P.positive _ (P.inverse_mem z))]
  rw [he] at hd
  exact hd

theorem SourceInterval.transformed_state_derivative (P : SourceInterval) {a u j : ℝ → ℝ}
    (h : EdgeEquation a P.density P.left P.right u j)
    (ha : ∀ x ∈ Icc P.left P.right, 0 < a x) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (P.transformed u) (P.weight a z * (P.fluxLevel j - z)) z := by
  have hj : j (P.inverse z) = P.mass * (P.fluxLevel j - z) :=
    P.transformed_flux h (Ioo_subset_Icc_self hz)
  convert P.transformed_derivative hz (h.state_derivative _ (P.inverse_interior hz)) using 1
  rw [hj]
  unfold SourceInterval.weight
  field_simp [ne_of_gt (ha _ (P.inverse_mem z)), ne_of_gt (P.positive _ (P.inverse_mem z))]

theorem SourceInterval.transformed_deficit_derivative (P : SourceInterval) {a u j : ℝ → ℝ}
    (h : EdgeEquation a P.density P.left P.right u j)
    (ha : ∀ x ∈ Icc P.left P.right, 0 < a x) (M : ℝ) {z : ℝ} (hz : z ∈ Ioo 0 1) :
    HasDerivAt (fun w => M - P.transformed u w) (P.weight a z * (z - P.fluxLevel j)) z := by
  have hd := (P.transformed_state_derivative h ha hz).const_sub M
  have he : -(P.weight a z * (P.fluxLevel j - z)) = P.weight a z * (z - P.fluxLevel j) := by ring
  rw [he] at hd
  exact hd

theorem SourceInterval.transformed_deficit_nonneg_iff (P : SourceInterval) (u : ℝ → ℝ) (M : ℝ) :
    (∀ z ∈ Icc 0 1, 0 ≤ M - P.transformed u z) ↔
      ∀ x ∈ Icc P.left P.right, u x ≤ M := by
  constructor
  · intro h x hx
    have hz := h (P.coordinate x) (P.coordinate_mem hx)
    rw [P.transformed_coordinate u hx] at hz
    linarith
  · intro h z _
    exact sub_nonneg.mpr (h _ (P.inverse_mem z))

/-- Transport the actual physical cost, with its original source and flux
terms, to the profile-sensitive integral used in the variable-edge theorem. -/
theorem SourceInterval.edge_cost_transport (P : SourceInterval) {a u j : ℝ → ℝ}
    (h : EdgeEquation a P.density P.left P.right u j)
    (ha : ContinuousOn a (Icc P.left P.right))
    (hapos : ∀ x ∈ Icc P.left P.right, 0 < a x) (M : ℝ) :
    (∫ x in P.left..P.right, (P.density x * (M - u x) + j x ^ 2 / a x)) =
      P.mass * ∫ z in 0..1, (M - P.transformed u z + P.weight a z * (z - P.fluxLevel j) ^ 2) := by
  have hc : ContinuousOn (fun x => P.density x * (M - u x) + j x ^ 2 / a x)
      (Icc P.left P.right) :=
    (P.continuous.mul (continuousOn_const.sub h.state_continuous)).add
      ((h.flux_continuous.pow 2).div ha (fun x hx => ne_of_gt (hapos x hx)))
  calc
    _ = ∫ z in 0..1, (P.density (P.inverse z) * (M - u (P.inverse z)) +
        j (P.inverse z) ^ 2 / a (P.inverse z)) * (P.mass / P.density (P.inverse z)) :=
      (P.inverse_substitution hc).symm
    _ = ∫ z in 0..1, P.mass *
        (M - P.transformed u z + P.weight a z * (z - P.fluxLevel j) ^ 2) := by
      apply intervalIntegral.integral_congr
      intro z hz
      have hz' : z ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hz
      have hj : j (P.inverse z) = P.mass * (P.fluxLevel j - z) := P.transformed_flux h hz'
      dsimp only
      rw [hj]
      unfold SourceInterval.transformed SourceInterval.weight
      simp only [Function.comp_apply]
      field_simp [ne_of_gt (P.positive _ (P.inverse_mem z)), ne_of_gt (hapos _ (P.inverse_mem z))]
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem SourceInterval.passive_left_fluxLevel (P : SourceInterval) (j : ℝ → ℝ)
    (hj : j P.left = 0) : P.fluxLevel j = 0 := by
  simp only [SourceInterval.fluxLevel, hj, zero_div]

theorem SourceInterval.passive_right_fluxLevel (P : SourceInterval) {a u j : ℝ → ℝ}
    (h : EdgeEquation a P.density P.left P.right u j) (hj : j P.right = 0) : P.fluxLevel j = 1 := by
  have hf := P.physical_flux h ⟨P.increasing.le, le_rfl⟩
  rw [hj, P.coordinate_right] at hf
  have hz := (mul_eq_zero.mp hf.symm).resolve_left (ne_of_gt P.mass_pos)
  exact sub_eq_zero.mp hz

end TimeTraps.Analysis
