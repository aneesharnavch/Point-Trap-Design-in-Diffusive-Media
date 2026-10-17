module

public import TimeTraps.Analysis.EdgeReconstruction
public import TimeTraps.Graph.EdgeBarrier

@[expose] public section

/-!
The quadratic profile and sharp costs are derived from the differential
equation with constant coefficients. Coefficients need only be constant on
the physical closed edge; extensions outside it are immaterial.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis

theorem constant_edge_of_eqOn {a f u j : ℝ → ℝ} {A ρ L : ℝ}
    (h : EdgeEquation a f 0 L u j)
    (ha : EqOn a (fun _ => A) (Icc 0 L)) (hf : EqOn f (fun _ => ρ) (Icc 0 L)) :
    EdgeEquation (fun _ => A) (fun _ => ρ) 0 L u j := by
  refine ⟨h.state_continuous, h.flux_continuous, ?_, ?_⟩
  · intro x hx
    simpa only [ha ⟨hx.1.le, hx.2.le⟩] using h.state_derivative x hx
  · intro x hx
    simpa only [hf ⟨hx.1.le, hx.2.le⟩] using h.flux_derivative x hx

theorem constant_edge_flux {u j : ℝ → ℝ} {A ρ L x : ℝ}
    (h : EdgeEquation (fun _ => A) (fun _ => ρ) 0 L u j) (hx : x ∈ Icc 0 L) :
    j x = j 0 - ρ * x := by
  simpa [sourcePrimitive, mul_comm] using h.flux_formula continuousOn_const hx

/-- The quadratic state is a consequence of the equation and initial data. -/
theorem constant_edge_state {u j : ℝ → ℝ} {A ρ L x : ℝ}
    (h : EdgeEquation (fun _ => A) (fun _ => ρ) 0 L u j) (hx : x ∈ Icc 0 L) :
    u x = u 0 + j 0 / A * x - ρ / (2 * A) * x ^ 2 := by
  let v : ℝ → ℝ := fun y => u 0 + j 0 / A * y - ρ / (2 * A) * y ^ 2
  have hg : ContinuousOn (fun y => (j 0 - ρ * y) / A) (Icc 0 L) :=
    ((continuous_const.sub (continuous_const.mul continuous_id)).div_const A).continuousOn
  have hdu : ∀ y ∈ Ioo 0 L, HasDerivAt u ((j 0 - ρ * y) / A) y := by
    intro y hy
    rw [← constant_edge_flux h ⟨hy.1.le, hy.2.le⟩]
    exact h.state_derivative y hy
  have hv : ContinuousOn v (Icc 0 L) :=
    ((continuous_const.add (continuous_const.mul continuous_id)).sub
      (continuous_const.mul (continuous_id.pow 2))).continuousOn
  have hdv : ∀ y ∈ Ioo 0 L, HasDerivAt v ((j 0 - ρ * y) / A) y := by
    intro y _
    convert! (((hasDerivAt_id y).const_mul (j 0 / A)).const_add (u 0)).sub
      (((hasDerivAt_id y).pow 2).const_mul (ρ / (2 * A))) using 1
    simp only [id_eq]
    ring
  have hid := (integral_derivative_to_point h.state_continuous hg hdu hx).symm.trans
    (integral_derivative_to_point hv hg hdv hx)
  dsimp only [v] at hid
  linarith

theorem constant_edge_centered {u j : ℝ → ℝ} {A ρ L x : ℝ}
    (h : EdgeEquation (fun _ => A) (fun _ => ρ) 0 L u j)
    (hA : A ≠ 0) (hρ : ρ ≠ 0) (M : ℝ) (hx : x ∈ Icc 0 L) :
    M - u x = (M - u 0 - j 0 ^ 2 / (2 * A * ρ)) +
      (ρ / A) / 2 * (x - j 0 / ρ) ^ 2 := by
  rw [constant_edge_state h hx]
  field_simp
  ring

/-- Exact identification with the previously proved sharp quadratic cost. -/
theorem constant_edge_cost_eq {u j : ℝ → ℝ} {A ρ L : ℝ}
    (h : EdgeEquation (fun _ => A) (fun _ => ρ) 0 L u j)
    (hL : 0 ≤ L) (hA : A ≠ 0) (hρ : ρ ≠ 0) (M : ℝ) :
    (∫ x in 0..L, (ρ * (M - u x) + j x ^ 2 / A)) =
      edgeCost ρ (ρ / A) (M - u 0 - j 0 ^ 2 / (2 * A * ρ)) (j 0 / ρ) L := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hxI : x ∈ Icc 0 L := by simpa only [uIcc_of_le hL] using hx
  dsimp only
  rw [constant_edge_centered h hA hρ M hxI, constant_edge_flux h hxI]
  field_simp
  ring

theorem constant_edge_ordinary_barrier {u j : ℝ → ℝ} {A ρ L M : ℝ}
    (h : EdgeEquation (fun _ => A) (fun _ => ρ) 0 L u j)
    (hA : 0 < A) (hρ : 0 < ρ) (hL : 0 < L) (hM : ∀ x ∈ Icc 0 L, u x ≤ M) :
    (ρ * L) ^ 2 * (L / A) / 8 ≤ ∫ x in 0..L, (ρ * (M - u x) + j x ^ 2 / A) ∧
      ((∫ x in 0..L, (ρ * (M - u x) + j x ^ 2 / A)) = (ρ * L) ^ 2 * (L / A) / 8 ↔
        M - u 0 - j 0 ^ 2 / (2 * A * ρ) = 0 ∧ j 0 / ρ = L / 2) := by
  have hw : ∀ x ∈ Icc 0 L, 0 ≤ (M - u 0 - j 0 ^ 2 / (2 * A * ρ)) +
      (ρ / A) / 2 * (x - j 0 / ρ) ^ 2 := by
    intro x hx
    rw [← constant_edge_centered h (ne_of_gt hA) (ne_of_gt hρ) M hx]
    exact sub_nonneg.mpr (hM x hx)
  rw [constant_edge_cost_eq h hL.le (ne_of_gt hA) (ne_of_gt hρ) M]
  have hscale : (ρ * L) ^ 2 * (L / A) / 8 = ρ * (ρ / A) * L ^ 3 / 8 := by ring
  rw [hscale]
  exact ordinary_edge_barrier hρ (div_pos hρ hA) hL hw

/-- A zero flux at the right endpoint forces the reflecting quadratic and
the factor-four bound, with equality exactly when the tip reaches M. -/
theorem constant_edge_reflecting_right {u j : ℝ → ℝ} {A ρ L M : ℝ}
    (h : EdgeEquation (fun _ => A) (fun _ => ρ) 0 L u j)
    (hA : 0 < A) (hρ : 0 < ρ) (hL : 0 < L)
    (hM : ∀ x ∈ Icc 0 L, u x ≤ M) (hj : j L = 0) :
    (ρ * L) ^ 2 * (L / A) / 2 ≤ ∫ x in 0..L, (ρ * (M - u x) + j x ^ 2 / A) ∧
      ((∫ x in 0..L, (ρ * (M - u x) + j x ^ 2 / A)) = (ρ * L) ^ 2 * (L / A) / 2 ↔
        u L = M) := by
  have hflux := constant_edge_flux h ⟨hL.le, le_rfl⟩
  have hz : j 0 / ρ = L := (div_eq_iff (ne_of_gt hρ)).mpr (by linarith)
  have hd : M - u 0 - j 0 ^ 2 / (2 * A * ρ) = M - u L := by
    have he := constant_edge_centered h (ne_of_gt hA) (ne_of_gt hρ) M ⟨hL.le, le_rfl⟩
    simpa only [hz, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using he.symm
  rw [constant_edge_cost_eq h hL.le (ne_of_gt hA) (ne_of_gt hρ) M, hz, hd]
  have hscale : (ρ * L) ^ 2 * (L / A) / 2 = ρ * (ρ / A) * L ^ 3 / 2 := by ring
  rw [hscale]
  have hb := reflecting_edge_barrier (q := ρ / A) hρ hL (sub_nonneg.mpr (hM L ⟨hL.le, le_rfl⟩))
  refine ⟨hb.1, hb.2.trans ?_⟩
  exact sub_eq_zero.trans eq_comm

theorem constant_edge_reflecting_left {u j : ℝ → ℝ} {A ρ L M : ℝ}
    (h : EdgeEquation (fun _ => A) (fun _ => ρ) 0 L u j)
    (hA : 0 < A) (hρ : 0 < ρ) (hL : 0 < L)
    (hM : ∀ x ∈ Icc 0 L, u x ≤ M) (hj : j 0 = 0) :
    (ρ * L) ^ 2 * (L / A) / 2 ≤ ∫ x in 0..L, (ρ * (M - u x) + j x ^ 2 / A) ∧
      ((∫ x in 0..L, (ρ * (M - u x) + j x ^ 2 / A)) = (ρ * L) ^ 2 * (L / A) / 2 ↔
        u 0 = M) := by
  rw [constant_edge_cost_eq h hL.le (ne_of_gt hA) (ne_of_gt hρ) M]
  simp only [hj, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
  have hmirror : edgeCost ρ (ρ / A) (M - u 0) 0 L = edgeCost ρ (ρ / A) (M - u 0) L L := by
    rw [edgeCost_eq, edgeCost_eq]
    ring
  rw [hmirror]
  have hscale : (ρ * L) ^ 2 * (L / A) / 2 = ρ * (ρ / A) * L ^ 3 / 2 := by ring
  rw [hscale]
  have hb := reflecting_edge_barrier (q := ρ / A) hρ hL (sub_nonneg.mpr (hM 0 ⟨le_rfl, hL.le⟩))
  exact ⟨hb.1, hb.2.trans (sub_eq_zero.trans eq_comm)⟩

end TimeTraps.Graph
