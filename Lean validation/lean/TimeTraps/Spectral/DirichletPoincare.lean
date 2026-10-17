module

public import TimeTraps.Spectral.DirichletCosine

@[expose] public section

/-!
Sharp Dirichlet and mixed Neumann--Dirichlet inequalities on the original
H1 space. The proof takes a continuous frequency limit of regular positive
cosine comparisons, so no division by a zero boundary value is used.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

theorem energy_bound_at_frequency_limit {v : ℝ → ℝ} {l r K : ℝ} (hK : 0 < K)
    (h : ∀ k ∈ Ioo (0 : ℝ) K,
      k ^ 2 * (∫ x in l..r, v x ^ 2) ≤ ∫ x in l..r, deriv v x ^ 2) :
    K ^ 2 * (∫ x in l..r, v x ^ 2) ≤ ∫ x in l..r, deriv v x ^ 2 := by
  have hc : K ∈ closure (Ioo (0 : ℝ) K) := by
    rw [closure_Ioo hK.ne]
    exact ⟨hK.le, le_rfl⟩
  exact ContinuousWithinAt.closure_le hc
    ((continuous_id.pow 2).mul continuous_const).continuousWithinAt
    continuous_const.continuousWithinAt h

theorem dirichlet_poincare {v : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hv : IntervalEnergy v 0 L) (hleft : v 0 = 0) (hright : v L = 0) :
    (Real.pi / L) ^ 2 * (∫ x in (0 : ℝ)..L, v x ^ 2) ≤
      ∫ x in (0 : ℝ)..L, deriv v x ^ 2 := by
  apply energy_bound_at_frequency_limit (div_pos Real.pi_pos hL)
  intro k hk
  have hkL : k * L < Real.pi := (lt_div_iff₀ hL).mp hk.2
  apply dirichletCosine_energy_lower_bound (c := L / 2) hL.le hv ?_
    (Or.inl hleft) (Or.inl hright)
  intro x hx
  constructor <;>
    nlinarith [mul_nonneg hk.1.le hx.1, mul_nonneg hk.1.le (sub_nonneg.mpr hx.2)]

theorem neumann_dirichlet_poincare {v : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hv : IntervalEnergy v 0 L) (hright : v L = 0) :
    (Real.pi / (2 * L)) ^ 2 * (∫ x in (0 : ℝ)..L, v x ^ 2) ≤
      ∫ x in (0 : ℝ)..L, deriv v x ^ 2 := by
  apply energy_bound_at_frequency_limit (div_pos Real.pi_pos (by positivity))
  intro k hk
  have hkL : k * (2 * L) < Real.pi := (lt_div_iff₀ (by positivity)).mp hk.2
  apply dirichletCosine_energy_lower_bound (c := 0) hL.le hv ?_
    (Or.inr (by simp [dirichletCosineSlope])) (Or.inl hright)
  intro x hx
  constructor <;>
    nlinarith [Real.pi_pos, mul_nonneg hk.1.le hx.1,
      mul_nonneg hk.1.le (sub_nonneg.mpr hx.2)]

theorem dirichlet_neumann_poincare {v : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hv : IntervalEnergy v 0 L) (hleft : v 0 = 0) :
    (Real.pi / (2 * L)) ^ 2 * (∫ x in (0 : ℝ)..L, v x ^ 2) ≤
      ∫ x in (0 : ℝ)..L, deriv v x ^ 2 := by
  apply energy_bound_at_frequency_limit (div_pos Real.pi_pos (by positivity))
  intro k hk
  have hkL : k * (2 * L) < Real.pi := (lt_div_iff₀ (by positivity)).mp hk.2
  apply dirichletCosine_energy_lower_bound (c := L) hL.le hv ?_
    (Or.inl hleft) (Or.inr (by simp [dirichletCosineSlope]))
  intro x hx
  constructor <;>
    nlinarith [Real.pi_pos, mul_nonneg hk.1.le hx.1,
      mul_nonneg hk.1.le (sub_nonneg.mpr hx.2)]

end TimeTraps.Spectral
