module

public import TimeTraps.Analysis.IntervalEnergy
public import TimeTraps.Analysis.EdgeReconstruction

@[expose] public section

/-!
Energy-space membership of the strong edge state, and Green's identity for
all absolutely continuous tests. This includes the full interval H1 test class.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory

/-- Changing an extension outside the physical edge does not change its equation. -/
theorem EdgeEquation.congr_state {a f u v j : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (hvu : EqOn v u (Icc l r)) : EdgeEquation a f l r v j := by
  refine ⟨h.state_continuous.congr hvu, h.flux_continuous, ?_, h.flux_derivative⟩
  intro x hx
  apply (h.state_derivative x hx).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact hvu ⟨hy.1.le, hy.2.le⟩

theorem EdgeEquation.state_energy {a f u j : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (hlr : l ≤ r)
    (ha : ContinuousOn a (Icc l r)) (hane : ∀ x ∈ Icc l r, a x ≠ 0) :
    IntervalEnergy u l r :=
  intervalEnergy_of_continuous_derivative hlr h.state_continuous
    (h.flux_continuous.div ha hane) h.state_derivative

theorem EdgeEquation.flux_absolutelyContinuous {a f u j : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (hlr : l ≤ r) (hf : ContinuousOn f (Icc l r)) :
    AbsolutelyContinuousOnInterval j l r :=
  (intervalEnergy_of_continuous_derivative hlr h.flux_continuous hf.neg h.flux_derivative).absolutelyContinuous

/-- Integration by parts holds for every absolutely continuous test, with no
continuity assumption on its derivative. -/
theorem EdgeEquation.green_identity_ac {a f u j ψ : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (hlr : l ≤ r) (hf : ContinuousOn f (Icc l r))
    (hψ : AbsolutelyContinuousOnInterval ψ l r) :
    (∫ x in l..r, j x * deriv ψ x) =
      (∫ x in l..r, f x * ψ x) + j r * ψ r - j l * ψ l := by
  have hid := (h.flux_absolutelyContinuous hlr hf).integral_mul_deriv_eq_deriv_mul hψ
  have hflux : (∫ x in l..r, deriv j x * ψ x) = -(∫ x in l..r, f x * ψ x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_Ioo_of_le hlr
    intro x hx
    dsimp only
    rw [(h.flux_derivative x hx).deriv]
    ring
  rw [hflux] at hid
  linarith

/-- The flux form of Green's identity agrees with the physical weighted
derivative form, including for H1 tests. -/
theorem EdgeEquation.green_identity_energy {a f u j ψ : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (hlr : l ≤ r) (hf : ContinuousOn f (Icc l r))
    (hane : ∀ x ∈ Icc l r, a x ≠ 0) (hψ : IntervalEnergy ψ l r) :
    (∫ x in l..r, a x * deriv u x * deriv ψ x) =
      (∫ x in l..r, f x * ψ x) + j r * ψ r - j l * ψ l := by
  have heq : (∫ x in l..r, a x * deriv u x * deriv ψ x) = ∫ x in l..r, j x * deriv ψ x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hlr
    intro x hx
    dsimp only
    rw [(h.state_derivative x hx).deriv]
    field_simp [hane x ⟨hx.1.le, hx.2.le⟩]
  rw [heq]
  exact h.green_identity_ac hlr hf hψ.absolutelyContinuous

end TimeTraps.Analysis
