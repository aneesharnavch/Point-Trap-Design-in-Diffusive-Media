module

public import TimeTraps.Analysis.EdgeReconstruction

@[expose] public section

/-!
Green's identity for an edge, first with continuously differentiable test
functions, and the exact state-energy identity. Extension to all interval
energy-space test functions remains a separate obligation.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory

/-- Integration by parts follows from the flux equation and the product rule. -/
theorem EdgeEquation.green_identity {a f u j : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (hlr : l ≤ r) (hf : ContinuousOn f (Icc l r))
    (ψ ψ' : ℝ → ℝ) (hψ : ContinuousOn ψ (Icc l r))
    (hψ' : ContinuousOn ψ' (Icc l r))
    (hdψ : ∀ x ∈ Ioo l r, HasDerivAt ψ (ψ' x) x) :
    (∫ x in l..r, j x * ψ' x) =
      (∫ x in l..r, f x * ψ x) + j r * ψ r - j l * ψ l := by
  have hprod : ∀ x ∈ Ioo l r,
      HasDerivAt (fun y => j y * ψ y) (-f x * ψ x + j x * ψ' x) x := by
    intro x hx
    exact (h.flux_derivative x hx).mul (hdψ x hx)
  have hi₁ : IntervalIntegrable (fun x => -f x * ψ x) volume l r :=
    (hf.neg.mul hψ).intervalIntegrable_of_Icc hlr
  have hi₂ : IntervalIntegrable (fun x => j x * ψ' x) volume l r :=
    (h.flux_continuous.mul hψ').intervalIntegrable_of_Icc hlr
  have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr
    (h.flux_continuous.mul hψ) hprod (hi₁.add hi₂)
  rw [intervalIntegral.integral_add hi₁ hi₂] at hid
  simp only [neg_mul, intervalIntegral.integral_neg, Pi.mul_apply] at hid
  linarith

/-- The physical energy identity, using flux squared divided by conductance. -/
theorem EdgeEquation.energy_identity {a f u j : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (hlr : l ≤ r)
    (ha : ContinuousOn a (Icc l r)) (hf : ContinuousOn f (Icc l r))
    (hane : ∀ x ∈ Icc l r, a x ≠ 0) :
    (∫ x in l..r, j x ^ 2 / a x) =
      (∫ x in l..r, f x * u x) + j r * u r - j l * u l := by
  have hid := h.green_identity hlr hf u (fun x => j x / a x) h.state_continuous
    (h.flux_continuous.div ha hane) h.state_derivative
  have heq : (∫ x in l..r, j x ^ 2 / a x) = ∫ x in l..r, j x * (j x / a x) := by
    apply intervalIntegral.integral_congr
    intro x _
    ring
  exact heq.trans hid

end TimeTraps.Analysis
