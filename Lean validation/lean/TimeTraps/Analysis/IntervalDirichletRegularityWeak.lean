module

public import TimeTraps.Analysis.IntervalDirichletPhysicalOperator
public import TimeTraps.Analysis.IntervalSobolevRepresentation

@[expose] public section

/-! Interior smooth tests are legitimate tests for the actual absorbing
boundary weak equation. On a contact-free open subinterval they determine
the distributional derivative of the slope, with the original L2 forcing. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace
open scoped Topology ContDiff

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem IntervalDirichletBoundary.test_zero_of_tsupport_subset
    (B : IntervalDirichletBoundary l r) {φ : ℝ → ℝ} (hs : tsupport φ ⊆ Ioo l r) :
    ∀ x ∈ B.zero_sites, φ x = 0 := by
  intro x hx
  have hout : x ∉ Ioo l r := by
    rcases B.boundary_only x hx with rfl | rfl <;> simp
  by_contra hn
  exact hout (hs (subset_closure hn))

theorem DirichletPointProblem.weak_slope_derivative (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ}
    (hweak : ∀ v : ℝ → ℝ, IntervalEnergy v l r →
      (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      intervalPointForm P.diffusivity P.strength P.site l r u v = ∫ x in l..r, f x * v x)
    {a b : ℝ} (hl : l ≤ a) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    IntervalWeakDerivative (deriv u) (fun x => -f x / P.diffusivity) a b := by
  intro φ hc _ hs
  have hs₀ : tsupport φ ⊆ Ioo l r := hs.trans (Ioo_subset_Ioo hl hr)
  have hφ : IntervalEnergy φ l r := intervalEnergy_of_continuous_derivative P.boundary.interval_pos.le
    hc.continuous.continuousOn (hc.continuous_deriv (by simp)).continuousOn
    (fun x _ => (hc.differentiable (by simp) x).hasDerivAt)
  have hzero (i : ι) : φ (P.site i) = 0 := by
    by_contra hn
    exact hsite i (hs (subset_closure hn))
  have he := hweak φ hφ (P.boundary.test_zero_of_tsupport_subset hs₀)
  simp only [intervalPointForm, hzero, mul_zero, Finset.sum_const_zero, add_zero] at he
  rw [intervalSobolev_test_integral P.boundary.interval_pos.le (tsupport_deriv_subset.trans hs₀),
    intervalSobolev_test_integral P.boundary.interval_pos.le hs₀] at he
  have hi : (∫ x, (-f x / P.diffusivity) * φ x) =
      -(∫ x, f x * φ x) / P.diffusivity := by
    calc
      _ = ∫ x, -(f x * φ x) / P.diffusivity := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := by rw [integral_div, integral_neg]
  rw [hi, neg_div, neg_neg]
  exact (eq_div_iff P.diffusivity_pos.ne').mpr (by simpa only [mul_comm] using he)

theorem DirichletPointProblem.operator_slope_weakDerivative (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {u : ℝ → ℝ} (hu : IntervalEnergy u l r)
    (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0)
    (hgraph : (P.boundary.stateL (P.boundary.ofEnergy hu huz), f) ∈ P.operator.graph)
    {a b : ℝ} (hl : l ≤ a) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    IntervalWeakDerivative (deriv u) (fun x => -f x / P.diffusivity) a b :=
  P.weak_slope_derivative f ((P.operator_graph_iff_physical f hu huz).mp hgraph) hl hr hsite

theorem DirichletPointProblem.solution_slope_weakDerivative (P : DirichletPointProblem ι l r)
    (f : IntervalSobolevL2 l r) {a b : ℝ} (hl : l ≤ a) (hr : b ≤ r)
    (hsite : ∀ i, P.site i ∉ Ioo a b) :
    IntervalWeakDerivative (deriv ((P.solution f).val.representative P.boundary.interval_pos))
      (fun x => -f x / P.diffusivity) a b :=
  P.weak_slope_derivative f (P.solution_physical f) hl hr hsite

end TimeTraps.Analysis
