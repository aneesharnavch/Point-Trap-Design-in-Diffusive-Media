module

public import TimeTraps.Analysis.IntervalPointOperator
public import TimeTraps.Analysis.IntervalSobolevRepresentation

@[expose] public section

/-! The actual physical variational equation gives the distributional slope
derivative on any subinterval with no contact in its open interior.
Contacts at either endpoint of that subinterval are allowed. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace
open scoped Topology ContDiff

variable {ι : Type*} [Fintype ι]

theorem UnitPointProblem.weak_slope_derivative (P : UnitPointProblem ι)
    (f : UnitIntervalL2) {u : ℝ → ℝ}
    (hweak : ∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
      unitPointForm P.diffusivity P.strength P.site u v = ∫ x in (0 : ℝ)..1, f x * v x)
    {l r : ℝ} (hl : 0 ≤ l) (hr : r ≤ 1)
    (hsite : ∀ i, P.site i ∉ Ioo l r) :
    IntervalWeakDerivative (deriv u) (fun x => -f x / P.diffusivity) l r := by
  intro φ hc _ hs
  have hs₀ : tsupport φ ⊆ Ioo (0 : ℝ) 1 :=
    hs.trans (Ioo_subset_Ioo hl hr)
  have hφ : IntervalEnergy φ 0 1 := intervalEnergy_of_continuous_derivative zero_le_one
    hc.continuous.continuousOn (hc.continuous_deriv (by simp)).continuousOn
    (fun x _ => (hc.differentiable (by simp) x).hasDerivAt)
  have hzero (i : ι) : φ (P.site i) = 0 := by
    by_contra hn
    exact hsite i (hs (subset_closure hn))
  have he := hweak φ hφ
  simp only [unitPointForm, hzero, mul_zero, Finset.sum_const_zero, add_zero] at he
  rw [intervalSobolev_test_integral zero_le_one (tsupport_deriv_subset.trans hs₀),
    intervalSobolev_test_integral zero_le_one hs₀] at he
  have hi : (∫ x, (-f x / P.diffusivity) * φ x) =
      -(∫ x, f x * φ x) / P.diffusivity := by
    calc
      _ = ∫ x, -(f x * φ x) / P.diffusivity := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := by rw [integral_div, integral_neg]
  rw [hi, neg_div, neg_neg]
  exact (eq_div_iff P.diffusivity_pos.ne').mpr (by simpa only [mul_comm] using he)

theorem UnitPointProblem.operator_slope_weakDerivative (P : UnitPointProblem ι)
    (f : UnitIntervalL2) {u : ℝ → ℝ} (hu : IntervalEnergy u 0 1)
    (hgraph : ((ofEnergy hu zero_lt_one).state, f) ∈ P.operator.graph)
    {l r : ℝ} (hl : 0 ≤ l) (hr : r ≤ 1)
    (hsite : ∀ i, P.site i ∉ Ioo l r) :
    IntervalWeakDerivative (deriv u) (fun x => -f x / P.diffusivity) l r :=
  P.weak_slope_derivative f ((P.operator_graph_iff_physical f hu).mp hgraph) hl hr hsite

theorem UnitPointProblem.solution_slope_weakDerivative (P : UnitPointProblem ι)
    (f : UnitIntervalL2) {l r : ℝ} (hl : 0 ≤ l) (hr : r ≤ 1)
    (hsite : ∀ i, P.site i ∉ Ioo l r) :
    IntervalWeakDerivative (deriv ((P.solution f).representative zero_lt_one))
      (fun x => -f x / P.diffusivity) l r :=
  P.weak_slope_derivative f (P.solution_physical f) hl hr hsite

end TimeTraps.Analysis
