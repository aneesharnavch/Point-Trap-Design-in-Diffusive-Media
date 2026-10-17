module

public import TimeTraps.Analysis.IntervalEnergy
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! Globally smooth Lagrange tests isolate individual distinct partition
nodes.  They are admissible physical H1 tests on the whole unit interval. -/

namespace TimeTraps.Analysis

open Set
open scoped ContDiff

noncomputable def intervalNodeTest {V : Type*} [Fintype V] [DecidableEq V]
    (q : V → ℝ) (v : V) (x : ℝ) : ℝ :=
  ∏ w ∈ Finset.univ.erase v, (x - q w) / (q v - q w)

theorem intervalNodeTest_contDiff {V : Type*} [Fintype V] [DecidableEq V]
    (q : V → ℝ) (v : V) : ContDiff ℝ ∞ (intervalNodeTest q v) := by
  apply contDiff_prod
  intro w _
  exact (contDiff_id.sub contDiff_const).div_const _

theorem intervalNodeTest_node {V : Type*} [Fintype V] [DecidableEq V]
    (q : V → ℝ) (hq : Function.Injective q) (v w : V) :
    intervalNodeTest q v (q w) = if w = v then 1 else 0 := by
  classical
  by_cases hw : w = v
  · subst w
    rw [if_pos rfl]
    unfold intervalNodeTest
    apply Finset.prod_eq_one
    intro j hj
    exact div_self (sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hj).1 (hq he).symm))
  · rw [if_neg hw]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hw, Finset.mem_univ w⟩)
    simp

theorem intervalNodeTest_energy {V : Type*} [Fintype V] [DecidableEq V]
    (q : V → ℝ) (v : V) : IntervalEnergy (intervalNodeTest q v) 0 1 :=
  intervalEnergy_of_continuous_derivative zero_le_one
    (intervalNodeTest_contDiff q v).continuous.continuousOn
    ((intervalNodeTest_contDiff q v).continuous_deriv (by simp)).continuousOn
    (fun x _ => ((intervalNodeTest_contDiff q v).differentiable (by simp) x).hasDerivAt)

end TimeTraps.Analysis
