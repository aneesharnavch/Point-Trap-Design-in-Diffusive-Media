module

public import TimeTraps.Probability.ReversibleResistanceMeanLifetime
public import TimeTraps.Interval.GlobalOptimization

@[expose] public section

/-! The arbitrary continuous-medium worst-start objective is defined
from the ordinary expectation of the actual first-attainment lifetime.
Its equality with the original independent physical cost is a theorem,
using the constructed process and full weak mean identity. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval

variable {A : IntervalMedium} {n : ℕ} {K : ℝ}

def reversibleLifetimeExpectation (E : IntervalDesign A n K) (x : ℝ) : ℝ :=
  reversibleResistanceMeanLifetime E.geometry.medium x E.geometry.site E.strength

def reversibleLifetimeWorst (E : IntervalDesign A n K) : ℝ :=
  sSup (reversibleLifetimeExpectation E '' Icc E.geometry.source.left E.geometry.source.right)

theorem reversibleLifetimeExpectation_eqOn (E : IntervalDesign A n K) :
    EqOn (reversibleLifetimeExpectation E) E.state
      (Icc E.geometry.source.left E.geometry.source.right) :=
  reversibleResistanceMeanLifetime_eqOn E.partition.size_pos E.strength_pos E.equation

theorem reversibleLifetimeExpectation_weak_equation (E : IntervalDesign A n K) :
    WeakIntervalEquation E.geometry E.strength (reversibleLifetimeExpectation E) :=
  E.equation.congr_state (reversibleLifetimeExpectation_eqOn E).symm

theorem reversibleLifetimeWorst_isGreatest (E : IntervalDesign A n K) :
    IsGreatest (reversibleLifetimeExpectation E '' Icc E.geometry.source.left E.geometry.source.right)
      E.cost := by
  rw [(reversibleLifetimeExpectation_eqOn E).image_eq]
  exact E.equation.essentialNorm_isGreatest (fun i => (E.strength_pos i).le)
    ⟨⟨0, E.partition.size_pos⟩, E.strength_pos _⟩

theorem reversibleLifetimeWorst_eq (E : IntervalDesign A n K) :
    reversibleLifetimeWorst E = E.cost :=
  (reversibleLifetimeWorst_isGreatest E).csSup_eq

theorem reversibleLifetimeWorst_values_eq (A : IntervalMedium) (n : ℕ) (K : ℝ) :
    range (fun E : IntervalDesign A n K => reversibleLifetimeWorst E) =
      range (fun E : IntervalDesign A n K => E.cost) := by
  simp only [reversibleLifetimeWorst_eq]

end TimeTraps.Probability

end
