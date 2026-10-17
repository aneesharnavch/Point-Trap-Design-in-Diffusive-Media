module

public import TimeTraps.Probability.ReflectedRobinEndpointMeanLifetime
public import TimeTraps.Interval.EndpointConverse

@[expose] public section

/-! The worst-start endpoint objective is independently defined from
the literal physical mean killing time on the original complete design
class, including architectures with no interior reaction. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval

variable {A : EndpointArchitecture} {B : IntervalMedium} {K : ℝ}

def reflectedRobinEndpointLifetimeExpectation (E : EndpointPhysicalDesign A B K) (x : ℝ) : ℝ :=
  reflectedRobinEndpointMeanLifetime E.geometry E.reactions x

def reflectedRobinEndpointLifetimeWorst (E : EndpointPhysicalDesign A B K) : ℝ :=
  sSup (reflectedRobinEndpointLifetimeExpectation E '' Icc B.source.left B.source.right)

theorem reflectedRobinEndpointLifetimeExpectation_eqOn (E : EndpointPhysicalDesign A B K) :
    EqOn (reflectedRobinEndpointLifetimeExpectation E) E.state (Icc B.source.left B.source.right) := by
  have hs : E.geometry.source = B.source := congrArg IntervalMedium.source E.medium_eq
  change EqOn (reflectedRobinEndpointMeanLifetime E.geometry E.reactions) E.state
    (Icc B.source.left B.source.right)
  rw [← hs]
  exact reflectedRobinEndpointMeanLifetime_eqOn E.equation

theorem reflectedRobinEndpointLifetimeExpectation_weak_equation (E : EndpointPhysicalDesign A B K) :
    EndpointWeakEquation E.geometry E.reactions (reflectedRobinEndpointLifetimeExpectation E) :=
  reflectedRobinEndpointMeanLifetime_weak_equation E.geometry E.reactions

theorem reflectedRobinEndpointLifetimeWorst_isGreatest (E : EndpointPhysicalDesign A B K) :
    IsGreatest (reflectedRobinEndpointLifetimeExpectation E '' Icc B.source.left B.source.right)
      E.cost := by
  rw [(reflectedRobinEndpointLifetimeExpectation_eqOn E).image_eq]
  exact E.cost_isGreatest

theorem reflectedRobinEndpointLifetimeWorst_eq (E : EndpointPhysicalDesign A B K) :
    reflectedRobinEndpointLifetimeWorst E = E.cost :=
  (reflectedRobinEndpointLifetimeWorst_isGreatest E).csSup_eq

theorem reflectedRobinEndpointLifetimeWorst_values_eq (A : EndpointArchitecture) (B : IntervalMedium) (K : ℝ) :
    range (fun E : EndpointPhysicalDesign A B K => reflectedRobinEndpointLifetimeWorst E) =
      range (fun E : EndpointPhysicalDesign A B K => E.cost) := by
  simp only [reflectedRobinEndpointLifetimeWorst_eq]

end TimeTraps.Probability

end
