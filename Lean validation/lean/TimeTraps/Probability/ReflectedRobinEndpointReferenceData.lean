module

public import TimeTraps.Probability.ReflectedRobinEndpointWeak
public import TimeTraps.Probability.ReflectedRobinWeakInfinite
public import TimeTraps.Probability.ReflectedRobinStoppingData

@[expose] public section

/-! The paper's endpoint architecture as an actual reference reaction
family. Endpoint labels exist even when the interior family is empty.
The positive lower bound on clock speed follows from the original medium. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal

variable {A : EndpointArchitecture} {K : ℝ}

def reflectedRobinEndpointPhysicalSite (D : OrderedMedium A.interiorCount) :
    Fin A.interiorCount ⊕ Bool → ℝ :=
  Sum.elim D.site (fun b => if b then D.source.right else D.source.left)

def reflectedRobinEndpointReferenceData (D : OrderedMedium A.interiorCount)
    (R : EndpointReactions A K) : ReflectedRobinReactionData (Fin A.interiorCount ⊕ Bool) where
  length := D.medium.resistanceLength
  length_pos := D.medium.resistanceLength_pos
  diffusivity := 1
  diffusivity_pos := zero_lt_one
  site := reflectedRobinSite D.medium.resistanceLength (fun i => D.medium.resistance (D.site i))
  strength := reflectedRobinStrength R.interiorStrength R.leftStrength R.rightStrength
  strength_nonneg := reflectedRobinStrength_nonneg (fun i => (R.interior_pos i).le)
    R.left_nonneg R.right_nonneg

theorem reflectedRobinEndpointPhysicalSite_resistance (D : OrderedMedium A.interiorCount) :
    (fun i => D.medium.resistance (reflectedRobinEndpointPhysicalSite D i)) =
      reflectedRobinSite D.medium.resistanceLength (fun i => D.medium.resistance (D.site i)) := by
  funext i
  cases i with
  | inl i => rfl
  | inr b =>
    cases b <;> simp only [reflectedRobinEndpointPhysicalSite, reflectedRobinSite, Sum.elim_inr,
      Bool.false_eq_true, ↓reduceIte]
    · exact D.medium.resistance_left
    · exact D.medium.resistance_right

theorem reflectedRobinEndpoint_speed_lower (D : OrderedMedium A.interiorCount) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ Icc 0 D.medium.resistanceLength, c ≤ D.medium.resistanceSpeed y := by
  obtain ⟨y, hy, hm⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) D.medium.resistanceLength).Nonempty from
      ⟨0, le_rfl, D.medium.resistanceLength_pos.le⟩)
    D.medium.resistanceSpeed_continuous.continuousOn
  exact ⟨_, D.medium.resistanceSpeed_pos y, fun z hz => hm hz⟩

theorem reflectedRobinEndpoint_survival_integrable
    {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) (x : ℝ) :
    IntegrableOn (fun r : ℝ => reflectedAtomicMeanSurvival D.medium.resistanceLength 1 x
      (reflectedRobinEndpointReferenceData D R).site (reflectedRobinEndpointReferenceData D R).strength
      r.toNNReal) (Ioi (0 : ℝ)) := by
  obtain ⟨c, hc, hcg⟩ := reflectedRobinEndpoint_speed_lower D
  exact (endpointWeakEquation_resistance hu).actual_survival_integrable
    D.medium.resistanceLength_pos zero_lt_one
    (fun i => D.medium.resistance_interior (D.site_interior i))
    (fun i => (R.interior_pos i).le) R.left_nonneg R.right_nonneg
    D.medium.resistanceSpeed_continuous.continuousOn
    (fun z _ => (hu.positive _ (D.medium.resistanceInverse_mem z)).le) hc hcg x

theorem reflectedRobinEndpoint_cost_expectation
    {D : OrderedMedium A.interiorCount} {R : EndpointReactions A K} {u : ℝ → ℝ}
    (hu : EndpointWeakEquation D R u) {x : ℝ} (hx : x ∈ Icc D.source.left D.source.right) :
    reflectedRobinCostExpectation (reflectedRobinEndpointReferenceData D R)
      D.medium.resistanceSpeed (D.medium.resistance x) = u x := by
  obtain ⟨c, hc, hcg⟩ := reflectedRobinEndpoint_speed_lower D
  have he := (endpointWeakEquation_resistance hu).actual_expected_infinite
    D.medium.resistanceLength_pos zero_lt_one
    (fun i => D.medium.resistance_interior (D.site_interior i))
    (fun i => (R.interior_pos i).le) R.left_nonneg R.right_nonneg
    D.medium.resistanceSpeed_continuous.continuousOn
    (fun z _ => (hu.positive _ (D.medium.resistanceInverse_mem z)).le) hc hcg
    (D.medium.resistance x)
  rw [reflectedFold_eq_self D.medium.resistanceLength D.medium.resistanceLength_pos _ (D.medium.resistance_mem hx)] at he
  simpa only [reflectedRobinSurvival_eq_atomic _ zero_lt_one, reflectedRobinCostExpectation,
    reflectedRobinEndpointReferenceData, reflectedAtomicWeightedValue,
    IntervalMedium.resistanceProfile, D.medium.resistanceInverse_resistance hx] using he

end TimeTraps.Probability

end
