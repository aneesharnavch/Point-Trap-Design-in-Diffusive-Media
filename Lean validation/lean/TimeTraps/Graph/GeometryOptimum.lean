module

public import TimeTraps.Graph.GeometryDesign

@[expose] public section

/-!
Constructive joint optimization of lengths and vertex reactivities on a fixed
labeled topology. The minimum is over independently admissible designs and
their actual weak states. Equality determines both physical parameter vectors.
-/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped BigOperators Classical

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GeometryProblem.optimalStrengths (P : GeometryProblem V E)
    {L : ℝ} (hL : 0 < L) (K : ℝ) : V → ℝ :=
  (P.optimalGraph hL).allocatedStrength P.marker K

noncomputable def GeometryProblem.optimalDesign (P : GeometryProblem V E)
    {L K : ℝ} (hL : 0 < L) (hK : 0 < K) : GeometryDesign P L K where
  length := P.optimalLengths L
  length_pos := P.optimalLengths_pos hL
  total_length := P.optimalLengths_sum L
  strength := P.optimalStrengths hL K
  strength_nonneg := (P.optimalGraph hL).allocatedStrength_nonneg P.marker hK.le
  total_strength := (P.optimalGraph hL).allocatedStrength_sum P.marker K
    (P.graph_no_two_passive (P.optimalLengths L) (P.optimalLengths_pos hL))
  passive_eq := fun v => ((P.optimalGraph hL).allocatedStrength_passive_iff P.marker hK v).trans
    (P.marker_passive (P.optimalLengths L) (P.optimalLengths_pos hL) v)

theorem GeometryProblem.optimalDesign_graph (P : GeometryProblem V E)
    {L K : ℝ} (hL : 0 < L) (hK : 0 < K) : (P.optimalDesign hL hK).graph = P.optimalGraph hL := rfl

omit [Fintype V] in
theorem GeometryProblem.optimalValue_capacity (P : GeometryProblem V E)
    {L : ℝ} (hL : 0 < L) (K : ℝ) :
    L / K + L / (8 * (P.totalScale ^ 2 / L)) = P.optimalValue L K := by
  unfold GeometryProblem.optimalValue
  congr 1
  field_simp [ne_of_gt hL, ne_of_gt P.totalScale_pos]

/-- The explicit length and strength vectors are admissible and attain the
claimed value through a verified weak solution. -/
theorem GeometryProblem.optimal_design_state (P : GeometryProblem V E)
    {L K : ℝ} (hL : 0 < L) (hK : 0 < K) :
    ∃ U u, WeakGraphEquation (P.optimalDesign hL hK).graph (P.optimalDesign hL hK).strength U u ∧
      (P.optimalDesign hL hK).graph.essentialNorm u = P.optimalValue L K := by
  obtain ⟨_, U, u, hu, hm⟩ := (P.optimalGraph hL).allocated_design_attains
    (P.constants (P.optimalLengths L) (P.optimalLengths_pos hL)) P.marker hK
    (P.graph_no_two_passive _ _) (P.optimal_balanced hL)
  refine ⟨U, u, hu, ?_⟩
  change (P.optimalGraph hL).essentialNorm u = _
  rw [hm, P.optimalGraph_totalMass hL, P.optimal_capacity hL]
  exact P.optimalValue_capacity hL K

theorem GeometryDesign.graph_eq_optimal {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hL : 0 < L) (hlen : d.length = P.optimalLengths L) :
    d.graph = P.optimalGraph hL := by
  have he : (⟨d.length, d.length_pos⟩ : {f : E → ℝ // ∀ e, 0 < f e}) =
      ⟨P.optimalLengths L, P.optimalLengths_pos hL⟩ := Subtype.ext hlen
  exact congrArg (fun ℓ : {f : E → ℝ // ∀ e, 0 < f e} => P.graph ℓ.1 ℓ.2)
    he

omit [Nonempty E] in
theorem GeometryDesign.marker_reflection {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (e : E) : d.graph.reflectionFactor P.marker e = P.reflection e :=
  P.graph_reflection _ _ e

omit [Nonempty E] in
theorem GeometryDesign.adjusted_eq_marker {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (e : E) :
    d.graph.adjustedResistance d.strength e = d.graph.adjustedResistance P.marker e := by
  simp only [MetricGraph.adjustedResistance, d.reflection e, d.marker_reflection e]

omit [Nonempty E] in
theorem GeometryDesign.coreLoad_eq_marker {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (v : V) :
    d.graph.coreLoad d.strength v = d.graph.coreLoad P.marker v := by
  have hs : d.graph.edgeShare d.strength = d.graph.edgeShare P.marker := by
    funext e
    simp only [MetricGraph.edgeShare, d.reflection e, d.marker_reflection e]
  simp only [MetricGraph.coreLoad, hs]

theorem GeometryDesign.boundHeight_of_lengths {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hL : 0 < L) (hlen : d.length = P.optimalLengths L) :
    d.graph.boundHeight d.strength = P.optimalValue L K := by
  unfold MetricGraph.boundHeight
  rw [d.totalMass, d.total_strength]
  simp_rw [d.adjusted_eq_marker]
  rw [d.graph_eq_optimal hL hlen, P.optimal_capacity hL]
  exact P.optimalValue_capacity hL K

omit [Nonempty E] in
theorem GeometryDesign.allocated_eq_of_sharp {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hs : d.graph.HasSharpStrengths d.strength) :
    d.strength = d.graph.allocatedStrength P.marker K := by
  funext v
  by_cases hp : P.passive v
  · have hk := ((d.passive_iff v).mpr hp).1
    have hm := (d.marker_passive_iff v).mpr hp
    rw [hk, MetricGraph.allocatedStrength, MetricGraph.sharpLoad, if_pos hm, mul_zero]
  · have hk : ¬d.graph.IsPassiveTip d.strength v := fun hk => hp ((d.passive_iff v).mp hk)
    have hm : ¬d.graph.IsPassiveTip P.marker v := fun hm => hp ((d.marker_passive_iff v).mp hm)
    have hv := hs v hk
    rw [d.total_strength, d.coreLoad_eq_marker v] at hv
    simpa only [MetricGraph.allocatedStrength, MetricGraph.sharpLoad, if_neg hm] using hv

/-- Equality also forces the unique vertex strength vector on the fixed
labeled optimal geometry. -/
theorem GeometryDesign.equality_strengths {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hL : 0 < L) (hK : 0 < K) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation d.graph d.strength U u)
    (heq : d.graph.essentialNorm u = P.optimalValue L K) : d.strength = P.optimalStrengths hL K := by
  have hlen := d.equality_lengths hL hK hu heq
  have hb := d.boundHeight_of_lengths hL hlen
  have hs := ((hu.sharp_eq_iff_balanced_strengths d.constants d.strength_nonneg
    (d.strength_anchor hK)).mp (heq.trans hb.symm)).2
  rw [d.allocated_eq_of_sharp hs, d.graph_eq_optimal hL hlen]
  rfl

/-- Complete optimizer characterization, with equality of the labeled
length and strength vectors. Weak uniqueness handles every state witness. -/
theorem GeometryDesign.optimal_iff {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hL : 0 < L) (hK : 0 < K) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation d.graph d.strength U u) :
    d.graph.essentialNorm u = P.optimalValue L K ↔
      d.length = P.optimalLengths L ∧ d.strength = P.optimalStrengths hL K := by
  constructor
  · intro heq
    exact ⟨d.equality_lengths hL hK hu heq, d.equality_strengths hL hK hu heq⟩
  · rintro ⟨hlen, hstrength⟩
    obtain ⟨W, w, hw, hm⟩ := P.optimal_design_state hL hK
    have hg := d.graph_eq_optimal hL hlen
    have hk := d.strength_nonneg
    have ha := d.strength_anchor hK
    rw [hstrength] at hk ha
    rw [hg, hstrength] at hu
    have hw' : WeakGraphEquation (P.optimalGraph hL) (P.optimalStrengths hL K) W w := hw
    have he := weak_graph_state_unique hu hw' hk ha
    rw [hg]
    exact (hu.energy.essentialNorm_congr hw'.energy he.2).trans hm

/-- The attainable values are defined using physical designs and the weak
equation, before the candidate minimum is used in any theorem. -/
def GeometryProblem.designValues (P : GeometryProblem V E) (L K : ℝ) : Set ℝ :=
  {M | ∃ d : GeometryDesign P L K, ∃ U u,
    WeakGraphEquation d.graph d.strength U u ∧ d.graph.essentialNorm u = M}

/-- The attained joint minimum over all admissible length/reactivity designs. -/
theorem GeometryProblem.geometry_minimum (P : GeometryProblem V E)
    {L K : ℝ} (hL : 0 < L) (hK : 0 < K) :
    IsLeast (P.designValues L K) (P.optimalValue L K) := by
  constructor
  · obtain ⟨U, u, hu, hm⟩ := P.optimal_design_state hL hK
    exact ⟨P.optimalDesign hL hK, U, u, hu, hm⟩
  · rintro M ⟨d, U, u, hu, rfl⟩
    exact d.lower_bound hL hK hu

end TimeTraps.Graph
