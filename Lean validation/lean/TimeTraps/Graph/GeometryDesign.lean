module

public import TimeTraps.Graph.GeometryProblem
public import TimeTraps.Analysis.CubicMoment

@[expose] public section

/-!
Admissible physical length/reactivity designs are defined independently of
the proposed optimum. The graph inequality and exact cubic identity give a
bound for every weak state and force the unique lengths at equality.
-/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators Classical

variable {V E : Type*} [Fintype V] [Fintype E]

structure GeometryDesign (P : GeometryProblem V E) (L K : ℝ) where
  length : E → ℝ
  length_pos : ∀ e, 0 < length e
  total_length : ∑ e, length e = L
  strength : V → ℝ
  strength_nonneg : ∀ v, 0 ≤ strength v
  total_strength : ∑ v, strength v = K
  passive_eq : ∀ v, (P.graph length length_pos).IsPassiveTip strength v ↔ P.passive v

def GeometryDesign.graph {P : GeometryProblem V E} {L K : ℝ} (d : GeometryDesign P L K) :
    MetricGraph V E := P.graph d.length d.length_pos

def GeometryDesign.constants {P : GeometryProblem V E} {L K : ℝ} (d : GeometryDesign P L K) :
    EdgeConstants d.graph := P.constants d.length d.length_pos

theorem GeometryDesign.mass {P : GeometryProblem V E} {L K : ℝ} (d : GeometryDesign P L K)
    (e : E) : d.graph.edgeMass e = d.length e := P.graph_mass _ _ e

theorem GeometryDesign.resistance {P : GeometryProblem V E} {L K : ℝ} (d : GeometryDesign P L K)
    (e : E) : d.graph.resistance e = d.length e / P.diffusivity e := P.graph_resistance _ _ e

theorem GeometryDesign.totalMass {P : GeometryProblem V E} {L K : ℝ} (d : GeometryDesign P L K) :
    d.graph.totalMass = L := (P.graph_totalMass _ _).trans d.total_length

theorem GeometryDesign.passive_iff {P : GeometryProblem V E} {L K : ℝ} (d : GeometryDesign P L K)
    (v : V) : d.graph.IsPassiveTip d.strength v ↔ P.passive v := d.passive_eq v

theorem GeometryDesign.marker_passive_iff {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (v : V) : d.graph.IsPassiveTip P.marker v ↔ P.passive v :=
  P.marker_passive _ _ v

theorem GeometryDesign.reflection {P : GeometryProblem V E} {L K : ℝ} (d : GeometryDesign P L K)
    (e : E) : d.graph.reflectionFactor d.strength e = P.reflection e := by
  change (if d.graph.IsPassiveTip d.strength (P.tail e) ∨
    d.graph.IsPassiveTip d.strength (P.head e) then 4 else 1) = _
  simp only [d.passive_iff, GeometryProblem.reflection]

theorem GeometryDesign.strength_anchor {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hK : 0 < K) : ∃ v, 0 < d.strength v := by
  by_contra hn
  push Not at hn
  have hs := Finset.sum_nonpos (s := Finset.univ) (fun v _ => hn v)
  rw [d.total_strength] at hs
  linarith

theorem GeometryDesign.state_exists {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hK : 0 < K) : ∃ U u, WeakGraphEquation d.graph d.strength U u :=
  weak_graph_state_exists d.graph d.strength d.strength_nonneg (d.strength_anchor hK)

theorem GeometryDesign.edge_cubic {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (e : E) :
    d.graph.adjustedResistance d.strength e * d.graph.edgeMass e ^ 2 =
      d.length e ^ 3 / P.scale e ^ 2 := by
  rw [MetricGraph.adjustedResistance, d.reflection e, d.resistance e, d.mass e,
    ← P.scale_relation e]
  field_simp [ne_of_gt (P.reflection_pos e), ne_of_gt (P.scale_pos e)]

theorem GeometryDesign.graph_bound [Nonempty E] {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hK : 0 < K) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation d.graph d.strength U u) :
    L / K + (∑ e, d.length e ^ 3 / P.scale e ^ 2) / (8 * L) ≤ d.graph.essentialNorm u := by
  simpa only [d.totalMass, d.total_strength, d.edge_cubic] using
    (hu.sharp_mass_resistance_bound d.constants d.strength_nonneg (d.strength_anchor hK)).1

theorem GeometryDesign.cubic_bound [Nonempty E] {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hL : 0 < L) :
    L ^ 3 / P.totalScale ^ 2 ≤ (∑ e, d.length e ^ 3 / P.scale e ^ 2) ∧
      ((∑ e, d.length e ^ 3 / P.scale e ^ 2) = L ^ 3 / P.totalScale ^ 2 ↔
        d.length = P.optimalLengths L) := by
  have hb := cubic_length_bound Finset.univ P.scale d.length P.totalScale_pos hL rfl
    d.total_length (fun e _ => P.scale_pos e) (fun e _ => (d.length_pos e).le)
  refine ⟨hb.1, hb.2.trans ?_⟩
  simp only [Finset.mem_univ, forall_const]
  exact ⟨fun h => funext h, fun h e => congrFun h e⟩

omit [Fintype V] in
theorem GeometryProblem.optimalValue_eq_cubic [Nonempty E] (P : GeometryProblem V E)
    {L : ℝ} (hL : 0 < L) (K : ℝ) :
    P.optimalValue L K = L / K + (L ^ 3 / P.totalScale ^ 2) / (8 * L) := by
  unfold GeometryProblem.optimalValue
  congr 1
  field_simp [ne_of_gt hL, ne_of_gt P.totalScale_pos]

/-- The proposed value is a lower bound for every admissible design's actual
weak state; no candidate profile is assumed. -/
theorem GeometryDesign.lower_bound [Nonempty E] {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hL : 0 < L) (hK : 0 < K) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation d.graph d.strength U u) : P.optimalValue L K ≤ d.graph.essentialNorm u := by
  calc
    _ = L / K + (L ^ 3 / P.totalScale ^ 2) / (8 * L) := P.optimalValue_eq_cubic hL K
    _ ≤ L / K + (∑ e, d.length e ^ 3 / P.scale e ^ 2) / (8 * L) :=
      add_le_add (le_refl (L / K)) (div_le_div_of_nonneg_right (d.cubic_bound hL).1
        (show (0 : ℝ) ≤ 8 * L by positivity))
    _ ≤ _ := d.graph_bound hK hu

/-- Equality in the design bound forces every labeled edge length. -/
theorem GeometryDesign.equality_lengths [Nonempty E] {P : GeometryProblem V E} {L K : ℝ}
    (d : GeometryDesign P L K) (hL : 0 < L) (hK : 0 < K) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : WeakGraphEquation d.graph d.strength U u)
    (heq : d.graph.essentialNorm u = P.optimalValue L K) : d.length = P.optimalLengths L := by
  have hb := d.graph_bound hK hu
  rw [heq, P.optimalValue_eq_cubic hL K] at hb
  have hdiv : (∑ e, d.length e ^ 3 / P.scale e ^ 2) / (8 * L) ≤
      (L ^ 3 / P.totalScale ^ 2) / (8 * L) := by linarith
  have hupper := (div_le_div_iff_of_pos_right (show 0 < (8 : ℝ) * L by positivity)).mp hdiv
  exact (d.cubic_bound hL).2.mp (le_antisymm hupper (d.cubic_bound hL).1)

end TimeTraps.Graph
