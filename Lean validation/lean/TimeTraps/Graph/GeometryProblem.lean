module

public import TimeTraps.Graph.StrengthAllocation
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
Fixed labeled topology, diffusivities, and passive leaves. Trial lengths
define genuine metric graphs with unit source density. The proposed lengths
are separate from admissibility and are proved positive, budget-correct,
and balanced.
-/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped BigOperators Classical

variable {V E : Type*}

structure GeometryProblem (V E : Type*) where
  tail : E → V
  head : E → V
  connected : IncidenceConnected tail head
  diffusivity : E → ℝ
  diffusivity_pos : ∀ e, 0 < diffusivity e
  passive : V → Prop
  passive_tip : ∀ v, passive v → ∃! s : E × Bool,
    (if s.2 then head s.1 else tail s.1) = v
  not_two_passive : ∀ e, ¬(passive (tail e) ∧ passive (head e))

/-- Every existing admissible graph supplies a feasible passive-leaf pattern. -/
def GeometryProblem.ofGraph [Fintype V] [Fintype E] (G : MetricGraph V E)
    (D : E → ℝ) (hD : ∀ e, 0 < D e) (κ : V → ℝ)
    (hκ : ∀ v, 0 ≤ κ v) (hanchor : ∃ v, 0 < κ v) : GeometryProblem V E where
  tail := G.tail
  head := G.head
  connected := G.connected
  diffusivity := D
  diffusivity_pos := hD
  passive := G.IsPassiveTip κ
  passive_tip := fun _ hv => hv.2
  not_two_passive := G.no_two_passive_tips κ hκ hanchor

def GeometryProblem.graph (P : GeometryProblem V E) (length : E → ℝ)
    (hpos : ∀ e, 0 < length e) : MetricGraph V E where
  tail := P.tail
  head := P.head
  length := length
  length_pos := hpos
  conductance := fun e _ => P.diffusivity e
  source := fun _ _ => 1
  conductance_continuous := fun _ => continuousOn_const
  source_continuous := fun _ => continuousOn_const
  conductance_pos := fun e _ _ => P.diffusivity_pos e
  source_pos := fun _ _ _ => zero_lt_one
  connected := P.connected

def GeometryProblem.constants (P : GeometryProblem V E) (length : E → ℝ)
    (hpos : ∀ e, 0 < length e) : EdgeConstants (P.graph length hpos) where
  conductance := P.diffusivity
  source := fun _ => 1
  conductance_eq := fun _ _ _ => rfl
  source_eq := fun _ _ _ => rfl

noncomputable def GeometryProblem.marker (P : GeometryProblem V E) (v : V) : ℝ :=
  if P.passive v then 0 else 1

noncomputable def GeometryProblem.reflection (P : GeometryProblem V E) (e : E) : ℝ :=
  if P.passive (P.tail e) ∨ P.passive (P.head e) then 4 else 1

noncomputable def GeometryProblem.scale (P : GeometryProblem V E) (e : E) : ℝ :=
  Real.sqrt (P.diffusivity e / P.reflection e)

noncomputable def GeometryProblem.totalScale [Fintype E] (P : GeometryProblem V E) : ℝ :=
  ∑ e, P.scale e

noncomputable def GeometryProblem.optimalLengths [Fintype E] (P : GeometryProblem V E)
    (L : ℝ) (e : E) : ℝ := L * P.scale e / P.totalScale

noncomputable def GeometryProblem.optimalValue [Fintype E] (P : GeometryProblem V E)
    (L K : ℝ) : ℝ := L / K + L ^ 2 / (8 * P.totalScale ^ 2)

theorem GeometryProblem.marker_passive (P : GeometryProblem V E) (length : E → ℝ)
    (hpos : ∀ e, 0 < length e) (v : V) :
    (P.graph length hpos).IsPassiveTip P.marker v ↔ P.passive v := by
  constructor
  · intro hv
    by_contra hp
    have hz := hv.1
    simp [GeometryProblem.marker, hp] at hz
  · intro hp
    refine ⟨by simp [GeometryProblem.marker, hp], ?_⟩
    exact P.passive_tip v hp

theorem GeometryProblem.graph_no_two_passive (P : GeometryProblem V E) (length : E → ℝ)
    (hpos : ∀ e, 0 < length e) (e : E) :
    ¬((P.graph length hpos).IsPassiveTip P.marker ((P.graph length hpos).tail e) ∧
      (P.graph length hpos).IsPassiveTip P.marker ((P.graph length hpos).head e)) := by
  change ¬((P.graph length hpos).IsPassiveTip P.marker (P.tail e) ∧
    (P.graph length hpos).IsPassiveTip P.marker (P.head e))
  simpa only [P.marker_passive length hpos] using P.not_two_passive e

theorem GeometryProblem.graph_reflection (P : GeometryProblem V E) (length : E → ℝ)
    (hpos : ∀ e, 0 < length e) (e : E) :
    (P.graph length hpos).reflectionFactor P.marker e = P.reflection e := by
  simp only [MetricGraph.reflectionFactor, P.marker_passive length hpos, GeometryProblem.reflection]
  rfl

theorem GeometryProblem.reflection_pos (P : GeometryProblem V E) (e : E) : 0 < P.reflection e := by
  unfold GeometryProblem.reflection
  split_ifs <;> positivity

theorem GeometryProblem.scale_pos (P : GeometryProblem V E) (e : E) : 0 < P.scale e :=
  Real.sqrt_pos.mpr (div_pos (P.diffusivity_pos e) (P.reflection_pos e))

theorem GeometryProblem.scale_sq (P : GeometryProblem V E) (e : E) :
    P.scale e ^ 2 = P.diffusivity e / P.reflection e :=
  Real.sq_sqrt (div_pos (P.diffusivity_pos e) (P.reflection_pos e)).le

theorem GeometryProblem.scale_relation (P : GeometryProblem V E) (e : E) :
    P.reflection e * P.scale e ^ 2 = P.diffusivity e := by
  rw [P.scale_sq e]
  field_simp [ne_of_gt (P.reflection_pos e)]

theorem GeometryProblem.totalScale_pos [Fintype E] [Nonempty E] (P : GeometryProblem V E) :
    0 < P.totalScale := Finset.sum_pos (fun e _ => P.scale_pos e) Finset.univ_nonempty

theorem GeometryProblem.optimalLengths_pos [Fintype E] [Nonempty E] (P : GeometryProblem V E)
    {L : ℝ} (hL : 0 < L) (e : E) : 0 < P.optimalLengths L e :=
  div_pos (mul_pos hL (P.scale_pos e)) P.totalScale_pos

theorem GeometryProblem.optimalLengths_sum [Fintype E] [Nonempty E] (P : GeometryProblem V E)
    (L : ℝ) : ∑ e, P.optimalLengths L e = L := by
  change (∑ e, L * P.scale e / P.totalScale) = L
  rw [← Finset.sum_div, ← Finset.mul_sum]
  exact mul_div_cancel_right₀ L (ne_of_gt P.totalScale_pos)

theorem GeometryProblem.graph_mass (P : GeometryProblem V E) (length : E → ℝ)
    (hpos : ∀ e, 0 < length e) (e : E) : (P.graph length hpos).edgeMass e = length e := by
  simpa only [GeometryProblem.constants, GeometryProblem.graph, one_mul] using
    (P.constants length hpos).mass_eq e

theorem GeometryProblem.graph_resistance (P : GeometryProblem V E) (length : E → ℝ)
    (hpos : ∀ e, 0 < length e) (e : E) :
    (P.graph length hpos).resistance e = length e / P.diffusivity e :=
  (P.constants length hpos).resistance_eq e

theorem GeometryProblem.graph_totalMass [Fintype E] (P : GeometryProblem V E) (length : E → ℝ)
    (hpos : ∀ e, 0 < length e) : (P.graph length hpos).totalMass = ∑ e, length e := by
  change (∑ e, (P.graph length hpos).edgeMass e) = _
  simp only [P.graph_mass length hpos]

noncomputable def GeometryProblem.optimalGraph [Fintype E] [Nonempty E] (P : GeometryProblem V E)
    {L : ℝ} (hL : 0 < L) : MetricGraph V E :=
  P.graph (P.optimalLengths L) (P.optimalLengths_pos hL)

theorem GeometryProblem.optimalGraph_mass [Fintype E] [Nonempty E] (P : GeometryProblem V E)
    {L : ℝ} (hL : 0 < L) (e : E) : (P.optimalGraph hL).edgeMass e = P.optimalLengths L e :=
  P.graph_mass _ _ e

theorem GeometryProblem.optimalGraph_totalMass [Fintype E] [Nonempty E] (P : GeometryProblem V E)
    {L : ℝ} (hL : 0 < L) : (P.optimalGraph hL).totalMass = L :=
  (P.graph_totalMass _ _).trans (P.optimalLengths_sum L)

theorem GeometryProblem.optimal_resistance [Fintype E] [Nonempty E] (P : GeometryProblem V E)
    {L : ℝ} (hL : 0 < L) (e : E) :
    (P.optimalGraph hL).adjustedResistance P.marker e = L / (P.totalScale * P.scale e) := by
  unfold GeometryProblem.optimalGraph
  rw [MetricGraph.adjustedResistance, P.graph_reflection, P.graph_resistance]
  change P.reflection e * (L * P.scale e / P.totalScale / P.diffusivity e) = _
  rw [← P.scale_relation e]
  field_simp [ne_of_gt (P.reflection_pos e), ne_of_gt (P.scale_pos e), ne_of_gt P.totalScale_pos]

theorem GeometryProblem.optimal_capacity [Fintype E] [Nonempty E] (P : GeometryProblem V E)
    {L : ℝ} (hL : 0 < L) :
    (∑ e, 1 / (P.optimalGraph hL).adjustedResistance P.marker e) = P.totalScale ^ 2 / L := by
  calc
    _ = ∑ e, (P.totalScale / L) * P.scale e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [P.optimal_resistance hL e]
      field_simp
    _ = _ := by
      rw [← Finset.mul_sum]
      change P.totalScale / L * P.totalScale = _
      ring

theorem GeometryProblem.optimal_balanced [Fintype E] [Nonempty E] (P : GeometryProblem V E)
    {L : ℝ} (hL : 0 < L) : (P.optimalGraph hL).HasBalancedMasses P.marker := by
  intro e
  rw [P.optimal_resistance hL e, P.optimalGraph_mass hL e,
    P.optimalGraph_totalMass hL, P.optimal_capacity hL]
  unfold GeometryProblem.optimalLengths
  field_simp [ne_of_gt hL, ne_of_gt (P.scale_pos e), ne_of_gt P.totalScale_pos]

end TimeTraps.Graph
