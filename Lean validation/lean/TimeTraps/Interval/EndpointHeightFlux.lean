module

public import TimeTraps.Interval.EndpointHeightCDF

@[expose] public section

/-! The actual endpoint flux and transformed state derivative, derived
from the full weak equation. Exact integration crosses all interior traps;
only interior derivatives and continuous endpoint extension are used. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators Classical

variable {A : EndpointArchitecture} {K : ℝ}

theorem EndpointReactions.initial_gap_flux (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) {U : Fin (A.interiorCount + 2) → ℝ}
    {u j : Fin (A.interiorCount + 1) → ℝ → ℝ} (h : GraphEquation D.graph R.nodal U u j)
    (e : Fin (A.interiorCount + 1)) :
    j e 0 = R.leftStrength * U 0 + absorptionPrefix (fun i => R.interiorStrength i * U (trapNode i)) e -
      D.source.mass * D.source.coordinate (D.node e.castSucc) := by
  induction e using Fin.induction with
  | zero =>
    simpa only [absorptionPrefix_zero, Fin.castSucc_zero, D.node_first,
      D.source.coordinate_left, mul_zero, sub_zero, add_zero] using (R.endpoint_flux D h).1
  | succ i ih =>
    have hf := (h.edge_equation i.castSucc).flux_formula (D.graph.source_continuous i.castSucc)
      (show D.gapLength i.castSucc ∈ Icc 0 (D.graph.length i.castSucc) from
        ⟨(D.gapLength_pos i.castSucc).le, le_rfl⟩)
    rw [D.gap_source_mass, ih] at hf
    have hj := R.interior_flux_jump D h i
    rw [absorptionPrefix_succ]
    change j i.succ 0 = R.leftStrength * U 0 +
      (absorptionPrefix (fun k => R.interiorStrength k * U (trapNode k)) i.castSucc +
        R.interiorStrength i * U (trapNode i)) -
      D.source.mass * D.source.coordinate (D.node i.castSucc.succ)
    linarith

theorem EndpointReactions.gap_flux (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) {U : Fin (A.interiorCount + 2) → ℝ}
    {u j : Fin (A.interiorCount + 1) → ℝ → ℝ} (h : GraphEquation D.graph R.nodal U u j)
    (e : Fin (A.interiorCount + 1)) {x : ℝ} (hx : x ∈ Icc 0 (D.gapLength e)) :
    j e x = R.leftStrength * U 0 + absorptionPrefix (fun i => R.interiorStrength i * U (trapNode i)) e -
      D.source.mass * D.source.coordinate (D.node e.castSucc + x) := by
  have hf := (h.edge_equation e).flux_formula (D.graph.source_continuous e) hx
  rw [R.initial_gap_flux D h e, D.gap_source_primitive e hx] at hf
  linarith

theorem EndpointReactions.active_absorption_flux (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) {w : ℝ → ℝ} {j : Fin (A.interiorCount + 1) → ℝ → ℝ}
    (h : GraphEquation D.graph R.nodal (fun v => w (D.node v)) (D.gapRestriction w) j)
    (e : Fin (A.interiorCount + 1)) {x : ℝ} (hx : x ∈ Ioo 0 (D.gapLength e)) :
    j e x = D.source.mass *
      (R.activeCDF D w (D.source.coordinate (D.node e.castSucc + x)) -
        D.source.coordinate (D.node e.castSucc + x)) := by
  have hpoint : D.node e.castSucc + x ∈ Ioo D.source.left D.source.right := by
    have hl := (D.node_mem e.castSucc).1
    have hr := (D.node_mem e.succ).2
    have hxr := hx.2
    unfold OrderedMedium.gapLength at hxr
    constructor <;> linarith [hx.1]
  have hz := D.source.coordinate_interior hpoint
  rw [R.activeCDF_interior D w ⟨hz.1.le, hz.2⟩, D.absorptionCDF_gap _ e hx,
    R.gap_flux D h e (Ioo_subset_Icc_self hx), D.node_first, absorptionPrefix_div]
  change R.leftStrength * w D.source.left +
      absorptionPrefix (fun i => R.interiorStrength i * w (D.site i)) e - _ = _
  field_simp [ne_of_gt D.source.mass_pos]

noncomputable def EndpointReactions.activeSlope (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) (w : ℝ → ℝ) (z : ℝ) : ℝ :=
  D.source.weight D.conductance z * (R.activeCDF D w z - z)

theorem EndpointReactions.activeSlope_integrable (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) (w : ℝ → ℝ) (a b : ℝ) :
    IntervalIntegrable (R.activeSlope D w) volume a b := by
  have hw := D.source.weight_continuous D.conductance_continuous D.conductance_pos
  exact ((R.activeCDF_integrable D w a b).sub
    (continuous_id.intervalIntegrable a b)).continuousOn_mul hw.continuousOn

theorem EndpointWeakEquation.transformed_derivative {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) (hsite : ∀ i, D.sourceSite i ≠ z) :
    HasDerivAt (D.source.transformed w) (R.activeSlope D w z) z := by
  obtain ⟨j, hj⟩ := hw.to_strong
  have hn : ∀ i, D.site i ≠ D.source.inverse z := by
    intro i he
    apply hsite i
    change D.source.coordinate (D.site i) = z
    rw [he, D.source.coordinate_inverse (Ioo_subset_Icc_self hz)]
  obtain ⟨e, he⟩ := D.gap_cover_open (D.source.inverse_interior hz) hn
  have ht : D.source.inverse z - D.node e.castSucc ∈ Ioo 0 (D.gapLength e) :=
    ⟨sub_pos.mpr he.1, sub_lt_sub_right he.2 _⟩
  have hd := ((hj.edge_equation e).state_derivative _ ht).comp (D.source.inverse z)
    ((hasDerivAt_id (D.source.inverse z)).sub_const (D.node e.castSucc))
  have hdu : HasDerivAt w
      (j e (D.source.inverse z - D.node e.castSucc) / D.conductance (D.source.inverse z))
      (D.source.inverse z) := by
    simpa only [OrderedMedium.gapRestriction, OrderedMedium.graph, Function.comp_def,
      add_sub_cancel, id_eq, mul_one] using hd
  have hf := R.active_absorption_flux D hj e ht
  rw [add_sub_cancel, D.source.coordinate_inverse (Ioo_subset_Icc_self hz)] at hf
  have hdt := D.source.transformed_derivative hz hdu
  rw [hf] at hdt
  convert hdt using 1
  unfold EndpointReactions.activeSlope SourceInterval.weight
  field_simp [ne_of_gt (D.conductance_pos _ (D.source.inverse_mem z)),
    ne_of_gt (D.source.positive _ (D.source.inverse_mem z))]

theorem EndpointWeakEquation.transformed_integral {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    (∫ z in a..b, R.activeSlope D w z) = D.source.transformed w b - D.source.transformed w a := by
  have hc : Continuous (D.source.transformed w) := D.source.transformed_continuous
    (by simpa only [uIcc_of_le D.source.increasing.le] using hw.energy.continuousOn)
  apply integral_eq_of_hasDerivAt_off_countable_of_le _ _ hab
    (Set.finite_range D.sourceSite).countable hc.continuousOn
  · intro z hz
    apply hw.transformed_derivative ⟨ha.trans_lt hz.1.1, hz.1.2.trans_le hb⟩
    intro i hi
    exact hz.2 ⟨i, hi⟩
  · exact R.activeSlope_integrable D w a b

end TimeTraps.Interval
