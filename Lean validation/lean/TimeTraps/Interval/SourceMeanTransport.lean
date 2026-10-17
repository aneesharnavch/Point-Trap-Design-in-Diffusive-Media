module

public import TimeTraps.Interval.WeightedCDFPosition
public import TimeTraps.Interval.PhysicalDesign

@[expose] public section

/-!
Local energy transport to normalized source coordinates. The source density
and conductance are positive and continuous; neither coefficient needs a
derivative. The physical objective is defined before the transport identity.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

variable {n : ℕ} {A : IntervalMedium} {K : ℝ}

noncomputable def IntervalDesign.sourceMeanCost (E : IntervalDesign A n K) : ℝ :=
  (∫ x in A.source.left..A.source.right, A.source.density x * E.state x) / A.source.mass

theorem IntervalDesign.source_eq (E : IntervalDesign A n K) : E.geometry.source = A.source :=
  congrArg IntervalMedium.source E.medium_eq

theorem IntervalDesign.conductance_eq (E : IntervalDesign A n K) :
    E.geometry.conductance = A.conductance := congrArg IntervalMedium.conductance E.medium_eq

theorem IntervalDesign.sourceSite_eq (E : IntervalDesign A n K) (i : Fin n) :
    E.geometry.sourceSite i = A.source.coordinate (E.geometry.site i) := by
  rw [OrderedMedium.sourceSite, E.source_eq]

theorem IntervalDesign.sourceSite_mem (E : IntervalDesign A n K) (i : Fin n) :
    E.geometry.sourceSite i ∈ Icc (0 : ℝ) 1 :=
  E.geometry.source.coordinate_mem (Ioo_subset_Icc_self (E.geometry.site_interior i))

theorem IntervalDesign.source_share (E : IntervalDesign A n K) (i : Fin n) :
    E.partition.width i = E.strength i * E.state (E.geometry.site i) / A.source.mass := by
  simpa only [StrictPartition.closed_width, OrderedMedium.stateShare, E.source_mass]
    using E.partition_width i

theorem IntervalDesign.source_cdfNode (E : IntervalDesign A n K) (v : Fin (n + 2)) :
    cdfNode E.geometry.sourceSite v = A.source.coordinate (E.geometry.node v) := by
  refine Fin.cases ?_ (fun w => ?_) v
  · rw [cdfNode_first, E.geometry.node_first, E.source_eq, A.source.coordinate_left]
  · refine Fin.lastCases ?_ (fun i => ?_) w
    · change cdfNode E.geometry.sourceSite (Fin.last (n + 1)) =
        A.source.coordinate (E.geometry.node (Fin.last (n + 1)))
      rw [cdfNode_last, E.geometry.node_last, E.source_eq, A.source.coordinate_right]
    · rw [cdfNode_site]
      exact E.sourceSite_eq i

theorem source_mean_gap_transport (P : SourceInterval) {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc P.left P.right))
    (hapos : ∀ x ∈ Icc P.left P.right, 0 < a x) {l r : ℝ}
    (hl : l ∈ Icc P.left P.right) (hr : r ∈ Icc P.left P.right) (hlr : l ≤ r) (q : ℝ) :
    (∫ x in l..r, (P.mass / a x) * (q - P.coordinate x) ^ 2) =
      ∫ z in P.coordinate l..P.coordinate r, P.weight a z * (q - z) ^ 2 := by
  have hsub : uIcc l r ⊆ Icc P.left P.right := by
    rw [uIcc_of_le hlr]
    exact Icc_subset_Icc hl.1 hr.2
  have hg : Continuous (fun z => P.weight a z * (q - z) ^ 2) :=
    (P.weight_continuous ha hapos).mul ((continuous_const.sub continuous_id).pow 2)
  have hi := intervalIntegral.integral_comp_mul_deriv''
    (a := l) (b := r) (f := P.coordinate) (f' := fun x => P.density x / P.mass)
    (g := fun z => P.weight a z * (q - z) ^ 2)
    (P.coordinate_continuous.mono hsub)
    (by
      intro x hx
      apply (P.coordinate_derivative ?_).hasDerivWithinAt
      simp only [min_eq_left hlr, max_eq_right hlr] at hx
      exact ⟨hl.1.trans_lt hx.1, hx.2.trans_le hr.2⟩)
    ((P.continuous.div_const P.mass).mono hsub) hg.continuousOn
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro x hx
  have hxp := hsub hx
  dsimp only [Function.comp_apply, SourceInterval.weight]
  rw [P.inverse_coordinate hxp]
  field_simp [ne_of_gt P.mass_pos, ne_of_gt (hapos x hxp), ne_of_gt (P.positive x hxp)]

theorem IntervalDesign.sourceMeanCost_transformed (E : IntervalDesign A n K) :
    E.sourceMeanCost = ∫ z in (0 : ℝ)..1, A.source.transformed E.state z := by
  have hc : ContinuousOn E.state (Icc A.source.left A.source.right) := by
    rw [← E.source_eq]
    exact E.equation.energy.absolutelyContinuous.continuousOn.mono Icc_subset_uIcc
  rw [IntervalDesign.sourceMeanCost, A.source.source_integral hc]
  field_simp [ne_of_gt A.source.mass_pos]

end TimeTraps.Interval
