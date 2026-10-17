module

public import TimeTraps.Interval.EndpointReconstructionProfile
public import TimeTraps.Interval.PartitionState

@[expose] public section

/-! Physical pullback of the mixed profile, with exact state and flux
derivatives on open gaps and continuous flux traces at their ends. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

theorem EndpointArchitecture.sourceSite_gap_iff (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) (e : Fin (A.interiorCount + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (D.gapLength e)) (i : Fin A.count) :
    A.sourceSite D i ≤ D.source.coordinate (D.node e.castSucc + x) ↔
      i.val < (A.gapBoundary e).val := by
  rw [show A.sourceSite D i = D.source.coordinate (D.node (A.activeNode i)) from rfl,
    D.source.coordinate_strictMono.le_iff_le (D.node_mem _) (D.gap_point_mem e (Ioo_subset_Icc_self hx))]
  have hnode : D.node (A.activeNode i) ≤ D.node e.castSucc + x ↔
      (A.activeNode i).val ≤ e.val := by
    constructor
    · intro h
      have hp : D.node e.castSucc + x < D.node e.succ := by
        have hh := hx.2
        unfold OrderedMedium.gapLength at hh
        linarith
      have hlt := D.node_strictMono.lt_iff_lt.mp (h.trans_lt hp)
      change (A.activeNode i).val < e.val + 1 at hlt
      omega
    · intro h
      have hn : A.activeNode i ≤ e.castSucc := h
      exact (D.node_strictMono.monotone hn).trans (le_add_of_nonneg_right hx.1.le)
  rw [hnode]
  cases hl : A.leftReactive <;> simp only [activeNode, gapBoundary, hl,
    Bool.false_eq_true, if_false, if_true, Bool.toNat_false, Bool.toNat_true] <;> omega

theorem EndpointArchitecture.sourceSite_ne_gap (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) (e : Fin (A.interiorCount + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (D.gapLength e)) (i : Fin A.count) :
    A.sourceSite D i ≠ D.source.coordinate (D.node e.castSucc + x) := by
  intro h
  have he : D.node (A.activeNode i) = D.node e.castSucc + x :=
    D.source.coordinate_strictMono.injOn (D.node_mem _) (D.gap_point_mem e (Ioo_subset_Icc_self hx)) h
  have hp := (A.sourceSite_gap_iff D e hx i).mp h.le
  have hn : A.activeNode i ≤ e.castSucc := by
    change (A.activeNode i).val ≤ e.val
    cases hl : A.leftReactive <;> simp only [gapBoundary, hl, Bool.toNat_false,
      Bool.toNat_true] at hp <;> simp only [activeNode, hl, Bool.false_eq_true, if_false, if_true] <;> omega
  have hle := D.node_strictMono.monotone hn
  rw [he] at hle
  linarith [hx.1]

theorem IntervalMedium.endpointPartitionCDF_gap (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (e : Fin (A.interiorCount + 1))
    {x : ℝ} (hx : x ∈ Ioo 0 ((B.endpointPartitionGeometry A Q).gapLength e)) :
    A.reconstructionCDF Q B.cellWeight
      (B.source.coordinate ((B.endpointPartitionGeometry A Q).node e.castSucc + x)) =
      Q.point (A.gapBoundary e) := by
  rw [← Q.prefix_width]
  unfold EndpointArchitecture.reconstructionCDF absorptionPrefix
  apply Finset.sum_congr rfl
  intro i _
  rw [← B.endpointPartitionGeometry_sourceSite]
  have hg : A.sourceSite (B.endpointPartitionGeometry A Q) i ≤
      B.source.coordinate ((B.endpointPartitionGeometry A Q).node e.castSucc + x) ↔
        i.val < (A.gapBoundary e).val := A.sourceSite_gap_iff (B.endpointPartitionGeometry A Q) e hx i
  simp only [hg]

noncomputable def IntervalMedium.endpointPartitionState (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M x : ℝ) : ℝ :=
  B.endpointPartitionProfile A Q M (B.source.coordinate x)

noncomputable def IntervalMedium.endpointPartitionFlux (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count)
    (e : Fin (A.interiorCount + 1)) (x : ℝ) : ℝ :=
  B.source.mass * (Q.point (A.gapBoundary e) -
    B.source.coordinate ((B.endpointPartitionGeometry A Q).node e.castSucc + x))

theorem IntervalMedium.endpointPartitionState_continuous (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) :
    ContinuousOn (B.endpointPartitionState A Q M) (Icc B.source.left B.source.right) :=
  (B.endpointPartitionProfile_continuous A Q M).comp_continuousOn B.source.coordinate_continuous

theorem IntervalMedium.endpointPartitionState_boundary (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ)
    (e : Fin (A.interiorCount + 1)) :
    B.endpointPartitionState A Q M (B.source.inverse (Q.point (A.gapBoundary e))) = M := by
  unfold endpointPartitionState
  rw [B.source.coordinate_inverse (Q.point_mem _), B.endpointPartitionProfile_boundary]

theorem IntervalMedium.endpointPartitionState_site (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) (i : Fin A.count) :
    B.endpointPartitionState A Q M (A.physicalSite (B.endpointPartitionGeometry A Q) i) =
      M - A.barrier Q.closed B.cellWeight i := by
  change B.endpointPartitionProfile A Q M (A.sourceSite (B.endpointPartitionGeometry A Q) i) = _
  rw [B.endpointPartitionGeometry_sourceSite, B.endpointPartitionProfile_site]

theorem IntervalMedium.endpointPartitionState_le (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) {x : ℝ}
    (hx : x ∈ Icc B.source.left B.source.right) : B.endpointPartitionState A Q M x ≤ M :=
  B.endpointPartitionProfile_le A Q M (B.source.coordinate_mem hx)

theorem IntervalMedium.endpointPartitionState_derivative (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ)
    (e : Fin (A.interiorCount + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 ((B.endpointPartitionGeometry A Q).gapLength e)) :
    HasDerivAt (B.endpointPartitionState A Q M)
      (B.endpointPartitionFlux A Q e x / B.conductance ((B.endpointPartitionGeometry A Q).node e.castSucc + x))
      ((B.endpointPartitionGeometry A Q).node e.castSucc + x) := by
  let D := B.endpointPartitionGeometry A Q
  let y := D.node e.castSucc + x
  have hy : y ∈ Ioo B.source.left B.source.right := D.gap_point_interior e hx
  have hn : ∀ i, A.reconstructionSite Q B.cellWeight i ≠ B.source.coordinate y := by
    intro i
    rw [← B.endpointPartitionGeometry_sourceSite]
    exact A.sourceSite_ne_gap D e hx i
  have hd := (B.endpointPartitionProfile_derivative A Q M hn).comp y (B.source.coordinate_derivative hy)
  have hcdf : A.reconstructionCDF Q B.cellWeight (B.source.coordinate y) = Q.point (A.gapBoundary e) :=
    B.endpointPartitionCDF_gap A Q e hx
  have he : B.endpointPartitionSlope A Q (B.source.coordinate y) * (B.source.density y / B.source.mass) =
      B.endpointPartitionFlux A Q e x / B.conductance y := by
    unfold endpointPartitionSlope
    rw [hcdf]
    unfold SourceInterval.weight
    rw [B.source.inverse_coordinate (Ioo_subset_Icc_self hy)]
    change (B.source.mass ^ 2 / (B.conductance y * B.source.density y)) *
      (Q.point (A.gapBoundary e) - B.source.coordinate y) * (B.source.density y / B.source.mass) =
        B.source.mass * (Q.point (A.gapBoundary e) - B.source.coordinate y) / B.conductance y
    field_simp [ne_of_gt B.source.mass_pos,
      ne_of_gt (B.source.positive y (Ioo_subset_Icc_self hy)),
      ne_of_gt (B.conductance_pos y (Ioo_subset_Icc_self hy))]
  rw [he] at hd
  exact hd

theorem IntervalMedium.endpointPartitionFlux_continuous (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (e : Fin (A.interiorCount + 1)) :
    ContinuousOn (B.endpointPartitionFlux A Q e) (Icc 0 ((B.endpointPartitionGeometry A Q).gapLength e)) := by
  have hc := B.source.coordinate_continuous.comp
    (continuous_const.add continuous_id).continuousOn
    (fun _ hx => (B.endpointPartitionGeometry A Q).gap_point_mem e hx)
  exact continuousOn_const.mul (continuousOn_const.sub hc)

theorem IntervalMedium.endpointPartitionFlux_derivative (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (e : Fin (A.interiorCount + 1))
    {x : ℝ} (hx : x ∈ Ioo 0 ((B.endpointPartitionGeometry A Q).gapLength e)) :
    HasDerivAt (B.endpointPartitionFlux A Q e)
      (-B.source.density ((B.endpointPartitionGeometry A Q).node e.castSucc + x)) x := by
  have hd := (B.source.coordinate_derivative ((B.endpointPartitionGeometry A Q).gap_point_interior e hx)).comp x
    ((hasDerivAt_id x).const_add ((B.endpointPartitionGeometry A Q).node e.castSucc))
  have hj := (hd.const_sub (Q.point (A.gapBoundary e))).const_mul B.source.mass
  have he : B.source.mass * -(B.source.density ((B.endpointPartitionGeometry A Q).node e.castSucc + x) /
      B.source.mass * 1) = -B.source.density ((B.endpointPartitionGeometry A Q).node e.castSucc + x) := by
    field_simp [ne_of_gt B.source.mass_pos]
  rw [he] at hj
  exact hj

theorem IntervalMedium.endpointPartition_edge_equation (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ)
    (e : Fin (A.interiorCount + 1)) :
    EdgeEquation ((B.endpointPartitionGeometry A Q).graph.conductance e)
      ((B.endpointPartitionGeometry A Q).graph.source e) 0 ((B.endpointPartitionGeometry A Q).graph.length e)
      ((B.endpointPartitionGeometry A Q).gapRestriction (B.endpointPartitionState A Q M) e)
      (B.endpointPartitionFlux A Q e) := by
  refine ⟨?_, B.endpointPartitionFlux_continuous A Q e, ?_, fun x hx => B.endpointPartitionFlux_derivative A Q e hx⟩
  · exact (B.endpointPartitionState_continuous A Q M).comp (continuous_const.add continuous_id).continuousOn
      (fun _ hx => (B.endpointPartitionGeometry A Q).gap_point_mem e hx)
  · intro x hx
    have hd := (B.endpointPartitionState_derivative A Q M e hx).comp x
      ((hasDerivAt_id x).const_add ((B.endpointPartitionGeometry A Q).node e.castSucc))
    change HasDerivAt (fun t => B.endpointPartitionState A Q M ((B.endpointPartitionGeometry A Q).node e.castSucc + t))
      (B.endpointPartitionFlux A Q e x / B.conductance ((B.endpointPartitionGeometry A Q).node e.castSucc + x)) x
    simpa only [mul_one, Function.comp_def] using hd

end TimeTraps.Interval
