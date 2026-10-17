module

public import TimeTraps.Interval.PartitionProfile

@[expose] public section

/-!
Pull back the constructed profile to the physical medium and verify its
actual state and flux derivatives on every trap-free gap.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Graph
open scoped BigOperators

variable {n : ℕ}

theorem OrderedMedium.gap_point_interior (D : OrderedMedium n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (D.gapLength e)) :
    D.node e.castSucc + x ∈ Ioo D.source.left D.source.right := by
  have hl := (D.node_mem e.castSucc).1
  have hr := (D.node_mem e.succ).2
  unfold OrderedMedium.gapLength at hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem OrderedMedium.sourceSite_ne_gap (D : OrderedMedium n) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 (D.gapLength e)) (i : Fin n) :
    D.sourceSite i ≠ D.source.coordinate (D.node e.castSucc + x) := by
  intro h
  have he : D.site i = D.node e.castSucc + x :=
    D.source.coordinate_strictMono.injOn (Ioo_subset_Icc_self (D.site_interior i))
      (D.gap_point_mem e (Ioo_subset_Icc_self hx)) h
  have hi := (D.site_le_gap_point_iff e hx i).mp he.le
  have hn : trapNode i ≤ e.castSucc := by change i.val + 1 ≤ e.val; omega
  have hle := D.node_strictMono.monotone hn
  change D.site i ≤ D.node e.castSucc at hle
  rw [he] at hle
  linarith [hx.1]

noncomputable def IntervalMedium.partitionState (A : IntervalMedium) (Q : StrictPartition n)
    (M x : ℝ) : ℝ := A.partitionProfile Q M (A.source.coordinate x)

noncomputable def IntervalMedium.partitionFlux (A : IntervalMedium) (Q : StrictPartition n)
    (e : Fin (n + 1)) (x : ℝ) : ℝ :=
  A.source.mass * (Q.point e - A.source.coordinate ((A.partitionDesign Q).node e.castSucc + x))

theorem IntervalMedium.partitionState_continuous (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) : ContinuousOn (A.partitionState Q M) (Icc A.source.left A.source.right) :=
  (A.partitionProfile_continuous Q M).comp_continuousOn A.source.coordinate_continuous

theorem IntervalMedium.partitionState_source (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    A.partitionState Q M (A.source.inverse z) = A.partitionProfile Q M z := by
  unfold IntervalMedium.partitionState
  rw [A.source.coordinate_inverse hz]

theorem IntervalMedium.partitionState_boundary (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) (e : Fin (n + 1)) : A.partitionState Q M (A.source.inverse (Q.point e)) = M := by
  rw [A.partitionState_source Q M (Q.point_mem e), A.partitionProfile_boundary]

theorem IntervalMedium.partitionState_trap (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) (i : Fin n) :
    A.partitionState Q M ((A.partitionDesign Q).site i) = M - Q.barrier A.cellWeight i := by
  change A.partitionProfile Q M ((A.partitionDesign Q).sourceSite i) = _
  rw [A.partitionDesign_sourceSite, A.partitionProfile_trap]

theorem IntervalMedium.partitionState_left (A : IntervalMedium) (Q : StrictPartition n) (M : ℝ) :
    A.partitionState Q M A.source.left = M := by
  unfold IntervalMedium.partitionState
  rw [A.source.coordinate_left, A.partitionProfile_zero]

theorem IntervalMedium.partitionState_le (A : IntervalMedium) (Q : StrictPartition n) (M : ℝ)
    {x : ℝ} (hx : x ∈ Icc A.source.left A.source.right) : A.partitionState Q M x ≤ M :=
  A.partitionProfile_le Q M (A.source.coordinate_mem hx)

theorem IntervalMedium.partitionState_derivative (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) (e : Fin (n + 1)) {x : ℝ}
    (hx : x ∈ Ioo 0 ((A.partitionDesign Q).gapLength e)) :
    HasDerivAt (A.partitionState Q M)
      (A.partitionFlux Q e x / A.conductance ((A.partitionDesign Q).node e.castSucc + x))
      ((A.partitionDesign Q).node e.castSucc + x) := by
  let D := A.partitionDesign Q
  let y := D.node e.castSucc + x
  have hy : y ∈ Ioo A.source.left A.source.right := D.gap_point_interior e hx
  have hn : ∀ i, Q.center A.cellWeight i ≠ A.source.coordinate y := by
    intro i
    rw [← A.partitionDesign_sourceSite Q i]
    exact D.sourceSite_ne_gap e hx i
  have hd := (A.partitionProfile_derivative Q M hn).comp y (A.source.coordinate_derivative hy)
  have hcdf : (A.partitionDesign Q).absorptionCDF Q.width (A.source.coordinate y) = Q.point e := by
    change D.absorptionCDF Q.width (D.source.coordinate (D.node e.castSucc + x)) = Q.point e
    rw [D.absorptionCDF_gap Q.width e hx, Q.prefix_width]
  have he : A.partitionSlope Q (A.source.coordinate y) * (A.source.density y / A.source.mass) =
      A.partitionFlux Q e x / A.conductance y := by
    unfold IntervalMedium.partitionSlope
    rw [hcdf]
    unfold SourceInterval.weight
    rw [A.source.inverse_coordinate (Ioo_subset_Icc_self hy)]
    change (A.source.mass ^ 2 / (A.conductance y * A.source.density y)) *
      (Q.point e - A.source.coordinate y) * (A.source.density y / A.source.mass) =
        A.source.mass * (Q.point e - A.source.coordinate y) / A.conductance y
    field_simp [ne_of_gt A.source.mass_pos,
      ne_of_gt (A.source.positive y (Ioo_subset_Icc_self hy)),
      ne_of_gt (A.conductance_pos y (Ioo_subset_Icc_self hy))]
  rw [he] at hd
  exact hd

theorem IntervalMedium.partitionFlux_continuous (A : IntervalMedium) (Q : StrictPartition n)
    (e : Fin (n + 1)) :
    ContinuousOn (A.partitionFlux Q e) (Icc 0 ((A.partitionDesign Q).gapLength e)) := by
  have hc := A.source.coordinate_continuous.comp
    (continuous_const.add continuous_id).continuousOn
    (fun _ hx => (A.partitionDesign Q).gap_point_mem e hx)
  exact continuousOn_const.mul (continuousOn_const.sub hc)

theorem IntervalMedium.partitionFlux_derivative (A : IntervalMedium) (Q : StrictPartition n)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo 0 ((A.partitionDesign Q).gapLength e)) :
    HasDerivAt (A.partitionFlux Q e)
      (-A.source.density ((A.partitionDesign Q).node e.castSucc + x)) x := by
  have hd := (A.source.coordinate_derivative ((A.partitionDesign Q).gap_point_interior e hx)).comp x
    ((hasDerivAt_id x).const_add ((A.partitionDesign Q).node e.castSucc))
  have hj := (hd.const_sub (Q.point e)).const_mul A.source.mass
  have he : A.source.mass * -(A.source.density ((A.partitionDesign Q).node e.castSucc + x) /
      A.source.mass * 1) = -A.source.density ((A.partitionDesign Q).node e.castSucc + x) := by
    field_simp [ne_of_gt A.source.mass_pos]
  rw [he] at hj
  exact hj

theorem IntervalMedium.partition_edge_equation (A : IntervalMedium) (Q : StrictPartition n)
    (M : ℝ) (e : Fin (n + 1)) :
    EdgeEquation ((A.partitionDesign Q).graph.conductance e) ((A.partitionDesign Q).graph.source e)
      0 ((A.partitionDesign Q).graph.length e)
      ((A.partitionDesign Q).gapRestriction (A.partitionState Q M) e) (A.partitionFlux Q e) := by
  refine ⟨?_, A.partitionFlux_continuous Q e, ?_, fun x hx => A.partitionFlux_derivative Q e hx⟩
  · exact (A.partitionState_continuous Q M).comp (continuous_const.add continuous_id).continuousOn
      (fun _ hx => (A.partitionDesign Q).gap_point_mem e hx)
  · intro x hx
    have hd := (A.partitionState_derivative Q M e hx).comp x
      ((hasDerivAt_id x).const_add ((A.partitionDesign Q).node e.castSucc))
    change HasDerivAt (fun t => A.partitionState Q M ((A.partitionDesign Q).node e.castSucc + t))
      (A.partitionFlux Q e x / A.conductance ((A.partitionDesign Q).node e.castSucc + x)) x
    simpa only [mul_one, Function.comp_def] using hd

end TimeTraps.Interval
