module

public import TimeTraps.Interval.EndpointActiveNodes
public import TimeTraps.Interval.EndpointPartitionRoot
public import TimeTraps.Interval.AbsorptionCDF

@[expose] public section

/-! Positive absorption shares of the actual endpoint weak state, indexed
by active sites only. Their strict cumulative partition retains the fixed
architecture and the physical left-to-right site order. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis
open scoped BigOperators

def EndpointArchitecture.physicalSite (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) (i : Fin A.count) : ℝ := D.node (A.activeNode i)

noncomputable def EndpointArchitecture.sourceSite (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) (i : Fin A.count) : ℝ :=
  D.source.coordinate (A.physicalSite D i)

theorem EndpointArchitecture.physicalSite_mem (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) (i : Fin A.count) :
    A.physicalSite D i ∈ Icc D.source.left D.source.right := D.node_mem _

theorem EndpointArchitecture.sourceSite_mem (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) (i : Fin A.count) :
    A.sourceSite D i ∈ Icc (0 : ℝ) 1 := D.source.coordinate_mem (A.physicalSite_mem D i)

theorem EndpointArchitecture.sourceSite_strictMono (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) : StrictMono (A.sourceSite D) := by
  intro i j hij
  exact D.source.coordinate_strictMono (A.physicalSite_mem D i) (A.physicalSite_mem D j)
    (D.node_strictMono (A.activeNode_strictMono hij))

theorem EndpointArchitecture.sourceSite_left (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) (i : Fin A.count) (hi : A.kind i = .leftEndpoint) :
    A.sourceSite D i = 0 := by
  simp only [sourceSite, physicalSite, A.activeNode_left i hi, D.node_first, D.source.coordinate_left]

theorem EndpointArchitecture.sourceSite_right (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) (i : Fin A.count) (hi : A.kind i = .rightEndpoint) :
    A.sourceSite D i = 1 := by
  simp only [sourceSite, physicalSite, A.activeNode_right i hi, D.node_last, D.source.coordinate_right]

theorem EndpointArchitecture.sourceSite_interior (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) (i : Fin A.interiorCount) :
    A.sourceSite D (A.interiorCell i) = D.sourceSite i := by
  simp only [sourceSite, physicalSite, A.activeNode_interior, OrderedMedium.sourceSite, OrderedMedium.site]

variable {A : EndpointArchitecture} {K : ℝ}

noncomputable def EndpointReactions.activeShare (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) (w : ℝ → ℝ) (i : Fin A.count) : ℝ :=
  R.activeStrength i * w (A.physicalSite D i) / D.source.mass

theorem EndpointWeakEquation.activeShare_pos {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) (i : Fin A.count) :
    0 < R.activeShare D w i :=
  div_pos (mul_pos (R.activeStrength_pos i) (hw.positive _ (A.physicalSite_mem D i))) D.source.mass_pos

theorem EndpointWeakEquation.activeShare_sum {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) :
    (∑ i, R.activeShare D w i) = 1 := by
  unfold EndpointReactions.activeShare EndpointArchitecture.physicalSite
  rw [← Finset.sum_div, R.active_pairing (fun v => w (D.node v)), hw.conservation,
    div_self (ne_of_gt D.source.mass_pos)]

noncomputable def EndpointWeakEquation.partition {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) : StrictPartition A.count where
  point := absorptionPrefix (R.activeShare D w)
  strictMono := absorptionPrefix_strictMono _ hw.activeShare_pos
  first := absorptionPrefix_zero _
  last := by rw [absorptionPrefix_last, hw.activeShare_sum]

theorem EndpointWeakEquation.partition_point {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) (i : Fin (A.count + 1)) :
    hw.partition.point i = absorptionPrefix (R.activeShare D w) i := rfl

theorem EndpointWeakEquation.partition_width {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) (i : Fin A.count) :
    hw.partition.closed.width i = R.activeShare D w i := by
  change absorptionPrefix _ i.succ - absorptionPrefix _ i.castSucc = _
  rw [absorptionPrefix_succ, add_sub_cancel_left]

theorem EndpointArchitecture.transformed_activeSite (A : EndpointArchitecture)
    (D : OrderedMedium A.interiorCount) (w : ℝ → ℝ) (i : Fin A.count) :
    D.source.transformed w (A.sourceSite D i) = w (A.physicalSite D i) :=
  D.source.transformed_coordinate w (A.physicalSite_mem D i)

end TimeTraps.Interval
