module

public import TimeTraps.Interval.SourceMeanDeficit
public import TimeTraps.Interval.VariableMeanAttainment

@[expose] public section

/-! Effective unit conductance and the physical inverse-source geometry.
The local coordinate maps preserve both endpoints and every open gap. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis

variable {n : ℕ}

noncomputable def sourceMeanConductance (A : IntervalMedium) (z : ℝ) : ℝ :=
  1 / A.cellWeight.value z

theorem sourceMeanConductance_continuous (A : IntervalMedium) :
    ContinuousOn (sourceMeanConductance A) (Icc (0 : ℝ) 1) :=
  continuousOn_const.div A.cellWeight.continuous
    (fun z hz => ne_of_gt (A.cellWeight.positive z hz))

theorem sourceMeanConductance_pos (A : IntervalMedium) (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
    0 < sourceMeanConductance A z := one_div_pos.mpr (A.cellWeight.positive z hz)

theorem sourceMeanConductance_weight (A : IntervalMedium) :
    variableMeanWeight (sourceMeanConductance A) (sourceMeanConductance_continuous A)
      (sourceMeanConductance_pos A) = A.cellWeight := by
  have hv : (variableMeanWeight (sourceMeanConductance A) (sourceMeanConductance_continuous A)
      (sourceMeanConductance_pos A)).value = A.cellWeight.value := by
    funext z
    change 1 / (1 / A.cellWeight.value z) = A.cellWeight.value z
    simp only [one_div_one_div]
  have hext : ∀ W V : CellWeight, W.value = V.value → W = V := by
    intro W V h
    cases W
    cases V
    cases h
    rfl
  exact hext _ _ hv

theorem sourceMeanConductance_coordinate (A : IntervalMedium) {x : ℝ}
    (hx : x ∈ Icc A.source.left A.source.right) :
    sourceMeanConductance A (A.source.coordinate x) =
      A.conductance x * A.source.density x / A.source.mass ^ 2 := by
  change 1 / (A.source.mass ^ 2 /
    (A.conductance (A.source.inverse (A.source.coordinate x)) *
      A.source.density (A.source.inverse (A.source.coordinate x)))) = _
  rw [A.source.inverse_coordinate hx, one_div_div]

theorem sourceMean_unit_node_mem (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) (v : Fin (n + 2)) :
    D.node v ∈ Icc (0 : ℝ) 1 := by
  have hv := D.node_mem v
  rw [hD] at hv
  exact hv

noncomputable def sourceMeanPullbackGeometry (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) : OrderedMedium n where
  source := A.source
  conductance := A.conductance
  conductance_continuous := A.conductance_continuous
  conductance_pos := A.conductance_pos
  node := fun v => A.source.inverse (D.node v)
  node_strictMono := fun i j hij => A.source.inverse_strictMono
    (sourceMean_unit_node_mem D hD i) (sourceMean_unit_node_mem D hD j) (D.node_strictMono hij)
  node_first := by rw [D.node_first, hD]; exact A.source.inverse_zero
  node_last := by rw [D.node_last, hD]; exact A.source.inverse_one

theorem sourceMeanPullbackGeometry_coordinate_node (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) (v : Fin (n + 2)) :
    A.source.coordinate ((sourceMeanPullbackGeometry A D hD).node v) = D.node v :=
  A.source.coordinate_inverse (sourceMean_unit_node_mem D hD v)

theorem sourceMeanPullbackGeometry_site (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) (i : Fin n) :
    (sourceMeanPullbackGeometry A D hD).site i = A.source.inverse (D.site i) := rfl

noncomputable def sourceMeanGapCoordinate (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) (e : Fin (n + 1)) (t : ℝ) : ℝ :=
  A.source.coordinate ((sourceMeanPullbackGeometry A D hD).node e.castSucc + t) - D.node e.castSucc

theorem sourceMeanGapCoordinate_tail (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) (e : Fin (n + 1)) :
    sourceMeanGapCoordinate A D hD e 0 = 0 := by
  rw [sourceMeanGapCoordinate, add_zero, sourceMeanPullbackGeometry_coordinate_node, sub_self]

theorem sourceMeanGapCoordinate_head (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) (e : Fin (n + 1)) :
    sourceMeanGapCoordinate A D hD e ((sourceMeanPullbackGeometry A D hD).gapLength e) = D.gapLength e := by
  rw [sourceMeanGapCoordinate]
  simp only [OrderedMedium.gapLength, add_sub_cancel, sourceMeanPullbackGeometry_coordinate_node]

theorem sourceMeanGapCoordinate_continuous (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) (e : Fin (n + 1)) :
    ContinuousOn (sourceMeanGapCoordinate A D hD e)
      (Icc 0 ((sourceMeanPullbackGeometry A D hD).gapLength e)) :=
  (A.source.coordinate_continuous.comp (continuous_const.add continuous_id).continuousOn
    (fun _ ht => (sourceMeanPullbackGeometry A D hD).gap_point_mem e ht)).sub continuousOn_const

theorem sourceMeanGapCoordinate_mem (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) (e : Fin (n + 1)) {t : ℝ}
    (ht : t ∈ Icc 0 ((sourceMeanPullbackGeometry A D hD).gapLength e)) :
    sourceMeanGapCoordinate A D hD e t ∈ Icc 0 (D.gapLength e) := by
  let G := sourceMeanPullbackGeometry A D hD
  have hl : G.node e.castSucc ≤ G.node e.castSucc + t := le_add_of_nonneg_right ht.1
  have hr : G.node e.castSucc + t ≤ G.node e.succ := by
    have htr := ht.2
    change t ≤ G.node e.succ - G.node e.castSucc at htr
    linarith
  have hc₁ := A.source.coordinate_strictMono.monotoneOn (G.node_mem e.castSucc) (G.gap_point_mem e ht) hl
  have hc₂ := A.source.coordinate_strictMono.monotoneOn (G.gap_point_mem e ht) (G.node_mem e.succ) hr
  change A.source.coordinate ((sourceMeanPullbackGeometry A D hD).node e.castSucc) ≤ _ at hc₁
  change _ ≤ A.source.coordinate ((sourceMeanPullbackGeometry A D hD).node e.succ) at hc₂
  rw [sourceMeanPullbackGeometry_coordinate_node] at hc₁ hc₂
  constructor
  · exact sub_nonneg.mpr hc₁
  · exact sub_le_sub_right hc₂ _

theorem sourceMeanGapCoordinate_interior (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) (e : Fin (n + 1)) {t : ℝ}
    (ht : t ∈ Ioo 0 ((sourceMeanPullbackGeometry A D hD).gapLength e)) :
    sourceMeanGapCoordinate A D hD e t ∈ Ioo 0 (D.gapLength e) := by
  let G := sourceMeanPullbackGeometry A D hD
  have hl : G.node e.castSucc < G.node e.castSucc + t := lt_add_of_pos_right _ ht.1
  have hr : G.node e.castSucc + t < G.node e.succ := by
    have htr := ht.2
    change t < G.node e.succ - G.node e.castSucc at htr
    linarith
  have hx := G.gap_point_mem e (Ioo_subset_Icc_self ht)
  have hc₁ := A.source.coordinate_strictMono (G.node_mem e.castSucc) hx hl
  have hc₂ := A.source.coordinate_strictMono hx (G.node_mem e.succ) hr
  change A.source.coordinate ((sourceMeanPullbackGeometry A D hD).node e.castSucc) < _ at hc₁
  change _ < A.source.coordinate ((sourceMeanPullbackGeometry A D hD).node e.succ) at hc₂
  rw [sourceMeanPullbackGeometry_coordinate_node] at hc₁ hc₂
  constructor
  · exact sub_pos.mpr hc₁
  · exact sub_lt_sub_right hc₂ _

theorem sourceMeanGapCoordinate_derivative (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source) (e : Fin (n + 1)) {t : ℝ}
    (ht : t ∈ Ioo 0 ((sourceMeanPullbackGeometry A D hD).gapLength e)) :
    HasDerivAt (sourceMeanGapCoordinate A D hD e)
      (A.source.density ((sourceMeanPullbackGeometry A D hD).node e.castSucc + t) / A.source.mass) t := by
  have hd := (A.source.coordinate_derivative ((sourceMeanPullbackGeometry A D hD).gap_point_interior e ht)).comp t
    ((hasDerivAt_id t).const_add ((sourceMeanPullbackGeometry A D hD).node e.castSucc))
  have he := hd.sub_const (D.node e.castSucc)
  change HasDerivAt (sourceMeanGapCoordinate A D hD e)
    ((A.source.density ((sourceMeanPullbackGeometry A D hD).node e.castSucc + t) / A.source.mass) * 1) t at he
  simpa only [mul_one] using he

theorem sourceMeanGapCoordinate_conductance (A : IntervalMedium) (D : OrderedMedium n)
    (hD : D.source = (homogeneous 1 1 zero_lt_one zero_lt_one).source)
    (haD : D.conductance = sourceMeanConductance A) (e : Fin (n + 1)) {t : ℝ}
    (ht : t ∈ Icc 0 ((sourceMeanPullbackGeometry A D hD).gapLength e)) :
    D.conductance (D.node e.castSucc + sourceMeanGapCoordinate A D hD e t) =
      A.conductance ((sourceMeanPullbackGeometry A D hD).node e.castSucc + t) *
        A.source.density ((sourceMeanPullbackGeometry A D hD).node e.castSucc + t) / A.source.mass ^ 2 := by
  rw [haD, sourceMeanGapCoordinate, add_sub_cancel, sourceMeanConductance_coordinate A
    ((sourceMeanPullbackGeometry A D hD).gap_point_mem e ht)]

end TimeTraps.Interval
