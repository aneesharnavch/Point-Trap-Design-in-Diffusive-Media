module

public import TimeTraps.Interval.EndpointShares
public import TimeTraps.Interval.TransformedIntegral

@[expose] public section

/-! The actual active absorption CDF. On the open source interval it is
the left endpoint share plus the interior CDF; the right endpoint jump
does not contribute there. Its order bounds hold at every active site. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators Classical

variable {A : EndpointArchitecture} {K : ℝ}

noncomputable def EndpointReactions.activeCDF (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) (w : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i, if A.sourceSite D i ≤ z then R.activeShare D w i else 0

theorem EndpointReactions.activeCDF_nodal (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) (w : ℝ → ℝ) (z : ℝ) :
    R.activeCDF D w z = ∑ v, R.nodal v *
      (if D.source.coordinate (D.node v) ≤ z then w (D.node v) / D.source.mass else 0) := by
  calc
    _ = ∑ i, R.activeStrength i *
        (if A.sourceSite D i ≤ z then w (A.physicalSite D i) / D.source.mass else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp only [activeShare, mul_zero, mul_div_assoc]
    _ = _ := R.active_pairing (fun v =>
      if D.source.coordinate (D.node v) ≤ z then w (D.node v) / D.source.mass else 0)

theorem EndpointReactions.activeCDF_interior (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) (w : ℝ → ℝ) {z : ℝ} (hz : z ∈ Ico (0 : ℝ) 1) :
    R.activeCDF D w z = R.leftStrength * w D.source.left / D.source.mass +
      D.absorptionCDF (fun i => R.interiorStrength i * w (D.site i) / D.source.mass) z := by
  rw [R.activeCDF_nodal, R.nodal_pairing]
  simp only [D.node_first, D.node_last, D.source.coordinate_left, D.source.coordinate_right,
    if_pos hz.1, if_neg (not_le.mpr hz.2), mul_zero, add_zero, OrderedMedium.absorptionCDF,
    OrderedMedium.sourceSite, OrderedMedium.site, mul_ite, mul_div_assoc]

theorem EndpointReactions.activeCDF_integrable (R : EndpointReactions A K)
    (D : OrderedMedium A.interiorCount) (w : ℝ → ℝ) (a b : ℝ) :
    IntervalIntegrable (R.activeCDF D w) volume a b := by
  have hi : ∀ i : Fin A.count,
      IntervalIntegrable (fun z => if A.sourceSite D i ≤ z then R.activeShare D w i else 0) volume a b := by
    intro i
    have hc : IntervalIntegrable (fun _ : ℝ => R.activeShare D w i) volume a b := intervalIntegrable_const
    have he : (Ici (A.sourceSite D i)).indicator (fun _ : ℝ => R.activeShare D w i) =
        (fun z => if A.sourceSite D i ≤ z then R.activeShare D w i else 0) := by
      funext z
      simp only [Set.indicator, mem_Ici]
    constructor
    · rw [← he]
      exact hc.1.indicator measurableSet_Ici
    · rw [← he]
      exact hc.2.indicator measurableSet_Ici
  have hs := IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
  have he : (∑ i : Fin A.count, fun z => if A.sourceSite D i ≤ z then R.activeShare D w i else 0) =
      R.activeCDF D w := by funext z; simp only [activeCDF, Finset.sum_apply]
  rwa [he] at hs

theorem EndpointWeakEquation.activeCDF_before {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (i : Fin A.count) {t : ℝ} (ht : t < A.sourceSite D i) :
    R.activeCDF D w t ≤ hw.partition.point i.castSucc := by
  change R.activeCDF D w t ≤ absorptionPrefix (R.activeShare D w) i.castSucc
  have hp := fun k => (hw.activeShare_pos k).le
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val < i.val
  · simp only [Fin.val_castSucc, if_pos hk]
    split_ifs <;> simp [hp k]
  · have hik : i ≤ k := by change i.val ≤ k.val; omega
    have hn : ¬ A.sourceSite D k ≤ t :=
      not_le.mpr (ht.trans_le ((A.sourceSite_strictMono D).monotone hik))
    simp only [Fin.val_castSucc, if_neg hk, if_neg hn, le_refl]

theorem EndpointWeakEquation.activeCDF_after {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w)
    (i : Fin A.count) {t : ℝ} (ht : A.sourceSite D i < t) :
    hw.partition.point i.succ ≤ R.activeCDF D w t := by
  change absorptionPrefix (R.activeShare D w) i.succ ≤ R.activeCDF D w t
  have hp := fun k => (hw.activeShare_pos k).le
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val < i.val + 1
  · have hki : k ≤ i := by change k.val ≤ i.val; omega
    have hy : A.sourceSite D k ≤ t := ((A.sourceSite_strictMono D).monotone hki).trans ht.le
    simp only [Fin.val_succ, if_pos hk, if_pos hy, le_refl]
  · simp only [Fin.val_succ, if_neg hk]
    split_ifs <;> simp [hp k]

end TimeTraps.Interval
