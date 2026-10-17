module

public import TimeTraps.Interval.EndpointHeightFlux
public import TimeTraps.Interval.HeightComparison

@[expose] public section

/-! Actual mixed height barriers. Integrated CDF comparisons apply to
every active physical site, including interior sites outside their source
cells. Endpoint cells retain their full one-sided rise. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis

variable {A : EndpointArchitecture} {K : ℝ}

theorem EndpointWeakEquation.transformed_le_norm {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) (z : ℝ) :
    D.source.transformed w z ≤ D.essentialNorm w :=
  hw.essentialNorm_isGreatest.2 ⟨D.source.inverse z, D.source.inverse_mem z, rfl⟩

theorem EndpointWeakEquation.active_leftRise_bound {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) (i : Fin A.count)
    (hac : hw.partition.point i.castSucc ≤ A.sourceSite D i) :
    D.medium.cellWeight.leftRise (hw.partition.point i.castSucc) (A.sourceSite D i) ≤
      D.source.transformed w (hw.partition.point i.castSucc) - w (A.physicalSite D i) := by
  let α := hw.partition.point i.castSucc
  let c := A.sourceSite D i
  have hα := hw.partition.point_mem i.castSucc
  have hc := A.sourceSite_mem D i
  have hweight := D.source.weight_continuous D.conductance_continuous D.conductance_pos
  have hi : IntervalIntegrable (fun t => D.source.weight D.conductance t * (t - α)) volume α c :=
    (hweight.mul (continuous_id.sub continuous_const)).intervalIntegrable α c
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hac hi
    (R.activeSlope_integrable D w α c).neg (fun t ht => ?_)
  · change (∫ t in α..c, D.source.weight D.conductance t * (t - α)) ≤
      ∫ t in α..c, -(R.activeSlope D w t) at hm
    rw [intervalIntegral.integral_neg, hw.transformed_integral hα.1 hc.2 hac] at hm
    change D.medium.cellWeight.leftRise α c ≤ -(D.source.transformed w c - D.source.transformed w α) at hm
    dsimp only [c] at hm
    rw [A.transformed_activeSite D w i] at hm
    linarith
  · have hb := hw.activeCDF_before i ht.2
    change R.activeCDF D w t ≤ α at hb
    have hm := mul_le_mul_of_nonneg_left hb (D.source.weight_pos D.conductance_pos t).le
    change D.source.weight D.conductance t * (t - α) ≤
      -(D.source.weight D.conductance t * (R.activeCDF D w t - t))
    nlinarith only [hm]

theorem EndpointWeakEquation.active_rightRise_bound {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) (i : Fin A.count)
    (hcb : A.sourceSite D i ≤ hw.partition.point i.succ) :
    D.medium.cellWeight.rightRise (hw.partition.point i.succ) (A.sourceSite D i) ≤
      D.source.transformed w (hw.partition.point i.succ) - w (A.physicalSite D i) := by
  let β := hw.partition.point i.succ
  let c := A.sourceSite D i
  have hβ := hw.partition.point_mem i.succ
  have hc := A.sourceSite_mem D i
  have hweight := D.source.weight_continuous D.conductance_continuous D.conductance_pos
  have hi : IntervalIntegrable (fun t => D.source.weight D.conductance t * (β - t)) volume c β :=
    (hweight.mul (continuous_const.sub continuous_id)).intervalIntegrable c β
  have hm := intervalIntegral.integral_mono_on_of_le_Ioo hcb hi
    (R.activeSlope_integrable D w c β) (fun t ht => ?_)
  · rw [hw.transformed_integral hc.1 hβ.2 hcb] at hm
    change D.medium.cellWeight.rightRise β c ≤ D.source.transformed w β - D.source.transformed w c at hm
    dsimp only [c] at hm
    rw [A.transformed_activeSite D w i] at hm
    exact hm
  · have hb := hw.activeCDF_after i ht.1
    change β ≤ R.activeCDF D w t at hb
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hb t)
      (D.source.weight_pos D.conductance_pos t).le

theorem EndpointWeakEquation.mixed_height_barrier {D : OrderedMedium A.interiorCount}
    {R : EndpointReactions A K} {w : ℝ → ℝ} (hw : EndpointWeakEquation D R w) (i : Fin A.count) :
    A.barrier hw.partition.closed D.medium.cellWeight i ≤
      D.essentialNorm w - w (A.physicalSite D i) := by
  have hα := hw.partition.point_mem i.castSucc
  have hβ := hw.partition.point_mem i.succ
  have hab := hw.partition.strictMono (Fin.castSucc_lt_succ (i := i))
  have hc := A.sourceSite_mem D i
  have hMa := hw.transformed_le_norm (hw.partition.point i.castSucc)
  have hMb := hw.transformed_le_norm (hw.partition.point i.succ)
  change D.medium.cellWeight.orientedBarrier (A.kind i)
    (hw.partition.point i.castSucc) (hw.partition.point i.succ) ≤ _
  cases hi : A.kind i with
  | ordinary =>
    exact (D.medium.cellWeight.height_comparison hα.1 hβ.2 hab hc hMa hMb
      (hw.active_leftRise_bound i) (hw.active_rightRise_bound i)).1
  | leftEndpoint =>
    have hi0 : i.castSucc = 0 := Fin.ext ((A.kind_left_iff i).mp hi).2
    have hα0 : hw.partition.point i.castSucc = 0 := by rw [hi0, hw.partition.first]
    have hc0 := A.sourceSite_left D i hi
    have hb := hw.active_rightRise_bound i (by rw [hc0]; exact hβ.1)
    rw [hc0] at hb
    change D.medium.cellWeight.rightRise (hw.partition.point i.succ) (hw.partition.point i.castSucc) ≤ _
    rw [hα0]
    linarith
  | rightEndpoint =>
    have hi1 : i.succ = Fin.last A.count := Fin.ext ((A.kind_right_iff i).mp hi).2
    have hβ1 : hw.partition.point i.succ = 1 := by rw [hi1, hw.partition.last]
    have hc1 := A.sourceSite_right D i hi
    have hb := hw.active_leftRise_bound i (by rw [hc1]; exact hα.2)
    rw [hc1] at hb
    change D.medium.cellWeight.leftRise (hw.partition.point i.castSucc) (hw.partition.point i.succ) ≤ _
    rw [hβ1]
    linarith

end TimeTraps.Interval
