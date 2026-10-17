module

public import TimeTraps.Interval.EndpointReconstructionCDF

@[expose] public section

/-! An exact integral profile anchored at a mixed cell's outer maximum.
The anchor and all ordinary-cell boundaries have height M. Reactive
physical ends instead have their full one-sided barrier deficit. -/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis

def EndpointArchitecture.gapBoundary (A : EndpointArchitecture)
    (e : Fin (A.interiorCount + 1)) : Fin (A.count + 1) :=
  ⟨A.leftReactive.toNat + e.val, by have he := e.isLt; unfold count; omega⟩

theorem EndpointArchitecture.gapBoundary_left (A : EndpointArchitecture) (i : Fin A.count)
    (hi : A.kind i = .leftEndpoint) : i.succ = A.gapBoundary 0 := by
  obtain ⟨hl, hv⟩ := (A.kind_left_iff i).mp hi
  apply Fin.ext
  simp only [Fin.val_succ, gapBoundary, hl, Bool.toNat_true, Fin.val_zero, Nat.add_zero, hv]

theorem EndpointArchitecture.gapBoundary_right (A : EndpointArchitecture) (i : Fin A.count)
    (hi : A.kind i = .rightEndpoint) : i.castSucc = A.gapBoundary (Fin.last A.interiorCount) := by
  obtain ⟨hr, hv⟩ := (A.kind_right_iff i).mp hi
  apply Fin.ext
  simp only [gapBoundary, Fin.val_castSucc, Fin.val_last]
  simp only [count, hr, Bool.toNat_true] at hv
  omega

noncomputable def IntervalMedium.endpointPartitionProfile (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M z : ℝ) : ℝ :=
  M + ∫ t in Q.point (A.gapBoundary 0)..z, B.endpointPartitionSlope A Q t

theorem IntervalMedium.endpointPartitionProfile_continuous (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) :
    Continuous (B.endpointPartitionProfile A Q M) :=
  continuous_const.add (intervalIntegral.continuous_primitive
    (B.endpointPartitionSlope_integrable A Q) _)

theorem IntervalMedium.endpointPartitionProfile_derivative (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) {z : ℝ}
    (hz : ∀ i, A.reconstructionSite Q B.cellWeight i ≠ z) :
    HasDerivAt (B.endpointPartitionProfile A Q M) (B.endpointPartitionSlope A Q z) z :=
  (intervalIntegral.integral_hasDerivAt_right (B.endpointPartitionSlope_integrable A Q _ z)
    (B.endpointPartitionSlope_measurable A Q).stronglyMeasurable.stronglyMeasurableAtFilter
    (B.endpointPartitionSlope_continuousAt A Q hz)).const_add M

theorem IntervalMedium.endpointPartitionProfile_difference (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M a b : ℝ) :
    B.endpointPartitionProfile A Q M b - B.endpointPartitionProfile A Q M a =
      ∫ t in a..b, B.endpointPartitionSlope A Q t := by
  unfold endpointPartitionProfile
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (B.endpointPartitionSlope_integrable A Q _ b) (B.endpointPartitionSlope_integrable A Q _ a)

theorem IntervalMedium.endpointPartitionProfile_left (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) (i : Fin A.count)
    {z : ℝ} (hz : z ∈ Icc (Q.point i.castSucc) (A.reconstructionSite Q B.cellWeight i)) :
    B.endpointPartitionProfile A Q M z - B.endpointPartitionProfile A Q M (Q.point i.castSucc) =
      -B.cellWeight.leftRise (Q.point i.castSucc) z := by
  rw [B.endpointPartitionProfile_difference]
  change (∫ t in Q.point i.castSucc..z, B.endpointPartitionSlope A Q t) =
    -(∫ t in Q.point i.castSucc..z, B.source.weight B.conductance t * (t - Q.point i.castSucc))
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr_Ioo_of_le hz.1
  intro t ht
  dsimp only [endpointPartitionSlope]
  rw [A.reconstructionCDF_left Q B.cellWeight i ⟨ht.1, ht.2.trans_le hz.2⟩]
  ring

theorem IntervalMedium.endpointPartitionProfile_right (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) (i : Fin A.count)
    {z : ℝ} (hz : z ∈ Icc (A.reconstructionSite Q B.cellWeight i) (Q.point i.succ)) :
    B.endpointPartitionProfile A Q M (Q.point i.succ) - B.endpointPartitionProfile A Q M z =
      B.cellWeight.rightRise (Q.point i.succ) z := by
  rw [B.endpointPartitionProfile_difference]
  apply intervalIntegral.integral_congr_Ioo_of_le hz.2
  intro t ht
  dsimp only [endpointPartitionSlope]
  rw [A.reconstructionCDF_right Q B.cellWeight i ⟨hz.1.trans_lt ht.1, ht.2⟩]
  rfl

theorem IntervalMedium.endpointPartitionProfile_ordinary_equal (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) (j : Fin A.interiorCount) :
    B.endpointPartitionProfile A Q M (Q.point (A.gapBoundary j.succ)) =
      B.endpointPartitionProfile A Q M (Q.point (A.gapBoundary j.castSucc)) := by
  have hc := A.reconstructionSite_mem Q B.cellWeight (A.interiorCell j)
  have hl := B.endpointPartitionProfile_left A Q M (A.interiorCell j) ⟨hc.1, le_rfl⟩
  have hr := B.endpointPartitionProfile_right A Q M (A.interiorCell j) ⟨le_rfl, hc.2⟩
  rw [A.reconstructionSite_ordinary Q B.cellWeight _ (A.kind_interiorCell j)] at hl hr
  rw [Q.balance] at hl
  change B.endpointPartitionProfile A Q M (Q.center B.cellWeight (A.interiorCell j)) -
    B.endpointPartitionProfile A Q M (Q.point (A.gapBoundary j.castSucc)) = _ at hl
  change B.endpointPartitionProfile A Q M (Q.point (A.gapBoundary j.succ)) -
    B.endpointPartitionProfile A Q M (Q.center B.cellWeight (A.interiorCell j)) = _ at hr
  linarith

theorem IntervalMedium.endpointPartitionProfile_boundary (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ)
    (e : Fin (A.interiorCount + 1)) :
    B.endpointPartitionProfile A Q M (Q.point (A.gapBoundary e)) = M := by
  induction e using Fin.induction with
  | zero => simp only [endpointPartitionProfile, intervalIntegral.integral_same, add_zero]
  | succ i ih => rw [B.endpointPartitionProfile_ordinary_equal, ih]

theorem IntervalMedium.endpointPartitionProfile_site (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) (i : Fin A.count) :
    B.endpointPartitionProfile A Q M (A.reconstructionSite Q B.cellWeight i) =
      M - A.barrier Q.closed B.cellWeight i := by
  have hc := A.reconstructionSite_mem Q B.cellWeight i
  cases hi : A.kind i with
  | ordinary =>
    obtain ⟨j, rfl⟩ := A.ordinary_is_interiorCell i hi
    have hl := B.endpointPartitionProfile_left A Q M (A.interiorCell j) ⟨hc.1, le_rfl⟩
    change _ - B.endpointPartitionProfile A Q M (Q.point (A.gapBoundary j.castSucc)) = _ at hl
    rw [B.endpointPartitionProfile_boundary] at hl
    rw [A.barrier_ordinary Q.closed B.cellWeight _ hi]
    rw [A.reconstructionSite_ordinary Q B.cellWeight _ hi] at hl ⊢
    change B.endpointPartitionProfile A Q M (Q.center B.cellWeight (A.interiorCell j)) =
      M - B.cellWeight.leftRise (Q.point (A.interiorCell j).castSucc) (Q.center B.cellWeight (A.interiorCell j))
    linarith
  | leftEndpoint =>
    have hr := B.endpointPartitionProfile_right A Q M i ⟨le_rfl, hc.2⟩
    rw [A.gapBoundary_left i hi, B.endpointPartitionProfile_boundary] at hr
    change _ = M - B.cellWeight.orientedBarrier (A.kind i) _ _
    simp only [CellWeight.orientedBarrier, hi]
    have he : i.castSucc = 0 := Fin.ext ((A.kind_left_iff i).mp hi).2
    change B.endpointPartitionProfile A Q M (A.reconstructionSite Q B.cellWeight i) =
      M - B.cellWeight.rightRise (Q.point i.succ) (Q.point i.castSucc)
    simp only [EndpointArchitecture.reconstructionSite, hi] at hr ⊢
    rw [he, Q.first, A.gapBoundary_left i hi]
    linarith
  | rightEndpoint =>
    have hl := B.endpointPartitionProfile_left A Q M i ⟨hc.1, le_rfl⟩
    rw [A.gapBoundary_right i hi, B.endpointPartitionProfile_boundary] at hl
    change _ = M - B.cellWeight.orientedBarrier (A.kind i) _ _
    simp only [CellWeight.orientedBarrier, hi]
    have he : i.succ = Fin.last A.count := Fin.ext ((A.kind_right_iff i).mp hi).2
    change B.endpointPartitionProfile A Q M (A.reconstructionSite Q B.cellWeight i) =
      M - B.cellWeight.leftRise (Q.point i.castSucc) (Q.point i.succ)
    simp only [EndpointArchitecture.reconstructionSite, hi] at hl ⊢
    rw [he, Q.last, A.gapBoundary_right i hi]
    linarith

theorem IntervalMedium.endpointPartitionProfile_le (B : IntervalMedium)
    (A : EndpointArchitecture) (Q : StrictPartition A.count) (M : ℝ) {z : ℝ}
    (hz : z ∈ Icc (0 : ℝ) 1) : B.endpointPartitionProfile A Q M z ≤ M := by
  obtain ⟨i, hi⟩ := Q.cover hz
  have hleft (hb : B.endpointPartitionProfile A Q M (Q.point i.castSucc) = M)
      (hc : z ≤ A.reconstructionSite Q B.cellWeight i) : B.endpointPartitionProfile A Q M z ≤ M := by
    have he := B.endpointPartitionProfile_left A Q M i ⟨hi.1, hc⟩
    rw [hb] at he
    have hn : 0 ≤ B.cellWeight.leftRise (Q.point i.castSucc) z :=
      intervalIntegral.integral_nonneg hi.1 (fun t ht =>
        mul_nonneg (B.source.weight_pos B.conductance_pos t).le (sub_nonneg.mpr ht.1))
    linarith
  have hright (hb : B.endpointPartitionProfile A Q M (Q.point i.succ) = M)
      (hc : A.reconstructionSite Q B.cellWeight i ≤ z) : B.endpointPartitionProfile A Q M z ≤ M := by
    have he := B.endpointPartitionProfile_right A Q M i ⟨hc, hi.2⟩
    rw [hb] at he
    have hn : 0 ≤ B.cellWeight.rightRise (Q.point i.succ) z :=
      intervalIntegral.integral_nonneg hi.2 (fun t ht =>
        mul_nonneg (B.source.weight_pos B.conductance_pos t).le (sub_nonneg.mpr ht.2))
    linarith
  cases hk : A.kind i with
  | ordinary =>
    obtain ⟨j, rfl⟩ := A.ordinary_is_interiorCell i hk
    rcases le_total z (A.reconstructionSite Q B.cellWeight (A.interiorCell j)) with hc | hc
    · exact hleft (B.endpointPartitionProfile_boundary A Q M j.castSucc) hc
    · exact hright (B.endpointPartitionProfile_boundary A Q M j.succ) hc
  | leftEndpoint =>
    apply hright
    · rw [A.gapBoundary_left i hk, B.endpointPartitionProfile_boundary]
    · simpa only [EndpointArchitecture.reconstructionSite, hk] using hz.1
  | rightEndpoint =>
    apply hleft
    · rw [A.gapBoundary_right i hk, B.endpointPartitionProfile_boundary]
    · simpa only [EndpointArchitecture.reconstructionSite, hk] using hz.2

end TimeTraps.Interval
