module

public import TimeTraps.Interval.PhysicalMediumComparison

@[expose] public section

/-!
The L-infinity distance in the manuscript is the Lebesgue essential
supremum on the open source interval. Continuity turns that hypothesis into
the pointwise bound used by the integral proof, including endpoint values.
-/

namespace TimeTraps.Interval

open Set MeasureTheory Filter

variable {n : ℕ}

noncomputable def CellWeight.uniformDistance (W V : CellWeight) : ℝ :=
  essSup (fun x => |W.value x - V.value x|) (volume.restrict (Ioo (0 : ℝ) 1))

theorem CellWeight.uniformDistance_closed (W V : CellWeight) :
    W.uniformDistance V =
      essSup (fun x => |W.value x - V.value x|) (volume.restrict (Icc (0 : ℝ) 1)) := by
  unfold uniformDistance
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]

theorem CellWeight.uniformDistance_le_iff (W V : CellWeight) {ε : ℝ} :
    W.uniformDistance V ≤ ε ↔ ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε := by
  rw [W.uniformDistance_closed V]
  have hc : ContinuousOn (fun x => |W.value x - V.value x|) (Icc (0 : ℝ) 1) :=
    (W.continuous.sub V.continuous).abs
  let : NeZero (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by
    intro hz
    have hzv := Measure.restrict_eq_zero.mp hz
    have hp : 0 < volume (Icc (0 : ℝ) 1) := by simp
    exact (ne_of_gt hp) hzv⟩
  obtain ⟨x₀, _, hx₀⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, zero_le_one⟩ hc
  have hb : IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Icc (0 : ℝ) 1)))
      (fun x => |W.value x - V.value x|) :=
    ⟨|W.value x₀ - V.value x₀|, (ae_restrict_mem measurableSet_Icc).mono fun x hx => hx₀ hx⟩
  have hcb : IsCoboundedUnder (· ≤ ·) (ae (volume.restrict (Icc (0 : ℝ) 1)))
      (fun x => |W.value x - V.value x|) :=
    isCoboundedUnder_le_of_le _ (fun x => abs_nonneg (W.value x - V.value x))
  constructor
  · intro hε
    exact continuous_interval_le_of_ae_le zero_lt_one hc
      ((ae_le_essSup hb).mono fun x hx => hx.trans hε)
  · intro hε
    exact essSup_le_of_ae_le ε ((ae_restrict_mem measurableSet_Icc).mono fun x hx => hε x hx) hcb

theorem ClosedPartition.root_abs_sub_le_Linfty (Q : ClosedPartition n) (W V : CellWeight)
    {ε : ℝ} (hWV : W.uniformDistance V ≤ ε) {b : ℝ} (hb : 0 < b) :
    |Q.root W hb - Q.root V hb| ≤ ε * Q.mesh ^ 2 / 2 :=
  Q.root_abs_sub_le_mesh W V ((W.uniformDistance_le_iff V).mp hWV) hb

theorem CellWeight.optimalIn_abs_sub_le_Linfty (W V : CellWeight)
    (C : Set (ClosedPartition n)) (hC : C.Nonempty)
    {ε : ℝ} (hWV : W.uniformDistance V ≤ ε) {b : ℝ} (hb : 0 < b) :
    |W.optimalIn C hb - V.optimalIn C hb| ≤ ε / 2 :=
  W.optimalIn_abs_sub_le V C hC ((W.uniformDistance_le_iff V).mp hWV) hb

theorem CellWeight.optimalValue_abs_sub_le_Linfty (W V : CellWeight) (hn : 0 < n)
    {ε : ℝ} (hWV : W.uniformDistance V ≤ ε) {b : ℝ} (hb : 0 < b) :
    |W.optimalValue n hb - V.optimalValue n hb| ≤ ε / 2 :=
  W.optimalValue_abs_sub_le V hn ((W.uniformDistance_le_iff V).mp hWV) hb

theorem IntervalMedium.optimalValue_abs_sub_le_Linfty (A B : IntervalMedium) (hn : 0 < n)
    {K₁ K₂ ε : ℝ} (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hbudget : K₁ / A.source.mass = K₂ / B.source.mass)
    (hAB : A.cellWeight.uniformDistance B.cellWeight ≤ ε) :
    |A.optimalValue n K₁ - B.optimalValue n K₂| ≤ ε / 2 :=
  A.optimalValue_abs_sub_le B hn hK₁ hK₂ hbudget ((A.cellWeight.uniformDistance_le_iff B.cellWeight).mp hAB)

end TimeTraps.Interval
