module

public import TimeTraps.Interval.WeakProblem

@[expose] public section

/-!
The physical essential-supremum norm is defined from Lebesgue measure on the
single interval, independently of the ordered graph. It agrees with the
attained state maximum for every weak solution.
-/

namespace TimeTraps.Interval

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Graph

variable {n : ℕ}

noncomputable def OrderedMedium.essentialNorm (D : OrderedMedium n) (w : ℝ → ℝ) : ℝ :=
  essSup (fun x => |w x|) (volume.restrict (Icc D.source.left D.source.right))

theorem continuous_interval_le_of_ae_le {u : ℝ → ℝ} {l r M : ℝ} (hlr : l < r)
    (hu : ContinuousOn u (Icc l r)) (hb : u ≤ᵐ[volume.restrict (Icc l r)] fun _ => M) :
    ∀ x ∈ Icc l r, u x ≤ M := by
  have heq : (fun x => min (u x) M) =ᵐ[volume.restrict (Icc l r)] u :=
    hb.mono fun x hx => min_eq_left hx
  have hon := Measure.eqOn_Icc_of_ae_eq volume (ne_of_lt hlr) heq (hu.inf continuousOn_const) hu
  intro x hx
  exact min_eq_left_iff.mp (hon hx)

theorem OrderedMedium.essentialNorm_le_iff (D : OrderedMedium n) {w : ℝ → ℝ}
    (hw : IntervalEnergy w D.source.left D.source.right) {M : ℝ} :
    D.essentialNorm w ≤ M ↔ ∀ x ∈ Icc D.source.left D.source.right, |w x| ≤ M := by
  have hc : ContinuousOn w (Icc D.source.left D.source.right) := by
    simpa only [uIcc_of_le D.source.increasing.le] using hw.continuousOn
  let : NeZero (volume.restrict (Icc D.source.left D.source.right)) := ⟨by
    intro hz
    have hzv := Measure.restrict_eq_zero.mp hz
    have hp : 0 < volume (Icc D.source.left D.source.right) := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr D.source.increasing)
    exact (ne_of_gt hp) hzv⟩
  obtain ⟨x₀, _, hx₀⟩ := isCompact_Icc.exists_isMaxOn
    ⟨D.source.left, le_rfl, D.source.increasing.le⟩ hc.abs
  have hb : IsBoundedUnder (· ≤ ·) (ae (volume.restrict (Icc D.source.left D.source.right)))
      (fun x => |w x|) :=
    ⟨|w x₀|, (ae_restrict_mem measurableSet_Icc).mono fun x hx => hx₀ hx⟩
  have hcb : IsCoboundedUnder (· ≤ ·) (ae (volume.restrict (Icc D.source.left D.source.right)))
      (fun x => |w x|) := isCoboundedUnder_le_of_le _ (fun x => abs_nonneg (w x))
  constructor
  · intro hM
    exact continuous_interval_le_of_ae_le D.source.increasing hc.abs
      ((ae_le_essSup hb).mono fun x hx => hx.trans hM)
  · intro hM
    exact essSup_le_of_ae_le M ((ae_restrict_mem measurableSet_Icc).mono fun x hx => hM x hx) hcb

theorem OrderedMedium.essentialNorm_open (D : OrderedMedium n) (w : ℝ → ℝ) :
    D.essentialNorm w = essSup (fun x => |w x|) (volume.restrict (Ioo D.source.left D.source.right)) := by
  unfold OrderedMedium.essentialNorm
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc]

theorem WeakIntervalEquation.positive {D : OrderedMedium n} {κ : Fin n → ℝ} {w : ℝ → ℝ}
    (hw : WeakIntervalEquation D κ w) (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) :
    ∀ x ∈ Icc D.source.left D.source.right, 0 < w x := by
  obtain ⟨j, hj⟩ := hw.to_strong hκ hanchor
  have hp := (hj.positive (nodalStrength_nonneg κ hκ)).2
  intro x hx
  obtain ⟨e, he⟩ := D.gap_cover hx
  have ht : x - D.node e.castSucc ∈ Icc 0 (D.gapLength e) :=
    ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
  simpa only [OrderedMedium.gapRestriction, add_sub_cancel] using hp e _ ht

theorem OrderedMedium.restriction_values (D : OrderedMedium n) (w : ℝ → ℝ) :
    D.graph.stateValues (D.gapRestriction w) = w '' Icc D.source.left D.source.right := by
  ext y
  constructor
  · intro hy
    obtain ⟨e, x, hx, rfl⟩ := mem_iUnion.mp hy
    exact ⟨D.node e.castSucc + x, D.gap_point_mem e hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨e, he⟩ := D.gap_cover hx
    have ht : x - D.node e.castSucc ∈ Icc 0 (D.gapLength e) :=
      ⟨sub_nonneg.mpr he.1, sub_le_sub_right he.2 _⟩
    apply mem_iUnion.mpr
    refine ⟨e, x - D.node e.castSucc, ht, ?_⟩
    simp only [OrderedMedium.gapRestriction, add_sub_cancel]

theorem WeakIntervalEquation.maximum_eq_essentialNorm {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) :
    D.graph.stateMaximum (D.gapRestriction w) = D.essentialNorm w := by
  have hm := (D.restrict_energy hw.energy).maximum_isGreatest
  rw [D.restriction_values] at hm
  apply le_antisymm
  · obtain ⟨x, hx, he⟩ := hm.1
    rw [← he]
    exact (le_abs_self _).trans ((D.essentialNorm_le_iff hw.energy).mp le_rfl x hx)
  · apply (D.essentialNorm_le_iff hw.energy).mpr
    intro x hx
    rw [abs_of_pos (hw.positive hκ hanchor x hx)]
    exact hm.2 ⟨x, hx, rfl⟩

theorem WeakIntervalEquation.essentialNorm_isGreatest {D : OrderedMedium n}
    {κ : Fin n → ℝ} {w : ℝ → ℝ} (hw : WeakIntervalEquation D κ w)
    (hκ : ∀ i, 0 ≤ κ i) (hanchor : ∃ i, 0 < κ i) :
    IsGreatest (w '' Icc D.source.left D.source.right) (D.essentialNorm w) := by
  rw [← hw.maximum_eq_essentialNorm hκ hanchor, ← D.restriction_values]
  exact (D.restrict_energy hw.energy).maximum_isGreatest

end TimeTraps.Interval
