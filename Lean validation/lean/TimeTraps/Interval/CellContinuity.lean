module

public import TimeTraps.Interval.BalancedCell

@[expose] public section

/-!
Joint dependence on the cell endpoints, including zero-length cells. The
explicit primitive-coordinate formula proves continuity off the diagonal;
the center's location between the endpoints proves continuity on it.
-/

namespace TimeTraps.Interval

open Set MeasureTheory Filter
open scoped Topology

def cellDomain : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}

def properCellDomain : Set (ℝ × ℝ) := cellDomain ∩ {p | p.1 < p.2}

theorem cell_left_mem {p : ℝ × ℝ} (hp : p ∈ cellDomain) : p.1 ∈ Icc (0 : ℝ) 1 :=
  ⟨hp.1, hp.2.1.trans hp.2.2⟩

theorem cell_right_mem {p : ℝ × ℝ} (hp : p ∈ cellDomain) : p.2 ∈ Icc (0 : ℝ) 1 :=
  ⟨hp.1.trans hp.2.1, hp.2.2⟩

theorem CellWeight.leftRise_joint_continuous (W : CellWeight) {T : Type*} [TopologicalSpace T]
    {s : Set T} {α c : T → ℝ} (ha : ContinuousOn α s) (hc : ContinuousOn c s)
    (ha_range : MapsTo α s (Icc 0 1)) (hc_range : MapsTo c s (Icc 0 1)) :
    ContinuousOn (fun t => W.leftRise (α t) (c t)) s := by
  have hpa := W.primitive_continuous.comp ha ha_range
  have hpc := W.primitive_continuous.comp hc hc_range
  have hma := W.moment_continuous.comp ha ha_range
  have hmc := W.moment_continuous.comp hc hc_range
  exact ((hmc.sub hma).sub (ha.mul (hpc.sub hpa))).congr
    (fun t ht => W.leftRise_formula (ha_range ht) (hc_range ht))

theorem CellWeight.rightRise_joint_continuous (W : CellWeight) {T : Type*} [TopologicalSpace T]
    {s : Set T} {β c : T → ℝ} (hb : ContinuousOn β s) (hc : ContinuousOn c s)
    (hb_range : MapsTo β s (Icc 0 1)) (hc_range : MapsTo c s (Icc 0 1)) :
    ContinuousOn (fun t => W.rightRise (β t) (c t)) s := by
  have hpb := W.primitive_continuous.comp hb hb_range
  have hpc := W.primitive_continuous.comp hc hc_range
  have hmb := W.moment_continuous.comp hb hb_range
  have hmc := W.moment_continuous.comp hc hc_range
  exact ((hb.mul (hpb.sub hpc)).sub (hmb.sub hmc)).congr
    (fun t ht => W.rightRise_formula (hb_range ht) (hc_range ht))

theorem CellWeight.balanceTarget_continuous (W : CellWeight) :
    ContinuousOn (fun p : ℝ × ℝ => W.balanceTarget p.1 p.2) properCellDomain := by
  have ha : MapsTo (fun p : ℝ × ℝ => p.1) properCellDomain (Icc 0 1) :=
    fun _ hp => cell_left_mem hp.1
  have hb : MapsTo (fun p : ℝ × ℝ => p.2) properCellDomain (Icc 0 1) :=
    fun _ hp => cell_right_mem hp.1
  have hpa := W.primitive_continuous.comp continuous_fst.continuousOn ha
  have hpb := W.primitive_continuous.comp continuous_snd.continuousOn hb
  have hma := W.moment_continuous.comp continuous_fst.continuousOn ha
  have hmb := W.moment_continuous.comp continuous_snd.continuousOn hb
  exact (((hma.sub (continuous_fst.continuousOn.mul hpa)).add
    (continuous_snd.continuousOn.mul hpb)).sub hmb).div
    (continuous_snd.sub continuous_fst).continuousOn
    (fun p hp => ne_of_gt (sub_pos.mpr hp.2))

theorem CellWeight.center_continuous_proper (W : CellWeight) :
    ContinuousOn (fun p : ℝ × ℝ => W.center p.1 p.2) properCellDomain := by
  have hc := W.sourceInterval.inverse_continuous.comp_continuousOn
    (W.balanceTarget_continuous.div_const W.sourceInterval.mass)
  apply hc.congr
  intro p hp
  change W.center p.1 p.2 = W.sourceInterval.inverse (W.balanceTarget p.1 p.2 / W.sourceInterval.mass)
  exact if_pos (show p.1 < p.2 from hp.2)

theorem CellWeight.center_unit (W : CellWeight) {p : ℝ × ℝ} (hp : p ∈ cellDomain) :
    W.center p.1 p.2 ∈ Icc (0 : ℝ) 1 := by
  have hc := W.center_mem hp.1 hp.2.2 hp.2.1
  exact ⟨hp.1.trans hc.1, hc.2.trans hp.2.2⟩

/-- Joint center continuity on the entire closed triangle, including the
diagonal and cells touching the physical endpoints. -/
theorem CellWeight.center_continuous (W : CellWeight) :
    ContinuousOn (fun p : ℝ × ℝ => W.center p.1 p.2) cellDomain := by
  intro p hp
  rcases hp.2.1.lt_or_eq with hlt | he
  · have hc := W.center_continuous_proper p ⟨hp, hlt⟩
    exact (continuousWithinAt_inter ((isOpen_lt continuous_fst continuous_snd).mem_nhds hlt)).mp hc
  · have hz : W.center p.1 p.2 = p.1 := by rw [← he, W.center_diagonal]
    change Tendsto (fun q : ℝ × ℝ => W.center q.1 q.2) (𝓝[cellDomain] p) (𝓝 (W.center p.1 p.2))
    rw [hz]
    have hlo : Tendsto (fun q : ℝ × ℝ => q.1) (𝓝[cellDomain] p) (𝓝 p.1) :=
      continuous_fst.continuousAt.continuousWithinAt
    have hhi : Tendsto (fun q : ℝ × ℝ => q.2) (𝓝[cellDomain] p) (𝓝 p.1) := by
      rw [he]
      exact continuous_snd.continuousAt.continuousWithinAt
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact (W.center_mem hq.1 hq.2.2 hq.2.1).1
    · filter_upwards [self_mem_nhdsWithin] with q hq
      exact (W.center_mem hq.1 hq.2.2 hq.2.1).2

theorem CellWeight.barrier_continuous (W : CellWeight) :
    ContinuousOn (fun p : ℝ × ℝ => W.barrier p.1 p.2) cellDomain :=
  W.leftRise_joint_continuous continuous_fst.continuousOn W.center_continuous
    (fun _ hp => cell_left_mem hp) (fun _ hp => W.center_unit hp)

theorem CellWeight.barrier_zero_iff (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) : W.barrier α β = 0 ↔ α = β := by
  constructor
  · intro hz
    rcases hab.lt_or_eq with hlt | he
    · have hp := W.barrier_pos hα hβ hlt
      linarith
    · exact he
  · rintro rfl
    exact W.barrier_diagonal α

/-- The minimax interpretation also holds on the diagonal of the closed
cell domain, where the only trial site is the common endpoint. -/
theorem CellWeight.local_minimax_closed (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    IsLeast (W.trialHeight α β '' Icc α β) (W.barrier α β) := by
  rcases hab.lt_or_eq with hlt | rfl
  · exact W.local_minimax hα hβ hlt
  · rw [W.barrier_diagonal]
    constructor
    · refine ⟨α, ⟨le_rfl, le_rfl⟩, ?_⟩
      simp only [CellWeight.trialHeight, W.leftRise_self, W.rightRise_self, max_self]
    · rintro M ⟨c, hc, rfl⟩
      have he : c = α := le_antisymm hc.2 hc.1
      rw [he]
      simp only [CellWeight.trialHeight, W.leftRise_self, W.rightRise_self, max_self, le_refl]

end TimeTraps.Interval
