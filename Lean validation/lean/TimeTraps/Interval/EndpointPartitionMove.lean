module

public import TimeTraps.Interval.EndpointPartitionRoot
public import TimeTraps.Interval.PartitionMove

@[expose] public section

/-!
A small boundary transfer between cells whose kinds remain fixed. At a
zero receiver the new barrier tends to zero, while a positive donor's
barrier strictly decreases on its proper subcell. This applies even when
the two cells have different orientations.
-/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology

theorem CellWeight.oriented_split_left_exists (W : CellWeight) (left right : CellKind)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) :
    ∃ c ∈ Ioo α β,
      W.orientedBarrier left α c < W.orientedBarrier right α β ∧
      W.orientedBarrier right c β < W.orientedBarrier right α β := by
  have hcont : ContinuousOn (fun c => W.orientedBarrier left α c) (Icc α β) :=
    (W.orientedBarrier_continuous left).comp
      (continuousOn_const.prodMk continuousOn_id)
      (fun c hc => ⟨hα, hc.1, hc.2.trans hβ⟩)
  have hzero := W.orientedBarrier_diagonal left α
  have hpos := W.orientedBarrier_pos right hα hβ hab
  have hlim : Tendsto (fun c => W.orientedBarrier left α c)
      (𝓝[Ioo α β] α) (𝓝 (W.orientedBarrier left α α)) :=
    (hcont α ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self
  have he := hlim.eventually_lt_const (by rw [hzero]; exact hpos)
  let : NeBot (𝓝[Ioo α β] α) := left_nhdsWithin_Ioo_neBot hab
  obtain ⟨c, hcR, hc⟩ := (he.and self_mem_nhdsWithin).exists
  exact ⟨c, hc, hcR, W.orientedBarrier_strict_subcell right hα hβ
    hc.1.le hc.2 le_rfl (Or.inl hc.1)⟩

theorem CellWeight.oriented_split_right_exists (W : CellWeight) (left right : CellKind)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) :
    ∃ c ∈ Ioo α β,
      W.orientedBarrier left α c < W.orientedBarrier left α β ∧
      W.orientedBarrier right c β < W.orientedBarrier left α β := by
  have hcont : ContinuousOn (fun c => W.orientedBarrier right c β) (Icc α β) :=
    (W.orientedBarrier_continuous right).comp
      (continuousOn_id.prodMk continuousOn_const)
      (fun c hc => ⟨hα.trans hc.1, hc.2, hβ⟩)
  have hzero := W.orientedBarrier_diagonal right β
  have hpos := W.orientedBarrier_pos left hα hβ hab
  have hlim : Tendsto (fun c => W.orientedBarrier right c β)
      (𝓝[Ioo α β] β) (𝓝 (W.orientedBarrier right β β)) :=
    (hcont β ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self
  have he := hlim.eventually_lt_const (by rw [hzero]; exact hpos)
  let : NeBot (𝓝[Ioo α β] β) := right_nhdsWithin_Ioo_neBot hab
  obtain ⟨c, hcR, hc⟩ := (he.and self_mem_nhdsWithin).exists
  exact ⟨c, hc, W.orientedBarrier_strict_subcell left hα hβ
    le_rfl hc.1 hc.2.le (Or.inr hc.2), hcR⟩

variable {n : ℕ}

noncomputable def ClosedPartition.mixedBarrier (Q : ClosedPartition n) (W : CellWeight)
    (kind : Fin n → CellKind) (i : Fin n) : ℝ :=
  W.orientedBarrier (kind i) (Q.point i.castSucc) (Q.point i.succ)

theorem EndpointArchitecture.barrier_eq_mixedBarrier (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) :
    A.barrier Q W = Q.mixedBarrier W A.kind := rfl

theorem ClosedPartition.move_mixedBarrier_left (Q : ClosedPartition (n + 1))
    (W : CellWeight) (kind : Fin (n + 1) → CellKind) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    (Q.move i c hc).mixedBarrier W kind i.castSucc =
      W.orientedBarrier (kind i.castSucc) (Q.point i.castSucc.castSucc) c := by
  unfold mixedBarrier
  rw [Q.move_middle, Q.move_left]

theorem ClosedPartition.move_mixedBarrier_right (Q : ClosedPartition (n + 1))
    (W : CellWeight) (kind : Fin (n + 1) → CellKind) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ)) :
    (Q.move i c hc).mixedBarrier W kind i.succ =
      W.orientedBarrier (kind i.succ) c (Q.point i.succ.succ) := by
  unfold mixedBarrier
  rw [← Fin.succ_castSucc, Q.move_right, Q.move_middle]

theorem ClosedPartition.move_mixedCell_other (Q : ClosedPartition (n + 1))
    (W : CellWeight) (kind : Fin (n + 1) → CellKind) (i : Fin n) (c : ℝ)
    (hc : c ∈ Icc (Q.point i.castSucc.castSucc) (Q.point i.succ.succ))
    (k : Fin (n + 1)) (hl : k ≠ i.castSucc) (hr : k ≠ i.succ) :
    (Q.move i c hc).width k = Q.width k ∧
      (Q.move i c hc).mixedBarrier W kind k = Q.mixedBarrier W kind k := by
  have h₀ : k.castSucc ≠ i.castSucc.succ := by
    intro he
    apply hr
    apply Fin.ext
    have hv := congrArg Fin.val he
    exact hv
  have h₁ : k.succ ≠ i.castSucc.succ := fun he => hl (Fin.succ_injective _ he)
  unfold ClosedPartition.width mixedBarrier
  rw [Q.move_other i c hc _ h₀, Q.move_other i c hc _ h₁]
  exact ⟨rfl, rfl⟩

end TimeTraps.Interval
