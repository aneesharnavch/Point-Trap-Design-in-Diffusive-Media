module

public import TimeTraps.Interval.WeakConsequences

@[expose] public section

/-!
An independent strict partition of normalized source mass. Its widths and
balanced centers are input to construction, not inferred from a chosen state.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped BigOperators

structure StrictPartition (n : ℕ) where
  point : Fin (n + 1) → ℝ
  strictMono : StrictMono point
  first : point 0 = 0
  last : point (Fin.last n) = 1

variable {n : ℕ}

theorem StrictPartition.size_pos (Q : StrictPartition n) : 0 < n := by
  cases n with
  | zero =>
    have h : (0 : ℝ) = 1 := Q.first.symm.trans Q.last
    norm_num at h
  | succ n => omega

theorem StrictPartition.point_mem (Q : StrictPartition n) (e : Fin (n + 1)) :
    Q.point e ∈ Icc 0 1 := by
  rw [← Q.first, ← Q.last]
  exact ⟨Q.strictMono.monotone (Fin.zero_le e), Q.strictMono.monotone (Fin.le_last e)⟩

def StrictPartition.width (Q : StrictPartition n) (i : Fin n) : ℝ :=
  Q.point i.succ - Q.point i.castSucc

theorem StrictPartition.width_pos (Q : StrictPartition n) (i : Fin n) : 0 < Q.width i :=
  sub_pos.mpr (Q.strictMono Fin.castSucc_lt_succ)

theorem StrictPartition.width_sum (Q : StrictPartition n) : (∑ i, Q.width i) = 1 := by
  unfold StrictPartition.width
  rw [Finset.sum_sub_distrib]
  have h₀ := Fin.sum_univ_succ Q.point
  have h₁ := Fin.sum_univ_castSucc Q.point
  rw [Q.first] at h₀
  rw [Q.last] at h₁
  linarith

theorem StrictPartition.prefix_width (Q : StrictPartition n) (e : Fin (n + 1)) :
    absorptionPrefix Q.width e = Q.point e := by
  induction e using Fin.induction with
  | zero => rw [absorptionPrefix_zero, Q.first]
  | succ i ih =>
    rw [absorptionPrefix_succ, ih]
    unfold StrictPartition.width
    ring

noncomputable def StrictPartition.center (Q : StrictPartition n) (W : CellWeight) (i : Fin n) : ℝ :=
  W.center (Q.point i.castSucc) (Q.point i.succ)

noncomputable def StrictPartition.barrier (Q : StrictPartition n) (W : CellWeight) (i : Fin n) : ℝ :=
  W.barrier (Q.point i.castSucc) (Q.point i.succ)

theorem StrictPartition.center_mem (Q : StrictPartition n) (W : CellWeight) (i : Fin n) :
    Q.center W i ∈ Ioo (Q.point i.castSucc) (Q.point i.succ) :=
  (W.center_spec (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.strictMono Fin.castSucc_lt_succ)).1

theorem StrictPartition.center_interior (Q : StrictPartition n) (W : CellWeight) (i : Fin n) :
    Q.center W i ∈ Ioo (0 : ℝ) 1 :=
  ⟨(Q.point_mem i.castSucc).1.trans_lt (Q.center_mem W i).1,
    (Q.center_mem W i).2.trans_le (Q.point_mem i.succ).2⟩

theorem StrictPartition.center_strictMono (Q : StrictPartition n) (W : CellWeight) :
    StrictMono (Q.center W) := by
  intro i j hij
  have hi : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
  exact ((Q.center_mem W i).2.trans_le (Q.strictMono.monotone hi)).trans (Q.center_mem W j).1

theorem StrictPartition.balance (Q : StrictPartition n) (W : CellWeight) (i : Fin n) :
    W.leftRise (Q.point i.castSucc) (Q.center W i) =
      W.rightRise (Q.point i.succ) (Q.center W i) :=
  (W.center_spec (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.strictMono Fin.castSucc_lt_succ)).2

theorem StrictPartition.barrier_pos (Q : StrictPartition n) (W : CellWeight) (i : Fin n) :
    0 < Q.barrier W i :=
  W.barrier_pos (Q.point_mem i.castSucc).1 (Q.point_mem i.succ).2
    (Q.strictMono Fin.castSucc_lt_succ)

theorem StrictPartition.cover (Q : StrictPartition n) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    ∃ i : Fin n, z ∈ Icc (Q.point i.castSucc) (Q.point i.succ) := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 Q.size_pos).elim
  | succ m =>
    have hc : ∀ e : Fin (m + 1), ∀ y ∈ Icc (Q.point 0) (Q.point e.succ),
        ∃ i : Fin (m + 1), y ∈ Icc (Q.point i.castSucc) (Q.point i.succ) := by
      intro e
      induction e using Fin.induction with
      | zero => intro y hy; exact ⟨0, hy⟩
      | succ i ih =>
        intro y hy
        by_cases hb : y ≤ Q.point i.castSucc.succ
        · exact ih y ⟨hy.1, hb⟩
        · exact ⟨i.succ, ⟨(lt_of_not_ge hb).le, hy.2⟩⟩
    apply hc (Fin.last m) z
    change z ∈ Icc (Q.point 0) (Q.point (Fin.last (m + 1)))
    simpa only [Q.first, Q.last] using hz

/-- The medium is fixed before any sites or reaction strengths are chosen. -/
structure IntervalMedium where
  source : SourceInterval
  conductance : ℝ → ℝ
  conductance_continuous : ContinuousOn conductance (Icc source.left source.right)
  conductance_pos : ∀ x ∈ Icc source.left source.right, 0 < conductance x

def OrderedMedium.medium (D : OrderedMedium n) : IntervalMedium :=
  ⟨D.source, D.conductance, D.conductance_continuous, D.conductance_pos⟩

noncomputable def IntervalMedium.cellWeight (A : IntervalMedium) : CellWeight :=
  CellWeight.ofSource A.source A.conductance A.conductance_continuous A.conductance_pos

noncomputable def IntervalMedium.partitionSites (A : IntervalMedium) (Q : StrictPartition n)
    (i : Fin n) : ℝ := A.source.inverse (Q.center A.cellWeight i)

theorem IntervalMedium.partitionSites_interior (A : IntervalMedium) (Q : StrictPartition n) (i : Fin n) :
    A.partitionSites Q i ∈ Ioo A.source.left A.source.right := by
  have hc := Q.center_interior A.cellWeight i
  constructor
  · rw [← A.source.inverse_zero]
    exact A.source.inverse_strictMono ⟨le_rfl, zero_le_one⟩ (Ioo_subset_Icc_self hc) hc.1
  · rw [← A.source.inverse_one]
    exact A.source.inverse_strictMono (Ioo_subset_Icc_self hc) ⟨zero_le_one, le_rfl⟩ hc.2

theorem IntervalMedium.partitionSites_strictMono (A : IntervalMedium) (Q : StrictPartition n) :
    StrictMono (A.partitionSites Q) := by
  intro i j hij
  exact A.source.inverse_strictMono (Ioo_subset_Icc_self (Q.center_interior A.cellWeight i))
    (Ioo_subset_Icc_self (Q.center_interior A.cellWeight j)) (Q.center_strictMono A.cellWeight hij)

noncomputable def IntervalMedium.partitionDesign (A : IntervalMedium) (Q : StrictPartition n) :
    OrderedMedium n :=
  OrderedMedium.ofSites A.source A.conductance A.conductance_continuous A.conductance_pos
    (A.partitionSites Q) (A.partitionSites_strictMono Q) (A.partitionSites_interior Q)

theorem IntervalMedium.partitionDesign_site (A : IntervalMedium) (Q : StrictPartition n) (i : Fin n) :
    (A.partitionDesign Q).site i = A.partitionSites Q i :=
  OrderedMedium.ofSites_site _ _ _ _ _ _ _ i

theorem IntervalMedium.partitionDesign_sourceSite (A : IntervalMedium) (Q : StrictPartition n) (i : Fin n) :
    (A.partitionDesign Q).sourceSite i = Q.center A.cellWeight i := by
  change A.source.coordinate ((A.partitionDesign Q).site i) = _
  rw [A.partitionDesign_site]
  exact A.source.coordinate_inverse (Ioo_subset_Icc_self (Q.center_interior A.cellWeight i))

end TimeTraps.Interval
