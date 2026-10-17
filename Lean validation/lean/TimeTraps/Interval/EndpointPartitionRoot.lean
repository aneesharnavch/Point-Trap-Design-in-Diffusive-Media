module

public import TimeTraps.Interval.EndpointPartition
public import TimeTraps.Interval.BudgetContinuity

@[expose] public section

/-!
The genuine mixed-cell harmonic root for a fixed endpoint architecture.
It remains continuous on the full closed simplex when positive support
changes, and it attains a closed-simplex minimum. No assertion that a
minimizing partition has positive widths is made here.
-/

namespace TimeTraps.Interval

open Set
open scoped BigOperators

theorem EndpointArchitecture.root_existsUnique (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    ∃! M : ℝ, (∀ i, A.barrier Q W i < M) ∧
      budget Finset.univ Q.width (A.barrier Q W) M = b := by
  obtain ⟨i, hi⟩ := Q.positive_width
  simpa only [Finset.mem_univ, forall_const] using
    budget_root_existsUnique_nonneg Finset.univ Q.width (A.barrier Q W)
      (fun i _ => Q.width_nonneg i) ⟨i, Finset.mem_univ i, hi⟩
      (fun i _ => A.barrier_nonneg Q W i)
      (fun i _ => A.barrier_zero_of_width_zero Q W i) hb

noncomputable def EndpointArchitecture.root (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {b : ℝ} (hb : 0 < b) : ℝ :=
  Classical.choose (A.root_existsUnique Q W hb)

theorem EndpointArchitecture.root_spec (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    (∀ i, A.barrier Q W i < A.root Q W hb) ∧
      budget Finset.univ Q.width (A.barrier Q W) (A.root Q W hb) = b :=
  (Classical.choose_spec (A.root_existsUnique Q W hb)).1

theorem EndpointArchitecture.eq_root (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {b M : ℝ} (hb : 0 < b)
    (hM : ∀ i, A.barrier Q W i < M)
    (hroot : budget Finset.univ Q.width (A.barrier Q W) M = b) : M = A.root Q W hb :=
  (Classical.choose_spec (A.root_existsUnique Q W hb)).2 M ⟨hM, hroot⟩

theorem EndpointArchitecture.root_pos (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    0 < A.root Q W hb := by
  obtain ⟨i, _⟩ := Q.positive_width
  exact (A.barrier_nonneg Q W i).trans_lt ((A.root_spec Q W hb).1 i)

theorem EndpointArchitecture.root_lower (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    1 / b ≤ A.root Q W hb := by
  obtain ⟨i, hi⟩ := Q.positive_width
  have h := budget_root_lower_nonneg Finset.univ Q.width (A.barrier Q W)
    (fun i _ => Q.width_nonneg i) ⟨i, Finset.mem_univ i, hi⟩
    (fun i _ => A.barrier_nonneg Q W i) hb
    (fun i _ => (A.root_spec Q W hb).1 i) (A.root_spec Q W hb).2
  simpa only [Q.width_sum] using h

theorem EndpointArchitecture.root_upper (A : EndpointArchitecture)
    (Q : ClosedPartition A.count) (W : CellWeight) {b Rmax : ℝ} (hb : 0 < b)
    (hR : ∀ i, A.barrier Q W i ≤ Rmax) :
    A.root Q W hb ≤ Rmax + 1 / b := by
  obtain ⟨i, hi⟩ := Q.positive_width
  have h := budget_root_upper_nonneg Finset.univ Q.width (A.barrier Q W)
    (fun i _ => Q.width_nonneg i) ⟨i, Finset.mem_univ i, hi⟩ hb
    (fun i _ => hR i) (A.root_spec Q W hb).2
  simpa only [Q.width_sum] using h

theorem EndpointArchitecture.root_continuous (A : EndpointArchitecture)
    (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    Continuous (fun Q : ClosedPartition A.count => A.root Q W hb) := by
  apply continuous_iff_continuousAt.mpr
  intro Q
  have hpos : ∀ P : ClosedPartition A.count, ∃ i ∈ Finset.univ, 0 < P.width i := by
    intro P
    obtain ⟨i, hi⟩ := P.positive_width
    exact ⟨i, Finset.mem_univ i, hi⟩
  exact budget_root_continuousAt Finset.univ (fun P : ClosedPartition A.count => P.width)
    (fun P => A.barrier P W) (fun P => A.root P W hb)
    (fun P i _ => P.width_nonneg i) hpos
    (fun P i _ => (A.root_spec P W hb).1 i) (fun P => (A.root_spec P W hb).2)
    (fun i _ => (ClosedPartition.width_continuous i).continuousAt)
    (fun i _ => (A.barrier_continuous W i).continuousAt)

theorem EndpointArchitecture.minimum_exists (A : EndpointArchitecture)
    (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    ∃ Q : ClosedPartition A.count, ∀ P : ClosedPartition A.count,
      A.root Q W hb ≤ A.root P W hb := by
  obtain ⟨Q, _, hQ⟩ := isCompact_univ.exists_isMinOn
    (show (Set.univ : Set (ClosedPartition A.count)).Nonempty from
      ⟨(StrictPartition.uniform A.count A.count_pos).closed, mem_univ _⟩)
    (A.root_continuous W hb).continuousOn
  exact ⟨Q, fun P => hQ (mem_univ P)⟩

theorem EndpointArchitecture.minimum_isLeast (A : EndpointArchitecture)
    (W : CellWeight) {b : ℝ} (hb : 0 < b) :
    ∃ Q : ClosedPartition A.count,
      IsLeast (range (fun P : ClosedPartition A.count => A.root P W hb)) (A.root Q W hb) := by
  obtain ⟨Q, hQ⟩ := A.minimum_exists W hb
  refine ⟨Q, ⟨Q, rfl⟩, ?_⟩
  rintro M ⟨P, rfl⟩
  exact hQ P

end TimeTraps.Interval
