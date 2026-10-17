module

public import TimeTraps.Interval.ClosedBudget
public import Mathlib.Order.Filter.Finite

@[expose] public section

/-!
Continuity of the genuine scalar root when positive support may change.
Fixed heights on either side of the root give strict budget inequalities;
continuity preserves these inequalities and traps all nearby roots between
the heights. No continuity of the root is assumed.
-/

namespace TimeTraps.Interval

open Filter
open scoped Topology BigOperators

variable {ι α : Type*} [TopologicalSpace α]

theorem budget_parameters_continuousAt (s : Finset ι) (p R : α → ι → ℝ)
    {x : α} {M : ℝ} (hp : ∀ i ∈ s, ContinuousAt (fun y => p y i) x)
    (hR : ∀ i ∈ s, ContinuousAt (fun y => R y i) x)
    (hM : ∀ i ∈ s, R x i < M) :
    ContinuousAt (fun y => budget s (p y) (R y) M) x := by
  apply tendsto_finsetSum
  intro i hi
  exact (hp i hi).div (continuousAt_const.sub (hR i hi))
    (ne_of_gt (sub_pos.mpr (hM i hi)))

/-- Finite nonnegative weights with at least one positive weight have a
continuous root whenever their weights and barriers vary continuously. -/
theorem budget_root_continuousAt (s : Finset ι) (p R : α → ι → ℝ) (T : α → ℝ)
    (hp : ∀ x, ∀ i ∈ s, 0 ≤ p x i) (hpos : ∀ x, ∃ i ∈ s, 0 < p x i)
    {b : ℝ} (hT : ∀ x, ∀ i ∈ s, R x i < T x)
    (hroot : ∀ x, budget s (p x) (R x) (T x) = b)
    {x : α} (hpc : ∀ i ∈ s, ContinuousAt (fun y => p y i) x)
    (hRc : ∀ i ∈ s, ContinuousAt (fun y => R y i) x) : ContinuousAt T x := by
  obtain ⟨i, hi, _⟩ := hpos x
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (R x) ⟨i, hi⟩
  apply tendsto_order.mpr
  constructor
  · intro l hl
    obtain ⟨c, hlc, hcT⟩ := exists_between (max_lt hl (hT x j hj))
    have hcR : ∀ k ∈ s, R x k < c := fun k hk =>
      (hmax k hk).trans_lt ((le_max_right l (R x j)).trans_lt hlc)
    have hb := budget_strict_decreasing_nonneg s (p x) (R x) (hp x) (hpos x) hcR hcT
    rw [hroot x] at hb
    have he := Filter.Tendsto.eventually_const_lt hb
      (budget_parameters_continuousAt s p R hpc hRc hcR)
    filter_upwards [he] with y hy
    exact ((le_max_left l (R x j)).trans_lt hlc).trans
      (lt_root_of_lt_budget_nonneg s (p y) (R y) (hp y) (hpos y) (hT y) (hroot y) hy)
  · intro u hu
    obtain ⟨c, hTc, hcu⟩ := exists_between hu
    have hcR : ∀ k ∈ s, R x k < c := fun k hk => (hT x k hk).trans hTc
    have hb := budget_strict_decreasing_nonneg s (p x) (R x) (hp x) (hpos x) (hT x) hTc
    rw [hroot x] at hb
    have he := Filter.Tendsto.eventually_lt_const hb
      (budget_parameters_continuousAt s p R hpc hRc hcR)
    have hd : ∀ᶠ y in 𝓝 x, ∀ k ∈ s, R y k < c :=
      s.eventually_all.mpr (fun k hk => Filter.Tendsto.eventually_lt_const (hcR k hk) (hRc k hk))
    filter_upwards [he, hd] with y hy hyd
    exact (root_lt_of_budget_lt_nonneg s (p y) (R y) (hp y) (hpos y) hyd (hroot y) hy).trans hcu

end TimeTraps.Interval
