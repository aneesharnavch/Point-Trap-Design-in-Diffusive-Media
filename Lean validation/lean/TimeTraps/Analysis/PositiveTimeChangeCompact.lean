module

public import TimeTraps.Analysis.PositiveTimeChangeInverse
public import Mathlib.Topology.Order.Compact

@[expose] public section

/-! A positive continuous spatial speed on a nonempty compact space
supplies attained uniform bounds for every continuous path in that space.
The resulting clock is the integral of the original composed speed. -/

namespace TimeTraps.Analysis

open Set
open scoped NNReal

variable {α : Type*} [TopologicalSpace α] [CompactSpace α] [Nonempty α]

noncomputable def PositiveTimeSpeed.ofCompact (c : α → ℝ) (hc : Continuous c)
    (hpos : ∀ y, 0 < c y) (Y : ℝ≥0 → α) (hY : Continuous Y) : PositiveTimeSpeed :=
  let hmin := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  let hmax := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  { rate := fun s => c (Y s)
    continuous_rate := hc.comp hY
    lower := ⟨c (Classical.choose hmin), (hpos _).le⟩
    upper := ⟨c (Classical.choose hmax), (hpos _).le⟩
    lower_pos := hpos _
    lower_le := fun s => (Classical.choose_spec hmin).2 (mem_univ (Y s))
    le_upper := fun s => (Classical.choose_spec hmax).2 (mem_univ (Y s)) }

theorem PositiveTimeSpeed.ofCompact_rate (c : α → ℝ) (hc : Continuous c)
    (hpos : ∀ y, 0 < c y) (Y : ℝ≥0 → α) (hY : Continuous Y) (s : ℝ≥0) :
    (PositiveTimeSpeed.ofCompact c hc hpos Y hY).rate s = c (Y s) := rfl

theorem PositiveTimeSpeed.ofCompact_lower_minimum (c : α → ℝ) (hc : Continuous c)
    (hpos : ∀ y, 0 < c y) (Y : ℝ≥0 → α) (hY : Continuous Y) :
    ∃ y : α, c y = ((PositiveTimeSpeed.ofCompact c hc hpos Y hY).lower : ℝ) ∧
      ∀ z : α, c y ≤ c z := by
  let hm := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  exact ⟨Classical.choose hm, rfl, fun z => (Classical.choose_spec hm).2 (mem_univ z)⟩

theorem PositiveTimeSpeed.ofCompact_upper_maximum (c : α → ℝ) (hc : Continuous c)
    (hpos : ∀ y, 0 < c y) (Y : ℝ≥0 → α) (hY : Continuous Y) :
    ∃ y : α, c y = ((PositiveTimeSpeed.ofCompact c hc hpos Y hY).upper : ℝ) ∧
      ∀ z : α, c z ≤ c y := by
  let hm := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  exact ⟨Classical.choose hm, rfl, fun z => (Classical.choose_spec hm).2 (mem_univ z)⟩

theorem PositiveTimeSpeed.ofCompact_clock_coe (c : α → ℝ) (hc : Continuous c)
    (hpos : ∀ y, 0 < c y) (Y : ℝ≥0 → α) (hY : Continuous Y) (s : ℝ≥0) :
    ((PositiveTimeSpeed.ofCompact c hc hpos Y hY).clock s : ℝ) =
      ∫ r in (0 : ℝ)..s.val, c (Y r.toNNReal) := rfl

end TimeTraps.Analysis
