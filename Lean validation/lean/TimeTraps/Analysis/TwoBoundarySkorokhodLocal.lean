module

public import TimeTraps.Analysis.ContinuousBoundaryComparison

@[expose] public section

/-! Deterministic two-boundary path uniqueness from continuous regulators
that are locally constant away from their respective boundary. The common
input cancels in the comparison; no derivatives or stochastic law enter. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped Topology

structure TwoBoundarySkorokhodLocal (L : ℝ) (w X lower upper : ℝ → ℝ) : Prop where
  path_continuous : Continuous X
  lower_continuous : Continuous lower
  upper_continuous : Continuous upper
  lower_monotone : Monotone lower
  upper_monotone : Monotone upper
  lower_zero : lower 0 = 0
  upper_zero : upper 0 = 0
  confined : ∀ t : ℝ, 0 ≤ t → X t ∈ Icc 0 L
  equation : ∀ t : ℝ, 0 ≤ t → X t = w t + lower t - upper t
  lower_local : ∀ t : ℝ, 0 < t → X t ≠ 0 → ∀ᶠ s in 𝓝 t, lower s = lower t
  upper_local : ∀ t : ℝ, 0 < t → X t ≠ L → ∀ᶠ s in 𝓝 t, upper s = upper t

theorem twoBoundarySkorokhodLocal_comparison {L : ℝ} {w X₁ X₂ lower₁ lower₂ upper₁ upper₂ : ℝ → ℝ}
    (h₁ : TwoBoundarySkorokhodLocal L w X₁ lower₁ upper₁)
    (h₂ : TwoBoundarySkorokhodLocal L w X₂ lower₂ upper₂) :
    ∀ t : ℝ, 0 ≤ t → X₁ t ≤ X₂ t := by
  have hz : X₁ 0 - X₂ 0 ≤ 0 := by
    have he₁ := h₁.equation 0 le_rfl
    have he₂ := h₂.equation 0 le_rfl
    rw [h₁.lower_zero, h₁.upper_zero] at he₁
    rw [h₂.lower_zero, h₂.upper_zero] at he₂
    linarith
  have hnonpos : ∀ t : ℝ, 0 ≤ t → X₁ t - X₂ t ≤ 0 := by
    apply continuous_nonpos_of_positive_interval_nonincrease
      (h₁.path_continuous.sub h₂.path_continuous) hz
    intro a b ha hab hp
    change X₁ b - X₂ b ≤ X₁ a - X₂ a
    have hl : lower₁ b = lower₁ a := by
      apply continuous_eq_endpoints_of_locally_constant_Ioo h₁.lower_continuous hab
      intro t ht
      have htpos : 0 < t := ha.trans_lt ht.1
      apply h₁.lower_local t htpos
      intro he
      have hd := hp t ht
      have hb := (h₂.confined t htpos.le).1
      change 0 < X₁ t - X₂ t at hd
      rw [he] at hd
      linarith
    have hu : upper₂ b = upper₂ a := by
      apply continuous_eq_endpoints_of_locally_constant_Ioo h₂.upper_continuous hab
      intro t ht
      have htpos : 0 < t := ha.trans_lt ht.1
      apply h₂.upper_local t htpos
      intro he
      have hd := hp t ht
      have hb := (h₁.confined t htpos.le).2
      change 0 < X₁ t - X₂ t at hd
      rw [he] at hd
      linarith
    have hb : 0 ≤ b := ha.trans hab.le
    have he₁a := h₁.equation a ha
    have he₂a := h₂.equation a ha
    have he₁b := h₁.equation b hb
    have he₂b := h₂.equation b hb
    have hm₁ := h₁.upper_monotone hab.le
    have hm₂ := h₂.lower_monotone hab.le
    linarith
  intro t ht
  exact sub_nonpos.mp (hnonpos t ht)

theorem twoBoundarySkorokhodLocal_unique {L : ℝ} {w X₁ X₂ lower₁ lower₂ upper₁ upper₂ : ℝ → ℝ}
    (h₁ : TwoBoundarySkorokhodLocal L w X₁ lower₁ upper₁)
    (h₂ : TwoBoundarySkorokhodLocal L w X₂ lower₂ upper₂) : EqOn X₁ X₂ (Ici 0) := by
  intro t ht
  exact le_antisymm (twoBoundarySkorokhodLocal_comparison h₁ h₂ t ht)
    (twoBoundarySkorokhodLocal_comparison h₂ h₁ t ht)

end TimeTraps.Analysis
