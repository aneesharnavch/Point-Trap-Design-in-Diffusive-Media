module

public import TimeTraps.Analysis.TwoBoundarySkorokhodSupport

@[expose] public section

/-! Both regulators are uniquely determined by the common input when
the two reflecting boundaries are distinct. Once the confined paths
agree, the lower and upper regulator differences coincide. This common
difference is locally constant at every positive time and starts at zero.
No differentiation or stochastic assumption is used. -/

namespace TimeTraps.Analysis

open Set Filter
open scoped Topology

theorem twoBoundarySkorokhodLocal_regulators_unique {L : ℝ} (hL : 0 < L)
    {w X₁ X₂ lower₁ lower₂ upper₁ upper₂ : ℝ → ℝ}
    (h₁ : TwoBoundarySkorokhodLocal L w X₁ lower₁ upper₁)
    (h₂ : TwoBoundarySkorokhodLocal L w X₂ lower₂ upper₂) :
    EqOn lower₁ lower₂ (Ici 0) ∧ EqOn upper₁ upper₂ (Ici 0) := by
  have hX := twoBoundarySkorokhodLocal_unique h₁ h₂
  have hd : ∀ t : ℝ, 0 ≤ t → lower₁ t - lower₂ t = upper₁ t - upper₂ t := by
    intro t ht
    have hx := hX ht
    have he₁ := h₁.equation t ht
    have he₂ := h₂.equation t ht
    linarith
  have hlocal : ∀ t : ℝ, 0 < t →
      ∀ᶠ s in 𝓝 t, lower₁ s - lower₂ s = lower₁ t - lower₂ t := by
    intro t ht
    by_cases hz : X₁ t = 0
    · have hn₁ : X₁ t ≠ L := by rw [hz]; exact ne_of_lt hL
      have hn₂ : X₂ t ≠ L := by rw [← hX ht.le]; exact hn₁
      filter_upwards [h₁.upper_local t ht hn₁, h₂.upper_local t ht hn₂,
        Ioi_mem_nhds ht] with s hs₁ hs₂ hs
      rw [hd s hs.le, hd t ht.le, hs₁, hs₂]
    · have hn₂ : X₂ t ≠ 0 := by rw [← hX ht.le]; exact hz
      filter_upwards [h₁.lower_local t ht hz, h₂.lower_local t ht hn₂] with s hs₁ hs₂
      rw [hs₁, hs₂]
  have hl : EqOn lower₁ lower₂ (Ici 0) := by
    intro t ht
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ t from ht) with he | hp
    · rw [← he, h₁.lower_zero, h₂.lower_zero]
    · have he := continuous_eq_endpoints_of_locally_constant_Ioo
        (h₁.lower_continuous.sub h₂.lower_continuous) hp
        (fun s hs => hlocal s hs.1)
      change lower₁ t - lower₂ t = lower₁ 0 - lower₂ 0 at he
      rw [h₁.lower_zero, h₂.lower_zero, sub_self] at he
      exact sub_eq_zero.mp he
  refine ⟨hl, ?_⟩
  intro t ht
  have he := hd t ht
  rw [hl ht, sub_self] at he
  exact sub_eq_zero.mp he.symm

theorem twoBoundarySkorokhodStieltjes_unique_all {L : ℝ} (hL : 0 < L)
    {w X₁ X₂ : ℝ → ℝ} {lower₁ lower₂ upper₁ upper₂ : StieltjesFunction ℝ}
    (h₁ : TwoBoundarySkorokhodStieltjes L w X₁ lower₁ upper₁)
    (h₂ : TwoBoundarySkorokhodStieltjes L w X₂ lower₂ upper₂) :
    EqOn X₁ X₂ (Ici 0) ∧ EqOn (fun t => lower₁ t) (fun t => lower₂ t) (Ici 0) ∧
      EqOn (fun t => upper₁ t) (fun t => upper₂ t) (Ici 0) :=
  ⟨twoBoundarySkorokhodStieltjes_unique h₁ h₂,
    twoBoundarySkorokhodLocal_regulators_unique hL
      (twoBoundarySkorokhodStieltjes_toLocal h₁) (twoBoundarySkorokhodStieltjes_toLocal h₂)⟩

end TimeTraps.Analysis
