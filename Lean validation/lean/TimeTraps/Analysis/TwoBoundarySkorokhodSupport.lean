module

public import TimeTraps.Analysis.TwoBoundarySkorokhodLocal
public import TimeTraps.Analysis.StieltjesLocalSupport

@[expose] public section

/-! Stieltjes boundary support implies the local constancy needed for
deterministic two-boundary path uniqueness. The measure is the actual
Stieltjes measure of each regulator, not an independently assumed support
surrogate. The conclusion is uniqueness of the confined path. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology ENNReal

theorem stieltjes_locally_constant_of_notMem_support (f : StieltjesFunction ℝ) (t : ℝ)
    (ht : t ∉ f.measure.support) : ∀ᶠ s in 𝓝 t, f s = f t := by
  obtain ⟨U, hU, hzero⟩ := Measure.notMem_support_iff_exists.mp ht
  obtain ⟨a, b, htmem, hN, hsub⟩ := exists_Icc_mem_subset_of_mem_nhds hU
  have hm : f.measure (Ioc a b) = 0 :=
    measure_mono_null (Ioc_subset_Icc_self.trans hsub) hzero
  rw [StieltjesFunction.measure_Ioc] at hm
  have hba : f b ≤ f a := sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hm)
  have he : ∀ s ∈ Icc a b, f s = f a := fun s hs =>
    le_antisymm ((f.mono hs.2).trans hba) (f.mono hs.1)
  filter_upwards [hN] with s hs
  exact (he s hs).trans (he t htmem).symm

structure TwoBoundarySkorokhodStieltjes (L : ℝ) (w X : ℝ → ℝ)
    (lower upper : StieltjesFunction ℝ) : Prop where
  path_continuous : Continuous X
  lower_continuous : Continuous (fun t => lower t)
  upper_continuous : Continuous (fun t => upper t)
  lower_zero : lower 0 = 0
  upper_zero : upper 0 = 0
  confined : ∀ t : ℝ, 0 ≤ t → X t ∈ Icc 0 L
  equation : ∀ t : ℝ, 0 ≤ t → X t = w t + lower t - upper t
  lower_support : lower.measure.support ⊆ {t : ℝ | 0 ≤ t ∧ X t = 0}
  upper_support : upper.measure.support ⊆ {t : ℝ | 0 ≤ t ∧ X t = L}

theorem twoBoundarySkorokhodStieltjes_toLocal {L : ℝ} {w X : ℝ → ℝ}
    {lower upper : StieltjesFunction ℝ} (h : TwoBoundarySkorokhodStieltjes L w X lower upper) :
    TwoBoundarySkorokhodLocal L w X (fun t => lower t) (fun t => upper t) := by
  refine ⟨h.path_continuous, h.lower_continuous, h.upper_continuous, lower.mono, upper.mono,
    h.lower_zero, h.upper_zero, h.confined, h.equation, ?_, ?_⟩
  · intro t _ hne
    exact stieltjes_locally_constant_of_notMem_support lower t
      (fun ht => hne (h.lower_support ht).2)
  · intro t _ hne
    exact stieltjes_locally_constant_of_notMem_support upper t
      (fun ht => hne (h.upper_support ht).2)

theorem twoBoundarySkorokhodStieltjes_unique {L : ℝ} {w X₁ X₂ : ℝ → ℝ}
    {lower₁ lower₂ upper₁ upper₂ : StieltjesFunction ℝ}
    (h₁ : TwoBoundarySkorokhodStieltjes L w X₁ lower₁ upper₁)
    (h₂ : TwoBoundarySkorokhodStieltjes L w X₂ lower₂ upper₂) : EqOn X₁ X₂ (Ici 0) :=
  twoBoundarySkorokhodLocal_unique (twoBoundarySkorokhodStieltjes_toLocal h₁)
    (twoBoundarySkorokhodStieltjes_toLocal h₂)

end TimeTraps.Analysis
