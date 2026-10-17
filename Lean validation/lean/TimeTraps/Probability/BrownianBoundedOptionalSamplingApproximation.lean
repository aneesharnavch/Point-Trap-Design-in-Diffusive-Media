module

public import TimeTraps.Probability.BrownianCompletedMartingaleRightContinuous
public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Countable upper-grid approximations of finite nonnegative stopping
times. Their stopping property is proved from a countable union of
earlier stopping events; no countable-range premise is imposed on the
original stopping time. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def boundedStoppingUpperGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (⌈t * ((n : ℝ≥0) + 1)⌉₊ : ℝ≥0) / ((n : ℝ≥0) + 1)

theorem boundedStoppingUpperGrid_bounds (n : ℕ) (t : ℝ≥0) :
    t ≤ boundedStoppingUpperGrid n t ∧
      boundedStoppingUpperGrid n t ≤ t + 1 / ((n : ℝ≥0) + 1) := by
  have hd : 0 < (n : ℝ≥0) + 1 := by positivity
  constructor
  · exact (le_div_iff₀ hd).mpr (Nat.le_ceil _)
  · calc
      _ ≤ (t * ((n : ℝ≥0) + 1) + 1) / ((n : ℝ≥0) + 1) :=
        div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le (le_of_lt hd)
      _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hd.ne']

theorem boundedStoppingUpperGrid_le_grid (n k : ℕ) {t : ℝ≥0}
    (ht : t ≤ (k : ℝ≥0) / ((n : ℝ≥0) + 1)) :
    boundedStoppingUpperGrid n t ≤ (k : ℝ≥0) / ((n : ℝ≥0) + 1) := by
  have hd : 0 < (n : ℝ≥0) + 1 := by positivity
  apply (div_le_div_iff_of_pos_right hd).mpr
  exact_mod_cast (Nat.ceil_le.mpr ((le_div_iff₀ hd).mp ht))

theorem boundedStoppingUpperGrid_tendsto (t : ℝ≥0) :
    Tendsto (fun n => boundedStoppingUpperGrid n t) atTop (𝓝 t) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n : ℕ => t + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 t) by
      simpa only [add_zero] using (tendsto_const_nhds (x := t)).add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0)))
  · exact fun n => (boundedStoppingUpperGrid_bounds n t).1
  · exact fun n => (boundedStoppingUpperGrid_bounds n t).2

theorem boundedStoppingUpperGrid_countable_range {Ω : Type*} (τ : Ω → ℝ≥0) (n : ℕ) :
    (range (fun ω => (boundedStoppingUpperGrid n (τ ω) : WithTop ℝ≥0))).Countable := by
  apply (countable_range (fun k : ℕ => ((k : ℝ≥0) / ((n : ℝ≥0) + 1) : WithTop ℝ≥0))).mono
  rintro _ ⟨ω, rfl⟩
  exact ⟨⌈τ ω * ((n : ℝ≥0) + 1)⌉₊, rfl⟩

theorem boundedStoppingUpperGrid_isStoppingTime {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0))) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (boundedStoppingUpperGrid n (τ ω) : WithTop ℝ≥0)) := by
  intro s
  have he : {ω | (boundedStoppingUpperGrid n (τ ω) : WithTop ℝ≥0) ≤ s} =
      ⋃ k : ℕ, ⋃ (_ : (k : ℝ≥0) / ((n : ℝ≥0) + 1) ≤ s),
        {ω | (τ ω : WithTop ℝ≥0) ≤ ((k : ℝ≥0) / ((n : ℝ≥0) + 1) : ℝ≥0)} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_iUnion]
    constructor
    · intro hs
      exact ⟨⌈τ ω * ((n : ℝ≥0) + 1)⌉₊, hs, (boundedStoppingUpperGrid_bounds n (τ ω)).1⟩
    · rintro ⟨k, hk, hτk⟩
      exact (boundedStoppingUpperGrid_le_grid n k hτk).trans hk
  rw [he]
  exact MeasurableSet.iUnion (fun k => MeasurableSet.iUnion
    (fun hk => ℱ.mono hk _ (hτ ((k : ℝ≥0) / ((n : ℝ≥0) + 1)))))

theorem boundedStoppingUpperGrid_le_bound {Ω : Type*} {τ : Ω → ℝ≥0} {T : ℝ≥0}
    (hτ : ∀ ω, τ ω ≤ T) (n : ℕ) (ω : Ω) : boundedStoppingUpperGrid n (τ ω) ≤ T + 1 := by
  apply (boundedStoppingUpperGrid_bounds n (τ ω)).2.trans
  apply add_le_add (hτ ω)
  have hd : (1 : ℝ≥0) ≤ (n : ℝ≥0) + 1 := le_add_of_nonneg_left bot_le
  simpa only [div_one] using one_div_le_one_div_of_le (zero_lt_one : (0 : ℝ≥0) < 1) hd

end TimeTraps.Probability
