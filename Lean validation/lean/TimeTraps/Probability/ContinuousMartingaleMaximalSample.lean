module

public import TimeTraps.Probability.ContinuousMartingaleMaximalFinite

@[expose] public section

/-! Every finite prefix of an arbitrary countable observation schedule
obeys the same terminal-time Doob bound. The schedule need not be sorted. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {M : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}

theorem martingaleSampleMax_memLp (hM2 : ∀ t, MemLp (M t) 2 μ)
    (τ : ℕ → ℝ≥0) (n : ℕ) :
    MemLp (fun ω => finiteRunningMax (fun k => |M (τ k) ω|) n) 2 μ := by
  apply finiteRunningMax_memLp
  intro k
  simpa only [Real.norm_eq_abs] using (hM2 (τ k)).norm

theorem martingaleSampleMax_second_moment [IsFiniteMeasure μ] (hM : Martingale M 𝓕 μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) (τ : ℕ → ℝ≥0) (T : ℝ≥0) (hT : ∀ k, τ k ≤ T) (n : ℕ) :
    (∫ ω, finiteRunningMax (fun k => |M (τ k) ω|) n ^ 2 ∂μ) ≤ 4 * ∫ ω, M T ω ^ 2 ∂μ := by
  classical
  let s := insert T ((Finset.range (n + 1)).image τ)
  have hs : s.Nonempty := ⟨T, Finset.mem_insert_self _ _⟩
  have hsT : ∀ t ∈ s, t ≤ T := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact le_rfl
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
      exact hT k
  have hle (ω : Ω) : finiteRunningMax (fun k => |M (τ k) ω|) n ≤ martingaleFiniteMax M s hs ω := by
    apply (finiteRunningMax_le_iff _ n _).mpr
    intro k hk
    apply Finset.le_sup' (fun t => |M t ω|)
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)
  have hsq (ω : Ω) : finiteRunningMax (fun k => |M (τ k) ω|) n ^ 2 ≤
      martingaleFiniteMax M s hs ω ^ 2 := by
    have h0 := finiteRunningMax_nonneg (fun k => |M (τ k) ω|) (abs_nonneg _) n
    exact (sq_le_sq₀ h0 (h0.trans (hle ω))).mpr (hle ω)
  exact (integral_mono (martingaleSampleMax_memLp hM2 τ n).integrable_sq
    (martingaleFiniteMax_memLp hM2 s hs).integrable_sq hsq).trans
      (martingaleFiniteMax_second_moment hM hM2 s hs T (Finset.mem_insert_self _ _) hsT)

end TimeTraps.Probability
