module

public import TimeTraps.Probability.BrownianIntegralMaximalDiscrete
public import TimeTraps.Probability.BrownianIntegralMaximalGrid

@[expose] public section

/-! The proved discrete Doob inequality applies to every real martingale
sampled at an ordered finite grid, with repeated times allowed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {M : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}

def sampledMartingaleFiltration (𝓕 : Filtration ℝ≥0 mΩ)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) : Filtration ℕ mΩ where
  seq k := 𝓕 (brownianIntegralGridTime τ k)
  mono' := fun _ _ hij => 𝓕.mono (brownianIntegralGridTime_monotone hτ hij)
  le' k := 𝓕.le (brownianIntegralGridTime τ k)

theorem sampledMartingale_grid (hM : Martingale M 𝓕 μ)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) :
    Martingale (fun k => M (brownianIntegralGridTime τ k)) (sampledMartingaleFiltration 𝓕 τ hτ) μ :=
  ⟨fun _k => hM.stronglyMeasurable _, fun _ _ hij =>
    hM.condExp_ae_eq (brownianIntegralGridTime_monotone hτ hij)⟩

noncomputable def martingaleGridMax (M : ℝ≥0 → Ω → ℝ)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |M (τ i) ω|)

theorem martingaleGridMax_eq_running {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (ω : Ω) :
    martingaleGridMax M τ ω = finiteRunningMax (fun k => |M (brownianIntegralGridTime τ k) ω|) N := by
  unfold martingaleGridMax
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    have h := le_finiteRunningMax (fun k => |M (brownianIntegralGridTime τ k) ω|)
      (Nat.le_of_lt_succ i.isLt)
    simpa only [brownianIntegralGridTime_at_fin] using h
  · apply (finiteRunningMax_le_iff _ N _).mpr
    intro k hk
    let i : Fin (N + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    rw [show brownianIntegralGridTime τ k = τ i from brownianIntegralGridTime_at_fin τ i]
    exact Finset.le_sup' (fun i => |M (τ i) ω|) (Finset.mem_univ i)

theorem martingaleGridMax_memLp (hM2 : ∀ t, MemLp (M t) 2 μ)
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) : MemLp (martingaleGridMax M τ) 2 μ := by
  have h2 (k : ℕ) : MemLp (fun ω => |M (brownianIntegralGridTime τ k) ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using (hM2 (brownianIntegralGridTime τ k)).norm
  simpa only [← martingaleGridMax_eq_running] using finiteRunningMax_memLp h2 N

theorem martingaleGridMax_second_moment [IsFiniteMeasure μ] (hM : Martingale M 𝓕 μ)
    (hM2 : ∀ t, MemLp (M t) 2 μ) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) :
    (∫ ω, martingaleGridMax M τ ω ^ 2 ∂μ) ≤ 4 * ∫ ω, M (τ (Fin.last N)) ω ^ 2 ∂μ := by
  have h2 (k : ℕ) : MemLp (fun ω => |M (brownianIntegralGridTime τ k) ω|) 2 μ := by
    simpa only [Real.norm_eq_abs] using (hM2 (brownianIntegralGridTime τ k)).norm
  have h := nonnegative_submartingale_maximal_L2
    (martingale_abs_submartingale (sampledMartingale_grid hM τ hτ))
    (fun _ _ => abs_nonneg _) h2 N
  have he : brownianIntegralGridTime τ N = τ (Fin.last N) := brownianIntegralGridTime_at_fin τ (Fin.last N)
  simpa only [← martingaleGridMax_eq_running, he, sq_abs] using h

end TimeTraps.Probability
