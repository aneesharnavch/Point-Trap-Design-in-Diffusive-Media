module

public import TimeTraps.Probability.BrownianIntegralMaximalPathwise

@[expose] public section

/-! Sampling the actual integral martingale on a finite ordered grid.
The last grid time is repeated after the final index, so a grid with one
point and grids with repeated times require no separate convention. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

def brownianIntegralGridTime {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (k : ℕ) : ℝ≥0 :=
  τ ⟨min k N, Nat.lt_succ_of_le (min_le_right k N)⟩

theorem brownianIntegralGridTime_monotone {N : ℕ} {τ : Fin (N + 1) → ℝ≥0}
    (hτ : Monotone τ) : Monotone (brownianIntegralGridTime τ) := by
  intro i j hij
  apply hτ
  exact min_le_min hij le_rfl

theorem brownianIntegralGridTime_at_fin {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (i : Fin (N + 1)) : brownianIntegralGridTime τ i.val = τ i := by
  unfold brownianIntegralGridTime
  congr 1
  apply Fin.ext
  exact min_eq_left (Nat.le_of_lt_succ i.isLt)

def brownianIntegralGridFiltration (B : ℝ≥0 → Ω → ℝ) (hBm : ∀ t, Measurable (B t))
    {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (hτ : Monotone τ) : Filtration ℕ mΩ where
  seq k := brownianNaturalFiltration B hBm (brownianIntegralGridTime τ k)
  mono' := fun _ _ hij => (brownianNaturalFiltration B hBm).mono
    (brownianIntegralGridTime_monotone hτ hij)
  le' k := (brownianNaturalFiltration B hBm).le (brownianIntegralGridTime τ k)

theorem brownianIntegralProcess_grid_martingale (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) :
    Martingale (fun k => brownianIntegralProcess hB f (brownianIntegralGridTime τ k))
      (brownianIntegralGridFiltration B hBm τ hτ) P := by
  have hM := brownianIntegralProcess_martingale hB f
  exact ⟨fun k => hM.stronglyMeasurable _, fun _ _ hij =>
    hM.condExp_ae_eq (brownianIntegralGridTime_monotone hτ hij)⟩

noncomputable def brownianIntegralGridMax (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (ω : Ω) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |brownianIntegralProcess hB f (τ i) ω|)

theorem brownianIntegralGridMax_eq_running (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0) (ω : Ω) :
    brownianIntegralGridMax hB f τ ω = finiteRunningMax
      (fun k => |brownianIntegralProcess hB f (brownianIntegralGridTime τ k) ω|) N := by
  unfold brownianIntegralGridMax
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    have h := le_finiteRunningMax
      (fun k => |brownianIntegralProcess hB f (brownianIntegralGridTime τ k) ω|)
      (Nat.le_of_lt_succ i.isLt)
    simpa only [brownianIntegralGridTime_at_fin] using h
  · apply (finiteRunningMax_le_iff _ N _).mpr
    intro k hk
    let i : Fin (N + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
    have he : brownianIntegralGridTime τ k = τ i := brownianIntegralGridTime_at_fin τ i
    rw [he]
    exact Finset.le_sup' (fun i => |brownianIntegralProcess hB f (τ i) ω|) (Finset.mem_univ i)

end TimeTraps.Probability
