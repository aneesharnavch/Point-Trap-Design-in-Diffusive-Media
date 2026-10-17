module

public import TimeTraps.Probability.BrownianIntegralFourthMaximal
public import TimeTraps.Probability.BrownianIntegralCompactMaximalFinite

@[expose] public section

/-! Fourth moments for finite samples of the actual integral martingale.
The fourth integrability hypothesis is explicit and is discharged by the
countably discontinuous coefficient construction in subsequent modules. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)}

theorem finiteRunningMax_memLp_four {X : ℕ → Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 4 P) (n : ℕ) :
    MemLp (fun ω => finiteRunningMax (fun k => X k ω) n) 4 P := by
  induction n with
  | zero => exact hX 0
  | succ n ih => exact ih.sup (hX (n + 1))

theorem brownianIntegralProcess_fourth_moment_mono (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {s t : ℝ≥0} (hst : s ≤ t)
    (hs : MemLp (brownianIntegralProcess hB f s) 4 P)
    (ht : MemLp (brownianIntegralProcess hB f t) 4 P) :
    (∫ ω, brownianIntegralProcess hB f s ω ^ 4 ∂P) ≤
      ∫ ω, brownianIntegralProcess hB f t ω ^ 4 ∂P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hn (z : ℝ) : ‖z‖ ^ (4 : ℝ) = z ^ 4 := by
    rw [Real.rpow_ofNat, Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs]
    ring
  have hi : Integrable (fun ω => ‖brownianIntegralProcess hB f t ω‖ ^ (4 : ℝ)) P := by
    simpa only [hn] using brownian_memLp_four_integrable_fourth ht
  have hc := Integrable.norm_condExp_rpow_le (f := brownianIntegralProcess hB f t)
    (m := brownianNaturalFiltration B hBm s) (by norm_num : (1 : ℝ) ≤ 4) hi
  have he := (brownianIntegralProcess_martingale hB f).condExp_ae_eq hst
  calc
    _ ≤ ∫ ω, P[fun ω => brownianIntegralProcess hB f t ω ^ 4 |
        brownianNaturalFiltration B hBm s] ω ∂P := by
      apply integral_mono_ae (brownian_memLp_four_integrable_fourth hs) integrable_condExp
      filter_upwards [hc, he] with ω hω heω
      simpa only [heω, hn] using hω
    _ = _ := integral_condExp ((brownianNaturalFiltration B hBm).le s)

theorem brownianIntegralGridMax_fourth (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) {N : ℕ} (τ : Fin (N + 1) → ℝ≥0)
    (hτ : Monotone τ) (T : ℝ≥0) (hT : ∀ i, τ i ≤ T)
    (h4 : ∀ t ≤ T, MemLp (brownianIntegralProcess hB f t) 4 P) :
    MemLp (brownianIntegralGridMax hB f τ) 4 P ∧
    (∫ ω, brownianIntegralGridMax hB f τ ω ^ 4 ∂P) ≤
      4 * ∫ ω, brownianIntegralProcess hB f T ω ^ 4 ∂P := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hg (k : ℕ) : MemLp
      (brownianIntegralProcess hB f (brownianIntegralGridTime τ k)) 4 P :=
    h4 _ (hT _)
  have hm := brownian_fourth_martingale_maximal
    (brownianIntegralProcess_grid_martingale hB f τ hτ) hg N
  have he : brownianIntegralGridTime τ N = τ (Fin.last N) :=
    brownianIntegralGridTime_at_fin τ (Fin.last N)
  have hmem := finiteRunningMax_memLp_four (fun k => (hg k).norm) N
  constructor
  · simpa only [Real.norm_eq_abs, ← brownianIntegralGridMax_eq_running] using hmem
  · have hlast := brownianIntegralProcess_fourth_moment_mono hB f (hT (Fin.last N))
      (h4 _ (hT _)) (h4 T le_rfl)
    have hb : (∫ ω, brownianIntegralGridMax hB f τ ω ^ 4 ∂P) ≤
        4 * ∫ ω, brownianIntegralProcess hB f (τ (Fin.last N)) ω ^ 4 ∂P := by
      simpa only [← brownianIntegralGridMax_eq_running, he] using hm
    exact hb.trans (mul_le_mul_of_nonneg_left hlast (by norm_num))

theorem brownianIntegralFiniteMax_fourth (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (s : Finset ℝ≥0) (hs : s.Nonempty)
    (T : ℝ≥0) (hT : ∀ t ∈ s, t ≤ T)
    (h4 : ∀ t ≤ T, MemLp (brownianIntegralProcess hB f t) 4 P) :
    MemLp (brownianIntegralFiniteMax hB f s hs) 4 P ∧
    (∫ ω, brownianIntegralFiniteMax hB f s hs ω ^ 4 ∂P) ≤
      4 * ∫ ω, brownianIntegralProcess hB f T ω ^ 4 ∂P := by
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr hs).ne'
  have he : brownianIntegralFiniteMax hB f s hs =
      brownianIntegralGridMax hB f (s.orderEmbOfFin hN) :=
    funext (brownianIntegralFiniteMax_eq_ordered hB f s hs hN)
  rw [he]
  exact brownianIntegralGridMax_fourth hB f _ (s.orderEmbOfFin hN).monotone T
    (fun i => hT _ (s.orderEmbOfFin_mem hN i)) h4

end TimeTraps.Probability
