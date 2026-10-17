module

public import TimeTraps.Interval.WeightedGridIFTVariation
public import Mathlib.Analysis.Calculus.Taylor

@[expose] public section

/-! A uniform quadratic remainder for the C² implicit-function branch.
The first-order coefficient is its checked tridiagonal-system solution. -/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology ContDiff

theorem gridIFT_quadratic_remainder {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : ContDiffAt ℝ 2 f 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ε : ℝ, |ε| < δ →
      ‖f ε - f 0 - ε • deriv f 0‖ ≤ C * ε ^ 2 := by
  obtain ⟨u, hu, hcu⟩ := hf.contDiffOn le_rfl (by norm_num)
  obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.mp hu
  let s := Metric.ball (0 : ℝ) r
  have hs : s ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hr
  have h0s : (0 : ℝ) ∈ s := Metric.mem_ball_self hr
  have hc : ContDiffOn ℝ (2 : ℕ) f s := hcu.mono hru
  have ht := taylor_isLittleO (convex_ball (0 : ℝ) r) h0s hc
  rw [nhdsWithin_eq_nhds.mpr hs] at ht
  have hp (ε : ℝ) : taylorWithinEval f 2 s 0 ε =
      f 0 + ε • deriv f 0 + ((1 / 2 : ℝ) * ε ^ 2) • iteratedDerivWithin 2 f s 0 := by
    norm_num [taylorWithinEval_succ, derivWithin_of_mem_nhds hs]
  have he := ht.def (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨δ, hδ, hδe⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨1 + ‖iteratedDerivWithin 2 f s 0‖ / 2, δ, by positivity, hδ, ?_⟩
  intro ε hε
  have hεe := hδe (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε)
  have hsplit : f ε - f 0 - ε • deriv f 0 =
      (f ε - taylorWithinEval f 2 s 0 ε) +
        ((1 / 2 : ℝ) * ε ^ 2) • iteratedDerivWithin 2 f s 0 := by
    rw [hp]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖f ε - taylorWithinEval f 2 s 0 ε‖ +
        ‖((1 / 2 : ℝ) * ε ^ 2) • iteratedDerivWithin 2 f s 0‖ := norm_add_le _ _
    _ ≤ 1 * ‖(ε - 0) ^ 2‖ +
        ‖((1 / 2 : ℝ) * ε ^ 2) • iteratedDerivWithin 2 f s 0‖ := add_le_add hεe le_rfl
    _ = (1 + ‖iteratedDerivWithin 2 f s 0‖ / 2) * ε ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring

variable {n : ℕ} (h : ℝ → ℝ) (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)

theorem gridIFTBranch_quadratic_remainder :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ε : ℝ, |ε| < δ →
      ‖gridIFTBranch (n := n) h hh Ω hΩ ε - gridIFTBaseline n -
        ε • deriv (gridIFTBranch h hh Ω hΩ) 0‖ ≤ C * ε ^ 2 := by
  simpa only [gridIFTBranch_zero] using
    gridIFT_quadratic_remainder (gridIFTBranch (n := n) h hh Ω hΩ)
      (gridIFTBranch_contDiffAt h hh Ω hΩ)

theorem gridIFTBranch_coordinate_expansion :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ i : Fin n,
      |gridIFTBranch h hh Ω hΩ ε i - gridIFTBaseline n i -
        ε * deriv (gridIFTBranch h hh Ω hΩ) 0 i| ≤ C * ε ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := gridIFTBranch_quadratic_remainder (n := n) h hh Ω hΩ
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro ε hε i
  exact (norm_le_pi_norm (gridIFTBranch h hh Ω hΩ ε - gridIFTBaseline n -
    ε • deriv (gridIFTBranch h hh Ω hΩ) 0) i).trans (hb ε hε)

end TimeTraps.Interval
