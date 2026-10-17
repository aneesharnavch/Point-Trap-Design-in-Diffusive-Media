module

public import TimeTraps.Probability.GraphConservativeOccupationKacTriangle
public import Mathlib.Topology.MetricSpace.Cauchy

@[expose] public section

/-! Elementary signed estimates used to turn uniform potential
approximation into genuine mean-square convergence of occupation times. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped Topology

theorem occupationDifference_mul_le {f g v ε : ℝ}
    (hf : 0 ≤ f) (hg : 0 ≤ g) (hv : |v| ≤ ε) :
    (f - g) * v ≤ ε * (f + g) := by
  have hd : |f - g| ≤ f + g := abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    (f - g) * v ≤ |(f - g) * v| := le_abs_self _
    _ = |f - g| * |v| := abs_mul _ _
    _ ≤ (f + g) * ε := mul_le_mul hd hv (abs_nonneg _) (add_nonneg hf hg)
    _ = ε * (f + g) := mul_comm _ _

theorem integral_occupationDifference_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g v : Ω → ℝ) {ε : ℝ}
    (hf : ∀ ω, 0 ≤ f ω) (hg : ∀ ω, 0 ≤ g ω) (hv : ∀ ω, |v ω| ≤ ε)
    (hi : Integrable (fun ω => (f ω - g ω) * v ω) μ)
    (hj : Integrable (fun ω => f ω + g ω) μ) :
    (∫ ω, (f ω - g ω) * v ω ∂μ) ≤ ε * ∫ ω, f ω + g ω ∂μ := by
  rw [← integral_const_mul]
  exact integral_mono hi (hj.const_mul ε) (fun ω => occupationDifference_mul_le (hf ω) (hg ω) (hv ω))

theorem cauchySeq_of_norm_sub_sq_le {A : Type*} [NormedAddCommGroup A]
    {u : ℕ → A} {e : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (he : Tendsto e atTop (𝓝 0))
    (hb : ∀ n m, ‖u n - u m‖ ^ 2 ≤ C * (e n + e m)) : CauchySeq u := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ := ε ^ 2 / (4 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδeq : δ * (4 * (C + 1)) = ε ^ 2 := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (he.eventually (gt_mem_nhds hδ))
  refine ⟨N, ?_⟩
  intro n hn m hm
  have hbound := (hb n m).trans
    (mul_le_mul_of_nonneg_left (add_le_add (hN n hn).le (hN m hm).le) hC)
  have hs : ‖u n - u m‖ ^ 2 < ε ^ 2 := by
    nlinarith [mul_nonneg hC hδ.le]
  rw [dist_eq_norm]
  exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hs

end TimeTraps.Probability
