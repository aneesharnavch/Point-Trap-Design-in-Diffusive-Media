module

public import TimeTraps.Probability.GraphLocalTimeCanonicalData
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-! Natural compact horizons control the genuine compact-open global
path space. Summably bounded eventual compact increments therefore give
a global continuous limit, without selecting limits under a measure. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal Topology

theorem graphLocalTime_cauchySeq_of_compact (F : ℕ → C(ℝ≥0, ℝ))
    (hF : ∀ N : ℕ, CauchySeq (fun n => graphLocalTimeCompactRestriction (N : ℝ≥0) (F n))) :
    CauchySeq F := by
  apply (Metric.uniformity_basis_dist.compactConvergenceUniformity).cauchySeq_iff.mpr
  intro q hq
  obtain ⟨b, hb⟩ := hq.1.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge b
  obtain ⟨M, hM⟩ := Metric.cauchySeq_iff.mp (hF N) q.2 hq.2
  refine ⟨M, fun m hm n hn t ht => ?_⟩
  let u : Icc (0 : ℝ≥0) (N : ℝ≥0) := ⟨t, zero_le, (hb ht).trans hN⟩
  exact (ContinuousMap.dist_apply_le_dist
    (f := graphLocalTimeCompactRestriction (N : ℝ≥0) (F m))
    (g := graphLocalTimeCompactRestriction (N : ℝ≥0) (F n)) u).trans_lt (hM m hm n hn)

theorem graphLocalTime_cauchySeq_of_eventually_dist_le_summable
    {α : Type*} [PseudoMetricSpace α] (F : ℕ → α) (ε : ℕ → ℝ)
    (hε : Summable ε) (hF : ∀ᶠ n in atTop, dist (F n) (F (n + 1)) ≤ ε n) :
    CauchySeq F := by
  apply cauchySeq_of_summable_dist
  apply hε.of_norm_bounded_eventually_nat
  filter_upwards [hF] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hn

theorem graphLocalTime_exists_limit_of_compact_increments (F : ℕ → C(ℝ≥0, ℝ))
    (ε : ℕ → ℕ → ℝ) (hε : ∀ N, Summable (ε N))
    (hF : ∀ N : ℕ, ∀ᶠ n in atTop,
      ‖graphLocalTimeCompactRestriction (N : ℝ≥0) (F (n + 1)) -
        graphLocalTimeCompactRestriction (N : ℝ≥0) (F n)‖ ≤ ε N n) :
    ∃ l : C(ℝ≥0, ℝ), Tendsto F atTop (𝓝 l) := by
  apply cauchySeq_tendsto_of_complete
  apply graphLocalTime_cauchySeq_of_compact
  intro N
  apply graphLocalTime_cauchySeq_of_eventually_dist_le_summable _ (ε N) (hε N)
  filter_upwards [hF N] with n hn
  simpa only [dist_eq_norm, norm_sub_rev] using hn

end TimeTraps.Probability
