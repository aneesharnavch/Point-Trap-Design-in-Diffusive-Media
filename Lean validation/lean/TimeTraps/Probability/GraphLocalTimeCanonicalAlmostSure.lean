module

public import TimeTraps.Probability.GraphLocalTimeCanonicalCauchy
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

@[expose] public section

/-! First Borel-Cantelli gives almost-sure convergence to the same Borel
path functional under each initial law. The deterministic approximant
sequence and its canonical limit never depend on that law. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω]

theorem graphLocalTimeCanonical_hasLimit_ae (A : ℕ → Ω → C(ℝ≥0, ℝ)) (μ : Measure Ω)
    (ε : ℕ → ℕ → ℝ) (hε : ∀ N, Summable (ε N))
    (hsum : ∀ N : ℕ, (∑' n, μ {ω | ε N n <
      ‖graphLocalTimeCompactRestriction (N : ℝ≥0) (A (n + 1) ω) -
        graphLocalTimeCompactRestriction (N : ℝ≥0) (A n ω)‖}) ≠ ∞) :
    ∀ᵐ ω ∂μ, GraphLocalTimeCanonicalHasLimit A ω := by
  have h (N : ℕ) : ∀ᵐ ω ∂μ, ∀ᶠ n in atTop,
      ‖graphLocalTimeCompactRestriction (N : ℝ≥0) (A (n + 1) ω) -
        graphLocalTimeCompactRestriction (N : ℝ≥0) (A n ω)‖ ≤ ε N n := by
    simpa only [Set.mem_ofPred_eq, not_lt] using ae_eventually_notMem (hsum N)
  filter_upwards [ae_all_iff.mpr h] with ω hω
  exact graphLocalTime_exists_limit_of_compact_increments (fun n => A n ω) ε hε hω

theorem graphLocalTimeCanonical_tendsto_ae (A : ℕ → Ω → C(ℝ≥0, ℝ)) (μ : Measure Ω)
    (ε : ℕ → ℕ → ℝ) (hε : ∀ N, Summable (ε N))
    (hsum : ∀ N : ℕ, (∑' n, μ {ω | ε N n <
      ‖graphLocalTimeCompactRestriction (N : ℝ≥0) (A (n + 1) ω) -
        graphLocalTimeCompactRestriction (N : ℝ≥0) (A n ω)‖}) ≠ ∞) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (graphLocalTimeCanonicalPath A ω)) :=
  (graphLocalTimeCanonical_hasLimit_ae A μ ε hε hsum).mono (fun _ hω => hω.tendsto)

omit [MeasurableSpace Ω] in
theorem GraphLocalTimeCanonicalHasLimit.compact_tendsto {A : ℕ → Ω → C(ℝ≥0, ℝ)} {ω : Ω}
    (hω : GraphLocalTimeCanonicalHasLimit A ω) (T : ℝ≥0) :
    Tendsto (fun n => graphLocalTimeCompactRestriction T (A n ω)) atTop
      (𝓝 (graphLocalTimeCompactRestriction T (graphLocalTimeCanonicalPath A ω))) :=
  (graphLocalTimeCompactRestriction_continuous T).continuousAt.tendsto.comp hω.tendsto

omit [MeasurableSpace Ω] in
theorem GraphLocalTimeCanonicalHasLimit.compact_sup_tendsto {A : ℕ → Ω → C(ℝ≥0, ℝ)} {ω : Ω}
    (hω : GraphLocalTimeCanonicalHasLimit A ω) (T : ℝ≥0) :
    Tendsto (fun n => ⨆ t : Icc (0 : ℝ≥0) T, |A n ω t.val - graphLocalTimeCanonicalPath A ω t.val|)
      atTop (𝓝 0) := by
  have h := ((hω.compact_tendsto T).sub
    (tendsto_const_nhds (x := graphLocalTimeCompactRestriction T (graphLocalTimeCanonicalPath A ω)))).norm
  simpa only [sub_self, norm_zero, ContinuousMap.norm_eq_iSup_norm,
    ContinuousMap.sub_apply, graphLocalTimeCompactRestriction_apply, Real.norm_eq_abs] using h

theorem graphLocalTimeCanonical_all_compact_uniform_ae (A : ℕ → Ω → C(ℝ≥0, ℝ)) (μ : Measure Ω)
    (ε : ℕ → ℕ → ℝ) (hε : ∀ N, Summable (ε N))
    (hsum : ∀ N : ℕ, (∑' n, μ {ω | ε N n <
      ‖graphLocalTimeCompactRestriction (N : ℝ≥0) (A (n + 1) ω) -
        graphLocalTimeCompactRestriction (N : ℝ≥0) (A n ω)‖}) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ T : ℝ≥0,
      Tendsto (fun n => ⨆ t : Icc (0 : ℝ≥0) T, |A n ω t.val - graphLocalTimeCanonicalPath A ω t.val|)
        atTop (𝓝 0) :=
  (graphLocalTimeCanonical_hasLimit_ae A μ ε hε hsum).mono (fun _ hω T => hω.compact_sup_tendsto T)

end TimeTraps.Probability
