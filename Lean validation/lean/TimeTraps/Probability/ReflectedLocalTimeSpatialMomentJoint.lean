module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentSpatialVersion

@[expose] public section

/-! The constructed version is jointly continuous in the spatial level
and time on each compact horizon, with joint measurability in the sample.
For every fixed interior level it is indistinguishable on that horizon
from the original local-time coefficient. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedLocalTimeSpatialVersion_joint_continuous (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Continuous (fun p : Ioo (0 : ℝ) L × BrownianCompactTime T =>
      reflectedLocalTimeSpatialVersion L hL D hD x T p.1 ω p.2) :=
  continuous_eval.comp (((reflectedLocalTimeSpatialVersion_continuous L hL D hD x T ω).comp
    continuous_fst).prodMk continuous_snd)

theorem reflectedLocalTimeSpatialVersion_jointlyMeasurable (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    Measurable (fun p : (Ioo (0 : ℝ) L × BrownianCompactTime T) × (ℕ → ℝ) =>
      reflectedLocalTimeSpatialVersion L hL D hD x T p.1.1 p.2 p.1.2) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (reflectedLocalTimeSpatialVersion_joint_continuous L hL D hD x T)
  intro p
  exact ((continuous_eval_const p.2).comp_stronglyMeasurable
    (reflectedLocalTimeSpatialVersion_stronglyMeasurable L hL D hD x T p.1)).measurable

theorem reflectedLocalTimeSpatialVersion_exists (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∃ V : Ioo (0 : ℝ) L → (ℕ → ℝ) → C(BrownianCompactTime T, ℝ),
      (∀ ω, Continuous (fun a => V a ω)) ∧
      (∀ a, StronglyMeasurable (V a)) ∧
      (∀ a, ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : BrownianCompactTime T,
        V a ω t = reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a.val t.val ω) :=
  ⟨reflectedLocalTimeSpatialVersion L hL D hD x T,
    reflectedLocalTimeSpatialVersion_continuous L hL D hD x T,
    reflectedLocalTimeSpatialVersion_stronglyMeasurable L hL D hD x T,
    reflectedLocalTimeSpatialVersion_fixed_level_all_times L hL D hD x T⟩

end TimeTraps.Probability
