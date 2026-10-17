module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentJoint
public import Mathlib.Topology.MetricSpace.Lipschitz

@[expose] public section

/-! Continuous local extensions of the spatial local-time version are
obtained by clamping to a compact interval strictly inside (0,L). These
extensions will support Bochner spatial averaging without endpoint assumptions. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedSpatialWindowPoint (L l r : ℝ) (hl : 0 < l) (hlr : l ≤ r)
    (hr : r < L) (z : ℝ) : Ioo (0 : ℝ) L :=
  ⟨(projIcc l r hlr z).val, hl.trans_le (projIcc l r hlr z).property.1,
    (projIcc l r hlr z).property.2.trans_lt hr⟩

theorem reflectedSpatialWindowPoint_continuous (L l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L) :
    Continuous (reflectedSpatialWindowPoint L l r hl hlr hr) :=
  ((LipschitzWith.projIcc hlr).continuous.subtype_val).subtype_mk _

theorem reflectedSpatialWindowPoint_of_mem (L l r : ℝ) (hl : 0 < l) (hlr : l ≤ r)
    (hr : r < L) {z : ℝ} (hz : z ∈ Icc l r) :
    (reflectedSpatialWindowPoint L l r hl hlr hr z).val = z := by
  change (projIcc l r hlr z).val = z
  rw [projIcc_of_mem hlr hz]

noncomputable def reflectedLocalTimeWindowVersion (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L)
    (z : ℝ) (ω : ℕ → ℝ) : C(BrownianCompactTime T, ℝ) :=
  reflectedLocalTimeSpatialVersion L hL D hD x T (reflectedSpatialWindowPoint L l r hl hlr hr z) ω

theorem reflectedLocalTimeWindowVersion_continuous (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L) (ω : ℕ → ℝ) :
    Continuous (fun z => reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω) :=
  (reflectedLocalTimeSpatialVersion_continuous L hL D hD x T ω).comp
    (reflectedSpatialWindowPoint_continuous L l r hl hlr hr)

theorem reflectedLocalTimeWindowVersion_jointlyMeasurable (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L) (t : BrownianCompactTime T) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr p.1 p.2 t) := by
  apply measurable_uncurry_of_continuous_of_measurable
    (u := fun z ω => reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω t)
  · intro ω
    exact (continuous_eval_const t).comp (reflectedLocalTimeWindowVersion_continuous L hL D hD x T l r hl hlr hr ω)
  · intro z
    exact ((continuous_eval_const t).comp_stronglyMeasurable
      (reflectedLocalTimeSpatialVersion_stronglyMeasurable L hL D hD x T _)).measurable

end TimeTraps.Probability
