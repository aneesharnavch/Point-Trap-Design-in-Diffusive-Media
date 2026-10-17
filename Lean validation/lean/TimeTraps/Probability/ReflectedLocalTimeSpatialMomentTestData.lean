module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentWindow
public import TimeTraps.Probability.ReflectedLocalTimeBandData

@[expose] public section

/-! Ordinary time integrals of bounded Borel tests are continuous.
Spatial integrals of a bounded test against the continuous local-time
version are genuine integrable continuous-path-valued Bochner integrals. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem brownianItoDrift_bounded_continuous {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ z, |g z| ≤ M) (ω : Ω) :
    Continuous (fun t => brownianItoDrift B g t ω) := by
  let q : ℝ → ℝ≥0 × Ω := fun s => (s.toNNReal, ω)
  have hq : Measurable q := measurable_real_toNNReal.prodMk measurable_const
  have hm : Measurable (fun s : ℝ => g (B s.toNNReal ω)) := hg.comp (hjoint.comp hq)
  have hi (u v : ℝ) : IntervalIntegrable (fun s : ℝ => g (B s.toNNReal ω)) volume u v := by
    have hj : IntegrableOn (fun s : ℝ => g (B s.toNNReal ω)) (uIcc u v) volume :=
      (integrableOn_const (C := M) (μ := volume) (s := uIcc u v) isCompact_uIcc.measure_ne_top).mono'
        hm.aestronglyMeasurable (Eventually.of_forall (fun s => hb (B s.toNNReal ω)))
    exact hj.intervalIntegrable
  exact (intervalIntegral.continuous_primitive hi 0).comp NNReal.continuous_coe

theorem reflectedLocalTimeWindow_test_integrable (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ z, |g z| ≤ M) (ω : ℕ → ℝ) :
    Integrable (fun z => g z • reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω)
      (volume.restrict (Icc l r)) := by
  have hc := reflectedLocalTimeWindowVersion_continuous L hL D hD x T l r hl hlr hr ω
  have hi : IntegrableOn (fun z => reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω)
      (Icc l r) volume := hc.integrableOn_Icc
  apply (hi.norm.const_mul M).mono'
    (hg.stronglyMeasurable.smul hc.stronglyMeasurable).aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    change ‖g z • reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _))

noncomputable def reflectedLocalTimeWindowTestPath (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L)
    (g : ℝ → ℝ) (ω : ℕ → ℝ) : C(BrownianCompactTime T, ℝ) :=
  ∫ z in Icc l r, g z • reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω

theorem reflectedLocalTimeWindowTestPath_apply (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (T : ℝ≥0) (l r : ℝ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < L)
    {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hb : ∀ z, |g z| ≤ M)
    (ω : ℕ → ℝ) (t : BrownianCompactTime T) :
    reflectedLocalTimeWindowTestPath L hL D hD x T l r hl hlr hr g ω t =
      ∫ z in Icc l r, g z * reflectedLocalTimeWindowVersion L hL D hD x T l r hl hlr hr z ω t := by
  have hi := reflectedLocalTimeWindow_test_integrable L hL D hD x T l r hl hlr hr hg hb ω
  exact ((ContinuousMap.evalCLM ℝ t).integral_comp_comm hi).symm

end TimeTraps.Probability
