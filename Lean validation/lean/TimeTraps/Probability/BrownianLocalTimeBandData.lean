module

public import TimeTraps.Probability.BrownianOccupationL1Extension

@[expose] public section

/-! The genuine open occupation band and its normalized ordinary time
integral. Its L2 element is constructed from that time integral, before
identifying it with any spatial average of the Tanaka compensation. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

noncomputable def brownianBandIndicator (a h : ℝ) : ℝ → ℝ :=
  (Ioo (a - h) (a + h)).indicator (fun _ => 1)

theorem brownianBandIndicator_apply (a h x : ℝ) :
    brownianBandIndicator a h x = if |x - a| < h then 1 else 0 := by
  have he : x ∈ Ioo (a - h) (a + h) ↔ |x - a| < h := by
    rw [mem_Ioo, abs_lt]
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  simp only [brownianBandIndicator, indicator_apply, he]

theorem brownianBandIndicator_measurable (a h : ℝ) : Measurable (brownianBandIndicator a h) :=
  measurable_const.indicator measurableSet_Ioo

theorem brownianBandIndicator_abs_le_one (a h x : ℝ) : |brownianBandIndicator a h x| ≤ 1 := by
  rw [brownianBandIndicator_apply]
  split_ifs <;> norm_num

theorem brownianBandIndicator_integrable (a h : ℝ) : Integrable (brownianBandIndicator a h) volume := by
  apply (integrable_indicator_iff measurableSet_Ioo).mpr
  exact (integrableOn_const (μ := volume) (s := Icc (a - h) (a + h))
    isCompact_Icc.measure_ne_top).mono_set Ioo_subset_Icc_self

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianBandOccupation (B : ℝ≥0 → Ω → ℝ) (a h : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  (1 / (2 * h)) * brownianItoDrift B (brownianBandIndicator a h) T ω

theorem brownianBandOccupation_formula (B : ℝ≥0 → Ω → ℝ) (a h : ℝ) (T : ℝ≥0) (ω : Ω) :
    brownianBandOccupation B a h T ω = (1 / (2 * h)) *
      ∫ s in (0 : ℝ)..T.val, if |B s.toNNReal ω - a| < h then (1 : ℝ) else 0 := by
  simp only [brownianBandOccupation, brownianItoDrift, brownianBandIndicator_apply]

theorem brownianBandOccupation_drift_memLp (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a h : ℝ) (T : ℝ≥0) :
    MemLp (brownianItoDrift B (brownianBandIndicator a h) T) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact brownianItoDrift_bounded_memLp (brownianBandIndicator_measurable a h) hjoint
    (brownianBandIndicator_abs_le_one a h) T

noncomputable def brownianBandOccupationL2 (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a h : ℝ) (T : ℝ≥0) : Lp ℝ 2 P :=
  (1 / (2 * h)) • brownianItoDriftL2 B (brownianBandIndicator a h) T
    (brownianBandOccupation_drift_memLp hB hjoint a h T)

theorem brownianBandOccupationL2_coe (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a h : ℝ) (T : ℝ≥0) :
    brownianBandOccupationL2 hB hjoint a h T =ᵐ[P] brownianBandOccupation B a h T := by
  let X := brownianItoDriftL2 B (brownianBandIndicator a h) T
    (brownianBandOccupation_drift_memLp hB hjoint a h T)
  filter_upwards [Lp.coeFn_smul (1 / (2 * h)) X,
    brownianItoDriftL2_coe B (brownianBandIndicator a h) T
      (brownianBandOccupation_drift_memLp hB hjoint a h T)] with ω hs hx
  change ((1 / (2 * h)) • X) ω = _
  rw [hs, Pi.smul_apply, smul_eq_mul, hx]
  rfl

end TimeTraps.Probability
