module

public import TimeTraps.Probability.GraphPhysicalClock
public import TimeTraps.Probability.GraphConservativeFuturePathData

@[expose] public section

/-! The Borel-speed integral clock is measurable in the original raw
past at each time. Its true inverse is a bounded stopping time, derived
from the clock order equivalence. -/

namespace TimeTraps.Graph

open Set MeasureTheory ProbabilityTheory TimeTraps.Analysis
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

omit [Nonempty E] in
theorem MetricGraph.physicalClock_integral_stronglyMeasurable (G : MetricGraph V E)
    (b : ℝ) (t : ℝ≥0) :
    StronglyMeasurable[graphContinuousNaturalFiltration G t]
      (fun p : GraphContinuousPath G => ∫ r in 0..t.val, G.physicalSpeed b (p r.toNNReal)) := by
  let ℱ := graphContinuousNaturalFiltration G
  have hX : StronglyAdapted ℱ (fun s (p : GraphContinuousPath G) => p s) :=
    Filtration.stronglyAdapted_natural _
  have hmX : @StronglyMeasurable (ℝ × GraphContinuousPath G) (GraphRealization G) _
      (MeasurableSpace.prod inferInstance (ℱ t)) (fun q => q.2 (min q.1.toNNReal t)) := by
    let : MeasurableSpace (GraphContinuousPath G) := ℱ t
    apply stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun (r : ℝ) (p : GraphContinuousPath G) => p (min r.toNNReal t))
    · intro p
      exact p.continuous.comp (continuous_real_toNNReal.min continuous_const)
    · intro r
      exact (hX (min r.toNNReal t)).mono (ℱ.mono (min_le_right _ _))
  have hm : @StronglyMeasurable (ℝ × GraphContinuousPath G) ℝ _
      (MeasurableSpace.prod inferInstance (ℱ t))
      (fun q => G.physicalSpeed b (q.2 (min q.1.toNNReal t))) :=
    ((G.physicalSpeed_measurable b).comp hmX.measurable).stronglyMeasurable
  have he : (fun p : GraphContinuousPath G => ∫ r in 0..t.val, G.physicalSpeed b (p r.toNNReal)) =
      (fun p => ∫ r in Ioc 0 t.val, G.physicalSpeed b (p (min r.toNNReal t))) := by
    funext p
    apply (intervalIntegral.integral_of_le (f := fun r => G.physicalSpeed b (p r.toNNReal)) t.coe_nonneg).trans
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hr.2)]
  rw [he]
  let : MeasurableSpace (GraphContinuousPath G) := ℱ t
  exact hm.integral_prod_left' (μ := volume.restrict (Ioc 0 t.val))

theorem MetricGraph.physicalClock_measurable_past (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) : Measurable[graphContinuousNaturalFiltration G t] (G.physicalClock b hb t) :=
  (G.physicalClock_integral_stronglyMeasurable b t).measurable.subtype_mk

theorem MetricGraph.physicalInverseClock_le_iff (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t s : ℝ≥0) (p : GraphContinuousPath G) :
    G.physicalInverseClock b hb t p ≤ s ↔ t ≤ G.physicalClock b hb s p := by
  simpa only [G.physicalClock_inverse] using
    ((G.physicalClock_strictMono b hb p).le_iff_le
      (a := G.physicalInverseClock b hb t p) (b := s)).symm

theorem MetricGraph.physicalInverseClock_isStoppingTime (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) : IsStoppingTime (graphContinuousNaturalFiltration G)
      (fun p => (G.physicalInverseClock b hb t p : WithTop ℝ≥0)) := by
  intro s
  simp only [WithTop.coe_le_coe]
  simp_rw [G.physicalInverseClock_le_iff]
  exact measurableSet_le measurable_const (G.physicalClock_measurable_past b hb s)

theorem MetricGraph.physicalInverseClock_measurable (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (t : ℝ≥0) : Measurable (G.physicalInverseClock b hb t) := by
  apply measurable_of_Iic
  intro s
  change MeasurableSet {p | G.physicalInverseClock b hb t p ≤ s}
  simp_rw [G.physicalInverseClock_le_iff]
  exact measurableSet_le measurable_const
    ((G.physicalClock_measurable_past b hb s).mono ((graphContinuousNaturalFiltration G).le s) le_rfl)

end TimeTraps.Graph
