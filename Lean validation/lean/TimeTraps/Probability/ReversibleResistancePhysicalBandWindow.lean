module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandLimit

@[expose] public section

/-! Physical shrinking bands and continuous coefficient extensions by
projection onto the physical interval. Every sufficiently narrow band
around an interior site lies in both the physical interval and the
reference local-time comparison window. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

noncomputable def resistancePhysicalProjection (A : IntervalMedium) (z : ℝ) : ℝ :=
  projIcc A.source.left A.source.right A.source.increasing.le z

noncomputable def resistancePhysicalCoordinate (A : IntervalMedium) (z : ℝ) : ℝ :=
  A.resistance (resistancePhysicalProjection A z)

noncomputable def resistancePhysicalDensity (A : IntervalMedium) (z : ℝ) : ℝ :=
  A.source.density (resistancePhysicalProjection A z)

theorem resistancePhysicalProjection_mem (A : IntervalMedium) (z : ℝ) :
    resistancePhysicalProjection A z ∈ Icc A.source.left A.source.right :=
  (projIcc A.source.left A.source.right A.source.increasing.le z).property

theorem resistancePhysicalProjection_continuous (A : IntervalMedium) :
    Continuous (resistancePhysicalProjection A) := continuous_subtype_val.comp continuous_projIcc

theorem resistancePhysicalProjection_eq (A : IntervalMedium) {z : ℝ}
    (hz : z ∈ Icc A.source.left A.source.right) : resistancePhysicalProjection A z = z := by
  simp only [resistancePhysicalProjection, projIcc_of_mem A.source.increasing.le hz]

theorem resistancePhysicalCoordinate_continuous (A : IntervalMedium) :
    Continuous (resistancePhysicalCoordinate A) :=
  A.resistance_continuous.comp_continuous (resistancePhysicalProjection_continuous A)
    (resistancePhysicalProjection_mem A)

theorem resistancePhysicalDensity_continuous (A : IntervalMedium) :
    Continuous (resistancePhysicalDensity A) :=
  A.source.continuous.comp_continuous (resistancePhysicalProjection_continuous A)
    (resistancePhysicalProjection_mem A)

theorem resistancePhysicalDensity_pos (A : IntervalMedium) (z : ℝ) :
    0 < resistancePhysicalDensity A z := A.source.positive _ (resistancePhysicalProjection_mem A z)

theorem resistancePhysicalCoordinate_eq (A : IntervalMedium) {z : ℝ}
    (hz : z ∈ Icc A.source.left A.source.right) : resistancePhysicalCoordinate A z = A.resistance z := by
  rw [resistancePhysicalCoordinate, resistancePhysicalProjection_eq A hz]

theorem resistancePhysicalDensity_eq (A : IntervalMedium) {z : ℝ}
    (hz : z ∈ Icc A.source.left A.source.right) : resistancePhysicalDensity A z = A.source.density z := by
  rw [resistancePhysicalDensity, resistancePhysicalProjection_eq A hz]

theorem reversibleResistancePhysicalBand_window (A : IntervalMedium) {a : ℝ}
    (ha : a ∈ Ioo A.source.left A.source.right) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, |z - a| < r →
      z ∈ Ioo A.source.left A.source.right ∧
      A.resistance z ∈ Ioo (A.resistance a / 2) ((A.resistance a + A.resistanceLength) / 2) := by
  have haR := reversibleResistance_site_interior A ha
  have hwindow : Ioo (A.resistance a / 2) ((A.resistance a + A.resistanceLength) / 2) ∈
      𝓝 (resistancePhysicalCoordinate A a) := by
    rw [resistancePhysicalCoordinate_eq A (Ioo_subset_Icc_self ha)]
    exact Ioo_mem_nhds (by linarith [haR.1]) (by linarith [haR.2])
  have hpre := (resistancePhysicalCoordinate_continuous A).continuousAt.tendsto hwindow
  have hn : {z | z ∈ Ioo A.source.left A.source.right ∧
      resistancePhysicalCoordinate A z ∈ Ioo (A.resistance a / 2)
        ((A.resistance a + A.resistanceLength) / 2)} ∈ 𝓝 a :=
    inter_mem (Ioo_mem_nhds ha.1 ha.2) hpre
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, fun z hz => ?_⟩
  have he := hsub (show z ∈ Metric.ball a r by simpa only [Metric.mem_ball, Real.dist_eq] using hz)
  exact ⟨he.1, by simpa only [resistancePhysicalCoordinate_eq A (Ioo_subset_Icc_self he.1)] using he.2⟩

end TimeTraps.Probability
