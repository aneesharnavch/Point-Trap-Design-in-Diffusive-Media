module

public import TimeTraps.Probability.ReversibleResistancePhysicalBandWindow
public import TimeTraps.Probability.ReflectedLocalTimeBandErrorAverage

@[expose] public section

/-! A jointly measurable physical-space maximal-error family, weighted
by the original speed density. It is continuous as an L2 family and
vanishes at the central site. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

noncomputable def resistancePhysicalBandErrorL2 (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (z : ℝ) : Lp ℝ 2 brownianDyadicMeasure :=
  resistancePhysicalDensity A z • reflectedBandErrorL2 A.resistanceLength A.resistanceLength_pos
    (A.resistance x) (Real.sqrt_pos.mpr (show 0 < 2 * (1 : ℝ) by norm_num)) S
      ⟨A.resistance a, reversibleResistance_site_interior A a.property⟩ (resistancePhysicalCoordinate A z)

noncomputable def resistancePhysicalBandErrorVersion (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (z : ℝ) (ω : ℕ → ℝ) : ℝ :=
  resistancePhysicalDensity A z * reflectedBandErrorVersion A.resistanceLength A.resistanceLength_pos
    (A.resistance x) (Real.sqrt_pos.mpr (show 0 < 2 * (1 : ℝ) by norm_num)) S
      ⟨A.resistance a, reversibleResistance_site_interior A a.property⟩ (resistancePhysicalCoordinate A z) ω

theorem resistancePhysicalBandErrorL2_continuous (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) : Continuous (resistancePhysicalBandErrorL2 A x S a) :=
  (resistancePhysicalDensity_continuous A).smul
    ((reflectedBandErrorL2_continuous A.resistanceLength A.resistanceLength_pos (A.resistance x)
      (Real.sqrt_pos.mpr (show 0 < 2 * (1 : ℝ) by norm_num)) S ⟨A.resistance a, reversibleResistance_site_interior A a.property⟩).comp
        (resistancePhysicalCoordinate_continuous A))

theorem resistancePhysicalBandErrorL2_center (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) : resistancePhysicalBandErrorL2 A x S a a.val = 0 := by
  rw [resistancePhysicalBandErrorL2, resistancePhysicalCoordinate_eq A (Ioo_subset_Icc_self a.property)]
  have hc := reflectedBandErrorL2_center A.resistanceLength A.resistanceLength_pos (A.resistance x)
    (Real.sqrt_pos.mpr (show 0 < 2 * (1 : ℝ) by norm_num)) S
      ⟨A.resistance a, reversibleResistance_site_interior A a.property⟩
  rw [hc, smul_zero]

theorem resistancePhysicalBandErrorVersion_jointlyMeasurable (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => resistancePhysicalBandErrorVersion A x S a p.1 p.2) := by
  let q : ℝ × (ℕ → ℝ) → ℝ × (ℕ → ℝ) := fun p => (resistancePhysicalCoordinate A p.1, p.2)
  have hq : Measurable q := ((resistancePhysicalCoordinate_continuous A).measurable.comp measurable_fst).prodMk measurable_snd
  have he := (reflectedBandErrorVersion_jointlyMeasurable A.resistanceLength A.resistanceLength_pos
    (A.resistance x) (Real.sqrt_pos.mpr (show 0 < 2 * (1 : ℝ) by norm_num)) S
      ⟨A.resistance a, reversibleResistance_site_interior A a.property⟩).comp hq
  dsimp only [Function.comp_def, q] at he
  exact ((resistancePhysicalDensity_continuous A).measurable.comp measurable_fst).mul he

theorem resistancePhysicalBandErrorVersion_nonneg (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (z : ℝ) (ω : ℕ → ℝ) :
    0 ≤ resistancePhysicalBandErrorVersion A x S a z ω :=
  mul_nonneg (resistancePhysicalDensity_pos A z).le
    (reflectedBandErrorVersion_nonneg A.resistanceLength A.resistanceLength_pos (A.resistance x)
      (Real.sqrt_pos.mpr (show 0 < 2 * (1 : ℝ) by norm_num)) S ⟨A.resistance a, reversibleResistance_site_interior A a.property⟩ _ ω)

theorem resistancePhysicalBandErrorVersion_ae (A : IntervalMedium) (x : ℝ) (S : ℝ≥0)
    (a : Ioo A.source.left A.source.right) (z : ℝ) :
    resistancePhysicalBandErrorVersion A x S a z =ᵐ[brownianDyadicMeasure] resistancePhysicalBandErrorL2 A x S a z := by
  let F := reflectedBandErrorL2 A.resistanceLength A.resistanceLength_pos (A.resistance x)
    (Real.sqrt_pos.mpr (show 0 < 2 * (1 : ℝ) by norm_num)) S
      ⟨A.resistance a, reversibleResistance_site_interior A a.property⟩ (resistancePhysicalCoordinate A z)
  filter_upwards [Lp.coeFn_smul (resistancePhysicalDensity A z) F,
    reflectedBandErrorVersion_ae A.resistanceLength A.resistanceLength_pos (A.resistance x)
      (Real.sqrt_pos.mpr (show 0 < 2 * (1 : ℝ) by norm_num)) S ⟨A.resistance a, reversibleResistance_site_interior A a.property⟩
        (resistancePhysicalCoordinate A z)] with ω hs he
  change resistancePhysicalDensity A z * _ = ((resistancePhysicalDensity A z) • F) ω
  rw [hs, Pi.smul_apply, smul_eq_mul, he]

end TimeTraps.Probability
