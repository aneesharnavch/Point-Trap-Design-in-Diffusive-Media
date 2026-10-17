module

public import TimeTraps.Analysis.ReversibleResistanceCoordinate

@[expose] public section

/-! The inverse resistance coordinate is extended constantly outside its
closed range. This extension makes the transformed speed globally continuous
using only the original coefficients on the physical interval. -/

namespace TimeTraps.Interval

open Set TimeTraps.Analysis Filter
open scoped Topology

noncomputable def IntervalMedium.resistanceInverse (A : IntervalMedium) (y : ℝ) : ℝ :=
  A.resistanceOrderIso.symm (projIcc 0 A.resistanceLength A.resistanceLength_pos.le y)

theorem IntervalMedium.resistanceInverse_mem (A : IntervalMedium) (y : ℝ) :
    A.resistanceInverse y ∈ Icc A.source.left A.source.right :=
  (A.resistanceOrderIso.symm (projIcc 0 A.resistanceLength A.resistanceLength_pos.le y)).property

theorem IntervalMedium.resistanceInverse_continuous (A : IntervalMedium) :
    Continuous A.resistanceInverse :=
  continuous_subtype_val.comp
    (A.resistanceOrderIso.symm.toHomeomorph.continuous.comp continuous_projIcc)

theorem IntervalMedium.resistance_inverse (A : IntervalMedium) {y : ℝ}
    (hy : y ∈ Icc 0 A.resistanceLength) : A.resistance (A.resistanceInverse y) = y := by
  have h := congrArg (fun z : Icc 0 A.resistanceLength => (z : ℝ))
    (A.resistanceOrderIso.apply_symm_apply
      (projIcc 0 A.resistanceLength A.resistanceLength_pos.le y))
  simpa only [IntervalMedium.resistanceInverse, A.resistanceOrderIso_apply,
    projIcc_of_mem A.resistanceLength_pos.le hy] using h

theorem IntervalMedium.resistanceInverse_resistance (A : IntervalMedium) {x : ℝ}
    (hx : x ∈ Icc A.source.left A.source.right) :
    A.resistanceInverse (A.resistance x) = x := by
  apply A.resistance_strictMono.injOn (A.resistanceInverse_mem _) hx
  exact A.resistance_inverse (A.resistance_mem hx)

theorem IntervalMedium.resistanceInverse_zero (A : IntervalMedium) :
    A.resistanceInverse 0 = A.source.left := by
  rw [← A.resistance_left]
  exact A.resistanceInverse_resistance ⟨le_rfl, A.source.increasing.le⟩

theorem IntervalMedium.resistanceInverse_length (A : IntervalMedium) :
    A.resistanceInverse A.resistanceLength = A.source.right := by
  rw [← A.resistance_right]
  exact A.resistanceInverse_resistance ⟨A.source.increasing.le, le_rfl⟩

theorem IntervalMedium.resistanceInverse_strictMono (A : IntervalMedium) :
    StrictMonoOn A.resistanceInverse (Icc 0 A.resistanceLength) := by
  intro x hx y hy hxy
  apply (A.resistance_strictMono.lt_iff_lt
    (A.resistanceInverse_mem x) (A.resistanceInverse_mem y)).mp
  simpa only [A.resistance_inverse hx, A.resistance_inverse hy] using hxy

theorem IntervalMedium.resistanceInverse_interior (A : IntervalMedium) {y : ℝ}
    (hy : y ∈ Ioo 0 A.resistanceLength) :
    A.resistanceInverse y ∈ Ioo A.source.left A.source.right := by
  constructor
  · simpa only [A.resistanceInverse_zero] using A.resistanceInverse_strictMono
      ⟨le_rfl, A.resistanceLength_pos.le⟩ (Ioo_subset_Icc_self hy) hy.1
  · simpa only [A.resistanceInverse_length] using A.resistanceInverse_strictMono
      (Ioo_subset_Icc_self hy) ⟨A.resistanceLength_pos.le, le_rfl⟩ hy.2

theorem IntervalMedium.resistanceInverse_hasDerivAt (A : IntervalMedium) {y : ℝ}
    (hy : y ∈ Ioo 0 A.resistanceLength) :
    HasDerivAt A.resistanceInverse (A.conductance (A.resistanceInverse y)) y := by
  have hn : 1 / A.conductance (A.resistanceInverse y) ≠ 0 :=
    ne_of_gt (one_div_pos.mpr (A.conductance_pos _ (A.resistanceInverse_mem y)))
  have hi : ∀ᶠ z in 𝓝 y, A.resistance (A.resistanceInverse z) = z := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    exact A.resistance_inverse (Ioo_subset_Icc_self hz)
  simpa only [one_div, inv_inv] using HasDerivAt.of_local_left_inverse
    A.resistanceInverse_continuous.continuousAt
      (A.resistance_hasDerivAt (A.resistanceInverse_interior hy)) hn hi

noncomputable def IntervalMedium.resistanceSpeed (A : IntervalMedium) (y : ℝ) : ℝ :=
  A.conductance (A.resistanceInverse y) * A.source.density (A.resistanceInverse y)

theorem IntervalMedium.resistanceSpeed_continuous (A : IntervalMedium) :
    Continuous A.resistanceSpeed :=
  (A.conductance_continuous.mul A.source.continuous).comp_continuous
    A.resistanceInverse_continuous A.resistanceInverse_mem

theorem IntervalMedium.resistanceSpeed_pos (A : IntervalMedium) (y : ℝ) :
    0 < A.resistanceSpeed y :=
  mul_pos (A.conductance_pos _ (A.resistanceInverse_mem y))
    (A.source.positive _ (A.resistanceInverse_mem y))

theorem IntervalMedium.resistanceSpeed_resistance (A : IntervalMedium) {x : ℝ}
    (hx : x ∈ Icc A.source.left A.source.right) :
    A.resistanceSpeed (A.resistance x) = A.conductance x * A.source.density x := by
  simp only [IntervalMedium.resistanceSpeed, A.resistanceInverse_resistance hx]

end TimeTraps.Interval
