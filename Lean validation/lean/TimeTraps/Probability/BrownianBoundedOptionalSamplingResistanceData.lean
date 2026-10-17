module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingNeumannPhysical

@[expose] public section

/-! Resistance-coordinate Neumann tests have the original divergence
form generator. Only continuity and positivity of conductance and speed
density are used: the derivative of the flux exists by cancellation,
without differentiating the conductance. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

noncomputable def reversibleResistanceNeumannTest (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) (z : ℝ) : ℝ := F.value (A.resistance z)

noncomputable def reversibleResistanceNeumannFlux (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) (z : ℝ) : ℝ := F.slope (A.resistance z)

noncomputable def reversibleResistanceNeumannGenerator (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) (z : ℝ) : ℝ :=
  F.curvature (A.resistance z) / (A.conductance z * A.source.density z)

theorem reversibleResistance_interior (A : IntervalMedium) {z : ℝ}
    (hz : z ∈ Ioo A.source.left A.source.right) : A.resistance z ∈ Ioo 0 A.resistanceLength := by
  constructor
  · simpa only [A.resistance_left] using A.resistance_strictMono
      ⟨le_rfl, A.source.increasing.le⟩ (Ioo_subset_Icc_self hz) hz.1
  · simpa only [A.resistance_right] using A.resistance_strictMono
      (Ioo_subset_Icc_self hz) ⟨A.source.increasing.le, le_rfl⟩ hz.2

theorem reversibleResistanceNeumannTest_continuous (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) :
    ContinuousOn (reversibleResistanceNeumannTest A F) (Icc A.source.left A.source.right) :=
  F.value_continuous.comp A.resistance_continuous (fun _ hz => A.resistance_mem hz)

theorem reversibleResistanceNeumannTest_hasDerivAt (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) {z : ℝ} (hz : z ∈ Ioo A.source.left A.source.right) :
    HasDerivAt (reversibleResistanceNeumannTest A F)
      (F.slope (A.resistance z) / A.conductance z) z := by
  convert! (F.value_derivative _ (reversibleResistance_interior A hz)).comp z
    (A.resistance_hasDerivAt hz) using 1
  simp only [mul_one_div]

theorem reversibleResistanceNeumannFlux_continuous (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) :
    ContinuousOn (reversibleResistanceNeumannFlux A F) (Icc A.source.left A.source.right) :=
  F.slope_continuous.comp A.resistance_continuous (fun _ hz => A.resistance_mem hz)

theorem reversibleResistanceNeumannFlux_eq (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) {z : ℝ} (hz : z ∈ Ioo A.source.left A.source.right) :
    A.conductance z * deriv (reversibleResistanceNeumannTest A F) z =
      reversibleResistanceNeumannFlux A F z := by
  rw [(reversibleResistanceNeumannTest_hasDerivAt A F hz).deriv]
  unfold reversibleResistanceNeumannFlux
  field_simp [(A.conductance_pos z (Ioo_subset_Icc_self hz)).ne']

theorem reversibleResistanceNeumannFlux_endpoints (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) :
    reversibleResistanceNeumannFlux A F A.source.left = 0 ∧
      reversibleResistanceNeumannFlux A F A.source.right = 0 := by
  simp only [reversibleResistanceNeumannFlux, A.resistance_left, A.resistance_right,
    F.neumann_left, F.neumann_right, and_self]

theorem reversibleResistanceNeumannFlux_hasDerivAt (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) {z : ℝ} (hz : z ∈ Ioo A.source.left A.source.right) :
    HasDerivAt (fun y => A.conductance y * deriv (reversibleResistanceNeumannTest A F) y)
      (F.curvature (A.resistance z) / A.conductance z) z := by
  have hd : HasDerivAt (reversibleResistanceNeumannFlux A F)
      (F.curvature (A.resistance z) / A.conductance z) z := by
    convert! (F.slope_derivative _ (reversibleResistance_interior A hz)).comp z
      (A.resistance_hasDerivAt hz) using 1
    simp only [mul_one_div]
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hz] with y hy
  exact reversibleResistanceNeumannFlux_eq A F hy

theorem reversibleResistanceNeumannGenerator_divergence (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) {z : ℝ} (hz : z ∈ Ioo A.source.left A.source.right) :
    deriv (fun y => A.conductance y * deriv (reversibleResistanceNeumannTest A F) y) z /
      A.source.density z = reversibleResistanceNeumannGenerator A F z := by
  rw [(reversibleResistanceNeumannFlux_hasDerivAt A F hz).deriv]
  exact div_div _ _ _

theorem reversibleResistanceNeumannGenerator_continuous (A : IntervalMedium)
    (F : ReflectedNeumannC2 A.resistanceLength) :
    ContinuousOn (reversibleResistanceNeumannGenerator A F) (Icc A.source.left A.source.right) :=
  (F.curvature_continuous.comp A.resistance_continuous (fun _ hz => A.resistance_mem hz)).div
    (A.conductance_continuous.mul A.source.continuous)
    (fun z hz => (mul_pos (A.conductance_pos z hz) (A.source.positive z hz)).ne')

end TimeTraps.Probability
