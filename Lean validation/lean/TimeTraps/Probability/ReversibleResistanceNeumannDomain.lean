module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingResistance

@[expose] public section

/-! Physical divergence-form Neumann tests for continuous positive
coefficients. The value, flux and generator are continuous on the closed
physical interval; only the flux is differentiated. Every such test
gives an actual reference C² Neumann test in resistance coordinates. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Interval
open scoped Topology

structure ReversibleNeumannTest (A : IntervalMedium) where
  value : ℝ → ℝ
  flux : ℝ → ℝ
  generator : ℝ → ℝ
  value_continuous : ContinuousOn value (Icc A.source.left A.source.right)
  flux_continuous : ContinuousOn flux (Icc A.source.left A.source.right)
  generator_continuous : ContinuousOn generator (Icc A.source.left A.source.right)
  value_derivative : ∀ x ∈ Ioo A.source.left A.source.right,
    HasDerivAt value (flux x / A.conductance x) x
  flux_derivative : ∀ x ∈ Ioo A.source.left A.source.right,
    HasDerivAt flux (A.source.density x * generator x) x
  neumann_left : flux A.source.left = 0
  neumann_right : flux A.source.right = 0

variable {A : IntervalMedium}

noncomputable def ReversibleNeumannTest.reference (H : ReversibleNeumannTest A) :
    ReflectedNeumannC2 A.resistanceLength where
  value := fun y => H.value (A.resistanceInverse y)
  slope := fun y => H.flux (A.resistanceInverse y)
  curvature := fun y => A.resistanceSpeed y * H.generator (A.resistanceInverse y)
  value_continuous := (H.value_continuous.comp_continuous A.resistanceInverse_continuous
    A.resistanceInverse_mem).continuousOn
  slope_continuous := (H.flux_continuous.comp_continuous A.resistanceInverse_continuous
    A.resistanceInverse_mem).continuousOn
  curvature_continuous := (A.resistanceSpeed_continuous.mul
    (H.generator_continuous.comp_continuous A.resistanceInverse_continuous
      A.resistanceInverse_mem)).continuousOn
  value_derivative := by
    intro y hy
    convert! (H.value_derivative _ (A.resistanceInverse_interior hy)).comp y
      (A.resistanceInverse_hasDerivAt hy) using 1
    exact (div_mul_cancel₀ _ (A.conductance_pos _ (A.resistanceInverse_mem y)).ne').symm
  slope_derivative := by
    intro y hy
    convert! (H.flux_derivative _ (A.resistanceInverse_interior hy)).comp y
      (A.resistanceInverse_hasDerivAt hy) using 1
    dsimp only [IntervalMedium.resistanceSpeed]
    ring
  neumann_left := by rw [A.resistanceInverse_zero]; exact H.neumann_left
  neumann_right := by rw [A.resistanceInverse_length]; exact H.neumann_right

theorem ReversibleNeumannTest.reference_value (H : ReversibleNeumannTest A) {x : ℝ}
    (hx : x ∈ Icc A.source.left A.source.right) :
    reversibleResistanceNeumannTest A H.reference x = H.value x := by
  change H.value (A.resistanceInverse (A.resistance x)) = H.value x
  rw [A.resistanceInverse_resistance hx]

theorem ReversibleNeumannTest.reference_flux (H : ReversibleNeumannTest A) {x : ℝ}
    (hx : x ∈ Icc A.source.left A.source.right) :
    reversibleResistanceNeumannFlux A H.reference x = H.flux x := by
  change H.flux (A.resistanceInverse (A.resistance x)) = H.flux x
  rw [A.resistanceInverse_resistance hx]

theorem ReversibleNeumannTest.reference_generator (H : ReversibleNeumannTest A) {x : ℝ}
    (hx : x ∈ Icc A.source.left A.source.right) :
    reversibleResistanceNeumannGenerator A H.reference x = H.generator x := by
  change (A.resistanceSpeed (A.resistance x) *
    H.generator (A.resistanceInverse (A.resistance x))) /
      (A.conductance x * A.source.density x) = H.generator x
  rw [A.resistanceInverse_resistance hx, A.resistanceSpeed_resistance hx]
  exact mul_div_cancel_left₀ _ (mul_pos (A.conductance_pos x hx) (A.source.positive x hx)).ne'

theorem ReversibleNeumannTest.flux_eq (H : ReversibleNeumannTest A) {x : ℝ}
    (hx : x ∈ Ioo A.source.left A.source.right) :
    A.conductance x * deriv H.value x = H.flux x := by
  rw [(H.value_derivative x hx).deriv]
  field_simp [(A.conductance_pos x (Ioo_subset_Icc_self hx)).ne']

theorem ReversibleNeumannTest.generator_divergence (H : ReversibleNeumannTest A) {x : ℝ}
    (hx : x ∈ Ioo A.source.left A.source.right) :
    deriv (fun y => A.conductance y * deriv H.value y) x / A.source.density x = H.generator x := by
  have hd := (H.flux_derivative x hx).congr_of_eventuallyEq (show
      (fun y => A.conductance y * deriv H.value y) =ᶠ[𝓝 x] H.flux from by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact H.flux_eq hy)
  rw [hd.deriv]
  exact mul_div_cancel_left₀ _ (A.source.positive x (Ioo_subset_Icc_self hx)).ne'

end TimeTraps.Probability
