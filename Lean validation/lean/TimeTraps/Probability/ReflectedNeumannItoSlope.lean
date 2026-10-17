module

public import TimeTraps.Probability.ReflectedFellerSmoothingRegularity
public import TimeTraps.Probability.BrownianFoldSlopeUnit
public import TimeTraps.Probability.ReflectedFoldAffine

@[expose] public section

/-! The actual derivative of a folded Neumann test away from the corner
lattice is its physical slope times the signed fold slope. Positive-time
Gaussian laws exclude that countable lattice in product measure, which
identifies the stochastic coefficient without assigning a derivative to
the nonsmooth fold at its corners. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedFold_hasDerivAt_away (L : ℝ) (hL : 0 < L) (z : ℝ)
    (hz : ∀ j : ℤ, z ≠ j * L) :
    HasDerivAt (reflectedFold L) (reflectedFoldSlope L z) z := by
  let r := reflectedFold L z
  have hr : r ∈ Ioo 0 L := reflectedFold_interior_of_ne_lattice L hL z hz
  obtain ⟨k, hk | hk⟩ := (reflectedFold_eq_iff_lattice L hL z r ⟨hr.1.le, hr.2.le⟩).mp rfl
  · have hi : z ∈ Ioo ((k : ℝ) * (2 * L)) ((k : ℝ) * (2 * L) + L) := by
      constructor <;> linarith [hr.1, hr.2]
    have hs : reflectedFoldSlope L z = 1 := by
      rw [hk]
      exact reflectedFoldSlope_rising L hL k r hr
    rw [hs]
    have hd : HasDerivAt (fun y : ℝ => reflectedFold L z + (y - z)) 1 z :=
      ((hasDerivAt_id z).sub_const z).const_add (reflectedFold L z)
    exact hd.congr_of_eventuallyEq (reflectedFold_locally_rising L hL k z hi)
  · have hi : z ∈ Ioo ((k : ℝ) * (2 * L) - L) ((k : ℝ) * (2 * L)) := by
      constructor <;> linarith [hr.1, hr.2]
    have hs : reflectedFoldSlope L z = -1 := by
      rw [hk]
      exact reflectedFoldSlope_falling L hL k r hr
    rw [hs]
    have hd : HasDerivAt (fun y : ℝ => reflectedFold L z - (y - z)) (-1) z := by
      have hh : HasDerivAt (fun y : ℝ => -(y - z) + reflectedFold L z) (-1) z :=
        (((hasDerivAt_id z).sub_const z).neg).add_const (reflectedFold L z)
      convert hh using 1
      funext y
      ring
    exact hd.congr_of_eventuallyEq (reflectedFold_locally_falling L hL k z hi)

theorem ReflectedNeumannC2.extension_fold_derivative_away {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (z : ℝ) (hz : ∀ j : ℤ, z ≠ j * L) :
    HasDerivAt (reflectedFellerExtension L hL F.valueMap)
      (F.slope (reflectedFold L z) * reflectedFoldSlope L z) z := by
  exact (F.value_derivative (reflectedFold L z) (reflectedFold_interior_of_ne_lattice L hL z hz)).comp z
    (reflectedFold_hasDerivAt_away L hL z hz)

theorem ReflectedNeumannC2.extension_fold_deriv_prod_ae {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω} {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P, p.1 ∈ Ioc (0 : ℝ) T.val →
      deriv (reflectedFellerExtension L hL F.valueMap) (x + σ * B p.1.toNNReal p.2) =
        F.slope (reflectedFold L (x + σ * B p.1.toNNReal p.2)) *
          reflectedFoldSlope L (x + σ * B p.1.toNNReal p.2) := by
  filter_upwards [brownian_affine_ne_lattice_prod_ae hB hjoint L x hσ T] with p hp ht
  exact (F.extension_fold_derivative_away hL _ (hp ht)).deriv

end TimeTraps.Probability
