module

public import TimeTraps.Probability.BrownianIntegralPastMultiplierStep

@[expose] public section

/-! A bounded strongly measurable version of one almost-everywhere
measurable coefficient. This construction is used only at the finitely
many nodes of each dyadic grid; no simultaneous all-time version of a
process is asserted. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ m : MeasurableSpace Ω} {P : @Measure Ω mΩ}
variable {Z : Ω → ℝ} {M : ℝ≥0}

def brownianBoundedAERepresentative (hZ : AEStronglyMeasurable[m] Z P) (M : ℝ≥0) : Ω → ℝ :=
  fun ω => max (-M.val) (min M.val (hZ.mk Z ω))

theorem brownianBoundedAERepresentative_stronglyMeasurable
    (hZ : AEStronglyMeasurable[m] Z P) :
    StronglyMeasurable[m] (brownianBoundedAERepresentative hZ M) :=
  stronglyMeasurable_const.sup (stronglyMeasurable_const.inf hZ.stronglyMeasurable_mk)

theorem brownianBoundedAERepresentative_bound (hZ : AEStronglyMeasurable[m] Z P) (ω : Ω) :
    |brownianBoundedAERepresentative hZ M ω| ≤ M.val := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith [M.property]) (min_le_left _ _)⟩

theorem brownianBoundedAERepresentative_ae (hZ : AEStronglyMeasurable[m] Z P)
    (hb : ∀ ω, |Z ω| ≤ M.val) : brownianBoundedAERepresentative hZ M =ᵐ[P] Z := by
  filter_upwards [hZ.ae_eq_mk] with ω hω
  unfold brownianBoundedAERepresentative
  rw [← hω, min_eq_right (abs_le.mp (hb ω)).2, max_eq_right (abs_le.mp (hb ω)).1]

end TimeTraps.Probability

end
