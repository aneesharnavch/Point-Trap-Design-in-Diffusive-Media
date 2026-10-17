module

public import TimeTraps.Probability.ReflectedFoldAffine
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! Folded trajectories with the manuscript's `sqrt (2D)` diffusion scale.
Only deterministic confinement, continuity and measurable/adapted composition
are asserted here. No Brownian law, generator or local-time property is assumed
or concluded. -/

namespace TimeTraps.Probability

open Set MeasureTheory

noncomputable def foldedTrajectory {ι Ω : Type*} (L D x : ℝ) (B : ι → Ω → ℝ)
    (t : ι) (ω : Ω) : ℝ :=
  reflectedFold L (x + Real.sqrt (2 * D) * B t ω)

theorem foldedTrajectory_mem {ι Ω : Type*} (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (B : ι → Ω → ℝ) (t : ι) (ω : Ω) : foldedTrajectory L D x B t ω ∈ Icc 0 L :=
  reflectedFold_mem L hL _

theorem foldedTrajectory_initial {ι Ω : Type*} (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (hx : x ∈ Icc 0 L) (B : ι → Ω → ℝ) (t₀ : ι) (ω : Ω) (hB : B t₀ ω = 0) :
    foldedTrajectory L D x B t₀ ω = x := by
  simp only [foldedTrajectory, hB, mul_zero, add_zero, reflectedFold_eq_self L hL x hx]

theorem foldedTrajectory_measurable {ι Ω : Type*} [MeasurableSpace Ω] (L D x : ℝ)
    (B : ι → Ω → ℝ) (hB : ∀ t, Measurable (B t)) (t : ι) :
    Measurable (foldedTrajectory L D x B t) :=
  (reflectedFold_measurable L).comp (measurable_const.add (measurable_const.mul (hB t)))

theorem foldedTrajectory_joint_measurable {ι Ω : Type*} [MeasurableSpace ι] [MeasurableSpace Ω]
    (L D x : ℝ) (B : ι → Ω → ℝ) (hB : Measurable (Function.uncurry B)) :
    Measurable (Function.uncurry (foldedTrajectory L D x B)) :=
  (reflectedFold_measurable L).comp (measurable_const.add (measurable_const.mul hB))

theorem foldedTrajectory_continuous {ι Ω : Type*} [TopologicalSpace ι] (L D x : ℝ)
    (B : ι → Ω → ℝ) (hB : ∀ ω, Continuous (fun t => B t ω)) (ω : Ω) :
    Continuous (fun t => foldedTrajectory L D x B t ω) :=
  (reflectedFold_continuous L).comp (continuous_const.add (continuous_const.mul (hB ω)))

theorem foldedTrajectory_adapted {ι Ω : Type*} [Preorder ι] [m : MeasurableSpace Ω]
    (F : Filtration ι m) (L D x : ℝ) (B : ι → Ω → ℝ) (hB : Adapted F B) :
    Adapted F (foldedTrajectory L D x B) := by
  intro t
  exact (reflectedFold_measurable L).comp (measurable_const.add (measurable_const.mul (hB t)))

theorem foldedTrajectory_increment_bound {ι Ω : Type*} (L D x : ℝ) (B : ι → Ω → ℝ)
    (s t : ι) (ω : Ω) :
    |foldedTrajectory L D x B t ω - foldedTrajectory L D x B s ω| ≤
      Real.sqrt (2 * D) * |B t ω - B s ω| := by
  calc
    _ ≤ |(x + Real.sqrt (2 * D) * B t ω) - (x + Real.sqrt (2 * D) * B s ω)| :=
      reflectedFold_abs_sub_le L _ _
    _ = _ := by
      rw [show (x + Real.sqrt (2 * D) * B t ω) - (x + Real.sqrt (2 * D) * B s ω) =
        Real.sqrt (2 * D) * (B t ω - B s ω) by ring,
        abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

end TimeTraps.Probability
